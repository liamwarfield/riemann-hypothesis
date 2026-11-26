module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCechKodairaSpencerClassAbelianTriple
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLabelsSurjectiveHomLatticeModLevel

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAffineOpenAbelianPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAffineOpenAbelianPullback
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KSOpen

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem exists_pull_chart {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) :
    ∃ (t' : SAB H S') (m : SABMap t' t f), Nonempty (ChartPull t'.PP.L t.PP.L m.φ) := by
  have h := isGrpPullback_pullback t.G f
  obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := Out.CubePf.cubePull S S' t.G _ (cubeMapOf h) t.PP t.cub
  have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
      pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
  have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
      pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
    Over.OverMorphism.ext (by
      show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
      rw [Category.assoc, hact, Category.assoc])
  refine ⟨⟨(Over.pullback f).obj t.G, IsSemiAbelian.pullback f t.G t.semi, OAct.pullback f t.G t.act,
    (cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_⟩, ⟨cubeMapOf h, h, rfl, hact, hc'⟩,
    ⟨ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ _ rfl⟩⟩
  · let U := lift (pushPt h.1.w (fst ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
      (pushPt h.1.w (snd ((Over.pullback f).obj t.G) ((Over.pullback f).obj t.G)))
    refine LBIso.chartPull (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down)
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) (t.adj a)
    · fin_cases i
      · exact (pa _ a).trans (by simp [U])
      · simp [U]
    · fin_cases i
      · simp [U]
      · exact (pa _ _).trans (by simp [U])
  · let U := pushPt h.1.w (𝟙 ((Over.pullback f).obj t.G))
    refine LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull t.PP.L _ U.left (Category.id_comp _))
      (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
    fin_cases i
    · simp [U]
    · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)

theorem proper_ample_kTriv {S S' : Scheme.{0}} [IsAffine S'] {f : S' ⟶ S} {t : SAB H S} {u u' : SAB H S'}
    (m : SABMap u t f) (m' : SABMap u' t f) (hP : IsProper u.G.hom) (hA : Out.RelAmple u.G u.PP.L)
    (hK : Out.KTriv u.G u.PP.L) : IsProper u'.G.hom ∧ Out.RelAmple u'.G u'.PP.L ∧ Out.KTriv u'.G u'.PP.L := by
  obtain ⟨n, -⟩ := GlobalTheory.ObjMaps.exists_sab_cancel (g := 𝟙 S') m ((Category.id_comp f).symm ▸ m')
  obtain ⟨w, hw, -⟩ := n.lin
  exact ⟨MorphismProperty.of_isPullback n.cart.1 hP,
    relAmple_pull n.cart.1 u.PP.isLB u'.PP.isLB ((isGen_iff w).1 hw) ⊤ (isAffineOpen_top S') (fun _ => trivial) hA,
    kTriv_pull n.cart u.PP.isLB u'.PP.isLB ((isGen_iff w).1 hw) hK⟩

theorem bijective_appLE {X X' : Scheme.{0}} (j : X' ⟶ X) [IsOpenImmersion j] {U : X.Opens} {U' : X'.Opens}
    (h : j ''ᵁ U' = U) (e : U' ≤ j ⁻¹ᵁ U) : Function.Bijective (j.appLE U U' e).hom := by
  subst h
  rw [← Scheme.Hom.appIso_hom']
  exact ConcreteCategory.bijective_of_isIso (j.appIso U').hom

theorem resG_appLE {Y Z : Scheme.{0}} (m : Z ⟶ Y) (U : Y.Opens) {V V' : Z.Opens} (h : V ≤ m ⁻¹ᵁ U) (e : V' ≤ V)
    (r : Γ(Y, U)) : resG Z e ((m.appLE U V h).hom r) = (m.appLE U V' (e.trans h)).hom r := by
  rw [← Scheme.Hom.appLE_map m h (homOfLE e).op]
  rfl

theorem app_appLE {X X' G G' : Scheme.{0}} {φ : G' ⟶ G} {p' : G' ⟶ X'} {p : G ⟶ X} {j : X' ⟶ X}
    (sq : φ ≫ p = p' ≫ j) {U : X.Opens} {U' : X'.Opens} (e : U' ≤ j ⁻¹ᵁ U) {O : G.Opens} (h : O ≤ p ⁻¹ᵁ U)
    (h' : φ ⁻¹ᵁ O ≤ p' ⁻¹ᵁ U') (r : Γ(X, U)) :
    (φ.app O).hom ((p.appLE U O h).hom r) = (p'.appLE U' (φ ⁻¹ᵁ O) h').hom ((j.appLE U U' e).hom r) := by
  rw [Scheme.Hom.app_eq_appLE, ← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_comp_appLE,
    Scheme.Hom.appLE_comp_appLE]
  congr 3

theorem valR_comp_appLE {Y Z : Scheme.{0}} {S : Type} [CommRing S] (z : Sp S ⟶ Y) (m : Y ⟶ Z) {O : Z.Opens}
    {O' : Y.Opens} (e : O' ≤ m ⁻¹ᵁ O) (hz : ⊤ ≤ z ⁻¹ᵁ O') (f : Γ(Z, O)) :
    valR (z ≫ m) O f = valR z O' ((m.appLE O O' e).hom f) := by
  rw [GlobalTheory.CechKS.valR_comp_app, ← GlobalTheory.CechKS.valR_resG z e hz]
  rfl

theorem isKS_of_openImmersion {X X' : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {j : X' ⟶ X} [IsOpenImmersion j]
    (m : SABMap t' t j) (cp : ChartPull t'.PP.L t.PP.L m.φ) (V : X.Opens) (U : X.affineOpens) (hUV : U.1 ≤ V)
    (U' : X'.affineOpens) (hU : j ''ᵁ U'.1 = U.1) (ψ : Γ(X, U.1) ≃+* Γ(X', U'.1)) (e : U'.1 ≤ j ⁻¹ᵁ U.1)
    (hψ : ∀ r, ψ r = (j.appLE U.1 U'.1 e).hom r) (hch : chart U' ≫ j = spMap ψ.toRingHom ≫ chart U) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (v' : Fin n → (Sp (DualNumber Γ(X', U'.1)) ⟶ t'.G.left))
    (hv : ∀ i, IsTanAtG t (chart U) (v i)) (hv' : ∀ i, IsTanAtG t' (chart U') (v' i))
    (hvv : ∀ i, v' i ≫ m.φ = spMap (dualMap ψ.toRingHom) ≫ v i)
    (D : Γ(X, U.1) → Γ(X, U.1)) (D' : Γ(X', U'.1) → Γ(X', U'.1)) (hD : ∀ r, D' (ψ r) = ψ (D r))
    (Θ : Matrix (Fin n) (Fin n) Γ(X', U'.1)) (h : IsKS t' ⊤ U' v' D' Θ) : IsKS t V U v D (Θ.map ψ.symm) := by
  obtain ⟨J, W, c, d, hcov, hWc, hd, hl, hr⟩ := h
  obtain ⟨hoi, hrange⟩ := GlobalTheory.sabMap_isOpenImmersion_opensRange E H X X' t t' j m
  have sq : m.φ ≫ t.G.hom = t'.G.hom ≫ j := m.cart.1.w
  rw [inf_top_eq] at hcov
  have hWU : ∀ i, W i ≤ t'.G.hom ⁻¹ᵁ U'.1 := fun i => hcov ▸ le_iSup W i
  have hpre : t'.G.hom ⁻¹ᵁ U'.1 = m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U.1) := by
    rw [← Scheme.Hom.comp_preimage, sq, Scheme.Hom.comp_preimage, ← hU, Scheme.Hom.preimage_image_eq]
  have hle : ∀ i {O : t.G.left.Opens}, O ≤ m.φ ''ᵁ W i → m.φ ⁻¹ᵁ O ≤ W i := fun i O hO =>
    (m.φ.preimage_mono hO).trans (m.φ.preimage_image_eq (W i)).le
  choose d₂ hd₂ hd₂' using fun i => GlobalTheory.LogKS.isField_image _ _ m.φ (W i) (d i) (hd i)
  refine ⟨J, fun i => m.φ ''ᵁ W i, fun i => cp.idx (c i), d₂, ?_, fun i => ?_, hd₂, fun i hW r => ?_, ?_⟩
  · rw [← Scheme.Hom.image_iSup, hcov, hpre, Scheme.Hom.image_preimage_eq_opensRange_inf, hrange, inf_eq_left.2 hUV,
      inf_eq_right]
    apply t.G.hom.preimage_mono
    rw [← hU]
    exact j.image_le_opensRange _
  · rintro _ ⟨y, hy, rfl⟩
    exact cp.le _ (hWc i hy)
  · have hinj : Function.Injective (m.φ.app (m.φ ''ᵁ W i)).hom :=
      (ConcreteCategory.bijective_of_isIso (m.φ.app (m.φ ''ᵁ W i))).1
    apply hinj
    have h1 := hle i le_rfl
    rw [hd₂' i _ le_rfl, app_appLE sq e hW (h1.trans (hWU i)), app_appLE sq e hW (h1.trans (hWU i)), ← hψ, ← hψ,
      ← hD, ← resG_appLE _ _ (hWU i) h1, (hd i).2.2 _ _ h1 le_rfl, hl i (hWU i), resG_appLE]
  · intro i i' O hO f S _ φ g₀ w hg hO₀ hT
    have hOi : O ≤ m.φ ''ᵁ W i := hO.trans inf_le_left
    have hOi' : O ≤ m.φ ''ᵁ W i' := hO.trans inf_le_right
    obtain ⟨g₁, rfl⟩ : ∃ g₁ : Sp S ⟶ t'.G.left, g₁ ≫ m.φ = g₀ :=
      ⟨IsOpenImmersion.lift m.φ g₀ (by
        rintro _ ⟨y, rfl⟩
        obtain ⟨z, -, hz⟩ := hOi (hO₀ (Set.mem_univ y))
        exact ⟨z, hz⟩), IsOpenImmersion.lift_fac _ _ _⟩
    obtain ⟨φ₁, rfl⟩ : ∃ φ₁ : Γ(X', U'.1) →+* S, φ₁.comp ψ.toRingHom = φ :=
      ⟨φ.comp ψ.symm.toRingHom, RingHom.ext fun r => by simp⟩
    have hg₁ : g₁ ≫ t'.G.hom = spMap φ₁ ≫ chart U' := by
      rw [← cancel_mono j, Category.assoc, ← sq, ← Category.assoc, hg, Category.assoc, hch, ← Category.assoc]
      congr 1
      exact Spec.map_comp (CommRingCat.ofHom ψ.toRingHom) (CommRingCat.ofHom φ₁)
    choose w₁ hw₁ hT₁ using fun a => GlobalTheory.TransLift.lift_isTranslate E H X X' t t' j m _ _ ψ.toRingHom (chart U) (chart U') hch
      (v a) (v' a) (hv a) (hv' a) (hvv a) S φ₁ g₁ hg₁ (w a) (hT a)
    obtain rfl : w = fun a => w₁ a ≫ m.φ := funext fun a => (hw₁ a).symm
    have hO₁ : ⊤ ≤ g₁ ⁻¹ᵁ (m.φ ⁻¹ᵁ O) := hO₀
    have key := hr i i' (m.φ ⁻¹ᵁ O) (le_inf (hle i hOi) (hle i' hOi')) ((m.φ.app O).hom f) S φ₁ g₁ w₁ hg₁ hO₁ hT₁
    have hgc : ⊤ ≤ g₁ ⁻¹ᵁ (t'.PP.L.U (c i) ⊓ t'.PP.L.U (c i')) :=
      hO₁.trans (g₁.preimage_mono (le_inf ((hle i hOi).trans (hWc i)) ((hle i' hOi').trans (hWc i'))))
    have hwc : ∀ b, ⊤ ≤ w₁ b ⁻¹ᵁ (t'.PP.L.U (c i) ⊓ t'.PP.L.U (c i')) := fun b =>
      GlobalTheory.CechKS.le_preimage_of_red (GlobalTheory.LogKS.IsTranslate.fst_comp E H X' t' _ S φ₁ (chart U') g₁ (v' b) (w₁ b) hg₁ (hv' b) (hT₁ b)) hgc
    have hgp := GlobalTheory.chartPull_g_appLE _ _ _ _ m.φ cp (c i) (c i')
    have hgi : ((t'.PP.L.g (c i) (c i'))⁻¹).val = (m.φ.appLE _ _
        (le_inf (inf_le_left.trans (cp.le (c i))) (inf_le_right.trans (cp.le (c i'))))).hom
        ((t.PP.L.g (cp.idx (c i)) (cp.idx (c i')))⁻¹).val :=
      Units.inv_eq_of_mul_eq_one_right (by rw [hgp, ← map_mul, Units.mul_inv, map_one])
    rw [GlobalTheory.CechKS.valR_comp_app, map_sub, hd₂' i O hOi, hd₂' i' O hOi', key]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hgp, hgi]
    refine congrArg₂ (· * ·) (congrArg₂ (· * ·) (by simp) (congrArg₂ (· * ·) (congrArg TrivSqZeroExt.snd ?_) ?_))
      (congrArg TrivSqZeroExt.snd ?_)
    · exact (valR_comp_appLE (w₁ b) m.φ _ (hwc b) _).symm
    · exact (valR_comp_appLE g₁ m.φ _ hgc _).symm
    · exact (GlobalTheory.CechKS.valR_comp_app (w₁ a) m.φ O f).symm

def derivMap {A B : Type} [CommRing A] [CommRing B] (ψ : A ≃+* B) (D : Derivation ℤ A A) : Derivation ℤ B B :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap
    ((ψ.toAddMonoidHom.comp D.toLinearMap.toAddMonoidHom).comp ψ.symm.toAddMonoidHom)) fun a b => by
      simp

theorem derivMap_apply {A B : Type} [CommRing A] [CommRing B] (ψ : A ≃+* B) (D : Derivation ℤ A A) (r : A) :
    derivMap ψ D (ψ r) = ψ (D r) := by
  simp [derivMap]

theorem exists_isKS_of_pull : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens), U.1 ≤ V → ∀ (t' : SAB H (Sp Γ(X, U.1))), Nonempty (SABMap t' t (chart U)) → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t V U v D Θ := by
  intro E _ _ _ H X t V U hUV t' ⟨m'⟩ hP hA hK n v hv hb D
  obtain ⟨u, m, ⟨cp⟩⟩ := exists_pull_chart (chart U) t
  obtain ⟨hP', hA', hK'⟩ := proper_ample_kTriv m' m hP hA hK
  haveI : IsOpenImmersion (chart U) := U.2.isOpenImmersion_fromSpec
  let U' : (Sp Γ(X, U.1)).affineOpens := ⟨⊤, isAffineOpen_top _⟩
  have hU : chart U ''ᵁ U'.1 = U.1 := by
    show chart U ''ᵁ ⊤ = U.1
    rw [Scheme.Hom.image_top_eq_opensRange]
    exact U.2.opensRange_fromSpec
  have e : U'.1 ≤ chart U ⁻¹ᵁ U.1 := U.2.fromSpec_preimage_self.ge
  let ψ : Γ(X, U.1) ≃+* Γ(Sp Γ(X, U.1), U'.1) := RingEquiv.ofBijective _ (bijective_appLE (chart U) hU e)
  have hch : chart U' ≫ chart U = spMap ψ.toRingHom ≫ chart U :=
    (IsAffineOpen.SpecMap_appLE_fromSpec (chart U) U.2 U'.2 e).symm
  obtain ⟨v', hvv, hv', hb'⟩ := GlobalTheory.SabTan.tanBasis_sabMap E H X _ t u (chart U) m _ _ ψ.toRingHom (chart U) (chart U') hch n v hv hb
  obtain ⟨Θ, hΘ⟩ := GlobalTheory.T.exists_cech_kodairaSpencer_class_abelianTriple E H _ u hP' hA' hK' U' n v' hv' hb' (derivMap ψ D)
  exact ⟨_, isKS_of_openImmersion m cp V U hUV U' hU ψ e (fun _ => rfl) hch v v' hv hv' hvv D _
    (derivMap_apply ψ D) Θ hΘ⟩

end GlobalTheory.KSOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAffineOpenAbelianPullbackStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kodairaSpencer_affine_open_abelian_pullback : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X : Scheme.{0}) (t : SAB H X) (V : X.Opens) (U : X.affineOpens), U.1 ≤ V → ∀ (t' : SAB H (Sp Γ(X, U.1))), Nonempty (SABMap t' t (chart U)) → IsProper t'.G.hom → Out.RelAmple t'.G t'.PP.L → Out.KTriv t'.G t'.PP.L → ∀ (n : ℕ) (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)), (∀ i, IsTanAtG t (chart U) (v i)) → (∀ w, IsTanAtG t (chart U) w → ∃! cf : Fin n → Γ(X, U.1), IsCombAtG t (chart U) v cf w) → ∀ D : Derivation ℤ Γ(X, U.1) Γ(X, U.1), ∃ Θ, IsKS t V U v D Θ := by
  first | exact @GlobalTheory.KSOpen.exists_isKS_of_pull | exact GlobalTheory.KSOpen.exists_isKS_of_pull | (intros; apply GlobalTheory.KSOpen.exists_isKS_of_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsObjMapOfPIsogenyPullback
section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsObjMapOfPIsogenyPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem UpperTheory.Cb.exists_objMap_of_p_isogeny_pullback :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ o₁' : Obj b N s₁) (o o' : Obj b N s) (m : ObjMap o₁ o t) (ψ₁ : o₁.A ⟶ o₁'.A) (ψ : o.A ⟶ o'.A) (θ : o₁'.A.left ⟶ o'.A.left), IsUnit ((p : ℕ) : R) → IsPIsog c o₁ o₁' ψ₁ → IsPIsog c o o' ψ → IsGrpPullback o₁'.A o'.A t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → ∃ m' : ObjMap o₁' o' t, m'.φ = θ := by
  intro p _ D R _ b N c T Y s₁ s t o₁ o₁' o o' m ψ₁ ψ θ hp hψ₁ hψ hcart hmc
  obtain ⟨θ₂, hθ₂1, hθ₂2⟩ : ∃ θ₂ : (G2 o₁'.A).left ⟶ (G2 o'.A).left,
      θ₂ ≫ (fst o'.A o'.A).left = (fst o₁'.A o₁'.A).left ≫ θ ∧
      θ₂ ≫ (snd o'.A o'.A).left = (snd o₁'.A o₁'.A).left ≫ θ := by
    refine ⟨Limits.pullback.lift (Limits.pullback.fst _ _ ≫ θ) (Limits.pullback.snd _ _ ≫ θ) ?_,
      Limits.pullback.lift_fst _ _ _, Limits.pullback.lift_snd _ _ _⟩
    rw [Category.assoc, Category.assoc, hcart.1.w, ← Category.assoc, ← Category.assoc,
      Limits.pullback.condition]
  have ext2 : ∀ {Z : Scheme} (f g : Z ⟶ (G2 o'.A).left),
      f ≫ (fst o'.A o'.A).left = g ≫ (fst o'.A o'.A).left →
      f ≫ (snd o'.A o'.A).left = g ≫ (snd o'.A o'.A).left → f = g :=
    fun f g h1 h2 => Limits.pullback.hom_ext h1 h2
  obtain ⟨ψ₁', hq⟩ := hψ₁.exists_quasiInv
  have hc : 0 < c := hψ₁.pos
  haveI := (SiegUniqBase.flat_surjective_qc_pow T o₁'.A o₁'.ab c hc).1
  haveI := (SiegUniqBase.flat_surjective_qc_pow T o₁'.A o₁'.ab c hc).2.1
  have hepi : Epi (Over.Hom.left (𝟙 o₁'.A ^ c)) := Flat.epi_of_flat_of_surjective _
  have he : Over.Hom.left (𝟙 o₁'.A ^ c) = ψ₁'.left ≫ ψ₁.left := by
    rw [← hq.2.2.2, Over.comp_left]
  have hone : (1 : o₁'.A ⟶ o₁'.A).left ≫ θ = θ ≫ (1 : o'.A ⟶ o'.A).left := by
    have h := GlobalTheory.LocTrivDescent.one_left_comp hcart
    rw [Hom.one_def, Over.comp_left, Over.toUnit_left, Hom.one_def, Over.comp_left, Over.toUnit_left] at h
    rw [Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left]
    rw [Category.assoc, ← Category.assoc θ, hcart.1.w, Category.assoc]
    congr 1
  have hs2 : ∀ {S : Scheme} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
      (f : A ⟶ A'), sq2 f ≫ (fst A' A').left = (fst A A).left ≫ f.left ∧
        sq2 f ≫ (snd A' A').left = (snd A A).left ≫ f.left := by
    intro S A A' _ _ _ _ f
    constructor <;> (rw [sq2, ← Over.comp_left]; simp)
  have hsq : sq2 ψ₁ ≫ θ₂ = m.φ₂ ≫ sq2 ψ := by
    apply ext2
    · simp only [Category.assoc]
      rw [hθ₂1, (hs2 ψ).1, ← Category.assoc (sq2 ψ₁), (hs2 ψ₁).1, ← Category.assoc m.φ₂, m.sq.1]
      simp only [Category.assoc, hmc]
    · simp only [Category.assoc]
      rw [hθ₂2, (hs2 ψ).2, ← Category.assoc (sq2 ψ₁), (hs2 ψ₁).2, ← Category.assoc m.φ₂, m.sq.2]
      simp only [Category.assoc, hmc]
  have hQ : (o'.P.pull θ₂).IsLB := pull_isLB o'.isLB θ₂
  have hcu : IsUnit ((c : ℕ) : Γ(T, ⊤)) := by
    obtain ⟨kk, rfl⟩ := hψ₁.exists_eq_pow
    rw [Nat.cast_pow]
    refine IsUnit.pow _ ?_
    have := hp.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s₁.appTop).hom
    simpa using this
  have hone2 : (lift 1 (𝟙 o₁'.A)).left ≫ θ₂ = θ ≫ (lift 1 (𝟙 o'.A)).left := by
    apply ext2
    · rw [Category.assoc, hθ₂1, ← Category.assoc, ← Over.comp_left, lift_fst, hone, Category.assoc, ← Over.comp_left, lift_fst]
    · rw [Category.assoc, hθ₂2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.id_comp, Category.assoc, ← Over.comp_left, lift_snd, Over.id_left, Category.comp_id]
  have hone3 : (lift (𝟙 o₁'.A) 1).left ≫ θ₂ = θ ≫ (lift (𝟙 o'.A) 1).left := by
    apply ext2
    · rw [Category.assoc, hθ₂1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.id_comp, Category.assoc, ← Over.comp_left, lift_fst, Over.id_left, Category.comp_id]
    · rw [Category.assoc, hθ₂2, ← Category.assoc, ← Over.comp_left, lift_snd, hone, Category.assoc, ← Over.comp_left, lift_snd]
  have r1 : ∃ t : ((o'.P.pull θ₂).pull (lift 1 (𝟙 o₁'.A)).left).Gen, t.IsGen := by
    rw [GlobalTheory.LocTrivDescent.triv_iff hQ, GlobalTheory.CechPic.cls_pull o'.isLB θ₂ hQ, ← GlobalTheory.CechPic.pull_comp,
      hone2, GlobalTheory.CechPic.pull_comp, (GlobalTheory.LocTrivDescent.triv_iff o'.isLB _).1 o'.rig₁, map_zero]
  have r2 : ∃ t : ((o'.P.pull θ₂).pull (lift (𝟙 o₁'.A) 1).left).Gen, t.IsGen := by
    rw [GlobalTheory.LocTrivDescent.triv_iff hQ, GlobalTheory.CechPic.cls_pull o'.isLB θ₂ hQ, ← GlobalTheory.CechPic.pull_comp,
      hone3, GlobalTheory.CechPic.pull_comp, (GlobalTheory.LocTrivDescent.triv_iff o'.isLB _).1 o'.rig₂, map_zero]
  have hiso : LBIso (o₁'.P.pull (sq2 ψ₁)) ((o'.P.pull θ₂).pull (sq2 ψ₁)) := by
    rw [← GlobalTheory.CechPic.cls_eq_iff (pull_isLB o₁'.isLB _) (pull_isLB hQ _)]
    obtain ⟨hI⟩ := hψ₁.2.2.2.2.1
    obtain ⟨hI'⟩ := hψ.2.2.2.2.1
    have e1 : c • GlobalTheory.CechPic.cls o₁.P o₁.isLB =
        GlobalTheory.CechPic.cls (o₁'.P.pull (sq2 ψ₁)) (pull_isLB o₁'.isLB _) := by
      rw [← GlobalTheory.LocTrivDescent.cls_lbPow_eq o₁.isLB c (LB.isLB_linComb o₁.isLB _ _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 hI
    have e2 : c • GlobalTheory.CechPic.cls o.P o.isLB =
        GlobalTheory.CechPic.cls (o'.P.pull (sq2 ψ)) (pull_isLB o'.isLB _) := by
      rw [← GlobalTheory.LocTrivDescent.cls_lbPow_eq o.isLB c (LB.isLB_linComb o.isLB _ _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).2 hI'
    have e3 := (GlobalTheory.CechPic.cls_eq_iff o₁.isLB (pull_isLB o.isLB m.φ₂)).2 m.pol
    rw [← e1, GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull o'.isLB, ← GlobalTheory.CechPic.pull_comp, hsq,
      GlobalTheory.CechPic.pull_comp, ← GlobalTheory.CechPic.cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _), ← e2,
      map_nsmul, ← GlobalTheory.CechPic.cls_pull o.isLB _ (pull_isLB o.isLB _), ← e3]
  refine ⟨⟨θ, θ₂, hcart, ⟨hθ₂1, hθ₂2⟩, ?_, ?_, ?_⟩, rfl⟩
  · intro c'
    rw [← cancel_epi (Over.Hom.left (𝟙 o₁'.A ^ c)), he]
    have h1 := congrArg Over.Hom.left (hψ₁.2.2.1 c')
    have h2 := congrArg Over.Hom.left (hψ.2.2.1 c')
    simp only [Over.comp_left] at h1 h2
    simp only [Category.assoc]
    rw [← reassoc_of% h1, ← hmc, reassoc_of% (m.act c'), h2, reassoc_of% hmc]
  · exact GlobalTheory.QuasiInvPull.lbIso_of_pullback_quasiInverseIsogeny_trivial_axes T o₁.A o₁'.A c ψ₁ ψ₁' o₁'.P (o'.P.pull θ₂) o₁'.ab hc hcu
      hq (isAxesTriv_obj o₁') ⟨hQ, r1, r2⟩ hiso
  · intro y
    rw [hψ₁.2.2.2.1 y, Over.comp_left, Category.assoc, ← hmc, ← Category.assoc, m.eta y,
      Category.assoc, ← Over.comp_left, ← hψ.2.2.2.1 y]
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_objMap_of_p_isogeny_pullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ o₁' : Obj b N s₁) (o o' : Obj b N s) (m : ObjMap o₁ o t) (ψ₁ : o₁.A ⟶ o₁'.A) (ψ : o.A ⟶ o'.A) (θ : o₁'.A.left ⟶ o'.A.left), IsUnit ((p : ℕ) : R) → IsPIsog c o₁ o₁' ψ₁ → IsPIsog c o o' ψ → IsGrpPullback o₁'.A o'.A t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → ∃ m' : ObjMap o₁' o' t, m'.φ = θ := by
  first | exact @UpperTheory.Cb.exists_objMap_of_p_isogeny_pullback | exact UpperTheory.Cb.exists_objMap_of_p_isogeny_pullback
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationKernelOfPIsogenyQuasiInverse
section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PolarizationKernelOfPIsogenyQuasiInverse
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

open GlobalTheory.BirigidPow (val_one_left val_one_right val_pow_right comp_pow_pt) in
open GlobalTheory.CechPic (cls cls_pull cls_eq_iff cls_eq_zero_iff pull_comp) in
set_option maxHeartbeats 1000000 in
theorem UpperTheory.Cb.polarization_kernel_of_p_isogeny_quasi_inverse :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) (ψ' : o'.A ⟶ o.A), IsUnit ((p : ℕ) : R) → IsPIsog c o o' ψ → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) := by
  intro p _ D R _ b N c Y s o o' ψ ψ' hp hI hq T σ hσ x hx
  have hP := o.isLB
  have hP' := o'.isLB
  have hc0 : 0 < c := hI.pos
  obtain ⟨k, hk⟩ := hI.1
  haveI := hq.1
  haveI := hq.2.1
  have hu : IsUnit (c : Γ(Y, ⊤)) := by
    have h := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [map_natCast] at h
    rw [hk, Nat.cast_pow]
    exact h.pow k

  have hQ1 : (o.P.pull (sq2 ψ')).IsLB := pull_isLB hP _
  have hQ2 : (Hecke.lbPow o'.P c).IsLB := LB.isLB_linComb hP' _ _
  have cQ1 : cls _ hQ1 = GlobalTheory.CechPic.pull (sq2 ψ') (cls o.P hP) := cls_pull hP _ hQ1
  have cQ2 : cls _ hQ2 = c • cls o'.P hP' := GlobalTheory.BirigidPow.cls_lbPow hP' c hQ2
  have atQ₁ : ∀ {U : Over Y} (a b : U ⟶ o'.A),
      GlobalTheory.CechPic.pull (lift a b).left (cls _ hQ1) = GlobalTheory.BirigidPow.val hP (a ≫ ψ') (b ≫ ψ') := by
    intro U a b
    rw [cQ1, GlobalTheory.BirigidPow.val, ← pull_comp, sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc]
  have atQ₂ : ∀ {U : Over Y} (a b : U ⟶ o'.A),
      GlobalTheory.CechPic.pull (lift a b).left (cls _ hQ2) = c • GlobalTheory.BirigidPow.val hP' a b := by
    intro U a b
    rw [cQ2, map_nsmul, GlobalTheory.BirigidPow.val]
  have ax1 : IsAxesTriv o'.A (o.P.pull (sq2 ψ')) := by
    refine ⟨hQ1, (cls_eq_zero_iff (pull_isLB hQ1 _)).1 ?_, (cls_eq_zero_iff (pull_isLB hQ1 _)).1 ?_⟩
    · rw [cls_pull hQ1 _ (pull_isLB hQ1 _), atQ₁, MonObj.one_comp]
      exact val_one_left hP o.rig₁ _
    · rw [cls_pull hQ1 _ (pull_isLB hQ1 _), atQ₁, MonObj.one_comp]
      exact val_one_right hP o.rig₂ _
  have ax2 : IsAxesTriv o'.A (Hecke.lbPow o'.P c) := by
    refine ⟨hQ2, (cls_eq_zero_iff (pull_isLB hQ2 _)).1 ?_, (cls_eq_zero_iff (pull_isLB hQ2 _)).1 ?_⟩
    · rw [cls_pull hQ2 _ (pull_isLB hQ2 _), atQ₂, val_one_left hP' o'.rig₁, smul_zero]
    · rw [cls_pull hQ2 _ (pull_isLB hQ2 _), atQ₂, val_one_right hP' o'.rig₂, smul_zero]

  have eP : GlobalTheory.CechPic.pull (sq2 ψ) (cls o'.P hP') = c • cls o.P hP := by
    obtain ⟨i⟩ := hI.2.2.2.2.1
    have h := (cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hP' _)).2 i
    rw [cls_pull hP' _ (pull_isLB hP' _)] at h
    rw [← h]
    exact GlobalTheory.BirigidPow.cls_lbPow hP c _
  have eC : GlobalTheory.CechPic.pull (sq2 ((𝟙 o.A) ^ c)) (cls o.P hP) = (c ^ 2) • cls o.P hP := by
    have i := GlobalTheory.BirigidPow.lineBundleIso_tensorPowSq_pullback_mulPair hP o.ab o.ample o.rig₁ o.rig₂ c
    have h := (cls_eq_iff (LB.isLB_linComb hP _ _) (pull_isLB hP _)).2 i
    rw [cls_pull hP _ (pull_isLB hP _)] at h
    rw [← h]
    exact GlobalTheory.BirigidPow.cls_lbPow hP _ _
  have eS : sq2 ψ ≫ sq2 ψ' = sq2 ((𝟙 o.A) ^ c) := by
    rw [← hq.2.2.1, sq2, sq2, sq2, ← Over.comp_left, comp_lift]
    simp
  have iso : LBIso ((o.P.pull (sq2 ψ')).pull (sq2 ψ)) ((Hecke.lbPow o'.P c).pull (sq2 ψ)) := by
    refine (cls_eq_iff (pull_isLB hQ1 _) (pull_isLB hQ2 _)).1 ?_
    rw [cls_pull hQ1 _ (pull_isLB hQ1 _), cls_pull hQ2 _ (pull_isLB hQ2 _), cQ1, cQ2, map_nsmul, eP,
      ← pull_comp, eS, eC, smul_smul, sq]
  have cE : cls _ hQ1 = cls _ hQ2 := (cls_eq_iff hQ1 hQ2).2
    (GlobalTheory.QuasiInvPull.lbIso_of_pullback_quasiInverseIsogeny_trivial_axes Y o.A o'.A c ψ ψ' _ _ o'.ab hc0 hu hq ax1 ax2 iso)
  have key : ∀ {U : Over Y} (a b : U ⟶ o'.A), GlobalTheory.BirigidPow.val hP (a ≫ ψ') (b ≫ ψ') = c • GlobalTheory.BirigidPow.val hP' a b := by
    intro U a b
    rw [← atQ₁, cE, atQ₂]
  have hT : PullPolTriv o ψ' x ↔ GlobalTheory.BirigidPow.val hP' (fst o'.A T) (snd o'.A T ≫ x ^ c) = 0 := by
    unfold PullPolTriv
    rw [← cls_eq_zero_iff (pull_isLB hP _), cls_pull hP _ (pull_isLB hP _)]
    change GlobalTheory.BirigidPow.val hP _ _ = 0 ↔ _
    rw [← Category.assoc (snd o'.A T) x ψ', key, comp_pow_pt,
      val_pow_right hP' o'.ab o'.ample o'.rig₁ o'.rig₂]
  have hsym : ∀ {U : Over Y} (a b : U ⟶ o'.A), GlobalTheory.BirigidPow.val hP' a b = GlobalTheory.BirigidPow.val hP' b a := by
    intro U a b
    obtain ⟨i⟩ : Nonempty (LBIso o'.P (o'.P.pull (lift (snd o'.A o'.A) (fst o'.A o'.A)).left)) := ⟨o'.symm⟩
    have h := (cls_eq_iff hP' (pull_isLB hP' _)).2 i
    rw [cls_pull hP' _ (pull_isLB hP' _)] at h
    rw [GlobalTheory.BirigidPow.val, h, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd, lift_fst, GlobalTheory.BirigidPow.val]
  rw [hT]
  constructor
  · intro h
    obtain ⟨e, he, hker⟩ := o'.kerP
    have h1 : (x ^ c) ^ e = 1 := hker T (x ^ c)
      ((cls_eq_zero_iff (pull_isLB hP' _)).1 (by
        rw [cls_pull hP' _ (pull_isLB hP' _)]
        exact (hsym _ _).trans h))
    have h2 : (x ^ c) ^ (c ^ 2) = 1 := by
      rw [← pow_mul, ← pow_succ', hx]
    have hco : e.gcd (c ^ 2) = 1 := by
      rw [hk]
      exact Nat.Coprime.pow_right _ (Nat.Coprime.pow_right _ he)
    have := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rwa [hco, pow_one] at this
  · intro h
    rw [h, MonObj.comp_one]
    exact val_one_right hP' o'.rig₂ _
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.polarization_kernel_of_p_isogeny_quasi_inverse : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o o' : Obj b N s) (ψ : o.A ⟶ o'.A) (ψ' : o'.A ⟶ o.A), IsUnit ((p : ℕ) : R) → IsPIsog c o o' ψ → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) := by
  first | exact @UpperTheory.Cb.polarization_kernel_of_p_isogeny_quasi_inverse | exact UpperTheory.Cb.polarization_kernel_of_p_isogeny_quasi_inverse
end
