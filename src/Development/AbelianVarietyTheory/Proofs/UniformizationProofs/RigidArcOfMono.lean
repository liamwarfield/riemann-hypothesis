module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisedArcIsoMatchesLevelPoints
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisedArcIsoMatchesLevelPoints
noncomputable section

namespace GlobalTheory.ArcLevel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem epi_spMap {K k : Type} [Field K] [Field k] (β : K →+* k) : Epi (spMap β) := by
  have : Flat (spMap β) := inferInstance
  have : Surjective (spMap β) := ⟨fun y => ⟨default, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_genPt {R : Type} [CommRing R] [IsDomain R] {G : Over (Sp R)} {A : Over (Sp (FractionRing R))}
    (gen : (Over.pullback (jK R)).obj G ≅ A) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (g : Sp F ⟶ G.left) (hg : g ≫ G.hom = jFK (R := R) F ≫ jK R) :
    ∃ x : TFK (R := R) F ⟶ A, x.left ≫ gen.inv.left ≫ pullback.fst G.hom (jK R) = g := by
  let z : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G :=
    Over.homMk (pullback.lift g (jFK (R := R) F) hg) (pullback.lift_snd _ _ _)
  refine ⟨z ≫ gen.hom, ?_⟩
  have hgi : gen.hom.left ≫ gen.inv.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
  show (z.left ≫ gen.hom.left) ≫ _ = _
  rw [Category.assoc, ← Category.assoc gen.hom.left, hgi, Category.id_comp]
  exact pullback.lift_fst _ _ _

theorem genRel_of_heq {F : Type} [Field F] {B B₀ : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {φ φ' : B ⟶ B₀} (h : φ' = φ)
    {w : LB.Iso M (M₀.pull φ)} {w' : LB.Iso M (M₀.pull φ')} (hw : HEq w' w)
    {K : Type} [Fintype K] {pt : K → (Sp F ⟶ B)} {pt₀ : K → (Sp F ⟶ B₀)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb M pt ε)} {t₀ : LB.Gen (LB.LinComb M₀ pt₀ ε)} {x : F} (H : GenRel w t t₀ x) :
    GenRel w' t t₀ x := by
  subst h
  obtain rfl := eq_of_heq hw
  exact H

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_conj_part (v : D.La) : ∃ v' ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
    ∀ {S : Scheme.{0}} {B : Type} [CommRing B] {b : Base l B} {s : S ⟶ Sp B} (o : Obj D l b s),
      o.eta v = o.eta v' := by
  have h : v ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) ⊔
      l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) := by
    rw [← Submodule.sup_smul, l.coprime, Submodule.top_smul]; trivial
  obtain ⟨v₁, h₁, v₂, h₂, rfl⟩ := Submodule.mem_sup.1 h
  exact ⟨v₂, h₂, fun o => by rw [o.eta_add, o.eta_ker _ h₁, _root_.one_mul]⟩

variable {Xo : Moduli D l} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}

theorem witData {O : Type} [CommRing O] {β : O →+* c.F} {Y : Model Xo c β} {χ : Sp (PowerSeries k) ⟶ Y.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) :
    WitData a W.P.D W.P.oD W.φ W.he W.w W.e := by
  obtain ⟨s1, s2, s3, s4, s5, s6⟩ := W.spec
  exact ⟨s1, s2, s3, s4, s5, fun F _ _ _ _ uF h₁ h₂ => (s6 F uF h₁ h₂).1⟩


set_option maxHeartbeats 1600000 in
theorem level_core (hL : Laws) (hL2 : Laws2) (h5 : Laws5) {O O' : Type} [CommRing O] [CommRing O']
    {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
    {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X}
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre)
    (hφ : (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ)
    (hxe : ∀ x, hD.xe (W.e x) = W'.e x)
    (w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫
      pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)))
    (hw₁ : HEq w₁ W.w) (T : Tri W'.w hD.w w₁) (ψ : W.t.G ≅ W'.t.G)
    (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G) (hbc : IsMonHom bc.hom)
    (hψ : bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left)
    (hPU : IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U)
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c) (hy : y ≫ Y.j = jK (PowerSeries k) ≫ χ)
    (hy' : y' ≫ Y'.j = jK (PowerSeries k) ≫ χ') (n : ℕ) (p₀ : QkPt a.D₀ (FractionRing k) n)
    (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G)
    (hσ : (n = l.A ∧ ∃ v, HEq p₀ (a.etaA v) ∧ σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨
      (n = l.M ∧ ∃ v ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
        HEq p₀ (a.eta v) ∧ σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v))
    (g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left) (hg : g ≫ W.t.G.hom = jK (PowerSeries k))
    (hgm : g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ) : g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ := by
  have hG : GlobalFnsSt := globalFns_holds
  have hR := admissibleBase_powerSeries k
  obtain ⟨F, _, _, _, _, hF⟩ := ArcTransport.exists_commonField k
  have hn : 1 ≤ n := by
    rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact l.A_pos
    · exact le_trans (by norm_num) l.three_le
  have hn' : n ∣ l.M' := by
    rcases hσ with ⟨rfl, -⟩ | ⟨rfl, -⟩
    · exact Nat.dvd_lcm_right _ _
    · exact Nat.dvd_lcm_left _ _
  obtain ⟨q₀, e1, -⟩ := TorusExt.existsUnique_qkExt a.bimult (algebraMap (FractionRing k) F) (RingHom.comp_id _) p₀
  obtain ⟨q, e2, e3⟩ := ArcTransport.exists_transport (witData W) hF rfl hG hn' q₀
  have hF' : ∀ r : PowerSeries k, algebraMap (FractionRing (PowerSeries k)) F (algebraMap _ _ r) =
      algebraMap (FractionRing (PowerSeries k)) F (algebraMap _ _ ((RingHom.id _) r)) := fun _ => rfl
  obtain ⟨q', hq₁, hq₂⟩ := qkPullExists hG _ _ (RingHom.id _) W'.P.D.toPre W.P.D.toPre hD F hF' n q

  have hc : (y' ≫ σ'.left ≫ Y'.m.φ) ≫ Y'.t.G.hom = jK (PowerSeries k) ≫ χ' := by
    have a₁ : Y'.m.φ ≫ Y'.t.G.hom = Y'.oF.t.G.hom ≫ Y'.j := Y'.m.cart.1.w
    have a₂ : σ'.left ≫ Y'.oF.t.G.hom = 𝟙 _ := Over.w σ'
    rw [Category.assoc, Category.assoc, a₁, reassoc_of% a₂, hy']
  let g' : Sp (FractionRing (PowerSeries k)) ⟶ W'.t.G.left := W'.m.cart.1.lift _ _ hc
  have hg' : g' ≫ W'.t.G.hom = jK (PowerSeries k) := W'.m.cart.1.lift_snd _ _ _
  have hgm' : g' ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ := W'.m.cart.1.lift_fst _ _ _
  have hih : ψ.inv.left ≫ ψ.hom.left = 𝟙 _ := by rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  obtain ⟨x, hx⟩ := exists_genPt W.P.U.gen (jFK (R := PowerSeries k) F ≫ g) (by rw [Category.assoc, hg])
  obtain ⟨x', hx'⟩ := exists_genPt W'.P.U.gen (jFK (R := PowerSeries k) F ≫ g') (by rw [Category.assoc, hg'])
  obtain ⟨x'', hx''⟩ := exists_genPt W.P.U.gen (jFK (R := PowerSeries k) F ≫ g' ≫ ψ.inv.left)
    (by rw [Category.assoc, Category.assoc, Over.w, hg'])
  have t₁ : QkToAkU W.P.U.toUnifPre F n q x := by
    refine (W.spec.2.2.2.2.2 F _ hF rfl).2 (jFK (R := PowerSeries k) F ≫ y) (by rw [Category.assoc, hy]) n p₀ σ ?_
      q₀ q x e1 e2 e3 ?_
    · rcases hσ with ⟨h, v, h₁, h₂, -⟩ | ⟨h, v, hv, h₁, h₂, -⟩
      · exact Or.inl ⟨h, v, h₁, h₂⟩
      · exact Or.inr ⟨h, v, hv, h₁, h₂⟩
    · rw [reassoc_of% hx, hgm, Category.assoc]
  have t₂ : QkToAkU W'.P.U.toUnifPre F n q' x' := by
    refine (W'.spec.2.2.2.2.2 F _ hF rfl).2 (jFK (R := PowerSeries k) F ≫ y') (by rw [Category.assoc, hy']) n p₀ σ' ?_
      q₀ q' x' e1 ?_ (fun z => ?_) ?_
    · rcases hσ with ⟨h, v, h₁, -, h₂⟩ | ⟨h, v, hv, h₁, -, h₂⟩
      · exact Or.inl ⟨h, v, h₁, h₂⟩
      · exact Or.inr ⟨h, v, hv, h₁, h₂⟩
    · have : hD.xe q.y = q'.y := by rw [hq₁, AddEquiv.apply_symm_apply]
      rw [← this, e2]; exact hxe _
    · obtain ⟨hψ', hm⟩ := hq₂.2 (W.e z)
      have pm := (maps_iff hD.w _ _ _ (q.g.s (W.e z)) (q'.g.s (hD.xe (W.e z))) (𝟙 _) _
        (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ') (fun _ => rfl)).1 hm
      have k' := (genRel_transfer T W'.P.D.toPre.P.isLB W.P.D.toPre.P.isLB hψ' pm _ _).2
        (genRel_of_heq hφ hw₁ (e3 z))
      rw [hxe z] at k'
      exact k'
    · rw [reassoc_of% hx', hgm', Category.assoc]
  have t₃ : QkToAkU W.P.U.toUnifPre F n q x'' :=
    h5.qkBaseChange _ _ _ _ hR hR (RingHom.id _) W'.P.D W'.P.A W'.t.G W'.P.U W.t.G bc hbc W.P.A W.P.D hD W.P.U
      hPU F hF' n hn q' x' q x'' hq₁ hq₂ (by rw [hψ, reassoc_of% hx'', hih, Category.comp_id, hx']) t₂
  have hxx := TorsionImage.qkToAkU_unique hL hL2 _ _ hR W.P.D W.P.A W.t.G W.t.semi W.P.U F n hn q x x'' t₁ t₃
  have := epi_spMap (algebraMap (FractionRing (PowerSeries k)) F)
  have hgg : g = g' ≫ ψ.inv.left :=
    (cancel_epi (spMap (algebraMap (FractionRing (PowerSeries k)) F))).1 (hx.symm.trans (hxx ▸ hx''))
  rw [hgg, Category.assoc, reassoc_of% hih, hgm']

theorem level_match : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → ∀ (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → (∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G), ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) → ∀ g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left, g ≫ W.t.G.hom = jK (PowerSeries k) → g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ → g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ) := by
  intro hL hL2 h5 E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' hD ⟨hφ, hxe, w₁, hw₁, T⟩ ψ bc _ hbc hψ hPU _
    y y' hy hy' _ _ σ σ' hσ g hg hgm
  rcases hσ with ⟨v, h₁, h₂⟩ | ⟨v, h₁, h₂⟩
  · exact level_core hL hL2 h5 W W' hD hφ hxe w₁ hw₁ T ψ bc hbc hψ hPU y y' hy hy' l.A (a.etaA v) σ σ'
      (Or.inl ⟨rfl, v, HEq.rfl, h₁, h₂⟩) g hg hgm
  · obtain ⟨v', hv', e⟩ := exists_conj_part (l := l) v
    exact level_core hL hL2 h5 W W' hD hφ hxe w₁ hw₁ T ψ bc hbc hψ hPU y y' hy hy' l.M (a.eta v') σ σ'
      (Or.inr ⟨rfl, v', hv', HEq.rfl, h₁.trans (e _), h₂.trans (e _)⟩) g hg hgm

end GlobalTheory.ArcLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisedArcIsoMatchesLevelPointsStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.uniformisedArc_iso_matches_levelPoints : Laws → Laws2 → Laws5 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → ∀ (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c), y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' → y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF → (∀ (σ : 𝟙_ (Over (Xo.XF c)) ⟶ Y.oF.t.G) (σ' : 𝟙_ (Over (Xo.XF c)) ⟶ Y'.oF.t.G), ((∃ v, σ = Y.oF.etaA v ∧ σ' = Y'.oF.etaA v) ∨ ∃ v, σ = Y.oF.eta v ∧ σ' = Y'.oF.eta v) → ∀ g : Sp (FractionRing (PowerSeries k)) ⟶ W.t.G.left, g ≫ W.t.G.hom = jK (PowerSeries k) → g ≫ W.m.φ = y ≫ σ.left ≫ Y.m.φ → g ≫ ψ.hom.left ≫ W'.m.φ = y' ≫ σ'.left ≫ Y'.m.φ) := by
  first | exact @GlobalTheory.ArcLevel.level_match | exact GlobalTheory.ArcLevel.level_match | (intros; apply GlobalTheory.ArcLevel.level_match <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ArcWitAgreeOfIsPullUnif
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


set_option maxHeartbeats 6400000 in
theorem arcWit_agree_of_isPullUnif : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF) (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β') (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X) (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ) (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ') (hD : IsPullDeg (RingHom.id (PowerSeries k)) W'.P.D.toPre W.P.D.toPre), ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ = W.φ ∧ (∀ x, hD.xe (W.e x) = W'.e x) ∧ ∃ w₁ : LB.Iso W.P.D.toPre.P.L (a.D₀.P.L.pull ((hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫ W'.φ)), HEq w₁ W.w ∧ Tri W'.w hD.w w₁) → ∀ (ψ : W.t.G ≅ W'.t.G) (bc : W.t.G ≅ (Over.pullback (specOf (RingHom.id (PowerSeries k)))).obj W'.t.G), IsMonHom ψ.hom → IsMonHom bc.hom → bc.hom.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k))) = ψ.hom.left → IsPullUnif (RingHom.id (PowerSeries k)) hD bc W'.P.U W.P.U → (∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x) → (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left), g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) → W.Agree W' ψ := by
  intro E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' hD₂ ⟨hφe, hee, w₂, hwe, T₂⟩ ψ bc hψ _ hbc hPU₂
    hact h3
  have he : eSec W.t.G ≫ ψ.hom.left = 𝟙 _ ≫ eSec W'.t.G := by
    rw [Category.id_comp]
    exact congrArg (fun f => f.left) (IsMonHom.one_hom ψ.hom)
  obtain ⟨wL₂, g₂, he₂, m₂, lev₂⟩ := hPU₂.lg
  have pg₂ := (isGen_iff wL₂).1 g₂
  refine ⟨hψ, hact, h3, he, pullCongr hbc wL₂,
    (isGen_iff _).2 (pgen_pullCongr hbc pg₂), ?_, fun n ψn hψn => ?_⟩
  · have HA := (maps_iff wL₂ _ (fun _ => eSec W'.t.G) _ W.P.U.LG.rig W'.P.U.LG.rig
      (Out.specOf (RingHom.id (PowerSeries k))) _ (rigPull_le _ _ he₂ W'.P.U.LG.L) (fun _ => rfl)).1 m₂
    have e0 : Out.specOf (RingHom.id (PowerSeries k)) = 𝟙 (𝟙_ (Over (Sp (PowerSeries k)))).left := by
      simp [Out.specOf]
    have HB : PMaps wL₂ (fun _ : PUnit => eSec W.t.G) (fun _ => eSec W'.t.G) (fun _ => 1) W.P.U.LG.rig W'.P.U.LG.rig
        (𝟙 _) := e0 ▸ HA
    exact (maps_iff (pullCongr hbc wL₂) _ (fun _ => eSec W'.t.G) _ W.P.U.LG.rig W'.P.U.LG.rig (𝟙 _) _
      (rigPull_le _ _ he W'.P.U.LG.L) (fun _ => rfl)).2 (pmaps_pullCongr hbc HB)
  · obtain ⟨h₂, hh₁, hh₂, ht₂, hw₂⟩ := lev₂ n
    have hfst : h₂ ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left =
        (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left ≫ ψ.hom.left := by
      rw [hh₁, hbc]
    obtain rfl : h₂ = ψn := by rw [hψn]; exact thick_map_eq ψ.hom h₂ hfst
    refine ⟨?_, fun A _ _ v => ⟨fun x pt₀ t₀ _ hg => ?_, fun j₀ jM jM' jL jL' H1 H2 H3 => ?_⟩⟩
    · exact (congrArg (fun f => (W.P.U.gt n).pG.left ≫ f) hφe.symm).trans (((Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ W'.φ) hh₂)).trans (Category.assoc _ _ _))
    · obtain ⟨hψ₂, hm₂⟩ := ht₂ (W.e x)
      have P₂ := (maps_iff hD₂.w _ _ _ ((W.P.U.gt n).t (W.e x)) ((W'.P.U.gt n).t (hD₂.xe (W.e x))) h₂ _
        (Out.GeneratorPullback.pullAlong_le _ _ _ _ _ hψ₂) (fun _ => rfl)).1 hm₂
      have Q₂ := genRelR_transfer T₂ W'.P.D.toPre.P.isLB W.P.D.toPre.P.isLB
        (fun k => by rw [Category.assoc, hψ₂ k, Category.id_comp, Category.assoc])
        (pmaps_pullGen P₂ v (v ≫ h₂) rfl) t₀
      have Q₃ := genRelR_heq hφe hwe (LB.pullGen _ _ _ ((W.P.U.gt n).t (W.e x)) v) t₀
      rw [← hee x]
      exact Q₂.2 (Q₃.2 hg)
    · have m1 := (top_le_iff_cpt _ _).1 H1
      have m2 := (top_le_iff_cpt _ _).1 H2
      have m3 := (top_le_iff_cpt _ _).1 H3
      have p2 : (v ≫ (W.P.U.gt n).pG.left) ≫ hD₂.e.hom.left ≫
          pullback.fst W'.P.D.toPre.P.A.hom (Out.specOf (RingHom.id (PowerSeries k))) =
          v ≫ h₂ ≫ (W'.P.U.gt n).pG.left := by rw [Category.assoc, hh₂]
      have p3 : (v ≫ h₂) ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left =
          (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) ≫ ψ.hom.left := by
        rw [Category.assoc, hfst, Category.assoc]
      have e2 := congrArg (fun g => g (cpt A)) p2
      have e3 := congrArg (fun g => g (cpt A)) p3
      simp only at e2 e3
      have hjM := m1.2
      have mB1 : W'.φ ((hD₂.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom
          (Out.specOf (RingHom.id (PowerSeries k)))) ((v ≫ (W.P.U.gt n).pG.left) (cpt A))) ∈ a.D₀.P.L.U j₀ := by
        have := mem_pull.1 m2.1; rw [← e2] at this; exact this
      have mB2 : (hD₂.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (Out.specOf (RingHom.id (PowerSeries k))))
          ((v ≫ (W.P.U.gt n).pG.left) (cpt A)) ∈ W'.P.D.toPre.P.L.U jM' := by
        have := m2.2; rw [← e2] at this; exact this
      have mC1 := mem_pull.1 m3.1
      have mC2 := m3.2
      have mC3 : (bc.hom.left ≫ pullback.fst W'.t.G.hom (Out.specOf (RingHom.id (PowerSeries k))))
          ((v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A)) ∈ W'.P.U.LG.L.U jL' := by
        rw [hbc]; exact mC1
      have mD : (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left ((v ≫ h₂) (cpt A)) ∈ W'.P.U.LG.L.U jL' := by
        have e3' : (Out.fstG (Ideal.span {PowerSeries.X}) n W'.t.G).left ((v ≫ h₂) (cpt A)) =
            ψ.hom.left ((v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A)) := e3
        rw [e3']; exact mC1
      have R2 := T₂ _ (v ≫ (W.P.U.gt n).pG.left) (cpt A) j₀ jM' jM mB1 mB2 hjM
      rw [p2] at R2
      have RE := gw_heq hφe hwe (v ≫ (W.P.U.gt n).pG.left) (cpt A) j₀ jM
      have RU2 : gw hD₂.w (v ≫ (W.P.U.gt n).pG.left) (cpt A) jM' jM *
          gm v (cpt A) _ ((W.P.U.w n).s (fun _ => jM, fun _ => jL)) =
          gm (v ≫ h₂) (cpt A) _ ((W'.P.U.w n).s (fun _ => jM', fun _ => jL')) *
          gw wL₂ (v ≫ (Out.fstG (Ideal.span {PowerSeries.X}) n W.t.G).left) (cpt A) jL' jL := by
        have := gm_of_res_eq' (hw₂ (fun _ => jM') jM jL (fun _ => jL')) v (y := cpt A)
          ⟨⟨⟨⟨mem_pull.2 mB2, hjM⟩, ⟨mem_pull.2 hjM, mem_pull.2 mC2⟩⟩, ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩⟩,
            ⟨mem_pull.2 mC3, mC2⟩⟩
        rw [gm_pull, gm_pull, gm_pull] at this
        · exact this
        · exact ⟨mem_pull.2 mC3, mC2⟩
        · exact ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩
        · exact ⟨mem_pull.2 mB2, hjM⟩
      have EU := congrArg (· * gm v (cpt A) _ ((W.P.U.w n).s (fun _ => jM, fun _ => jL))) (RE.symm.trans R2)
      beta_reduce at EU
      rw [_root_.mul_assoc, RU2, ← _root_.mul_assoc, ← gw_pullCongr hbc wL₂] at EU
      apply toStkA_injective
      rw [map_mul, map_mul, map_mul, toStkA_valR, toStkA_valR, toStkA_valR, toStkA_valR, toStkA_valR]
      · have EU' := congrArg Units.val EU
        simp only [Units.val_mul] at EU'
        exact EU'
      all_goals first
        | exact H1
        | exact H2
        | exact H3
        | exact (top_le_iff_cpt _ _).2 ⟨mem_pull.2 m2.2, mem_pull.2 mD⟩
        | exact (top_le_iff_cpt _ _).2 ⟨mem_pull.2 m1.2, mem_pull.2 mC2⟩

end GlobalTheory
end

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory
namespace ArcRigidity

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {k : Type} [Field k] {bF : c.F →+* k} {a : ArcIn D l (RingHom.id c.F) k bF}
  {O O' : Type} [CommRing O] [CommRing O'] {β : O →+* c.F} {β' : O' →+* c.F} {Y : Model Xo c β} {Y' : Model Xo c β'}
  {χ : Sp (PowerSeries k) ⟶ Y.X} {χ' : Sp (PowerSeries k) ⟶ Y'.X}

theorem core (hL : Laws) (hL₂ : Laws2) (hL₅ : Laws5)
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c)
    (hy : y ≫ Y.j = jK (PowerSeries k) ≫ χ) (hy' : y' ≫ Y'.j = jK (PowerSeries k) ≫ χ')
    (hs : y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF)
    (hs' : y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF) :
    y = y' ∧ ∃ ψ : W.t.G ≅ W'.t.G,
      (∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left)
        (τ : T ⟶ Sp (FractionRing (PowerSeries k))),
        g ≫ W.t.G.hom = τ ≫ jK (PowerSeries k) → g₁ ≫ Y.oF.t.G.hom = τ ≫ y → g ≫ W.m.φ = g₁ ≫ Y.m.φ →
        g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ → g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom →
        g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) ∧
      ((∀ (T : Scheme.{0}) (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (g₂ : T ⟶ Y'.oF.t.G.left),
        g ≫ W.m.φ = g₁ ≫ Y.m.φ → g₁ ≫ Y.m0.toSABMap.φ = g₂ ≫ Y'.m0.toSABMap.φ →
        g₁ ≫ Y.oF.t.G.hom = g₂ ≫ Y'.oF.t.G.hom → g ≫ ψ.hom.left ≫ W'.m.φ = g₂ ≫ Y'.m.φ) → W.Agree W' ψ) := by
  letI := H.starRing
  obtain ⟨hD, hdat⟩ := GlobalTheory.arcWit_data_iso hL₅ E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W'
  have hI : Ideal.span {(PowerSeries.X : PowerSeries k)} = IsLocalRing.maximalIdeal (PowerSeries k) :=
    PowerSeries.maximalIdeal_eq_span_X.symm
  obtain ⟨ψ, bc, hψ, hbc, hfst, hU⟩ := GlobalTheory.T.exists_iso_uniformisations_of_iso_degeneration_data hL hL₂ (PowerSeries k) _ (admissibleBase_powerSeries k) hI W'.P.D W.P.D W'.P.A W.P.A
    W'.t.G W.t.G W'.t.semi W.t.semi W'.P.U W.P.U hD
  have hx : ∀ (x : 𝓞 E) (z : W.P.D.toPre.X), hD.xe (x • z) = x • hD.xe z := by
    intro x z
    obtain ⟨z₀, rfl⟩ := W.e.surjective z
    rw [← W.e.map_smul, hdat.2.1, hdat.2.1]
    exact W'.e.map_smul x z₀
  have hB : ∀ x, (W.P.oD.onB.act x).left ≫
        (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) =
      (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫
        (W'.P.oD.onB.act x).left := by
    intro x
    apply W'.spec.1.1.hom_ext
    · have h₁ : (W.P.oD.onB.act x).left ≫ W.φ = W.φ ≫ (a.oa.onB.act x).left := W.spec.2.2.2.1 x
      have h₂ : (W'.P.oD.onB.act x).left ≫ W'.φ = W'.φ ≫ (a.oa.onB.act x).left := W'.spec.2.2.2.1 x
      exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hdat.1).trans h₁)).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans
          ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hdat.1)))).symm
    · have e : (hD.e.hom.left ≫ pullback.fst W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k)))) ≫
          W'.P.D.toPre.P.A.hom = W.P.D.toPre.P.A.hom := by
        have w : hD.e.hom.left ≫ pullback.snd W'.P.D.toPre.P.A.hom (specOf (RingHom.id (PowerSeries k))) =
          W.P.D.toPre.P.A.hom := Over.w hD.e.hom
        rw [Category.assoc, pullback.condition, ← Category.assoc, w, specOf_id, Category.comp_id]
      rw [Category.assoc, e, Over.w, Category.assoc, Over.w, e]
  have hlin := act_comm_of_isPullUnif_id hL.globalFns (PowerSeries k) _ (admissibleBase_powerSeries k) hI W'.P.D W.P.D W'.P.A W.P.A
    W'.t.G W.t.G W'.t.semi W.t.semi W'.P.U W.P.U hD bc hbc hU (𝓞 E) W'.P.oD W.P.oD W'.P.oA W.P.oA
    W'.t.act.toRingAct W.t.act.toRingAct W'.P.lin W.P.lin hx hB
  have hact : ∀ x, W.t.act.act x ≫ ψ.hom = ψ.hom ≫ W'.t.act.act x := by
    intro x
    have q := congrArg (fun z => z.left ≫ pullback.fst W'.t.G.hom (specOf (RingHom.id (PowerSeries k)))) (hlin x)
    ext
    simp only [Over.comp_left, Category.assoc, Over.pullback_map_left, pullback.lift_fst] at q
    rw [hfst, ← Category.assoc, hfst] at q
    exact q
  have hlev := GlobalTheory.T.uniformisedArc_iso_matches_levelPoints hL hL₂ hL₅ E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W' hD hdat ψ bc hψ hbc hfst hU hact
    y y' hy hy' hs hs'
  have hb : LBIso W.t.PP.L (W'.t.PP.L.pull ψ.hom.left) := by
    obtain ⟨w, hw, -⟩ := hU.lg
    rw [← W.P.bundle, ← W'.P.bundle, ← hfst]
    exact ⟨w, hw⟩
  obtain ⟨e, h⟩ := ArcObj.point_eq hL W.m W'.m ψ hact hb _ y y' hy hy' (hs.trans hs'.symm) hlev
  exact ⟨e, ψ, h, arcWit_agree_of_isPullUnif E H D l Xo c k bF a O O' β β' Y Y' χ χ' W W' hD hdat ψ bc hψ hbc hfst hU hact⟩

theorem exists_generic
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    {T : Scheme.{0}} (g : T ⟶ W.t.G.left) (g₁ : T ⟶ Y.oF.t.G.left) (h₁ : g ≫ W.m.φ = g₁ ≫ Y.m.φ) :
    (g ≫ W.t.G.hom) ≫ χ = (g₁ ≫ Y.oF.t.G.hom) ≫ Y.j ∧
      ∃ τ : T ⟶ Sp (FractionRing (PowerSeries k)), g ≫ W.t.G.hom = τ ≫ jK (PowerSeries k) := by
  have := ThetaShiftProofs.isOpenImmersion_jK_powerSeries k
  have q : (g ≫ W.t.G.hom) ≫ χ = (g₁ ≫ Y.oF.t.G.hom) ≫ Y.j := by
    have h₁' : g ≫ W.m.cm.F = g₁ ≫ Y.m.cm.F := h₁
    rw [Category.assoc, ← W.m.cart.1.w, reassoc_of% h₁', Y.m.cart.1.w, Category.assoc]; rfl
  have hr : Set.range (g ≫ W.t.G.hom) ⊆ Set.range (jK (PowerSeries k)) := by
    rintro _ ⟨p, rfl⟩
    exact arcWit_mem_range_jK_of_mem_range_j E H D l Xo c k bF a O β Y χ W _
      ⟨(g₁ ≫ Y.oF.t.G.hom) p, congrArg (fun z => z p) q.symm⟩
  exact ⟨q, _, (IsOpenImmersion.lift_fac (jK (PowerSeries k)) _ hr).symm⟩

end ArcRigidity

theorem rigidArc_of_mono : Laws → Laws2 → Laws5 →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (k : Type) [Field k] (bF : c.F →+* k) (a : ArcIn D l (RingHom.id c.F) k bF)
    (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F) (β' : O' →+* c.F) (Y : Model Xo c β) (Y' : Model Xo c β')
    (χ : Sp (PowerSeries k) ⟶ Y.X) (χ' : Sp (PowerSeries k) ⟶ Y'.X)
    (W : ArcWit Y (a.restrict β) (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ)
    (W' : ArcWit Y' (a.restrict β') (Ideal.span {PowerSeries.X}) (PowerSeries.C (R := k)) PowerSeries.X χ')
    (y y' : Sp (FractionRing (PowerSeries k)) ⟶ Xo.XF c),
    y ≫ Y.j = jK (PowerSeries k) ≫ χ → y' ≫ Y'.j = jK (PowerSeries k) ≫ χ' →
    y ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
    y' ≫ pullback.snd _ _ = jK (PowerSeries k) ≫ spMap (PowerSeries.C (R := k)) ≫ spMap bF →
    y = y' ∧ (Mono Y.j → ∃ ψ : W.t.G ≅ W'.t.G, W.Agree W' ψ) := by
  intro hL hL₂ hL₅ E _ _ _ H D l Xo c k _ bF a O O' _ _ β β' Y Y' χ χ' W W' y y' hy hy' hs hs'
  obtain ⟨e, ψ, h, hA⟩ := ArcRigidity.core hL hL₂ hL₅ W W' y y' hy hy' hs hs'
  refine ⟨e, fun hm => ⟨ψ, hA fun T g g₁ g₂ h₁ h₂ h₃ => ?_⟩⟩
  obtain ⟨q, τ, hτ⟩ := ArcRigidity.exists_generic W g g₁ h₁
  refine h T g g₁ g₂ τ hτ ?_ h₁ h₂ h₃
  rw [← cancel_mono Y.j, ← q, hτ, Category.assoc, Category.assoc, hy]

end GlobalTheory
