module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenMovePow
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GmMulEqOfResMulEq

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PushEquivSymmLeft
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ObjPull

section Pts

variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

def pushEquiv (h : IsGrpPullback G' G f φ) (T : Over S') : (T ⟶ G') ≃* (Over.mk (T.hom ≫ f) ⟶ G) :=
  MulEquiv.ofBijective (pushHom h T)
    ⟨fun x y hxy =>
      Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y])),
    fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem pushEquiv_left (h : IsGrpPullback G' G f φ) (T : Over S') (x : T ⟶ G') :
    (pushEquiv h T x).left = x.left ≫ φ := rfl

theorem pushEquiv_symm_left (h : IsGrpPullback G' G f φ) (T : Over S') (x : Over.mk (T.hom ≫ f) ⟶ G) :
    ((pushEquiv h T).symm x).left ≫ φ = x.left := by
  rw [← pushEquiv_left h, MulEquiv.apply_symm_apply]

def secPull (h : IsGrpPullback G' G f φ) : (𝟙_ (Over S) ⟶ G) →* (𝟙_ (Over S') ⟶ G') :=
  (pushEquiv h (𝟙_ (Over S'))).symm.toMonoidHom.comp (preHom (toUnit _))

theorem toUnit_left' (T : Over S) : (toUnit T).left = T.hom := by
  have := Over.w (toUnit T)
  exact (Category.comp_id _).symm.trans this

theorem secPull_left (h : IsGrpPullback G' G f φ) (e : 𝟙_ (Over S) ⟶ G) :
    (secPull h e).left ≫ φ = f ≫ e.left := by
  refine (pushEquiv_symm_left h _ _).trans ?_
  show (toUnit _ ≫ e).left = _
  rw [Over.comp_left, toUnit_left']
  exact congrArg (· ≫ e.left) (Category.id_comp f)

theorem pushEquiv_secPull (h : IsGrpPullback G' G f φ) (T : Over S') (e : 𝟙_ (Over S) ⟶ G) :
    pushEquiv h T (toUnit _ ≫ secPull h e) = toUnit _ ≫ e := by
  apply Over.OverMorphism.ext
  rw [pushEquiv_left, Over.comp_left, Over.comp_left, Category.assoc, secPull_left, toUnit_left', toUnit_left']
  exact (Category.assoc _ _ _).symm

end Pts

def tateMove {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {k : Type} [Field k]
    {Q Q' : Type} [Group Q] [Group Q'] {act : 𝓞 E → Q → Q} {act' : 𝓞 E → Q' → Q'}
    {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop} (Φ : Q' ≃* Q)
    (hact : ∀ c x, Φ (act' c x) = act c (Φ x)) (he : ∀ n x y c, e n (Φ x) (Φ y) c → e' n x y c)
    (I : TateIso D k Q act e) : TateIso D k Q' act' e' where
  ζ := I.ζ
  ζ_prim := I.ζ_prim
  ζ_pow := I.ζ_pow
  ev := fun n a => Φ.symm (I.ev n a)
  add := fun n a b => by simp only [I.add, map_mul]
  lin := fun n c a => by
    apply Φ.injective
    rw [MulEquiv.apply_symm_apply, hact, MulEquiv.apply_symm_apply]
    exact I.lin n c a
  ker := fun n hn a => (map_eq_one_iff _ Φ.symm.injective).trans (I.ker n hn a)
  onto := fun n hn x => by
    rw [← map_eq_one_iff Φ Φ.injective, map_pow, I.onto n hn]
    exact exists_congr fun a => Φ.symm_apply_eq.symm
  tower := fun n m hn hm a => by rw [← map_pow, I.tower n m hn hm a]
  isom := fun n hn a b => he _ _ _ _ (by
    rw [Φ.apply_symm_apply, Φ.apply_symm_apply]
    exact I.isom n hn a b)

theorem objPull_of_pol : (∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L')) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f) := by
  intro hAb E _ _ _ H D l B B' _ _ b b' j S S' s s' f hρ hζ hs o
  obtain ⟨t', ⟨m⟩⟩ : ∃ t' : SAB H S', Nonempty (SABMap t' o.t f) := by
    let t := o.t
    have hC := Out.CubePf.cubePull
    have hsemi : IsSemiAbelian ((Over.pullback f).obj t.G) := by
      refine { comm := ?_, smooth := ?_, separated := ?_, quasiCompact := ?_, geomConnected := ?_, fibres := ?_ }
      · have := t.semi.comm
        infer_instance
      · have := t.semi.smooth
        change Smooth (pullback.snd t.G.hom f)
        infer_instance
      · have := t.semi.separated
        change IsSeparated (pullback.snd t.G.hom f)
        infer_instance
      · have := t.semi.quasiCompact
        change QuasiCompact (pullback.snd t.G.hom f)
        infer_instance
      · have := t.semi.geomConnected
        change GeometricallyConnected (pullback.snd t.G.hom f)
        infer_instance
      · intro Ω _ _ q
        obtain ⟨A⟩ := t.semi.fibres Ω (q ≫ f)
        exact ⟨torusExtOfIso (pullCompIso q f t.G) A⟩
    have hp : ∃ (PP' : RigLB ((Over.pullback f).obj t.G)) (cub : CubicalStr _ PP') (sym : PP'.IsSymmetric) (adj : _) (prim : _)
        (m : SABMap ⟨(Over.pullback f).obj t.G, hsemi, OAct.pullback f t.G t.act, PP', cub,
          sym, adj, prim⟩ t f), m.φ = pullback.fst t.G.hom f := by
      have h := isGrpPullback_pullback t.G f
      obtain ⟨hL, hr, ⟨c', hc'⟩, hs⟩ := hC S S' t.G _ (cubeMapOf h) t.PP t.cub
      have hact : ∀ a, ((OAct.pullback f t.G t.act).act a).left ≫ pullback.fst t.G.hom f =
          pullback.fst t.G.hom f ≫ (t.act.act a).left := fun a => pullback.lift_fst _ _ _
      have pa : ∀ {T : Over S'} (x : T ⟶ (Over.pullback f).obj t.G) a,
          pushPt h.1.w (x ≫ (OAct.pullback f t.G t.act).act a) = pushPt h.1.w x ≫ t.act.act a := fun x a =>
        Over.OverMorphism.ext (by
          show (x.left ≫ _) ≫ _ = (x.left ≫ _) ≫ _
          rw [Category.assoc, hact, Category.assoc])
      refine ⟨(cubeMapOf h).rigLB t.PP hL hr, c', hs t.sym, fun a => ?_, ?_, ⟨cubeMapOf h, h, rfl, hact, hc'⟩, rfl⟩
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
        refine LBIso.chartPull (chartPullPull t.PP.L _ U.left (Category.id_comp _))
          (chartPullLinComb t.PP.L _ _ _ _ U.left fun I => psum_push h _ _ U (fun i => ?_) I.down) t.prim
        fin_cases i
        · simp [U]
        · exact (congrArg (pushPt h.1.w) (Category.id_comp _).symm).trans (pa _ _)
    obtain ⟨_, _, _, _, _, m, -⟩ := hp
    exact ⟨_, ⟨m⟩⟩
  have hL : LBIso t'.PP.L (o.t.PP.L.pull m.cm.F) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  have hpr := o.proper
  obtain ⟨-, hamp, hk⟩ := hAb S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB
    (AbelianSchemeGerms.isAbelianScheme_of_proper o.t.G o.t.semi) m.cart hL
  refine ⟨{ t := t'
            proper := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 hpr
            ample := hamp o.ample
            ktriv := hk o.ktriv
            eta := fun a => secPull m.cart (o.eta a)
            eta_add := fun a c => by rw [o.eta_add, map_mul]
            eta_ker := fun a ha => by rw [o.eta_ker a ha, map_one]
            etaA := fun a => secPull m.cart (o.etaA a)
            etaA_add := fun a c => by rw [o.etaA_add, map_mul]
            etaA_ker := fun a => by rw [o.etaA_ker a, map_one]
            geom := fun k _ _ x β hx => ?_ },
    ⟨⟨m, fun a => secPull_left m.cart _, fun a => secPull_left m.cart _⟩⟩⟩
  obtain ⟨hdet, I, hI, hA, hM⟩ := o.geom k (x ≫ f) (β.comp j)
    (by rw [Category.assoc, hs, ← Category.assoc, hx, spMap_comp])
  rw [RingHom.comp_apply, hρ] at hdet
  rw [RingHom.comp_apply, hζ] at hI
  refine ⟨fun τ => ?_, tateMove (pushEquiv m.cart (Over.mk x)) (fun c g => ?_) (fun n g g' c hc => ?_) I,
    hI, fun a => ?_, fun a ha => ?_⟩
  · rw [GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ,
      GlobalTheory.LiePull.lieMult_pull _ S S' o.t.G t'.G f m.cm.F o.t.act t'.act m.cart m.act k x τ]
    exact hdet τ
  · apply Over.OverMorphism.ext
    show (g.left ≫ _) ≫ _ = (g.left ≫ _) ≫ _
    rw [Category.assoc, m.act, Category.assoc]
  · exact (GlobalTheory.weilIs_grpPullback_of_comm S S' o.t.G t'.G f m.cm.F o.t.PP.L t'.PP.L o.t.PP.isLB t'.PP.isLB m.cart hL (Over.mk x) n g g'
      _ _ _ rfl rfl).2 hc
  · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hA a))
  · exact (MulEquiv.eq_symm_apply _).2 ((pushEquiv_secPull m.cart _ _).trans (hM a ha))

end GlobalTheory.ObjPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsIffOfIsGrpPullbackComm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.weilIs_iff_of_isGrpPullback_comm : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] [IsCommMonObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G') (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ → y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) :=
  GlobalTheory.weilIs_grpPullback_of_comm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabMapOfLbIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory
namespace TripleMap

theorem exists_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (hu' : u'.IsGen) :
    ∃ a : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι), r z ∈ LB.wchart L φ j →
      gm r z (LB.wchart L φ j) (u.s j) = gm r z ⊤ a * gm r z (LB.wchart L φ j) (u'.s j) := by
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → L.ι),
      gm r z (LB.wchart L φ j) (u.s j * (u'.s j)⁻¹) =
        gm r z (LB.wchart L φ j) (u.s j) * (gm r z (LB.wchart L φ j) (u'.s j))⁻¹ := fun Z r z j =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨a, ha⟩ := glue_unit ⊤ (LB.wchart L φ) (fun _ => le_top)
    (fun y _ => by
      choose p hp using fun k => exists_chart hL (φ k y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp⟩) (fun j => u.s j * (u'.s j)⁻¹)
    (fun j j' y hy => by
      rw [hv, hv, gen_trans hu (𝟙 Y) y hy.1 hy.2, gen_trans hu' (𝟙 Y) y hy.1 hy.2, mul_inv,
        _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul])
  refine ⟨a, fun Z r z j hj => ?_⟩
  rw [← gm_res r z le_top hj a, ha j, hv, inv_mul_cancel_right]

theorem exists_rigidified {X X' S S' : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} (hL : L.IsLB)
    (hL' : L'.IsLB) (w : LB.Iso L' (L.pull F)) (hw : PGen w) (e : S ⟶ X) (e' : S' ⟶ X') (p : X' ⟶ S')
    (hp : e' ≫ p = 𝟙 _) (f : S' ⟶ S) (he : e' ≫ F = f ≫ e) (ρ : LB.Gen (L.pull e)) (hρ : ρ.IsGen)
    (ρ' : LB.Gen (L'.pull e')) (hρ' : ρ'.IsGen) :
    ∃ w' : LB.Iso L' (L.pull F), PGen w' ∧
      PMaps w' (K := PUnit) (fun _ => e') (fun _ => e) (fun _ => 1) ρ' ρ f := by
  obtain ⟨ρ₀, h₀, H⟩ := DegPull.exists_pmaps hw hL hL' (K := PUnit) (φ' := fun _ => e') (φ := fun _ => e)
    (ε := fun _ => 1) f (fun _ => he) ρ hρ
  obtain ⟨a, ha⟩ := exists_ratio hL' h₀ hρ'
  let w' : LB.Iso L' (L.pull F) := ⟨fun j => res le_top (pullU p ⊤ a) * w.s j⟩
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ X') (z : Z) (j : L.ι) (k : L'.ι), F (r z) ∈ L.U j → r z ∈ L'.U k →
      gw w' r z j k = gm (r ≫ p) z ⊤ a * gw w r z j k := fun Z r z j k hj hk =>
    (map_mul _ _ _).trans (congrArg (· * _) ((gm_res r z _
      (show r z ∈ (L.pull F).U (fun _ => j) ⊓ L'.U k from ⟨mem_pull.2 hj, hk⟩) _).trans
        (gm_pull r p z ⊤ trivial a)))
  refine ⟨w', fun Z r z j j' k k' hj hj' hk hk' => ?_, fun Z r z j k hj hk => ?_⟩
  · rw [key Z r z j k hj hk, key Z r z j' k' hj' hk', hw Z r z j j' k k' hj hj' hk hk', mul_left_comm]
  · rw [H Z r z j k hj hk, ha Z r z k (Set.mem_iInter.2 hk), Fintype.prod_unique, Fintype.prod_unique,
      key Z (r ≫ e') z _ _ (hj _) (hk _), Category.assoc, hp, Category.comp_id, zpow_one, zpow_one,
      ← _root_.mul_assoc, mul_comm (gm r z ⊤ a)]

theorem pmaps_cubical {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] {f : S' ⟶ S} {F : G'.left ⟶ G.left} (gp : IsGrpPullback G' G f F) {L : RigLB G}
    {L' : RigLB G'} (c : CubicalStr G L) (c' : CubicalStr G' L') {w : LB.Iso L'.L (L.L.pull F)} (hw : PGen w)
    (rigid : ∀ a : Γ((G3 G').left, ⊤)ˣ,
      (∀ y, gm (lift (1 : 𝟙_ (Over S') ⟶ G') (lift (1 : 𝟙_ (Over S') ⟶ G') (1 : 𝟙_ (Over S') ⟶ G'))).left y ⊤ a = 1) →
        a = 1) :
    PMaps w (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (cubeMapOf gp).F3 := by
  have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ F = (cubeMapOf gp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf gp).psum_comm I.down
  obtain ⟨t, ht, H⟩ := DegPull.exists_pmaps hw L.isLB L'.isLB (ε := thε) (cubeMapOf gp).F3 hψ c.t c.isGen
  obtain ⟨a, ha⟩ := exists_ratio L'.isLB ht c'.isGen
  have a1 : a = 1 := rigid a fun y => by
    obtain ⟨J, hJ⟩ := DegPull.exists_good' L.isLB y
    obtain ⟨J', hJ'⟩ := DegPull.exists_good' L'.isLB y
    let o : 𝟙_ (Over S') ⟶ G' := 1
    have e := DegPull.pmaps_val hψ H (lift o (lift o o)).left y hJ hJ'
    have q : (lift o (lift o o)).left ≫ (cubeMapOf gp).F3 =
        (lift (pushHom gp _ o) (lift (pushHom gp _ o) (pushHom gp _ o))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    rw [q] at e
    have e₁ : cubV c y J (pushHom gp _ o) (pushHom gp _ o) (pushHom gp _ o) = 1 := by
      rw [map_one]
      exact (isCub_cubV c (T := Over.mk ((𝟙_ (Over S')).hom ≫ f)) hJ).face _ _
    have e₂ := prod_cub o o o (fun q => gw w q y (J (q ≫ F)) (J' q))
    have e₃ : cubV c' y J' o o o = 1 := (isCub_cubV c' hJ').face _ _
    have e₄ := ha _ (lift o (lift o o)).left y _ (hJ'.mem (thφ G' (x3 G')) _)
    have e₅ := e₁.symm.trans (e.trans (congrArg₂ (· * ·) e₂ (e₄.trans (congrArg _ e₃))))
    simp only [o, _root_.mul_one, mul_inv_cancel, inv_mul_cancel_right, mul_inv_cancel_right, _root_.one_mul, inv_mul_cancel] at e₅
    exact e₅.symm
  intro Z r z p q hp hq
  rw [H Z r z p q hp hq, ha Z r z q (Set.mem_iInter.2 hq), a1, map_one, _root_.one_mul]

end TripleMap

theorem exists_sabMap_of_lbIso : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (X X' : Scheme.{0}) (t : SAB H X) (t' : SAB H X') (f : X' ⟶ X) (φ : t'.G.left ⟶ t.G.left), (IsReduced X' ∧ genericPoints X' ⊆ abLocus t'.G) → IsGrpPullback t'.G t.G f φ → (∀ a, (t'.act.act a).left ≫ φ = φ ≫ (t.act.act a).left) → LBIso t'.PP.L (t.PP.L.pull φ) → ∃ ν : SABMap t' t f, ν.φ = φ := by
  intro E _ _ _ H X X' t t' f φ ⟨hr, hab⟩ gp hact ⟨w, hw⟩
  obtain ⟨w', hw', Hr⟩ := TripleMap.exists_rigidified t.PP.isLB t'.PP.isLB w ((isGen_iff w).1 hw) (eSec t.G)
    (eSec t'.G) t'.G.hom (Over.w _) f (cubeMapOf gp).e_comm t.PP.rig t.PP.rigGen t'.PP.rig t'.PP.rigGen
  have sm := t'.semi.smooth
  have gc := t'.semi.geomConnected
  have gi := grpObj_geometricallyIntegral_of_smooth X' t'.G
  obtain ⟨s₂, i₂, l₂⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X' t'.G t'.G sm sm gi gi
  obtain ⟨s₃, i₃, l₃⟩ := smooth_geometricallyIntegral_abLocus_tensorObj X' t'.G (t'.G ⊗ t'.G) sm s₂ gi i₂
  refine ⟨⟨cubeMapOf gp, gp, rfl, hact, (isPullCubical_iff _ _ _).2 ⟨w', hw', Hr,
    TripleMap.pmaps_cubical gp t.cub t'.cub hw' fun a ha => ?_⟩⟩, rfl⟩
  let o := lift (1 : 𝟙_ (Over X') ⟶ t'.G) (lift (1 : 𝟙_ (Over X') ⟶ t'.G) (1 : 𝟙_ (Over X') ⟶ t'.G))
  have h₁ : pullU o.left ⊤ a = 1 := unit_ext fun y _ =>
    (gm_pull (𝟙 _) o.left y ⊤ trivial a).trans ((congrArg (fun q => gm q y ⊤ a) (Category.id_comp _)).trans
      ((ha y).trans (map_one _).symm))
  refine Units.ext (eq_one_of_appLE_section_eq_one X' (G3 t'.G) o.left (Over.w o) s₃ i₃
    ⟨hr, fun x hx => l₃ ⟨hab hx, l₂ ⟨hab hx, hab hx⟩⟩⟩ ⊤ a.val le_rfl ?_)
  exact (congrArg (fun q => q.hom a.val) (o.left.appLE_eq_app (U := ⊤))).trans (congrArg Units.val h₁)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory

private lemma res_res_lemma {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (a : Γ(X, U)ˣ) :
    res h₂ (res h₁ a) = res (h₂.trans h₁) a := by
  unfold res
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]
  rfl

private lemma U_le_pull_id_U {X : Scheme.{0}} (N : LB X) (i : N.ι) :
    N.U i ≤ (N.pull (𝟙 X)).U (fun _ => i) := by
  intro x hx
  unfold LB.pull LB.LinComb LB.wchart
  simpa using hx

private lemma res_pullU_id_moduli {X : Scheme.{0}} {U V : X.Opens} (h : V ≤ (𝟙 X) ⁻¹ᵁ U) (h' : V ≤ U)
    (a : Γ(X, U)ˣ) : res h (pullU (𝟙 X) U a) = res h' a := by
  unfold res pullU
  ext
  simp only [Units.coe_map, MonoidHom.coe_coe]
  rfl

private lemma res_self_moduli {X : Scheme.{0}} {U : X.Opens} (h : U ≤ U) (a : Γ(X, U)ˣ) : res h a = a := by
  unfold res
  ext
  simp

theorem exists_gen_of_pull_id {X : Scheme.{0}} (N : LB X) (t : (N.pull (𝟙 X)).Gen) (ht : t.IsGen) :
    ∃ t : N.Gen, t.IsGen := by
  refine ⟨⟨fun i => res (U_le_pull_id_U N i) (t.s (fun _ => i))⟩, ?_⟩
  intro i j
  have key := congrArg (res (inf_le_inf (U_le_pull_id_U N i) (U_le_pull_id_U N j))) (ht (fun _ => i) (fun _ => j))
  rw [map_mul, res_res_lemma, res_res_lemma] at key
  simp only [res_res_lemma]
  refine key.trans ?_
  congr 1
  have hle : (N.pull (𝟙 X)).U (fun _ => i) ⊓ (N.pull (𝟙 X)).U (fun _ => j) ≤ (𝟙 X) ⁻¹ᵁ (N.U i ⊓ N.U j) := by
    intro x hx
    obtain ⟨h1, h2⟩ := hx
    simp only [LB.pull, LB.LinComb, LB.wchart] at h1 h2
    have a : x ∈ N.U i := by simpa using h1
    have b : x ∈ N.U j := by simpa using h2
    exact ⟨a, b⟩
  have hG : (N.pull (𝟙 X)).g (fun _ => i) (fun _ => j) = res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j)) := by
    show ∏ _k : PUnit, (res hle (pullU (𝟙 X) (N.U i ⊓ N.U j) (N.g i j))) ^ (1 : ℤ) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [hG, res_res_lemma]
  exact (res_pullU_id_moduli _ le_rfl _).trans (res_self_moduli _ _)

private theorem val_mul_val_comm_of_fst_eq (hG : Out.GlobalFnsSt) {S S' : Scheme.{0}} (π : S' ⟶ S) (A : Over S) [GrpObj A]
    (N : LB A.left) (hA : IsAbelianScheme A) (hN : N.IsLB)
    (w : (N.LinComb (fun _ : PUnit.{1} => pullback.fst A.hom π) (fun _ => (1 : ℤ))).Gen) (hw : w.IsGen)
    (e' : S' ⟶ pullback A.hom π) (he'p : e' ≫ pullback.fst A.hom π = π ≫ eSec A)
    (he'q : e' ≫ pullback.snd A.hom π = 𝟙 S')
    {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ pullback A.hom π)
    (hg : g₁ ≫ pullback.fst A.hom π = g₂ ≫ pullback.fst A.hom π) (z : Z) (J : (Z ⟶ A.left) → N.ι)
    (hJ : Good N z J) :
    val w g₁ z J * val w (g₂ ≫ pullback.snd A.hom π ≫ e') z J =
      val w g₂ z J * val w (g₁ ≫ pullback.snd A.hom π ≫ e') z J := by
  have hπ : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π := by
    rw [← pullback.condition, ← Category.assoc, ← Category.assoc, hg]
  let FinalForm : Over S := Over.mk (g₁ ≫ pullback.snd A.hom π ≫ π)
  have hw1 : (fst A FinalForm).left ≫ A.hom = (snd A FinalForm).left ≫ (g₁ ≫ pullback.snd A.hom π ≫ π) :=
    (Over.w (fst A FinalForm)).trans (Over.w (snd A FinalForm)).symm
  let a : (A ⊗ FinalForm).left ⟶ pullback A.hom π :=
    pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₁ ≫ pullback.snd A.hom π) (by rw [hw1]; simp)
  let a' : (A ⊗ FinalForm).left ⟶ pullback A.hom π :=
    pullback.lift (fst A FinalForm).left ((snd A FinalForm).left ≫ g₂ ≫ pullback.snd A.hom π) (by rw [hw1, hπ]; simp)
  let p0 : (A ⊗ FinalForm).left ⟶ Z := (snd A FinalForm).left
  let e : Z ⟶ (A ⊗ FinalForm).left := (lift (toUnit FinalForm ≫ η[A]) (𝟙 FinalForm)).left
  have he : e ≫ p0 = 𝟙 Z := by
    simp only [e, p0]
    rw [← Over.comp_left, lift_snd]
    rfl
  have hap : a ≫ pullback.fst A.hom π = a' ≫ pullback.fst A.hom π := by
    simp only [a, a', pullback.lift_fst]
  have hU : (toUnit FinalForm).left = g₁ ≫ pullback.snd A.hom π ≫ π :=
    (Category.comp_id _).symm.trans (Over.w (toUnit FinalForm))
  have hea : e ≫ a = g₁ ≫ pullback.snd A.hom π ≫ e' := by
    apply pullback.hom_ext
    · simp only [a, e, Category.assoc, pullback.lift_fst, he'p]
      rw [← Over.comp_left, lift_fst, Over.comp_left, hU]
      rfl
    · simp only [a, e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  have hea' : e ≫ a' = g₂ ≫ pullback.snd A.hom π ≫ e' := by
    apply pullback.hom_ext
    · simp only [a', e, Category.assoc, pullback.lift_fst, he'p]
      rw [← Over.comp_left, lift_fst, Over.comp_left, hU, hπ]
      rfl
    · simp only [a', e, Category.assoc, pullback.lift_snd, he'q, Category.comp_id]
      rw [← Category.assoc, ← Over.comp_left, lift_snd]
      rfl
  let x : FinalForm ⟶ A := Over.homMk (g₁ ≫ pullback.fst A.hom π) (by simp [FinalForm, pullback.condition])
  let ρ : Z ⟶ (A ⊗ FinalForm).left := (lift x (𝟙 FinalForm)).left
  have hρp : ρ ≫ p0 = 𝟙 Z := by
    simp only [ρ, p0]
    rw [← Over.comp_left, lift_snd]
    rfl
  have hρa : ρ ≫ a = g₁ := by
    apply pullback.hom_ext
    · simp only [a, ρ, Category.assoc, pullback.lift_fst]
      rw [← Over.comp_left, lift_fst]
      rfl
    · simp only [a, Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hρp, Category.id_comp]
  have hρa' : ρ ≫ a' = g₂ := by
    apply pullback.hom_ext
    · simp only [a', ρ, Category.assoc, pullback.lift_fst]
      rw [← Over.comp_left, lift_fst, ← hg]
      rfl
    · simp only [a', Category.assoc, pullback.lift_snd]
      rw [← Category.assoc, hρp, Category.id_comp]
  let u := LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a) (LB.pullGen N _ _ w (p0 ≫ e ≫ a'))
  let u' := LB.mulGen N _ _ _ _ (LB.pullGen N _ _ w a') (LB.pullGen N _ _ w (p0 ≫ e ≫ a))
  have hu : u.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a) (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)
  have hu' : u'.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _
    (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw a') (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w hw _)
  have hF : FormEq (Sum.elim (fun _ : PUnit.{1} => a' ≫ pullback.fst A.hom π)
        (fun _ : PUnit.{1} => (p0 ≫ e ≫ a) ≫ pullback.fst A.hom π)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => 1))
      (Sum.elim (fun _ : PUnit.{1} => a ≫ pullback.fst A.hom π)
        (fun _ : PUnit.{1} => (p0 ≫ e ≫ a') ≫ pullback.fst A.hom π)) (Sum.elim (fun _ => (1 : ℤ)) (fun _ => 1)) := by
    intro U _ h
    simp [Fintype.prod_sum_type, hap]
  have key := ReciprocityTheory.ChartRestriction.G.Geo.Tor.gen_unique' hN hF p0 e he
    (ReciprocityTheory.ChartRestriction.G.Geo.Tor.surj_snd hG hA FinalForm) hu hu' ?_ Z ρ z J hJ
  · simp only [u, u'] at key
    rw [val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, val_pull hJ, val_pull hJ] at key
    have hρp' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), ρ ≫ p0 ≫ h = h := fun h => by
      rw [← Category.assoc, hρp, Category.id_comp]
    rw [hρp', hρp', hea', hea, hρa, hρa'] at key
    exact key
  · intro y J' hJ'
    simp only [u, u']
    rw [val_mul hJ', val_mul hJ', val_pull hJ', val_pull hJ', val_pull hJ', val_pull hJ']
    have he' : ∀ {W : Scheme.{0}} (h : Z ⟶ W), e ≫ p0 ≫ h = h := fun h => by
      rw [← Category.assoc, he, Category.id_comp]
    rw [he', he', mul_comm]

theorem exists_gen_of_rigidified_of_flat_baseChange :
    Out.GlobalFnsSt → ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Flat π → Surjective π → QuasiCompact π → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom π)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  intro hG S S' π A _ N hA hN hfl hsu hqc hr hw
  obtain ⟨r, hr⟩ := hr
  obtain ⟨w, hw⟩ := hw
  have := hfl
  have := hsu
  have := hqc
  have hz : (π ≫ eSec A) ≫ A.hom = 𝟙 S' ≫ π := by
    rw [Category.assoc, Category.id_comp]
    have h0 : (η[A]).left ≫ A.hom = 𝟙 S := Over.w (η[A])
    unfold eSec
    rw [h0, Category.comp_id]
  let e' : S' ⟶ pullback A.hom π := pullback.lift (π ≫ eSec A) (𝟙 S') hz
  have he'p : e' ≫ pullback.fst A.hom π = π ≫ eSec A := pullback.lift_fst _ _ _
  have he'q : e' ≫ pullback.snd A.hom π = 𝟙 S' := pullback.lift_snd _ _ _
  let w' : (N.LinComb (fun _ : PUnit.{1} => pullback.fst A.hom π) (fun _ => (1 : ℤ))).Gen := w
  have hw' : w'.IsGen := hw
  let r' : (N.LinComb (fun _ : PUnit.{1} => eSec A) (fun _ => (1 : ℤ))).Gen := r
  have hr' : r'.IsGen := hr
  let v := LB.mulGen N _ _ _ _ w' (LB.mulGen N _ _ _ _ (LB.pullGen N _ _ r' (pullback.snd A.hom π ≫ π))
    (LB.invGen N _ _ (LB.pullGen N _ _ w' (pullback.snd A.hom π ≫ e'))))
  have hv : v.IsGen := ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ hw'
    (ReciprocityTheory.ChartRestriction.G.DVR.mulGen_isGen N _ _ _ _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ r' hr' _)
      (ReciprocityTheory.ChartRestriction.G.DVR.invGen_isGen N _ _ _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ w' hw' _)))
  obtain ⟨t', ht', hvv⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hN
    (φ' := fun _ : PUnit.{1} => pullback.fst A.hom π ≫ 𝟙 A.left) (ε' := fun _ => (1 : ℤ))
    (by intro U _ h; simp [Fintype.prod_sum_type, he'p]) v hv
  refine Exists.elim (GlobalTheory.CubeDescent.exists_gen_descend hN (pullback.fst A.hom π)
    (fun _ : PUnit.{1} => 𝟙 A.left) (fun _ => (1 : ℤ)) t' ht' ?_) (fun t ht => exists_gen_of_pull_id N t ht)
  · intro Z g₁ g₂ z J hJ hg
    rw [hvv Z g₁ z J hJ, hvv Z g₂ z J hJ]
    simp only [v, val_mul hJ, val_pull hJ, val_inv]
    have hq : g₁ ≫ pullback.snd A.hom π ≫ π = g₂ ≫ pullback.snd A.hom π ≫ π := by
      rw [← pullback.condition, ← Category.assoc, ← Category.assoc, hg]
    rw [hq]
    have key := val_mul_val_comm_of_fst_eq hG π A N hA hN w' hw' e' he'p he'q g₁ g₂ hg z J hJ
    rw [mul_left_comm (val w' g₁ z J), mul_left_comm (val w' g₂ z J)]
    congr 1
    rw [← div_eq_mul_inv, ← div_eq_mul_inv, div_eq_div_iff_mul_eq_mul]
    exact key

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGenOfRigidifiedFaithfullyFlatDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_gen_of_rigidified_faithfullyFlat_descent : Out.GlobalFnsSt → ∀ (S S' : Scheme.{0}) (π : S' ⟶ S) (A : Over S) [GrpObj A] (N : LB A.left), IsAbelianScheme A → N.IsLB → Flat π → Surjective π → QuasiCompact π → (∃ t : (N.pull (eSec A)).Gen, t.IsGen) → (∃ t : (N.pull (pullback.fst A.hom π)).Gen, t.IsGen) → ∃ t : N.Gen, t.IsGen := by
  first | exact @GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange | exact GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange | (intros; apply GlobalTheory.exists_gen_of_rigidified_of_flat_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIdentityPullbackDegeneration
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

theorem exists_gen_of_eq {X Y : Scheme.{0}} (L : LB X) {p q : Y ⟶ X} (h : q = p) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => q) (fun _ => n)),
      (∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → L.ι),
        gm r z (LB.wchart L (fun _ => q) j) (b.s j) = gm r z (LB.wchart L (fun _ => p) j) (a.s j)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by
  subst h
  exact ⟨a, fun _ _ _ _ => rfl, fun _ _ _ _ => rfl⟩

theorem exists_mapsAt_id {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X) (p : Y ⟶ X) (n : ℤ)
    (a : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p) (fun _ => n))) (ha : a.IsGen) :
    ∃ b : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => p ≫ F) (fun _ => n)),
      GeneratorPullback.MapsAt L L (J := PUnit) (fun _ => F) (isoPullId (idIso L) hF) p n a b ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), val b r z J = val a r z J := by
  obtain ⟨b, hb, hv⟩ := exists_gen_of_eq L (q := p ≫ F) (p := p) (by rw [hF, Category.comp_id]) n a
  refine ⟨b, fun jN jL => unit_ext fun y hy => ?_, hv⟩
  have hL : p y ∈ L.U jL := hy.2
  have hN : p y ∈ L.U (jN PUnit.unit) := by
    have := mem_pull.1 hy.1
    rw [hF] at this
    exact this
  have m₁ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : PUnit => p) jN := Set.mem_iInter.2 fun _ => hN
  have m₂ : (𝟙 Y : Y ⟶ Y) y ∈ LB.wchart L (fun _ : PUnit => p) (fun _ => jL) := Set.mem_iInter.2 fun _ => hL
  refine (gm_res _ y _ hy _).trans ((hb _ _ y jN).trans ((gen_trans ha (𝟙 Y) y m₁ m₂).trans ?_))
  refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (gm_res _ y _ hy _)))
  rw [trF, Fintype.prod_unique]
  refine congrArg (· ^ n) ((gm_pull (𝟙 Y) p y _ hy _).trans ?_)
  exact gw_isoPullId (idIso L) hF (𝟙 Y ≫ p) y (jN PUnit.unit) jL hN hL

theorem exists_isIdPull : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (W : (Sp R).Opens), genericPoint (Sp R) ∈ W → Nonempty (PsiOn D W) → ∃ hD : IsPullDeg (RingHom.id R) D D, IsIdPull hD := by
  rintro R _ _ D W hW ⟨ψ⟩
  have hs := specOf_id R
  have mR : IsMonHom (Iso.refl D.P.A).hom := by show IsMonHom (𝟙 _); infer_instance
  have gp : IsGrpPullback D.P.A D.P.A (specOf (RingHom.id R)) (Iso.refl D.P.A).hom.left :=
    (isGrpPullback_of_iso (Iso.refl D.P.A)).congr hs.symm rfl
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf (RingHom.id R)))
  have hF : e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ := he
  have hz : eSec D.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec D.P.A := by
    rw [hF, hs, Category.comp_id]; exact (Category.id_comp _).symm
  have hgen : ∀ z : Sp (FractionRing R), jK R z ∈ W := by
    intro z
    have : jK R z = genericPoint (Sp R) := by
      rw [genericPoint_eq_bot_of_affine]
      apply PrimeSpectrum.ext
      show Ideal.comap (algebraMap R (FractionRing R)) z.asIdeal = ⊥
      have hz0 : z.asIdeal = ⊥ := @Ideal.eq_bot_of_prime _ _ _ z.isPrime
      rw [hz0]
      exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective R _)
    rw [this]; exact hW
  have hr : Set.range (𝟙 (Sp (FractionRing R)) : _ ⟶ _) ⊆ Set.range (jK R ⁻¹ᵁ W).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hgen z
  let l := IsOpenImmersion.lift (jK R ⁻¹ᵁ W).ι (𝟙 _) hr
  have hl : l ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ := IsOpenImmersion.lift_fac _ _ _
  refine ⟨{ e := e, e_hom := me, w := isoPullId (idIso D.P.L) hF
            w_gen := (isGen_iff _).2 (isoPullId_pgen (idIso_isGen D.P.isLB) hF)
            he := hz
            w_rig := isoPullId_maps (idIso_maps (⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ : RigLB D.P.A)) hF hs hz
            xe := AddEquiv.refl _
            c_pr := fun x => by rw [hF, hs, Category.comp_id]; exact (Category.id_comp _).symm
            W := W, psiW := ψ, g := l ≫ jK R ∣_ W
            g_comm := by
              rw [hs, Category.comp_id]
              exact (Category.assoc _ _ _).trans ((congrArg (l ≫ ·) (morphismRestrict_ι (jK R) W)).trans
                ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ jK R) hl).trans (Category.id_comp _))))
            psi_pr := fun x => ?_ }, fun _ => rfl, hF, fun Y f y j k hj hk => ?_⟩
  · obtain ⟨b, hb, hv⟩ := exists_mapsAt_id hF (D.xK x) (-1) (D.psi x) (D.psi_gen x)
    refine ⟨b, hb, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    have c := val_corr hJ (ψ.psi_eq x) l
    have c₁ := val_pull hJ (ψ.psi x) (jK R ∣_ W) l
    have c₂ := val_pull hJ (D.psi x) (jK R ⁻¹ᵁ W).ι l
    have c₃ := val_pull hJ (ψ.psi x) (l ≫ jK R ∣_ W) (𝟙 _)
    refine (hv _ _ y J).trans (Eq.trans ?_ c₃.symm)
    refine (congrArg (fun r => val (D.psi x) r y J) hl).symm.trans (c₂.symm.trans (c.symm.trans (c₁.trans ?_)))
    exact congrArg (fun r => val (ψ.psi x) r y J) (Category.id_comp _).symm
  · exact gw_isoPullId (idIso D.P.L) hF f y j k hj hk

end GlobalTheory.TorsionFormCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUniformizationIdentityPullback
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

theorem mono_fst_thick {R : Type} [CommRing R] (I : Ideal R) (e : ℕ) (G : Over (Sp R)) :
    Mono (pullback.fst G.hom (thick R I e)) := by
  have : IsClosedImmersion (thick R I e) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  infer_instance

theorem corr_pullGen_of_pmaps {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {F : X ⟶ X} (hF : F = 𝟙 X)
    (w : LB.Iso L (L.pull F))
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j k : L.ι), f z ∈ L.U j → f z ∈ L.U k →
      gw w f z j k = gm f z _ (L.g j k))
    {K : Type} [Fintype K] {φ' : K → (Y' ⟶ X)} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {a : LB.Gen (LB.LinComb L φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y}
    (hψ : ∀ k, φ' k ≫ F = h ≫ φ k) (hm : PMaps w φ' φ ε a t h) :
    LB.Gen.Corr L _ _ _ _ a (LB.pullGen L _ _ t h) := by
  subst hF
  refine corr_of_val hL fun z J hJ => ?_
  have hk : ∀ k, (𝟙 Y' ≫ h) ≫ φ k = 𝟙 Y' ≫ φ' k := fun k => by
    rw [Category.assoc, ← hψ k, Category.comp_id]
  have hmem : ∀ k, (𝟙 Y' ≫ φ' k) z ∈ L.U (J (𝟙 Y' ≫ φ' k)) := fun k => hJ _
  have key := hm _ (𝟙 Y') z (fun k => J (𝟙 Y' ≫ φ' k)) (fun k => J (𝟙 Y' ≫ φ' k)) hmem hmem
  rw [Finset.prod_eq_one (fun k _ => by
    rw [hw _ _ z _ _ (hmem k) (hmem k), gm_self hL _ z (hmem k), one_zpow]), _root_.one_mul] at key
  rw [val_pull hJ, val_of t _ z J _ (fun k => congrArg J (hk k))]
  exact key.symm

theorem sameUnif_of_isPullUnif : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G G' : Over (Sp R)) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (ε : G' ≅ G) (hD : IsPullDeg (RingHom.id R) D.toPre D.toPre), IsIdPull hD → ∀ (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G) (U : Unif I D A G) (U' : Unif I D A G'), bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ε.hom.left → U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom → IsPullUnif (RingHom.id R) hD bc U U' → SameUnif ε U.toUnifPre U'.toUnifPre := by
  intro R _ _ I D A G G' _ _ _ _ ε hD hid bc U U' hF hgen H
  obtain ⟨hx, hΦ, hw₀⟩ := hid
  obtain ⟨wL, hg, he, hr, H⟩ := (isPullUnif_iff_stalks R R I I _ D D hD A A G G' bc U U').1 H
  have hr' := (maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
    (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).1 hr
  clear hr he
  generalize bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = F at wL hg hr' H hF
  subst hF
  refine ⟨hgen, wL, ⟨hg, ?_⟩, fun e => ?_⟩
  · have hs := specOf_id R
    rw [hs] at hr'
    exact hr'
  obtain ⟨h, hf, ⟨hp, ht⟩, hw⟩ := H e
  have hh : h = ((Over.pullback (thick R I e)).map ε.hom).left := by
    have := mono_fst_thick I e G
    rw [← cancel_mono (pullback.fst G.hom (thick R I e))]
    refine hf.trans ?_
    exact (pullback.lift_fst _ _ _).symm
  subst hh
  rw [hΦ, Category.comp_id] at hp
  have hpt : ∀ y, (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) y = y := fun y => by
    rw [hΦ]; rfl
  refine ⟨?_, fun χ => ?_, ?_⟩
  · ext1
    have := mono_fst_thick I e D.toPre.P.A
    rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e))]
    exact hp
  · obtain ⟨hψ, hm⟩ := ht χ
    rw [hx χ] at hψ hm
    exact corr_pullGen_of_pmaps D.toPre.P.isLB hΦ hD.w hw₀ hψ hm
  · intro Z r z jM jL jL' h₁ h₂ h₃
    have key := hw Z r z jM jM jL jL' (by rw [hpt]; exact h₁) h₁ h₂ h₃
    rw [hw₀ _ (r ≫ (U'.gt e).pG.left) z jM jM h₁ h₁, gm_self D.toPre.P.isLB (r ≫ (U'.gt e).pG.left) z h₁,
      _root_.one_mul] at key
    exact key

end GlobalTheory.TorsionFormCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DetCondOfEigenbasis
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PeriodPoint

variable {E : Type} [Field E] [NumberField E]

theorem exists_embedding {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) (τ : 𝓞 E →+* k) :
    ∃ τ₀ : E →+* ℂ, β.comp (τ₀.comp (algebraMap (𝓞 E) E)) = τ := by
  have : CharZero k := charZero_of_injective_ringHom β.injective
  have hτ : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  have hb : Function.Bijective fun φ : E →+* ℂ => β.comp φ :=
    (Fintype.bijective_iff_injective_and_card _).2 ⟨fun φ ψ h => RingHom.ext fun a => β.injective (DFunLike.congr_fun h a),
      by rw [NumberField.Embeddings.card, NumberField.Embeddings.card]⟩
  obtain ⟨τ₀, h⟩ := hb.2 (IsFractionRing.lift hτ)
  refine ⟨τ₀, RingHom.ext fun a => ?_⟩
  exact (DFunLike.congr_fun h _).trans (IsFractionRing.lift_algebraMap hτ a)

variable [IsCMField E] {H : Host E}

theorem detCond_of_eigenbasis
    (lie : ∀ (k : Type) [Field k] (O : Type) [CommRing O] (G : Over (Sp k)) [GrpObj G] (act : OAct O G) (n : ℕ) (v : Fin n → (epsR k ⟶ G)) (τs : Fin n → (O →+* k)), Smooth G.hom → IsLieBasis v → (∀ i a, (v i ≫ act.act a).left = spMap (epsScale (τs i a)) ≫ (v i).left) → ∀ τ : O →+* k, LieMult act (𝟙 (Sp k)) τ (Nat.card {i // τs i = τ}))
    (D : Datum H) (t : SAB H (Sp ℂ)) {g : ℕ} (ty : Fin g → (E →+* ℂ)) (hty : IsTypeFn H D.p D.q ty)
    (v : Fin g → (epsR ℂ ⟶ t.G)) (hv : IsLieBasis v)
    (heig : ∀ i (a : 𝓞 E), (v i ≫ t.act.act a).left = spMap (epsScale (ty i (a : E))) ≫ (v i).left)
    {k : Type} [Field k] [IsAlgClosed k] (β : ℂ →+* k) : DetCond D t.act (spMap β) (β H.rt0) := by
  obtain ⟨t', m⟩ : ∃ t' : SAB H (Sp k), Nonempty (SABMap t' t (spMap β)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap β) t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨m⟩ := m
  obtain ⟨v', hv', hφ⟩ := exists_isLieBasis_baseChange ℂ k β t.G t'.G m.cm.F m.cart t.semi.smooth g v hv
  have sc : ∀ c : k, spMap (epsScale c) ≫ spMap (algebraMap k (DualNumber k)) =
      spMap (algebraMap k (DualNumber k)) := fun c => by
    refine (Spec.map_comp _ _).symm.trans (congrArg Spec.map ?_)
    ext a <;> simp [epsScale, TrivSqZeroExt.algebraMap_eq_inl]
  have dm : ∀ c : ℂ, spMap (Chart.dualMapR β) ≫ spMap (epsScale c) =
      spMap (epsScale (β c)) ≫ spMap (Chart.dualMapR β) := fun c => by
    refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_comp _ _))
    ext a <;> simp [epsScale, Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  have key : ∀ τ₀ : E →+* ℂ, LieMult t.act (spMap β) (β.comp (τ₀.comp (algebraMap (𝓞 E) E)))
      (Nat.card {i // ty i = τ₀}) := fun τ₀ => by
    have h := lie k (𝓞 E) t'.G t'.act g v' (fun i => β.comp ((ty i).comp (algebraMap (𝓞 E) E))) t'.semi.smooth hv'
      (fun i a => m.cart.1.hom_ext ?_ ?_) (β.comp (τ₀.comp (algebraMap (𝓞 E) E)))
    · rw [LiePull.lieMult_pull _ _ _ t.G t'.G _ _ t.act t'.act m.cart m.act, Category.id_comp] at h
      convert h using 1
      refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ⟨fun e => by rw [e], fun e => ?_⟩)
      exact IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E))
        (RingHom.ext fun a => β.injective (DFunLike.congr_fun e a))
    · have e := heig i a
      rw [Over.comp_left] at e
      rw [Over.comp_left, Category.assoc, m.act, ← Category.assoc, hφ, Category.assoc, e, Category.assoc, hφ,
        ← Category.assoc, dm, Category.assoc]
    · rw [Over.w, Category.assoc, Over.w]
      exact (sc _).symm
  intro τ
  obtain ⟨τ₀, rfl⟩ := exists_embedding β τ
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← (hty τ₀).1 (β.injective h)]; exact key τ₀
  · rw [← (hty τ₀).2 fun e => h (congrArg β e)]; exact key τ₀

theorem exists_fibre_unif {S : Scheme.{0}} (t : SAB H (Sp ℂ)) (t₀ : SAB H S) (y : Sp ℂ ⟶ S) (m : SABMap t t₀ y)
    {L : LB t.G.left} {g : ℕ} (u : HolUnif t.G L g) (h₁ : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (h₂ : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) :
    ∃ e : (Fin g → ℂ) → (Over.mk y ⟶ t₀.G), (∀ z, (e z).left = (u.ex z).left ≫ m.cm.F) ∧
      ((∀ z w, e (z + w) = e z * e w) ∧ Function.Surjective e ∧ IsHolTo Set.univ (fun z => (e z).left) ∧
        (∀ w, ∃! v : epsPt y ⟶ t₀.G, IsDerivAt0 (fun z => (e z).left) w v.left) ∧
        (∀ v : epsPt y ⟶ t₀.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (e 0).left →
          ∃! w, IsDerivAt0 (fun z => (e z).left) w v.left)) ∧
      (∀ z, e z = 1 ↔ u.ex z = 1) ∧
      (∀ a z w, u.ex w = u.ex z ≫ t.act.act a → e w = e z ≫ t₀.act.act a) ∧
      ∀ (k : ℤ) z w c, Out.WeilIs t.G t.PP.L k (u.ex z) (u.ex w) c → Out.WeilIs t₀.G t₀.PP.L k (e z) (e w) c := by
  obtain ⟨φ, hφ⟩ := LiePull.exists_pushEquiv m.cart (𝟙_ (Over (Sp ℂ))) y (Category.id_comp y).symm
  obtain ⟨ψ, hψ⟩ := LiePull.exists_pushEquiv m.cart (epsR ℂ) (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) rfl
  have hee : (fun z => (φ (u.ex z)).left) = fun z => (u.ex z).left ≫ m.cm.F := funext fun z => hφ _
  have hol : IsHolTo Set.univ (fun z => (u.ex z).left ≫ m.cm.F) := fun U f => by
    obtain ⟨a, b⟩ := u.hol (m.cm.F ⁻¹ᵁ U) ((m.cm.F.app U).hom f)
    simp only [← valAt'_comp, Set.mem_univ, true_and]
    exact ⟨a, b⟩
  have key : ∀ (w : Fin g → ℂ) (v : epsR ℂ ⟶ t.G), IsTangent v ∧ u.IsDiff w v ↔
      IsDerivAt0 (fun z => (φ (u.ex z)).left) w (ψ v).left := fun w v => by
    have e₀ : IsTangent v ∧ u.IsDiff w v ↔ IsDerivAt0 (fun z => (u.ex z).left) w v.left :=
      and_congr (by rw [IsTangent, ← TangentOrigin.ex_zero_left u]) Iff.rfl
    rw [e₀, hee, hψ]
    exact ⟨fun h => FibreDeriv.isDerivAt0_comp h _,
      fun h => FibreDeriv.isDerivAt0_of_isPullback m.cart.1 (fun z => Over.w (u.ex z)) hol (Over.w v) h⟩
  refine ⟨fun z => φ (u.ex z), fun z => hφ _, ⟨fun z w => by simp only [u.ex_add, map_mul],
    φ.surjective.comp u.ex_onto, by rw [hee]; exact hol, fun w => ?_, fun v hv => ?_⟩,
    fun z => φ.map_eq_one_iff, fun a z w h => Over.OverMorphism.ext ?_, fun k z w c h => ?_⟩
  · obtain ⟨v, hv, huniq⟩ := h₂ w
    refine ⟨ψ v, (key w v).1 hv, fun v' hv' => ?_⟩
    obtain ⟨v', rfl⟩ := ψ.surjective v'
    rw [huniq v' ((key w v').2 hv')]
  · obtain ⟨v, rfl⟩ := ψ.surjective v
    have ht : IsTangent v := by
      rw [IsTangent, ← TangentOrigin.ex_zero_left u]
      refine m.cart.1.hom_ext (by rw [Category.assoc, ← hψ, hv, hφ]) ?_
      refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w v)).trans (Eq.trans ?_ (Over.w (u.ex 0)).symm))
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      ext a
      simp [TrivSqZeroExt.algebraMap_eq_inl]
    simp only [← key, ht, true_and]
    exact h₁ v ht
  · rw [Over.comp_left, hφ, hφ, h, Over.comp_left, Category.assoc, m.act, Category.assoc]
  · obtain ⟨ω, hω, -⟩ := m.lin
    have H := fun (y' : Sp ℂ ⟶ S) (hy' : y' = (𝟙_ (Over (Sp ℂ))).hom ≫ y) (x₀ y₀ : Over.mk y' ⟶ t₀.G)
        (hx : x₀.left = (u.ex z).left ≫ m.cm.F) (hy : y₀.left = (u.ex w).left ≫ m.cm.F) =>
      show Out.WeilIs t₀.G t₀.PP.L k x₀ y₀ c by
        subst hy'
        exact (weilIs_grpPullback_of_comm' _ _ t₀.G t.G y _ _ _ t₀.PP.isLB t.PP.isLB m.cart ⟨ω, hω⟩ _ k _ _ x₀ y₀ c
          hx hy).1 h
    exact H y (Category.id_comp y).symm _ _ (hφ _) (hφ _)

theorem exists_halfLevel {D : Datum H} (l : Level H) {Q : Type} [Group Q] (ev : D.La → Q)
    (hadd : ∀ a b, ev (a + b) = ev a * ev b) (hker : ∀ b, ev (l.M • b) = 1) :
    ∃ κ : D.La → Q, (∀ a b, κ (a + b) = κ a * κ b) ∧ (∀ a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), κ a = 1) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), κ a = ev a := by
  obtain ⟨v, hv, u, hu, huv⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have hM : ∀ a ∈ (l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) • (⊤ : Submodule (𝓞 E) D.La), ev a = 1 := fun a ha => by
    rw [l.prod, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists] at ha
    obtain ⟨b, -, rfl⟩ := ha
    rw [Nat.cast_smul_eq_nsmul, hker]
  refine ⟨fun a => ev (u • a), fun a b => by simp only [smul_add, hadd], fun a ha => hM _ ?_, fun a ha => ?_⟩
  · rw [mul_comm, Submodule.mul_smul]
    exact Submodule.smul_mem_smul hu ha
  · have h : ev (v • a) = 1 := hM _ (by rw [Submodule.mul_smul]; exact Submodule.smul_mem_smul hv ha)
    conv_rhs => rw [← one_smul (𝓞 E) a, ← huv, add_smul, hadd, h, _root_.one_mul]

end GlobalTheory.PeriodPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.PullPointIdentityDegeneration
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TorsionFormCompare
open scoped CategoryTheory.Obj

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

theorem pmaps_self_of_tautological {X Y : Scheme.{0}} {L : LB X} {F : X ⟶ X} (hF : F = 𝟙 X)
    (w : LB.Iso L (L.pull F))
    (hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) (j k : L.ι), f z ∈ L.U j → f z ∈ L.U k →
      gw w f z j k = gm f z _ (L.g j k))
    {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    PMaps w φ φ ε t t (𝟙 Y) := by
  subst hF
  intro Z r z p q hp hq
  have hp' : ∀ k, φ k (r z) ∈ L.U (p k) := hp
  rw [Category.comp_id, gen_trans ht r z (j := p) (j' := q) (Set.mem_iInter.2 hp') (Set.mem_iInter.2 hq), trF]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by rw [hw Z (r ≫ φ k) z (p k) (q k) (hp' k) (hq k)]

end GlobalTheory.TorsionFormCompare
end
end
