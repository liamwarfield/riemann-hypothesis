module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticModelAffineCoverRadical

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListFieldExtensionEqUpToPerm
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListFieldExtensionEqUpToPerm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UMin.SymCmp

theorem grpPullback_id {S : Scheme.{0}} (G : Over S) [GrpObj G] : IsGrpPullback G G (𝟙 S) (𝟙 G.left) := by
  refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
  let ρ : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have ex : x₀ = ρ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  have ey : y₀ = ρ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
  rw [ex, ey, ← MonObj.comp_mul]
  exact (Category.id_comp _).trans (Category.comp_id _).symm

theorem spMap_comp_ringHom {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem sec_eq_of_f {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_pullS {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq_of_f (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem thList_ext_perm : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (K F : Type) [Field K] [Field F] (i : R →+* K) (i' : R →+* F) (φ : K →+* F), φ.comp i = i' → ∀ (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G)) (c : Fin N → K) (pt' : Fin N → (Over.mk (spMap i' ≫ x) ⟶ G)) (c' : Fin N → F), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt c → ThList G L ρ m (spMap i' ≫ x) (SecAt.pull G L θ i') pt' c' → ∃ σ : Equiv.Perm (Fin N), ∀ b, c' b = φ (c (σ b)) := by
  intro S G _ _ L ρ hL hρ g m R _ x θ hm hu hP K F _ _ i i' φ hi N pt c pt' c' H H'
  subst hi
  obtain ⟨p₁, -, h₁⟩ := GlobalTheory.T.isThetaConstantListOfFibre_pullback_field_extension S G L ρ hL hρ m N K F φ (spMap i ≫ x) (SecAt.pull G L θ i) pt c H
  simp only [SecAt.pull] at h₁
  rw [pullS_pullS G hL] at h₁
  have ey : spMap φ ≫ spMap i ≫ x = spMap (φ.comp i) ≫ x := by
    rw [← Category.assoc, spMap_comp_ringHom]
  have key : ∀ {y y' : Sp F ⟶ S} (e : y = y') (u : Over.mk y ⟶ Over.mk x) (u' : Over.mk y' ⟶ Over.mk x),
      u.left = u'.left → ∀ {p : Fin N → (Over.mk y ⟶ G)} {d : Fin N → F},
      ThList G L ρ m y (VVRank.pullS G _ u θ) p d →
      ∃ p' : Fin N → (Over.mk y' ⟶ G), ThList G L ρ m y' (VVRank.pullS G _ u' θ) p' d := by
    intro y y' e u u' hu p d h
    subst e
    obtain rfl : u = u' := Over.OverMorphism.ext hu
    exact ⟨p, h⟩
  obtain ⟨q₁, H₁⟩ := key ey _ (Over.homMk (spMap (φ.comp i)) rfl : Over.mk (spMap (φ.comp i) ≫ x) ⟶ Over.mk x)
    (by simp only [Over.comp_left, Over.homMk_left]; rw [spMap_comp_ringHom]) h₁
  have hPy : PolFib G L g (spMap (φ.comp i) ≫ x) :=
    (GlobalTheory.T.principallyPolarisedFibre_iff_of_grpPullback S S G L G L (𝟙 S) (𝟙 G.left) hL hL (grpPullback_id G)
      (GlobalTheory.ThetaAffineGlue.lbIso_pull_id hL) g R x).2 F (φ.comp i) hP
  have hmF : (m : F) ≠ 0 := by
    rw [← map_natCast (φ.comp i) m]
    exact (hu.map (φ.comp i)).ne_zero
  exact (GlobalTheory.T.thetaConstantLists_unique_up_to_perm_scalar S G L ρ hL hρ g m m N N F (spMap (φ.comp i) ≫ x) hm hmF hm hmF hPy).1 _ q₁ pt' _ c' H₁ H'

end GlobalTheory.UMin.SymCmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantListFieldExtensionEqUpToPermStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstantList_fieldExtension_eq_up_to_perm : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (K F : Type) [Field K] [Field F] (i : R →+* K) (i' : R →+* F) (φ : K →+* F), φ.comp i = i' → ∀ (N : ℕ) (pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G)) (c : Fin N → K) (pt' : Fin N → (Over.mk (spMap i' ≫ x) ⟶ G)) (c' : Fin N → F), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt c → ThList G L ρ m (spMap i' ≫ x) (SecAt.pull G L θ i') pt' c' → ∃ σ : Equiv.Perm (Fin N), ∀ b, c' b = φ (c (σ b)) := by
  first | exact @GlobalTheory.UMin.SymCmp.thList_ext_perm | exact GlobalTheory.UMin.SymCmp.thList_ext_perm | (intros; apply GlobalTheory.UMin.SymCmp.thList_ext_perm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFunctionsFiniteFlatCover
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalThetaConstantsLocalisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalThetaConstantsLocalisation
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.ThLocal
open GlobalTheory.ThetaPtMove GlobalTheory.ThetaPtExist

theorem sec_eq {X : Scheme.{0}} {M : LB X} {s s' : LB.Sec M} (h : ∀ j, s.f j = s'.f j) : s = s' := by
  cases s; cases s'
  simp only [LB.Sec.mk.injEq]
  exact funext h

theorem pullS_comp {S : Scheme.{0}} (G : Over S) [GrpObj G] {L : LB G.left} (hL : L.IsLB) (a : ℤ) {T T' T'' : Over S}
    (h : T' ⟶ T) (h' : T'' ⟶ T') (s : LB.Sec (LPow G L a T)) :
    VVRank.pullS G a h' (VVRank.pullS G a h s) = VVRank.pullS G a (h' ≫ h) s := by
  refine sec_eq (sec_ext_val hL (fun y J hJ => ?_))
  refine (VVRank.sv_pullS G a h' _ (𝟙 _) y hJ).trans ((VVRank.sv_pullS G a h s _ y hJ).trans ?_)
  refine Eq.trans ?_ (VVRank.sv_pullS G a (h' ≫ h) s (𝟙 _) y hJ).symm
  rw [MonoidalCategory.comp_whiskerRight, Over.comp_left, Category.assoc]

theorem exists_local : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x) (R₁ : Type) [CommRing R₁] [Algebra R R₁] [IsNoetherianRing R₁] (N : ℕ) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Odd m → IsUnit (m : R) → PolFib G L g x → (∀ a, q a ^ (m ^ 2) = 1) → ∀ p : Ideal R₁, p.IsPrime → ∃ f ∉ p, ∃ c : Fin N → Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K) (a : Fin N) (pt : Over.mk (spMap ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap (j.comp (algebraMap R₁ (Localization.Away f))) ≫ (q a).left → ThG G L ρ m (SecAt.pull G L θ ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁))) pt (fn (j (c a))) := by
  intro S G _ _ L ρ hL hρ g m R _ _ x θ R₁ _ _ _ N q hm hmu hP hq p hp
  obtain ⟨P, α, -, hpb, w, hw⟩ := hP
  have hL₁ := P.isLB
  haveI := P.isAb.comm
  obtain ⟨ρ₁, hρ₁, hr⟩ := exists_rigidificationPullbackCompatibleIso hpb hw hL hL₁ hρ
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  have cg := GlobalTheory.AbLaw.CubeAssembly.cube_gen
  have neg := GlobalTheory.exists_gen_negLB hG
  obtain ⟨α₀, hα₀⟩ := (GlobalTheory.MulPull.mulPull_of_cube_of_symm cg neg).1 (Sp R) P m
  have sym := (GlobalTheory.symLift_odd hG (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube cg).1).2.2 neg).1
  let T : Over (Sp R) := Over.mk (spMap (algebraMap R R₁))
  let T₁ : Over S := Over.mk (spMap (algebraMap R R₁) ≫ x)
  have hτ₁ : 𝟙 T.left ≫ T₁.hom = T.hom ≫ x := Category.id_comp _
  choose y hy hym using fun a => exists_torsion_down hpb (𝟙 T.left) (T₀ := T₁) hτ₁ (q a) (hq a)
  let pt₀ : T.left := (⟨p, hp⟩ : PrimeSpectrum R₁)
  choose V hV U hU using fun a => (sym (Sp R) P (m ^ 2) hm.pow T (y a) (hym a)).1 pt₀
  have hO : IsOpen (⋂ a, ((V a : T.left.Opens) : Set T.left)) := isOpen_iInter_of_finite fun a => (V a).2
  obtain ⟨_, ⟨f, rfl⟩, hf, hfO⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open
    (show pt₀ ∈ ⋂ a, ((V a : T.left.Opens) : Set T.left) from Set.mem_iInter.2 hV) hO
  refine ⟨f, hf, ?_⟩
  let Lf := Localization.Away f
  let af : R₁ →+* Lf := algebraMap R₁ Lf
  let i_f : R →+* Lf := af.comp (algebraMap R R₁)
  let Tf : Over (Sp R) := Over.mk (spMap i_f)
  let β : Tf ⟶ T := Over.homMk (spMap af) (by
    show spMap af ≫ spMap (algebraMap R R₁) = spMap (af.comp (algebraMap R R₁))
    exact (spMap_comp _ _).symm)
  have hrange : ∀ a, Set.range (spMap af) ⊆ Set.range (V a).ι := by
    intro a
    rintro _ ⟨p', rfl⟩
    rw [Scheme.Opens.range_ι]
    exact Set.mem_iInter.1 (hfO ((PrimeSpectrum.localization_away_comap_range Lf f).le ⟨p', rfl⟩)) a
  have hsym : ∀ a, ∃ θ' : ThetaGrp P.A P.L ((m : ℤ) ^ 2) Tf,
      SymLift P.A P.L ((m : ℤ) ^ 2) (m ^ 2) (β ≫ y a) θ' := by
    intro a
    let u := IsOpenImmersion.lift (V a).ι (spMap af) (hrange a)
    have hu : u ≫ (V a).ι = spMap af := IsOpenImmersion.lift_fac _ _ _
    let r : Tf ⟶ overRes (V a) := Over.homMk u (by
      show u ≫ (V a).ι ≫ T.hom = Tf.hom
      rw [← Category.assoc, hu]
      exact Over.w β)
    obtain ⟨θ', h'⟩ := GlobalLift.exists_symLift_pull hL₁ r (hU a)
    have e : r ≫ overResι (V a) = β := Over.OverMorphism.ext hu
    rw [← Category.assoc, e] at h'
    rw [← Nat.cast_pow]
    exact ⟨θ', h'⟩
  let T₀ : Over S := Over.mk (spMap i_f ≫ x)
  have hτ : 𝟙 Tf.left ≫ T₀.hom = Tf.hom ≫ x := Category.id_comp _
  obtain ⟨th, hth⟩ := exists_secRel hpb (𝟙 Tf.left) (T₀ := T₀) hτ hw hL hL₁ (SecAt.pull G L θ i_f)
  have e₁ : (snd Tf P.A).left ≫ (mulA P.A m).left = (snd Tf P.A ^ m).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨αf, hαf, -⟩ := exists_gen hL₁ (φ' := ![(snd Tf P.A).left, (snd Tf P.A ^ m).left]) (ε' := ![(m : ℤ) ^ 2, -1])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => f q ^ ((m : ℤ) ^ 2)) (Category.comp_id _)
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A m).left] ![(m : ℤ) ^ 2, -1] α₀ (snd Tf P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨τf, hτf, -⟩ := exists_gen hL₁ (φ' := fun _ : Fin 1 => (1 : Tf ⟶ P.A).left) (ε' := fun _ => (m : ℤ) ^ 2)
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ₁ (toUnit Tf).left) (m ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ₁ _) _)
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL₁ (mulT P.A Tf m) (snd Tf P.A ^ m) (lift_snd _ _)
    ((m : ℤ) ^ 2) 1 αf hαf th
  choose Uf hUf using hsym
  choose s₂ hs₂ using fun a => ThetaPtExist.exists_isTwistPull hL₁ (translT P.A (Uf a).pt) (translPt P.A (Uf a).pt)
    (lift_snd _ _) ((m : ℤ) ^ 2) ((m : ℤ) ^ 2) (Uf a).φ (Uf a).isGen s₁
  choose wv hwv using fun a => ThetaPtExist.exists_isValueAt hL₁ (s₂ a) 1 τf hτf
  have hyf : ∀ a, (β ≫ y a) ^ (m ^ 2) = 1 := fun a => by rw [← MonObj.comp_pow, hym a, MonObj.comp_one]
  obtain ⟨e, he⟩ := exists_thG hL₁ hρ₁ m ((m : ℤ) ^ 2) (Nat.cast_pow m 2).symm hyf (th := th) (α := αf)
    hαf hτf hs₁ hUf hs₂ hwv
  refine ⟨fun a => (Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a), ?_⟩
  intro K _ j a pt hpt
  clear hUf hs₂ hwv hs₁ sym hU hV hfO hO cg neg hG hrange
  let ξ : T₀ ⟶ T₁ := Over.homMk (spMap af) (by
    show spMap af ≫ spMap (algebraMap R R₁) ≫ x = spMap (af.comp (algebraMap R R₁)) ≫ x
    rw [← Category.assoc, ← spMap_comp])
  have hx₀ : 𝟙 Tf.left ≫ (ξ ≫ q a).left = (β ≫ y a).left ≫ α := by
    have h := hy a
    rw [Category.id_comp] at h
    rw [Category.id_comp, Over.comp_left, Over.comp_left, Category.assoc, ← h]
    rfl
  have hn₀ : (ξ ≫ q a) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, hq a, MonObj.comp_one]
  have up := ThG.up hpb (T := Tf) (T₀ := T₀) (𝟙 Tf.left) hτ hw hL hL₁ hr hx₀ hn₀ hth (he a)
  let δ : Over.mk (spMap ((j.comp af).comp (algebraMap R R₁)) ≫ x) ⟶ T₀ := Over.homMk (spMap j) (by
    show spMap j ≫ spMap (af.comp (algebraMap R R₁)) ≫ x = spMap ((j.comp af).comp (algebraMap R R₁)) ≫ x
    rw [← Category.assoc, ← spMap_comp])
  have down := ThPull.thG_pull hL hρ δ up
  have ept : pt = δ ≫ ξ ≫ q a := by
    refine Over.OverMorphism.ext ?_
    rw [hpt, Over.comp_left, Over.comp_left, ← Category.assoc]
    exact congrArg (· ≫ (q a).left) (spMap_comp af j)
  have eθ : SecAt.pull G L θ ((j.comp af).comp (algebraMap R R₁)) = VVRank.pullS G _ δ (SecAt.pull G L θ i_f) := by
    unfold SecAt.pull
    rw [pullS_comp G hL]
    congr 1
    refine Over.OverMorphism.ext ?_
    exact spMap_comp i_f j
  have ec : δ.left.appTop.hom ((inv (𝟙 Tf.left)).appTop.hom ((e : Γ(Tf.left, ⊤)) * wv a)) =
      fn (j ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a))) := by
    have h1 : (inv (𝟙 Tf.left)).appTop.hom ((e : Γ(Tf.left, ⊤)) * wv a) =
        fn ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a)) := by
      simp only [IsIso.inv_id, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply]
      exact ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom_inv_id_apply _).symm
    rw [h1]
    exact (congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of Lf)).hom.hom ((e : Γ(Tf.left, ⊤)) * wv a)))
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom j))).symm
  rw [ept, eθ, ← ec]
  exact down

end GlobalTheory.UMin.ThLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalThetaConstantsLocalisationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_local_thetaConstants_localisation : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x) (R₁ : Type) [CommRing R₁] [Algebra R R₁] [IsNoetherianRing R₁] (N : ℕ) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Odd m → IsUnit (m : R) → PolFib G L g x → (∀ a, q a ^ (m ^ 2) = 1) → ∀ p : Ideal R₁, p.IsPrime → ∃ f ∉ p, ∃ c : Fin N → Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K) (a : Fin N) (pt : Over.mk (spMap ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap (j.comp (algebraMap R₁ (Localization.Away f))) ≫ (q a).left → ThG G L ρ m (SecAt.pull G L θ ((j.comp (algebraMap R₁ (Localization.Away f))).comp (algebraMap R R₁))) pt (fn (j (c a))) := by
  first | exact @GlobalTheory.UMin.ThLocal.exists_local | exact GlobalTheory.UMin.ThLocal.exists_local | (intros; apply GlobalTheory.UMin.ThLocal.exists_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatCoverMSqTorsionSections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatCoverMSqTorsionSections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.TorsionList

theorem pow_exp (n k : ℕ) (c : Multiplicative (Fin k → ZMod n)) : c ^ n = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  simp

theorem spMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap]

theorem pushHom_bij {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Bijective (pushHom h T) := by
  refine ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) ?_), fun y => ?_⟩
  · exact (Over.w x).trans (Over.w y).symm
  · exact ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem spMap_comp_assoc {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D] {X : Scheme.{0}}
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (y : Sp A ⟶ X) :
    spMap (h.comp g) ≫ spMap f ≫ y = spMap h ≫ spMap (g.comp f) ≫ y := by
  simp only [spMap_comp, Category.assoc]

abbrev lft {S X : Scheme.{0}} {G : Over S} {a : X ⟶ S} (p : Over.mk a ⟶ G) : X ⟶ G.left := p.left

theorem pow_lft_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b)
    (x : Over.mk a ⟶ G) (y : Over.mk b ⟶ G) (hx : lft x = lft y) (n : ℕ) : lft (x ^ n) = lft (y ^ n) := by
  subst h
  rw [Over.OverMorphism.ext hx]

theorem one_lft_congr {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) :
    lft (1 : Over.mk a ⟶ G) = lft (1 : Over.mk b ⟶ G) := by
  subst h
  rfl

theorem transport {S X : Scheme.{0}} {G : Over S} {a b : X ⟶ S} (h : a = b) (p : Over.mk b ⟶ G) :
    ∃ p' : Over.mk a ⟶ G, lft p' = lft p := by
  subst h
  exact ⟨p, rfl⟩

theorem lft_pushHom {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
    {φ : A'.left ⟶ A.left} (h : IsGrpPullback A' A f φ) {X : Scheme.{0}} (t : X ⟶ S') (y : Over.mk t ⟶ A') :
    lft (pushHom h (Over.mk t) y) = y.left ≫ φ := rfl

theorem toUnit_mk_left {X Y : Scheme.{0}} (f : Y ⟶ X) : (toUnit (Over.mk f)).left = f :=
  (Category.comp_id _).symm.trans (Over.w (toUnit (Over.mk f)))

theorem toUnit_left {X : Scheme.{0}} (T : Over X) : (toUnit T).left = T.hom :=
  (Category.comp_id _).symm.trans (Over.w (toUnit T))

theorem exists_cover_torsion_list : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ (∀ a, q a ^ (m ^ 2) = 1) ∧ ∀ (K : Type) [Field K] (i₁ : R₁ →+* K) (pt : Fin N → (Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G)), (∀ a, (pt a).left = spMap i₁ ≫ (q a).left) → Function.Injective pt ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i' : K →+* K') (p : Over.mk (spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i' ≫ (pt a).left := by
  intro S G _ _ L g m N R _ _ x hm hmu hN hP
  obtain ⟨P, α, hg, hp, -⟩ := hP
  haveI := P.isAb.comm
  have hm0 : m ≠ 0 := by rintro rfl; exact absurd hm (by decide)
  haveI : NeZero (m ^ 2) := ⟨pow_ne_zero _ hm0⟩
  have hsm : SmoothOfRelativeDimension g P.A.hom := hg ▸ P.smoothDim
  have hu : IsUnit (((m ^ 2 : ℕ)) : R) := by rw [Nat.cast_pow]; exact hmu.pow 2
  obtain ⟨R₁, _, _, ⟨hfin, -, hff⟩, H⟩ :=
    GlobalTheory.TorsionCover.exists_torsion_basis_cover R P.A g (m ^ 2) P.isAb hsm hu
  let b := spMap (algebraMap R R₁)
  let A₁ := (Over.pullback b).obj P.A
  haveI : IsCommMonObj A₁ := Functor.isCommMonObj_obj
  have h₁ := isGrpPullback_pullback P.A b
  obtain ⟨ψ, hψ⟩ := H A₁ _ h₁
  have hc := h₁.comp hp
  have hcard : Fintype.card (Multiplicative (Fin (2 * g) → ZMod (m ^ 2))) = N := by
    rw [hN]
    simp [Fintype.card_fun, ZMod.card, ← pow_mul]
    ring_nf
  let e := (Fintype.equivFinOfCardEq hcard).symm
  let U : Over.mk (b ≫ x) ⟶ Over.mk ((𝟙_ (Over (Sp R₁))).hom ≫ b ≫ x) := Over.homMk (𝟙 _) (by simp)
  let Q := (preHom (G := G) U).comp ((pushHom hc (𝟙_ (Over (Sp R₁)))).comp ψ)
  have hQ : ∀ c, (Q c).left = (ψ c).left ≫ pullback.fst P.A.hom b ≫ α := fun c => by
    simp [Q, U, pushHom, pushPt, preHom]
  refine ⟨R₁, inferInstance, inferInstance, fun a => Q (e a), hfin, hff, fun a => by
    rw [← map_pow, pow_exp, map_one], ?_⟩
  intro K _ i₁ pt hpt
  have key : ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R₁) c d,
      t ≫ (Q c).left = t ≫ (Q d).left → c = d := by
    intro k _ _ t c d h
    have hinj : Function.Injective ((preHom (G := A₁) (toUnit (Over.mk t))).comp ψ) := by
      rw [injective_iff_map_eq_one]
      exact fun c hc => (hψ k t).2 c hc
    apply hinj
    apply Over.OverMorphism.ext
    show (toUnit (Over.mk t) ≫ ψ c).left = (toUnit (Over.mk t) ≫ ψ d).left
    rw [Over.comp_left, Over.comp_left, toUnit_left]
    apply hc.1.hom_ext
    · rw [hQ, hQ] at h
      simpa [Category.assoc] using h
    · have e1 := Over.w (ψ c)
      have e2 := Over.w (ψ d)
      simp only [Category.assoc]
      erw [e1, e2]
  refine ⟨fun a a' h => ?_, ?_⟩
  · have h' := congrArg (fun z => z.left) h
    simp only [hpt] at h'
    let k := AlgebraicClosure K
    have := key k (spMap ((algebraMap K k).comp i₁)) (e a) (e a') (by
      rw [spMap_comp, Category.assoc, Category.assoc]; exact congrArg (spMap (algebraMap K k) ≫ ·) h')
    exact e.injective this
  · intro K' _ _ i' p hp2
    have ht : spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x = spMap (i'.comp i₁) ≫ b ≫ x :=
      (spMap_comp_assoc (algebraMap R R₁) i₁ i' x).symm
    obtain ⟨p', hp'⟩ := transport ht.symm p
    obtain ⟨p₁, hp₁⟩ := (pushHom_bij hc (Over.mk (spMap (i'.comp i₁)))).2 p'
    have hk : p₁ ^ (m ^ 2) = 1 := by
      apply (pushHom_bij hc _).1
      rw [map_pow, hp₁, map_one]
      apply Over.OverMorphism.ext
      change lft _ = lft _
      rw [pow_lft_congr ht.symm p' p hp', hp2]
      exact one_lft_congr ht
    obtain ⟨c, rfl⟩ := ((hψ K' _).1 p₁).1 hk
    refine ⟨e.symm c, ?_⟩
    rw [hpt]
    simp only [Equiv.apply_symm_apply]
    change lft p = _
    have h2 := congrArg lft hp₁
    rw [← hp', ← h2, lft_pushHom, hQ, Over.comp_left, toUnit_mk_left, spMap_comp]
    simp only [Category.assoc]

end GlobalTheory.UMin.TorsionList
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteFlatCoverMSqTorsionSectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_flat_cover_m_sq_torsion_sections : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (q : Fin N → (Over.mk (spMap (algebraMap R R₁) ≫ x) ⟶ G)), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ (∀ a, q a ^ (m ^ 2) = 1) ∧ ∀ (K : Type) [Field K] (i₁ : R₁ →+* K) (pt : Fin N → (Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G)), (∀ a, (pt a).left = spMap i₁ ≫ (q a).left) → Function.Injective pt ∧ ∀ (K' : Type) [Field K'] [IsAlgClosed K'] (i' : K →+* K') (p : Over.mk (spMap i' ≫ spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), p ^ (m ^ 2) = 1 → ∃ a, p.left = spMap i' ≫ (pt a).left := by
  first | exact @GlobalTheory.UMin.TorsionList.exists_cover_torsion_list | exact GlobalTheory.UMin.TorsionList.exists_cover_torsion_list | (intros; apply GlobalTheory.UMin.TorsionList.exists_cover_torsion_list <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingElementOfLocalFieldPointValues
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingElementOfLocalFieldPointValues
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem glue_field_points (R : Type) [CommRing R]
    (P : (K : Type) → [Field K] → (R →+* K) → K → Prop)
    (huniq : ∀ (K : Type) [Field K] (i : R →+* K) (u v : K), P K i u → P K i v → u = v)
    (hloc : ∀ p : Ideal R, p.IsPrime → ∃ f ∉ p, ∃ c : Localization.Away f,
      ∀ (K : Type) [Field K] (j : Localization.Away f →+* K),
        P K (j.comp (algebraMap R (Localization.Away f))) (j c)) :
    ∃ c : R, ∀ (K : Type) [Field K] (i : R →+* K), P K i (i c) := by
  classical
  have hloc' : ∀ k : {p : Ideal R // p.IsPrime}, ∃ f ∉ k.1, ∃ c : Localization.Away f,
      ∀ (K : Type) [Field K] (j : Localization.Away f →+* K),
        P K (j.comp (algebraMap R (Localization.Away f))) (j c) := fun k => hloc k.1 k.2
  choose f hf c hc using hloc'
  have hsurj : ∀ k : {p : Ideal R // p.IsPrime}, ∃ (a : R) (n : ℕ),
      c k * algebraMap R _ (f k ^ n) = algebraMap R _ a := by
    intro k
    obtain ⟨n, a, h⟩ := IsLocalization.Away.surj (f k) (c k)
    exact ⟨a, n, by rw [map_pow]; exact h⟩
  choose a n ha using hsurj

  have key : ∀ (K : Type) [Field K] (i : R →+* K) (k : {p : Ideal R // p.IsPrime}),
      i (f k) ≠ 0 → ∃ v, P K i v ∧ v * i (f k) ^ n k = i (a k) := by
    intro K _ i k hk
    let j : Localization.Away (f k) →+* K :=
      IsLocalization.Away.lift (f k) (isUnit_iff_ne_zero.mpr hk)
    have hj : j.comp (algebraMap R _) = i := by first | exact IsLocalization.Away.lift_comp _ | exact IsLocalization.lift_comp _
    refine ⟨j (c k), ?_, ?_⟩
    · have := hc k K j
      rwa [hj] at this
    · have h2 := congrArg j (ha k)
      rw [map_mul, ← RingHom.comp_apply, ← RingHom.comp_apply, hj, map_pow] at h2
      exact h2

  have hnil : ∀ k l : {p : Ideal R // p.IsPrime},
      IsNilpotent (f k * f l * (a k * f l ^ n l - a l * f k ^ n k)) := by
    intro k l
    rw [← mem_nilradical, nilradical_eq_sInf, Ideal.mem_sInf]
    intro q hq
    haveI : q.IsPrime := hq
    by_cases hk : f k ∈ q
    · exact q.mul_mem_right _ (q.mul_mem_right _ hk)
    by_cases hl : f l ∈ q
    · exact q.mul_mem_right _ (q.mul_mem_left _ hl)
    apply q.mul_mem_left
    have hker : RingHom.ker (algebraMap R q.ResidueField) = q := Ideal.ker_algebraMap_residueField q
    have hik : algebraMap R q.ResidueField (f k) ≠ 0 := fun h => hk (hker ▸ RingHom.mem_ker.mpr h)
    have hil : algebraMap R q.ResidueField (f l) ≠ 0 := fun h => hl (hker ▸ RingHom.mem_ker.mpr h)
    obtain ⟨v, hv, hv'⟩ := key _ (algebraMap R q.ResidueField) k hik
    obtain ⟨w, hw, hw'⟩ := key _ (algebraMap R q.ResidueField) l hil
    have hvw := huniq _ _ v w hv hw
    subst hvw
    rw [← hker, RingHom.mem_ker, map_sub, map_mul, map_mul, map_pow, map_pow, ← hv', ← hw']
    ring

  let g : {p : Ideal R // p.IsPrime} → R := fun k => f k ^ (n k + 1)
  let α : {p : Ideal R // p.IsPrime} → R := fun k => f k * a k
  have hspan : Ideal.span (Set.range g) = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    let k : {p : Ideal R // p.IsPrime} := ⟨m, hm.isPrime⟩
    exact hf k (hm.isPrime.mem_of_pow_mem _ (hle (Ideal.subset_span ⟨k, rfl⟩)))
  have h1 : (1 : R) ∈ Submodule.span R (Set.range g) := by
    rw [← Ideal.span, hspan]; exact Submodule.mem_top
  obtain ⟨b, hb⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp h1
  let π := Ideal.Quotient.mk (nilradical R)
  have hrel : ∀ k l, π (g l) * π (α k) = π (g k) * π (α l) := by
    intro k l
    rw [← map_mul, ← map_mul, Ideal.Quotient.eq, mem_nilradical]
    have e : g l * α k - g k * α l = f k * f l * (a k * f l ^ n l - a l * f k ^ n k) := by
      simp only [g, α]; ring
    rw [e]; exact hnil k l
  obtain ⟨c0, hc0⟩ := Ideal.Quotient.mk_surjective (I := nilradical R)
    (b.sum fun k r => π r * π (α k))
  have hb' : (b.sum fun k r => π r * π (g k)) = 1 := by
    have := congrArg π hb
    set_option synthInstance.maxHeartbeats 100000 in
      simpa [Finsupp.sum, map_sum, smul_eq_mul] using this
  have hglue : ∀ l, IsNilpotent (g l * c0 - α l) := by
    intro l
    rw [← mem_nilradical, ← Ideal.Quotient.eq]
    calc π (g l * c0) = b.sum (fun k r => π r * π (g k) * π (α l)) := by
          rw [map_mul]
          change π (g l) * Ideal.Quotient.mk (nilradical R) c0 = _
          rw [hc0, Finsupp.mul_sum]
          refine Finsupp.sum_congr fun k _ => ?_
          linear_combination π (b k) * hrel k l
      _ = π (α l) := by rw [← Finsupp.sum_mul, hb', _root_.one_mul]
  refine ⟨c0, fun K _ i => ?_⟩
  let k : {p : Ideal R // p.IsPrime} := ⟨RingHom.ker i, RingHom.ker_isPrime i⟩
  have hik : i (f k) ≠ 0 := fun h => hf k (RingHom.mem_ker.mpr h)
  obtain ⟨v, hv, hv'⟩ := key K i k hik
  have h0 : i (g k * c0 - α k) = 0 := ((hglue k).map i).eq_zero
  have hcv : i c0 = v := by
    have hp : i (f k) ^ (n k + 1) ≠ 0 := pow_ne_zero _ hik
    apply mul_left_cancel₀ hp
    simp only [g, α, map_sub, map_mul, map_pow, sub_eq_zero] at h0
    rw [h0, ← hv']; ring
  rw [hcv]; exact hv

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingElementOfLocalFieldPointValuesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ring_element_of_local_field_point_values : ∀ (R : Type) [CommRing R] (P : (K : Type) → [Field K] → (R →+* K) → K → Prop), (∀ (K : Type) [Field K] (i : R →+* K) (u v : K), P K i u → P K i v → u = v) → (∀ p : Ideal R, p.IsPrime → ∃ f ∉ p, ∃ c : Localization.Away f, ∀ (K : Type) [Field K] (j : Localization.Away f →+* K), P K (j.comp (algebraMap R (Localization.Away f))) (j c)) → ∃ c : R, ∀ (K : Type) [Field K] (i : R →+* K), P K i (i c) := by
  first | exact @GlobalTheory.glue_field_points | exact GlobalTheory.glue_field_points | (intros; apply GlobalTheory.glue_field_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueFieldPointPolarisedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueFieldPointPolarisedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem thG_unique_of_polFib : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (K : Type) [Field K] (i : R →+* K), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (th : SecAt G L (spMap i ≫ x)) (pt : Over.mk (spMap i ≫ x) ⟶ G) (c c' : K), ThG G L ρ m th pt (fn c) → ThG G L ρ m th pt (fn c') → c = c' := by
  intro S G _ _ L ρ hL hρ g m R _ _ x K _ i hm hu hP th pt c c' H H'
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  obtain ⟨ρ₁, -, hr⟩ := GlobalTheory.Ex.OneGen.exists_rigidificationPullbackCompatibleIso hp hw hL P.isLB hρ
  let T : Over (Sp R) := Over.mk (spMap i)
  let T₀ : Over S := Over.mk (spMap i ≫ x)
  have hτ : 𝟙 (Sp K) ≫ T₀.hom = T.hom ≫ x := Category.id_comp _
  obtain ⟨th₁, hth⟩ := GlobalTheory.ThetaPtMove.exists_secRel hp (T := T) (T₀ := T₀) (𝟙 _) hτ hw hL P.isLB th
  have hsq : pt.left ≫ G.hom = spMap i ≫ x := Over.w pt
  let x₁ : T ⟶ P.A := Over.homMk (hp.1.lift pt.left (spMap i) hsq) (hp.1.lift_snd _ _ _)
  have hx : 𝟙 (Sp K) ≫ pt.left = x₁.left ≫ α := by
    rw [Category.id_comp]; exact (hp.1.lift_fst _ _ _).symm
  have hn : x₁ ^ (m ^ 2) = 1 := by
    have h1 := GlobalTheory.ThetaPtMove.over_pow hp (T := T) (T₀ := T₀) (𝟙 _) hτ hx (m ^ 2)
    rw [H.1] at h1
    have h2 := GlobalTheory.ThetaPtMove.over_one hp (T := T) (T₀ := T₀) (𝟙 _) hτ
    exact Over.OverMorphism.ext (hp.1.hom_ext (h1.symm.trans h2) ((Over.w _).trans (Over.w _).symm))
  have hu' : IsUnit ((m ^ 2 : ℕ) : Γ(Sp R, ⊤)) := by
    rw [Nat.cast_pow, ← map_natCast (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom m, ← map_pow]
    exact (hu.pow 2).map _
  have m1 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c)) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H
  have m2 : ThG P.A P.L ρ₁ m th₁ x₁ ((𝟙 (Sp K) : Sp K ⟶ Sp K).appTop.hom (fn c')) :=
    ThG.move (T := T) (T₀ := T₀) hp (𝟙 _) hτ hw hL P.isLB hr hx hn hth H'
  have e := ThG.unique (T := T) abelianSchemeLaws_all.1 P hm hu' m1 m2
  have e2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom e
  simpa using e2

end GlobalTheory.UMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantUniqueFieldPointPolarisedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaConstant_unique_field_point_polarisedFibre : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (K : Type) [Field K] (i : R →+* K), Odd m → IsUnit (m : R) → PolFib G L g x → ∀ (th : SecAt G L (spMap i ≫ x)) (pt : Over.mk (spMap i ≫ x) ⟶ G) (c c' : K), ThG G L ρ m th pt (fn c) → ThG G L ρ m th pt (fn c') → c = c' := by
  first | exact @GlobalTheory.UMin.thG_unique_of_polFib | exact GlobalTheory.UMin.thG_unique_of_polFib | (intros; apply GlobalTheory.UMin.thG_unique_of_polFib <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFunctionsFiniteFlatCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UMin

theorem thList_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (c : Fin N → R₁), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ ∀ (K : Type) [Field K] (i : R →+* K) (i₁ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i → ∃ pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun a => i₁ (c a)) := by
  intro S G _ _ L ρ hL hρ g m N R _ _ x θ hm hu hN hP
  obtain ⟨R₁, _, _, q, hfin, hff, hq, hpts⟩ := GlobalTheory.T.exists_finite_flat_cover_m_sq_torsion_sections S G L g m N R x hm hu hN hP
  haveI : IsNoetherianRing R₁ := Algebra.FiniteType.isNoetherianRing R R₁
  have hcomp : ∀ {K : Type} [Field K] (i₁ : R₁ →+* K),
      spMap i₁ ≫ spMap (algebraMap R R₁) = spMap (i₁.comp (algebraMap R R₁)) := by
    intro K _ i₁; simp [spMap]
  let pt₀ : ∀ {K : Type} [Field K] (i₁ : R₁ →+* K) (a : Fin N), Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G :=
    fun i₁ a => Over.homMk (spMap i₁ ≫ (q a).left) (by
      have h := Over.w (q a)
      simp only [Over.mk_hom] at h ⊢
      rw [Category.assoc, h, ← Category.assoc, hcomp])
  have key : ∀ a : Fin N, ∃ c : R₁, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K)
      (pt : Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G), pt.left = spMap i₁ ≫ (q a).left →
        ThG G L ρ m (SecAt.pull G L θ (i₁.comp (algebraMap R R₁))) pt (fn (i₁ c)) := by
    intro a
    refine GlobalTheory.T.exists_ring_element_of_local_field_point_values R₁ (fun K _ i₁ v => ∀ (pt : Over.mk (spMap (i₁.comp (algebraMap R R₁)) ≫ x) ⟶ G),
        pt.left = spMap i₁ ≫ (q a).left →
        ThG G L ρ m (SecAt.pull G L θ (i₁.comp (algebraMap R R₁))) pt (fn v)) ?_ ?_
    · intro K _ i₁ u v hu' hv'
      exact GlobalTheory.T.thetaConstant_unique_field_point_polarisedFibre S G L ρ hL hρ g m R x K (i₁.comp (algebraMap R R₁)) hm hu hP _ (pt₀ i₁ a) u v
        (hu' _ rfl) (hv' _ rfl)
    · intro p hp
      obtain ⟨f, hf, c, hc⟩ := GlobalTheory.T.exists_local_thetaConstants_localisation S G L ρ hL hρ g m R x θ R₁ N q hm hu hP hq p hp
      exact ⟨f, hf, c a, fun K _ j pt hpt => hc K j a pt hpt⟩
  choose c hc using key
  refine ⟨R₁, inferInstance, inferInstance, c, hfin, hff, fun K _ i i₁ hi => ?_⟩
  subst hi
  obtain ⟨hinj, hcov⟩ := hpts K i₁ (pt₀ i₁) (fun a => rfl)
  exact ⟨pt₀ i₁, hinj, fun a => hc a K i₁ _ rfl, hcov⟩

end GlobalTheory.UMin
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsFunctionsFiniteFlatCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_constants_functions_finite_flat_cover : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsNoetherianRing R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : Algebra R R₁) (c : Fin N → R₁), Module.Finite R R₁ ∧ Module.FaithfullyFlat R R₁ ∧ ∀ (K : Type) [Field K] (i : R →+* K) (i₁ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i → ∃ pt : Fin N → (Over.mk (spMap i ≫ x) ⟶ G), ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun a => i₁ (c a)) := by
  first | exact @GlobalTheory.UMin.thList_cover | exact GlobalTheory.UMin.thList_cover | (intros; apply GlobalTheory.UMin.thList_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendElementOfFieldEqualizerFaithfullyFlat
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemRangeOfForallAlgHomEq
open scoped TensorProduct

namespace GlobalTheory


open Polynomial in
theorem mem_range_of_forall_algHom_eq :
    ∀ (F K₀ : Type) [Field F] [CharZero F] [Field K₀] [Algebra F K₀], Algebra.IsAlgebraic F K₀ →
      ∀ t : K₀, (∀ (Ω : Type) [Field Ω] [Algebra F Ω] (φ₁ φ₂ : K₀ →ₐ[F] Ω), φ₁ t = φ₂ t) →
        t ∈ Set.range (algebraMap F K₀) := by
  intro F K₀ _ _ _ _ halg t ht
  classical
  have hint : IsIntegral F t := (Algebra.IsAlgebraic.isAlgebraic t).isIntegral
  set Ω := AlgebraicClosure K₀
  have hsep : (minpoly F t).Separable := (minpoly.irreducible hint).separable
  have hsplit : Splits ((minpoly F t).map (algebraMap F Ω)) := IsAlgClosed.splits _
  have hcard := card_rootSet_eq_natDegree (K := Ω) hsep hsplit
  by_contra hnot
  have h1 : (minpoly F t).natDegree ≠ 1 := fun h => by
    obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.mp h
    exact hnot ⟨c, hc⟩
  have hpos := minpoly.natDegree_pos hint
  have hlt : 1 < Fintype.card ((minpoly F t).rootSet Ω) := by omega
  obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card hlt
  have hK' : ∀ s : K₀, IsIntegral F s ∧ Splits ((minpoly F s).map (algebraMap F Ω)) :=
    fun s => ⟨(Algebra.IsAlgebraic.isAlgebraic s).isIntegral, IsAlgClosed.splits _⟩
  have ha : aeval (a : Ω) (minpoly F t) = 0 :=
    (mem_rootSet.mp a.2).2
  have hb : aeval (b : Ω) (minpoly F t) = 0 :=
    (mem_rootSet.mp b.2).2
  obtain ⟨φa, hφa⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hK' ha
  obtain ⟨φb, hφb⟩ := IntermediateField.exists_algHom_of_splits_of_aeval hK' hb
  apply hab
  apply Subtype.ext
  rw [← hφa, ← hφb]
  exact ht Ω φa φb

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendElementOfFieldEqualizerFaithfullyFlat
open scoped TensorProduct

namespace GlobalTheory.SymDesc

variable {R R₁ : Type} [CommRing R] [IsDomain R] [CommRing R₁] [Algebra R R₁]

theorem injective_quotient (Q : Ideal R₁) (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    Function.Injective (algebraMap R (R₁ ⧸ Q)) := by
  set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
  intro r hr
  have : r ∈ Q.comap (algebraMap R R₁) := by
    rw [Ideal.mem_comap, ← Ideal.Quotient.eq_zero_iff_mem, Ideal.Quotient.mk_algebraMap]
    exact hr
  rwa [hQ, Ideal.mem_bot] at this

theorem exists_sub_mem_of_under_eq_bot [IsIntegrallyClosed R] [CharZero R]
    [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q : Ideal R₁) [Q.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥) :
    ∃ e : R, s - algebraMap R R₁ e ∈ Q := by
  classical
  let A := R₁ ⧸ Q
  let K₀ := FractionRing A
  let F := FractionRing R
  have hRA : Function.Injective (algebraMap R A) := injective_quotient Q hQ
  have hRK : Function.Injective (algebraMap R K₀) := by
    rw [IsScalarTower.algebraMap_eq R A K₀]
    exact (IsFractionRing.injective A K₀).comp hRA
  haveI : FaithfulSMul R K₀ := (faithfulSMul_iff_algebraMap_injective R K₀).2 hRK
  letI : Algebra F K₀ := FractionRing.liftAlgebra R K₀
  haveI : IsScalarTower R F K₀ := FractionRing.isScalarTower_liftAlgebra R K₀
  haveI : FaithfulSMul R A := (faithfulSMul_iff_algebraMap_injective R A).2 hRA
  haveI : Module.IsTorsionFree R K₀ := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRK
  haveI : Module.IsTorsionFree R A := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRA
  haveI : Algebra.IsAlgebraic R A := Algebra.IsIntegral.isAlgebraic
  haveI : Algebra.IsAlgebraic R K₀ := (IsFractionRing.isAlgebraic_iff' R A K₀).1 inferInstance
  haveI : Algebra.IsAlgebraic F K₀ :=
    ⟨fun x => (IsFractionRing.isAlgebraic_iff R F K₀).1 (Algebra.IsAlgebraic.isAlgebraic x)⟩
  let π : R₁ →+* K₀ := (algebraMap A K₀).comp (Ideal.Quotient.mk Q)
  have hπ : ∀ r : R, π (algebraMap R R₁ r) = algebraMap F K₀ (algebraMap R F r) := by
    intro r
    have hq : (Ideal.Quotient.mk Q) ((algebraMap R R₁) r) = algebraMap R A r := by
      first | rfl | exact Ideal.Quotient.mk_algebraMap _ _ | simp [A]
    simp only [π, RingHom.comp_apply]
    rw [hq, ← IsScalarTower.algebraMap_apply R A K₀, ← IsScalarTower.algebraMap_apply R F K₀]
  obtain ⟨e', he'⟩ := GlobalTheory.mem_range_of_forall_algHom_eq F K₀ inferInstance (π s) (by
    intro Ω _ _ φ₁ φ₂
    have h := hs Ω (φ₁.toRingHom.comp π) (φ₂.toRingHom.comp π) (by
      ext r
      simp only [RingHom.comp_apply, hπ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes])
    simpa using h)
  have hint : IsIntegral R (π s) := by
    have h1 : IsIntegral R (Ideal.Quotient.mk Q s) := Algebra.IsIntegral.isIntegral _
    exact h1.map (IsScalarTower.toAlgHom R A K₀)
  rw [← he'] at hint
  have hint' : IsIntegral R e' :=
    (isIntegral_algHom_iff (IsScalarTower.toAlgHom R F K₀) (algebraMap F K₀).injective).1 hint
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  refine ⟨y, ?_⟩
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  apply IsFractionRing.injective A K₀
  rw [map_zero]
  have h : π (s - algebraMap R R₁ y) = 0 := by
    rw [RingHom.map_sub, hπ, hy, he', sub_self]
  exact h

theorem eq_of_sub_mem [Algebra.IsIntegral R R₁] (s : R₁)
    (hs : ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s)
    (Q Q' : Ideal R₁) [Q.IsPrime] [Q'.IsPrime] (hQ : Q.comap (algebraMap R R₁) = ⊥)
    (hQ' : Q'.comap (algebraMap R R₁) = ⊥) (e e' : R) (he : s - algebraMap R R₁ e ∈ Q)
    (he' : s - algebraMap R R₁ e' ∈ Q') : e = e' := by
  classical
  let F := FractionRing R
  let M := AlgebraicClosure F
  have hRM : Function.Injective (algebraMap R M) := by
    rw [IsScalarTower.algebraMap_eq R F M]
    exact (algebraMap F M).injective.comp (IsFractionRing.injective R F)
  haveI : FaithfulSMul R M := (faithfulSMul_iff_algebraMap_injective R M).2 hRM
  haveI : Module.IsTorsionFree R M := by
    rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRM
  have key : ∀ (P : Ideal R₁) [P.IsPrime], P.comap (algebraMap R R₁) = ⊥ →
      ∃ j : R₁ →+* M, j.comp (algebraMap R R₁) = algebraMap R M ∧ ∀ x ∈ P, j x = 0 := by
    intro P _ hP
    have hRA : Function.Injective (algebraMap R (R₁ ⧸ P)) := injective_quotient P hP
    haveI : FaithfulSMul R (R₁ ⧸ P) := (faithfulSMul_iff_algebraMap_injective R _).2 hRA
    haveI : Module.IsTorsionFree R (R₁ ⧸ P) := by
      rw [Module.isTorsionFree_iff_algebraMap_injective]; exact hRA
    haveI : Algebra.IsAlgebraic R (R₁ ⧸ P) := Algebra.IsIntegral.isAlgebraic
    let l : (R₁ ⧸ P) →ₐ[R] M := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    refine ⟨l.toRingHom.comp (Ideal.Quotient.mk P), ?_, fun x hx => ?_⟩
    · ext r
      simp only [RingHom.comp_apply, Ideal.Quotient.mk_algebraMap, AlgHom.toRingHom_eq_coe,
        RingHom.coe_coe, AlgHom.commutes]
    · simp only [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem.2 hx, map_zero]
  obtain ⟨j, hj, hj0⟩ := key Q hQ
  obtain ⟨j', hj', hj0'⟩ := key Q' hQ'
  have h := hs M j j' (hj.trans hj'.symm)
  have h1 : j s = algebraMap R M e := by
    have := hj0 _ he
    rw [map_sub, sub_eq_zero] at this
    rw [this, ← RingHom.comp_apply, hj]
  have h2 : j' s = algebraMap R M e' := by
    have := hj0' _ he'
    rw [map_sub, sub_eq_zero] at this
    rw [this, ← RingHom.comp_apply, hj']
  exact hRM (h1.symm.trans (h.trans h2))

end GlobalTheory.SymDesc

namespace GlobalTheory

theorem exists_eq_algebraMap_of_forall_ringHom_eq : ∀ (R R₁ : Type) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] [CharZero R] [CommRing R₁] [Algebra R R₁], Module.Finite R R₁ →
    Module.FaithfullyFlat R R₁ → ∀ s : R₁, (∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K),
      i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s) →
    ∃ e : R, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K), i₁ s = i₁ (algebraMap R R₁ e) := by
  intro R R₁ _ _ _ _ _ _ hfin hff s hs
  haveI := hfin
  haveI := hff
  haveI : Algebra.IsIntegral R R₁ := Algebra.IsIntegral.of_finite R R₁
  have hinj : Function.Injective (algebraMap R R₁) := FaithfulSMul.algebraMap_injective R R₁
  have hker : Ideal.comap (algebraMap R R₁) (⊥ : Ideal R₁) ≤ ⊥ := by
    intro r hr
    rw [Ideal.mem_comap, Ideal.mem_bot] at hr
    rw [Ideal.mem_bot]
    exact hinj (by rw [hr, map_zero])
  obtain ⟨Q₀, -, hQ₀, hQ₀b⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (⊥ : Ideal R) ⊥ hker
  haveI := hQ₀
  obtain ⟨e, he⟩ := SymDesc.exists_sub_mem_of_under_eq_bot s hs Q₀ hQ₀b
  refine ⟨e, fun K _ i₁ => ?_⟩
  let P := RingHom.ker i₁
  haveI : P.IsPrime := RingHom.ker_isPrime i₁
  haveI : P.LiesOver (P.under R) := ⟨rfl⟩
  obtain ⟨Q, hQP, hQ, hQo⟩ :=
    Ideal.exists_ideal_le_liesOver_of_le (p := (⊥ : Ideal R)) (q := P.under R) P bot_le
  have hQb : Q.comap (algebraMap R R₁) = ⊥ := hQo.over.symm
  obtain ⟨e₁, he₁⟩ := SymDesc.exists_sub_mem_of_under_eq_bot s hs Q hQb
  have hee := SymDesc.eq_of_sub_mem s hs Q₀ Q hQ₀b hQb e e₁ he he₁
  subst hee
  have hm : s - algebraMap R R₁ e ∈ P := hQP he₁
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hm
  exact hm

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DescendElementOfFieldEqualizerFaithfullyFlatStatement
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.descend_element_of_field_equalizer_faithfully_flat : ∀ (R R₁ : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CharZero R] [CommRing R₁] [Algebra R R₁], Module.Finite R R₁ → Module.FaithfullyFlat R R₁ → ∀ s : R₁, (∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) → i₁ s = i₂ s) → ∃ e : R, ∀ (K : Type) [Field K] (i₁ : R₁ →+* K), i₁ s = i₁ (algebraMap R R₁ e) := by
  first | exact @GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq | exact GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq | (intros; apply GlobalTheory.exists_eq_algebraMap_of_forall_ringHom_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsMemNormalDomain
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.UMin.SymRing

theorem exists_common_field : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] [Algebra R R₁], Module.FaithfullyFlat R R₁ → ∀ (K : Type) [Field K] (i : R →+* K), ∃ (K' : Type) (_ : Field K') (φ : K →+* K') (i₁ : R₁ →+* K'), i₁.comp (algebraMap R R₁) = φ.comp i := by
  intro R R₁ _ _ _ hff K _ i
  letI : Algebra R K := i.toAlgebra
  haveI : Nontrivial (K ⊗[R] R₁) := Module.FaithfullyFlat.rTensor_nontrivial R R₁ K
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (K ⊗[R] R₁)
  letI : Field ((K ⊗[R] R₁) ⧸ M) := Ideal.Quotient.field M
  refine ⟨(K ⊗[R] R₁) ⧸ M, inferInstance,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeLeft (R := R) (S := R) (A := K) (B := R₁)).toRingHom,
    (Ideal.Quotient.mk M).comp (Algebra.TensorProduct.includeRight (R := R) (A := K) (B := R₁)).toRingHom, ?_⟩
  ext r
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
  rw [AlgHom.commutes, show i r = algebraMap R K r from rfl, AlgHom.commutes]

theorem symTup_map' {R R' : Type} [CommRing R] [CommRing R'] (i : R →+* R') {N : ℕ} (c : Fin N → R) (j : Fin N) :
    i (symTup c j) = symTup (fun a => i (c a)) j := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [symTup, Finset.esymm_map_val, map_pow, map_sum, map_prod]

theorem symTup_perm' {R : Type} [CommRing R] {N : ℕ} (c : Fin N → R) (σ : Equiv.Perm (Fin N)) :
    symTup (fun b => c (σ b)) = symTup c := by
  funext j
  show _ = (Finset.univ.val.map c).esymm _ ^ _
  rw [symTup, ← Function.comp_def c σ, ← Multiset.map_map, Multiset.map_univ_val_equiv]

theorem sym_ring : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → R, SymAt G L ρ m x θ e := by
  intro S G _ _ L ρ hL hρ g m N R _ _ _ _ _ x θ hm hmu hN hP
  obtain ⟨R₁, _, _, c, hfin, hff, hc⟩ := GlobalTheory.T.theta_constants_functions_finite_flat_cover S G L ρ hL hρ g m N R x θ hm hmu hN hP
  have hP' : ∀ j, ∀ (K : Type) [Field K] (i₁ i₂ : R₁ →+* K), i₁.comp (algebraMap R R₁) = i₂.comp (algebraMap R R₁) →
      i₁ (symTup c j) = i₂ (symTup c j) := by
    intro j K _ i₁ i₂ h
    obtain ⟨pt₁, h₁⟩ := hc K (i₁.comp (algebraMap R R₁)) i₁ rfl
    obtain ⟨pt₂, h₂⟩ := hc K (i₁.comp (algebraMap R R₁)) i₂ h.symm
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.thetaConstantList_fieldExtension_eq_up_to_perm S G L ρ hL hρ g m R x θ hm hmu hP K K _ _ (RingHom.id K) (RingHom.id_comp _) N pt₁ _ pt₂ _ h₁ h₂
    rw [symTup_map', symTup_map', funext hσ]
    exact (symTup_perm' (fun b => i₁ (c b)) σ).symm ▸ rfl
  choose e he using fun j => GlobalTheory.T.descend_element_of_field_equalizer_faithfully_flat R R₁ hfin hff (symTup c j) (hP' j)
  refine ⟨e, fun K _ i pt c' hl j => ?_⟩
  obtain ⟨K', _, φ, i₁, hφ⟩ := exists_common_field R R₁ hff K i
  obtain ⟨pt₁, h₁⟩ := hc K' (φ.comp i) i₁ hφ
  obtain ⟨σ, hσ⟩ := GlobalTheory.T.thetaConstantList_fieldExtension_eq_up_to_perm S G L ρ hL hρ g m R x θ hm hmu hP K K' i (φ.comp i) φ rfl N pt c' pt₁ _ hl h₁
  apply φ.injective
  have h1 : φ (i (e j)) = i₁ (algebraMap R R₁ (e j)) := by rw [← RingHom.comp_apply, ← RingHom.comp_apply, hφ]
  rw [h1, ← he j K' i₁, symTup_map', symTup_map', funext hσ]
  exact congrFun (symTup_perm' (fun a => φ (c' a)) σ) j

end GlobalTheory.UMin.SymRing

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsMemNormalDomainStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSymmetricFunctions_mem_normalDomain : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → IsUnit (m : R) → N = m ^ (4 * g) → PolFib G L g x → ∃ e : Fin N → R, SymAt G L ρ m x θ e := by
  first | exact @GlobalTheory.UMin.SymRing.sym_ring | exact GlobalTheory.UMin.SymRing.sym_ring | (intros; apply GlobalTheory.UMin.SymRing.sym_ring <;> assumption)
end
