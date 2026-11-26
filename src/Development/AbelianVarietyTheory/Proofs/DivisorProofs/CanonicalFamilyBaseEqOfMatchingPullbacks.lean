module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTautologicalBaseNsmulDegenerationData
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelPointLiftZeroFirstCoordinate
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniversalAbelianSchemeTorsionRationalFieldPoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SabMapKeepsLevelEta
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SabMapKeepsLevelEta
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem toUnit_left_eq' {X : Scheme.{0}} (T : Over X) : (toUnit T).left = T.hom := by
  have := Over.w (toUnit T)
  simpa using this

theorem grpPullback_pow_succ {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (hφ : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G')
    (x₀ : Over.mk (T.hom ≫ f) ⟶ G) (hx : x₀.left = x.left ≫ φ) (n : ℕ) :
    (x₀ ^ (n + 1)).left = (x ^ (n + 1)).left ≫ φ := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
    rw [pow_succ x₀, pow_succ x]
    exact hφ.2 T _ _ _ _ ih hx

theorem eta_eq_etaA_pow {D : Datum H} {l : Geo.Tor.Level H} {B : Type} [CommRing B] {bb : Base (LowDat.lowLevel l) B}
    {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D (LowDat.lowLevel l) bb s) (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S) (β : B →+* k) (hx : x ≫ s = spMap β) (a : D.La)
    (ha : a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La)) :
    toUnit (Over.mk x) ≫ o.eta a = (toUnit (Over.mk x) ≫ o.etaA a) ^ (l.M' / l.M) := by
  obtain ⟨-, I, -, hA, hM⟩ := o.geom k x β hx
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hdvd : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
  have hM'0 : 0 < l.M' := Nat.lcm_pos hM0 l.A_pos
  have hq : 0 < l.M' / l.M := Nat.div_pos (Nat.le_of_dvd hM'0 hdvd) hM0
  have hmul : l.M * (l.M' / l.M) = (LowDat.lowLevel l).A := Nat.mul_div_cancel' hdvd
  rw [hM a ha, hA a, ← hmul]
  exact (I.tower l.M (l.M' / l.M) hM0 hq a).symm

end GlobalTheory.UCanon

namespace GlobalTheory.UCanon

theorem sabMap_keeps_eta : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (A W : Type) [CommRing A] [IsDomain A] [CommRing W] (bA : c.F →+* A) (b : c.F →+* W) (o' : LowObj D c bA) (o : LowObj D c b) (f : W →+* A), f.comp b = bA → ∀ m : SABMap o'.t o.t (spMap f), (∀ a, (o'.etaA a).left ≫ m.φ = spMap f ≫ (o.etaA a).left) → ∀ a, (o'.eta a).left ≫ m.φ = spMap f ≫ (o.eta a).left := by
  intro E _ _ _ H D l c A W _ _ _ bA b o' o f hf m hA a
  subst hf

  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; exact Submodule.mem_top
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 h1
  have ha : u • a + v • a = a := by rw [← add_smul, huv, one_smul]
  have hu' : u • a ∈ (LowDat.lowLevel l).Mb • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hu Submodule.mem_top
  have hv' : v • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
    Submodule.smul_mem_smul hv Submodule.mem_top
  have e1 : o'.eta a = o'.eta (v • a) := by
    conv_lhs => rw [← ha]
    rw [o'.eta_add, o'.eta_ker _ hu', _root_.one_mul]
  have e2 : o.eta a = o.eta (v • a) := by
    conv_lhs => rw [← ha]
    rw [o.eta_add, o.eta_ker _ hu', _root_.one_mul]
  rw [e1, e2]
  generalize v • a = a' at hv' ⊢

  let K := AlgebraicClosure (FractionRing A)
  let κ : A →+* K := (algebraMap (FractionRing A) K).comp (algebraMap A (FractionRing A))
  have hκ : Function.Injective κ :=
    (algebraMap (FractionRing A) K).injective.comp (IsFractionRing.injective A (FractionRing A))
  haveI : IsDominant (spMap κ) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical κ).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot _).1 hκ]; exact bot_le)⟩
  haveI := o.proper
  haveI : IsReduced (𝟙_ (Over (Sp A))).left := (inferInstance : IsReduced (Sp A))
  refine ext_of_isDominant_of_isSeparated o.t.G.hom ?_ (spMap κ) ?_
  · have w1 := Over.w (o'.eta a')
    have w2 := Over.w (o.eta a')
    have w3 := m.cart.1.w
    simp only [Category.assoc]
    rw [w3, ← Category.assoc, w1, w2]
    simp
  · let β : KA (LowDat.lowLevel l) →+* K := κ.comp ((f.comp b).comp (IntermediateField.inclusion (LowDat.ka_le l c)).toRingHom)
    have hx' : spMap κ ≫ lowMap c (f.comp b) = spMap β := by
      unfold lowMap; rw [← Spec.map_comp]; rfl
    have hx : (spMap κ ≫ spMap f) ≫ lowMap c b = spMap β := by
      unfold lowMap; rw [← Spec.map_comp, ← Spec.map_comp]; rfl
    have p' := eta_eq_etaA_pow o' K (spMap κ) β hx' a' hv'
    have p := eta_eq_etaA_pow o K (spMap κ ≫ spMap f) β hx a' hv'
    have hM0 : 0 < l.M := by have := l.three_le; omega
    have hdvd : l.M ∣ l.M' := Nat.dvd_lcm_left l.M l.A
    have hq : 0 < l.M' / l.M := Nat.div_pos (Nat.le_of_dvd (Nat.lcm_pos hM0 l.A_pos) hdvd) hM0
    obtain ⟨n, hn⟩ : ∃ n, l.M' / l.M = n + 1 := ⟨l.M' / l.M - 1, by omega⟩
    rw [hn] at p p'
    have key := grpPullback_pow_succ m.cart (T := Over.mk (spMap κ)) (toUnit _ ≫ o'.etaA a')
      (toUnit (Over.mk (spMap κ ≫ spMap f)) ≫ o.etaA a') (by
        rw [Over.comp_left, Over.comp_left, toUnit_left_eq', toUnit_left_eq']
        simp only [Over.mk_hom, Category.assoc]
        rw [hA a']) n
    have q' := congrArg Over.Hom.left p'
    have q := congrArg Over.Hom.left p
    rw [Over.comp_left, toUnit_left_eq'] at q q'
    simp only [Over.mk_hom] at q q'
    rw [← Category.assoc, q', ← key, ← q, Category.assoc]

end GlobalTheory.UCanon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SabMapKeepsLevelEtaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sabMap_keeps_levelEta : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Geo.Tor.Level H} (c : Coeff l) (A W : Type) [CommRing A] [IsDomain A] [CommRing W] (bA : c.F →+* A) (b : c.F →+* W) (o' : LowObj D c bA) (o : LowObj D c b) (f : W →+* A), f.comp b = bA → ∀ m : SABMap o'.t o.t (spMap f), (∀ a, (o'.etaA a).left ≫ m.φ = spMap f ≫ (o.etaA a).left) → ∀ a, (o'.eta a).left ≫ m.φ = spMap f ≫ (o.eta a).left := by
  first | exact @GlobalTheory.UCanon.sabMap_keeps_eta | exact GlobalTheory.UCanon.sabMap_keeps_eta | (intros; apply GlobalTheory.UCanon.sabMap_keeps_eta <;> assumption)
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.FineAgree

theorem sec_hom {S : Scheme.{0}} {G : Over S} (x : 𝟙_ (Over S) ⟶ G) : x.left ≫ G.hom = 𝟙 S := Over.w x

theorem main : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (A : Type) [CommRing A] [IsDomain A] (f₁ f₂ : L.W →+* A), f₁.comp L.b = f₂.comp L.b → ∀ (B' : Over (Sp A)) [GrpObj B'] (π₁ π₂ : B'.left ⟶ L.D.P.A.left) (act' : 𝓞 E → (B'.left ⟶ B'.left)), IsGrpPullback B' L.D.P.A (spMap f₁) π₁ → IsGrpPullback B' L.D.P.A (spMap f₂) π₂ → (letI := H.starRing; ∀ x, act' x ≫ π₁ = π₁ ≫ (L.oa.onB.act x).left) → (letI := H.starRing; ∀ x, act' x ≫ π₂ = π₂ ≫ (L.oa.onB.act x).left) → (∀ x, act' x ≫ B'.hom = B'.hom) → LBIso (L.D.P.L.pull π₁) (L.D.P.L.pull π₂) → ∀ (F : Type) [Field F] (j : A →+* F), Function.Injective j → (∀ a, ∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ (L.o.etaA a).left ≫ L.φB ∧ z ≫ π₂ = spMap j ≫ spMap f₂ ≫ (L.o.etaA a).left ≫ L.φB) → (∀ y, ∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ (L.D.c y).left ∧ z ≫ π₂ = spMap j ≫ spMap f₂ ≫ (L.D.c y).left) → f₁ = f₂ ∧ π₁ = π₂ := by
  intro E _ _ _ H D' l c L A _ _ f₁ f₂ hb B' _ π₁ π₂ act' h₁ h₂ ha₁ ha₂ hab hL F _ j hj hη hc
  letI := H.starRing
  obtain ⟨o', ⟨m₁⟩⟩ := GlobalTheory.obj_pull E H D' (LowDat.lowLevel l) _ _ (baseKA _) (baseKA _) (RingHom.id _) _ _
    (lowMap c L.b) (lowMap c (f₁.comp L.b)) (spMap f₁) rfl rfl (by
      simp only [lowMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]) L.o
  have hφ₁ : IsGrpPullback o'.t.G L.D.P.A (spMap f₁) (m₁.φ ≫ L.φB) :=
    (m₁.cart.comp L.ab.1).congr (Category.comp_id _) rfl
  obtain ⟨e, he, heq⟩ := grpPullback_iso hφ₁ h₁
  haveI := he
  have hew : e.hom.left ≫ B'.hom = o'.t.G.hom := Over.w e.hom
  obtain ⟨ψ, hψ₁, hψ₂⟩ : ∃ ψ : o'.t.G.left ⟶ L.o.t.G.left, ψ ≫ L.φB = e.hom.left ≫ π₂ ∧
      ψ ≫ L.o.t.G.hom = o'.t.G.hom ≫ spMap f₂ :=
    ⟨L.ab.1.1.lift (e.hom.left ≫ π₂) (o'.t.G.hom ≫ spMap f₂) (by
      rw [Category.assoc, h₂.1.w, ← Category.assoc, hew, Category.comp_id]), IsPullback.lift_fst _ _ _ _,
      IsPullback.lift_snd _ _ _ _⟩
  have hψ : IsGrpPullback o'.t.G L.o.t.G (spMap f₂) ψ := by
    have n : IsGrpPullback o'.t.G L.D.P.A (spMap f₂ ≫ 𝟙 _) (ψ ≫ L.φB) := by
      rw [hψ₁, Category.comp_id]
      exact ((isGrpPullback_of_iso e).comp h₂).congr (Category.id_comp _) rfl
    exact L.ab.1.cancel n hψ₂
  have hact : ∀ x, (o'.t.act.act x).left ≫ ψ = ψ ≫ (L.o.t.act.act x).left := by
    intro x
    have key : (o'.t.act.act x).left ≫ e.hom.left = e.hom.left ≫ act' x := by
      apply h₁.1.hom_ext
      · have e1 : (o'.t.act.act x).left ≫ m₁.φ = m₁.φ ≫ (L.o.t.act.act x).left := m₁.act x
        calc ((o'.t.act.act x).left ≫ e.hom.left) ≫ π₁ = ((o'.t.act.act x).left ≫ m₁.φ) ≫ L.φB := by
              rw [Category.assoc, heq, Category.assoc]
          _ = m₁.φ ≫ (L.o.t.act.act x).left ≫ L.φB := by rw [e1, Category.assoc]
          _ = (m₁.φ ≫ L.φB) ≫ (L.oa.onB.act x).left := by rw [L.ab.2.1, Category.assoc]
          _ = (e.hom.left ≫ act' x) ≫ π₁ := by rw [← heq, Category.assoc, Category.assoc, ha₁]
      · rw [Category.assoc, hew, Category.assoc, hab, hew, Over.w (o'.t.act.act x)]
    apply L.ab.1.1.hom_ext
    · calc ((o'.t.act.act x).left ≫ ψ) ≫ L.φB = ((o'.t.act.act x).left ≫ e.hom.left) ≫ π₂ := by
            rw [Category.assoc, hψ₁, Category.assoc]
        _ = (ψ ≫ L.φB) ≫ (L.oa.onB.act x).left := by rw [key, Category.assoc, ha₂, hψ₁, Category.assoc]
        _ = (ψ ≫ (L.o.t.act.act x).left) ≫ L.φB := by rw [Category.assoc, Category.assoc, L.ab.2.1]
    · rw [Category.assoc, hψ₂, ← Category.assoc, Over.w (o'.t.act.act x), Category.assoc,
        Over.w (L.o.t.act.act x), hψ₂]

  have hLψ : LBIso o'.t.PP.L (L.o.t.PP.L.pull ψ) := by
    obtain ⟨w, hw, -⟩ := m₁.lin
    have K1 : LBIso o'.t.PP.L (L.D.P.L.pull (m₁.φ ≫ L.φB)) :=
      GlobalTheory.ThetaAffineGlue.lbIso_comp o'.t.PP.isLB L.o.t.PP.isLB L.D.P.isLB ⟨w, hw⟩ L.ab.2.2
    rw [← heq] at K1
    have K2 : LBIso o'.t.PP.L ((L.D.P.L.pull π₂).pull e.hom.left) :=
      GlobalTheory.ThetaAffineGlue.lbIso_cancel o'.t.PP.isLB (pull_isLB L.D.P.isLB _) L.D.P.isLB K1 hL.symm
    have K3 : LBIso o'.t.PP.L (L.D.P.L.pull (e.hom.left ≫ π₂)) :=
      GlobalTheory.ThetaAffineGlue.lbIso_comp o'.t.PP.isLB (pull_isLB L.D.P.isLB _) L.D.P.isLB K2
        (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB L.D.P.isLB _))
    rw [← hψ₁] at K3
    exact GlobalTheory.ThetaAffineGlue.lbIso_cancel o'.t.PP.isLB L.o.t.PP.isLB L.D.P.isLB K3 L.ab.2.2
  obtain ⟨n, hn⟩ := GlobalTheory.UCanon.TriplePull.exists_sabMap_of_isProper o'.t L.o.t (spMap f₂) ψ L.o.proper hψ hact hLψ
  haveI : IsDominant (spMap j) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical j).2 (by
    rw [(RingHom.injective_iff_ker_eq_bot j).1 hj]; exact bot_le)⟩
  haveI := L.o.proper
  have transfer : ∀ (u : Sp A ⟶ o'.t.G.left) (v : Sp L.W ⟶ L.o.t.G.left), u ≫ o'.t.G.hom = 𝟙 _ →
      v ≫ L.o.t.G.hom = 𝟙 _ → u ≫ m₁.φ = spMap f₁ ≫ v →
      (∃ z : Sp F ⟶ B'.left, z ≫ B'.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ v ≫ L.φB ∧
        z ≫ π₂ = spMap j ≫ spMap f₂ ≫ v ≫ L.φB) → u ≫ ψ = spMap f₂ ≫ v := by
    intro u v hu hv huv ⟨z, hz0, hz1, hz2⟩
    have hz : spMap j ≫ u ≫ e.hom.left = z := by
      apply h₁.1.hom_ext
      · rw [hz1, Category.assoc, Category.assoc, heq, ← Category.assoc u, huv, Category.assoc]
      · rw [hz0, Category.assoc, Category.assoc, hew, hu, Category.comp_id]
    refine ext_of_isDominant_of_isSeparated (X := Sp A) L.o.t.G.hom ?_ (spMap j) ?_
    · rw [Category.assoc, hψ₂, ← Category.assoc, hu, Category.id_comp, Category.assoc, hv, Category.comp_id]
    · apply L.ab.1.1.hom_ext
      · rw [Category.assoc, Category.assoc, hψ₁, ← Category.assoc u, ← Category.assoc, hz, hz2,
          Category.assoc, Category.assoc]
      · rw [Category.assoc, Category.assoc, hψ₂, ← Category.assoc u, hu, Category.id_comp, Category.assoc,
          Category.assoc, hv, Category.comp_id]
  have hetaA : ∀ a, (o'.etaA a).left ≫ n.φ = spMap f₂ ≫ (L.o.etaA a).left := by
    intro a
    rw [hn]
    exact transfer _ _ (sec_hom _) (sec_hom _) (m₁.etaA a) (hη a)
  have heta := GlobalTheory.T.sabMap_keeps_levelEta c A L.W (f₁.comp L.b) L.b o' L.o f₂ hb.symm n hetaA
  obtain ⟨m₂, hm₂⟩ : ∃ m₂ : ObjMap o' L.o (spMap f₂), m₂.φ = ψ := ⟨⟨n, heta, hetaA⟩, hn⟩

  have hcy : ∀ y, ∃ cy : Sp L.W ⟶ L.o.t.G.left, cy ≫ L.φB = (L.D.c y).left ∧ cy ≫ L.o.t.G.hom = 𝟙 _ := fun y =>
    ⟨L.ab.1.1.lift (L.D.c y).left (𝟙 _) (by rw [sec_hom, Category.comp_id]),
      IsPullback.lift_fst _ _ _ _, IsPullback.lift_snd _ _ _ _⟩
  choose cy hcy₁ hcy₂ using hcy
  have hx : ∀ y, ∃ x : Sp A ⟶ o'.t.G.left, x ≫ m₁.φ = spMap f₁ ≫ cy y ∧ x ≫ o'.t.G.hom = 𝟙 _ := fun y =>
    ⟨m₁.cart.1.lift (spMap f₁ ≫ cy y) (𝟙 _) (by
      rw [Category.assoc, hcy₂, Category.comp_id, Category.id_comp]),
      IsPullback.lift_fst _ _ _ _, IsPullback.lift_snd _ _ _ _⟩
  choose x hx₁ hx₃ using hx
  have hf : f₁ = f₂ := by
    refine L.fineRed A f₁ f₂ hb o' m₁ m₂ x (fun y => ?_) (fun y => ?_) hx₃
    · rw [← Category.assoc, hx₁, Category.assoc, hcy₁]
    · rw [hm₂, ← Category.assoc, transfer (x y) (cy y) (hx₃ y) (hcy₂ y) (hx₁ y) (by
        obtain ⟨z, hz⟩ := hc y
        exact ⟨z, by simpa only [hcy₁] using hz⟩), Category.assoc, hcy₁]
  subst hf
  refine ⟨rfl, ?_⟩
  have hu : m₁.φ = m₂.φ := GlobalTheory.ObjMapUnique.objMap_unique_of_nilpotent_nilradical A
    (by rw [nilradical_eq_zero]; exact IsNilpotent.zero) _ _ o' L.o (spMap f₁) m₁ m₂
  have hi : IsIso e.hom.left := ⟨⟨e.inv.left, by rw [← Over.comp_left, e.hom_inv_id, Over.id_left],
    by rw [← Over.comp_left, e.inv_hom_id, Over.id_left]⟩⟩
  apply (cancel_epi e.hom.left).1
  rw [heq, hu, hm₂, hψ₁]

end GlobalTheory.UCanon.FineAgree
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionPointsCorrespondMatchedPullbacks
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisionPointPairOverAlgClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisionPointPairOverAlgClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon

theorem exists_qk_over_cF : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult →
    ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k →
    ∀ (y : D.X) (x : TF (R := V) F ⟶ D.P.A), x ^ k = DegPre.cF D F y → ∃ p : QkPt D F k, p.y = y ∧ p.g.b = x := by
  intro V _ _ D hB F _ _ _ k hk y x hx
  obtain ⟨J, hJ⟩ := good_pt D.P.isLB (default : PrimeSpectrum F)
  exact exists_qk_over (F := F) hJ hB hk y x hx

end GlobalTheory.UCanon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisionPointPairOverAlgClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_divisionPoint_pair_over_algClosed : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V), D.TauBimult → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (k : ℕ), 1 ≤ k → ∀ (y : D.X) (x : TF (R := V) F ⟶ D.P.A), x ^ k = DegPre.cF D F y → ∃ p : QkPt D F k, p.y = y ∧ p.g.b = x := by
  first | exact @GlobalTheory.UCanon.exists_qk_over_cF | exact GlobalTheory.UCanon.exists_qk_over_cF | (intros; apply GlobalTheory.UCanon.exists_qk_over_cF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionPointsCorrespondMatchedPullbacks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TInj

theorem divPt_match_of_pairs : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (D₀ : DegPre R) (D₁ D₂ : DegPre V), D₀.TauBimult → D₂.TauBimult → ∀ (f₁ f₂ : R →+* V) (hD₁ : IsPullDeg f₁ D₀ D₁) (hD₂ : IsPullDeg f₂ D₀ D₂) (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j₁ j₂ : F₀ →+* F) (b : D₁.P.A ⟶ D₂.P.A) (φ' : D₁.X ≃+ D₂.X) (k : ℕ), 1 ≤ k → (∀ p₀ : QkPt D₀ F₀ k, ∃ (p₁ : QkPt D₁ F k) (p₂ : QkPt D₂ F k), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → (∀ y : D₀.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y) → ∀ (y : D₀.X) (x : TF (R := R) F₀ ⟶ D₀.P.A), x ^ k = DegPre.cF D₀ F₀ y → ∃ z : TF (R := V) F ⟶ D₁.P.A, z.left ≫ hD₁.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₁) = spMap j₁ ≫ x.left ∧ z.left ≫ b.left ≫ hD₂.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₂) = spMap j₂ ≫ x.left := by
  intro R V _ _ _ _ D₀ D₁ D₂ hB₀ hB₂ f₁ f₂ hD₁ hD₂ F₀ _ _ _ F _ _ j₁ j₂ b φ' k hk hpair hφ y x hx
  obtain ⟨p₀, hp₀y, hp₀b⟩ := GlobalTheory.T.exists_divisionPoint_pair_over_algClosed R D₀ hB₀ F₀ k hk y x hx
  obtain ⟨p₁, p₂, h₁y, hT₁, h₂y, hT₂, p', hp'y, hAct, hEq⟩ := hpair p₀
  have hy' : p'.y = p₂.y := by
    rw [hp'y, h₂y, h₁y, hp₀y]
    apply hD₂.xe.injective
    rw [hφ y, AddEquiv.apply_symm_apply]
  have hg : p'.g = p₂.g := qkPt_g_eq_of_equiv V D₂ hB₂ F k hk p' p₂ hy' hEq
  obtain ⟨g₁, ⟨hg₁b, -⟩, hP₁, -⟩ := hT₁
  obtain ⟨g₂, ⟨hg₂b, -⟩, hP₂, -⟩ := hT₂
  refine ⟨p₁.g.b, ?_, ?_⟩
  · rw [hP₁, hg₁b, hp₀b]
  · have hb : p₂.g.b = p₁.g.b ≫ b := by rw [← hg]; exact hAct.1
    rw [← Over.comp_left_assoc, ← hb, hP₂, hg₂b, hp₀b]

end GlobalTheory.TInj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivisionPointsCorrespondMatchedPullbacksStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.divisionPoints_correspond_matched_pullbacks : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (D₀ : DegPre R) (D₁ D₂ : DegPre V), D₀.TauBimult → D₂.TauBimult → ∀ (f₁ f₂ : R →+* V) (hD₁ : IsPullDeg f₁ D₀ D₁) (hD₂ : IsPullDeg f₂ D₀ D₂) (F₀ : Type) [Field F₀] [IsAlgClosed F₀] [Algebra (FractionRing R) F₀] (F : Type) [Field F] [Algebra (FractionRing V) F] (j₁ j₂ : F₀ →+* F) (b : D₁.P.A ⟶ D₂.P.A) (φ' : D₁.X ≃+ D₂.X) (k : ℕ), 1 ≤ k → (∀ p₀ : QkPt D₀ F₀ k, ∃ (p₁ : QkPt D₁ F k) (p₂ : QkPt D₂ F k), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → (∀ y : D₀.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y) → ∀ (y : D₀.X) (x : TF (R := R) F₀ ⟶ D₀.P.A), x ^ k = DegPre.cF D₀ F₀ y → ∃ z : TF (R := V) F ⟶ D₁.P.A, z.left ≫ hD₁.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₁) = spMap j₁ ≫ x.left ∧ z.left ≫ b.left ≫ hD₂.e.hom.left ≫ pullback.fst D₀.P.A.hom (specOf f₂) = spMap j₂ ≫ x.left := by
  first | exact @GlobalTheory.TInj.divPt_match_of_pairs | exact GlobalTheory.TInj.divPt_match_of_pairs | (intros; apply GlobalTheory.TInj.divPt_match_of_pairs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowLeftOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.FamTorsion

theorem one_left_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : Over.mk (T.hom ≫ f) ⟶ G).left = (1 : T ⟶ G').left ≫ φ := by
  let u : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have : u = 1 := mul_eq_left.1 hu
  rw [← this]
  rfl

theorem pow_left_of_isGrpPullback {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (hx : x₀.left = x.left ≫ φ) (n : ℕ) : (x₀ ^ n).left = (x ^ n).left ≫ φ := by
  induction n with
  | zero => rw [pow_zero, pow_zero]; exact one_left_of_isGrpPullback h T
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact h.2 T _ _ _ _ ih hx

end GlobalTheory.FamTorsion
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfActionCompatibleMatch
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfActionCompatibleMatch
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UCanon.MatchBundle

open GlobalTheory.CechPic

variable {R : Type} [CommRing R] [IsDomain R]

theorem pull_one (D : DegPre R) (T : Over (Sp R)) : CechPic.pull (1 : T ⟶ D.P.A).left (cls D.P.L D.P.isLB) = 0 := by
  have h : CechPic.pull (eSec D.P.A) (cls D.P.L D.P.isLB) = 0 :=
    (cls_pull D.P.isLB _ (pull_isLB D.P.isLB _)).symm.trans
      ((cls_eq_zero_iff (pull_isLB D.P.isLB _)).2 ⟨D.rig, D.rig_gen⟩)
  have e : (1 : T ⟶ D.P.A).left = (toUnit T).left ≫ eSec D.P.A := rfl
  rw [e, pull_comp, h, map_zero]

theorem cls_eq_lam (D : DegPre R) {O : Type} [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (w0 : O)
    (h : TraceFormTwistIso D oa w0) : cls D.P.L D.P.isLB = lam (cls D.P.L D.P.isLB) (𝟙 _) (oa.onB.act w0) := by
  obtain ⟨u, hu, -⟩ := h
  have h₀ := (cls_eq_zero_iff (LB.isLB_linComb D.P.isLB _ _)).2 ⟨u, hu⟩
  rw [cls_linComb D.P.isLB, Fin.sum_univ_four] at h₀
  have h₁ : (1 : ℤ) • CechPic.pull (𝟙 D.P.A * oa.onB.act w0).left (cls D.P.L D.P.isLB) +
      (-2 : ℤ) • CechPic.pull (𝟙 D.P.A.left) (cls D.P.L D.P.isLB) +
      (-1 : ℤ) • CechPic.pull (oa.onB.act w0).left (cls D.P.L D.P.isLB) +
      (2 : ℤ) • CechPic.pull (1 : D.P.A ⟶ D.P.A).left (cls D.P.L D.P.isLB) = 0 := h₀
  rw [lam, Over.id_left]
  rw [pull_one] at h₁ ⊢
  rw [pull_id] at h₁ ⊢
  linear_combination (norm := abel) -h₁

theorem cls_eq_lam_pull {V : Type} [CommRing V] [IsDomain V] {f : R →+* V} {D : DegPre R} {D' : DegPre V}
    (hD : IsPullDeg f D D') (a : D.P.A ⟶ D.P.A) (a' : D'.P.A ⟶ D'.P.A)
    (ha : a' ≫ hD.e.hom = hD.e.hom ≫ (Over.pullback (specOf f)).map a)
    (h : cls D.P.L D.P.isLB = lam (cls D.P.L D.P.isLB) (𝟙 _) a) :
    cls D'.P.L D'.P.isLB = lam (cls D'.P.L D'.P.isLB) (𝟙 _) a' := by
  have gp := pull_grp hD
  have e : cls D'.P.L D'.P.isLB =
      CechPic.pull (hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf f)) (cls D.P.L D.P.isLB) :=
    ((cls_eq_iff D'.P.isLB (pull_isLB D.P.isLB _)).2 ⟨hD.w, hD.w_gen⟩).trans (cls_pull D.P.isLB _ _)
  have p1 : (pushHom gp _ (𝟙 D'.P.A)).left = hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf f) := Category.id_comp _
  have q : pushHom gp _ a' = pushHom gp _ (𝟙 D'.P.A) ≫ a := Over.OverMorphism.ext (by
    rw [Over.comp_left, p1]
    have a₂ : ((Over.pullback (specOf f)).map a).left ≫ pullback.fst D.P.A.hom (specOf f) =
        pullback.fst _ _ ≫ a.left := pullback.lift_fst _ _ _
    show a'.left ≫ hD.e.hom.left ≫ _ = (hD.e.hom.left ≫ _) ≫ _
    rw [← Category.assoc, ← Over.comp_left, ha, Over.comp_left, Category.assoc, a₂, Category.assoc])
  have k := congrArg (CechPic.pull (pushHom gp _ (𝟙 D'.P.A)).left) h
  rw [pull_lam, Category.comp_id, ← q, p1] at k
  rw [e, lam_pull_of_isGrpPullback gp]
  exact k

theorem lbIso_of_match : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) → LBIso D₁.toPre.P.L (D₂.toPre.P.L.pull b.left) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ _ C _ V _ _ _ _ _ f₁ f₂ _ _ _ _ D₁ D₂ hD₁ hD₂ _ _ b φ' _ _ hM hact
  letI := H.starRing
  obtain ⟨a₁, a₂, h₁, h₂, hb⟩ := hact H.w0
  have k := cls_eq_lam C.P.D.toPre C.P.oD H.w0 C.P.w0
  have k₁ := cls_eq_lam_pull hD₁ _ a₁ h₁ k
  have k₂ := cls_eq_lam_pull hD₂ _ a₂ h₂ k
  have hL₁ := D₁.toPre.P.isLB
  have hL₂ := D₂.toPre.P.isLB
  have i₁ : (abelian₂ D₁.toPre.P.A D₁.toPre.P.L).IsLB := LB.isLB_linComb hL₁ _ _
  have i₂ : (abelian₂ D₂.toPre.P.A D₂.toPre.P.L).IsLB := LB.isLB_linComb hL₂ _ _
  have m := ((cls_eq_iff i₁ (pull_isLB i₂ _)).2 hM.2.2.1).trans (cls_pull i₂ _ _)
  have c₁ : cls _ i₁ = lam (cls _ hL₁) (fst _ _) (snd _ _) := cls_cube_two hL₁ _ _ _
  have c₂ : cls _ i₂ = lam (cls _ hL₂) (fst _ _) (snd _ _) := cls_cube_two hL₂ _ _ _
  rw [c₁, c₂] at m
  have m' := congrArg (CechPic.pull (lift (𝟙 D₁.toPre.P.A) a₁).left) m
  simp only [pull_lam, lift_fst, lift_snd, lift_fst_assoc, lift_snd_assoc, Category.id_comp] at m'
  refine (cls_eq_iff hL₁ (pull_isLB hL₂ _)).1 ?_
  rw [cls_pull hL₂, k₁, m', hb]
  conv_rhs => rw [k₂, pull_lam, Category.comp_id]

end GlobalTheory.UCanon.MatchBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoOfActionCompatibleMatchStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleIso_of_action_compatible_match : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) → LBIso D₁.toPre.P.L (D₂.toPre.P.L.pull b.left) := by
  first | exact @GlobalTheory.UCanon.MatchBundle.lbIso_of_match | exact GlobalTheory.UCanon.MatchBundle.lbIso_of_match | (intros; apply GlobalTheory.UCanon.MatchBundle.lbIso_of_match <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseEqOfMatchingPullbacks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

theorem GlobalTheory.UCanon.PairBase.spMap_comp {A B C' : Type} [CommRing A] [CommRing B] [CommRing C'] (f : B →+* C') (g : A →+* B) :
    spMap (f.comp g) = spMap f ≫ spMap g := by
  simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

namespace GlobalTheory.UCanon.PairBase

theorem comp_pow {S : Scheme.{0}} {X Y M : Over S} [MonObj M] (f : X ⟶ Y) (g : Y ⟶ M) (n : ℕ) :
    f ≫ g ^ n = (f ≫ g) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, MonObj.comp_one]
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih]

theorem c_pow {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (T : Over (Sp R)) (y : D.X) (n : ℕ)
    (u v : T ⟶ D.P.A) (hu : u.left = T.hom ≫ (D.c y).left) (hv : v.left = T.hom ≫ (D.c (n • y)).left) : u ^ n = v := by
  have eu : u = toUnit T ≫ D.c y := Over.OverMorphism.ext (by rw [hu, Over.comp_left, Over.toUnit_left])
  have ev : v = toUnit T ≫ D.c (n • y) := Over.OverMorphism.ext (by rw [hv, Over.comp_left, Over.toUnit_left])
  rw [eu, ev, GlobalTheory.UCanon.LevLift.degPre_cocharPoint_nsmul_eq_pow_levelLift, comp_pow]

theorem etaA_pow {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H}
    {c : Coeff l} (L : LowBase D' c) (T : Over (Sp L.W)) (a : D'.La) (u : T ⟶ L.D.P.A)
    (hu : u.left = T.hom ≫ (L.o.etaA a).left ≫ L.φB) : u ^ l.M' = 1 := by
  have h0 : L.o.etaA 0 = 1 := by
    have h := L.o.etaA_add 0 0
    rw [add_zero] at h
    exact mul_left_cancel (a := L.o.etaA 0) (by rw [_root_.mul_one]; exact h.symm)
  have hn : ∀ n : ℕ, L.o.etaA (n • a) = L.o.etaA a ^ n := by
    intro n
    induction n with
    | zero => rw [zero_smul, pow_zero, h0]
    | succ n ih => rw [succ_nsmul, L.o.etaA_add, ih, pow_succ]
  have hη : L.o.etaA a ^ l.M' = 1 := by
    rw [← hn]
    exact L.o.etaA_ker a
  let x : T ⟶ L.o.t.G := toUnit T ≫ L.o.etaA a
  have hx : x ^ l.M' = 1 := by
    rw [← comp_pow, hη, MonObj.comp_one]
  have hw : (x.left ≫ L.φB) ≫ L.D.P.A.hom = (Over.mk (T.hom ≫ 𝟙 _)).hom := by
    rw [Category.assoc, L.ab.1.1.w, ← Category.assoc, Over.w x]
    rfl
  let x₀ : Over.mk (T.hom ≫ 𝟙 _) ⟶ L.D.P.A := Over.homMk (x.left ≫ L.φB) hw
  have hp := GlobalTheory.FamTorsion.pow_left_of_isGrpPullback L.ab.1 x x₀ rfl l.M'
  have hx₀ : x₀ ^ l.M' = 1 := Over.OverMorphism.ext (by
    rw [hp, hx, GlobalTheory.FamTorsion.one_left_of_isGrpPullback L.ab.1 T])
  let e : T ⟶ Over.mk (T.hom ≫ 𝟙 _) := Over.homMk (𝟙 _) (by simp)
  have hue : u = e ≫ x₀ := Over.OverMorphism.ext (by
    rw [hu, Over.comp_left]
    simp [e, x₀, x, Over.toUnit_left])
  rw [hue, ← comp_pow, hx₀, MonObj.comp_one]

end GlobalTheory.UCanon.PairBase

theorem GlobalTheory.UCanon.PairBase.base_eq_of_match : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (∀ p₀ : QkPt C.P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M') (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) → (∀ y : C.P.D.toPre.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y) → f₁.comp C.b = f₂.comp C.b → f₁.comp (Cn.ψ.comp MvPolynomial.C) = f₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  intro E _ _ _ H Dw l Xo c φ R _ _ _ hR C Cn V _ _ _ _ hV f₁ f₂ hi₁ hi₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ' hE₁ hE₂ hM hpts hact hφ hb
  obtain ⟨g, hD, hg, hxe, hoa⟩ := Cn.data
  have hβ : IsGrpPullback C.P.D.toPre.P.A Cn.L.D.P.A (spMap (Cn.ψ.comp MvPolynomial.C))
      (hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C))) := pull_grp hD
  set β : C.P.D.toPre.P.A.left ⟶ Cn.L.D.P.A.left := hD.e.hom.left ≫ pullback.fst Cn.L.D.P.A.hom (specOf (Cn.ψ.comp MvPolynomial.C)) with hβdef
  set π₁ : D₁.toPre.P.A.left ⟶ Cn.L.D.P.A.left := prj hD₁ ≫ β with hπ₁
  set π₂ : D₁.toPre.P.A.left ⟶ Cn.L.D.P.A.left := b.left ≫ prj hD₂ ≫ β with hπ₂
  have hp₁ : IsGrpPullback D₁.toPre.P.A Cn.L.D.P.A (spMap (f₁.comp (Cn.ψ.comp MvPolynomial.C))) π₁ :=
    ((pull_grp hD₁).comp hβ).congr (GlobalTheory.UCanon.PairBase.spMap_comp _ _).symm rfl
  haveI := hM.2.1
  haveI : IsMonHom (asIso b).hom := hM.1
  have hp₂ : IsGrpPullback D₁.toPre.P.A Cn.L.D.P.A (spMap (f₂.comp (Cn.ψ.comp MvPolynomial.C))) π₂ :=
    ((isGrpPullback_of_iso (asIso b)).comp ((pull_grp hD₂).comp hβ)).congr (by rw [Category.id_comp]; exact (GlobalTheory.UCanon.PairBase.spMap_comp f₂ _).symm) (by rw [hπ₂, asIso_hom])

  letI := H.starRing
  have hsq : ∀ {R' : Type} [CommRing R'] [IsDomain R'] {θ : R →+* R'} {D' : DegPre R'} (h : IsPullDeg θ C.P.D.toPre D')
      (f : C.P.D.toPre.P.A ⟶ C.P.D.toPre.P.A) (f' : D'.P.A ⟶ D'.P.A),
      f' ≫ h.e.hom = h.e.hom ≫ (Over.pullback (specOf θ)).map f → f'.left ≫ prj h = prj h ≫ f.left :=
    fun h f f' e => (GlobalTheory.PullDegTop.main.2.1 h f f').1 e
  have hoa' : letI := H.starRing; ∀ x, (C.P.oD.onB.act x).left ≫ β = β ≫ (Cn.L.oa.onB.act x).left :=
    fun x => (hoa x).trans (Category.assoc _ _ _).symm

  have hLB0 := GlobalTheory.T.lineBundleIso_of_action_compatible_match Xo c φ R hR C Cn V hV f₁ f₂ hi₁ hi₂ hl₁ hl₂ D₁ D₂ hD₁ hD₂ j₁ j₂ b φ' hE₁ hE₂ hM hact
  have hβL : LBIso C.P.D.toPre.P.L (Cn.L.D.P.L.pull β) := ⟨hD.w, hD.w_gen⟩
  have hC := C.P.D.toPre.P.isLB
  have hLD := Cn.L.D.P.isLB
  have hW₁ : LBIso D₁.toPre.P.L (Cn.L.D.P.L.pull π₁) :=
    LBIso.trans D₁.toPre.P.isLB (pull_isLB hC _) (pull_isLB hLD _) ⟨hD₁.w, hD₁.w_gen⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp hβL (prj hD₁) rfl)
  have hW₂ : LBIso D₂.toPre.P.L (Cn.L.D.P.L.pull (prj hD₂ ≫ β)) :=
    LBIso.trans D₂.toPre.P.isLB (pull_isLB hC _) (pull_isLB hLD _) ⟨hD₂.w, hD₂.w_gen⟩
      (GlobalTheory.PolDeg.lbIso_pull_comp hβL (prj hD₂) rfl)
  have hLB : LBIso (Cn.L.D.P.L.pull π₁) (Cn.L.D.P.L.pull π₂) :=
    LBIso.trans (pull_isLB hLD _) D₁.toPre.P.isLB (pull_isLB hLD _) hW₁.symm
      (LBIso.trans D₁.toPre.P.isLB (pull_isLB D₂.toPre.P.isLB _) (pull_isLB hLD _) hLB0
        (GlobalTheory.PolDeg.lbIso_pull_comp hW₂ b.left hπ₂))
  choose a₁ a₂ ha₁ ha₂ hab using hact
  have hA₁ : letI := H.starRing; ∀ x, (a₁ x).left ≫ π₁ = π₁ ≫ (Cn.L.oa.onB.act x).left := by
    intro x
    have e1 := hsq hD₁ _ _ (ha₁ x)
    calc (a₁ x).left ≫ π₁ = ((a₁ x).left ≫ prj hD₁) ≫ β := (Category.assoc _ _ _).symm
      _ = prj hD₁ ≫ ((C.P.oD.onB.act x).left ≫ β) := by rw [e1, Category.assoc]
      _ = π₁ ≫ (Cn.L.oa.onB.act x).left := by rw [hoa' x, ← Category.assoc]
  have hA₂ : letI := H.starRing; ∀ x, (a₁ x).left ≫ π₂ = π₂ ≫ (Cn.L.oa.onB.act x).left := by
    intro x
    have e1 := hsq hD₂ _ _ (ha₂ x)
    have e3 : (a₁ x).left ≫ b.left = b.left ≫ (a₂ x).left := by rw [← Over.comp_left, hab x, Over.comp_left]
    have e3r : ∀ {Z : Scheme.{0}} (k : D₂.toPre.P.A.left ⟶ Z), (a₁ x).left ≫ b.left ≫ k = b.left ≫ (a₂ x).left ≫ k :=
      fun k => by rw [← Category.assoc, e3, Category.assoc]
    have e1r : ∀ {Z : Scheme.{0}} (k : C.P.D.toPre.P.A.left ⟶ Z), (a₂ x).left ≫ prj hD₂ ≫ k = prj hD₂ ≫ (C.P.oD.onB.act x).left ≫ k :=
      fun k => by rw [← Category.assoc, e1, Category.assoc]
    rw [hπ₂, e3r, e1r, hoa' x]
    simp only [Category.assoc]
  have hA₀ : ∀ x, (a₁ x).left ≫ D₁.toPre.P.A.hom = D₁.toPre.P.A.hom := fun x => Over.w (a₁ x)

  have hM1 : 1 ≤ l.M' := (GlobalTheory.LowDat.lowLevel l).A_pos
  let F₀ := AlgebraicClosure (FractionRing R)
  let F := AlgebraicClosure (FractionRing V)
  let j : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hj : Function.Injective j :=
    (algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V (FractionRing V))
  have hTF : (TF (R := V) F).hom = spMap j := (GlobalTheory.UCanon.PairBase.spMap_comp _ _).symm
  have hExt : ∀ (fi : R →+* V) (ji : F₀ →+* F), TInj.Ext fi ji →
      spMap ji ≫ (TF (R := R) F₀).hom = spMap j ≫ spMap fi := by
    intro fi ji hE
    have e : ji.comp ((algebraMap (FractionRing R) F₀).comp (algebraMap R (FractionRing R))) = j.comp fi :=
      RingHom.ext fun r => hE r
    have e1 : (TF (R := R) F₀).hom = spMap ((algebraMap (FractionRing R) F₀).comp (algebraMap R (FractionRing R))) :=
      (GlobalTheory.UCanon.PairBase.spMap_comp _ _).symm
    rw [e1, ← GlobalTheory.UCanon.PairBase.spMap_comp, e, GlobalTheory.UCanon.PairBase.spMap_comp]
  have hz : ∀ (y' : C.P.D.toPre.X) (x : TF (R := R) F₀ ⟶ C.P.D.toPre.P.A) (u : Sp R ⟶ Cn.L.D.P.A.left),
      x ^ l.M' = DegPre.cF C.P.D.toPre F₀ y' → x.left ≫ β = (TF (R := R) F₀).hom ≫ u →
      ∃ z : Sp F ⟶ D₁.toPre.P.A.left, z ≫ D₁.toPre.P.A.hom = spMap j ∧ z ≫ π₁ = spMap j ≫ spMap f₁ ≫ u ∧
        z ≫ π₂ = spMap j ≫ spMap f₂ ≫ u := by
    intro y' x u hx hxu
    obtain ⟨z, hz₁, hz₂⟩ := GlobalTheory.T.divisionPoints_correspond_matched_pullbacks R V C.P.D.toPre D₁.toPre D₂.toPre C.P.D.tau_bimult D₂.tau_bimult f₁ f₂ hD₁ hD₂
      F₀ F j₁ j₂ b φ' l.M' hM1 hpts hφ y' x hx
    have hz₁' : z.left ≫ prj hD₁ = spMap j₁ ≫ x.left := hz₁
    have hz₂' : z.left ≫ b.left ≫ prj hD₂ = spMap j₂ ≫ x.left := hz₂
    refine ⟨z.left, by rw [Over.w z, hTF], ?_, ?_⟩
    · calc z.left ≫ π₁ = (z.left ≫ prj hD₁) ≫ β := by rw [hπ₁]; simp only [Category.assoc]
        _ = (spMap j₁ ≫ (TF (R := R) F₀).hom) ≫ u := by rw [hz₁', Category.assoc, hxu, Category.assoc]
        _ = spMap j ≫ spMap f₁ ≫ u := by rw [hExt f₁ j₁ hE₁, Category.assoc]
    · calc z.left ≫ π₂ = (z.left ≫ b.left ≫ prj hD₂) ≫ β := by rw [hπ₂]; simp only [Category.assoc]
        _ = (spMap j₂ ≫ (TF (R := R) F₀).hom) ≫ u := by rw [hz₂', Category.assoc, hxu, Category.assoc]
        _ = spMap j ≫ spMap f₂ ≫ u := by rw [hExt f₂ j₂ hE₂, Category.assoc]

  have hlift : ∀ (y' : C.P.D.toPre.X) (u : Sp R ⟶ Cn.L.D.P.A.left),
      u ≫ Cn.L.D.P.A.hom = spMap (Cn.ψ.comp MvPolynomial.C) →
      (∀ w w' : Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C)) ⟶ Cn.L.D.P.A,
        w.left = (TF (R := R) F₀).hom ≫ u →
        w'.left = (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • Cn.e y')).left →
        w ^ l.M' = w') →
      ∃ x : TF (R := R) F₀ ⟶ C.P.D.toPre.P.A, x ^ l.M' = DegPre.cF C.P.D.toPre F₀ y' ∧
        x.left ≫ β = (TF (R := R) F₀).hom ≫ u := by
    intro y' u hu H'
    have hw0 : ((TF (R := R) F₀).hom ≫ u) ≫ Cn.L.D.P.A.hom =
        (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) := by rw [Category.assoc, hu]
    let x : TF (R := R) F₀ ⟶ C.P.D.toPre.P.A := Over.homMk (hβ.1.lift _ _ hw0) (hβ.1.lift_snd _ _ _)
    have hxβ : x.left ≫ β = (TF (R := R) F₀).hom ≫ u := hβ.1.lift_fst _ _ _
    refine ⟨x, ?_, hxβ⟩
    let w : Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C)) ⟶ Cn.L.D.P.A :=
      Over.homMk ((TF (R := R) F₀).hom ≫ u) hw0
    have hc0 : ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • Cn.e y')).left) ≫
        Cn.L.D.P.A.hom = (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) := by
      simp only [Category.assoc]
      erw [Over.w (Cn.L.D.c (l.M' • Cn.e y'))]
      simp
    let w' : Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C)) ⟶ Cn.L.D.P.A := Over.homMk _ hc0
    have hw := H' w w' rfl rfl
    have hpow := GlobalTheory.FamTorsion.pow_left_of_isGrpPullback hβ x w hxβ.symm l.M'
    apply Over.OverMorphism.ext
    apply hβ.1.hom_ext
    · rw [← hpow, hw]
      have hcp := hD.c_pr y'
      show (TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c (l.M' • Cn.e y')).left =
        (toUnit (TF (R := R) F₀) ≫ C.P.D.toPre.c y').left ≫ β
      rw [Over.comp_left, Over.toUnit_left, Category.assoc]
      erw [hcp]
      rw [hxe]
      rfl
    · rw [Over.w, Over.w]
  have hEta : ∀ a, ∃ z : Sp F ⟶ D₁.toPre.P.A.left, z ≫ D₁.toPre.P.A.hom = spMap j ∧
      z ≫ π₁ = spMap j ≫ spMap (f₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.o.etaA a).left ≫ Cn.L.φB ∧
      z ≫ π₂ = spMap j ≫ spMap (f₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.o.etaA a).left ≫ Cn.L.φB := by
    intro a
    have hu : (spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.o.etaA a).left ≫ Cn.L.φB) ≫ Cn.L.D.P.A.hom =
        spMap (Cn.ψ.comp MvPolynomial.C) := by
      rw [Category.assoc, Category.assoc, Cn.L.ab.1.1.w, Category.comp_id, Over.w (Cn.L.o.etaA a)]
      simp
    obtain ⟨x, hx, hxu⟩ := hlift 0 _ hu (fun w w' hw hw' => by
      have e1 : w ^ l.M' = 1 := GlobalTheory.UCanon.PairBase.etaA_pow Cn.L _ a w (by rw [hw]; simp only [Over.mk_hom, Category.assoc])
      have h0 : w'.left = (Over.mk ((TF (R := R) F₀).hom ≫ spMap (Cn.ψ.comp MvPolynomial.C))).hom ≫ (Cn.L.D.c 0).left := by
        rw [hw', map_zero, smul_zero]; simp only [Over.mk_hom, Category.assoc]
      have e2 := GlobalTheory.UCanon.PairBase.c_pow Cn.L.D _ 0 0 w' w' h0 (by rw [h0, zero_smul])
      rw [pow_zero] at e2
      rw [e1, e2])
    obtain ⟨z, hz0, hz1, hz2⟩ := hz 0 x _ hx hxu
    refine ⟨z, hz0, ?_, ?_⟩
    · rw [hz1, GlobalTheory.UCanon.PairBase.spMap_comp f₁ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
    · rw [hz2, GlobalTheory.UCanon.PairBase.spMap_comp f₂ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
  have hCp : ∀ y, ∃ z : Sp F ⟶ D₁.toPre.P.A.left, z ≫ D₁.toPre.P.A.hom = spMap j ∧
      z ≫ π₁ = spMap j ≫ spMap (f₁.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left ∧
      z ≫ π₂ = spMap j ≫ spMap (f₂.comp (Cn.ψ.comp MvPolynomial.C)) ≫ (Cn.L.D.c y).left := by
    intro y
    have hu : (spMap (Cn.ψ.comp MvPolynomial.C) ≫ (Cn.L.D.c y).left) ≫ Cn.L.D.P.A.hom =
        spMap (Cn.ψ.comp MvPolynomial.C) := by
      rw [Category.assoc, Over.w (Cn.L.D.c y)]
      simp
    obtain ⟨x, hx, hxu⟩ := hlift (Cn.e.symm y) _ hu (fun w w' hw hw' =>
      GlobalTheory.UCanon.PairBase.c_pow Cn.L.D _ y l.M' w w' (by rw [hw]; simp only [Over.mk_hom, Category.assoc])
        (by rw [hw', Cn.e.apply_symm_apply]; simp only [Over.mk_hom, Category.assoc]))
    obtain ⟨z, hz0, hz1, hz2⟩ := hz _ x _ hx hxu
    refine ⟨z, hz0, ?_, ?_⟩
    · rw [hz1, GlobalTheory.UCanon.PairBase.spMap_comp f₁ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
    · rw [hz2, GlobalTheory.UCanon.PairBase.spMap_comp f₂ (Cn.ψ.comp MvPolynomial.C)]; simp only [Category.assoc]
  have hbase : (f₁.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b = (f₂.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b := by
    have e : ∀ f : R →+* V, (f.comp (Cn.ψ.comp MvPolynomial.C)).comp Cn.L.b = f.comp C.b := fun f => by
      rw [← Cn.base]; rfl
    rw [e, e, hb]
  exact (GlobalTheory.UCanon.FineAgree.main Cn.L V _ _ hbase D₁.toPre.P.A π₁ π₂ (fun x => (a₁ x).left) hp₁ hp₂ hA₁ hA₂ hA₀ hLB F j hj
    hEta hCp).1
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CanonicalFamilyBaseEqOfMatchingPullbacksStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFamily_base_eq_of_matching_pullbacks : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : MonoFam Xo c φ R) (Cn : Canon C) (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V], IsAdicComplete (maximalIdeal V) V → ∀ f₁ f₂ : R →+* V, Function.Injective f₁ → Function.Injective f₂ → IsLocalHom f₁ → IsLocalHom f₂ → ∀ (D₁ D₂ : DegData V (maximalIdeal V)) (hD₁ : IsPullDeg f₁ C.P.D.toPre D₁.toPre) (hD₂ : IsPullDeg f₂ C.P.D.toPre D₂.toPre) (j₁ j₂ : (AlgebraicClosure (FractionRing R)) →+* (AlgebraicClosure (FractionRing V))) (b : D₁.toPre.P.A ⟶ D₂.toPre.P.A) (φ' : D₁.toPre.X ≃+ D₂.toPre.X), GlobalTheory.TInj.Ext f₁ j₁ → GlobalTheory.TInj.Ext f₂ j₂ → GlobalTheory.TInj.Match D₁.toPre D₂.toPre b φ' (AlgebraicClosure (FractionRing V)) → (∀ p₀ : QkPt C.P.D.toPre (AlgebraicClosure (FractionRing R)) l.M', ∃ (p₁ : QkPt D₁.toPre (AlgebraicClosure (FractionRing V)) l.M') (p₂ : QkPt D₂.toPre (AlgebraicClosure (FractionRing V)) l.M'), p₁.y = hD₁.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₁ hD₁ j₁ p₀.g p₁.g ∧ p₂.y = hD₂.xe.symm p₀.y ∧ GlobalTheory.TInj.Tr f₂ hD₂ j₂ p₀.g p₂.g ∧ GlobalTheory.TInj.QImg b φ' p₁ p₂) → (letI := H.starRing; ∀ x : 𝓞 E, ∃ (a₁ : D₁.toPre.P.A ⟶ D₁.toPre.P.A) (a₂ : D₂.toPre.P.A ⟶ D₂.toPre.P.A), a₁ ≫ hD₁.e.hom = hD₁.e.hom ≫ (Over.pullback (specOf f₁)).map (C.P.oD.onB.act x) ∧ a₂ ≫ hD₂.e.hom = hD₂.e.hom ≫ (Over.pullback (specOf f₂)).map (C.P.oD.onB.act x) ∧ a₁ ≫ b = b ≫ a₂) → (∀ y : C.P.D.toPre.X, hD₂.xe (φ' (hD₁.xe.symm y)) = y) → f₁.comp C.b = f₂.comp C.b → f₁.comp (Cn.ψ.comp MvPolynomial.C) = f₂.comp (Cn.ψ.comp MvPolynomial.C) := by
  first | exact @GlobalTheory.UCanon.PairBase.base_eq_of_match | exact GlobalTheory.UCanon.PairBase.base_eq_of_match | (intros; apply GlobalTheory.UCanon.PairBase.base_eq_of_match <;> assumption)
end
