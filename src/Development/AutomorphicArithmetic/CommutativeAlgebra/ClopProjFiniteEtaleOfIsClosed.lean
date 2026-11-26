module

public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
public import Development.AutomorphicArithmetic.CommutativeAlgebra.LevDefs
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorModuliObjectPullback

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFiniteEtaleOfIsClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

private lemma UpperTheory.isPullback_fst_snd_over {S : Scheme.{0}} {T G : Over S} :
    IsPullback (fst T G).left (snd T G).left T.hom G.hom :=
  IsPullback.of_hasPullback T.hom G.hom

theorem UpperTheory.clopProj_finite_etale_of_isClosed :
    ∀ {S : Scheme.{0}} {T G : Over S} (V : (T ⊗ G).left.Opens), IsFinite G.hom → Etale G.hom → IsClosed (V : Set (T ⊗ G).left) → IsFinite (UpperTheory.RepresentationRank.proj V) ∧ Etale (UpperTheory.RepresentationRank.proj V) := by
  intro S T G V hf he hV
  have hpb : IsPullback (snd T G).left (fst T G).left G.hom T.hom := UpperTheory.isPullback_fst_snd_over.flip
  haveI : IsClosedImmersion V.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [Scheme.Opens.range_ι]; exact hV)
  haveI : IsFinite (fst T G).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) hpb hf
  haveI : Etale (fst T G).left :=
    MorphismProperty.of_isPullback (P := @Etale) hpb he
  exact ⟨inferInstanceAs (IsFinite (V.ι ≫ (fst T G).left)),
    inferInstanceAs (Etale (V.ι ≫ (fst T G).left))⟩
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopRepPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.ClopPullback

variable {S S' : Scheme.{0}} (t : S' ⟶ S) (G Y : Over S)

private noncomputable def fwd (T' : Over S') :
    (T' ⊗ (Over.pullback t).obj G).left ⟶ ((Over.map t).obj T' ⊗ G).left :=
  pullback.lift (pullback.fst T'.hom (pullback.snd G.hom t))
    (pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t) (by
      have h := pullback.condition (f := T'.hom) (g := pullback.snd G.hom t)
      have h2 := pullback.condition (f := G.hom) (g := t)
      simp only [Over.map_obj_hom, Category.assoc, h2]
      rw [reassoc_of% h])

private noncomputable def bwd (T' : Over S') :
    ((Over.map t).obj T' ⊗ G).left ⟶ (T' ⊗ (Over.pullback t).obj G).left :=
  pullback.lift (pullback.fst (T'.hom ≫ t) G.hom)
    (pullback.lift (pullback.snd (T'.hom ≫ t) G.hom) (pullback.fst (T'.hom ≫ t) G.hom ≫ T'.hom)
      (by simpa using (pullback.condition (f := T'.hom ≫ t) (g := G.hom)).symm))
    (pullback.lift_snd _ _ _).symm

private theorem fwd_fst (T' : Over S') :
    fwd t G T' ≫ pullback.fst (T'.hom ≫ t) G.hom = pullback.fst T'.hom (pullback.snd G.hom t) :=
  pullback.lift_fst _ _ _

private theorem fwd_snd (T' : Over S') :
    fwd t G T' ≫ pullback.snd (T'.hom ≫ t) G.hom =
      pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t :=
  pullback.lift_snd _ _ _

private theorem bwd_fst (T' : Over S') :
    bwd t G T' ≫ pullback.fst T'.hom (pullback.snd G.hom t) = pullback.fst (T'.hom ≫ t) G.hom :=
  pullback.lift_fst _ _ _

private theorem bwd_snd_fst (T' : Over S') :
    bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t =
      pullback.snd (T'.hom ≫ t) G.hom := by
  unfold bwd
  erw [pullback.lift_snd_assoc, pullback.lift_fst]

private theorem fwd_bwd (T' : Over S') : fwd t G T' ≫ bwd t G T' = 𝟙 _ := by
  apply pullback.hom_ext
  · show fwd t G T' ≫ bwd t G T' ≫ pullback.fst T'.hom (pullback.snd G.hom t) =
      𝟙 _ ≫ pullback.fst T'.hom (pullback.snd G.hom t)
    rw [bwd_fst, fwd_fst, Category.id_comp]
  · show fwd t G T' ≫ bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) =
      𝟙 _ ≫ pullback.snd T'.hom (pullback.snd G.hom t)
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, bwd_snd_fst, fwd_snd]
      exact (Category.id_comp _).symm
    · have hb : bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.snd G.hom t =
          pullback.fst (T'.hom ≫ t) G.hom ≫ T'.hom := by
        unfold bwd
        erw [pullback.lift_snd_assoc, pullback.lift_snd]
      rw [Category.assoc, Category.assoc, hb, ← Category.assoc, fwd_fst, pullback.condition]
      exact (Category.id_comp _).symm

private theorem bwd_fwd (T' : Over S') : bwd t G T' ≫ fwd t G T' = 𝟙 _ := by
  apply pullback.hom_ext
  · show bwd t G T' ≫ fwd t G T' ≫ pullback.fst (T'.hom ≫ t) G.hom =
      𝟙 _ ≫ pullback.fst (T'.hom ≫ t) G.hom
    rw [fwd_fst, bwd_fst, Category.id_comp]
  · show bwd t G T' ≫ fwd t G T' ≫ pullback.snd (T'.hom ≫ t) G.hom =
      𝟙 _ ≫ pullback.snd (T'.hom ≫ t) G.hom
    rw [fwd_snd, bwd_snd_fst, Category.id_comp]

private noncomputable def cmp :
    ((Over.pullback t).obj Y ⊗ (Over.pullback t).obj G).left ⟶ (Y ⊗ G).left :=
  pullback.map _ _ _ _ (pullback.fst Y.hom t) (pullback.fst G.hom t) t
    (by simp [pullback.condition]) (by simp [pullback.condition])

private theorem key {T' : Over S'} (y' : T' ⟶ (Over.pullback t).obj Y) :
    (y' ▷ (Over.pullback t).obj G).left ≫ cmp t G Y =
      fwd t G T' ≫ (((Over.mapPullbackAdj t).homEquiv _ _).symm y' ▷ G).left := by
  set x := ((Over.mapPullbackAdj t).homEquiv _ _).symm y' with hx
  have a1 : (y' ▷ (Over.pullback t).obj G).left ≫
      pullback.fst ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom =
      pullback.fst T'.hom ((Over.pullback t).obj G).hom ≫ y'.left :=
    Over.whiskerRight_left_fst _
  have a2 : (y' ▷ (Over.pullback t).obj G).left ≫
      pullback.snd ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom =
      pullback.snd T'.hom ((Over.pullback t).obj G).hom :=
    Over.whiskerRight_left_snd _
  have b1 : (x ▷ G).left ≫ pullback.fst Y.hom G.hom =
      pullback.fst ((Over.map t).obj T').hom G.hom ≫ x.left :=
    Over.whiskerRight_left_fst _
  have b2 : (x ▷ G).left ≫ pullback.snd Y.hom G.hom =
      pullback.snd ((Over.map t).obj T').hom G.hom :=
    Over.whiskerRight_left_snd _
  have c1 : cmp t G Y ≫ pullback.fst Y.hom G.hom =
      pullback.fst ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫
        pullback.fst Y.hom t :=
    pullback.lift_fst _ _ _
  have c2 : cmp t G Y ≫ pullback.snd Y.hom G.hom =
      pullback.snd ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫
        pullback.fst G.hom t :=
    pullback.lift_snd _ _ _
  have hxl : x.left = y'.left ≫ pullback.fst Y.hom t := by
    simp [hx, Over.mapPullbackAdj]
  apply pullback.hom_ext
  · rw [Category.assoc, c1, ← Category.assoc, a1, Category.assoc, Category.assoc, b1,
      ← Category.assoc, hxl]
    exact congrArg (· ≫ y'.left ≫ pullback.fst Y.hom t) (fwd_fst t G T').symm
  · rw [Category.assoc, c2, ← Category.assoc, a2, Category.assoc, b2]
    exact (fwd_snd t G T').symm

end UpperTheory.ClopPullback

open UpperTheory.ClopPullback

private theorem UpperTheory.preimage_comp_scheme_opens_of_pullback {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  simp

private theorem UpperTheory.isClosed_preimage_opens_of_isClosed {X Y : Scheme.{0}} (f : X ⟶ Y) {W : Y.Opens}
    (hW : IsClosed (W : Set Y)) : IsClosed ((f ⁻¹ᵁ W : X.Opens) : Set X) :=
  hW.preimage f.continuous

private theorem UpperTheory.preimage_preimage_eq_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X)
    (W : X.Opens) : f ⁻¹ᵁ (g ⁻¹ᵁ W) = W := by
  rw [← UpperTheory.preimage_comp_scheme_opens_of_pullback, h]
  simp

theorem UpperTheory.exists_clopRep_pullback :
    ∀ {S S' : Scheme.{0}} (t : S' ⟶ S) (G Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U → ∃ U' : ((Over.pullback t).obj Y ⊗ (Over.pullback t).obj G).left.Opens, UpperTheory.RepresentationRank.Rep ((Over.pullback t).obj G) ((Over.pullback t).obj Y) U' := by
  intro S S' t G Y U hU
  refine ⟨cmp t G Y ⁻¹ᵁ U, UpperTheory.isClosed_preimage_opens_of_isClosed _ hU.1, ?_⟩
  intro T' V' hV'
  obtain ⟨y, hy, huniq⟩ := hU.2 ((Over.map t).obj T') (bwd t G T' ⁻¹ᵁ V')
    (UpperTheory.isClosed_preimage_opens_of_isClosed _ hV')
  have hpre : ∀ y' : T' ⟶ (Over.pullback t).obj Y,
      (y' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) =
        fwd t G T' ⁻¹ᵁ ((((Over.mapPullbackAdj t).homEquiv _ _).symm y' ▷ G).left ⁻¹ᵁ U) := by
    intro y'
    rw [← UpperTheory.preimage_comp_scheme_opens_of_pullback, key, UpperTheory.preimage_comp_scheme_opens_of_pullback]
  refine ⟨(Over.mapPullbackAdj t).homEquiv _ _ y, ?_, ?_⟩
  · show (((Over.mapPullbackAdj t).homEquiv _ _ y) ▷ (Over.pullback t).obj G).left ⁻¹ᵁ
        (cmp t G Y ⁻¹ᵁ U) = V'
    rw [hpre, Equiv.symm_apply_apply, hy]
    exact UpperTheory.preimage_preimage_eq_of_section _ _ (fwd_bwd t G T') V'
  · intro y'' hy''
    have hy2 : (y'' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) = V' := hy''
    have h1 : ((((Over.mapPullbackAdj t).homEquiv _ _).symm y'' ▷ G).left ⁻¹ᵁ U) =
        bwd t G T' ⁻¹ᵁ V' := by
      rw [← hy2, hpre, UpperTheory.preimage_preimage_eq_of_section _ _ (bwd_fwd t G T')]
    have h2 := huniq _ h1
    rw [← h2, Equiv.apply_symm_apply]
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsLevelObjPullbackOfCharZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Lev

noncomputable section

namespace UpperTheory.LevPull

open GlobalTheory.PELU
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison (pφ pφ₂ isSquare pφ₂_fst pφ₂_snd isGrpPullback gen_refl)
open GlobalTheory.HTPullEvery (lift_pφ₂ map_left_pφ push_map)

section Act

variable {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A]

private def pullAct (a : OActN O A) : OActN O ((Over.pullback f).obj A) where
  act c := (Over.pullback f).map (a.act c)
  hom c := by have := a.hom c; infer_instance
  one := by simp [a.one]
  mul b c := by simp [a.mul]
  add b c := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f A) _ ?_
    rw [map_mul]
    simp only [push_map, a.add, MonObj.comp_mul]

private theorem pullAct_sq (a : OActN O A) (c : O) :
    ((pullAct f a).act c).left ≫ pφ f A = pφ f A ≫ (a.act c).left :=
  map_left_pφ f A (a.act c)

private theorem push_pullAct (a : OActN O A) {T : Over S'} (u : T ⟶ (Over.pullback f).obj A) (c : O) :
    pushHom (isGrpPullback f A) T (u ≫ (pullAct f a).act c) = pushHom (isGrpPullback f A) T u ≫ a.act c := by
  apply Over.OverMorphism.ext
  change (u ≫ (pullAct f a).act c).left ≫ pφ f A = (u.left ≫ pφ f A) ≫ (a.act c).left
  simp [pullAct_sq]

end Act

section Tan

variable {S S' : Scheme.{0}} (f : S' ⟶ S) {O : Type} [Ring O] {A : Over S} [GrpObj A] [IsCommMonObj A]

private theorem tanScal_iff (a : OActN O A) {R' : Type} [CommRing R'] (x : Sp R' ⟶ S')
    (e : (epsPtR x ⟶ (Over.pullback f).obj A) ≃* (epsPtR (x ≫ f) ⟶ A))
    (he : ∀ v, (e v).left = v.left ≫ pφ f A) (c : O) (r : R') (v : epsPtR x ⟶ (Over.pullback f).obj A) :
    IsTanScal (pullAct f a) x c r v ↔ IsTanScal a (x ≫ f) c r (e v) := by
  have cart := isGrpPullback f A
  obtain ⟨e₀, he₀⟩ := GlobalTheory.LiePull.exists_pushEquiv cart (Over.mk x) (x ≫ f) rfl
  have unit : (1 : Over.mk (x ≫ f) ⟶ A).left = (1 : Over.mk x ⟶ (Over.pullback f).obj A).left ≫ pφ f A := by
    rw [← he₀, map_one]
  have retr : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ spMap (algebraMap R' (DualNumber R')) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
  have scale : spMap (epsScaleR r) ≫ spMap (algebraMap R' (DualNumber R')) =
      spMap (algebraMap R' (DualNumber R')) := by
    rw [← Spec.map_comp]
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have down : e (v ≫ (pullAct f a).act c) = e v ≫ a.act c := by
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, he, Category.assoc, pullAct_sq]
  have wv : v.left ≫ ((Over.pullback f).obj A).hom = spMap (algebraMap R' (DualNumber R')) ≫ x := Over.w v
  have wc : (v ≫ (pullAct f a).act c).left ≫ ((Over.pullback f).obj A).hom =
      spMap (algebraMap R' (DualNumber R')) ≫ x := Over.w _
  have w1 : (1 : Over.mk x ⟶ (Over.pullback f).obj A).left ≫ ((Over.pullback f).obj A).hom = x := Over.w _
  unfold IsTanScal
  rw [← down, he, he, unit]
  constructor
  · rintro ⟨h₁, h₂⟩
    exact ⟨by rw [← Category.assoc, h₁], by rw [h₂, Category.assoc]⟩
  · rintro ⟨h₁, h₂⟩
    refine ⟨cart.1.hom_ext (by simpa using h₁) ?_, cart.1.hom_ext (by simpa using h₂) ?_⟩
    · rw [Category.assoc, wv, w1, ← Category.assoc, retr, Category.id_comp]
    · rw [wc, Category.assoc, wv, ← Category.assoc, scale]

end Tan

section Tate

variable {G : GDatum}

private theorem tate_along {k : Type} [Field k] {Q Q' : Type} [Group Q] [Group Q']
    {act : G.O → Q → Q} {act' : G.O → Q' → Q'} {e : ℕ → Q → Q → kˣ → Prop} {e' : ℕ → Q' → Q' → kˣ → Prop}
    (I : GTateIso G k Q act e) (r : Q ≃* Q') (hact : ∀ c q, r (act c q) = act' c (r q))
    (hisom : ∀ n, 0 < n → ∀ x y, e' n (r (I.ev n x)) (r (I.ev n y)) (I.ζ n ^ (2 * G.EF x y))) :
    ∃ I' : GTateIso G k Q' act' e', ∀ n x, I'.ev n x = r (I.ev n x) :=
  ⟨{ ζ := I.ζ
     ζ_prim := I.ζ_prim
     ζ_pow := I.ζ_pow
     ev := fun n x => r (I.ev n x)
     add := fun n x y => by rw [I.add, map_mul]
     lin := fun n c x => by rw [I.lin, hact]
     ker := fun n hn x => by rw [map_eq_one_iff r r.injective, I.ker n hn]
     onto := fun n hn q => by
       have : q ^ n = 1 ↔ (r.symm q) ^ n = 1 := by
         rw [← map_pow, map_eq_one_iff r.symm r.symm.injective]
       rw [this, I.onto n hn]
       exact exists_congr fun x => by rw [MulEquiv.eq_symm_apply]
     tower := fun n m hn hm x => by rw [← map_pow, I.tower n m hn hm]
     isom := hisom }, fun _ _ => rfl⟩

end Tate

section Obj

variable {S S' : Scheme.{0}} (f : S' ⟶ S) {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R}
  {N : ℕ} {s : S ⟶ Sp R}

private theorem geom_of_pull (o : GObj gb N s) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') (k : Type) [Field k]
    [IsAlgClosed k] (x : Sp k ⟶ S') (β : R →+* k) (hx : x ≫ s' = spMap β) :
    ∃ I : GTateIso G k (Over.mk x ⟶ (Over.pullback f).obj o.A) (fun c g => g ≫ (pullAct f o.act).act c)
        (fun n g g' z => Out.WeilIs ((Over.pullback f).obj o.A)
          ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) n g g' (unitOn z)),
      ∀ y, toUnit _ ≫ GlobalTheory.SiegelPull.secPull (isGrpPullback f o.A) (o.eta y) = I.ev N y := by
  have cart := isGrpPullback f o.A
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv cart (Over.mk x) (x ≫ f) rfl
  obtain ⟨I, hI⟩ := o.geom k (x ≫ f) β (by rw [Category.assoc, hs, hx])
  have back : ∀ q, (e.symm q).left ≫ pφ f o.A = q.left := fun q => by rw [← he, e.apply_symm_apply]
  have hact : ∀ c q, e.symm (q ≫ o.act.act c) = e.symm q ≫ (pullAct f o.act).act c := by
    intro c q
    rw [MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    rw [he, Over.comp_left, Over.comp_left, Category.assoc, pullAct_sq, ← Category.assoc, back]
  have hisom : ∀ n : ℕ, 0 < n → ∀ a a', Out.WeilIs ((Over.pullback f).obj o.A)
      ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) (n : ℤ)
      (e.symm (I.ev n a)) (e.symm (I.ev n a')) (unitOn (I.ζ n ^ (2 * G.EF a a'))) := fun n hn a a' =>
    (GlobalTheory.weilIs_grpPullback_of_comm S S' o.A _ f (pφ f o.A) _ _ (pull_isLB o.isLB _)
      (pull_isLB (pull_isLB o.isLB _) _) cart
      (GlobalTheory.SiegelPull.diag_iso (isSquare f o.A) (gen_refl _ (pull_isLB o.isLB _))) (Over.mk x) n _ _
      (I.ev n a) (I.ev n a') _ (back _).symm (back _).symm).2 (I.isom n hn a a')
  obtain ⟨I', hI'⟩ := tate_along (Q' := Over.mk x ⟶ (Over.pullback f).obj o.A)
    (act' := fun c g => g ≫ (pullAct f o.act).act c)
    (e' := fun n g g' z => Out.WeilIs ((Over.pullback f).obj o.A)
      ((o.P.pull (pφ₂ f o.A)).pull (lift (𝟙 ((Over.pullback f).obj o.A)) (𝟙 _)).left) n g g' (unitOn z))
    I e.symm hact hisom
  refine ⟨I', fun y => ?_⟩
  rw [hI', MulEquiv.eq_symm_apply, ← hI y]
  refine Eq.trans ?_ (GlobalTheory.SiegelPull.push_secPull cart (o.eta y) (Over.mk x))
  apply Over.OverMorphism.ext
  rw [he]
  rfl

private def baseChange (o : GObj gb N s) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') : GObj gb N s' where
  A := (Over.pullback f).obj o.A
  ab :=
    { comm := by have := o.ab.comm; infer_instance
      smooth := by have := o.ab.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := by have := o.ab.proper; show IsProper (pullback.snd _ _); infer_instance
      geomConnected := by
        have := o.ab.geomConnected
        show GeometricallyConnected (pullback.snd _ _); infer_instance }
  act := pullAct f o.act
  P := o.P.pull (pφ₂ f o.A)
  isLB := pull_isLB o.isLB (pφ₂ f o.A)
  rig₁ := by
    obtain ⟨t, ht⟩ := o.rig₁
    exact gen_chartPull (chartPullLinComb o.P _ _ _ _ (pφ f o.A)
      fun _ => Pdiv.PullbackComparison.lift_one_id f o.A) t ht
  rig₂ := by
    obtain ⟨t, ht⟩ := o.rig₂
    exact gen_chartPull (chartPullLinComb o.P _ _ _ _ (pφ f o.A)
      fun _ => Pdiv.PullbackComparison.lift_id_one f o.A) t ht
  symm := LBIso.chartPull (chartPullPull o.P _ _ rfl)
    (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) fun _ => Pdiv.PullbackComparison.lift_swap f o.A) o.symm
  ample := (GlobalTheory.pol_pull S S' o.A _ f (pφ f o.A) _ _ (pull_isLB o.isLB _) (pull_isLB (pull_isLB o.isLB _) _) o.ab
    (isGrpPullback f o.A) (GlobalTheory.SiegelPull.diag_iso (isSquare f o.A) (gen_refl _ (pull_isLB o.isLB _)))).2.1 o.ample
  rosati c := by
    have h₁ : (fst ((Over.pullback f).obj o.A) _ ≫ (pullAct f o.act).act c).left ≫ pφ f o.A =
        pφ₂ f o.A ≫ (fst o.A o.A ≫ o.act.act c).left := by
      simp only [Over.comp_left, Category.assoc, pullAct_sq]
      rw [← Category.assoc, ← pφ₂_fst, Category.assoc]
    have h₂ : (snd ((Over.pullback f).obj o.A) _ ≫ (pullAct f o.act).act (G.star c).unop).left ≫ pφ f o.A =
        pφ₂ f o.A ≫ (snd o.A o.A ≫ o.act.act (G.star c).unop).left := by
      simp only [Over.comp_left, Category.assoc, pullAct_sq]
      rw [← Category.assoc, ← pφ₂_snd, Category.assoc]
    exact LBIso.chartPull
      (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) fun _ =>
        lift_pφ₂ f o.A _ _ _ _ h₁ (pφ₂_snd f o.A).symm)
      (chartPullLinComb o.P _ _ _ _ (pφ₂ f o.A) fun _ =>
        lift_pφ₂ f o.A _ _ _ _ (pφ₂_fst f o.A).symm h₂)
      (o.rosati c)
  lie R' _ β x hx v hv := by
    obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv (isGrpPullback f o.A) (epsPtR x)
      (spMap (algebraMap R' (DualNumber R')) ≫ x ≫ f) (Category.assoc _ _ _).symm
    obtain ⟨w, hw, hsum⟩ := o.lie R' β (x ≫ f) (by rw [Category.assoc, hs, hx]) (e v)
      ((tanScal_iff f o.act x e he _ _ v).1 hv)
    refine ⟨fun i => e.symm (w i), fun i c => ?_, ?_⟩
    · rw [tanScal_iff f o.act x e he, e.apply_symm_apply]
      exact hw i c
    · rw [← e.symm_apply_apply v, hsum, map_list_prod, List.map_ofFn]
      rfl
  lieRank k _ _ x β hx i :=
    (GlobalTheory.LiePull.lieMult_pull (𝓞 G.F) S S' o.A _ f (pφ f o.A) (actF o.act) (actF (pullAct f o.act))
      (isGrpPullback f o.A) (fun c => pullAct_sq f o.act _) k x _ G.m).2
      (o.lieRank k (x ≫ f) β (by rw [Category.assoc, hs, hx]) i)
  eta y := GlobalTheory.SiegelPull.secPull (isGrpPullback f o.A) (o.eta y)
  eta_add y y' := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ ?_
    simp only [map_mul, GlobalTheory.SiegelPull.push_secPull', o.eta_add, MonObj.comp_mul]
  eta_lin c y := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ ?_
    simp only [push_pullAct, GlobalTheory.SiegelPull.push_secPull', o.eta_lin, Category.assoc]
  eta_ker y := by
    refine GlobalTheory.SiegelPull.push_injective (isGrpPullback f o.A) _ ?_
    simp only [map_one, GlobalTheory.SiegelPull.push_secPull', o.eta_ker, MonObj.comp_one]
  geom k _ _ x β hx := geom_of_pull f o s' hs k x β hx

private def baseChangeMap (o : GObj gb N s) (s' : S' ⟶ Sp R) (hs : f ≫ s = s') :
    GObjMap (baseChange f o s' hs) o f where
  φ := pφ f o.A
  φ₂ := pφ₂ f o.A
  cart := isGrpPullback f o.A
  sq := isSquare f o.A
  act c := pullAct_sq f o.act c
  pol := gen_refl _ (pull_isLB o.isLB _)
  eta y := GlobalTheory.SiegelPull.secPull_left (isGrpPullback f o.A) _

end Obj

end UpperTheory.LevPull

theorem UpperTheory.exists_levelObj_pullback_of_charZero :
    ∀ {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N : ℕ} {S S' : Scheme.{0}} {s : S ⟶ Sp R}
        (s' : S' ⟶ Sp R) (f : S' ⟶ S), f ≫ s = s' → ∀ o : GObj gb N s, ∃ o' : GObj gb N s', Nonempty (GObjMap o' o f) :=
  fun s' f hs o => ⟨_, ⟨UpperTheory.LevPull.baseChangeMap f o s' hs⟩⟩
end
end
