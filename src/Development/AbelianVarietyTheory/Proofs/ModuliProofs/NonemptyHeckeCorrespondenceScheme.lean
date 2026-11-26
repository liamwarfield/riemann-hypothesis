module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformisationExistenceAndTorsionStatements
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeKernelSchemeUniversalReducedBases
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEtaleHasHeckeQuotientNoetherianDomain

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsogOfSurjectiveBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.IsogDescent

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G₁ G₂ : Over S} {G₁' G₂' : Over S'}

theorem over_ext {T G : Over S} [IsReduced T.left] [IsSeparated G.hom] {a b : T ⟶ G} {W : Scheme.{0}}
    (q : W ⟶ T.left) [Surjective q] (h : q ≫ a.left = q ≫ b.left) : a = b :=
  Over.OverMorphism.ext (ext_of_isDominant_of_isSeparated G.hom ((Over.w a).trans (Over.w b).symm) q h)

variable [GrpObj G₁] [GrpObj G₂] [GrpObj G₁'] [GrpObj G₂'] {φ₁ : G₁'.left ⟶ G₁.left} {φ₂ : G₂'.left ⟶ G₂.left}

theorem mul_comp [Surjective f] [IsSeparated G₂.hom] (h₁ : IsGrpPullback G₁' G₁ f φ₁)
    (h₂ : IsGrpPullback G₂' G₂ f φ₂) (ψ : G₁ ⟶ G₂) (ψ' : G₁' ⟶ G₂') [IsMonHom ψ']
    (hψ : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) (T : Over S) [IsReduced T.left] (x y : T ⟶ G₁) :
    (x * y) ≫ ψ = (x ≫ ψ) * (y ≫ ψ) := by
  have H := IsPullback.of_hasPullback T.hom f
  let q := pullback.fst T.hom f
  let W : Over S' := Over.mk (pullback.snd T.hom f)
  let l : (T ⟶ G₁) → (W ⟶ G₁') := fun z => Over.homMk
    (h₁.1.lift (q ≫ z.left) (pullback.snd T.hom f) (by rw [Category.assoc, Over.w z]; exact H.w))
    (h₁.1.lift_snd _ _ _)
  have hl : ∀ z, (l z).left ≫ φ₁ = q ≫ z.left := fun z => h₁.1.lift_fst _ _ _
  let q' : Over.mk (W.hom ≫ f) ⟶ T := Over.homMk q H.w
  have hl' : ∀ z, (q' ≫ z ≫ ψ).left = (l z ≫ ψ').left ≫ φ₂ := fun z => by
    show q ≫ z.left ≫ ψ.left = ((l z).left ≫ ψ'.left) ≫ φ₂
    rw [Category.assoc, hψ, ← Category.assoc (l z).left, hl, Category.assoc]
  have e₁ := h₁.2 W (l x) (l y) (q' ≫ x) (q' ≫ y) (hl x).symm (hl y).symm
  have e₂ := h₂.2 W (l x ≫ ψ') (l y ≫ ψ') (q' ≫ x ≫ ψ) (q' ≫ y ≫ ψ) (hl' x) (hl' y)
  rw [← MonObj.comp_mul] at e₁ e₂
  rw [← MonObj.mul_comp (l x) (l y) ψ'] at e₂
  replace e₂ : _ = (l x * l y).left ≫ ψ'.left ≫ φ₂ := e₂.trans (Category.assoc _ _ _)
  rw [hψ, ← Category.assoc, ← e₁] at e₂
  refine over_ext q ?_
  refine Eq.trans ?_ e₂.symm
  exact (Category.assoc _ _ _).symm

theorem isMonHom [IsReduced S] [Surjective f] [Smooth G₁.hom] [IsSeparated G₂.hom] (h₁ : IsGrpPullback G₁' G₁ f φ₁)
    (h₂ : IsGrpPullback G₂' G₂ f φ₂) (ψ : G₁ ⟶ G₂) (ψ' : G₁' ⟶ G₂') [IsMonHom ψ']
    (hψ : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) : IsMonHom ψ := by
  have : IsReduced (𝟙_ (Over S)).left := ‹IsReduced S›
  have : Smooth (G₁ ⊗ G₁).hom := inferInstanceAs (Smooth (pullback.fst G₁.hom G₁.hom ≫ G₁.hom))
  have : IsReduced (G₁ ⊗ G₁).left := GlobalTheory.isReduced_of_smooth_of_isReduced (G₁ ⊗ G₁).hom
  refine ⟨?_, ?_⟩
  · have h := mul_comp h₁ h₂ ψ ψ' hψ (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S) ⟶ G₁) ≫ ψ = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul_comp h₁ h₂ ψ ψ' hψ (G₁ ⊗ G₁) (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1

theorem kerSet [Surjective f] [IsSeparated G₂.hom] (h₁ : IsPullback φ₁ G₁'.hom G₁.hom f)
    (h₂ : IsPullback φ₂ G₂'.hom G₂.hom f) (he : η[G₂'].left ≫ φ₂ = f ≫ η[G₂].left) (ψ : G₁ ⟶ G₂) (ψ' : G₁' ⟶ G₂')
    (hψ : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) (K : Set G₁.left) (hK : KerSet ψ' (φ₁ ⁻¹' K)) : KerSet ψ K := by
  intro k _ _ x z
  obtain ⟨w, -⟩ := (pullback.fst x f).surjective (default : PrimeSpectrum k)
  let k' := AlgebraicClosure ((pullback x f).residueField w)
  let u : Sp k' ⟶ pullback x f :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback x f).residueField w) k')) ≫ (pullback x f).fromSpecResidueField w
  let j : Sp k' ⟶ Sp k := u ≫ pullback.fst x f
  let x' : Sp k' ⟶ S' := u ≫ pullback.snd x f
  have hj : j ≫ x = x' ≫ f := by simp only [j, x', Category.assoc, pullback.condition]
  have : Surjective j := ⟨fun a => ⟨(default : PrimeSpectrum k'), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  let z' : Over.mk x' ⟶ G₁' := Over.homMk (h₁.lift (j ≫ z.left) x' (by rw [Category.assoc, Over.w z]; exact hj))
    (h₁.lift_snd _ _ _)
  have hz : z'.left ≫ φ₁ = j ≫ z.left := h₁.lift_fst _ _ _
  have a₁ : (z' ≫ ψ').left ≫ φ₂ = j ≫ (z ≫ ψ).left := by
    rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc, hz, Category.assoc]
    rfl
  have a₂ : (1 : Over.mk x' ⟶ G₂').left ≫ φ₂ = j ≫ (1 : Over.mk x ⟶ G₂).left := by
    show (x' ≫ η[G₂'].left) ≫ φ₂ = j ≫ x ≫ η[G₂].left
    rw [Category.assoc, he, ← Category.assoc, ← hj, Category.assoc]
  have : IsReduced (Over.mk x).left := inferInstanceAs (IsReduced (Spec (CommRingCat.of k)))
  have b₁ : z ≫ ψ = 1 ↔ z' ≫ ψ' = 1 :=
    ⟨fun h => Over.OverMorphism.ext (h₂.hom_ext (by rw [a₁, a₂, h]) ((Over.w _).trans (Over.w _).symm)),
      fun h => over_ext (T := Over.mk x) j (by rw [← a₁, ← a₂, h])⟩
  have pt : ∀ a, φ₁ (z'.left a) = z.left (j a) := fun a => congrArg (fun q => q a) hz
  rw [b₁, hK k' x' z']
  constructor
  · rintro h _ ⟨a, rfl⟩
    obtain ⟨a', rfl⟩ := j.surjective a
    rw [← pt]
    exact h ⟨a', rfl⟩
  · rintro h _ ⟨a, rfl⟩
    show φ₁ (z'.left a) ∈ K
    rw [pt]
    exact h ⟨_, rfl⟩

end Grp

section Bundle

theorem exists_gen_pow {X Y : Scheme.{0}} (L : LB X) (e : Y ⟶ X) (n : ℤ) (t : (L.pull e).Gen) (ht : t.IsGen) :
    ∃ c : (LB.LinComb L (K := PUnit) (fun _ => e) (fun _ => n)).Gen, c.IsGen := by
  refine ⟨⟨fun j => (t.s j) ^ n⟩, fun i j => ?_⟩
  refine (map_zpow _ _ _).trans ((congrArg (· ^ n) (ht i j)).trans ((mul_zpow _ _ _).trans
    (congrArg₂ (· * ·) ?_ (map_zpow _ _ _).symm)))
  simp only [LB.pull, LB.LinComb, Fintype.prod_unique, zpow_one]
  rfl

theorem lbIso_of_surjective {S S' X' : Scheme.{0}} [IsReduced S] (A : Over S) [GrpObj A] [IsCommMonObj A]
    (M : LB A.left) (hA : IsAbelianScheme A) (hM : M.IsLB) (ha : Out.RelAmple A M) {f : S' ⟶ S} [Surjective f]
    {φ : X' ⟶ A.left} {g : X' ⟶ S'} (h : IsPullback φ g A.hom f) {P Q : LB A.left} (hP : P.IsLB) (hQ : Q.IsLB)
    (hi : LBIso (P.pull φ) (Q.pull φ)) (s : (P.pull (eSec A)).Gen) (hs : s.IsGen) (t : (Q.pull (eSec A)).Gen)
    (ht : t.IsGen) : LBIso P Q := by
  refine GlobalTheory.seesaw_reduced_of_dense GlobalTheory.globalFns_holds S A M hA hM ha S A.left (𝟙 S) (𝟙 _) A.hom (LB.div Q P)
    (IsPullback.id_horiz _) (LB.isLB_div hQ hP) ?_ (eSec A) (Over.w η[A]) ?_
  · obtain ⟨w, hw⟩ := hi
    obtain ⟨c, hc⟩ := gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q φ) w hw
    refine dense_univ.mono fun p _ => ?_
    obtain ⟨p', rfl⟩ := f.surjective p
    let x' : Sp (S'.residueField p') ⟶ S' := S'.fromSpecResidueField p'
    refine ⟨S'.residueField p', inferInstance, x' ≫ f, pullback g x', pullback.fst g x' ≫ φ, pullback.snd g x',
      ⟨(default : PrimeSpectrum (S'.residueField p')), congrArg f (Scheme.fromSpecResidueField_apply p' _)⟩,
      (IsPullback.of_hasPullback g x').paste_horiz h, ?_⟩
    exact gen_chartPull (chartPullSame (LB.div Q P) (K := PUnit) _ (fun _ => φ) (fun _ => 1) (pullback.fst g x')
      fun _ => rfl) c hc
  · obtain ⟨w, hw⟩ := GlobalTheory.SabMapDescent.lbIso_of_gen_of_gen s hs t ht
    exact gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q _) w hw

end Bundle

end GlobalTheory.IsogDescent


open GlobalTheory.IsogDescent in
theorem GlobalTheory.isIsog_of_surjective_baseChange :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (p : ℕ) (S S' : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (o₁ o₂ : Ob D l s) (o₁' o₂' : Ob D l s') (n₁ : ObjMap o₁' o₁ f) (n₂ : ObjMap o₂' o₂ f) (ψ : o₁.t.G ⟶ o₂.t.G) (ψ' : o₁'.t.G ⟶ o₂'.t.G), Surjective f → ψ'.left ≫ n₂.toSABMap.φ = n₁.toSABMap.φ ≫ ψ.left → IsIsog o₁' o₂' p ψ' → IsFinite ψ.left → Etale ψ.left → IsIsog o₁ o₂ p ψ ∧ ∀ K, KerSet ψ' (n₁.toSABMap.φ ⁻¹' K) → KerSet ψ K := by
  intro E _ _ _ H D l p S S' _ s s' f o₁ o₂ o₁' o₂' n₁ n₂ ψ ψ' hf hψ ⟨⟨hm, _, _, hsurj, hact, hL⟩, hlev⟩ hfin het
  have := o₁.t.semi.smooth
  have := o₂.proper
  have : IsReduced o₁.t.G.left := GlobalTheory.isReduced_of_smooth_of_isReduced o₁.t.G.hom
  have : IsReduced (𝟙_ (Over S)).left := ‹IsReduced S›
  have : Surjective n₁.cm.F := MorphismProperty.of_isPullback (P := @Surjective) n₁.cart.1.flip hf
  have : Surjective n₂.cm.F := MorphismProperty.of_isPullback (P := @Surjective) n₂.cart.1.flip hf
  have hψ : ψ'.left ≫ n₂.cm.F = n₁.cm.F ≫ ψ.left := hψ
  have hmon : IsMonHom ψ := isMonHom n₁.cart n₂.cart ψ ψ' hψ
  have sec : ∀ {a : 𝟙_ (Over S) ⟶ o₁.t.G} {b : 𝟙_ (Over S) ⟶ o₂.t.G} {a' : 𝟙_ (Over S') ⟶ o₁'.t.G}
      {b' : 𝟙_ (Over S') ⟶ o₂'.t.G}, a'.left ≫ n₁.cm.F = f ≫ a.left → b'.left ≫ n₂.cm.F = f ≫ b.left →
      a' ≫ ψ' = b' → a ≫ ψ = b := fun {a b a' b'} ha hb h =>
    over_ext (T := 𝟙_ (Over S)) f (by
      rw [← hb, ← h, Over.comp_left, Over.comp_left, Category.assoc, hψ, ← Category.assoc, ← Category.assoc, ha])
  refine ⟨⟨⟨hmon, hfin, het, ?_, fun a => over_ext n₁.cm.F ?_, ?_⟩, fun p' hp a =>
    ⟨sec (n₁.eta _) (n₂.eta _) (hlev p' hp a).1, sec (n₁.etaA _) (n₂.etaA _) (hlev p' hp a).2⟩⟩, fun K hK =>
    kerSet n₁.cart.1 n₂.cart.1 (n₂.cm.e_comm.trans (by rw [n₂.base]; rfl)) ψ ψ' hψ K hK⟩
  · have : Surjective (n₁.cm.F ≫ ψ.left) := by rw [← hψ]; infer_instance
    exact Surjective.of_comp n₁.cm.F _
  · have e := congrArg (fun q => q.left) (hact a)
    simp only [Over.comp_left] at e ⊢
    rw [← Category.assoc, ← n₁.act, Category.assoc, ← hψ, ← Category.assoc, e, Category.assoc, n₂.act,
      ← Category.assoc, hψ, Category.assoc]
  · have hP : (lbPow o₁.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb o₁.t.PP.isLB _ _
    have hP' : (lbPow o₁'.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb o₁'.t.PP.isLB _ _
    have hQ := pull_isLB o₂.t.PP.isLB ψ.left
    obtain ⟨c, hc⟩ := GlobalTheory.IsogDescent.exists_gen_pow o₁.t.PP.L _ ((p ^ 2 : ℕ) : ℤ) o₁.t.PP.rig o₁.t.PP.rigGen
    obtain ⟨c₁, hc₁⟩ := gen_chartPull (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ))
      (eSec o₁.t.G) (fun _ => eSec o₁.t.G) fun _ => (Category.comp_id _).symm) c hc
    obtain ⟨c₂, hc₂⟩ := gen_chartPull (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) (fun _ => 1)
      (eSec o₁.t.G) (fun _ => eSec o₂.t.G) fun _ => (congrArg (fun q => q.left) hmon.one_hom).symm)
      o₂.t.PP.rig o₂.t.PP.rigGen
    refine lbIso_of_surjective o₁.t.G o₁.t.PP.L (GlobalTheory.ObjDim.isAbelianScheme o₁) o₁.t.PP.isLB o₁.ample n₁.cart.1 hP hQ
      ?_ c₁ hc₁ c₂ hc₂
    obtain ⟨w₁, hw₁, -⟩ := n₁.lin
    obtain ⟨w₂, hw₂, -⟩ := n₂.lin
    have i₁ : LBIso (lbPow o₁'.t.PP.L (p ^ 2)) ((lbPow o₁.t.PP.L (p ^ 2)).pull n₁.cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) _ n₁.cm.F _
        fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
        (iso_linComb ((isGen_iff w₁).1 hw₁) (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ)))
    have i₂ : LBIso (o₂'.t.PP.L.pull ψ'.left) ((o₂.t.PP.L.pull ψ.left).pull n₁.cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) _ n₁.cm.F _ fun _ => hψ)
        (iso_linComb ((isGen_iff w₂).1 hw₂) (K := PUnit) (fun _ => ψ'.left) (fun _ => 1))
    exact LBIso.trans (pull_isLB hP _) hP' (pull_isLB hQ _) i₁.symm
      (LBIso.trans hP' (pull_isLB o₂'.t.PP.isLB _) (pull_isLB hQ _) hL i₂)

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientDescendsEtaleSurjectiveCover
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientDescendsEtaleSurjectiveCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem desc_pull {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)} (s' : S' ⟶ Sp (KA l)) (f : S' ⟶ S) (h : f ≫ s = s')
    (o : Ob D l s) : ∃ o' : Ob D l s', Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s s' f rfl rfl
    (by rw [h]; simp [spMap]) o

theorem desc_comp {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} (m : ObjMap o' o f)
    (m' : ObjMap o'' o' f') :
    ∃ m'' : ObjMap o'' o (f' ≫ f), m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ :=
  ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).1 m'

theorem desc_cancel {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {g : S'' ⟶ S} (m : ObjMap o' o f)
    (m'' : ObjMap o'' o g) (e : f' ≫ f = g) :
    ∃ m' : ObjMap o'' o' f', m''.toSABMap.φ = m'.toSABMap.φ ≫ m.toSABMap.φ := by
  subst e
  exact ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).2 m''

theorem desc_cocycle (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) {S S' : Scheme.{0}} [IsReduced S']
    {s : S ⟶ Sp (KA l)} (π : S' ⟶ S) [Etale π] (o : Ob D l s) (o' o₂' : Ob D l (π ≫ s)) (m : ObjMap o' o π)
    (K : Set o.t.G.left) (hA : admitted l 𝔓 p) (hK : HeckeSet D o.t 𝔓 p i K) (ψ' : o'.t.G ⟶ o₂'.t.G)
    (hψ : IsIsog o' o₂' p ψ') (hker : KerSet ψ' (m.toSABMap.φ ⁻¹' K)) (f' : S' ⟶ Xo.X) (hf' : f' ≫ Xo.s = π ≫ s)
    (n' : ObjMap o₂' Xo.univ f') :
    (∀ {Z : Scheme.{0}} (x y : Z ⟶ S'), x ≫ π = y ≫ π → x ≫ f' = y ≫ f') ∧
    ∀ {Z : Scheme.{0}} (x y : Z ⟶ o'.t.G.left), x ≫ m.toSABMap.φ = y ≫ m.toSABMap.φ →
      x ≫ ψ'.left ≫ n'.toSABMap.φ = y ≫ ψ'.left ≫ n'.toSABMap.φ := by
  have hab : pullback.fst π π ≫ π = pullback.snd π π ≫ π := pullback.condition
  haveI : IsReduced (pullback π π) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst π π)
  obtain ⟨oT, ⟨mT⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.fst π π ≫ π) (by simp) o
  obtain ⟨ma, hma⟩ := desc_cancel (f' := pullback.fst π π) m mT rfl
  obtain ⟨mb, hmb⟩ := desc_cancel (f' := pullback.snd π π) m mT hab.symm
  obtain ⟨oa, ⟨na⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.fst π π) rfl o₂'
  obtain ⟨ob, ⟨nb⟩⟩ := desc_pull (pullback.fst π π ≫ π ≫ s) (pullback.snd π π)
    (by rw [reassoc_of% hab]) o₂'
  obtain ⟨⟨ψa, hψa, -⟩, Ha⟩ := GlobalTheory.HkFam.isog_pull E H D l p _ _ _ _ _ o' o₂' oT oa ma na ψ'
  obtain ⟨⟨ψb, hψb, -⟩, Hb⟩ := GlobalTheory.HkFam.isog_pull E H D l p _ _ _ _ _ o' o₂' oT ob mb nb ψ'
  obtain ⟨ia, ka⟩ := Ha ψa hψa
  obtain ⟨ib, kb⟩ := Hb ψb hψb
  have ka' : KerSet ψa (mT.toSABMap.φ ⁻¹' K) := by
    have := ka _ hψ.1.1 hker
    rw [hma]; simpa [Set.preimage_comp] using this
  have kb' : KerSet ψb (mT.toSABMap.φ ⁻¹' K) := by
    have := kb _ hψ.1.1 hker
    rw [hmb]; simpa [Set.preimage_comp] using this
  have hKT : HeckeSet D oT.t 𝔓 p i (mT.toSABMap.φ ⁻¹' K) :=
    ((GlobalTheory.heckeSets_pull E H D 𝔓 p i _ _ o.t oT.t _ mT.toSABMap o.proper).2 K).1 hK
  obtain ⟨na', hna⟩ := desc_comp n' na
  obtain ⟨nb', hnb⟩ := desc_comp n' nb
  obtain ⟨e₁, e₂⟩ := GlobalTheory.T.heckeQuotient_classifyingMap_isogeny_unique E H D l Xo 𝔓 p i _ _ oT oa ob ψa ψb _ _ _ na' nb' hA hKT
    (by rw [Category.assoc, hf']) (by rw [Category.assoc, hf', reassoc_of% hab]) (ia hψ) (ib hψ) ka' kb'
  rw [hna, hnb, reassoc_of% hψa, reassoc_of% hψb] at e₂
  refine ⟨fun x y hxy => ?_, fun x y hxy => ?_⟩
  · have := pullback.lift x y hxy ≫= e₁
    rwa [pullback.lift_fst_assoc, pullback.lift_snd_assoc] at this
  · have pm : IsPullback m.toSABMap.φ o'.t.G.hom o.t.G.hom π := m.cart.1
    have pa : IsPullback ma.toSABMap.φ oT.t.G.hom o'.t.G.hom (pullback.fst π π) := ma.cart.1
    have pb : IsPullback mb.toSABMap.φ oT.t.G.hom o'.t.G.hom (pullback.snd π π) := mb.cart.1
    have h₀ : (x ≫ o'.t.G.hom) ≫ π = (y ≫ o'.t.G.hom) ≫ π := by
      simp only [Category.assoc, ← pm.w, reassoc_of% hxy]
    let w := pa.lift x (pullback.lift _ _ h₀) (pullback.lift_fst _ _ _).symm
    have wa : w ≫ ma.toSABMap.φ = x := pa.lift_fst _ _ _
    have wb : w ≫ mb.toSABMap.φ = y := by
      apply pm.hom_ext
      · rw [Category.assoc, ← hmb, hma, reassoc_of% wa, hxy]
      · rw [Category.assoc, pb.w, pa.lift_snd_assoc, pullback.lift_snd]
    rw [← wa, ← wb, Category.assoc, Category.assoc, e₂]

theorem hasQuot_descend : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S S' : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (π : S' ⟶ S) (o : Ob D l s) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → Etale π → Surjective π → QuasiCompact π → HasQuot o' p (m.toSABMap.φ ⁻¹' K) → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i S S' _ s π o o' m K hA hK hE hS hQ ⟨o₂', ψ', hψ, hker⟩
  haveI : IsReduced S' := GlobalTheory.isReduced_of_smooth_of_isReduced π
  obtain ⟨f', ⟨hf', ⟨n'⟩⟩, -⟩ := Xo.rep S' (π ≫ s) inferInstance o₂'
  obtain ⟨c₁, c₂⟩ := desc_cocycle Xo 𝔓 p i π o o' o₂' m K hA hK ψ' hψ hker f' hf' n'
  have pm : IsPullback m.toSABMap.φ o'.t.G.hom o.t.G.hom π := m.cart.1
  have pn' : IsPullback n'.toSABMap.φ o₂'.t.G.hom Xo.univ.t.G.hom f' := n'.cart.1
  haveI : Flat m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip (inferInstance : Flat π)
  haveI : Surjective m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip hS
  haveI : QuasiCompact m.toSABMap.φ := MorphismProperty.of_isPullback pm.flip hQ
  haveI : EffectiveEpi π := inferInstance
  haveI : EffectiveEpi m.toSABMap.φ := inferInstance
  obtain ⟨f, hf⟩ : ∃ f : S ⟶ Xo.X, π ≫ f = f' := ⟨_, EffectiveEpi.fac π f' c₁⟩
  obtain ⟨h, hh⟩ : ∃ h, m.toSABMap.φ ≫ h = ψ'.left ≫ n'.toSABMap.φ := ⟨_, EffectiveEpi.fac _ _ c₂⟩
  have hfs : f ≫ Xo.s = s := by rw [← cancel_epi π, reassoc_of% hf, hf']
  obtain ⟨o₂, ⟨n⟩⟩ := desc_pull s f hfs Xo.univ
  obtain ⟨n₂, hn₂⟩ := desc_cancel n n' hf
  have pn : IsPullback n.toSABMap.φ o₂.t.G.hom Xo.univ.t.G.hom f := n.cart.1
  have pn₂ : IsPullback n₂.toSABMap.φ o₂'.t.G.hom o₂.t.G.hom π := n₂.cart.1
  have hw : h ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ f := by
    rw [← cancel_epi m.toSABMap.φ, reassoc_of% hh, pn'.w, pm.w_assoc, hf, Over.w_assoc]
  let ψ : o.t.G ⟶ o₂.t.G := Over.homMk (pn.lift h _ hw) (pn.lift_snd _ _ _)
  have hψn : ψ.left ≫ n.toSABMap.φ = h := pn.lift_fst _ _ _
  have sq : ψ'.left ≫ n₂.toSABMap.φ = m.toSABMap.φ ≫ ψ.left := by
    apply pn.hom_ext
    · rw [Category.assoc, Category.assoc, ← hn₂, hψn, hh]
    · rw [Category.assoc, Category.assoc, pn₂.w, Over.w_assoc, Over.w, pm.w]
  have P : IsPullback m.toSABMap.φ ψ'.left ψ.left n₂.toSABMap.φ :=
    IsPullback.of_bot (by rw [Over.w, Over.w]; exact pm) sq.symm pn₂
  have q : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) n₂.toSABMap.φ :=
    ⟨⟨MorphismProperty.of_isPullback pn₂.flip hS,
      MorphismProperty.of_isPullback pn₂.flip (inferInstance : Flat π)⟩,
      MorphismProperty.of_isPullback pn₂.flip hQ⟩
  have hEt : Etale ψ.left :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @Etale) P.flip q hψ.1.2.2.1
  haveI : IsFinite ψ'.left := hψ.1.2.1
  haveI : IsAffineHom ψ.left := by
    refine GlobalTheory.isAffineHom_of_isAffineHom_pullback_snd_of_fpqc _ _ _ ψ.left n₂.toSABMap.φ q.1.1 q.1.2 q.2 ?_
    rw [← P.isoPullback_inv_snd]
    infer_instance
  haveI := o₂.proper
  haveI : IsProper (ψ.left ≫ o₂.t.G.hom) := by rw [Over.w]; exact o.proper
  haveI : IsProper ψ.left := IsProper.of_comp ψ.left o₂.t.G.hom
  have hFin : IsFinite ψ.left := IsFinite.iff_isProper_and_isAffineHom.2 ⟨inferInstance, inferInstance⟩
  obtain ⟨r₁, r₂⟩ := GlobalTheory.isIsog_of_surjective_baseChange E H D l p S S' s _ π o o₂ o' o₂' m n₂ ψ ψ' hS sq hψ hFin hEt
  exact ⟨o₂, ψ, r₁, r₂ K hker⟩

end GlobalTheory.HkFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientDescendsEtaleSurjectiveCoverStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_descends_etale_surjective_cover : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S S' : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (π : S' ⟶ S) (o : Ob D l s) (o' : Ob D l (π ≫ s)) (m : ObjMap o' o π) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → Etale π → Surjective π → QuasiCompact π → HasQuot o' p (m.toSABMap.φ ⁻¹' K) → HasQuot o p K := by
  first | exact @GlobalTheory.HkFam.hasQuot_descend | exact GlobalTheory.HkFam.hasQuot_descend | (intros; apply GlobalTheory.HkFam.hasQuot_descend <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientExistsListedKernelsSmoothBase
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientOfOpenCoverReducedBase
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientOfOpenCoverReducedBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

noncomputable section

namespace GlobalTheory.QuotGlue

section Cover

variable {I : Type} {X Y S : Scheme.{0}} {V : I → Scheme.{0}}

theorem cover_ext (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x) {a b : X ⟶ Y}
    (h : ∀ i, f i ≫ a = f i ≫ b) : a = b :=
  Scheme.Cover.hom_ext (Scheme.Cover.mkOfCovers I V f hc) a b h

theorem cover_glue (f : ∀ i, V i ⟶ X) [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x) (g : ∀ i, V i ⟶ Y)
    (h : ∀ i j, pullback.fst (f i) (f j) ≫ g i = pullback.snd _ _ ≫ g j) : ∃ a : X ⟶ Y, ∀ i, f i ≫ a = g i :=
  ⟨Scheme.Cover.glueMorphisms (Scheme.Cover.mkOfCovers I V f hc) g h,
    Scheme.Cover.ι_glueMorphisms (Scheme.Cover.mkOfCovers I V f hc) g h⟩

theorem cover_pull {f : ∀ i, V i ⟶ S} (hc : ∀ x, ∃ i y, f i y = x) {p : X ⟶ S} {W : I → Scheme.{0}}
    {φ : ∀ i, W i ⟶ X} {q : ∀ i, W i ⟶ V i} (h : ∀ i, IsPullback (φ i) (q i) p (f i)) (x : X) : ∃ i y, φ i y = x := by
  obtain ⟨i, y, hy⟩ := hc (p x)
  obtain ⟨z, hz, -⟩ := Scheme.exists_preimage_of_isPullback (h i) x y hy.symm
  exact ⟨i, z, hz⟩

theorem cover_prop (Q : MorphismProperty Scheme.{0}) [IsZariskiLocalAtTarget Q] (f : ∀ i, V i ⟶ S)
    [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x) {p : X ⟶ S} {W : I → Scheme.{0}}
    {φ : ∀ i, W i ⟶ X} {q : ∀ i, W i ⟶ V i} (h : ∀ i, IsPullback (φ i) (q i) p (f i)) (hq : ∀ i, Q (q i)) : Q p := by
  refine IsZariskiLocalAtTarget.of_openCover (Scheme.Cover.mkOfCovers I V f hc) fun i => ?_
  change Q (pullback.snd p (f i))
  rw [← (h i).isoPullback_inv_snd, MorphismProperty.cancel_left_of_respectsIso Q]
  exact hq i

theorem exists_point_lift (f : ∀ i, V i ⟶ S) [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x)
    {k : Type} [Field k] (x : Sp k ⟶ S) : ∃ (i : I) (x' : Sp k ⟶ V i), x' ≫ f i = x := by
  obtain ⟨i, y, hy⟩ := hc (x (default : PrimeSpectrum k))
  refine ⟨i, IsOpenImmersion.lift (f i) x ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨a, rfl⟩
  exact ⟨y, hy.trans (congrArg x (Subsingleton.elim (α := PrimeSpectrum k) _ _))⟩

end Cover

section Grp

variable {I : Type} {S : Scheme.{0}} {V : I → Scheme.{0}} {f : ∀ i, V i ⟶ S} [∀ i, IsOpenImmersion (f i)]
  {G₁ G₂ : Over S} {G₁' G₂' : ∀ i, Over (V i)}
  [GrpObj G₁] [GrpObj G₂] [∀ i, GrpObj (G₁' i)] [∀ i, GrpObj (G₂' i)]
  {φ₁ : ∀ i, (G₁' i).left ⟶ G₁.left} {φ₂ : ∀ i, (G₂' i).left ⟶ G₂.left}

theorem mul_comp (hc : ∀ x, ∃ i y, f i y = x) (h₁ : ∀ i, IsGrpPullback (G₁' i) G₁ (f i) (φ₁ i))
    (h₂ : ∀ i, IsGrpPullback (G₂' i) G₂ (f i) (φ₂ i)) (ψ : G₁ ⟶ G₂) (ψ' : ∀ i, G₁' i ⟶ G₂' i) [∀ i, IsMonHom (ψ' i)]
    (hψ : ∀ i, (ψ' i).left ≫ φ₂ i = φ₁ i ≫ ψ.left) (T : Over S) (x y : T ⟶ G₁) :
    (x * y) ≫ ψ = (x ≫ ψ) * (y ≫ ψ) := by
  refine Over.OverMorphism.ext (cover_ext (fun i => pullback.fst T.hom (f i))
    (cover_pull hc fun i => IsPullback.of_hasPullback T.hom (f i)) fun i => ?_)
  have H := IsPullback.of_hasPullback T.hom (f i)
  let q := pullback.fst T.hom (f i)
  let W : Over (V i) := Over.mk (pullback.snd T.hom (f i))
  let l : (T ⟶ G₁) → (W ⟶ G₁' i) := fun z => Over.homMk
    ((h₁ i).1.lift (q ≫ z.left) (pullback.snd T.hom (f i)) (by rw [Category.assoc, Over.w z]; exact H.w))
    ((h₁ i).1.lift_snd _ _ _)
  have hl : ∀ z, (l z).left ≫ φ₁ i = q ≫ z.left := fun z => (h₁ i).1.lift_fst _ _ _
  let q' : Over.mk (W.hom ≫ f i) ⟶ T := Over.homMk q H.w
  have hl' : ∀ z, (q' ≫ z ≫ ψ).left = (l z ≫ ψ' i).left ≫ φ₂ i := fun z => by
    show q ≫ z.left ≫ ψ.left = ((l z).left ≫ (ψ' i).left) ≫ φ₂ i
    rw [Category.assoc, hψ, ← Category.assoc (l z).left, hl, Category.assoc]
  have e₁ := (h₁ i).2 W (l x) (l y) (q' ≫ x) (q' ≫ y) (hl x).symm (hl y).symm
  have e₂ := (h₂ i).2 W (l x ≫ ψ' i) (l y ≫ ψ' i) (q' ≫ x ≫ ψ) (q' ≫ y ≫ ψ) (hl' x) (hl' y)
  rw [← MonObj.comp_mul] at e₁ e₂
  rw [← MonObj.mul_comp (l x) (l y) (ψ' i)] at e₂
  replace e₂ : _ = (l x * l y).left ≫ (ψ' i).left ≫ φ₂ i := e₂.trans (Category.assoc _ _ _)
  rw [hψ, ← Category.assoc, ← e₁] at e₂
  refine Eq.trans ?_ e₂.symm
  exact (Category.assoc _ _ _).symm

theorem isMonHom (hc : ∀ x, ∃ i y, f i y = x) (h₁ : ∀ i, IsGrpPullback (G₁' i) G₁ (f i) (φ₁ i))
    (h₂ : ∀ i, IsGrpPullback (G₂' i) G₂ (f i) (φ₂ i)) (ψ : G₁ ⟶ G₂) (ψ' : ∀ i, G₁' i ⟶ G₂' i) [∀ i, IsMonHom (ψ' i)]
    (hψ : ∀ i, (ψ' i).left ≫ φ₂ i = φ₁ i ≫ ψ.left) : IsMonHom ψ := by
  refine ⟨?_, ?_⟩
  · have h := mul_comp hc h₁ h₂ ψ ψ' hψ (𝟙_ _) 1 1
    rw [_root_.mul_one] at h
    have h' : (1 : 𝟙_ (Over S) ⟶ G₁) ≫ ψ = 1 := mul_eq_left.1 h.symm
    simpa [Hom.one_def] using h'
  · have h := mul_comp hc h₁ h₂ ψ ψ' hψ (G₁ ⊗ G₁) (fst _ _) (snd _ _)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at h
    rw [h]; congr 1


omit [GrpObj G₁] [∀ i, GrpObj (G₁' i)] in
theorem kerSet (hc : ∀ x, ∃ i y, f i y = x) (h₁ : ∀ i, IsPullback (φ₁ i) (G₁' i).hom G₁.hom (f i))
    (h₂ : ∀ i, IsPullback (φ₂ i) (G₂' i).hom G₂.hom (f i))
    (he : ∀ i, η[G₂' i].left ≫ φ₂ i = f i ≫ η[G₂].left) (ψ : G₁ ⟶ G₂) (ψ' : ∀ i, G₁' i ⟶ G₂' i)
    (hψ : ∀ i, (ψ' i).left ≫ φ₂ i = φ₁ i ≫ ψ.left) (K : Set G₁.left) (hK : ∀ i, KerSet (ψ' i) (φ₁ i ⁻¹' K)) :
    KerSet ψ K := by
  intro k _ _ x z
  obtain ⟨i, x', hj⟩ := exists_point_lift f hc x
  let z' : Over.mk x' ⟶ G₁' i := Over.homMk ((h₁ i).lift z.left x' (by rw [Over.w z]; exact hj.symm))
    ((h₁ i).lift_snd _ _ _)
  have hz : z'.left ≫ φ₁ i = z.left := (h₁ i).lift_fst _ _ _
  have a₁ : (z' ≫ ψ' i).left ≫ φ₂ i = (z ≫ ψ).left := by
    rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc, hz]
    rfl
  have a₂ : (1 : Over.mk x' ⟶ G₂' i).left ≫ φ₂ i = (1 : Over.mk x ⟶ G₂).left := by
    show (x' ≫ η[G₂' i].left) ≫ φ₂ i = x ≫ η[G₂].left
    rw [Category.assoc, he, ← Category.assoc, hj]
  have b₁ : z ≫ ψ = 1 ↔ z' ≫ ψ' i = 1 :=
    ⟨fun h => Over.OverMorphism.ext ((h₂ i).hom_ext (by rw [a₁, a₂, h]) ((Over.w _).trans (Over.w _).symm)),
      fun h => Over.OverMorphism.ext (by rw [← a₁, ← a₂, h])⟩
  have pt : ∀ a, φ₁ i (z'.left a) = z.left a := fun a => congrArg (fun q => q a) hz
  rw [b₁, hK i k x' z']
  constructor
  · rintro h _ ⟨a, rfl⟩
    rw [← pt]
    exact h ⟨a, rfl⟩
  · rintro h _ ⟨a, rfl⟩
    show φ₁ i (z'.left a) ∈ K
    rw [pt]
    exact h ⟨_, rfl⟩

end Grp

theorem lbIso_of_cover {I : Type} {S : Scheme.{0}} {V X' : I → Scheme.{0}} [IsReduced S] (A : Over S) [GrpObj A]
    [IsCommMonObj A] (M : LB A.left) (hA : IsAbelianScheme A) (hM : M.IsLB) (ha : Out.RelAmple A M)
    {f : ∀ i, V i ⟶ S} (hc : ∀ x, ∃ i y, f i y = x)
    {φ : ∀ i, X' i ⟶ A.left} {g : ∀ i, X' i ⟶ V i} (h : ∀ i, IsPullback (φ i) (g i) A.hom (f i)) {P Q : LB A.left}
    (hP : P.IsLB) (hQ : Q.IsLB) (hi : ∀ i, LBIso (P.pull (φ i)) (Q.pull (φ i))) (s : (P.pull (eSec A)).Gen)
    (hs : s.IsGen) (t : (Q.pull (eSec A)).Gen) (ht : t.IsGen) : LBIso P Q := by
  refine GlobalTheory.seesaw_reduced_of_dense GlobalTheory.globalFns_holds S A M hA hM ha S A.left (𝟙 S) (𝟙 _) A.hom (LB.div Q P)
    (IsPullback.id_horiz _) (LB.isLB_div hQ hP) ?_ (eSec A) (Over.w η[A]) ?_
  · refine dense_univ.mono fun p _ => ?_
    obtain ⟨i, p', rfl⟩ := hc p
    obtain ⟨w, hw⟩ := hi i
    obtain ⟨c, hc⟩ := gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q (φ i)) w hw
    let x' : Sp ((V i).residueField p') ⟶ V i := (V i).fromSpecResidueField p'
    refine ⟨(V i).residueField p', inferInstance, x' ≫ f i, pullback (g i) x', pullback.fst (g i) x' ≫ φ i,
      pullback.snd (g i) x',
      ⟨(default : PrimeSpectrum ((V i).residueField p')), congrArg (f i) (Scheme.fromSpecResidueField_apply p' _)⟩,
      (IsPullback.of_hasPullback (g i) x').paste_horiz (h i), ?_⟩
    exact gen_chartPull (chartPullSame (LB.div Q P) (K := PUnit) _ (fun _ => φ i) (fun _ => 1) (pullback.fst (g i) x')
      fun _ => rfl) c hc
  · obtain ⟨w, hw⟩ := GlobalTheory.SabMapDescent.lbIso_of_gen_of_gen s hs t ht
    exact gen_chartPull (GlobalTheory.SabMapDescent.chartPullDivPull P Q _) w hw

set_option backward.isDefEq.respectTransparency.types false in
theorem isFinite_local : IsZariskiLocalAtTarget @IsFinite.{0} := inferInstance

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem isIsog_of_cover {I : Type} {p : ℕ} {S : Scheme.{0}} [IsReduced S] {s : S ⟶ Sp (KA l)} {V : I → Scheme.{0}}
    {s' : ∀ i, V i ⟶ Sp (KA l)} {f : ∀ i, V i ⟶ S} [∀ i, IsOpenImmersion (f i)] (hc : ∀ x, ∃ i y, f i y = x)
    {o₁ o₂ : Ob D l s} {o₁' o₂' : ∀ i, Ob D l (s' i)} (n₁ : ∀ i, ObjMap (o₁' i) o₁ (f i))
    (n₂ : ∀ i, ObjMap (o₂' i) o₂ (f i)) (ψ : o₁.t.G ⟶ o₂.t.G) (ψ' : ∀ i, (o₁' i).t.G ⟶ (o₂' i).t.G)
    (hψ : ∀ i, (ψ' i).left ≫ (n₂ i).cm.F = (n₁ i).cm.F ≫ ψ.left) (hI : ∀ i, IsIsog (o₁' i) (o₂' i) p (ψ' i)) :
    IsIsog o₁ o₂ p ψ := by
  have hm := fun i => (hI i).1.1
  have io₁ : ∀ i, IsOpenImmersion (n₁ i).cm.F := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (n₁ i).cart.1.flip inferInstance
  have io₂ : ∀ i, IsOpenImmersion (n₂ i).cm.F := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (n₂ i).cart.1.flip inferInstance
  have c₁ := cover_pull hc fun i => (n₁ i).cart.1
  have c₂ := cover_pull hc fun i => (n₂ i).cart.1
  have pb : ∀ i, IsPullback (n₁ i).cm.F (ψ' i).left ψ.left (n₂ i).cm.F := fun i => by
    refine IsPullback.of_bot ?_ (hψ i).symm (n₂ i).cart.1
    rw [Over.w, Over.w]
    exact (n₁ i).cart.1
  have hmon : IsMonHom ψ := isMonHom hc (fun i => (n₁ i).cart) (fun i => (n₂ i).cart) ψ ψ' hψ
  have sec : ∀ {a : 𝟙_ (Over S) ⟶ o₁.t.G} {b : 𝟙_ (Over S) ⟶ o₂.t.G} {a' : ∀ i, 𝟙_ (Over (V i)) ⟶ (o₁' i).t.G}
      {b' : ∀ i, 𝟙_ (Over (V i)) ⟶ (o₂' i).t.G}, (∀ i, (a' i).left ≫ (n₁ i).cm.F = f i ≫ a.left) →
      (∀ i, (b' i).left ≫ (n₂ i).cm.F = f i ≫ b.left) →
      (∀ i, a' i ≫ ψ' i = b' i) → a ≫ ψ = b := fun {a b a' b'} ha hb h =>
    Over.OverMorphism.ext (cover_ext f hc fun i => by
      rw [← hb, ← h, Over.comp_left, Over.comp_left, Category.assoc, hψ, ← Category.assoc, ← Category.assoc, ha])
  have : IsZariskiLocalAtTarget @Etale.{0} := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Etale)
  have := isFinite_local
  refine ⟨⟨hmon, cover_prop @IsFinite _ c₂ pb fun i => (hI i).1.2.1, cover_prop @Etale _ c₂ pb fun i => (hI i).1.2.2.1,
    cover_prop @Surjective _ c₂ pb fun i => (hI i).1.2.2.2.1,
    fun a => Over.OverMorphism.ext (cover_ext _ c₁ fun i => ?_), ?_⟩, fun p' hp a =>
    ⟨sec (fun i => (n₁ i).eta _) (fun i => (n₂ i).eta _) fun i => ((hI i).2 p' hp a).1,
      sec (fun i => (n₁ i).etaA _) (fun i => (n₂ i).etaA _) fun i => ((hI i).2 p' hp a).2⟩⟩
  · have e := congrArg (fun q => q.left) ((hI i).1.2.2.2.2.1 a)
    simp only [Over.comp_left] at e ⊢
    rw [← Category.assoc, ← (n₁ i).act, Category.assoc, ← hψ, ← Category.assoc, e, Category.assoc, (n₂ i).act,
      ← Category.assoc, hψ, Category.assoc]
  · have hP : (lbPow o₁.t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb o₁.t.PP.isLB _ _
    have hQ := pull_isLB o₂.t.PP.isLB ψ.left
    obtain ⟨c, hc'⟩ := GlobalTheory.IsogDescent.exists_gen_pow o₁.t.PP.L _ ((p ^ 2 : ℕ) : ℤ) o₁.t.PP.rig o₁.t.PP.rigGen
    obtain ⟨d₁, hd₁⟩ := gen_chartPull (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ))
      (eSec o₁.t.G) (fun _ => eSec o₁.t.G) fun _ => (Category.comp_id _).symm) c hc'
    obtain ⟨d₂, hd₂⟩ := gen_chartPull (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) (fun _ => 1)
      (eSec o₁.t.G) (fun _ => eSec o₂.t.G) fun _ => (congrArg (fun q => q.left) hmon.one_hom).symm)
      o₂.t.PP.rig o₂.t.PP.rigGen
    refine lbIso_of_cover o₁.t.G o₁.t.PP.L (GlobalTheory.ObjDim.isAbelianScheme o₁) o₁.t.PP.isLB o₁.ample hc
      (fun i => (n₁ i).cart.1) hP hQ (fun i => ?_) d₁ hd₁ d₂ hd₂
    have hP' : (lbPow (o₁' i).t.PP.L (p ^ 2)).IsLB := LB.isLB_linComb (o₁' i).t.PP.isLB _ _
    obtain ⟨w₁, hw₁, -⟩ := (n₁ i).lin
    obtain ⟨w₂, hw₂, -⟩ := (n₂ i).lin
    have i₁ : LBIso (lbPow (o₁' i).t.PP.L (p ^ 2)) ((lbPow o₁.t.PP.L (p ^ 2)).pull (n₁ i).cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₁.t.PP.L (K := PUnit) (fun _ => 𝟙 _) _ (n₁ i).cm.F _
        fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
        (iso_linComb ((isGen_iff w₁).1 hw₁) (K := PUnit) (fun _ => 𝟙 _) (fun _ => ((p ^ 2 : ℕ) : ℤ)))
    have i₂ : LBIso ((o₂' i).t.PP.L.pull (ψ' i).left) ((o₂.t.PP.L.pull ψ.left).pull (n₁ i).cm.F) :=
      LBIso.chartPull (chartPullId _) (chartPullOut o₂.t.PP.L (K := PUnit) (fun _ => ψ.left) _ (n₁ i).cm.F _
        fun _ => hψ i)
        (iso_linComb ((isGen_iff w₂).1 hw₂) (K := PUnit) (fun _ => (ψ' i).left) (fun _ => 1))
    exact LBIso.trans (pull_isLB hP _) hP' (pull_isLB hQ _) i₁.symm
      (LBIso.trans hP' (pull_isLB (o₂' i).t.PP.isLB _) (pull_isLB hQ _) (hI i).1.2.2.2.2.2 i₂)

theorem exists_pull {S S' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} (f : S' ⟶ S) (hf : f ≫ s = s')
    (o : Ob D l s) : ∃ o' : Ob D l s', Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s s' f rfl rfl
    (by rw [hf]; exact ((congrArg (s' ≫ ·) (Spec.map_id _)).trans (Category.comp_id _)).symm) o

theorem exists_comp {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} (m : ObjMap o' o f)
    (m' : ObjMap o'' o' f') : ∃ m'' : ObjMap o'' o (f' ≫ f), m''.cm.F = m'.cm.F ≫ m.cm.F :=
  ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).1 m'

theorem exists_cancel {S S' S'' : Scheme.{0}} {s : S ⟶ Sp (KA l)} {s' : S' ⟶ Sp (KA l)} {s'' : S'' ⟶ Sp (KA l)}
    {o : Ob D l s} {o' : Ob D l s'} {o'' : Ob D l s''} {f : S' ⟶ S} {f' : S'' ⟶ S'} {g : S'' ⟶ S} (hg : f' ≫ f = g)
    (m : ObjMap o' o f) (m'' : ObjMap o'' o g) : ∃ m' : ObjMap o'' o' f', m''.cm.F = m'.cm.F ≫ m.cm.F := by
  subst hg
  exact ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ S S' S'' s s' s'' o o' o'').2 f f' m).2 m''

theorem exists_restrict {p : ℕ} {S V T X : Scheme.{0}} {s : S ⟶ Sp (KA l)} {sV : V ⟶ Sp (KA l)} {sT : T ⟶ Sp (KA l)}
    {sX : X ⟶ Sp (KA l)} {o : Ob D l s} {K : Set o.t.G.left} {f : V ⟶ S} {oV a : Ob D l sV} (m : ObjMap oV o f)
    {ψ : oV.t.G ⟶ a.t.G} (hI : IsIsog oV a p ψ) (hK : KerSet ψ (m.cm.F ⁻¹' K)) {u : Ob D l sX} {c : V ⟶ X}
    (n : ObjMap a u c) {g : T ⟶ S} {oT : Ob D l sT} (mT : ObjMap oT o g) (g' : T ⟶ V) (hg : g' ≫ f = g)
    (hs : g' ≫ sV = sT) :
    ∃ (r : oT.t.G.left ⟶ oV.t.G.left) (aT : Ob D l sT) (ψT : oT.t.G ⟶ aT.t.G) (nT : ObjMap aT u (g' ≫ c)),
      r ≫ m.cm.F = mT.cm.F ∧ IsIsog oT aT p ψT ∧ KerSet ψT (mT.cm.F ⁻¹' K) ∧
        ψT.left ≫ nT.cm.F = r ≫ ψ.left ≫ n.cm.F := by
  obtain ⟨r, hr⟩ := exists_cancel hg m mT
  obtain ⟨aT, ⟨b⟩⟩ := exists_pull g' hs a
  obtain ⟨⟨ψT, hψ, -⟩, h⟩ := GlobalTheory.HkFam.isog_pull E H D l p V T sV sT g' oV a oT aT r b ψ
  obtain ⟨nT, hn⟩ := exists_comp n b
  have hψ' : ψT.left ≫ b.cm.F = r.cm.F ≫ ψ.left := hψ
  refine ⟨r.cm.F, aT, ψT, nT, hr.symm, (h ψT hψ).1 hI, ?_, ?_⟩
  · have := (h ψT hψ).2 _ hI.1.1 hK
    rw [hr]
    convert this using 1
    ext x
    simp only [Set.mem_preimage, Scheme.Hom.comp_apply]
  · rw [hn, reassoc_of% hψ']

theorem overlap (Xo : Moduli D l) {𝔓 : Ideal (𝓞 E)} {p i : ℕ} {S V₁ V₂ : Scheme.{0}} [IsReduced S]
    {s : S ⟶ Sp (KA l)} {o : Ob D l s} {K : Set o.t.G.left} (hA : admitted l 𝔓 p) (hH : HeckeSet D o.t 𝔓 p i K)
    {f₁ : V₁ ⟶ S} {f₂ : V₂ ⟶ S} [IsOpenImmersion f₁] [IsOpenImmersion f₂]
    {o₁ a₁ : Ob D l (f₁ ≫ s)} {o₂ a₂ : Ob D l (f₂ ≫ s)} (m₁ : ObjMap o₁ o f₁) (m₂ : ObjMap o₂ o f₂)
    {ψ₁ : o₁.t.G ⟶ a₁.t.G} {ψ₂ : o₂.t.G ⟶ a₂.t.G} (hI₁ : IsIsog o₁ a₁ p ψ₁) (hI₂ : IsIsog o₂ a₂ p ψ₂)
    (hK₁ : KerSet ψ₁ (m₁.cm.F ⁻¹' K)) (hK₂ : KerSet ψ₂ (m₂.cm.F ⁻¹' K)) {c₁ : V₁ ⟶ Xo.X} {c₂ : V₂ ⟶ Xo.X}
    (hc₁ : c₁ ≫ Xo.s = f₁ ≫ s) (hc₂ : c₂ ≫ Xo.s = f₂ ≫ s) (n₁ : ObjMap a₁ Xo.univ c₁) (n₂ : ObjMap a₂ Xo.univ c₂) :
    pullback.fst f₁ f₂ ≫ c₁ = pullback.snd f₁ f₂ ≫ c₂ ∧
      pullback.fst m₁.cm.F m₂.cm.F ≫ ψ₁.left ≫ n₁.cm.F = pullback.snd m₁.cm.F m₂.cm.F ≫ ψ₂.left ≫ n₂.cm.F := by
  let g : pullback f₁ f₂ ⟶ S := pullback.fst f₁ f₂ ≫ f₁
  have : IsReduced (pullback f₁ f₂) := isReduced_of_isOpenImmersion g
  have e₂ : pullback.snd f₁ f₂ ≫ f₂ = g := pullback.condition.symm
  obtain ⟨oT, ⟨mT⟩⟩ := exists_pull g rfl o
  have hs₁ : pullback.fst f₁ f₂ ≫ f₁ ≫ s = g ≫ s := (Category.assoc _ _ _).symm
  have hs₂ : pullback.snd f₁ f₂ ≫ f₂ ≫ s = g ≫ s := by rw [← e₂, Category.assoc]
  obtain ⟨r₁, b₁, χ₁, k₁, hr₁, hJ₁, hL₁, hk₁⟩ := exists_restrict m₁ hI₁ hK₁ n₁ mT (pullback.fst f₁ f₂) rfl hs₁
  obtain ⟨r₂, b₂, χ₂, k₂, hr₂, hJ₂, hL₂, hk₂⟩ := exists_restrict m₂ hI₂ hK₂ n₂ mT (pullback.snd f₁ f₂) e₂ hs₂
  have hHT := ((GlobalTheory.heckeSets_pull E H D 𝔓 p i S _ o.t oT.t g mT.toSABMap o.proper).2 K).1 hH
  obtain ⟨h₁, h₂⟩ := GlobalTheory.T.heckeQuotient_classifyingMap_isogeny_unique E H D l Xo 𝔓 p i _ (g ≫ s) oT b₁ b₂ χ₁ χ₂ _ _ _ k₁ k₂ hA hHT
    (by rw [Category.assoc, hc₁, hs₁]) (by rw [Category.assoc, hc₂, hs₂]) hJ₁ hJ₂ hL₁ hL₂
  refine ⟨h₁, ?_⟩
  have h₃ : r₁ ≫ ψ₁.left ≫ n₁.cm.F = r₂ ≫ ψ₂.left ≫ n₂.cm.F := hk₁.symm.trans (Eq.trans h₂ hk₂)
  have io₁ : IsOpenImmersion m₁.cm.F :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) m₁.cart.1.flip inferInstance
  have io₂ : IsOpenImmersion m₂.cm.F :=
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) m₂.cart.1.flip inferInstance
  let t : pullback m₁.cm.F m₂.cm.F ⟶ pullback f₁ f₂ :=
    pullback.lift (pullback.fst _ _ ≫ o₁.t.G.hom) (pullback.snd _ _ ≫ o₂.t.G.hom) (by
      rw [Category.assoc, Category.assoc, ← m₁.cart.1.w, ← m₂.cart.1.w, pullback.condition_assoc])
  let w : pullback m₁.cm.F m₂.cm.F ⟶ oT.t.G.left := mT.cart.1.lift (pullback.fst _ _ ≫ m₁.cm.F) t (by
    rw [Category.assoc, m₁.cart.1.w]
    simp only [t, g, pullback.lift_fst_assoc, Category.assoc])
  have hw : w ≫ mT.cm.F = pullback.fst _ _ ≫ m₁.cm.F := mT.cart.1.lift_fst _ _ _
  have w₁ : w ≫ r₁ = pullback.fst _ _ := by
    rw [← cancel_mono m₁.cm.F, Category.assoc, hr₁, hw]
  have w₂ : w ≫ r₂ = pullback.snd _ _ := by
    rw [← cancel_mono m₂.cm.F, Category.assoc, hr₂, hw, pullback.condition]
  rw [← w₁, ← w₂]
  exact (Category.assoc _ _ _).trans ((congrArg (w ≫ ·) h₃).trans (Category.assoc _ _ _).symm)

end GlobalTheory.QuotGlue


open GlobalTheory.QuotGlue in
theorem GlobalTheory.hasQuot_of_openCover :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → (∀ q : S, ∃ (U : S.Opens) (o' : Ob D l (U.ι ≫ s)) (m : ObjMap o' o U.ι), q ∈ U ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K)) → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i S _ s o K hA hH h
  choose U o' m hU a ψ hI hK using h
  have hrep : ∀ q, ∃ c : (U q).toScheme ⟶ Xo.X, c ≫ Xo.s = (U q).ι ≫ s ∧ Nonempty (ObjMap (a q) Xo.univ c) :=
    fun q => (Xo.rep _ _ (isReduced_of_isOpenImmersion (U q).ι) (a q)).exists
  choose c hc hn using hrep
  have n := fun q => (hn q).some
  have cov : ∀ x : S, ∃ (q : S) (y : (U q).toScheme), (U q).ι y = x := fun x => ⟨x, ⟨x, hU x⟩, rfl⟩
  have io : ∀ q, IsOpenImmersion (m q).cm.F := fun q =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (m q).cart.1.flip inferInstance
  have covG := cover_pull cov fun q => (m q).cart.1
  have ov := fun q q' => overlap Xo hA hH (m q) (m q') (hI q) (hI q') (hK q) (hK q') (hc q) (hc q') (n q) (n q')
  obtain ⟨F, hF⟩ := cover_glue (fun q => (U q).ι) cov c fun q q' => (ov q q').1
  obtain ⟨Φ, hΦ⟩ := cover_glue (fun q => (m q).cm.F) covG (fun q => (ψ q).left ≫ (n q).cm.F) fun q q' => (ov q q').2
  have hFs : F ≫ Xo.s = s := cover_ext _ cov fun q => by rw [← Category.assoc, hF, hc]
  obtain ⟨o₂, ⟨n₂⟩⟩ := exists_pull F hFs Xo.univ
  have hw : Φ ≫ Xo.univ.t.G.hom = o.t.G.hom ≫ F := cover_ext _ covG fun q => by
    rw [← Category.assoc, hΦ, Category.assoc, (n q).cart.1.w, ← Category.assoc, Over.w, ← Category.assoc,
      (m q).cart.1.w, Category.assoc, hF]
  let χ : o.t.G ⟶ o₂.t.G := Over.homMk (n₂.cart.1.lift Φ o.t.G.hom hw) (n₂.cart.1.lift_snd _ _ _)
  have hχ : χ.left ≫ n₂.cm.F = Φ := n₂.cart.1.lift_fst _ _ _
  choose b hb using fun q => exists_cancel (hF q) n₂ (n q)
  have hψ : ∀ q, (ψ q).left ≫ (b q).cm.F = (m q).cm.F ≫ χ.left := fun q => by
    refine n₂.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hχ, hΦ, hb]
    · rw [Category.assoc, Category.assoc, Over.w, (b q).cart.1.w, (m q).cart.1.w, ← Category.assoc, Over.w]
  exact ⟨o₂, χ, isIsog_of_cover cov m b χ ψ hψ hI, kerSet cov (fun q => (m q).cart.1) (fun q => (b q).cart.1)
    (fun q => (b q).cm.e_comm.trans (by rw [(b q).base]; rfl)) χ ψ hψ K hK⟩

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientOfOpenCoverReducedBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_of_open_cover_reduced_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) (S : Scheme.{0}) [IsReduced S] (s : S ⟶ Sp (KA l)) (o : Ob D l s) (K : Set o.t.G.left), admitted l 𝔓 p → HeckeSet D o.t 𝔓 p i K → (∀ q : S, ∃ (U : S.Opens) (o' : Ob D l (U.ι ≫ s)) (m : ObjMap o' o U.ι), q ∈ U ∧ HasQuot o' p (m.toSABMap.φ ⁻¹' K)) → HasQuot o p K := by
  first | exact @GlobalTheory.hasQuot_of_openCover | exact GlobalTheory.hasQuot_of_openCover | (intros; apply GlobalTheory.hasQuot_of_openCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientExistsListedKernelsSmoothBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkSplit

theorem exists_affine_isDomain {Z : Scheme.{0}} [IsLocallyNoetherian Z] (hZ : Geo.Tor.IsNormalScheme Z) (p : Z) :
    ∃ W : Z.Opens, IsAffineOpen W ∧ p ∈ W ∧ IsDomain Γ(Z, W) := by
  have := GlobalTheory.IsNormalScheme.of_pred hZ
  have hC := GlobalTheory.IsNormalScheme.isOpen_of_mem_irreducibleComponents (irreducibleComponent_mem_irreducibleComponents p)
  obtain ⟨W, hW, hpW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := ⟨_, hC⟩) (x := p) mem_irreducibleComponent
  exact ⟨W, hW, hpW, (GlobalTheory.IsNormalScheme.isDomain_and_isIntegrallyClosed_of_isIrreducible
    ⟨⟨p, hpW⟩, (isIrreducible_irreducibleComponent (x := p)).2.open_subset W.isOpen fun q hq => hle hq⟩).1⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}

theorem exists_pull {S S' : Scheme.{0}} (s : S ⟶ Sp (KA l)) (f : S' ⟶ S) (o : Ob D l s) :
    ∃ o' : Ob D l (f ≫ s), Nonempty (ObjMap o' o f) :=
  GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) S S' s (f ≫ s) f rfl rfl
    (by rw [show spMap (RingHom.id (KA l)) = 𝟙 _ from Spec.map_id _, Category.comp_id]) o

theorem hasQuot_image (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ) {S S' : Scheme.{0}} [IsReduced S] [IsNoetherian S']
    (s : S ⟶ Sp (KA l)) (g : S' ⟶ S) [Etale g] (o : Ob D l s) (s' : S' ⟶ Sp (KA l)) (hs : s' = g ≫ s)
    (o' : Ob D l s') (m : ObjMap o' o g) (K : Set o.t.G.left) (hA : admitted l 𝔓 p) (hK : HeckeSet D o.t 𝔓 p i K)
    (hQ : HasQuot o' p (m.toSABMap.φ ⁻¹' K)) (q : S) (hq : q ∈ Set.range g) :
    ∃ (U : S.Opens) (o₁ : Ob D l (U.ι ≫ s)) (m₁ : ObjMap o₁ o U.ι), q ∈ U ∧ HasQuot o₁ p (m₁.toSABMap.φ ⁻¹' K) := by
  let U : S.Opens := ⟨Set.range g, g.isOpenMap.isOpen_range⟩
  obtain ⟨g', hg'⟩ : ∃ g' : S' ⟶ U.toScheme, g' ≫ U.ι = g :=
    ⟨IsOpenImmersion.lift U.ι g (by simp [U]), IsOpenImmersion.lift_fac _ _ _⟩
  have hU : ∀ x : S, x ∈ U → x ∈ Set.range g := fun _ h => h
  have hqU : q ∈ U := hq
  clear_value U
  subst hg'
  rw [Category.assoc] at hs
  subst hs
  obtain ⟨o₁, ⟨m₁⟩⟩ := exists_pull s U.ι o
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 U.ι g' m₁).2 m
  have he : Etale g' := Etale.of_comp g' U.ι
  have hsur : Surjective g' := ⟨fun y => by
    obtain ⟨x, hx⟩ := hU (U.ι y) y.2
    exact ⟨x, U.ι.isOpenEmbedding.injective (by simpa using hx)⟩⟩
  refine ⟨U, o₁, m₁, hqU, GlobalTheory.T.heckeQuotient_descends_etale_surjective_cover E H D l Xo 𝔓 p i _ _ _ g' o₁ o' m' _ hA
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK) he hsur inferInstance ?_⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp] at hQ
  exact hQ

end GlobalTheory.HkSplit

theorem GlobalTheory.hasQuot_of_lists_of_smooth : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → Smooth s → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  intro E _ _ _ H D l Xo 𝔓 p i n S s o σ K hD hA hs hL hK
  obtain ⟨hr, hN, hn⟩ := GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ S s hs
  refine GlobalTheory.T.heckeQuotient_of_open_cover_reduced_base E H D l Xo 𝔓 p i S s o K hA hK fun q => ?_
  obtain ⟨W, hW, hq, hd⟩ := GlobalTheory.HkSplit.exists_affine_isDomain (fun x => ⟨hN.1 x, hN.2 x⟩) q
  have hR : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  let j : Sp Γ(S, W) ⟶ S := hW.fromSpec
  have hj : IsOpenImmersion j := inferInstanceAs (IsOpenImmersion hW.fromSpec)
  obtain ⟨x, hx⟩ : q ∈ Set.range j := by
    rw [show Set.range j = W from hW.range_fromSpec]; exact hq
  obtain ⟨o₁, ⟨m₁⟩⟩ := GlobalTheory.HkSplit.exists_pull s j o
  obtain ⟨σ', -, hL'⟩ := GlobalTheory.HkSetPull.lists_pull m₁.toSABMap.cart K _ n σ hL
  obtain ⟨R', _, π, o', m, he, ⟨y, hy⟩, hQ⟩ := GlobalTheory.T.exists_etale_hasHeckeQuotient_noetherian_domain E H D l 𝔓 p i n Γ(S, W) (j ≫ s) o₁ σ' _ x hD hA hL'
    (GlobalTheory.HkSetPull.heckeSet_pull D 𝔓 p i m₁.toSABMap K hK)
  obtain ⟨m', hm'⟩ := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o o₁ o').2 j π m₁).1 m
  have : IsLocallyNoetherian (Sp R') := LocallyOfFiniteType.isLocallyNoetherian π
  have : IsNoetherian (Sp R') := {}
  refine GlobalTheory.HkSplit.hasQuot_image Xo 𝔓 p i s (π ≫ j) o _ (Category.assoc _ _ _).symm o' m' K hA hK ?_ q
    ⟨y, by rw [Scheme.Hom.comp_apply, hy, hx]⟩
  rw [hm', Scheme.Hom.comp_base, TopCat.coe_comp, Set.preimage_comp]
  exact hQ
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HeckeQuotientExistsListedKernelsSmoothBaseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeQuotient_exists_listed_kernels_smooth_base : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i n : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp (KA l)) (o : Ob D l s) (σ : Fin n → (𝟙_ (Over S) ⟶ o.t.G)) (K : Set o.t.G.left), 1 ≤ D.p + D.q → admitted l 𝔓 p → Smooth s → Lists (p ^ 2) σ K → HeckeSet D o.t 𝔓 p i K → HasQuot o p K := by
  first | exact @GlobalTheory.hasQuot_of_lists_of_smooth | exact GlobalTheory.hasQuot_of_lists_of_smooth | (intros; apply GlobalTheory.hasQuot_of_lists_of_smooth <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyHeckeCorrespondenceScheme
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam

namespace GlobalTheory.HkFam

theorem corr_kerSet_unique {S : Scheme.{0}} {G G' : Over S} [GrpObj G'] {ψ : G ⟶ G'} {K K' : Set G.left}
    (h : KerSet ψ K) (h' : KerSet ψ K') : K = K' := by
  ext g
  obtain ⟨k, _, _, z₀, hz⟩ := exists_geomPt_range_eq G.left g
  let z : Over.mk (z₀ ≫ G.hom) ⟶ G := Over.homMk z₀ rfl
  have h1 := h k _ z
  have h2 := h' k _ z
  have hzl : z.left = z₀ := rfl
  rw [hzl, hz, Set.singleton_subset_iff] at h1 h2
  exact h1.symm.trans h2

theorem corr_heckeSet_kill {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}
    {S : Scheme.{0}} (t : SAB H S) {P : Ideal (𝓞 E)} {p i : ℕ} {K : Set t.G.left} (hpP : (p : 𝓞 E) ∈ P)
    (hK : HeckeSet D t P p i K) (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S) (z : Over.mk x ⟶ t.G)
    (hz : Set.range z.left ⊆ K) : z ^ p ^ 2 = 1 := by
  have hnat : ∀ {T : Over S} (x : T ⟶ t.G) (n : ℕ), x ≫ t.act.act (n : 𝓞 E) = x ^ n := by
    intro T x n
    induction n with
    | zero =>
      have h := t.act.add 0 0
      rw [add_zero] at h
      have h0 : t.act.act 0 = 1 := by simpa using h
      rw [Nat.cast_zero, pow_zero, h0, MonObj.comp_one]
    | succ n ih => rw [Nat.cast_succ, t.act.add, MonObj.comp_mul, ih, t.act.one, Category.comp_id, pow_succ]
  obtain ⟨C, hC, hH⟩ := hK k x
  have hzC := hH.2.2.1 ((hC z).2 hz)
  have hbar : (p : 𝓞 E) ∈ P.map (H.bar : 𝓞 E →+* 𝓞 E) := by
    have := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hpP
    rwa [map_natCast] at this
  have h := hzC ((p ^ 2 : ℕ) : 𝓞 E) (by
    rw [Nat.cast_pow, pow_two]
    exact Ideal.mul_mem_mul (Ideal.mem_span_singleton_self _) hbar)
  rwa [hnat] at h

theorem corr_nonempty : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), 1 ≤ D.p + D.q → admitted l 𝔓 p → Nonempty (Corr Xo 𝔓 p i) := by
  intro E _ _ _ H D l Xo P p i hr hA
  obtain ⟨Z, hZ⟩ := GlobalTheory.T.exists_heckeKernelScheme_universal_reduced_bases E H D l Xo P p i hA
  have := Z.et₁
  have := Xo.smooth
  have hXs : Smooth Xo.s := SmoothOfRelativeDimension.smooth D.dim Xo.s
  have hs : Smooth (Z.π₁ ≫ Xo.s) := inferInstance
  have hred : IsReduced Z.Hk :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field _ _ _ hs).1
  obtain ⟨S', π, o', m, τ, hf, he, hsu, hL⟩ :=
    GlobalTheory.T.hecke_set_etale_level_structure_exists E H D l P p i Z.Hk _ Z.o₁ Z.K hA hZ Z.hecke
  have hH' := ((GlobalTheory.heckeSets_pull E H D P p i _ _ _ _ _ m.toSABMap Z.o₁.proper).2 Z.K).1 Z.hecke
  have hq' := GlobalTheory.T.heckeQuotient_exists_listed_kernels_smooth_base E H D l Xo P p i _ S' _ o' τ _ hr hA inferInstance hL hH'
  obtain ⟨o₂, ψ, hi, hk⟩ := GlobalTheory.T.heckeQuotient_descends_etale_surjective_cover E H D l Xo P p i Z.Hk S' _ π Z.o₁ o' m Z.K hA Z.hecke he hsu
    inferInstance hq'
  obtain ⟨π₂, ⟨hb, ⟨m₂⟩⟩, -⟩ := Xo.rep _ _ hred o₂
  refine ⟨{ toKerScheme := Z, π₂ := π₂, base₂ := hb, o₂ := o₂, m₂ := m₂, ψ := ψ, isog := hi, ker := hk, univ := ?_ }⟩
  intro S s hS o o' ψ' ⟨hi', K', hk', hH⟩
  have := o'.proper
  have het := (etSet_of_kerSet S _ _ ψ' K' inferInstance hi'.1.2.1 hi'.1.2.2.1 hk').1
  obtain ⟨h, ⟨hh, n₁, hn₁⟩, hu⟩ := Z.rep S s hS o K' het hH
  refine ⟨h, ⟨hh, ?_⟩, ?_⟩
  · obtain ⟨o₃, ⟨n₃⟩⟩ := GlobalTheory.obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ _ s h rfl rfl
      (by rw [hh]; simp [spMap]) o₂
    obtain ⟨⟨ψ₃, hψ₃, -⟩, hall⟩ := GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject E H D l p _ _ _ _ h Z.o₁ o₂ o o₃ n₁ n₃ ψ
    obtain ⟨hi₃, hk₃⟩ := hall ψ₃ hψ₃
    have hk₃' := hk₃ Z.K hi.1.1 hk
    rw [← hn₁] at hk₃'
    obtain ⟨m, hm⟩ := GlobalTheory.T.exists_iso_quotients_same_kernel_reduced_base E H D l p S s o o' o₃ ψ' ψ₃ K' hA.2.2.1 hA.2.2.2.2 hi' (hi₃ hi) hk' hk₃'
      (corr_heckeSet_kill o.t hA.2.2.2.1 hH)
    have hc := ((GlobalTheory.ObjMaps.id_comp_cancel E H D l _ _ _ _ _ _ _ _ _ _ _ _ o₂ o₃ o').2 h (𝟙 S) n₃).1 m
    have hc' : ∀ g : S ⟶ Z.Hk, g = h → (∃ m'' : ObjMap o' o₂ g, m''.toSABMap.φ = m.toSABMap.φ ≫ n₃.toSABMap.φ) →
        ∃ m'' : ObjMap o' o₂ h, m''.toSABMap.φ = m.toSABMap.φ ≫ n₃.toSABMap.φ := by
      rintro g rfl hg
      exact hg
    obtain ⟨n₂, hn₂⟩ := hc' _ (Category.id_comp h) hc
    exact ⟨n₁, n₂, by rw [hn₂, ← Category.assoc, hm, hψ₃]⟩
  · rintro h' ⟨hh', n₁', n₂', e⟩
    have hk₃ := ((GlobalTheory.T.exists_isogeny_pullback_heckeModuliObject E H D l p _ _ _ _ h' Z.o₁ o₂ o o' n₁' n₂' ψ).2 ψ' e).2 Z.K hi.1.1 hk
    exact hu h' ⟨hh', n₁', corr_kerSet_unique hk' hk₃⟩

end GlobalTheory.HkFam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyHeckeCorrespondenceSchemeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.HkFam
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nonempty_heckeCorrespondenceScheme : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (𝔓 : Ideal (𝓞 E)) (p i : ℕ), 1 ≤ D.p + D.q → admitted l 𝔓 p → Nonempty (Corr Xo 𝔓 p i) := by
  first | exact @GlobalTheory.HkFam.corr_nonempty | exact GlobalTheory.HkFam.corr_nonempty | (intros; apply GlobalTheory.HkFam.corr_nonempty <;> assumption)
end
