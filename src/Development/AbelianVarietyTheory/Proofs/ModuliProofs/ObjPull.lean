module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelStructureDescendsFieldExtension
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SiegPairPBNonempty
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaEmbeddingSectionsBaseChangeAffine
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HolomorphicUniformizationTangentUnimodularRiemann
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsE8IsSharpBasis

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory

theorem obj_pull :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B B' : Type) [CommRing B] [CommRing B'] (b : Base l B) (b' : Base l B') (j : B →+* B') (S S' : Scheme.{0}) (s : S ⟶ Sp B) (s' : S' ⟶ Sp B') (f : S' ⟶ S), j b.ρ = b'.ρ → j b.ζ = b'.ζ → f ≫ s = s' ≫ spMap j → ∀ o : Obj D l b s, ∃ o' : Obj D l b' s', Nonempty (ObjMap o' o f) :=
  ObjPull.objPull_of_lie_of_ample LiePull.lieMult_pull
    (PolPull.pol_pull_of_relAmple_local AmpleLocal.relAmple_of_locally)

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipal
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.SiegelPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
  {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem push_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w]))

theorem push_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩


omit [GrpObj A] [GrpObj A'] in
theorem lift_sq (sq : IsSquare φ φ₂) {T : Over S} {T' : Over S'} (χ : T.left ⟶ T'.left) (x' y' : T' ⟶ A')
    {Z : Over S} (ψ : T.left ⟶ Z.left) (x y : Z ⟶ A) (hx : χ ≫ x'.left ≫ φ = ψ ≫ x.left)
    (hy : χ ≫ y'.left ≫ φ = ψ ≫ y.left) : χ ≫ (lift x' y').left ≫ φ₂ = ψ ≫ (lift x y).left := by
  refine pullback.hom_ext (f := A.hom) (g := A.hom) ?_ ?_
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (fst A A).left = (ψ ≫ (lift x y).left) ≫ (fst A A).left
    rw [Category.assoc, Category.assoc, sq.1, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_fst, hx,
      Category.assoc, ← Over.comp_left, lift_fst]
  · show (χ ≫ (lift x' y').left ≫ φ₂) ≫ (snd A A).left = (ψ ≫ (lift x y).left) ≫ (snd A A).left
    rw [Category.assoc, Category.assoc, sq.2, ← Category.assoc (lift x' y').left, ← Over.comp_left, lift_snd, hy,
      Category.assoc, ← Over.comp_left, lift_snd]


omit [GrpObj A] [GrpObj A'] in
theorem diag_iso (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left} {P' : LB (A' ⊗ A').left}
    (H : LBIso P' (P.pull φ₂)) :
    LBIso (P'.pull (lift (𝟙 A') (𝟙 A')).left) ((P.pull (lift (𝟙 A) (𝟙 A)).left).pull φ) := by
  obtain ⟨u, hu⟩ := H
  have e : (lift (𝟙 A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (𝟙 A)).left :=
    (Category.id_comp _).symm.trans (lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (𝟙 A')
      (Z := A) φ (𝟙 A) (𝟙 A) (by simp) (by simp))
  exact LBIso.chartPull (chartPullId _) (chartPullOut P _ _ φ _ fun _ => e)
    (iso_linComb ((isGen_iff u).1 hu) (fun _ : PUnit => (lift (𝟙 A') (𝟙 A')).left) (fun _ => 1))

theorem nondeg_pull (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) {P : LB (A ⊗ A).left}
    {P' : LB (A' ⊗ A').left} (hP : P.IsLB) (hP' : P'.IsLB) (H : LBIso P' (P.pull φ₂))
    (hn : ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1)
    (T : Over S') (x : T ⟶ A') (hx : ∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) :
    x = 1 := by
  obtain ⟨u, hu⟩ := H
  obtain ⟨t, ht⟩ := hx
  refine push_injective h T ((hn _ (pushHom h T x) ?_).trans (map_one _).symm)
  let T₀ : Over S := Over.mk (T.hom ≫ f)
  have w₁ : (fst A T₀).left ≫ A.hom = ((snd A T₀).left ≫ T.hom) ≫ f :=
    pullback.condition.trans (Category.assoc _ _ _).symm
  let a : (A ⊗ T₀).left ⟶ A'.left := h.1.lift _ _ w₁
  have a₁ : a ≫ φ = (fst A T₀).left := h.1.lift_fst _ _ _
  have a₂ : a ≫ A'.hom = (snd A T₀).left ≫ T.hom := h.1.lift_snd _ _ _
  let χ : (A ⊗ T₀).left ⟶ (A' ⊗ T).left := pullback.lift a (snd A T₀).left a₂
  have c₁ : χ ≫ (fst A' T).left = a := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd A' T).left = (snd A T₀).left := pullback.lift_snd _ _ _
  obtain ⟨t₂, ht₂, -⟩ := exists_up ((isGen_iff u).1 hu) hP hP' t ht
  refine gen_chartPull (chartPullSame P _ _ _ χ fun _ => ?_) t₂ ht₂
  refine ((Category.id_comp _).symm.trans (lift_sq sq (T := A ⊗ T₀) χ _ _ (𝟙 _) _ _ ?_ ?_).symm)
  · rw [Over.comp_left, Category.assoc, ← Category.assoc χ, c₂, Category.id_comp]
    rfl
  · rw [← Category.assoc, c₁, a₁, Category.id_comp]

def secPull (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) : 𝟙_ (Over S') ⟶ A' :=
  Over.homMk (h.1.lift (f ≫ x.left) (𝟙 S') (by
    rw [Category.assoc, Over.w x]; exact (Category.comp_id _).trans (Category.id_comp _).symm)) (h.1.lift_snd _ _ _)

theorem secPull_left (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) : (secPull h x).left ≫ φ = f ≫ x.left :=
  h.1.lift_fst _ _ _

theorem push_secPull (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) (T : Over S') :
    pushHom h T (toUnit T ≫ secPull h x) = toUnit (Over.mk (T.hom ≫ f)) ≫ x := by
  apply Over.OverMorphism.ext
  show ((toUnit T).left ≫ (secPull h x).left) ≫ φ = (toUnit (Over.mk (T.hom ≫ f))).left ≫ x.left
  rw [Category.assoc, secPull_left, Over.toUnit_left, Over.toUnit_left, ← Category.assoc]
  rfl

theorem push_secPull' (h : IsGrpPullback A' A f φ) (x : 𝟙_ (Over S) ⟶ A) :
    pushHom h _ (secPull h x) = toUnit _ ≫ x := by
  have e := push_secPull h x (𝟙_ (Over S'))
  rwa [toUnit_unit, Category.id_comp] at e

end GlobalTheory.SiegelPull

namespace GlobalTheory

open SiegelPull

theorem siegPre_pullback : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (c : SiegPre h M ζ s), f ≫ s = s' → (∃ c' : SiegPre h M ζ s', SiegPB c' c f) ∧ ∀ c' : SiegPre h M ζ s', SiegPB c' c f → c.Principal → c'.Principal := by
  intro h M o _ ζ S S' s s' f c hs
  refine ⟨?_, ?_⟩
  · obtain ⟨p⟩ := siegPairPB_nonempty c f
    refine ⟨{
      A := p.A
      ab := p.ab
      P := p.P
      isLB := p.isLB
      rig₁ := p.rig₁
      rig₂ := p.rig₂
      symm := p.symm
      lev := fun a => secPull p.pb (c.lev a)
      lev_add := fun a b => push_injective p.pb _ (by
        rw [map_mul, push_secPull', push_secPull', push_secPull', c.lev_add, MonObj.comp_mul])
      lev_tors := fun a => push_injective p.pb _ (by
        rw [map_pow, map_one, push_secPull', ← MonObj.comp_pow, c.lev_tors, MonObj.comp_one])
      geom := fun k _ _ x β z hx hz => ?_ }, p.φ, p.φ₂, p.pb, p.sq, p.iso, fun a => secPull_left p.pb _⟩
    obtain ⟨g₁, g₂, g₃⟩ := c.geom k (x ≫ f) β z (by rw [Category.assoc, hs, hx]) hz
    refine ⟨fun a => Iff.trans ?_ (g₁ a), fun g hg => ?_, fun a b => ?_⟩
    · rw [← (push_injective p.pb (Over.mk x)).eq_iff, push_secPull, map_one]
      rfl
    · obtain ⟨a, ha⟩ := g₂ (pushHom p.pb (Over.mk x) g) (by
        have := congrArg (pushHom p.pb (Over.mk x)) hg
        rw [map_pow, map_one] at this
        exact this)
      exact ⟨a, push_injective p.pb _ ((push_secPull p.pb _ _).trans ha)⟩
    · exact (weilIs_grpPullback_of_comm S S' c.A p.A f p.φ _ _ (pull_isLB c.isLB _) (pull_isLB p.isLB _) p.pb
        (diag_iso p.sq p.iso) (Over.mk x) M _ _ _ _ _
        (congrArg (fun q => q.left) (push_secPull p.pb (c.lev a) (Over.mk x)).symm)
        (congrArg (fun q => q.left) (push_secPull p.pb (c.lev b) (Over.mk x)).symm)).2 (g₃ a b)
  · rintro c' ⟨φ, φ₂, pb, sq, iso, -⟩ ⟨h₁, h₂⟩
    exact ⟨(pol_pull S S' c.A c'.A f φ _ _ (pull_isLB c.isLB _) (pull_isLB c'.isLB _) c.ab pb
      (diag_iso sq iso)).2.1 h₁, nondeg_pull pb sq c.isLB c'.isLB iso h₂⟩

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SiegelObjectPullbackExistsAndPrincipalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.siegelObject_pullback_exists_and_principal : ∀ (h M : ℕ) (o : Type) [CommRing o] (ζ : o) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (c : SiegPre h M ζ s), f ≫ s = s' → (∃ c' : SiegPre h M ζ s', SiegPB c' c f) ∧ ∀ c' : SiegPre h M ζ s', SiegPB c' c f → c.Principal → c'.Principal := by
  first | exact @GlobalTheory.siegPre_pullback | exact GlobalTheory.siegPre_pullback | (intros; apply GlobalTheory.siegPre_pullback <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaObjPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left}

theorem pushHom_injective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Injective (pushHom h T) :=
  fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w, Over.w]))

theorem pushHom_surjective (h : IsGrpPullback A' A f φ) (T : Over S') : Function.Surjective (pushHom h T) :=
  fun y => ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
    Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem map_linComb {T : Over S} {T' : Over S'} (ρ : (T' ⟶ A') →* (T ⟶ A)) {n : ℕ} (y : Fin n → (T' ⟶ A'))
    (a : Fin n → ℕ) : ρ (Out.linComb y a) = Out.linComb (fun i => ρ (y i)) a := by
  unfold Out.linComb
  rw [map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact map_pow ρ _ _

def toBase (f : S' ⟶ S) : Over.mk ((Out.baseOver S').hom ≫ f) ⟶ Out.baseOver S := Over.homMk f (by simp)

theorem exists_sec (h : IsGrpPullback A' A f φ) (x : Out.baseOver S ⟶ A) :
    ∃ x' : Out.baseOver S' ⟶ A', pushHom h _ x' = toBase f ≫ x :=
  pushHom_surjective h _ _

end GlobalTheory.ThetaObjPull

namespace GlobalTheory

open ThetaObjPull PolBaseChange

theorem tObj_pull : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0})
    (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' →
    ∃ t' : TObj g k J b s', TMap t' t f := by
  intro o _ g k J b S S' s s' f t hs
  subst hs
  have h := isGrpPullback_pullback t.A f
  have hL' := pull_isLB t.isLB (pullback.fst t.A.hom f)
  have hiso := lbIso_refl hL'
  obtain ⟨hab, hamp, hk⟩ := pol_pull _ _ _ _ _ _ _ _ t.isLB hL' t.ab h hiso
  choose pt hpt using fun i => exists_sec h (t.pt i)
  have hpt' : ∀ i, (pt i).left ≫ pullback.fst t.A.hom f = f ≫ (t.pt i).left := fun i =>
    congrArg (fun z => z.left) (hpt i)
  have := t.hom
  have := t.ab.comm
  refine ⟨{ A := (Over.pullback f).obj t.A
            ab := hab
            dim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 t.dim
            L := t.L.pull (pullback.fst t.A.hom f)
            isLB := hL'
            rigid := rigidified_pull h t.rigid
            sym := sym_pull h t.sym
            ample := hamp t.ample
            ktriv := hk t.ktriv
            pt := pt
            torsion := fun i => pushHom_injective h _ ?_
            bij := fun K _ _ x y hy => ?_
            pairing := fun i j => ?_
            act := fun j => (Over.pullback f).map (t.act j)
            hom := fun j => inferInstance }, pullback.fst t.A.hom f, h, hiso, hpt', fun j => pullback.lift_fst _ _ _⟩
  · rw [map_pow, map_one, hpt]
    exact (map_pow (preHom (toBase f)) _ _).symm.trans (by rw [t.torsion, map_one])
  · have key : ∀ c : Ix g k, pushHom h (Over.mk x) (Out.linComb (fun i =>
        (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S') ≫ pt i) (fun i => (c i).val)) =
        Out.linComb (fun i => (Over.homMk (x ≫ f) (by simp) : Over.mk (x ≫ f) ⟶ Out.baseOver S) ≫ t.pt i)
          (fun i => (c i).val) := fun c => by
      rw [map_linComb]
      congr 1
      funext i
      apply Over.OverMorphism.ext
      show (x ≫ (pt i).left) ≫ _ = (x ≫ f) ≫ (t.pt i).left
      rw [Category.assoc, hpt', Category.assoc]
    have hy' : pushHom h (Over.mk x) y ^ k = 1 := by rw [← map_pow, hy, map_one]
    obtain ⟨c, hc, hu⟩ := t.bij K (x ≫ f) (pushHom h (Over.mk x) y) hy'
    exact ⟨c, pushHom_injective h _ ((key c).trans hc), fun c' hc' => hu c' ((key c').symm.trans (congrArg _ hc'))⟩
  · refine (weilIs_grpPullback_of_comm _ _ _ _ f _ _ _ t.isLB hL' h hiso (Out.baseOver S') k (pt i) (pt j)
      (toBase f ≫ t.pt i) (toBase f ≫ t.pt j) _ (hpt' i).symm (hpt' j).symm).2 ?_
    have w := CommPairing.weilIs_pull globalFns_holds t.ab t.isLB (toBase f) (t.pairing i j)
    rw [map_zpow] at w
    have e : Units.map (toBase f).left.appTop.hom.toMonoidHom (unitS s b.ζ) = unitS (f ≫ s) b.ζ := by
      apply Units.ext
      show f.appTop.hom (s.appTop.hom _) = (f ≫ s).appTop.hom _
      rw [Scheme.Hom.comp_appTop]
      rfl
    exact e ▸ w

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.exists_thetaLevelAbelianScheme_pullback : ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (S S' : Scheme.{0}) (s : S ⟶ Sp o) (s' : S' ⟶ Sp o) (f : S' ⟶ S) (t : TObj g k J b s), f ≫ s = s' → ∃ t' : TObj g k J b s', TMap t' t f := by
  first | exact @GlobalTheory.tObj_pull | exact GlobalTheory.tObj_pull | (intros; apply GlobalTheory.tObj_pull <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChange
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ThetaBaseChange

open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ThetaCoord GlobalTheory.CommPairing GlobalTheory.GlobalLift GlobalTheory.VVRank

variable {S : Scheme.{0}} (P : PolAV S) {T T' : Over S}

theorem isThetaPtOver_pull_of_gen {n : ℕ} {I : Type} {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)}
    (H : IsThetaPtOver P n x v) (h : T' ⟶ T)
    (hg : ∀ th, IsGenSec P.A P.L 1 th → IsGenSec P.A P.L 1 (pullS P.A 1 h th)) :
    IsThetaPtOver P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  have hL := P.isLB
  obtain ⟨th, s₁, α, τ, U, s₂, w, u, hth, hα, hτ, hs₁, hU, hs₂, hw, hv⟩ := H
  obtain ⟨α', hα', k₁⟩ := exists_twist_pull P.A (ψ := mulT P.A T n) (hm := lift_snd _ _) (b := 1)
    hL hα h (ψ' := mulT P.A T' n) (lift_snd _ _) (mulT_comm P.A h n)
  obtain ⟨τ', hτ', k₂⟩ := exists_gen_pullTo (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) τ hτ h.left
    (fun _ => by rw [← Over.comp_left, MonObj.comp_one])
  choose U' hU' k₃ using fun a => exists_symLift_act_pull hL h (hU a)
  refine ⟨_, _, α', τ', U', fun a => pullS P.A _ h (s₂ a), fun a => h.left.appTop.hom (w a),
    Units.map h.left.appTop.hom.toMonoidHom u, hg _ hth, hα', hτ', k₁ _ _ hs₁, hU',
    fun a => k₃ a _ _ (hs₂ a), fun a => isValueAt_of_sv hL hτ' fun z J hJ => ?_, fun a => ?_⟩
  · have q := sv_of_isValueAt (hw a) h hJ
    rw [MonObj.comp_one] at q
    rw [sv_pullS _ _ _ _ _ z hJ, ← Over.comp_left, lift_whiskerRight, Category.id_comp, q, k₂ _ _ z J hJ,
      Category.id_comp]
    exact congrArg (· * _) ((gs_pull (𝟙 _) h.left z ⊤ trivial _).trans (by rw [Category.id_comp])).symm
  · exact (congrArg h.left.appTop.hom (hv a)).trans (map_mul _ _ _)

theorem exists_basicOpen_isGenSec (hS : SecBaseChangeAnySt) [IsAffine T.left] (V : T.left.Opens) (p : T.left)
    (hp : p ∈ V) : ∃ f : Γ(T.left, ⊤), p ∈ T.left.basicOpen f ∧
      ∃ j : overRes (T.left.basicOpen f) ⟶ overRes V, j ≫ overResι V = overResι _ ∧
        ∀ th, IsGenSec P.A P.L 1 th → IsGenSec P.A P.L 1 (pullS P.A 1 j th) := by
  obtain ⟨V₀, hV, b, hb⟩ := hS S P 1 le_rfl (T.hom p)
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  obtain ⟨f, hf, hpf⟩ := (isAffineOpen_top T.left).exists_basicOpen_le (V := V ⊓ T.hom ⁻¹ᵁ V₀) ⟨p, hp, hV⟩ trivial
  let W := T.left.basicOpen f
  let l : overRes W ⟶ overRes (T := baseOver S) V₀ := Over.homMk
    (IsOpenImmersion.lift V₀.ι (W.ι ≫ T.hom) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact (hf y.2).2)) ((congrArg (_ ≫ ·) (Category.comp_id _)).trans (IsOpenImmersion.lift_fac _ _ _))
  have hle : W ≤ V := hf.trans inf_le_left
  let j : overRes W ⟶ overRes V := Over.homMk (T.left.homOfLE hle) (by
    change T.left.homOfLE hle ≫ V.ι ≫ T.hom = W.ι ≫ T.hom
    rw [← Category.assoc, Scheme.homOfLE_ι])
  have hj : j ≫ overResι V = overResι W := Over.OverMorphism.ext (T.left.homOfLE_ι hle)
  refine ⟨f, hpf, j, hj, fun th H s => ?_⟩
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have : IsAffine (overRes W).left := hW
  obtain ⟨c, hc⟩ := exists_basis P 1 b hb (overRes W) l
  obtain ⟨n, u, hu⟩ := EmbPull.exists_pow_extend_secM P 1 f (pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)))
  obtain ⟨r, hr⟩ := H (pullS P.A 1 (overResι V) (SecM.toSec P.A u))
  have hr' : pullM P.A P.L 1 (overResι V) u = r • SecM.ofSec P.A th := Subtype.ext (funext hr)
  have e₁ := congrArg (pullM P.A P.L 1 j) hr'
  rw [pullM_comp _ P.isLB, hj, hu, LinearMap.map_smulₛₗ] at e₁
  obtain ⟨d, hd⟩ : ∃ d : Γ((overRes W).left, ⊤), SecM.ofSec P.A s =
      d • pullM P.A P.L 1 l (SecM.ofSec P.A (b hq.default)) := by
    have := c.sum_repr (SecM.ofSec P.A s)
    rw [Fintype.sum_unique, hc] at this
    exact ⟨_, this.symm⟩
  have hf₁ : IsUnit (W.ι.appTop.hom f) := by
    refine W.toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun y _ => ?_
    refine (Scheme.mem_basicOpen_top _ _ y).1 ?_
    rw [← Scheme.preimage_basicOpen_top]
    exact y.2
  obtain ⟨a, ha⟩ : IsUnit ((overResι W).left.appTop.hom (f ^ n)) := by
    rw [map_pow]
    exact hf₁.pow n
  have key : SecM.ofSec P.A s = (d * (a⁻¹ : Γ((overRes W).left, ⊤)ˣ) * j.left.appTop.hom r) •
      pullM P.A P.L 1 j (SecM.ofSec P.A th) := by
    rw [mul_smul, ← e₁, ← ha, ← mul_smul, Units.inv_mul_cancel_right, hd]
  exact ⟨_, fun i => congrArg (fun q => q.1 i) key⟩

theorem isThetaPt_pull (hS : SecBaseChangeAnySt) [IsAffine T.left] [IsAffine T'.left] (h : T' ⟶ T) {n : ℕ} {I : Type}
    {x : I → (T ⟶ P.A)} {v : I → Γ(T.left, ⊤)} (H : IsThetaPt P n x v) :
    IsThetaPt P n (fun a => h ≫ x a) (fun a => h.left.appTop.hom (v a)) := by
  obtain ⟨h₁, h₂, H⟩ := H
  refine ⟨h₁, by simpa using h₂.map h.left.appTop.hom, fun p => ?_⟩
  obtain ⟨V, hV, H⟩ := H (h.left p)
  obtain ⟨f, hf, j, hj, hg⟩ := exists_basicOpen_isGenSec P hS V _ hV
  let f' := h.left.appTop.hom f
  have hf' : h.left ⁻¹ᵁ T.left.basicOpen f = T'.left.basicOpen f' := Scheme.preimage_basicOpen_top _ _
  let W := T.left.basicOpen f
  let W' := T'.left.basicOpen f'
  let k₀ : W'.toScheme ⟶ W.toScheme := IsOpenImmersion.lift W.ι (W'.ι ≫ h.left) (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨y, rfl⟩
      exact hf'.ge y.2)
  have hk₀ : k₀ ≫ W.ι = W'.ι ≫ h.left := IsOpenImmersion.lift_fac _ _ _
  let k : overRes W' ⟶ overRes W := Over.homMk k₀ (by
    change k₀ ≫ W.ι ≫ T.hom = W'.ι ≫ T'.hom
    rw [← Category.assoc, hk₀, Category.assoc, Over.w])
  have hk : k ≫ overResι W = overResι W' ≫ h := Over.OverMorphism.ext hk₀
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have hW' : IsAffineOpen W' := (isAffineOpen_top _).basicOpen f'
  have : IsAffine (overRes W).left := hW
  have : IsAffine (overRes W').left := hW'
  have Q := isThetaPtOver_pull_of_gen P (isThetaPtOver_pull_of_gen P H j hg) k
    fun _ => EmbPull.isGenSec_pullS P hS k
  have e : k ≫ j ≫ overResι V = overResι W' ≫ h := by rw [hj]; exact hk
  refine ⟨W', hf'.le hf, ?_⟩
  convert Q using 2 with a a
  · rw [← Category.assoc, ← e]
    simp only [Category.assoc]
  · exact (congrArg (fun q => q.left.appTop.hom (v a)) e).symm

end GlobalTheory.ThetaBaseChange

theorem GlobalTheory.hasTh_baseChange : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh (spMap φ ≫ x) (fun a => φ (v a)) := by
  intro hl o _ g N' J b S s t R R' _ _ φ x v H
  have : IsAffine (Over.mk x).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine (Over.mk (spMap φ ≫ x)).left := inferInstanceAs (IsAffine (Spec _))
  have Q := GlobalTheory.ThetaBaseChange.isThetaPt_pull t.pol hl.secBaseChangeAny
    (Over.homMk (spMap φ) rfl : Over.mk (spMap φ ≫ x) ⟶ Over.mk x) H
  unfold TObj.HasTh
  convert Q using 2 with a a
  · exact Over.OverMorphism.ext (Category.assoc (spMap φ) x (t.lab a).left)
  · exact congrArg (fun q => q.hom (v a)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsRingBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hasThetaConstants_ring_baseChange : Out.Laws2 → ∀ (o : Type) [CommRing o] (g N' : ℕ) (J : Type) (b : TBase o (N' ^ 2)) (S : Scheme.{0}) (s : S ⟶ Sp o) (t : TObj g (N' ^ 2) J b s) (R R' : Type) [CommRing R] [CommRing R'] (φ : R →+* R') (x : Sp R ⟶ S) (v : Ix g (N' ^ 2) → R), t.HasTh x v → t.HasTh (spMap φ ≫ x) (fun a => φ (v a)) := by
  first | exact @GlobalTheory.hasTh_baseChange | exact GlobalTheory.hasTh_baseChange | (intros; apply GlobalTheory.hasTh_baseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannForm
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannForm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.AnyAppellHumbert

theorem hermForm_swap {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (h : Hm.IsHermitian) (z w : Fin g → ℂ) :
    hermForm Hm w z = star (hermForm Hm z w) := by
  unfold hermForm
  rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, h.eq, Matrix.dotProduct_mulVec]

theorem semicharacter_add {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (hL : L.IsLB) (u : HolUnif A L g)
    {Hm : Matrix (Fin g) (Fin g) ℂ} {χ : u.Λ → ℂ} (h : u.IsAH Hm χ) (l m : u.Λ) (n : ℤ)
    (hn : (n : ℝ) = (hermForm Hm l m).im) : χ (l + m) = χ l * χ m * (-1) ^ n := by
  obtain ⟨i, hi⟩ := PullHermitian.exists_chart (u.ex 0).left hL
  have hi' : ⊤ ≤ (u.ex (0 + l)).left ⁻¹ᵁ L.U i := by rwa [SectionTheta.ex_add_lattice]
  have hi'' : ⊤ ≤ (u.ex (0 + l + m)).left ⁻¹ᵁ L.U i := by rwa [SectionTheta.ex_add_lattice]
  have h1 := h.2.2.2 l i 0 hi
  have h2 := h.2.2.2 m i _ hi'
  have h3 := h.2.2.2 (l + m) i 0 hi
  have hs := hermForm_swap h.1 (l : Fin g → ℂ) m
  have hne := u.fr_ne i _ hi''
  rw [h2, h3] at h1
  simp only [zero_add, Submodule.coe_add, star_add, Matrix.mulVec_add, dotProduct_add, add_dotProduct,
    zero_dotProduct, mul_zero] at h1 hne
  unfold hermForm at hs hn
  rw [hs] at h1
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (l : Fin g → ℂ)) = a at h1
  generalize (m : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = b at h1
  generalize (l : Fin g → ℂ) ⬝ᵥ Hm.mulVec (star (m : Fin g → ℂ)) = c at h1 hn
  have hc : c = star c + 2 * n * Complex.I := by
    have := Complex.sub_conj c
    rw [← hn] at this
    push_cast at this
    rw [Complex.star_def]
    linear_combination this
  have he : Complex.exp (Real.pi / 2 * a) * Complex.exp (Real.pi * c + Real.pi / 2 * b) =
      (-1) ^ n * Complex.exp (Real.pi / 2 * (a + star c + (c + b))) := by
    rw [← Complex.exp_pi_mul_I, ← Complex.exp_int_mul, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    linear_combination (Real.pi / 2 : ℂ) * hc
  refine mul_right_cancel₀ (mul_ne_zero (Complex.exp_ne_zero (Real.pi / 2 * (a + star c + (c + b)))) hne) ?_
  linear_combination h1 + χ l * χ m * u.fr i (l + m) * he

theorem isAH_properties :
    Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ (∀ l, χ l = 1 ∨ χ l = -1) ∧ (∀ l m, χ (l + m) = χ l * χ m * (-1) ^ Ef l m) ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧ (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧ ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c) := by
  intro hlaw _ _ hU P u Hm χ hA
  obtain ⟨ht1, ht2, hE⟩ := AnyUnif.tangent_and_unimodular hU P u
  obtain ⟨Ef, hEf, hb⟩ := hE Hm χ hA
  have hval := @valAt'_rules
  have hvalaff := @existsUnique_point_of_ringHom
  have hvalext := @eq_of_valAt'_eq hval hvalaff
  have hsmred := @isReduced_of_smooth_complex
  have hholprod := @holFamily_lift hval
  have hthg := @ThetaGroupFrame.thetaGrp_in_frame hval hholprod
  have hweil := @WeilExp.weilIs_exp_riemannForm hlaw.weil hval hvalext hsmred hthg
  have hsecfn := @sections_pow_theta_functions hval hvalext hsmred
  have hfshift := @fourierCoeff_unitCube_translate_of_entire_periodic
  have hfvan := @entire_periodic_eq_zero_of_fourierCoeff_eq_zero hfshift
  have hdimcl := @ClassicalTheta.card_le_pow_of_linearIndependent hfshift hfvan
  have hnormform := @SiegelNormalForm.exists_normal_form
  have hdim := @card_le_pow_of_linearIndependent_theta_principal hnormform hdimcl
  have hindep := @PowSec.exists_indep_sections hlaw.globalSectionsRank
  have hseconto := @ThetaOnto.theta_from_section hval hdim hindep hsecfn
  have h7 := hsecfn P u Hm χ Ef ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩
  refine ⟨Ef, hEf, hb, fun l => sq_eq_one_iff.1 (semicharacter_sq_eq_one_of_symmetric P u Hm χ hA l), fun l m => semicharacter_add P.isLB u hA l m _ (hEf l m),
    ht1, ht2, fun n => ⟨(h7 n).1, fun θ hθ => ?_⟩, hweil P u Hm χ Ef ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩⟩
  obtain ⟨s, hs⟩ := hseconto P u Hm χ Ef hA ⟨hA.1, hA.2.2.1, hEf, hA.2.2.2⟩ hb n θ hθ
  exact ⟨s, hs, fun s' hs' => (h7 n).2 θ s' s hs' hs⟩

end GlobalTheory.AnyAppellHumbert
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AppellHumbertUniformisationRiemannFormStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.appellHumbert_uniformisation_riemannForm : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ), u.IsAH Hm χ → ∃ Ef : LinearMap.BilinForm ℤ u.Λ, (∀ a b : u.Λ, (Ef a b : ℝ) = (hermForm Hm a b).im) ∧ Function.Bijective Ef ∧ (∀ l, χ l = 1 ∨ χ l = -1) ∧ (∀ l m, χ (l + m) = χ l * χ m * (-1) ^ Ef l m) ∧ (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) ∧ (∀ n : ℕ, (∀ s, ∃! θ, u.IsThetaFn Hm χ n θ ∧ u.IsFnPow n s θ) ∧ ∀ θ, u.IsThetaFn Hm χ n θ → ∃! s, u.IsFnPow n s θ) ∧ ∀ (k : ℕ) (a b : u.Λ) (c : ℂˣ), 0 < k → (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (Ef a b : ℂ) / k) → Out.WeilIs P.A P.L k (u.ex ((k : ℂ)⁻¹ • (a : Fin P.g → ℂ))) (u.ex ((k : ℂ)⁻¹ • (b : Fin P.g → ℂ))) (unitOn c) := by
  first | exact @GlobalTheory.AnyAppellHumbert.isAH_properties | exact GlobalTheory.AnyAppellHumbert.isAH_properties | (intros; apply GlobalTheory.AnyAppellHumbert.isAH_properties <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbers
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ConstTheta

open GlobalTheory.CechPic

variable {K : Type} [Field K]

theorem isNilpotent_of_fst_eq_zero {x : DualNumber K} (hx : x.fst = 0) : IsNilpotent x := by
  rw [TrivSqZeroExt.isNilpotent_iff_isNilpotent_fst, hx]; exact IsNilpotent.zero

theorem fst_eq_zero_of_mem {x : DualNumber K} (hx : x ∈ IsLocalRing.maximalIdeal (DualNumber K)) : x.fst = 0 := by
  have : ¬ IsUnit x.fst := fun hu => hx (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 hu)
  simpa using this

theorem subsingleton_sp : Subsingleton (Sp (DualNumber K)) := by
  have h : ∀ p : PrimeSpectrum (DualNumber K),
      p.asIdeal = IsLocalRing.maximalIdeal (DualNumber K) := by
    intro p
    refine le_antisymm (IsLocalRing.le_maximalIdeal p.isPrime.ne_top) fun x hx => ?_
    obtain ⟨n, hn⟩ := isNilpotent_of_fst_eq_zero (fst_eq_zero_of_mem hx)
    exact p.isPrime.mem_of_pow_mem n (hn ▸ p.asIdeal.zero_mem)
  exact ⟨fun p q => PrimeSpectrum.ext ((h p).trans (h q).symm)⟩

theorem fst_comp_const : spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ spMap (algebraMap K (DualNumber K)) = 𝟙 _ := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
  congr 1

theorem rigidity (hG : Out.GlobalFnsSt) {A₀ : Over (Sp K)} {A' G' : Over (Sp (DualNumber K))} [GrpObj A'] [GrpObj G']
    {j : A₀.left ⟶ A'.left} {a b : A' ⟶ G'} (hA : IsAbelianScheme A')
    (hj : IsPullback j A₀.hom A'.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (hab : j ≫ a.left = j ≫ b.left) (hη : η[A'] ≫ a = η[A'] ≫ b) : a = b := by
  haveI := subsingleton_sp (K := K)
  let c : A' ⟶ G' := a * b⁻¹
  let j' : Over.mk (j ≫ A'.hom) ⟶ A' := Over.homMk j rfl
  have h1 : j' ≫ a = j' ≫ b := Over.OverMorphism.ext hab
  have h2 : j' ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, h1, mul_inv_cancel]
  have h3 : η[A'] ≫ c = 1 := by
    simp only [c, MonObj.comp_mul, GrpObj.comp_inv, hη, mul_inv_cancel]
  obtain ⟨t₀⟩ : Nonempty (Sp K) := inferInstance
  let t : Sp (DualNumber K) := spMap (TrivSqZeroExt.fstHom K K K).toRingHom t₀
  have hc : ∀ x : A'.left, c.left x = (η[G'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ G').left t := by
    intro x
    obtain ⟨z, rfl, -⟩ := Scheme.exists_preimage_of_isPullback hj x t₀ (Subsingleton.elim _ _)
    have e : j ≫ c.left = (j' ≫ c).left := rfl
    rw [← Scheme.Hom.comp_apply, e, h2, Hom.one_def, Over.comp_left]
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    congr 1
    exact Subsingleton.elim (α := Sp (DualNumber K)) _ _
  have hη' : (η[A'] : 𝟙_ (Over (Sp (DualNumber K))) ⟶ A').left ≫ A'.hom = 𝟙 _ := Over.w η[A']
  have key := DualRigidity.eq_comp_section_of_const A'.hom _ c.left hη' (hG _ A' hA).2 _ hc
  have key' : c = toUnit A' ≫ η[A'] ≫ c := Over.OverMorphism.ext key
  rw [h3, MonObj.comp_one] at key'
  exact mul_inv_eq_one.1 key'

variable {A : Over (Sp (DualNumber K))} {A₀ : Over (Sp K)} [GrpObj A] [GrpObj A₀] {io : A₀.left ⟶ A.left}
  {ψ : A.left ⟶ A₀.left}

theorem endo_const (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    (hi : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) io)
    (hψ : IsGrpPullback A A₀ (spMap (algebraMap K (DualNumber K))) ψ) (e : io ≫ ψ = 𝟙 _)
    (f : A ⟶ A) (f₀ : A₀ ⟶ A₀) [IsMonHom f] [IsMonHom f₀] (h : f₀.left ≫ io = io ≫ f.left) :
    f.left ≫ ψ = ψ ≫ f₀.left := by
  have w : (ψ ≫ f₀.left) ≫ A₀.hom = A.hom ≫ spMap (algebraMap K (DualNumber K)) := by
    rw [Category.assoc, Over.w, hψ.1.w]
  let b : A ⟶ A := Over.homMk (hψ.1.lift (ψ ≫ f₀.left) A.hom w) (hψ.1.lift_snd _ _ _)
  have hb : b.left ≫ ψ = ψ ≫ f₀.left := hψ.1.lift_fst _ _ _
  suffices H : f = b by rw [H, hb]
  refine rigidity hG hA hi.1 (hψ.1.hom_ext ?_ ?_) (Over.OverMorphism.ext (hψ.1.hom_ext ?_ ?_))
  · rw [← h, Category.assoc, Category.assoc, hb, e, reassoc_of% e, Category.comp_id]
  · rw [Category.assoc, Category.assoc, Over.w, Over.w]
  · have h₁ : eSec A ≫ ψ = _ ≫ eSec A₀ := PolBaseChange.eSec_comm hψ
    have h₂ : eSec A₀ ≫ f₀.left = eSec A₀ := congrArg (fun z => z.left) (IsMonHom.one_hom f₀)
    rw [IsMonHom.one_hom f]
    change eSec A ≫ ψ = (eSec A ≫ b.left) ≫ ψ
    rw [Category.assoc, hb, reassoc_of% h₁, h₂, h₁]
  · rw [Over.w, Over.w]

theorem torsion_const [IsCommMonObj A₀]
    (hψ : IsGrpPullback A A₀ (spMap (algebraMap K (DualNumber K))) ψ) (e : io ≫ ψ = 𝟙 _) {n : ℕ}
    (hn : IsUnit (n : Γ(Sp K, ⊤))) (y : Out.baseOver _ ⟶ A) (y₀ : Out.baseOver _ ⟶ A₀) (hy : y ^ n = 1)
    (hy₀ : y₀ ^ n = 1) (h : y₀.left ≫ io = spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ y.left) :
    y.left ≫ ψ = spMap (algebraMap K (DualNumber K)) ≫ y₀.left := by
  have := formallyUnramified_mulA _ A₀ n hn
  have hs : Function.Surjective (CommRingCat.ofHom (TrivSqZeroExt.fstHom K K K).toRingHom) :=
    TrivSqZeroExt.fst_surjective
  have := IsClosedImmersion.spec_of_surjective _ hs
  have hnil : IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) := by
    refine ⟨2, ?_⟩
    rw [pow_two, Ideal.zero_eq_bot, eq_bot_iff, Ideal.mul_le]
    intro r hr s hs
    have hr' : r.fst = 0 := hr
    have hs' : s.fst = 0 := hs
    rw [Ideal.mem_bot]
    ext <;> simp [hr', hs']
  let r : Over.mk ((Out.baseOver _).hom ≫ spMap (algebraMap K (DualNumber K))) ⟶ Out.baseOver (Sp K) :=
    Over.homMk (spMap (algebraMap K (DualNumber K))) (by simp)
  have m : ∀ {T : Over (Sp K)} (p : T ⟶ A₀), p ^ n = 1 → p ≫ Out.mulA A₀ n = 1 := fun p hp => by
    rw [Out.mulA, MonObj.comp_pow, Category.comp_id, hp]
  have e₁ := m (pushHom hψ _ y) (by rw [← map_pow, hy, map_one])
  have e₂ := m (r ≫ y₀) (by rw [← MonObj.comp_pow, hy₀, MonObj.comp_one])
  refine FormallyUnramified.hom_ext (spMap (TrivSqZeroExt.fstHom K K K).toRingHom)
    (isNilpotent_ker_specMap _ hnil) (Out.mulA A₀ n).left ?_ (congrArg (fun z => z.left) (e₁.trans e₂.symm))
  refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ ψ) h.symm).trans ?_)
  refine Eq.trans ?_ (Category.assoc _ _ _)
  rw [fst_comp_const]
  exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e).trans ((Category.comp_id _).trans (Category.id_comp _).symm))

theorem lam_push {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (c : Pic G.left) (x' : G' ⟶ G') (x : G ⟶ G)
    (hx : x'.left ≫ φ = φ ≫ x.left) : lam (pull φ c) (𝟙 G') x' = pull φ (lam c (𝟙 G) x) := by
  let r : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ h.1.w
  have e₁ : r ≫ 𝟙 G = pushHom h G' (𝟙 G') := Over.OverMorphism.ext
    ((Category.comp_id _).trans (Category.id_comp _).symm)
  have e₂ : r ≫ x = pushHom h G' x' := Over.OverMorphism.ext hx.symm
  refine Eq.trans ?_ (pull_lam r c (𝟙 G) x).symm
  rw [e₁, e₂]
  unfold lam
  rw [← map_mul, ← map_one (pushHom h G'), ← pull_comp, ← pull_comp, ← pull_comp, ← pull_comp]
  rfl

theorem lam_eq_zero (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    (hi : IsPullback io A₀.hom A.hom (spMap (TrivSqZeroExt.fstHom K K K).toRingHom))
    (q : Pic A.left) (hq : pull io q = 0) {T : Over (Sp (DualNumber K))} (x y : T ⟶ A) : lam q x y = 0 := by
  letI := hA.comm
  obtain ⟨Q, hQ, rfl⟩ := cls_surj q
  have hN : (cubeLB A ![fst A A, snd A A] Q).IsLB := LB.isLB_linComb hQ _ _
  have eN := cls_cube_two hQ _ _ hN
  have ax : ∀ {T : Over (Sp (DualNumber K))} (u v : T ⟶ A), lam (cls Q hQ) u v = 0 →
      ∃ t : LB.Gen ((cubeLB A ![fst A A, snd A A] Q).pull (lift u v).left), t.IsGen := fun u v h => by
    rw [← cls_eq_zero_iff (pull_isLB hN _), cls_pull hN, eN, pull_lam, lift_fst, lift_snd, h]
  let mk := Ideal.Quotient.mk (Ideal.span {(DualNumber.eps : DualNumber K)})
  let π : Over.mk (pullback.snd (A ⊗ A).hom (spMap mk) ≫ spMap mk) ⟶ A ⊗ A :=
    Over.homMk (pullback.fst _ _) pullback.condition
  have fac : spMap mk = spMap (mk.comp (algebraMap K (DualNumber K))) ≫
      spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    refine RingHom.ext fun a => Ideal.Quotient.eq.2 (Ideal.mem_span_singleton'.2 ⟨algebraMap K _ a.snd, ?_⟩)
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  have van : ∀ z : Over.mk (pullback.snd (A ⊗ A).hom (spMap mk) ≫ spMap mk) ⟶ A, pull z.left (cls Q hQ) = 0 := by
    intro z
    have w : z.left ≫ A.hom = (pullback.snd (A ⊗ A).hom (spMap mk) ≫
        spMap (mk.comp (algebraMap K (DualNumber K)))) ≫ spMap (TrivSqZeroExt.fstHom K K K).toRingHom := by
      rw [Over.w, Category.assoc, ← fac]; rfl
    rw [← hi.lift_fst z.left _ w, pull_comp, hq, map_zero]
  have hε : (DualNumber.eps : DualNumber K) ∈ IsLocalRing.maximalIdeal (DualNumber K) := fun hu => by
    simpa using TrivSqZeroExt.isUnit_iff_isUnit_fst.1 hu
  have H := SmallExtLift.exists_gen_of_small_extension hG KuennethOne.kuenneth_injective (DualNumber K)
    DualNumber.eps (fun a ha => by
      have := fst_eq_zero_of_mem ha
      ext <;> simp [this]) A hA _ hN (ax _ _ (lam_one_right _ _)) (ax _ _ (lam_one_left _ _)) _
    (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _) hε (by
      have := ax (π ≫ fst A A) (π ≫ snd A A) (by simp only [lam, van]; simp)
      rw [← comp_lift, lift_fst_snd, Category.comp_id] at this
      exact this)
  have H' := congrArg (pull (lift x y).left) (eN.symm.trans ((cls_eq_zero_iff hN).2 H))
  rwa [pull_lam, lift_fst, lift_snd, map_zero] at H'

theorem lb_const [IsCommMonObj A] (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    (hi : IsGrpPullback A₀ A (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) io)
    (hψ : IsGrpPullback A A₀ (spMap (algebraMap K (DualNumber K))) ψ) (e : io ≫ ψ = 𝟙 _)
    (w : A ⟶ A) (w₀ : A₀ ⟶ A₀) (h₁ : w₀.left ≫ io = io ≫ w.left) (h₂ : w.left ≫ ψ = ψ ≫ w₀.left)
    {L : LB A.left} {L₀ : LB A₀.left} (hL : L.IsLB) (hL₀ : L₀.IsLB) (h₀ : LBIso L₀ (L.pull io))
    (hp : LBIso L (cubeLB A ![𝟙 A, w] L)) : LBIso L (L₀.pull ψ) := by
  have e₀ : cls L₀ hL₀ = pull io (cls L hL) := (cls_eq_iff _ (pull_isLB hL io)).2 h₀
  have p : cls L hL = lam (cls L hL) (𝟙 A) w :=
    ((cls_eq_iff hL (LB.isLB_linComb hL _ _)).2 hp).trans (cls_cube_two hL _ _ _)
  have p₀ : cls L₀ hL₀ = lam (cls L₀ hL₀) (𝟙 A₀) w₀ := by
    rw [e₀, lam_push hi _ w₀ w h₁, ← p]
  have z := lam_eq_zero hG hA hi.1 (cls L hL - pull ψ (cls L₀ hL₀))
    (by rw [map_sub, ← pull_comp, e, pull_id, e₀, sub_self]) (𝟙 A) w
  have z' : lam (cls L hL) (𝟙 A) w - lam (pull ψ (cls L₀ hL₀)) (𝟙 A) w = 0 := by
    refine Eq.trans ?_ z
    simp only [lam, map_sub]
    abel
  rw [lam_push hψ _ w w₀ h₂, ← p, ← p₀, sub_eq_zero] at z'
  exact (cls_eq_iff hL (pull_isLB hL₀ ψ)).1 z'

theorem tMap_of_const : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (w w' : J) (K : Type) [Field K] (s : Sp (DualNumber K) ⟶ Sp o) (s₀ : Sp K ⟶ Sp o) (t : TObj g k J b s) (t₀ : TObj g k J b s₀) (io : t₀.A.left ⟶ t.A.left) (ψ₀ : t.A.left ⟶ t₀.A.left), t.Prim w w' → IsGrpPullback t₀.A t.A (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) io → LBIso t₀.L (t.L.pull io) → (∀ i, (t₀.pt i).left ≫ io = spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (t.pt i).left) → (∀ j, (t₀.act j).left ≫ io = io ≫ (t.act j).left) → IsGrpPullback t.A t₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ → io ≫ ψ₀ = 𝟙 _ → TMap t t₀ (spMap (algebraMap K (DualNumber K))) := by
  intro hL _ _ o _ g k J b w w' K _ s s₀ t t₀ io ψ₀ hp hi h₀ hpt hact hψ e
  have hw : ∀ j, (t.act j).left ≫ ψ₀ = ψ₀ ≫ (t₀.act j).left := fun j =>
    haveI := t.hom j
    haveI := t₀.hom j
    endo_const hL.globalFns t.ab hi hψ e _ _ (hact j)
  letI := t.ab.comm
  letI := t₀.ab.comm
  have hk : IsUnit (k : Γ(Sp K, ⊤)) := by
    simpa using b.unit.map (s₀.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
  exact ⟨ψ₀, hψ, lb_const hL.globalFns t.ab hi hψ e _ _ (hact w) (hw w) t.isLB t₀.isLB h₀ hp.2.2,
    fun i => torsion_const hψ e hk _ _ (t.torsion i) (t₀.torsion i) (hpt i), hw⟩

end GlobalTheory.ConstTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelAbelianSchemeConstOverDualNumbersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
theorem _root_.GlobalTheory.T.thetaLevelAbelianScheme_const_over_dualNumbers : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) (w w' : J) (K : Type) [Field K] (s : Sp (DualNumber K) ⟶ Sp o) (s₀ : Sp K ⟶ Sp o) (t : TObj g k J b s) (t₀ : TObj g k J b s₀) (io : t₀.A.left ⟶ t.A.left) (ψ₀ : t.A.left ⟶ t₀.A.left), t.Prim w w' → IsGrpPullback t₀.A t.A (spMap (TrivSqZeroExt.fstHom K K K).toRingHom) io → LBIso t₀.L (t.L.pull io) → (∀ i, (t₀.pt i).left ≫ io = spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ (t.pt i).left) → (∀ j, (t₀.act j).left ≫ io = io ≫ (t.act j).left) → IsGrpPullback t.A t₀.A (spMap (algebraMap K (DualNumber K))) ψ₀ → io ≫ ψ₀ = 𝟙 _ → TMap t t₀ (spMap (algebraMap K (DualNumber K))) := by
  first | exact @GlobalTheory.ConstTheta.tMap_of_const | exact GlobalTheory.ConstTheta.tMap_of_const | (intros; apply GlobalTheory.ConstTheta.tMap_of_const <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionOfDiagonalCMAction
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionOfDiagonalCMAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

theorem GlobalTheory.detCond_of_diagonal_action : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → (∀ (a : 𝓞 E) z, u.ex (fun i => ty i (a : E) * z i) = u.ex z ≫ act.act a) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : ℂ →+* K), DetCond D act (spMap β) (β H.rt0) := by
  intro _ _ _ unif E _ _ _ H D P u _ _ act ty _ hty hact K _ _ β
  obtain ⟨h₁, h₂, -⟩ := GlobalTheory.AnyUnif.tangent_and_unimodular unif P u
  have hs : Smooth P.A.hom := P.isAb.smooth
  obtain ⟨v, hv, heig⟩ := GlobalTheory.exists_lieBasis_of_holUnif P.A P.L P.g u hs h₁ h₂
  have key : ∀ τ₀ : E →+* ℂ, LieMult act (𝟙 (Sp ℂ)) (τ₀.comp (algebraMap (𝓞 E) E))
      (Nat.card {i // ty i = τ₀}) := fun τ₀ => by
    have h := GlobalTheory.lieMult_of_eigenbasis ℂ (𝓞 E) P.A act P.g v (fun i => (ty i).comp (algebraMap (𝓞 E) E)) hs hv
      (fun i a => heig _ _ (act.hom a) (hact a) i) (τ₀.comp (algebraMap (𝓞 E) E))
    convert h using 1
    exact Nat.card_congr (Equiv.subtypeEquivRight fun i =>
      ⟨fun e => by rw [e], fun e => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) e⟩)
  have hd : DetCond D act (𝟙 (Sp ℂ)) H.rt0 := fun τ => by
    obtain ⟨τ₀, rfl⟩ := GlobalTheory.PeriodPoint.exists_embedding (RingHom.id ℂ) τ
    refine ⟨fun h => ?_, fun h => ?_⟩
    · rw [← (hty τ₀).1 h]; exact key τ₀
    · rw [← (hty τ₀).2 h]; exact key τ₀
  have := (GlobalTheory.detCond_iff_of_field_extension E H D _ P.A ℂ K β (𝟙 _) act H.rt0 hs).2 hd
  rwa [Category.comp_id] at this
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionOfDiagonalCMActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
theorem _root_.GlobalTheory.T.determinantCondition_of_diagonalCMAction : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ThetaUnifAV → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (Hm : Matrix (Fin P.g) (Fin P.g) ℂ) (χ : u.Λ → ℂ) (act : OAct (𝓞 E) P.A) (ty : Fin P.g → (E →+* ℂ)), u.IsAH Hm χ → IsTypeFn H D.p D.q ty → (∀ (a : 𝓞 E) z, u.ex (fun i => ty i (a : E) * z i) = u.ex z ≫ act.act a) → ∀ (K : Type) [Field K] [IsAlgClosed K] (β : ℂ →+* K), DetCond D act (spMap β) (β H.rt0) := by
  first | exact @GlobalTheory.detCond_of_diagonal_action | exact GlobalTheory.detCond_of_diagonal_action | (intros; apply GlobalTheory.detCond_of_diagonal_action <;> assumption)
end
end
