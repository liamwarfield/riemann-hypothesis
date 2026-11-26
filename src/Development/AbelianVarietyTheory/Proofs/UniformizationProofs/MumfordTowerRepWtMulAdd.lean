module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpBijOfOnto
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.EndoEqOfSections
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
public import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ConstantThetaDeformationZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

section Germ
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}

theorem gm_eq_of_isWt {V : G.left.Opens} {u : Γ(G.left, V)ˣ} {χ : X} (hu : IsWt i V u.val χ) {Z : Over S}
    (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (h₁ : ((t ≫ i) * g).left z ∈ V) (h₂ : g.left z ∈ V) :
    gm ((t ≫ i) * g).left z V u = gm t.left z ⊤ (charUnit S X χ) * gm g.left z V u := by
  let W : Z.left.Opens := ((t ≫ i) * g).left ⁻¹ᵁ V ⊓ g.left ⁻¹ᵁ V
  have hz : z ∈ W := ⟨h₁, h₂⟩
  let ρ : Over.mk (W.ι ≫ Z.hom) ⟶ Z := Over.homMk W.ι rfl
  have hW : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := fun x _ => x.2
  have inj : Function.Injective (W.ι.appLE W ⊤ hW).hom := by
    rw [Scheme.Opens.ι_appLE]
    exact (ConcreteCategory.bijective_of_isIso
      (Z.left.presheaf.mapIso (eqToIso (by simp : W.ι ''ᵁ ⊤ = W)).op).hom).1
  have e₁ : ((ρ ≫ t) ≫ i) * (ρ ≫ g) = ρ ≫ ((t ≫ i) * g) := by rw [MonObj.comp_mul, Category.assoc]
  have a : ∀ {Y : Scheme.{0}} (r : Z.left ⟶ Y) (U : Y.Opens) (k : W ≤ r ⁻¹ᵁ U) (x : Γ(Y, U)ˣ) k',
      ((W.ι ≫ r).appLE U ⊤ k').hom x.val = (W.ι.appLE W ⊤ hW).hom (res k (pullU r U x)).val := fun r U k x k' =>
    (congrArg (fun q => q.hom x.val) (Scheme.Hom.appLE_comp_appLE W.ι r U W ⊤ k hW)).symm
  have b : ∀ {Y : Scheme.{0}} (r : Z.left ⟶ Y) (U : Y.Opens) (k : W ≤ r ⁻¹ᵁ U) (x : Γ(Y, U)ˣ),
      gm (𝟙 Z.left) z W (res k (pullU r U x)) = gm r z U x := fun r U k x =>
    (gm_res (𝟙 Z.left) z k hz _).trans ((gm_pull (𝟙 Z.left) r z U (k hz) x).trans (by simp only [Category.id_comp]))
  have h := hu _ (ρ ≫ t) (ρ ≫ g) (by rw [e₁]; exact fun x _ => x.2.1) (fun x _ => x.2.2)
  have c : ∀ (r r' : Over.mk (W.ι ≫ Z.hom) ⟶ G) (_ : r = r') k k',
      (r.left.appLE V ⊤ k).hom u.val = (r'.left.appLE V ⊤ k').hom u.val := by
    rintro r _ rfl k k'; rfl
  have d : (ρ ≫ t).left.appTop = (W.ι ≫ t.left).appLE ⊤ ⊤ le_top := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  rw [c _ _ e₁ _ (fun x _ => x.2.1), d] at h
  have h' := ((a _ V inf_le_left u _).symm.trans h).trans
    ((congrArg₂ (· * ·) (a t.left ⊤ le_top (charUnit S X χ) _) (a g.left V inf_le_right u _)).trans
      (map_mul _ _ _).symm)
  rw [← b _ V inf_le_left, ← b t.left ⊤ le_top, ← b g.left V inf_le_right, ← map_mul]
  exact congrArg _ (Units.ext (inj h'))

end Germ

section Flat
variable {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {F : Y' ⟶ Y}

theorem mem_pull_linComb {y : Y'} {j : PUnit → K → L.ι} :
    y ∈ ((LB.LinComb L φ ε).pull F).U j ↔ y ∈ LB.wchart L (fun k => F ≫ φ k) (j PUnit.unit) :=
  ⟨fun h => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (mem_pull.1 h) k,
    fun h => mem_pull.2 (Set.mem_iInter.2 fun k => Set.mem_iInter.1 h k)⟩

theorem gm_pull_linComb (y : Y') (j j' : PUnit → K → L.ι) (h : y ∈ ((LB.LinComb L φ ε).pull F).U j)
    (h' : y ∈ ((LB.LinComb L φ ε).pull F).U j') :
    gm (𝟙 Y') y _ (((LB.LinComb L φ ε).pull F).g j j') =
      gm (𝟙 Y') y _ ((LB.LinComb L (fun k => F ≫ φ k) ε).g (j PUnit.unit) (j' PUnit.unit)) := by
  have a := gm_pull_g (LB.LinComb L φ ε) F (𝟙 Y') y j j' h h'
  have m : ∀ j : PUnit → K → L.ι, y ∈ ((LB.LinComb L φ ε).pull F).U j →
      (𝟙 Y' ≫ F) y ∈ LB.wchart L φ (j PUnit.unit) := fun j h => by
    rw [Category.id_comp]; exact (mem_pull (L := LB.LinComb L φ ε)).1 h
  have b := gm_linComb L φ ε (𝟙 Y' ≫ F) y (j PUnit.unit) (j' PUnit.unit) (m j h) (m j' h')
  have c := gm_linComb L (fun k => F ≫ φ k) ε (𝟙 Y') y (j PUnit.unit) (j' PUnit.unit) (mem_pull_linComb.1 h)
      (mem_pull_linComb.1 h')
  simp only [Category.assoc] at b
  exact a.trans (b.trans c.symm)

def flatGen (u : LB.Gen ((LB.LinComb L φ ε).pull F)) : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε) :=
  ⟨fun j => res (show LB.wchart L (fun k => F ≫ φ k) j ≤ ((LB.LinComb L φ ε).pull F).U (fun _ => j) from
    fun _ h => (mem_pull_linComb (ε := ε) (j := fun _ => j)).2 h) (u.s fun _ => j)⟩

def unflatGen (v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)) : LB.Gen ((LB.LinComb L φ ε).pull F) :=
  ⟨fun j => res (fun _ h => mem_pull_linComb.1 h) (v.s (j PUnit.unit))⟩

theorem flatGen_isGen {u : LB.Gen ((LB.LinComb L φ ε).pull F)} (hu : u.IsGen) : (flatGen u).IsGen := fun j j' =>
  unit_ext fun y hy => by
    have m : y ∈ ((LB.LinComb L φ ε).pull F).U (fun _ => j) ⊓ ((LB.LinComb L φ ε).pull F).U (fun _ => j') :=
      ⟨(mem_pull_linComb (j := fun _ => j)).2 hy.1, (mem_pull_linComb (j := fun _ => j')).2 hy.2⟩
    have e := congrArg (gm (𝟙 _) y _) (hu (fun _ => j) (fun _ => j'))
    rw [map_mul, gm_res _ y _ m, gm_res _ y _ m, gm_pull_linComb y _ _ m.1 m.2] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy]
    exact (gm_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gm_res _ y _ hy.2 _).symm))

theorem unflatGen_isGen {v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)} (hv : v.IsGen) : (unflatGen v).IsGen :=
  fun j j' => unit_ext fun y hy => by
    have m : y ∈ (LB.LinComb L (fun k => F ≫ φ k) ε).U (j PUnit.unit) ⊓
        (LB.LinComb L (fun k => F ≫ φ k) ε).U (j' PUnit.unit) := ⟨mem_pull_linComb.1 hy.1, mem_pull_linComb.1 hy.2⟩
    have e := congrArg (gm (𝟙 _) y _) (hv (j PUnit.unit) (j' PUnit.unit))
    rw [map_mul, gm_res _ y _ m, gm_res _ y _ m] at e
    rw [map_mul, gm_res _ y _ hy, gm_res _ y _ hy, gm_pull_linComb y _ _ hy.1 hy.2]
    exact (gm_res _ y _ hy.1 _).trans (e.trans (congrArg _ (gm_res _ y _ hy.2 _).symm))

end Flat

section Add
variable {S A Y : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] {i : splitTorus S X ⟶ G}
  {L : LB A} {F : G.left ⟶ Y}
  (hF : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G), ((t ≫ i) * g).left ≫ F = g.left ≫ F)
include hF

theorem val_flatGen {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ} {u : LB.Gen ((LB.LinComb L φ ε).pull F)}
    {χ : X} (hu : ∀ j, IsWt i _ (u.s j).val χ) {Z : Over S} (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) {z : Z.left} {J}
    (hJ : Good L z J) : val (flatGen u) ((t ≫ i) * g).left z J =
      gm t.left z ⊤ (charUnit S X χ) * val (flatGen u) g.left z J := by
  have e : ∀ k, J (((t ≫ i) * g).left ≫ F ≫ φ k) = J (g.left ≫ F ≫ φ k) := fun k => by
    rw [← Category.assoc, hF, Category.assoc]
  have m₁ := hJ.mem (fun k => F ≫ φ k) ((t ≫ i) * g).left
  have m₂ := hJ.mem (fun k => F ≫ φ k) g.left
  rw [funext e] at m₁
  rw [val_of _ _ z J _ e]
  exact (gm_res _ z _ m₁ _).trans ((gm_eq_of_isWt (hu fun _ k => J (g.left ≫ F ≫ φ k)) t g z
    (mem_pull_linComb.2 m₁) (mem_pull_linComb.2 m₂)).trans
    (congrArg _ (gm_res _ z _ m₂ _).symm))

theorem isWt_unflatGen (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ A)} {ε : K → ℤ}
    {v : LB.Gen (LB.LinComb L (fun k => F ≫ φ k) ε)} (hv : v.IsGen) {χ : X}
    (h : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (z : Z.left) (J), Good L z J →
      val v ((t ≫ i) * g).left z J = gm t.left z ⊤ (charUnit S X χ) * val v g.left z J) (j) :
    IsWt i _ ((unflatGen v).s j).val χ := isWt_of_gm _ _ fun Z t g z m₂ => by
  obtain ⟨J, hJ⟩ := exists_good_pt hL z
  have m₁ : ((t ≫ i) * g).left z ∈ ((LB.LinComb L φ ε).pull F).U j := by
    have := mem_pull.1 m₂
    refine mem_pull.2 ?_
    exact (congrArg (fun q => q z) (hF Z t g)).symm ▸ this
  have le : ((LB.LinComb L φ ε).pull F).U j ≤ LB.wchart L (fun k => F ≫ φ k) (j PUnit.unit) :=
    fun _ h => mem_pull_linComb.1 h
  have e₁ := (gm_res _ z le m₁ _).trans (gen_trans hv _ z (mem_pull_linComb.1 m₁) (hJ.mem _ _))
  have e₂ := (gm_res _ z le m₂ _).trans (gen_trans hv _ z (mem_pull_linComb.1 m₂) (hJ.mem _ _))
  refine e₁.trans (Eq.trans ?_ (congrArg _ e₂.symm))
  rw [mul_left_comm]
  refine congrArg₂ (· * ·) ?_ (h Z t g z J hJ)
  have e : ∀ k, ((t ≫ i) * g).left ≫ F ≫ φ k = g.left ≫ F ≫ φ k := fun k => by
    rw [← Category.assoc, hF, Category.assoc]
  refine Finset.prod_congr rfl fun k _ => ?_
  beta_reduce
  rw [e]

theorem exists_genWt_add (hL : L.IsLB) {K K' K'' K₀ : Type} [Fintype K] [Fintype K'] [Fintype K''] [Fintype K₀]
    {φ : K → (Y ⟶ A)} {ε : K → ℤ} {φ' : K' → (Y ⟶ A)} {ε' : K' → ℤ} {φ'' : K'' → (Y ⟶ A)} {ε'' : K'' → ℤ}
    {φ₀ : K₀ → (Y ⟶ A)} {ε₀ : K₀ → ℤ} (hw : Triv (LB.LinComb L φ₀ ε₀))
    (hs : ∀ (U : Type) [CommGroup U] (f : (Y ⟶ A) → U),
      (∏ k, f (φ k) ^ ε k) * (∏ k, f (φ' k) ^ ε' k) * ∏ k, f (φ₀ k) ^ ε₀ k = ∏ k, f (φ'' k) ^ ε'' k) {χ χ' : X}
    (h : ∃ u : LB.Gen ((LB.LinComb L φ ε).pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ)
    (h' : ∃ u : LB.Gen ((LB.LinComb L φ' ε').pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val χ') :
    ∃ u : LB.Gen ((LB.LinComb L φ'' ε'').pull F), u.IsGen ∧ ∀ j, IsWt i _ (u.s j).val (χ + χ') := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨u, hu, hχ⟩ := h
  obtain ⟨u', hu', hχ'⟩ := h'
  obtain ⟨v, hv, H⟩ := exists_gen (φ' := fun k => F ≫ φ'' k) (ε' := ε'') hL
    (fun U _ f => (Fintype.prod_sum_type _).trans ((congrArg (· * _) (Fintype.prod_sum_type _)).trans
      (hs U fun q => f (F ≫ q)))) _
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (flatGen_isGen hu) (flatGen_isGen hu'))
      (DVR.pullGen_isGen _ _ _ _ hw F))
  refine ⟨unflatGen v, unflatGen_isGen hv, isWt_unflatGen hF hL hv fun Z t g z J hJ => ?_⟩
  rw [H _ _ z J hJ, H _ _ z J hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_mul hJ, val_pull hJ, val_pull hJ, hF,
    val_flatGen hF hχ t g hJ, val_flatGen hF hχ' t g hJ, gm_charUnit, gm_charUnit, gm_charUnit, chV_add, map_mul]
  ac_rfl

end Add

theorem TQ.mul_comp_q {S : Scheme.{0}} {G : Over S} [GrpObj G] {X : Type} [AddCommGroup X] (Q : TQ G X)
    (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) : ((t ≫ Q.i) * g) ≫ Q.q = g ≫ Q.q := by
  have := Q.q_hom
  rw [MonObj.mul_comp, Category.assoc, Q.isKernel.w, ← Hom.one_def, MonObj.comp_one, _root_.one_mul]

theorem triv_square_sections {V : Type} [CommRing V] [IsLocalRing V] {B : Over (Spec (CommRingCat.of V))} [GrpObj B]
    [IsCommMonObj B] {L : RigLB B} (κ : CubicalStr B L) (c c' : 𝟙_ _ ⟶ B) :
    Triv (LB.LinComb L.L (K := Fin 4) ![((toUnit B ≫ (c * c')) * 𝟙 B).left, 𝟙 B.left, ((toUnit B ≫ c) * 𝟙 B).left,
      ((toUnit B ≫ c') * 𝟙 B).left] ![1, 1, -1, -1]) := by
  obtain ⟨w, hw⟩ := GlobalTheory.Square.triv_square (t := 𝟙 (Spec (CommRingCat.of V))) κ c c'
  let ρ : B ⟶ 𝟙_ _ ⊗ B := lift (toUnit B) (𝟙 B)
  have e : ∀ x : 𝟙_ _ ⟶ B, ρ.left ≫ (translPt (T := 𝟙_ _) B x).left = ((toUnit B ≫ x) * 𝟙 B).left := fun x => by
    rw [← Over.comp_left]
    change (ρ ≫ ((fst _ B ≫ x) * snd _ B)).left = _
    rw [MonObj.comp_mul, lift_fst_assoc, lift_snd]
  have e' : ρ.left ≫ (snd (𝟙_ _) B).left = 𝟙 B.left := by rw [← Over.comp_left, lift_snd]; rfl
  obtain ⟨u, hu, -⟩ := exists_gen (φ' := ![((toUnit B ≫ (c * c')) * 𝟙 B).left, 𝟙 B.left, ((toUnit B ≫ c) * 𝟙 B).left,
      ((toUnit B ≫ c') * 𝟙 B).left]) (ε' := ![1, 1, -1, -1]) L.isLB (fun U _ f => Finset.prod_congr rfl fun k _ => by
      fin_cases k
      exacts [congrArg (fun q => f q ^ (1 : ℤ)) (e _), congrArg (fun q => f q ^ (1 : ℤ)) e',
        congrArg (fun q => f q ^ (-1 : ℤ)) (e _), congrArg (fun q => f q ^ (-1 : ℤ)) (e _)])
    _ (DVR.pullGen_isGen _ _ _ _ hw ρ.left)
  exact ⟨u, hu⟩

theorem repWt_add : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ χ' : s.X) (c c' : 𝟙_ _ ⟶ a.B) (e : ℕ), a.RepWt c χ e → a.RepWt c' χ' e → a.RepWt (c * c') (χ + χ') e := by
  intro V _ _ _ A G _ _ s t a χ χ' c c' e h h'
  refine exists_genWt_add (fun Z x g => ?_) a.M.L.isLB (GlobalTheory.Square.triv_inv (triv_square_sections a.M.c c c'))
    (fun U _ f => ?_) h h'
  · rw [← Category.assoc, ← Category.assoc, ← Over.comp_left, ← Over.comp_left, TQ.mul_comp_q]
  · simp only [Fin.prod_univ_two, Fin.prod_univ_four, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_zpow]
    module

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAddStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.mumfordTower_repWt_mul_add : AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg) (χ χ' : s.X) (c c' : 𝟙_ _ ⟶ a.B) (e : ℕ), a.RepWt c χ e → a.RepWt c' χ' e → a.RepWt (c * c') (χ + χ') e := by
  first | exact @GlobalTheory.UU.repWt_add | exact GlobalTheory.UU.repWt_add | (intros; apply GlobalTheory.UU.repWt_add <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducedFrobeniusCompUniqueOrigin
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducedFrobeniusCompUniqueOrigin
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

namespace GlobalTheory.UT.IndComp

section Twist

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A] {L : LB A.left}

theorem twist_unique (hL : L.IsLB) {ψ : T ⊗ A ⟶ T ⊗ A} {n : ℤ}
    {α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n])}
    {t u u' : LB.Sec (LPow A L n T)} (h : IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t u)
    (h' : IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α t u') : u = u' := by
  have e : ∀ j, u.f j = u'.f j := fun j => sec_ext_val hL (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => n)
    (fun y J hJ => (VVRank.sv_of_isTwistPull A h (𝟙 _) y hJ).trans (VVRank.sv_of_isTwistPull A h' (𝟙 _) y hJ).symm) j
  obtain ⟨a, _⟩ := u
  obtain ⟨b, _⟩ := u'
  obtain rfl : a = b := funext e
  rfl

theorem exists_twist_comp (hL : L.IsLB) (ψ ψ' : T ⊗ A ⟶ T ⊗ A) (n : ℤ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ ≫ snd _ _).left] ![n, -n]))
    (α' : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (ψ' ≫ snd _ _).left] ![n, -n]))
    (hα : α.IsGen) (hα' : α'.IsGen) :
    ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, ((ψ ≫ ψ') ≫ snd _ _).left] ![n, -n]), β.IsGen ∧
      ∀ t u v : LB.Sec (LPow A L n T), IsTwistPull A L ψ' (ψ' ≫ snd _ _) rfl n n α' t u →
        IsTwistPull A L ψ (ψ ≫ snd _ _) rfl n n α u v →
        IsTwistPull A L (ψ ≫ ψ') ((ψ ≫ ψ') ≫ snd _ _) rfl n n β t v := by
  obtain ⟨β, hβ, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, ((ψ ≫ ψ') ≫ snd _ _).left]) (ε' := ![n, -n])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, zpow_neg, Over.comp_left, Category.assoc]
      rw [_root_.mul_assoc, inv_mul_cancel_left])
    (LB.mulGen L _ _ _ _ α (LB.pullGen L _ _ α' ψ.left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hα (DVR.pullGen_isGen _ _ _ _ hα' _))
  refine ⟨β, hβ, fun t u v hu hv' => VVRank.isTwistPull_of_sv A hL hβ fun y J hJ => ?_⟩
  rw [VVRank.sv_of_isTwistPull A hv' (𝟙 _) y hJ, VVRank.sv_of_isTwistPull A hu _ y hJ, hv _ _ y J hJ, val_mul hJ,
    val_pull hJ, Units.val_mul, _root_.mul_assoc, Over.comp_left _ _ _ ψ ψ', Category.assoc]

theorem exists_twist_id (hL : L.IsLB) (n : ℤ) :
    ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) ![(snd T A).left, (𝟙 (T ⊗ A) ≫ snd _ _).left] ![n, -n]), β.IsGen ∧
      ∀ t : LB.Sec (LPow A L n T), IsTwistPull A L (𝟙 _) (𝟙 _ ≫ snd _ _) rfl n n β t t := by
  obtain ⟨β, hβ, hv⟩ := exists_gen hL (φ' := ![(snd T A).left, (𝟙 (T ⊗ A) ≫ snd _ _).left]) (ε' := ![n, -n])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, zpow_neg, Category.id_comp,
        mul_inv_cancel]
      exact Fintype.prod_empty _)
    (LB.oneGen L (Y := (T ⊗ A).left))
    (fun i j => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  refine ⟨β, hβ, fun t => VVRank.isTwistPull_of_sv A hL hβ fun y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_one, Units.val_one, _root_.one_mul, Over.id_left, Category.comp_id]

end Twist

theorem indAt_comp_unique : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p p' p'' : QkPt D.toPre F N) (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), IndAt U.toUnifPre F N p ψ → (IndAt U.toUnifPre F N p' ψ' → QkAdd p p' p'' → IndAt U.toUnifPre F N p'' (ψ ≫ ψ')) ∧ (QkPt.Equiv D.toPre F p p' → IndAt U.toUnifPre F N p' ψ) ∧ (4 ≤ N → IndAt U.toUnifPre F N p ψ' → ψ = ψ') ∧ (p'.y = 0 → p'.g.IsZero → IndAt U.toUnifPre F N p' (𝟙 _)) := by
  intro hL R _ _ _ I hR D A G _ _ _ U F _ _ _ N hN p p' p'' ψ ψ' hψ
  have hG := hL.1.globalFns
  obtain ⟨Φ, hrel, -, hrat, hequ, hadd, hone⟩ := PhiProj.phi_projective hL R I hR D F N hN
  refine ⟨fun hψ' hs => ⟨by rw [Category.assoc, hψ'.1, hψ.1], fun w₀ hw₀ => ?_⟩, fun he => ⟨hψ.1, fun w₀ hw₀ => ?_⟩,
    fun h4 hψ' => ?_, fun hy hg => ⟨Category.id_comp _, fun w₀ hw₀ => ?_⟩⟩
  · obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨α', w', hα', hw', h'⟩ := hψ'.2 w₀ hw₀
    obtain ⟨w'', hw'', hΦ⟩ := hadd p p' p'' w w' hw hw' hs
    obtain ⟨β, hβ, hc⟩ := exists_twist_comp A.isLB ψ ψ' (N : ℤ) α α' hα hα'
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨β, w'', hβ, hw'', fun t t' s s' ht ht' H => ?_⟩
    obtain ⟨u, hu⟩ := VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα' t
    obtain ⟨v, hv⟩ := VVRank.exists_isTwistPull A.A (hm := rfl) A.isLB hα u
    obtain rfl : v = t' := twist_unique A.isLB (hc t u v hu hv) H
    have e₁ := ((hrel p' w' hw').2 _ _).1 (h' t u s _ ht ((he u _).2 rfl) hu)
    have e₂ := ((hrel p w hw).2 _ _).1 (h u v _ s' ((he u _).2 rfl) ht' hv)
    refine ((hrel p'' w'' hw'').2 _ _).2 ?_
    rw [hΦ, LinearMap.comp_apply, ← e₁, e₂]
  · obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨w', hw', hΦ⟩ := hequ p p' w hw he
    refine ⟨α, w', hα, hw', fun t t' s s' ht ht' H => ((hrel p' w' hw').2 _ _).2 ?_⟩
    rw [hΦ]
    exact ((hrel p w hw).2 _ _).1 (h t t' s s' ht ht' H)
  · obtain ⟨w₀, hw₀⟩ := U.ext
    obtain ⟨α, w, hα, hw, h⟩ := hψ.2 w₀ hw₀
    obtain ⟨α', w', hα', hw', h'⟩ := hψ'.2 w₀ hw₀
    obtain ⟨c, hc, hΦ⟩ := hrat p w w' hw hw'
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine AutUniq.endo_eq_of_sections hL R A F N h4 ψ ψ' hψ.1 hψ'.1 α α' hα hα'
      (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom (Units.mk0 c hc)) fun t t₁ t₂ h₁ h₂ j => ?_
    have e₁ := ((hrel p w hw).2 _ _).1 (h t t₁ _ _ ((he t _).2 rfl) ((he t₁ _).2 rfl) h₁)
    have e₂ := ((hrel p w' hw').2 _ _).1 (h' t t₂ _ _ ((he t _).2 rfl) ((he t₂ _).2 rfl) h₂)
    rw [hΦ, LinearMap.smul_apply, ← e₁] at e₂
    exact congrArg (fun x => LB.Sec.f x j) (e.injective (e₂.trans (e.map_smul c t₁).symm))
  · obtain ⟨w, hw⟩ := (CoefBasic.coef_basic R D.toPre F N p'.g).2.1 hg.1
    obtain ⟨β, hβ, hc⟩ := exists_twist_id (T := TFK (R := R) F) A.isLB (N : ℤ)
    obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG U F hN w₀ hw₀
    refine ⟨β, w, hβ, hw.1, fun t t' s s' ht ht' H => ((hrel p' w hw.1).2 _ _).2 ?_⟩
    obtain rfl : t = t' := twist_unique A.isLB (hc t) H
    rw [hone p' w hy hg hw]
    exact ((he _ _).1 ht').symm.trans ((he _ _).1 ht)

end GlobalTheory.UT.IndComp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.InducedFrobeniusCompUniqueOriginStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.indAt_comp_equiv_unique_id : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (N : ℕ), 1 ≤ N → ∀ (p p' p'' : QkPt D.toPre F N) (ψ ψ' : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)), IndAt U.toUnifPre F N p ψ → (IndAt U.toUnifPre F N p' ψ' → QkAdd p p' p'' → IndAt U.toUnifPre F N p'' (ψ ≫ ψ')) ∧ (QkPt.Equiv D.toPre F p p' → IndAt U.toUnifPre F N p' ψ) ∧ (4 ≤ N → IndAt U.toUnifPre F N p ψ' → ψ = ψ') ∧ (p'.y = 0 → p'.g.IsZero → IndAt U.toUnifPre F N p' (𝟙 _)) := by
  first | exact @GlobalTheory.UT.IndComp.indAt_comp_unique | exact GlobalTheory.UT.IndComp.indAt_comp_unique | (intros; apply GlobalTheory.UT.IndComp.indAt_comp_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfCubWeilOrthogonal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UU

theorem mem_of_orthogonal_of_card {F : Type} [Field F] {M U : Type} [CommGroup M] [CommGroup U] (φ : U →* Fˣ)
    (hφ : Function.Injective φ) (N : ℕ) (w : M → M → U → Prop)
    (hex : ∀ x y, x ^ N = 1 → y ^ N = 1 → ∃! ζ, w x y ζ)
    (hmul : ∀ x x' y ζ ζ', w x y ζ → w x' y ζ' → w (x * x') y (ζ * ζ'))
    (hsymm : ∀ x y ζ, w x y ζ → w y x ζ⁻¹)
    (hfin : Nat.card {x : M // x ^ N = 1} ≠ 0)
    (hnd : ∀ x, x ^ N = 1 → (∀ y, y ^ N = 1 → w x y 1) → x = 1)
    (T H : Subgroup M) (hT : ∀ x ∈ T, x ^ N = 1) (hH : ∀ x ∈ H, x ^ N = 1)
    (hc : Nat.card T * Nat.card H = Nat.card {x : M // x ^ N = 1})
    (hTH : ∀ x ∈ T, ∀ y ∈ H, w x y 1) (x : M) (hx : x ^ N = 1) (hxH : ∀ y ∈ H, w x y 1) : x ∈ T := by
  let K : Subgroup M := (powMonoidHom N : M →* M).ker
  have hK : ∀ a, a ∈ K ↔ a ^ N = 1 := fun a => Iff.rfl
  have hcK : Nat.card K = Nat.card {x : M // x ^ N = 1} := rfl
  have : Finite K := Nat.finite_of_card_ne_zero (hcK ▸ hfin)
  have hex' : ∀ a b : K, ∃ ζ, w a b ζ := fun a b => (hex a b a.2 b.2).exists
  choose v hv using hex'
  have hu : ∀ (a b : K) ζ, w a b ζ → v a b = ζ := fun a b ζ h => (hex a b a.2 b.2).unique (hv a b) h
  have h1 : ∀ a a' b : K, v (a * a') b = v a b * v a' b :=
    fun a a' b => hu _ _ _ (hmul _ _ _ _ _ (hv a b) (hv a' b))
  have hs : ∀ a b : K, v b a = (v a b)⁻¹ := fun a b => hu _ _ _ (hsymm _ _ _ (hv a b))
  have hTK : T ≤ K := hT
  have hHK : H ≤ K := hH
  have key := (GlobalTheory.perfectPairing_orthogonal_of_card F K (fun a b => φ (v a b))
    (fun a a' b => by rw [h1, map_mul])
    (fun a b b' => by rw [hs (b * b') a, h1, mul_inv, ← hs, ← hs, map_mul])
    (fun a ha => Subtype.ext (hnd a a.2 fun y hy => by
      have h := hv a ⟨y, hy⟩
      rwa [hφ ((ha ⟨y, hy⟩).trans φ.map_one.symm)] at h))
    (T.subgroupOf K) (H.subgroupOf K)
    (fun t ht h hh => by rw [hu _ _ _ (hTH t ht h hh), map_one])
    (by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTK).toEquiv,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHK).toEquiv, hc, hcK])).1 ⟨x, hx⟩
  exact key.1 fun h hh => by rw [hu ⟨x, hx⟩ h _ (hxH h hh), map_one]

theorem mem_of_cubWeil_orthogonal : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ T H : Subgroup (TF (R := V) F ⟶ G), (∀ x ∈ T, x ^ N = 1) → (∀ x ∈ H, x ^ N = 1) → Nat.card T * Nat.card H = N ^ (2 * A.g) → (∀ x ∈ T, ∀ y ∈ H, CubWeil s.P.c N x y 1) → ∀ x, x ^ N = 1 → (∀ y ∈ H, CubWeil s.P.c N x y 1) → x ∈ T := by
  intro hL V _ _ _ A G _ _ s F _ _ _ N hN T H hT hH hc hTH x hx hxH
  obtain ⟨hcard, hnd⟩ := GlobalTheory.T.generic_fibre_card_torsion_cubical_pairing_perfect hL V A G s F N hN
  let ε₀ : Γ(Spec (CommRingCat.of F), ⊤) ≃+* F := (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv
  refine mem_of_orthogonal_of_card (F := F) (M := TF (R := V) F ⟶ G) (U := Γ((TF (R := V) F).left, ⊤)ˣ)
    (Units.map ε₀.toMonoidHom) (Units.map_injective ε₀.injective) N (CubWeil s.P.c N)
    (fun _ _ hx hy => existsUnique_cubWeil _ hx hy) (fun _ _ _ _ _ h h' => h.mul_left h')
    (fun _ _ _ h => h.symm) ?_ hnd T H hT hH (hc.trans hcard.symm) hTH x hx hxH
  rw [hcard]
  exact pow_ne_zero _ (by omega)

end GlobalTheory.UU
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsFiniteOfPullVeryAmpleIsoPow
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsFiniteOfPullVeryAmpleIsoPow
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.PullAmpleFinite

open TopologicalSpace GlobalTheory.MulFinite

theorem sec_gs {Z Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) (r : Z ⟶ Y) (z : Z) {j j' : M.ι}
    (hj : r z ∈ M.U j) (hj' : r z ∈ M.U j') :
    gs r z (M.U j) (s.f j) = (gm r z (M.U j ⊓ M.U j') (M.g j j')).val * gs r z (M.U j') (s.f j') := by
  have hm : r z ∈ M.U j ⊓ M.U j' := ⟨hj, hj'⟩
  exact (gs_res r z _ hm _).symm.trans ((congrArg (gs r z _) (s.compat j j')).trans ((gs_mul r z _ hm _ _).trans
    (congrArg₂ (· * ·) (gs_unit r z _ hm _) (gs_res r z _ hm _))))

theorem pow_cancel {R : Type} [CommRing R] (g t : Rˣ) (x : R) (e : ℕ) :
    (g.val * x) ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t).val = x ^ e * t.val := by
  have h : (g ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t)) = t := by
    rw [zpow_natCast, _root_.one_mul, mul_inv_cancel_left]
  have h' : g.val ^ e * (1 * (g ^ (e : ℤ))⁻¹ * t).val = t.val := congrArg Units.val h
  rw [mul_pow, ← h']; ring

theorem exists_fn {X W Z : Scheme.{0}} (H : LB X) (hH : H.IsLB) (L : LB W) (hL : L.IsLB)
    (s : LB.Sec L) (m : W ⟶ X) (e : ℕ) (he : e ≠ 0)
    (α : LB.Iso (pw L e) (H.pull m)) (hα : α.IsGen)
    (r : Z ⟶ W) (j₀ : H.ι) (h₀ : ∀ z, m (r z) ∈ H.U j₀) :
    ∃ a : Γ(Z, ⊤), Z.basicOpen a = r ⁻¹ᵁ nonzeroLocus s := by
  let V : L.ι → Z.Opens := fun j => r ⁻¹ᵁ L.U j
  have l₂ : ∀ j, V j ≤ r ⁻¹ᵁ ((H.pull m).U (fun _ => j₀) ⊓ (pw L e).U j) :=
    fun j z hz => ⟨mem_pull.2 (h₀ z), hz⟩
  obtain ⟨u, hu⟩ : ∃ u : ∀ j, Γ(Z, V j), ∀ j z, z ∈ V j → gs (𝟙 Z) z (V j) (u j) =
      gs r z (L.U j) (s.f j) ^ e * (gw α r z j₀ j).val := by
    refine ⟨fun j => (r.appLE _ _ le_rfl).hom (s.f j) ^ e *
      (r.appLE _ _ (l₂ j)).hom (α.s (fun _ => j₀, j)).val, fun j z hz => ?_⟩
    refine (gs_mul (𝟙 Z) z (V j) hz _ _).trans (congrArg₂ (· * ·) ((gs_pow (𝟙 Z) z (V j) hz _ _).trans ?_) ?_)
    · exact congrArg (· ^ e) (gs_appLE r z _ _ _ hz _)
    · exact (gs_appLE r z _ _ _ hz _).trans (gs_unit r z _ (l₂ j hz) _)
  have hcov : (⊤ : Z.Opens) ≤ iSup V := fun z _ => by
    obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hL (r z)
    exact Opens.mem_iSup.2 ⟨j, hj⟩
  obtain ⟨a, ha, -⟩ := Z.sheaf.existsUnique_gluing' V ⊤ (fun j => homOfLE le_top) hcov u
    (fun j j' => fn_ext (V := V j ⊓ V j') fun z hz => by
      refine (gs_res (𝟙 Z) z inf_le_left hz _).trans (Eq.trans ?_ (gs_res (𝟙 Z) z inf_le_right hz _).symm)
      rw [hu j z hz.1, hu j' z hz.2, sec_gs s r z hz.1 hz.2,
        (isGen_iff α).1 hα Z r z j₀ j₀ j j' (h₀ z) (h₀ z) hz.1 hz.2]
      have h1 : gm (r ≫ m) z (H.U j₀ ⊓ H.U j₀) (H.g j₀ j₀) = 1 := gm_self hH _ z (h₀ z)
      have t₁ : gm r z ((pw L e).U j ⊓ (pw L e).U j') ((pw L e).g j j') =
          gm r z (L.U j ⊓ L.U j') (L.g j j') ^ (e : ℤ) := map_zpow _ _ _
      rw [h1, t₁]
      exact pow_cancel _ _ _ _)
  refine ⟨a, ?_⟩
  ext z
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart hL (r z)
  have k₁ : gs (𝟙 Z) z ⊤ a = gs (𝟙 Z) z (V j) (u j) :=
    (gs_res (𝟙 Z) z le_top hj a).symm.trans (congrArg (gs (𝟙 Z) z (V j)) (ha j))
  have k₂ : z ∈ Z.basicOpen (show Γ(Z, ⊤) from a) ↔ IsUnit (gs r z (L.U j) (s.f j)) := by
    refine (isUnit_gs (𝟙 Z) z ⊤ trivial a).symm.trans ?_
    rw [k₁, hu j z hj, Units.isUnit_mul_units, isUnit_pow_iff he]
  refine k₂.trans ⟨fun h => ?_, fun h => ?_⟩
  · exact Opens.mem_iSup.2 ⟨j, (isUnit_gs r z _ hj _).1 h⟩
  · obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (show r z ∈ nonzeroLocus s from h)
    have hk' : r z ∈ L.U k := W.basicOpen_le _ hk
    rw [sec_gs s r z hj hk']
    exact (Units.isUnit _).mul ((isUnit_gs r z _ hk' _).2 hk)

theorem isFinite_of_pull_iso_pow :
    ∀ (K : Type) [Field K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (n : ℕ) (s : Fin (n + 1) → LB.Sec H') (d : ℕ), H.IsLB → H'.IsLB → IsSeparated f → VeryAmpleBy (φ ≫ f) H' s → 1 ≤ d → LBIso (pw H' d) (H.pull φ) → IsFinite φ := by
  intro K _ X X' f φ H H' n s d hH hH' hf hva hd ⟨α, hα⟩
  have : IsProper (φ ≫ f) := isProper_of_isProjBy K X' _ ⟨H', hH', n, s, hva⟩
  have : IsProper φ := .of_comp _ f
  suffices LocallyQuasiFinite φ from .of_isProper_of_locallyQuasiFinite _
  refine .of_fiberToSpecResidueField _ fun y => ?_
  obtain ⟨hcov, hs⟩ := hva
  have hy : ∀ z, φ (φ.fiberι y z) = y := fun z => (φ.range_fiberι y).le ⟨z, rfl⟩
  have := isAffineHom_fromSpecResidueField X y
  have : IsAffineHom (φ.fiberι y) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsAffineHom.{0})
      (IsPullback.of_hasPullback φ (X.fromSpecResidueField y)).flip this
  obtain ⟨j₀, hj₀⟩ := Geo.Tor.exists_chart hH y
  have key := fun i => exists_fn H hH H' hH' (s i) φ d (by omega) α hα (φ.fiberι y) j₀ (fun z => by
    rw [hy]; exact hj₀)
  choose a ha using key
  have : IsProper (φ.fiberToSpecResidueField y) :=
    inferInstanceAs (IsProper (pullback.snd φ (X.fromSpecResidueField y)))
  refine locallyQuasiFinite_of_cover (K := X.residueField y) (φ.fiberToSpecResidueField y) a ?_ fun i => ?_
  · simp only [ha]
    rw [← Scheme.Hom.preimage_iSup]
    exact (congrArg (fun V => φ.fiberι y ⁻¹ᵁ V) hcov).trans rfl
  · rw [ha]
    exact (hs i).1.preimage _

end GlobalTheory.PullAmpleFinite
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsFiniteOfPullVeryAmpleIsoPowStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.isFinite_of_pull_veryAmple_iso_pow : ∀ (K : Type) [Field K] (X X' : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of K)) (φ : X' ⟶ X) (H : LB X) (H' : LB X') (n : ℕ) (s : Fin (n + 1) → LB.Sec H') (d : ℕ), H.IsLB → H'.IsLB → IsSeparated f → VeryAmpleBy (φ ≫ f) H' s → 1 ≤ d → LBIso (pw H' d) (H.pull φ) → IsFinite φ := by
  first | exact @GlobalTheory.PullAmpleFinite.isFinite_of_pull_iso_pow | exact GlobalTheory.PullAmpleFinite.isFinite_of_pull_iso_pow | (intros; apply GlobalTheory.PullAmpleFinite.isFinite_of_pull_iso_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtUnique
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU

theorem TQ.exists_genWt_pull_comp {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G] (Q : TQ G X)
    {Y : Scheme.{0}} (N : LB Y) (b : Q.B.left ⟶ Y) {χ : X} (u : LB.Gen (N.pull (Q.q.left ≫ b))) (hu : u.IsGen)
    (hw : ∀ j, IsWt Q.i _ (u.s j).val χ) : ∃ t, Q.GenWt (N.pull b) t χ := by
  have le : ∀ J : PUnit → PUnit → N.ι,
      ((N.pull b).pull Q.q.left).U J ≤ (N.pull (Q.q.left ≫ b)).U (J PUnit.unit) :=
    fun J y hy => mem_pull.2 ((mem_pull (L := N) (F := b)).1 ((mem_pull (L := N.pull b)).1 hy))
  refine ⟨⟨fun J => res (le J) (u.s (J PUnit.unit))⟩, fun i j => Geo.Tor.unit_ext fun y hy => ?_,
    fun J => (hw _).res (le J)⟩
  have hm : (𝟙 G.left : G.left ⟶ G.left) y ∈
      (N.pull (Q.q.left ≫ b)).U (i PUnit.unit) ⊓ (N.pull (Q.q.left ≫ b)).U (j PUnit.unit) := ⟨le i hy.1, le j hy.2⟩
  have h1 := congrArg (gm (𝟙 G.left) y _) (hu (i PUnit.unit) (j PUnit.unit))
  rw [map_mul, gm_res _ y _ hm, gm_res _ y _ hm, gm_pull_g N _ (𝟙 _) y _ _ hm.1 hm.2] at h1
  have h2 := (gm_pull_g (N.pull b) Q.q.left (𝟙 _) y i j hy.1 hy.2).trans
    (gm_pull_g N b (𝟙 _ ≫ Q.q.left) y _ _ ((mem_pull (L := N.pull b)).1 hy.1)
      ((mem_pull (L := N.pull b)).1 hy.2))
  rw [Category.assoc] at h2
  rw [map_mul, gm_res _ y inf_le_left hy, gm_res _ y inf_le_right hy]
  exact (gm_res (𝟙 _) y (le i) hy.1 _).trans
    (h1.trans (congrArg₂ (· * ·) h2.symm (gm_res (𝟙 _) y (le j) hy.2 _).symm))

theorem hasGen_sum_of_lbIso {X Y : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ) (H : LBIso (LB.LinComb L φ ε) (LB.LinComb L φ' ε')) :
    KerPow.HasGen L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k) := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ j : K' ⊕ K → L.ι, LB.wchart L (Sum.elim φ' φ) j ≤
      LB.wchart L φ' (j ∘ Sum.inl) ⊓ LB.wchart L φ (j ∘ Sum.inr) := fun j y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (.inr k)⟩
  refine gen_chartPull (A' := LB.LinComb L (Sum.elim φ' φ) (Sum.elim ε' fun k => -ε k)) (h := 𝟙 Y)
    (A := LB.div (LB.LinComb L φ' ε') (LB.LinComb L φ ε))
    ⟨fun j => (j ∘ Sum.inl, j ∘ Sum.inr), le, fun y p q hp hq => ?_⟩ w hw
  refine (gm_linComb L _ _ (𝟙 Y) y p q hp hq).trans (Eq.trans ?_
    (gm_div (LB.LinComb L φ ε) (LB.LinComb L φ' ε') (𝟙 Y) y (p ∘ Sum.inl, p ∘ Sum.inr) (q ∘ Sum.inl, q ∘ Sum.inr)
      ⟨le p hp, le q hq⟩).symm)
  refine Eq.trans ?_ (congrArg₂ (fun a b => a * b⁻¹) (gm_linComb L φ' ε' (𝟙 Y) y _ _ (le p hp).1 (le q hq).1)
    (gm_linComb L φ ε (𝟙 Y) y _ _ (le p hp).2 (le q hq).2)).symm
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib]
  rfl

theorem section_eq_of_lbIso {S : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (hK : KTriv B L)
    (c c' : 𝟙_ _ ⟶ B) {T : Over S} {Y : Scheme.{0}} {b : Y ⟶ B.left} {p : Y ⟶ T.left}
    (pb : IsPullback b p B.hom T.hom)
    (H : LBIso ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c) * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull b)
      ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c') * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull b)) :
    toUnit T ≫ c = toUnit T ≫ c' := by
  have H₁ := hasGen_sum_of_lbIso L _ _ _ _ (H.chartPull (chartPullIn _ _ _ _) (chartPullIn _ _ _ _))
  let x : T ⟶ B := toUnit T ≫ c
  let y : T ⟶ B := toUnit T ≫ c'
  let w : T ⊗ B ⟶ B := (fst T B ≫ y⁻¹) * snd T B
  let h : (T ⊗ B).left ⟶ Y := pb.lift w.left (fst T B).left ((Over.w w).trans (Over.w (fst T B)).symm)
  have hb : h ≫ b = w.left := pb.lift_fst _ _ _
  have key : ∀ d : 𝟙_ _ ⟶ B, w ≫ ((toUnit B ≫ d) * 𝟙 B) = translPt B ((toUnit T ≫ d) * y⁻¹) := fun d => by
    change _ = (fst T B ≫ ((toUnit T ≫ d) * y⁻¹)) * snd T B
    rw [MonObj.comp_mul, MonObj.comp_mul, Category.comp_id, _root_.mul_assoc, ← Category.assoc, ← Category.assoc,
      toUnit_unique (w ≫ toUnit B) (fst T B ≫ toUnit T)]
  have k₁ : w ≫ ((toUnit B ≫ c') * 𝟙 B) = snd T B := by
    rw [key, mul_inv_cancel, KerPow.translPt_one]
  have H₂ := H₁.pull h (φ' := Sum.elim ![(snd T B).left, w.left] ![(translPt B (x * y⁻¹)).left, w.left]) fun k => by
    rcases k with k | k <;> refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) hb).trans ?_) <;> fin_cases k
    exacts [congrArg (fun q => q.left) k₁, Category.comp_id _, congrArg (fun q => q.left) (key c), Category.comp_id _]
  have triv : KerPow.HasGen L (Y := (T ⊗ B).left) (K := Fin 0) ![] ![] :=
    KerPow.hasGen_of_trivial hL fun U _ h => by simp
  have H₃ := H₂.comb hL triv (φ'' := ![(translPt B (x * y⁻¹)).left, (snd T B).left]) (ε'' := ![1, -1])
    fun U _ h => by
      rw [Fintype.prod_sum_type]
      simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr]
      apply Additive.ofMul.injective
      simp
      abel
  exact mul_inv_eq_one.1 (KerPow.eq_one_of_locGen hK (x * y⁻¹) fun _ => ⟨⊤, trivial, H₃.pull _ fun _ => rfl⟩)

theorem section_eq_of_isWt {S S' : Scheme.{0}} {B : Over S} [GrpObj B] {L : LB B.left} (hL : L.IsLB) (hK : KTriv B L)
    (c c' : 𝟙_ _ ⟶ B) {X : Type} [AddCommGroup X] {G : Over S'} [GrpObj G] (Q : TQ G X) {f : S' ⟶ S}
    {b : Q.B.left ⟶ B.left} (pb : IsPullback b Q.B.hom B.hom f) (χ : X)
    (hc : ∃ u : LB.Gen ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c) * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull
      (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ)
    (hc' : ∃ u : LB.Gen ((LB.LinComb L (K := Fin 2) ![((toUnit B ≫ c') * 𝟙 B).left, 𝟙 B.left] ![-1, 1]).pull
      (Q.q.left ≫ b)), u.IsGen ∧ ∀ j, IsWt Q.i _ (u.s j).val χ) :
    (toUnit (Over.mk f) ≫ c).left = (toUnit (Over.mk f) ≫ c').left := by
  obtain ⟨u, hu, hw⟩ := hc
  obtain ⟨u', hu', hw'⟩ := hc'
  obtain ⟨v, hv⟩ := Q.exists_genWt_pull_comp _ b u hu hw
  obtain ⟨v', hv'⟩ := Q.exists_genWt_pull_comp _ b u' hu' hw'
  have H := lbIso_of_genWt _ _ _ Q _ _ v v' χ (pull_isLB (DVR.linComb_isLB _ hL _ _) _)
    (pull_isLB (DVR.linComb_isLB _ hL _ _) _) hv hv'
  exact congrArg (fun q => q.left) (section_eq_of_lbIso hL hK c c' (T := Over.mk f) pb H)

theorem repWt_unique : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ (χ : s.X) (c c' : 𝟙_ _ ⟶ a.B), (∀ e, a.RepWt c χ e) → (∀ e, a.RepWt c' χ e) → c = c' := by
  intro _ V _ _ _ A G _ _ s t a hK χ c c' hc hc'
  have := s.cdvr.2.1
  refine Over.OverMorphism.ext (GlobalTheory.hom_ext_of_isHausdorff (IsLocalRing.maximalIdeal V) fun e => ?_)
  obtain ⟨pb, -⟩ := a.b_pb e
  have k := section_eq_of_isWt a.M.L.isLB hK c c' (t.l e).Q pb.1 χ (hc e) (hc' e)
  rw [Over.comp_left, Over.comp_left, Rosenlicht.toUnit_left] at k
  exact k

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtUniqueStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.mumfordTower_repWt_unique : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ (t : Tower s) (a : t.Alg), KTriv a.B a.M.L.L → ∀ (χ : s.X) (c c' : 𝟙_ _ ⟶ a.B), (∀ e, a.RepWt c χ e) → (∀ e, a.RepWt c' χ e) → c = c' := by
  first | exact @GlobalTheory.UU.repWt_unique | exact GlobalTheory.UU.repWt_unique | (intros; apply GlobalTheory.UU.repWt_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullbackOfEquationsLift
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ProjBaseChange

open MvPolynomial

variable {X X' : Scheme.{0}} {R R' : Type} [CommRing R] [CommRing R']

theorem appLE_cst (φ : X' ⟶ X) (f : X ⟶ Spec (CommRingCat.of R)) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) :
    (φ.appLE U V h).hom.comp (cst f U) = cst (φ ≫ f) V := by
  have e : X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op ≫ φ.appLE U V h =
      φ.appTop ≫ X'.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE]
    rfl
  ext a
  exact congrArg (fun q => q.hom (f.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))) e

theorem cst_comp (f' : X' ⟶ Spec (CommRingCat.of R')) (g : R →+* R') (V : X'.Opens) :
    cst (f' ≫ Spec.map (CommRingCat.ofHom g)) V = (cst f' V).comp g := by
  ext a
  have e := congrArg (fun q => q.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom g))
  exact congrArg (fun q => rs X' (le_top : V ≤ ⊤) (f'.appTop.hom q)) e.symm

theorem gs_appLE (φ : X' ⟶ X) {U : X.Opens} {V : X'.Opens} (h : V ≤ φ ⁻¹ᵁ U) (z : X') (hz : z ∈ V) (a : Γ(X, U)) :
    gs (𝟙 X') z V ((φ.appLE U V h).hom a) = gs φ z U a :=
  (gs_res (𝟙 X') z h hz ((φ.app U).hom a)).trans ((gs_pull (𝟙 X') φ z U (h hz) a).trans (by rw [Category.id_comp]))

theorem isClosedImmersion_of_charts (φ : X' ⟶ X) {J : Type} (U : J → X.Opens) (hc : ⨆ i, U i = ⊤)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (φ ⁻¹ᵁ U i))
    (hs : ∀ i, Function.Surjective (φ.app (U i)).hom) : IsClosedImmersion φ := by
  refine @HasAffineProperty.of_iSup_eq_top _ _ IsClosedImmersion.hasAffineProperty _ _ _ _
    (fun i => ⟨U i, hU i⟩) hc fun i => ⟨hV i, ?_⟩
  have key : ∀ (A : X.Opens) (B : X'.Opens) (h : B ≤ φ ⁻¹ᵁ A), A = U i → B = φ ⁻¹ᵁ U i →
      Function.Surjective (φ.appLE A B h).hom := by
    rintro _ _ h rfl rfl
    rw [Scheme.Hom.appLE_eq_app]
    exact hs i
  show Function.Surjective ((φ ∣_ U i).app ⊤).hom
  rw [morphismRestrict_app']
  exact key _ _ _ (by simp) (by simp)

theorem isPullback_of_charts (g : R →+* R') (hg : Function.Surjective g) (φ : X' ⟶ X)
    (f : X ⟶ Spec (CommRingCat.of R)) (f' : X' ⟶ Spec (CommRingCat.of R'))
    (hw : φ ≫ f = f' ≫ Spec.map (CommRingCat.ofHom g)) {J : Type} (U : J → X.Opens) (V : J → X'.Opens)
    (hUV : ∀ i, V i = φ ⁻¹ᵁ U i) (hc : ⨆ i, U i = ⊤) (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ i, IsAffineOpen (V i))
    (hs : ∀ i, Function.Surjective (φ.appLE (U i) (V i) (hUV i).le).hom)
    (hk : ∀ i a, (φ.appLE (U i) (V i) (hUV i).le).hom a = 0 → ∀ (B : Type) [CommRing B] (θ : Γ(X, U i) →+* B)
      (c : R' →+* B), θ.comp (cst f (U i)) = c.comp g → θ a = 0) :
    IsPullback φ f' f (Spec.map (CommRingCat.ofHom g)) := by
  obtain rfl : V = fun i => φ ⁻¹ᵁ U i := funext hUV
  simp only [Scheme.Hom.appLE_eq_app] at hs hk
  have := isClosedImmersion_of_charts φ U hc hU hV hs
  have := IsClosedImmersion.spec_of_surjective (CommRingCat.ofHom g) hg
  have hle : φ.ker ≤ (pullback.fst f (Spec.map (CommRingCat.ofHom g))).ker := by
    refine Scheme.IdealSheafData.le_of_iSup_eq_top (fun i => ⟨U i, hU i⟩) hc fun i a ha => ?_
    rw [Scheme.Hom.ker_apply] at ha ⊢
    refine hk i a ha _ _ (cst (pullback.snd f (Spec.map (CommRingCat.ofHom g))) _) ?_
    rw [← cst_comp, ← pullback.condition, ← appLE_cst _ f le_rfl, Scheme.Hom.appLE_eq_app]
  have hl := IsClosedImmersion.lift_fac φ _ hle
  refine ⟨⟨hw⟩, ⟨PullbackCone.IsLimit.mk _
    (fun t => pullback.lift t.fst t.snd t.condition ≫ IsClosedImmersion.lift φ _ hle) (fun t => ?_) (fun t => ?_)
    (fun t m h₁ _ => ?_)⟩⟩
  · rw [Category.assoc, hl, pullback.lift_fst]
  · rw [← cancel_mono (Spec.map (CommRingCat.ofHom g)), Category.assoc, ← hw, ← Category.assoc, Category.assoc _ _ φ,
      hl, pullback.lift_fst, t.condition]
  · rw [← cancel_mono φ, Category.assoc, hl, pullback.lift_fst, h₁]

theorem eventually_exists_form (f : X ⟶ Spec (CommRingCat.of R)) {H : LB X} {m : ℕ} {s : Fin (m + 1) → H.Sec}
    (hc : ⨆ i, nonzeroLocus (s i) = ⊤) (ha : ∀ i, IsAffineOpen (nonzeroLocus (s i)))
    (r : ∀ i, Fin (m + 1) → Γ(X, nonzeroLocus (s i))) (hr' : ∀ i, IsRatioFamily s i (r i)) (i : Fin (m + 1))
    (p : MvPolynomial (Fin (m + 1)) R) (hp : eval₂Hom (cst f _) (r i) p = 0) :
    ∀ᶠ d in Filter.atTop, ∃ F ∈ vanishingForms f s d, MvPolynomial.X i - 1 ∣ F - p := by
  obtain ⟨e, F, hF, hFp⟩ := (ThetaDeform.exists_homogeneous i p).exists
  have hFi : eval₂Hom (cst f _) (r i) F = 0 := by
    obtain ⟨G, hG⟩ := hFp
    rw [eq_add_of_sub_eq hG, map_add (f := _), hp, map_mul, map_sub, map_one, eval₂Hom_X', (hr' i).self_eq_one]
    simp
  have hn : ∀ j, ∃ n, r j i ^ n * eval₂Hom (cst f _) (r j) F = 0 := fun j => by
    refine exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isAffineOpen X (ha j) _ _ (fn_ext fun y hy => ?_)
    have hj : y ∈ nonzeroLocus (s j) := X.basicOpen_le _ hy
    obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hj
    have uj := (mem_nonzeroLocus_iff_isUnit _ hk).1 hj
    have hi : y ∈ nonzeroLocus (s i) := by
      rw [mem_nonzeroLocus_iff_isUnit _ hk, (hr' j).gs_eq hj hk i]
      exact ((LBGerm.isUnit_gs_iff (𝟙 X) y _ hj _).2 hy).mul uj
    have e₁ := ((hr' j).gs_form f hj hk hF).symm.trans ((hr' i).gs_form f hi hk hF)
    rw [hFi, LBGerm.gs_zero _ y _ hi, mul_zero] at e₁
    rw [LBGerm.gs_zero _ y _ hy]
    exact (gs_res _ y (X.basicOpen_le _) hy _).trans ((uj.pow e).mul_right_eq_zero.1 e₁)
  choose n hn using hn
  filter_upwards [Filter.eventually_ge_atTop (Finset.univ.sup n + e)] with d hd
  obtain ⟨c, rfl⟩ : ∃ c, d = c + e := ⟨d - e, by omega⟩
  refine ⟨MvPolynomial.X i ^ c * F, ?_, ?_⟩
  · refine mem_vanishingForms_of_ratios f hc r hr' ((isHomogeneous_X_pow i c).mul hF) fun j => ?_
    have hle : n j ≤ c := (Finset.le_sup (Finset.mem_univ j)).trans (by omega)
    obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le' hle
    rw [map_mul, map_pow, eval₂Hom_X', pow_add, _root_.mul_assoc, hn j, mul_zero]
  · have : MvPolynomial.X i ^ c * F - p = (MvPolynomial.X i ^ c - 1) * F + (F - p) := by ring
    rw [this]
    exact ((sub_one_dvd_pow_sub_one _ c).mul_right _).add hFp

theorem isPullback_of_equations_lift : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB → VeryAmpleBy f H s → ∀ (R' : Type) [CommRing R'] (g : R →+* R'), Function.Surjective g → ∀ (X' : Scheme.{0}) (f' : X' ⟶ Spec (CommRingCat.of R')) (H' : LB X') (s' : Fin (n + 1) → LB.Sec H') (φ : X' ⟶ X) (w : LB.Iso H' (H.pull φ)), H'.IsLB → VeryAmpleBy f' H' s' → φ ≫ f = f' ≫ (Spec.map (CommRingCat.ofHom g)) → w.IsGen → (∀ j, (∀ z (k : (H).ι) (k' : (H').ι), (φ) z ∈ (H).U k → z ∈ (H').U k' → gs (φ) z _ ((s j).f k) = (Geo.Tor.gw (w) (𝟙 _) z k k').val * gs (𝟙 _) z _ ((s' j).f k'))) → ∀ t₀ : ℕ, (∀ t, t₀ ≤ t → ∀ F : MvPolynomial (Fin (n + 1)) R, F.IsHomogeneous t → (∀ k : (H').ι, MvPolynomial.eval₂Hom (cst (f' ≫ (Spec.map (CommRingCat.ofHom g))) ((H').U k)) (fun j => (s' j).f k) (F) = 0) → ∃ F₁ : MvPolynomial (Fin (n + 1)) R, F₁.IsHomogeneous t ∧ (∀ k : (H).ι, MvPolynomial.eval₂Hom (cst (f) ((H).U k)) (fun j => (s j).f k) (F₁) = 0) ∧ MvPolynomial.map g F₁ = MvPolynomial.map g F) → IsPullback φ f' f (Spec.map (CommRingCat.ofHom g)) := by
  intro R _ X f H n s hH ⟨hc, hs⟩ R' _ g hg X' f' H' s' φ w hH' ⟨hc', hs'⟩ hw _ hrel t₀ hlift
  choose ha r hr hsur using hs
  choose ha' r' hr' hsur' using hs'
  have hR : ∀ i, IsRatioFamily s i (r i) := hr
  have hR' : ∀ i, IsRatioFamily s' i (r' i) := hr'
  have unit : ∀ i z k, φ z ∈ H.U k → (φ z ∈ nonzeroLocus (s i) ↔ IsUnit (gs φ z _ ((s i).f k))) := fun i z k hk =>
    ((mem_nonzeroLocus_iff_isUnit _ hk).trans (LBGerm.isUnit_gs_iff (𝟙 X) _ _ hk _)).trans
      (LBGerm.isUnit_gs_iff φ z _ hk _).symm
  have hUV : ∀ i, nonzeroLocus (s' i) = φ ⁻¹ᵁ nonzeroLocus (s i) := fun i => by
    ext z
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    refine (mem_nonzeroLocus_iff_isUnit _ hk').trans (Iff.trans ?_ (unit i z k hk).symm)
    rw [hrel i z k k' hk hk', Units.isUnit_units_mul]
  have hrr : ∀ i j, (φ.appLE _ _ (hUV i).le).hom (r i j) = r' i j := fun i j => fn_ext fun z hz => by
    obtain ⟨k, hk⟩ := exists_chart hH (φ z)
    obtain ⟨k', hk'⟩ := exists_chart hH' z
    have hz₁ : φ z ∈ nonzeroLocus (s i) := (hUV i).le hz
    have h : φ z ∈ nonzeroLocus (s i) ⊓ H.U k := ⟨hz₁, hk⟩
    have e := congrArg (gs φ z _) (hr i j k)
    rw [gs_res _ z _ h, gs_mul _ z _ h, gs_res _ z _ h, gs_res _ z _ h] at e
    rw [gs_appLE φ _ z hz]
    refine ((unit i z k hk).1 hz₁).mul_right_cancel (e.symm.trans ?_)
    rw [hrel j z k k' hk hk', hrel i z k k' hk hk', (hR' i).gs_eq hz hk' j]
    ring
  have hev : ∀ i p, (φ.appLE _ _ (hUV i).le).hom (eval₂Hom (cst f _) (r i) p) =
      eval₂Hom (cst (f' ≫ Spec.map (CommRingCat.ofHom g)) _) (r' i) p := fun i p => by
    rw [map_eval₂Hom, appLE_cst, hw]
    simp only [hrr]
  refine isPullback_of_charts g hg φ f f' hw _ _ hUV hc ha ha' (fun i b => ?_) fun i a h0 B _ θ c hθ => ?_
  · obtain ⟨q, rfl⟩ := hsur' i b
    obtain ⟨p, rfl⟩ := MvPolynomial.map_surjective g hg q
    exact ⟨_, (hev i p).trans (by rw [cst_comp, eval₂Hom_map_hom])⟩
  · obtain ⟨p, rfl⟩ := hsur i a
    rw [hev] at h0
    obtain ⟨t, ht, F, hF, G, hG⟩ := ((Filter.eventually_ge_atTop t₀).and
      (eventually_exists_form _ hc' ha' r' hR' i p h0)).exists
    obtain ⟨F₁, h₁, h₂, h₃⟩ := hlift t ht F hF.1 hF.2
    have e₁ : eval₂Hom (cst f _) (r i) F₁ = 0 := (hR i).eval_eq_zero f ⟨h₁, h₂⟩
    have e₂ : eval₂Hom (cst f _) (r i) p = eval₂Hom (cst f _) (r i) F := by
      rw [eq_add_of_sub_eq hG, map_add (f := _), map_mul, map_sub, map_one, eval₂Hom_X', (hR i).self_eq_one]
      simp
    have e₃ : ∀ P, θ (eval₂Hom (cst f _) (r i) P) = eval₂Hom c (fun j => θ (r i j)) (MvPolynomial.map g P) :=
      fun P => by rw [map_eval₂Hom, hθ, eval₂Hom_map_hom]
    rw [e₂, e₃, ← h₃, ← e₃, e₁, map_zero]

end GlobalTheory.ProjBaseChange
end
