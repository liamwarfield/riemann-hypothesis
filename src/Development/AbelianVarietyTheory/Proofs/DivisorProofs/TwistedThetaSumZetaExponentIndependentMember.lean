module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramedTorsionTorusExtensionRespectCubical
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivOfKer
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaConstantsTranslateEqTwistedSums

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsAffineTwoMembers
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTranslationExponentsAffine
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransExpAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.Poinc.Sep.TransAff
open GlobalTheory.UT.CoefBasic GlobalTheory.UT.TorsionValue GlobalTheory.Poinc.Sep.TermsExt GlobalTheory.Poinc.Tors

theorem ratio_pow {V : Type} [CommRing V] [IsDomain V] {A : PolAV (Sp (FractionRing V))}
    {ρA : LB.Gen (A.L.pull (eSec A.A))} {N : ℕ} {x : TFK (R := V) (FractionRing V) ⟶ A.A} {e e' : FrAt x}
    (H : IsTorsFrame A ρA N x e) (H' : IsTorsFrame A ρA N x e') {l : FractionRing V}
    (hl : ∀ z J, Good A.L z J → (val e' (𝟙 _) z J).val =
      @id ((TFK (R := V) (FractionRing V)).left.presheaf.stalk z) (cstH (R := V) z l) * (val e (𝟙 _) z J).val) :
    l ^ (N ^ 2) = 1 := by
  obtain ⟨-, he, α, hα, nα, cα⟩ := H
  obtain ⟨-, he', α', hα', nα', cα'⟩ := H'
  have hp : Function.Surjective A.A.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _ A.isAb).2
  have hαα : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) J, Good A.L z J → val α r z J = val α' r z J :=
    gen_unique A.isLB A.A.hom (eSec A.A) (Over.w η[A.A]) hp hα hα' (fun w I hI => by
      have a := val_corr hI nα (𝟙 _)
      have b := val_corr hI nα' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm)
  obtain ⟨z⟩ : Nonempty (TFK (R := V) (FractionRing V)).left := exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := exists_good' A.isLB z
  have q : val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) = val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := by
    have a := val_corr hJ cα (𝟙 _)
    have b := val_corr hJ cα' (𝟙 _)
    have p₁ : val (powFrame A.A A.L x e ((N : ℤ) ^ 2)) (𝟙 _) z J = val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    have p₂ : val (powFrame A.A A.L x e' ((N : ℤ) ^ 2)) (𝟙 _) z J = val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_mul hJ, val_pull hJ] at a b
    rw [← p₁, ← p₂, a, b, hαα _ _ z J hJ]
  have q' := congrArg Units.val q
  rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
    Units.val_pow_eq_pow_val, hl z J hJ, mul_pow] at q'
  have hu : IsUnit ((val e (𝟙 _) z J).val ^ (N ^ 2)) := (Units.isUnit _).pow _
  refine cstH_inj (R := V) z ((map_pow _ _ _).trans (Eq.trans ?_ (map_one _).symm))
  exact hu.mul_left_inj.1 (q'.symm.trans (_root_.one_mul _).symm)

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}
  {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
  {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
  {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}


attribute [local instance] GlobalTheory.TorusExt.gtGroup in
theorem shift (𝔪 : UMem X₁ z₁ act V ev X t δ) {x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)}
    {fr : ∀ a, FrAt (x a)} (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left)
    {ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))} (hρA : ρA.IsGen)
    (htors : ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a)) {w₀ : W0 𝔪.U.toUnifPre} (hw₀ : w₀.IsGen)
    {a τ : X₁.S.Gam} {χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ} (hχ : TorChar 𝔪 τ χ)
    {g₁ : GtPtF 𝔪.D.toPre (FractionRing V)} {w₁ : Frm 𝔪.D.toPre (FractionRing V) 1 g₁.b}
    (hc : (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₁ o ∧ o.IsZero) ∧ w₁.IsGen ∧ 𝔪.Over' w₀ g₁ w₁ (x a) (fr a)) :
    ∃ (u : FractionRing V) (g₂ : GtPtF 𝔪.D.toPre (FractionRing V)) (w₂ : Frm 𝔪.D.toPre (FractionRing V) 1 g₂.b),
      u ^ ((X₁.S.r * X₁.S.N) ^ 2) = 1 ∧
      ((∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) g₂ o ∧ o.IsZero) ∧ w₂.IsGen ∧ 𝔪.Over' w₀ g₂ w₂ (x (a + τ)) (fr (a + τ))) ∧
      g₂.b = g₁.b ∧ (∀ z J, Good 𝔪.D.toPre.P.L z J → (val w₂ (𝟙 _) z J).val = cstH z u⁻¹ * (val w₁ (𝟙 _) z J).val) ∧
      ∀ (s : Fam 𝔪.D.toPre (FractionRing V) 1) (β : 𝔪.D.toPre.X), coef s g₂ w₂ β =
        u⁻¹ * ((χ (Multiplicative.ofAdd β) : (FractionRing V)ˣ) : FractionRing V) * coef s g₁ w₁ β := by
  obtain ⟨hχ, hyp⟩ := hχ
  have hg₀ : IsTor χ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) :=
    (isTor_iff _ _).2 (GlobalTheory.TorusExt.isTorusPtF_torusPt χ)
  obtain ⟨p, xτ, hpy, hpg, hq, hxτ⟩ := hyp _ hg₀
  have hadd := (GlobalTheory.TorusExt.isAdd_iff_eq g₁ (GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)) _).2 rfl
  have hb := (GlobalTheory.UT.ThetaAverage.val_translate hg₀ hadd).1
  obtain ⟨w'', hw''g, hw''v⟩ : ∃ w'' : Frm 𝔪.D.toPre (FractionRing V) 1
      (g₁ + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b,
      w''.IsGen ∧ ∀ z J, val w'' (𝟙 _) z J = val w₁ (𝟙 _) z J := by
    revert hb
    generalize (g₁ + GlobalTheory.TorusExt.torusPt 𝔪.D.toPre (FractionRing V) (Additive.ofMul χ)).b = b
    rintro rfl
    exact ⟨w₁, hc.2.1, fun _ _ => rfl⟩
  obtain ⟨e₂, he₂, hov⟩ := GlobalTheory.T.torusExtension_translate_liesOver_product_torsionFrame g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 w₀ hw₀ ρA hρA (x a) (fr a) (htors _)
    g₁ w₁ hc.1 hc.2.1 hc.2.2 χ hχ _ hg₀ p xτ hpy hpg hq _ hadd w'' (fun z J _ => hw''v z J)
    (x (a + τ)) (GlobalTheory.T.memberTorsionPoints_additive_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx a τ xτ hxτ)
  obtain ⟨u, hu, huv⟩ := exists_frAt_ratio he₂.2.1 (htors (a + τ)).2.1
  obtain ⟨w₃, hw₃, hw₃v⟩ := exists_frm_scale w'' hw''g (inv_ne_zero hu)
  have hv : ∀ z J, Good 𝔪.D.toPre.P.L z J → (val w₃ (𝟙 _) z J).val = cstH z u⁻¹ * (val w₁ (𝟙 _) z J).val :=
    fun z J hJ => by rw [hw₃v z J hJ, hw''v, cst_eq]
  refine ⟨u, _, w₃, ratio_pow he₂ (htors _) huv, ⟨⟨0, (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).2 ?_,
    (GlobalTheory.TorusExt.isZero_iff_eq _).2 rfl⟩, hw₃, over_scale 𝔪 hw''g hu huv hw₃v hov⟩, hb, hv,
    GlobalTheory.UT.ThetaAverage.coef_translate hg₀ hadd hc.2.1 hv⟩
  obtain ⟨o, ho, ho'⟩ := hc.1
  rw [smul_add, ← (GlobalTheory.TorusExt.isNsmul_iff_eq _ _ _).1 ho, (GlobalTheory.TorusExt.isZero_iff_eq _).1 ho', ← map_nsmul,
    ← ofMul_pow, hχ, ofMul_one, map_zero, add_zero]

theorem cube_alg {S : Type} [CommRing S] {A C D B₀ B₁ B₂ B₃ B₁₂ B₁₃ B₂₃ B₁₂₃ : Sˣ} {k v₀ v₁ v₂ v₁₂ : S}
    (E : A * (B₁₂₃ * B₁ * B₂ * B₃) * C = D * (B₁₂ * B₁₃ * B₂₃ * B₀)) (K : D.val = k * A.val)
    (h₀ : B₃.val = v₀ * B₀.val) (h₁ : B₁₃.val = v₁ * B₁.val) (h₂ : B₂₃.val = v₂ * B₂.val)
    (h₁₂ : B₁₂₃.val = v₁₂ * B₁₂.val) : v₁₂ * v₀ * C.val = k * v₁ * v₂ := by
  have E' := congrArg Units.val E
  simp only [Units.val_mul, K, h₀, h₁, h₂, h₁₂] at E'
  refine (A * B₀ * B₁ * B₂ * B₁₂).mul_right_inj.1 ?_
  simp only [Units.val_mul]
  linear_combination E'

theorem cube_rel (𝔪 : UMem X₁ z₁ act V ev X t δ) {κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R}
    {x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)}
    {fr : ∀ a, FrAt (x a)} (hx : ∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) (hfr : ∀ a, (fr a).IsGen)
    {ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))} {hρ : ρ.IsGen} (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩)
    (hκ : ∀ (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val)
    {w₀ : W0 𝔪.U.toUnifPre} (hw₀ : w₀.IsGen) {H : AddSubgroup X₁.S.Gam} {τ : X₁.S.Gam}
    {g₁ g₂ : H → GtPtF 𝔪.D.toPre (FractionRing V)} {w₁ : ∀ b, Frm 𝔪.D.toPre (FractionRing V) 1 (g₁ b).b}
    {w₂ : ∀ b, Frm 𝔪.D.toPre (FractionRing V) 1 (g₂ b).b} {v : H → FractionRing V}
    (h₁ : ∀ b, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g₁ b) o ∧ o.IsZero) ∧ (w₁ b).IsGen ∧
      𝔪.Over' w₀ (g₁ b) (w₁ b) (x b) (fr b))
    (h₂ : ∀ b, (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) (g₂ b) o ∧ o.IsZero) ∧ (w₂ b).IsGen ∧
      𝔪.Over' w₀ (g₂ b) (w₂ b) (x (b + τ)) (fr (b + τ)))
    (hb : ∀ b, (g₂ b).b = (g₁ b).b)
    (hv : ∀ b z J, Good 𝔪.D.toPre.P.L z J → (val (w₂ b) (𝟙 _) z J).val = cstH z (v b) * (val (w₁ b) (𝟙 _) z J).val)
    (a a' : H) (z : (TF (R := V) (FractionRing V)).left) {JB} (hJB : Good 𝔪.D.toPre.P.L z JB) :
    cstH z (v (a + a') * v 0) * (cubV 𝔪.D.toPre.cub z JB (g₁ a).b (g₁ a').b (g₁ 0).b).val =
      cstH z (𝔪.yK (κ a a' τ) * v a * v a') := by
  have hadd : ∀ b b', x (b + b') = x b * x b' := fun b b' =>
    GlobalTheory.T.memberTorsionPoints_additive_label g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x hx b b' (x b') (hx b')
  have hx0 : x 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  have hk : 1 ≤ X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  obtain ⟨JA, hJA⟩ := exists_good' 𝔪.A.isLB z
  let P : (X₁.S.Gam × Σ g' : GtPtF 𝔪.D.toPre (FractionRing V), Frm 𝔪.D.toPre (FractionRing V) 1 g'.b) → Prop := fun q =>
    (∃ o, GtPtF.IsNsmul (X₁.S.r * X₁.S.N) q.2.1 o ∧ o.IsZero) ∧ q.2.2.IsGen ∧ (fr q.1).IsGen ∧
      LiesOver 𝔪.U.toUnifPre w₀ q.2.1 q.2.2 (x q.1) (fr q.1)
  have p₁ : ∀ b : H, P ⟨b, g₁ b, w₁ b⟩ := fun b => ⟨(h₁ b).1, (h₁ b).2.1, hfr _, (h₁ b).2.2⟩
  have p₂ : ∀ b : H, P ⟨b + τ, g₂ b, w₂ b⟩ := fun b => ⟨(h₂ b).1, (h₂ b).2.1, hfr _, (h₂ b).2.2⟩
  have p₃ : P ⟨τ, g₂ 0, w₂ 0⟩ := by
    have := p₂ 0
    rwa [AddSubgroup.coe_zero, zero_add] at this
  obtain ⟨f, hP, f₀, f₁, f₂, f₃, f₄, f₅, f₆, f₇⟩ : ∃ f : Finset (Fin 3) →
      (X₁.S.Gam × Σ g' : GtPtF 𝔪.D.toPre (FractionRing V), Frm 𝔪.D.toPre (FractionRing V) 1 g'.b), (∀ S, P (f S)) ∧
      f ∅ = ⟨0, g₁ 0, w₁ 0⟩ ∧ f {0} = ⟨a, g₁ a, w₁ a⟩ ∧ f {1} = ⟨a', g₁ a', w₁ a'⟩ ∧ f {2} = ⟨τ, g₂ 0, w₂ 0⟩ ∧
      f {0, 1} = ⟨a + a', g₁ (a + a'), w₁ (a + a')⟩ ∧ f {0, 2} = ⟨a + τ, g₂ a, w₂ a⟩ ∧
      f {1, 2} = ⟨a' + τ, g₂ a', w₂ a'⟩ ∧ f {0, 1, 2} = ⟨a + a' + τ, g₂ (a + a'), w₂ (a + a')⟩ := by
    refine ⟨fun S => if 2 ∈ S then
        (if 0 ∈ S then (if 1 ∈ S then ⟨a + a' + τ, g₂ (a + a'), w₂ (a + a')⟩ else ⟨a + τ, g₂ a, w₂ a⟩)
          else if 1 ∈ S then ⟨a' + τ, g₂ a', w₂ a'⟩ else ⟨τ, g₂ 0, w₂ 0⟩)
      else (if 0 ∈ S then (if 1 ∈ S then ⟨a + a', g₁ (a + a'), w₁ (a + a')⟩ else ⟨a, g₁ a, w₁ a⟩)
          else if 1 ∈ S then ⟨a', g₁ a', w₁ a'⟩ else ⟨0, g₁ 0, w₁ 0⟩), fun S => ?_, ?_⟩
    · dsimp only
      split_ifs
      exacts [p₂ (a + a'), p₂ a, p₂ a', p₃, p₁ (a + a'), p₁ a, p₁ a', p₁ 0]
    · simp
  have E := GlobalTheory.T.framed_torsion_torus_extension_respect_cubical V 𝔪.cn 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ _ hk ρ hρ c (fun S => (f S).2.1) (fun S => (f S).2.2)
    (fun S => x (f S).1) (fun S => fr (f S).1) (by simp only [f₀, hx0]) (by simp only [f₁, f₂, f₄, hadd])
    (by simp only [f₁, f₃, f₅, hadd]) (by simp only [f₂, f₃, f₆, hadd]) (by simp only [f₁, f₂, f₃, f₇, hadd]) hP
    z JA JB hJA hJB
  beta_reduce at E
  rw [f₀, f₁, f₂, f₃, f₄, f₅, f₆, f₇] at E
  dsimp only at E
  have := cube_alg E (hκ a a' τ z JA hJA) (hv 0 z JB hJB) (hv a z JB hJB) (hv a' z JB hJB) (hv (a + a') z JB hJB)
  rw [hb 0, cst_eq] at this
  rw [map_mul, map_mul, map_mul, this]

theorem one_member {κ : X₁.S.Gam → X₁.S.Gam → X₁.S.Gam → X₁.S.R} {x₀ : X₁.S.Gam} (hdiv : X₁.M.Div X₁.S.th x₀ z₁)
    (𝔪 : UMem X₁ z₁ act V ev X t δ)
    (hκ : ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∀ (ρ : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A))) (hρ : ρ.IsGen) (c : CubicalStr 𝔪.A.A ⟨𝔪.A.L, ρ, 𝔪.A.isLB, hρ⟩) (a a' a'' : X₁.S.Gam) (z : (TF (R := V) (FractionRing V)).left) (JA : ((TF (R := V) (FractionRing V)).left ⟶ 𝔪.A.A.left) → 𝔪.A.L.ι), Good 𝔪.A.L z JA → (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (cubV c (T := TFK (R := V) (FractionRing V)) z JA (x a) (x a') (x a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr 0) (𝟙 _) z JA))).val = GlobalTheory.UT.cst (FractionRing V) z (𝔪.yK (κ a a' a'')) * (@id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr (a + a' + a'')) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a) (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a') (𝟙 _) z JA) * @id ((TF (R := V) (FractionRing V)).left.presheaf.stalk z)ˣ (val (fr a'') (𝟙 _) z JA)).val)
    {τ : X₁.S.Gam} (hτ : τ ∈ X₁.S.TT X₁.M z₁) :
    ∃ e : X₁.S.HH X₁.M z₁ → ℕ, (∀ a : X₁.S.HH X₁.M z₁, TransExp 𝔪 x₀ a τ (e a)) ∧ ∀ a a' : X₁.S.HH X₁.M z₁,
      𝔪.yK (κ a a' 0 * algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ (e a + e a')) =
        𝔪.yK (κ a a' τ * algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ (e (a + a') + e 0)) := by
  obtain ⟨T₁, hT₀, -, -⟩ :=
    GlobalTheory.T.exists_member_terms_integral_unit_shift g n F W Z i X₁ z₁ act x₀ hdiv V ev X m t δ 𝔪 (X₁.S.HH X₁.M z₁) Subtype.val Subtype.range_coe
  generalize (fun mu c => T₁ mu c * mono W t δ mu) = T₀ at hT₀
  have hT₀' := hT₀
  obtain ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hTc⟩ := hT₀'
  obtain ⟨ρA, hρA, htors⟩ := GlobalTheory.T.exists_rigidification_matchingFrames_torsionFrames g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x fr hx hfr
  obtain ⟨χ₀, hχ₀⟩ : ∃ χ, TorChar 𝔪 τ χ := GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ hτ
  choose u g₂ w₂ hu h₂ hb hv hco using fun b : X₁.S.HH X₁.M z₁ => shift 𝔪 hx hρA htors hw₀ hχ₀ (hc b)
  choose e he using fun b => GlobalTheory.T.rootOfUnity_fractionField_member_eq_zeta_pow g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 (u b) (hu b)
  have hk : 0 < X₁.S.r * X₁.S.N := Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)
  have hu0 : ∀ b, u b ≠ 0 := fun b h => by
    have := hu b
    rw [h, zero_pow (by positivity)] at this
    exact zero_ne_one this
  obtain ⟨z⟩ : Nonempty (TF (R := V) (FractionRing V)).left := exists_pt (R := V) (F := FractionRing V)
  obtain ⟨J, hJ⟩ := exists_good' 𝔪.D.toPre.P.isLB z
  refine ⟨e, fun a χ hχ C lab T hT c hl C' lab' T' hT' c' hl' mu => ?_, fun a a' => ?_⟩
  · obtain ⟨u', g₃, w₃, hu', h₃, -, hv', hco'⟩ := shift 𝔪 hx hρA htors hw₀ hχ (hc a)
    have huu : u' = u a := by
      have q := (GlobalTheory.T.framedTorsionPoint_torusExtension_eq_of_liesOver V 𝔪.cn 𝔪.D 𝔪.A 𝔪.G 𝔪.semi 𝔪.U w₀ hw₀ _ hk g₃ (g₂ a) w₃ (w₂ a) _ _ h₃.1 (h₂ a).1 h₃.2.1
        (h₂ a).2.1 (hfr _).1 h₃.2.2 (h₂ a).2.2).2 z J hJ
      have q' := congrArg Units.val q
      rw [hv' z J hJ, hv a z J hJ] at q'
      exact inv_injective (cstH_inj z ((Units.mul_left_inj _).1 q'))
    subst huu
    haveI : IsIntegrallyClosed V := 𝔪.cn.2.1
    have hint : ∀ mu : Fin 8 → X, ∃ r : V, algebraMap V (FractionRing V) r =
        (u a)⁻¹ * ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) := fun mu => by
      refine IsIntegrallyClosed.isIntegral_iff.1 (IsIntegral.mul ?_ ?_)
      · refine IsIntegral.of_pow (n := (X₁.S.r * X₁.S.N) ^ 2) (by positivity) ?_
        rw [inv_pow, hu', inv_one]
        exact isIntegral_one
      · refine IsIntegral.of_pow hk ?_
        rw [← Units.val_pow_eq_pow_val, ← MonoidHom.pow_apply, hχ.1, MonoidHom.one_apply, Units.val_one]
        exact isIntegral_one
    choose r hr using hint
    have hT₂ : 𝔪.Terms x₀ (fun _ : Unit => a.1 + τ) fun mu _ => r mu * T₀ mu a :=
      ⟨x, fr, th, w₀, s, fun _ => g₃, fun _ => w₃, hx, hfr, hth, hw₀, hs, fun _ => h₃, fun mu _ => by
        rw [hco', map_mul, hr, ← hTc, _root_.mul_assoc]⟩
    have θ := GlobalTheory.T.uniformisedMember_dividingThetaConstant_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hdiv
    have a₁ := mul_right_cancel₀ θ
      (GlobalTheory.T.thetaFamily_terms_eq_up_to_normalising_thetaConst g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ x₀ _ _ _ _ _ _ hT hT₀ c a hl mu)
    have a₂ := mul_right_cancel₀ θ
      (GlobalTheory.T.thetaFamily_terms_eq_up_to_normalising_thetaConst g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ x₀ _ _ _ _ _ _ hT' hT₂ c' () hl' mu)
    rw [a₁, a₂, ← he, map_mul, hr, ← _root_.mul_assoc, mul_inv_cancel_left₀ (hu0 a)]
  · obtain ⟨c⟩ := (GlobalTheory.firstFiveLaws.1.cube _ 𝔪.A ⟨𝔪.A.L, ρA, 𝔪.A.isLB, hρA⟩ rfl).1
    have K := hκ x fr hx hfr ρA hρA c
    have E₁ := cube_rel 𝔪 hx (fun b => (hfr b).1) c K hw₀ hc h₂ hb hv a a' z hJ
    have E₀ := cube_rel 𝔪 hx (fun b => (hfr b).1) c K hw₀ (τ := 0) (v := fun _ => 1) hc
      (fun b => by rw [add_zero]; exact hc b) (fun _ => rfl) (fun b z J _ => by rw [map_one, _root_.one_mul]) a a' z hJ
    simp only [_root_.mul_one, map_one, _root_.one_mul] at E₀
    rw [E₀, ← map_mul] at E₁
    have E := cstH_inj z E₁
    have he' : ∀ b, 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ^ e b = u b := fun b => by rw [he, map_pow, map_pow]
    simp only [map_mul, pow_add, map_pow, he']
    have := hu0 a
    have := hu0 a'
    have := hu0 (a + a')
    have := hu0 0
    field_simp at E
    linear_combination E

theorem prim_ring : IsPrimitiveRoot (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ) ((X₁.S.r * X₁.S.N) ^ 2) := by
  refine X₁.S.prim.map_of_injective fun a b hab => X₁.ar.inj ?_
  simpa using congrArg (fun x : X₁.S.R => (x : X₁.Ω₁)) hab

theorem prim_member (𝔪 : UMem X₁ z₁ act V ev X t δ) :
    IsPrimitiveRoot (𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ)) ((X₁.S.r * X₁.S.N) ^ 2) := by
  haveI : CharZero V := 𝔪.cn.2.2.2
  haveI : CharZero (FractionRing V) := IsFractionRing.charZero V
  have hk : 0 < (X₁.S.r * X₁.S.N) ^ 2 := pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2
  have h := ((prim_ring (X₁ := X₁)).isRoot_cyclotomic hk).map (f := 𝔪.yK)
  rw [Polynomial.map_cyclotomic] at h
  haveI : NeZero ((((X₁.S.r * X₁.S.N) ^ 2 : ℕ)) : FractionRing V) := ⟨by exact_mod_cast hk.ne'⟩
  exact Polynomial.isRoot_cyclotomic_iff.1 h

theorem exp_eq (𝔪 : UMem X₁ z₁ act V ev X t δ) {p q : ℕ}
    (h : 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ p) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R X₁.S.ζ ^ q)) :
    (p : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = q := by
  have hk : 0 < (X₁.S.r * X₁.S.N) ^ 2 := pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2
  have hp := prim_member 𝔪
  rw [map_pow, map_pow, (isOfFinOrder_iff_pow_eq_one.2 ⟨_, hk, hp.pow_eq_one⟩).pow_eq_pow_iff_modEq, ← hp.eq_orderOf] at h
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h

theorem transExp_affine : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (m2 : ℕ) (t2 : Fin m2 → V2) (δ2 : Fin m2 → LinearMap.BilinForm ℤ Y2) (𝔪2 : UMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv V1 _ _ _ ev1 Y1 _ m1 t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ m2 t2 δ2 𝔪2 τ hτ
  classical
  obtain ⟨κ, hκ1, hκ⟩ := GlobalTheory.T.exists_theta_frame_cube_constant_root_of_unity g n F W Z i X₁ z₁ act
  obtain ⟨e₁, h₁, c₁⟩ := one_member hdiv 𝔪1 (hκ V1 ev1 Y1 m1 t1 δ1 𝔪1) hτ
  obtain ⟨e₂, h₂, c₂⟩ := one_member hdiv 𝔪2 (hκ V2 ev2 Y2 m2 t2 δ2 𝔪2) hτ
  haveI : NeZero ((X₁.S.r * X₁.S.N) ^ 2) :=
    ⟨(pow_pos (Nat.mul_pos X₁.S.r_pos (by have := X₁.S.N_ge; omega)) 2).ne'⟩
  let d : X₁.S.HH X₁.M z₁ → ZMod ((X₁.S.r * X₁.S.N) ^ 2) := fun a => (e₁ a : ZMod _) - (e₂ a : ZMod _)
  have hd : ∀ a a', d (a + a') - d 0 = d a - d 0 + (d a' - d 0) := fun a a' => by
    obtain ⟨k, -, hk⟩ := (prim_ring (X₁ := X₁)).eq_pow_of_pow_eq_one (hκ1 a a' 0)
    obtain ⟨k', -, hk'⟩ := (prim_ring (X₁ := X₁)).eq_pow_of_pow_eq_one (hκ1 a a' τ)
    have a₁ := c₁ a a'
    have a₂ := c₂ a a'
    rw [← hk, ← hk', ← pow_add, ← pow_add] at a₁ a₂
    have b₁ := exp_eq 𝔪1 a₁
    have b₂ := exp_eq 𝔪2 a₂
    push_cast at b₁ b₂
    simp only [d]
    linear_combination b₂ - b₁
  refine ⟨fun a => if h : a ∈ X₁.S.HH X₁.M z₁ then e₁ ⟨a, h⟩ else 0,
    fun a => if h : a ∈ X₁.S.HH X₁.M z₁ then e₂ ⟨a, h⟩ else 0, fun a ha => ?_, fun a ha => ?_, d 0,
    AddMonoidHom.mk' (fun a => d a - d 0) hd, fun a ha => ?_⟩
  · beta_reduce
    rw [dite_eq_left ha]
    exact h₁ ⟨a, ha⟩
  · beta_reduce
    rw [dite_eq_left ha]
    exact h₂ ⟨a, ha⟩
  · beta_reduce
    rw [dite_eq_left ha, dite_eq_left ha, AddMonoidHom.mk'_apply, add_sub_cancel]

end GlobalTheory.Poinc.Sep.TransAff
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTranslationExponentsAffine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep

theorem trans_exp_affine : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (m2 : ℕ) (t2 : Fin m2 → V2) (δ2 : Fin m2 → LinearMap.BilinForm ℤ Y2) (𝔪2 : UMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩) :=
  GlobalTheory.Poinc.Sep.TransAff.transExp_affine

end GlobalTheory.Poinc.Sep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSetupTranslationExponentsAffineStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSetup_translation_exponents_affine : (∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (m2 : ℕ) (t2 : Fin m2 → V2) (δ2 : Fin m2 → LinearMap.BilinForm ℤ Y2) (𝔪2 : UMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ F1 F2 : X₁.S.Gam → ℕ, (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪1 x₀ a τ (F1 a)) ∧ (∀ a ∈ X₁.S.HH X₁.M z₁, TransExp 𝔪2 x₀ a τ (F2 a)) ∧ ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((F1 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((F2 a : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩) := by
  first | exact @GlobalTheory.Poinc.Sep.trans_exp_affine | exact GlobalTheory.Poinc.Sep.trans_exp_affine | (intros; apply GlobalTheory.Poinc.Sep.trans_exp_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsAffineTwoMembers
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
namespace GlobalTheory.Poinc.Sep

theorem sumF_comp_equiv {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {K : Type} [Field K]
    [Algebra (FractionRing R) K] {Ix Jx : Type} {x : Ix → K} {s : K} (e : Jx ≃ Ix) (h : SumF I K x s) :
    SumF I K (fun j => x (e j)) s := by
  letI : Module R K := Module.compHom K (algebraMap R (FractionRing R))
  obtain ⟨N, hN, hs, hx, hlim⟩ := h
  refine ⟨N, hN, hs, fun j => hx _, fun k => ?_⟩
  classical
  obtain ⟨S, hS⟩ := hlim k
  refine ⟨S.map e.symm.toEmbedding, fun T hT => ?_⟩
  have hsub : S ⊆ T.map e.toEmbedding := by
    intro a ha
    have := hT (Finset.mem_map_of_mem e.symm.toEmbedding ha)
    exact Finset.mem_map.2 ⟨e.symm a, this, by simp⟩
  have := hS _ hsub
  rwa [Finset.sum_map] at this

theorem sum_terms : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V), 𝔪.Terms x₀ lab T → ∀ (c : C), SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) (𝔪.yK ⟨X₁.S.th (lab c), X₁.S.th_mem (lab c)⟩) := by
  intro g n F W Z i X₁ z₁ act x₀ _ V _ _ _ ev X _ m t δ 𝔪 C lab T hT c
  obtain ⟨x, fr, th, w₀, s, g', w, -, -, hth, -, hexp, hg', hTe⟩ := hT
  have hO := (hg' c).2.2 1 le_rfl (w c) (fun z J _ => (pow_one _).symm) (hg' c).2.1 th s _ hexp (hth (lab c))
  have := sumF_comp_equiv 𝔪.e₈.toEquiv hO
  convert this using 1
  funext mu
  exact hTe mu c

theorem twistSum_of_transExp {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}}
    {i : F.X ⟶ Z} {X₁ : Setup F W i} {z₁ : X₁.M.Z} {act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)}
    {x₀ : X₁.S.Gam} (hd : X₁.M.Div X₁.S.th x₀ z₁) (sg : ℤˣ)
    {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] {ev : X₁.M.Z.presheaf.stalk z₁ →+* V}
    {X : Type} [AddCommGroup X] {m : ℕ} {t : Fin m → V} {δ : Fin m → LinearMap.BilinForm ℤ X}
    (𝔪 : UMem X₁ z₁ act V ev X t δ)
    (hW : ∀ (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), TorChar 𝔪 τ χ →
      ∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) =
        𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))
    {C : Type} (lab : C → X₁.S.Gam) (hlab : ∀ c, lab c ∈ X₁.S.HH X₁.M z₁) (T : (Fin 8 → X) → C → V)
    (hT : 𝔪.Terms x₀ lab T) (c : C) (τ : X₁.S.Gam) (hτ : τ ∈ X₁.S.TT X₁.M z₁) (e : ℕ)
    (hE : TransExp 𝔪 x₀ (lab c) τ e) : TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  obtain ⟨χ, hχ1, hχ2⟩ := GlobalTheory.T.exists_torusTorsionPoint_of_label_orthogonal g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 τ hτ
  obtain ⟨T', hT'⟩ := GlobalTheory.T.exists_thetaTerms_torusTranslate g n F W Z i X₁ z₁ act x₀ hd V ev X m t δ 𝔪 C lab hlab T hT c τ hτ
  have hprop := hE χ ⟨hχ1, hχ2⟩ C lab T hT c rfl Unit _ T' hT' () rfl
  have hsum := sumF_const_mul (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)))
    (sum_terms g n F W Z i X₁ z₁ act x₀ hd V ev X m t δ 𝔪 Unit (fun _ => lab c + τ) T' hT' ())
  refine GlobalTheory.Poinc.TwistSum₂.twistSum_of_sumF g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ C lab T sg c τ χ e
    (UMem.yK_th_ne_zero g n F W Z i X₁ z₁ act V ev X m t δ 𝔪 x₀ hd)
    (UMem.exists_yy g n F W Z i X₁ z₁ act V ev X m t δ 𝔪) (hW τ χ ⟨hχ1, hχ2⟩) ?_
  convert hsum using 1
  funext mu
  rw [← _root_.mul_assoc, hprop mu, _root_.mul_assoc]

theorem twistSum_exp_affine : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (m2 : ℕ) (t2 : Fin m2 → V2) (δ2 : Fin m2 → LinearMap.BilinForm ℤ Y2) (𝔪2 : UMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y2) → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  intro g n F W Z i X₁ z₁ act x₀ hd sg _ hW V1 _ _ _ ev1 Y1 _ m1 t1 δ1 𝔪1 V2 _ _ _ ev2 Y2 _ m2 t2 δ2 𝔪2
  classical
  have hA := GlobalTheory.T.thetaSetup_translation_exponents_affine g n F W Z i X₁ z₁ act x₀ hd V1 ev1 Y1 m1 t1 δ1 𝔪1 V2 ev2 Y2 m2 t2 δ2 𝔪2
  choose! F1 F2 hF1 hF2 hAff using hA
  refine ⟨fun a τ => F1 τ a, fun a τ => F2 τ a, ?_, ?_, fun τ hτ => hAff τ hτ⟩
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪1 (fun τ χ hχ => hW V1 ev1 Y1 m1 t1 δ1 𝔪1 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF1 τ hτ (lab c) (hlab c))
  · intro C lab hlab T hT c τ hτ
    exact twistSum_of_transExp hd sg 𝔪2 (fun τ χ hχ => hW V2 ev2 Y2 m2 t2 δ2 𝔪2 τ χ hχ.1 hχ.2) lab hlab T hT c τ hτ _
      (hF2 τ hτ (lab c) (hlab c))

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSumExponentsAffineTwoMembersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedSum_exponents_affine_two_members : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (V2 : Type) [CommRing V2] [IsDomain V2] [IsLocalRing V2] (ev2 : X₁.M.Z.presheaf.stalk z₁ →+* V2) (Y2 : Type) [AddCommGroup Y2] (m2 : ℕ) (t2 : Fin m2 → V2) (δ2 : Fin m2 → LinearMap.BilinForm ℤ Y2) (𝔪2 : UMem X₁ z₁ act V2 ev2 Y2 t2 δ2), ∃ ε1 ε2 : X₁.S.Gam → X₁.S.Gam → ℕ, (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y1) → C → V1, 𝔪1.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, TwistSum X₁ z₁ act x₀ 𝔪1 lab T sg c τ (ε1 (lab c) τ)) ∧ (∀ (C : Type) (lab : C → X₁.S.Gam), (∀ c, lab c ∈ X₁.S.HH X₁.M z₁) → ∀ T : (Fin 8 → Y2) → C → V2, 𝔪2.Terms x₀ lab T → ∀ (c : C), ∀ τ ∈ X₁.S.TT X₁.M z₁, TwistSum X₁ z₁ act x₀ 𝔪2 lab T sg c τ (ε2 (lab c) τ)) ∧ ∀ τ ∈ X₁.S.TT X₁.M z₁, ∃ (κ : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) (h : X₁.S.HH X₁.M z₁ →+ ZMod ((X₁.S.r * X₁.S.N) ^ 2)), ∀ (a : X₁.S.Gam) (ha : a ∈ X₁.S.HH X₁.M z₁), ((ε1 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) - ((ε2 a τ : ℕ) : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = κ + h ⟨a, ha⟩ := by
  first | exact @GlobalTheory.Poinc.Sep.twistSum_exp_affine | exact GlobalTheory.Poinc.Sep.twistSum_exp_affine | (intros; apply GlobalTheory.Poinc.Sep.twistSum_exp_affine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermsDividingLabelGroupMember
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermsDividingLabelGroupMember
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem exists_terms_single : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ → ∃ T : (Fin 8 → Y1) → Unit → V1, 𝔪1.Terms x₀ (fun _ : Unit => a) T := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv V _ _ _ ev Y _ m t δ 𝔪 a ha
  obtain ⟨u, ⟨x, fr, th, w₀, s, g', w, hx, hfr, hth, hw₀, hs, hc, hT⟩, -, -⟩ :=
    GlobalTheory.T.exists_member_terms_integral_unit_shift g n F W Z i X₁ z₁ act x₀ hdiv V ev Y m t δ 𝔪 (X₁.S.HH X₁.M z₁) Subtype.val Subtype.range_coe
  exact ⟨fun mu _ => u mu ⟨a, ha⟩ * mono W t δ mu, x, fr, th, w₀, s, fun _ => g' ⟨a, ha⟩, fun _ => w ⟨a, ha⟩, hx, hfr, hth,
    hw₀, hs, fun _ => hc ⟨a, ha⟩, fun mu _ => hT mu ⟨a, ha⟩⟩

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTermsDividingLabelGroupMemberStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_terms_dividing_label_group_member : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ (V1 : Type) [CommRing V1] [IsDomain V1] [IsLocalRing V1] (ev1 : X₁.M.Z.presheaf.stalk z₁ →+* V1) (Y1 : Type) [AddCommGroup Y1] (m1 : ℕ) (t1 : Fin m1 → V1) (δ1 : Fin m1 → LinearMap.BilinForm ℤ Y1) (𝔪1 : UMem X₁ z₁ act V1 ev1 Y1 t1 δ1) (a : X₁.S.Gam), a ∈ X₁.S.HH X₁.M z₁ → ∃ T : (Fin 8 → Y1) → Unit → V1, 𝔪1.Terms x₀ (fun _ : Unit => a) T := by
  first | exact @GlobalTheory.Poinc.Sep.exists_terms_single | exact GlobalTheory.Poinc.Sep.exists_terms_single | (intros; apply GlobalTheory.Poinc.Sep.exists_terms_single <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaModelPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaModelPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

namespace GlobalTheory.Poinc.Sep.SupISymm

theorem exists_unit_of_pow_eq_one {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    {c ε : Ω} (hc : c ^ 2 = 1) (hε : ε ^ ((S.r * S.N) ^ 2) = 1) : ∃ u : oˣ, c * ε = algebraMap o Ω (u : o) := by
  have hinj : Function.Injective (algebraMap o Ω) := ArithBase.inj
  have hp : IsPrimitiveRoot (algebraMap o Ω S.ζ) ((S.r * S.N) ^ 2) := S.prim.map_of_injective hinj
  have hpos : 0 < (S.r * S.N) ^ 2 := by
    have := S.N_ge; have := S.r_pos; positivity
  obtain ⟨k, -, hk⟩ := hp.eq_pow_of_pow_eq_one hε
  have hζu : IsUnit S.ζ := S.prim.isUnit hpos.ne'
  have hc' : c = 1 ∨ c = -1 := by
    have : c * c = 1 := by rw [← sq]; exact hc
    exact mul_self_eq_one_iff.1 this
  rcases hc' with rfl | rfl
  · exact ⟨(hζu.unit) ^ k, by simp [← hk, map_pow]⟩
  · exact ⟨-(hζu.unit) ^ k, by simp [← hk, map_pow]⟩

theorem exists_unit_th_neg {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a) (a : S.Gam) :
    ∃ u : oˣ, S.th (-a) = algebraMap o Ω (u : o) * S.th a := by
  obtain ⟨c, ε, hc, hε, h⟩ := H a
  obtain ⟨u, hu⟩ := exists_unit_of_pow_eq_one S hc hε
  exact ⟨u, by rw [h, hu]⟩

theorem neg_mem_supI_of_parity {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω)
    (M : RatModel o Ω)
    (H : ∀ a : S.Gam, ∃ c ε : Ω, c ^ 2 = 1 ∧ ε ^ ((S.r * S.N) ^ 2) = 1 ∧ S.th (-a) = c * ε * S.th a)
    (z : M.Z) (a : S.Gam) (ha : a ∈ S.supI M z) : -a ∈ S.supI M z := _root_.GlobalTheory.GSep.SupISymm.neg_mem_supI_of_parity (o := o) (Ω := Ω) S M H z a ha

end GlobalTheory.Poinc.Sep.SupISymm


open GlobalTheory.Poinc.Sep.SupISymm in
theorem GlobalTheory.Poinc.Sep.neg_mem_supI : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ := by
  intro g n F W Z i X₁ z₁ a ha
  exact neg_mem_supI_of_parity X₁.S X₁.M (fun a => GlobalTheory.T.realisedThetaSystem_thetaConstant_neg_even_upToRoot X₁.o₁ X₁.Ω₁ X₁.S X₁.ρ a) z₁ a ha
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NegMemDividingLabelsThetaModelPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.neg_mem_dividing_labels_theta_model_point : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (a : X₁.S.Gam), a ∈ X₁.S.supI X₁.M z₁ → -a ∈ X₁.S.supI X₁.M z₁ := by
  first | exact @GlobalTheory.Poinc.Sep.neg_mem_supI | exact GlobalTheory.Poinc.Sep.neg_mem_supI | (intros; apply GlobalTheory.Poinc.Sep.neg_mem_supI <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndependentMember
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.Sep.TwistIndep

theorem isUnit_one_sub_pow {o : Type} [CommRing o] [IsDomain o] {ζ : o} {M : ℕ} (hζ : IsPrimitiveRoot ζ M)
    (hM : IsUnit (M : o)) {d : ℕ} (hd : ζ ^ d ≠ 1) : IsUnit (1 - ζ ^ d) := by
  have hη : (ζ ^ d) ^ M = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hsum : ∑ k ∈ Finset.range M, (ζ ^ d) ^ k = 0 := by
    have h := mul_geom_sum (ζ ^ d) M
    rw [hη, sub_self] at h
    exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hd)
  have hdiv : (1 - ζ ^ d) ∣ (M : o) := by
    have h : (M : o) = ∑ k ∈ Finset.range M, (1 - (ζ ^ d) ^ k) := by
      rw [Finset.sum_sub_distrib, hsum]; simp
    rw [h]
    exact Finset.dvd_sum fun k _ => by simpa using sub_dvd_pow_sub_pow (1 : o) (ζ ^ d) k
  exact isUnit_of_dvd_unit hdiv hM

theorem mem_maximalIdeal_of_map {R V : Type} [CommRing R] [IsLocalRing R] [CommRing V] [IsLocalRing V]
    (ev : R →+* V) {x : R} (h : ev x ∈ maximalIdeal V) : x ∈ maximalIdeal R := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at h ⊢
  exact fun hu => h (hu.map ev)

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem stalk_isUnit (X₁ : Setup F W i) (z₁ : X₁.M.Z) {s : X₁.M.Z.presheaf.stalk z₁} {x : X₁.o₁}
    (hs : X₁.M.stalkHom z₁ s = algebraMap X₁.o₁ X₁.Ω₁ x) (hx : IsUnit x) : IsUnit s := by
  obtain ⟨y, hy⟩ := hx.exists_right_inv
  obtain ⟨t, ht⟩ := exists_stalk_zeta X₁ z₁ y
  refine IsUnit.of_mul_eq_one t (X₁.M.stalkHom_injective z₁ ?_)
  rw [map_mul, hs, ht, ← map_mul, hy, map_one, map_one]

theorem pow_eq_of_sub_mem (X₁ : Setup F W i) (z₁ : X₁.M.Z) {s₁ s₂ : X₁.M.Z.presheaf.stalk z₁} {e₁ e₂ : ℕ}
    (h₁ : X₁.M.stalkHom z₁ s₁ = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e₁))
    (h₂ : X₁.M.stalkHom z₁ s₂ = algebraMap X₁.o₁ X₁.Ω₁ (X₁.S.ζ ^ e₂))
    (hm : s₁ - s₂ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁)) : X₁.S.ζ ^ e₁ = X₁.S.ζ ^ e₂ := by
  haveI : IsDomain X₁.o₁ := by haveI := X₁.ar.ded; infer_instance
  by_contra hne
  obtain ⟨M, hM⟩ : ∃ M, M = (X₁.S.r * X₁.S.N) ^ 2 := ⟨_, rfl⟩
  have hζ : IsPrimitiveRoot X₁.S.ζ M := hM ▸ X₁.S.prim
  have hM0 : M ≠ 0 := by
    rw [hM]; exact pow_ne_zero _ (Nat.mul_ne_zero (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega))
  have hMu : IsUnit (M : X₁.o₁) := by rw [hM, Nat.cast_pow]; exact X₁.S.unit.pow 2
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hM0
  have hd : X₁.S.ζ ^ e₂ * X₁.S.ζ ^ (e₁ + k * e₂) = X₁.S.ζ ^ e₁ := by
    have h1 : e₂ + (e₁ + k * e₂) = e₁ + M * e₂ := by rw [hk, Nat.succ_eq_add_one]; ring
    rw [← pow_add, h1, pow_add, pow_mul, hζ.pow_eq_one, one_pow, _root_.mul_one]
  have hd1 : X₁.S.ζ ^ (e₁ + k * e₂) ≠ 1 := fun h => hne (by rw [← hd, h, _root_.mul_one])
  have hu : IsUnit (X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂) := by
    have h3 : X₁.S.ζ ^ e₁ - X₁.S.ζ ^ e₂ = -(X₁.S.ζ ^ e₂ * (1 - X₁.S.ζ ^ (e₁ + k * e₂))) := by
      rw [← hd]; ring
    rw [h3]
    exact ((((hζ.isUnit hM0).pow e₂).mul (isUnit_one_sub_pow hζ hMu hd1))).neg
  have hs : IsUnit (s₁ - s₂) := stalk_isUnit X₁ z₁ (by rw [map_sub, h₁, h₂, map_sub]) hu
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hm
  exact hm hs

theorem pow_eq_iff_cast (X₁ : Setup F W i) (a b : ℕ) :
    X₁.S.ζ ^ a = X₁.S.ζ ^ b ↔ (a : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) = (b : ZMod ((X₁.S.r * X₁.S.N) ^ 2)) := by
  have hpos : 0 < (X₁.S.r * X₁.S.N) ^ 2 :=
    pow_pos (Nat.mul_pos (by have := X₁.S.r_pos; omega) (by have := X₁.S.N_ge; omega)) 2
  have hord := X₁.S.prim.eq_orderOf
  rw [ZMod.natCast_eq_natCast_iff']
  constructor
  · intro h
    apply X₁.S.prim.pow_inj (Nat.mod_lt _ hpos) (Nat.mod_lt _ hpos)
    rw [hord, pow_mod_orderOf, pow_mod_orderOf]
    exact h
  · intro h
    calc X₁.S.ζ ^ a = X₁.S.ζ ^ (a % orderOf X₁.S.ζ) := (pow_mod_orderOf _ _).symm
      _ = X₁.S.ζ ^ (b % orderOf X₁.S.ζ) := by rw [← hord, h]
      _ = X₁.S.ζ ^ b := pow_mod_orderOf _ _

theorem affine_zero {G : Type} [AddCommGroup G] {M : ℕ} (hM : Odd M) (S : Set G) (hS : ∀ s ∈ S, -s ∈ S)
    (hne : S.Nonempty) (κ : ZMod M) (h : AddSubgroup.closure S →+ ZMod M)
    (hz : ∀ s (hs : s ∈ S), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0) :
    ∀ a (ha : a ∈ AddSubgroup.closure S), κ + h ⟨a, ha⟩ = 0 := by
  obtain ⟨s₀, hs₀⟩ := hne
  have h1 := hz s₀ hs₀
  have h2 := hz (-s₀) (hS s₀ hs₀)
  have hneg : (⟨-s₀, AddSubgroup.subset_closure (hS s₀ hs₀)⟩ : AddSubgroup.closure S) =
      -⟨s₀, AddSubgroup.subset_closure hs₀⟩ := rfl
  rw [hneg, map_neg] at h2
  have h2κ : (2 : ZMod M) * κ = 0 := by linear_combination h1 + h2
  have hcop : Nat.Coprime 2 M := (Nat.coprime_two_left).2 hM
  have hκ : κ = 0 := by
    have hu : IsUnit (2 : ZMod M) := by
      have := (ZMod.unitOfCoprime 2 hcop).isUnit
      rwa [ZMod.coe_unitOfCoprime, Nat.cast_ofNat] at this
    exact hu.mul_right_eq_zero.1 h2κ
  subst hκ
  intro a ha
  rw [zero_add]
  refine AddSubgroup.closure_induction (p := fun x hx => h ⟨x, hx⟩ = 0) (fun x hx => ?_) ?_
    (fun x y hx hy h1 h2 => ?_) (fun x hx h1 => ?_) ha
  · simpa using hz x hx
  · exact map_zero h
  · have : (⟨x + y, add_mem hx hy⟩ : AddSubgroup.closure S) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [this, map_add (f := _), h1, h2, add_zero]
  · have : (⟨-x, neg_mem hx⟩ : AddSubgroup.closure S) = -⟨x, hx⟩ := rfl
    rw [this, map_neg, h1, neg_zero]

end GlobalTheory.Poinc.Sep.TwistIndep

namespace GlobalTheory.Poinc.Sep
open GlobalTheory.Poinc.Sep.TwistIndep

theorem twistSum_indep : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ Y₁) (𝔪₁ : UMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : (Fin 8 → Y₁) → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ Y₂) (𝔪₂ : UMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : (Fin 8 → Y₂) → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  intro g n F W Z i X₁ z₁ act x₀ hdiv sg hsg hpin V₁ _ _ _ ev₁ Y₁ _ m₁ t₁ δ₁ 𝔪₁ C₁ lab₁ hlab₁ T₁ hT₁ c₁
    V₂ _ _ _ ev₂ Y₂ _ m₂ t₂ δ₂ 𝔪₂ C₂ lab₂ hlab₂ T₂ hT₂ c₂ hlab τ hτ e₁ e₂ hS₁ _ hr'
  obtain ⟨r, hr, hr0⟩ := hr'
  obtain ⟨ε₁, ε₂, h1, h2, haff⟩ := GlobalTheory.T.twistedSum_exponents_affine_two_members g n F W Z i X₁ z₁ act x₀ hdiv sg hsg hpin V₁ ev₁ Y₁ m₁ t₁ δ₁ 𝔪₁ V₂ ev₂ Y₂ m₂ t₂ δ₂ 𝔪₂

  have hφ : ∀ b ∈ X₁.S.HH X₁.M z₁, X₁.S.ζ ^ ε₁ b τ = X₁.S.ζ ^ ε₂ b τ := by
    obtain ⟨κ, h, hκ⟩ := haff τ hτ
    have hsup : ∀ s (hs : s ∈ X₁.S.supI X₁.M z₁), κ + h ⟨s, AddSubgroup.subset_closure hs⟩ = 0 := by
      intro s hs
      have hsH : s ∈ X₁.S.HH X₁.M z₁ := AddSubgroup.subset_closure hs
      obtain ⟨U₁, hU₁⟩ := GlobalTheory.T.exists_terms_dividing_label_group_member g n F W Z i X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ m₁ t₁ δ₁ 𝔪₁ s hsH
      obtain ⟨U₂, hU₂⟩ := GlobalTheory.T.exists_terms_dividing_label_group_member g n F W Z i X₁ z₁ act x₀ hdiv V₂ ev₂ Y₂ m₂ t₂ δ₂ 𝔪₂ s hsH
      have hw₁ := h1 Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ () τ hτ
      have hw₂ := h2 Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ () τ hτ
      obtain ⟨q₁, hq₁⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ ε₁ s τ)
      obtain ⟨q₂, hq₂⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ ε₂ s τ)
      obtain ⟨u, hu⟩ := (X₁.M.stalkEquiv z₁).surjective ⟨_, hs.2 (s + τ)⟩
      have hu' : X₁.M.stalkHom z₁ u = X₁.S.th (s + τ) / X₁.S.th s := by rw [← RatModel.coe_stalkEquiv, hu]
      have r₁ := GlobalTheory.T.twistedThetaSum_zeta_power_residue_dividing_label g n F W Z i X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ m₁ t₁ δ₁ 𝔪₁ Unit (fun _ => s) (fun _ => hsH) U₁ hU₁ ()
        hs τ hτ sg _ hw₁ q₁ u hq₁ hu'
      have r₂ := GlobalTheory.T.twistedThetaSum_zeta_power_residue_dividing_label g n F W Z i X₁ z₁ act x₀ hdiv V₂ ev₂ Y₂ m₂ t₂ δ₂ 𝔪₂ Unit (fun _ => s) (fun _ => hsH) U₂ hU₂ ()
        hs τ hτ sg _ hw₂ q₂ u hq₂ hu'
      have m₁' : q₁ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
        mem_maximalIdeal_of_map ev₁ (by rwa [map_sub, map_one])
      have m₂' : q₂ * u - 1 ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
        mem_maximalIdeal_of_map ev₂ (by rwa [map_sub, map_one])
      have hunit : IsUnit u := by
        have hqu : IsUnit (q₁ * u) := by
          by_contra hn
          have hmem : q₁ * u ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := (IsLocalRing.mem_maximalIdeal _).2 hn
          have h1m : (1 : X₁.M.Z.presheaf.stalk z₁) ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
            simpa using sub_mem hmem m₁'
          exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top ((Ideal.eq_top_iff_one _).2 h1m)
        exact isUnit_of_mul_isUnit_right hqu
      have hdiff : (q₁ - q₂) * u ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
        have h3 := sub_mem m₁' m₂'
        rwa [show q₁ * u - 1 - (q₂ * u - 1) = (q₁ - q₂) * u by ring] at h3
      have hq : q₁ - q₂ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) := by
        obtain ⟨v, hv⟩ := hunit.exists_right_inv
        have h4 := Ideal.mul_mem_right v _ hdiff
        rwa [_root_.mul_assoc, hv, _root_.mul_one] at h4
      have heq := (pow_eq_iff_cast X₁ _ _).1 (pow_eq_of_sub_mem X₁ z₁ hq₁ hq₂ hq)
      rw [← hκ s hsH, heq, sub_self]
    have hodd : Odd ((X₁.S.r * X₁.S.N) ^ 2) := by
      have h5 : Odd (X₁.S.r * X₁.S.N) := by
        obtain ⟨j, -, hj⟩ := X₁.ρ.r_eq
        rw [hj, X₁.ρ.N_eq]
        exact X₁.ρ.n_odd.pow.mul X₁.ρ.n_odd.pow.pow
      exact h5.pow
    have hz := affine_zero hodd (X₁.S.supI X₁.M z₁) (GlobalTheory.T.neg_mem_dividing_labels_theta_model_point g n F W Z i X₁ z₁) ⟨x₀, hdiv⟩ κ h hsup
    intro b hb
    rw [pow_eq_iff_cast, ← sub_eq_zero, hκ b hb]
    exact hz b hb

  obtain ⟨zt, hzt⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))
  obtain ⟨wt, hwt⟩ := GlobalTheory.T.twistWeight_wellDefined_on_lattice_class g n F W Z i X₁ z₁ act x₀ hdiv V₁ ev₁ Y₁ m₁ t₁ δ₁ 𝔪₁ sg τ hτ
  obtain ⟨s₁, hs₁⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ e₁)
  obtain ⟨s₀, hs₀⟩ := exists_stalk_zeta X₁ z₁ (X₁.S.ζ ^ ε₁ (lab₁ c₁) τ)
  have hA := hS₁ zt (s₁ * r) hzt (by rw [map_mul, hs₁, hr, mul_div_assoc]) wt hwt
  have hB := h1 C₁ lab₁ hlab₁ T₁ hT₁ c₁ τ hτ zt (s₀ * r) hzt (by rw [map_mul, hs₀, hr, mul_div_assoc]) wt hwt
  haveI : IsNoetherianRing V₁ := 𝔪₁.cn.1
  have unique_sum {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
      {E Ix : Type} [AddCommGroup E] [Module R E] (hI : I ≤ Ideal.jacobson ⊥)
      {x : Ix → E} {s s' : E} (h : SumI I x s) (h' : SumI I x s') : s = s' := by
    classical
    obtain ⟨N, hN, hs, -, hconv⟩ := h

    obtain ⟨N', hN', hs', -, hconv'⟩ := h'
    set M := N ⊔ N' with hM
    have hMfg : M.FG := hN.sup hN'
    haveI : Module.Finite R M := Module.Finite.iff_fg.mpr hMfg
    have hmem : s - s' ∈ M := M.sub_mem (Submodule.mem_sup_left hs) (Submodule.mem_sup_right hs')
    have hpow : ∀ n : ℕ, (⟨s - s', hmem⟩ : M) ∈ I ^ n • (⊤ : Submodule R M) := by
      intro n
      obtain ⟨S, hS⟩ := hconv n
      obtain ⟨S', hS'⟩ := hconv' n
      have h1 := hS (S ∪ S') Finset.subset_union_left
      have h2 := hS' (S ∪ S') Finset.subset_union_right
      have h3 : s - s' ∈ I ^ n • M := by
        have e : s - s' = (s - ∑ i ∈ S ∪ S', x i) - (s' - ∑ i ∈ S ∪ S', x i) := by abel
        rw [e]
        exact Submodule.sub_mem _ (Submodule.smul_mono le_rfl le_sup_left h1)
          (Submodule.smul_mono le_rfl le_sup_right h2)
      rw [← Submodule.map_subtype_top M, ← Submodule.map_smul''] at h3
      obtain ⟨y, hy, hyeq⟩ := h3
      have hy' : y = ⟨s - s', hmem⟩ := Subtype.ext hyeq
      rwa [← hy']
    have h0 : (⟨s - s', hmem⟩ : M) = 0 := by
      rw [Ideal.jacobson_bot] at hI
      have hK := Ideal.iInf_pow_smul_eq_bot_of_le_jacobson (M := M) I hI
      rw [← Submodule.mem_bot R, ← hK, Submodule.mem_iInf]
      exact hpow
    exact sub_eq_zero.mp (congrArg Subtype.val h0)
  have hE := unique_sum (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge hA hB
  rw [map_mul, map_mul] at hE
  have hE' : ev₁ s₁ = ev₁ s₀ := mul_right_cancel₀ hr0 hE
  have hm : s₁ - s₀ ∈ maximalIdeal (X₁.M.Z.presheaf.stalk z₁) :=
    mem_maximalIdeal_of_map ev₁ (by rw [map_sub, hE', sub_self]; exact zero_mem _)
  have hpe : X₁.S.ζ ^ e₁ = X₁.S.ζ ^ ε₁ (lab₁ c₁) τ := pow_eq_of_sub_mem X₁ z₁ hs₁ hs₀ hm

  have hpe2 : X₁.S.ζ ^ ε₂ (lab₂ c₂) τ = X₁.S.ζ ^ e₁ := by
    rw [hpe, ← hlab]
    exact (hφ _ (hlab₁ c₁)).symm
  have hF := h2 C₂ lab₂ hlab₂ T₂ hT₂ c₂ τ hτ
  intro zt' h' hzt' hh' wt' hwt'
  exact hF zt' h' hzt' (by rw [hpe2]; exact hh') wt' hwt'

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedThetaSumZetaExponentIndependentMemberStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedThetaSum_zeta_exponent_independent_member : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (x₀ : X₁.S.Gam), X₁.M.Div X₁.S.th x₀ z₁ → ∀ sg : ℤˣ, TwistAtEach X₁ z₁ act x₀ sg → (∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ), χ ^ (X₁.S.r * X₁.S.N) = 1 → (∀ g₀ : GtPtF 𝔪.D.toPre (FractionRing V), IsTor χ g₀ → ∃ (p : QkPt 𝔪.D.toPre (FractionRing V) (X₁.S.r * X₁.S.N)) (x : TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A), p.y = 0 ∧ p.g = g₀ ∧ QkToAkU 𝔪.U.toUnifPre (FractionRing V) (X₁.S.r * X₁.S.N) p x ∧ x.left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt τ).left) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val))))) → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (ev₁ : X₁.M.Z.presheaf.stalk z₁ →+* V₁) (Y₁ : Type) [AddCommGroup Y₁] (m₁ : ℕ) (t₁ : Fin m₁ → V₁) (δ₁ : Fin m₁ → LinearMap.BilinForm ℤ Y₁) (𝔪₁ : UMem X₁ z₁ act V₁ ev₁ Y₁ t₁ δ₁) (C₁ : Type) (lab₁ : C₁ → X₁.S.Gam), (∀ c, lab₁ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₁ : (Fin 8 → Y₁) → C₁ → V₁, 𝔪₁.Terms x₀ lab₁ T₁ → ∀ c₁ : C₁, ∀ (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (ev₂ : X₁.M.Z.presheaf.stalk z₁ →+* V₂) (Y₂ : Type) [AddCommGroup Y₂] (m₂ : ℕ) (t₂ : Fin m₂ → V₂) (δ₂ : Fin m₂ → LinearMap.BilinForm ℤ Y₂) (𝔪₂ : UMem X₁ z₁ act V₂ ev₂ Y₂ t₂ δ₂) (C₂ : Type) (lab₂ : C₂ → X₁.S.Gam), (∀ c, lab₂ c ∈ X₁.S.HH X₁.M z₁) → ∀ T₂ : (Fin 8 → Y₂) → C₂ → V₂, 𝔪₂.Terms x₀ lab₂ T₂ → ∀ c₂ : C₂, lab₁ c₁ = lab₂ c₂ → ∀ τ ∈ X₁.S.TT X₁.M z₁, ∀ e₁ e₂ : ℕ, TwistSum X₁ z₁ act x₀ 𝔪₁ lab₁ T₁ sg c₁ τ e₁ → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₂ → (∃ r : X₁.M.Z.presheaf.stalk z₁, X₁.M.stalkHom z₁ r = X₁.S.th (lab₁ c₁ + τ) / X₁.S.th x₀ ∧ ev₁ r ≠ 0) → TwistSum X₁ z₁ act x₀ 𝔪₂ lab₂ T₂ sg c₂ τ e₁ := by
  first | exact @GlobalTheory.Poinc.Sep.twistSum_indep | exact GlobalTheory.Poinc.Sep.twistSum_indep | (intros; apply GlobalTheory.Poinc.Sep.twistSum_indep <;> assumption)
end
