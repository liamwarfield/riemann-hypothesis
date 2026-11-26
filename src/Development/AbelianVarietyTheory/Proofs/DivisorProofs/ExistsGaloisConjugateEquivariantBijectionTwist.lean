module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChart

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenCastIsGen
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Conj

variable {R : Type} [CommRing R] [IsDomain R]

theorem spMap_jFK (σ : Kb R →ₐ[FractionRing R] Kb R) :
    spMap σ.toRingHom ≫ jFK (R := R) (Kb R) = jFK (R := R) (Kb R) := by
  rw [spMap, jFK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  exact σ.comp_algebraMap

def twK (σ : Kb R →ₐ[FractionRing R] Kb R) : TFK (R := R) (Kb R) ⟶ TFK (R := R) (Kb R) :=
  Over.homMk (spMap σ.toRingHom) (spMap_jFK σ)

@[simp] theorem twK_left (σ : Kb R →ₐ[FractionRing R] Kb R) : (twK σ).left = spMap σ.toRingHom := rfl

def mTw (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    TFK (R := R) (Kb R) ⊗ A.A ⟶ TFK (R := R) (Kb R) ⊗ A.A :=
  lift (fst _ _ ≫ twK σ) (snd _ _)

theorem mTw_fst (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    mTw A σ ≫ fst _ _ = fst _ _ ≫ twK σ := lift_fst _ _

theorem mTw_snd (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    mTw A σ ≫ snd _ _ = snd _ _ := lift_snd _ _

theorem mTw_fst_left (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    (mTw A σ).left ≫ (fst (TFK (R := R) (Kb R)) A.A).left =
      (fst (TFK (R := R) (Kb R)) A.A).left ≫ Spec.map (CommRingCat.ofHom σ.toRingHom) := by
  rw [← Over.comp_left, mTw_fst, Over.comp_left]; rfl

theorem mTw_snd_left (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    (mTw A σ).left ≫ (snd (TFK (R := R) (Kb R)) A.A).left = (snd (TFK (R := R) (Kb R)) A.A).left := by
  rw [← Over.comp_left, mTw_snd]

def secTw (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N :=
  GlobalTheory.FieldBaseChange.pullOver (π := (fst (TFK (R := R) (Kb R)) A.A).left) (π' := (fst (TFK (R := R) (Kb R)) A.A).left)
    A.L (fun _ : Fin 1 => (N : ℤ)) (mTw_fst_left A σ) (fun _ => (mTw_snd_left A σ).symm) t

def TwF (σ : Kb R →ₐ[FractionRing R] Kb R) : Type := Kb R

instance (σ : Kb R →ₐ[FractionRing R] Kb R) : Field (TwF σ) := inferInstanceAs (Field (Kb R))
instance (σ : Kb R →ₐ[FractionRing R] Kb R) : Algebra (FractionRing R) (TwF σ) :=
  inferInstanceAs (Algebra (FractionRing R) (Kb R))
instance (σ : Kb R →ₐ[FractionRing R] Kb R) : Algebra (Kb R) (TwF σ) := σ.toRingHom.toAlgebra
instance (σ : Kb R →ₐ[FractionRing R] Kb R) : IsScalarTower (FractionRing R) (Kb R) (TwF σ) :=
  IsScalarTower.of_algebraMap_eq fun r => (σ.commutes r).symm

def famTw (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s : Fam D (Kb R) N) : Fam D (Kb R) N :=
  (GlobalTheory.FieldBaseChange.famPull D (Kb R) (TwF σ) GlobalTheory.allSixLaws.1.globalFns N s : Fam D (TwF σ) N)

def genCast {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ} (h : φ = φ')
    (t : LB.Gen (LB.LinComb L φ ε)) : LB.Gen (LB.LinComb L φ' ε) :=
  h ▸ t

theorem genCast_isGen {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') {t : LB.Gen (LB.LinComb L φ ε)} (ht : t.IsGen) : (genCast h t).IsGen := by
  subst h; exact ht

theorem val_genCast {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ φ' : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : φ = φ') (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    val (genCast h t) r z J = val t r z J := by
  subst h; rfl

theorem thetaφ_mTw (A : PolAV (Sp (FractionRing R))) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (x : TFK (R := R) (Kb R) ⟶ A.A) :
    (fun i => (mTw A σ).left ≫ (![(snd (TFK (R := R) (Kb R)) A.A).left, (translPt A.A x).left] : Fin 2 → _) i) =
      ![(snd (TFK (R := R) (Kb R)) A.A).left, (translPt A.A (twK σ ≫ x)).left] := by
  funext i
  fin_cases i
  · exact mTw_snd_left A σ
  · show (mTw A σ).left ≫ (translPt A.A x).left = (translPt A.A (twK σ ≫ x)).left
    rw [← Over.comp_left, translPt, translPt, ← Category.assoc, comp_lift, ← Category.assoc, mTw_fst, mTw_snd,
      Category.assoc]

def thTw (A : PolAV (Sp (FractionRing R))) (k : ℤ) (σ : Kb R →ₐ[FractionRing R] Kb R)
    (θ : ThetaGrp A.A A.L k (TFK (R := R) (Kb R))) : ThetaGrp A.A A.L k (TFK (R := R) (Kb R)) where
  pt := twK σ ≫ θ.pt
  φ := genCast (thetaφ_mTw A σ θ.pt) (LB.pullGen A.L _ _ θ.φ (mTw A σ).left)
  isGen := genCast_isGen _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen A.L _ _ θ.φ θ.isGen _)

theorem spMap_jFKR (σ : Kb R →ₐ[FractionRing R] Kb R) :
    spMap σ.toRingHom ≫ (jFK (R := R) (Kb R) ≫ jK R) = jFK (R := R) (Kb R) ≫ jK R := by
  rw [← Category.assoc, spMap_jFK]

def twF (σ : Kb R →ₐ[FractionRing R] Kb R) : TF (R := R) (Kb R) ⟶ TF (R := R) (Kb R) :=
  Over.homMk (spMap σ.toRingHom) (spMap_jFKR σ)

theorem lineφ_tw (D : DegPre R) {N : ℕ} (τ : Kb R →ₐ[FractionRing R] Kb R) {p p₀ : QkPt D (Kb R) N}
    (h : QkExt τ.toRingHom p p₀) :
    (fun k => spMap τ.toRingHom ≫ DegPre.lineφ D (Kb R) p.g.b k) = DegPre.lineφ D (Kb R) p₀.g.b := by
  funext k
  fin_cases k
  · show (twF τ).left ≫ (toUnit _ ≫ η[D.P.A]).left = (toUnit _ ≫ η[D.P.A]).left
    rw [← Over.comp_left, ← Category.assoc, comp_toUnit]
  · exact h.2.1.symm

def frTw (D : DegPre R) {N : ℕ} (τ : Kb R →ₐ[FractionRing R] Kb R) {p p₀ : QkPt D (Kb R) N}
    (h : QkExt τ.toRingHom p p₀) (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) : GlobalTheory.UT.Frm D (Kb R) N p₀.g.b :=
  genCast (lineφ_tw D τ h) (LB.pullGen D.P.L _ _ w (spMap τ.toRingHom))

end GlobalTheory.Mum.Conj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistBijective
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Mum.Conj.FamBij

open GlobalTheory.FieldBaseChange

variable {R : Type} [CommRing R] [IsDomain R]

def famMapTw (D : DegPre R) (σ : Kb R →ₐ[FractionRing R] Kb R) : DegPre.BF D (Kb R) ⟶ DegPre.BF D (Kb R) :=
  (famMap D (Kb R) (TwF σ) : DegPre.BF D (TwF σ) ⟶ DegPre.BF D (Kb R))

theorem famMapTw_eq (D : DegPre R) (σ : Kb R →ₐ[FractionRing R] Kb R) :
    famMapTw D σ = lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF σ) (snd (TF (R := R) (Kb R)) D.P.A) := rfl

theorem twF_comp_eq_id {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x) :
    twF τ ≫ twF σ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap τ.toRingHom ≫ spMap σ.toRingHom = 𝟙 _
  have e : τ.toRingHom.comp σ.toRingHom = RingHom.id _ := RingHom.ext h
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e, CommRingCat.ofHom_id, Spec.map_id]

theorem famMapTw_comp_eq_id (D : DegPre R) {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x) :
    famMapTw D τ ≫ famMapTw D σ = 𝟙 _ := by
  have : lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF τ) (snd (TF (R := R) (Kb R)) D.P.A) ≫
      lift (fst (TF (R := R) (Kb R)) D.P.A ≫ twF σ) (snd (TF (R := R) (Kb R)) D.P.A) = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, lift_fst, lift_fst_assoc, Category.assoc, twF_comp_eq_id h, Category.comp_id,
        Category.id_comp]
    · rw [Category.assoc, lift_snd, lift_snd, Category.id_comp]
  exact this

theorem sval_famTw (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s : Fam D (Kb R) N) (α : D.X)
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D (Kb R)).left) {z : Z} {J : (Z ⟶ D.P.A.left) → D.P.L.ι}
    (hJ : Good D.P.L z J) :
    sval ((famTw D N σ s).s α) r z J = sval (s.s α) (r ≫ (famMapTw D σ).left) z J :=
  sval_pullOver (isPullback_famMap D (Kb R) (TwF σ)).w (famφ_famMap D (Kb R) (TwF σ) α) (s.s α) r hJ

theorem famTw_famTw_eq (D : DegPre R) (N : ℕ) {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : ∀ x, τ (σ x) = x)
    (s : Fam D (Kb R) N) : famTw D N τ (famTw D N σ s) = s := by
  refine ReciprocityTheory.ChartRestriction.G.DVR.fam_ext fun α j => congrArg (fun q => LB.Sec.f q j) ?_
  refine sec_ext' D.P.isLB fun y J hJ => ?_
  rw [sval_famTw D N τ _ α _ hJ, sval_famTw D N σ _ α _ hJ, Category.assoc, ← Over.comp_left,
    famMapTw_comp_eq_id D h, Over.id_left, Category.comp_id]

theorem famTw_bijective (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) : Function.Bijective (famTw D N σ) := by
  let e : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  refine Function.bijective_iff_has_inverse.2 ⟨famTw D N (e.symm : Kb R →ₐ[FractionRing R] Kb R), ?_, ?_⟩
  · exact famTw_famTw_eq D N fun x => e.symm_apply_apply x
  · exact famTw_famTw_eq D N fun x => e.apply_symm_apply x

end GlobalTheory.Mum.Conj.FamBij
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistBijectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R), Function.Bijective (famTw D N σ) := by
  first | exact @GlobalTheory.Mum.Conj.FamBij.famTw_bijective | exact GlobalTheory.Mum.Conj.FamBij.famTw_bijective | (intros; apply GlobalTheory.Mum.Conj.FamBij.famTw_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorRelationPullbackGaloisAutomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorRelationPullbackGaloisAutomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj.PhiTw

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.Conj.FamBij

variable {R : Type} [CommRing R] [IsDomain R]

theorem famMapTw_trPt (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) {b b' : TF (R := R) (Kb R) ⟶ D.P.A}
    (hb : twF ρ ≫ b = b') : famMapTw D ρ ≫ DegPre.trPt D (Kb R) b = DegPre.trPt D (Kb R) b' ≫ famMapTw D ρ := by
  subst hb
  rw [famMapTw_eq]
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trPt]
  · simp [DegPre.trPt, padd, comp_lift_assoc]

theorem zF_famMapTw (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) :
    DegPre.zF D (Kb R) ≫ famMapTw D ρ = twF ρ ≫ DegPre.zF D (Kb R) := by
  rw [famMapTw_eq]
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.zF]
  · simp [DegPre.zF]

theorem famMapTw_famφ (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) (β : D.X) (i : Fin 4) :
    (famMapTw D ρ).left ≫ DegPre.famφ D (Kb R) β i = DegPre.famφ D (Kb R) β i :=
  (famφ_famMap D (Kb R) (TwF ρ) β i).symm

theorem famMapTw_phiφ (D : DegPre R) (ρ : Kb R →ₐ[FractionRing R] Kb R) {y y₀ : D.X} (α : D.X)
    {b b₀ : TF (R := R) (Kb R) ⟶ D.P.A} (hy : y₀ = y) (hb : twF ρ ≫ b₀ = b) :
    (fun k => (famMapTw D ρ).left ≫ DegPre.phiφ D (Kb R) y₀ α b₀ k) = DegPre.phiφ D (Kb R) y α b := by
  subst hy
  funext k
  rcases k with i | i
  · exact famMapTw_famφ D ρ _ i
  · show (famMapTw D ρ).left ≫ (DegPre.trPt D (Kb R) b₀).left ≫ DegPre.famφ D (Kb R) α i =
      (DegPre.trPt D (Kb R) b).left ≫ DegPre.famφ D (Kb R) α i
    rw [← Category.assoc, ← Over.comp_left, famMapTw_trPt D ρ hb, Over.comp_left, Category.assoc,
      famMapTw_famφ]

theorem twF_left (ρ : Kb R →ₐ[FractionRing R] Kb R) : (twF ρ).left = spMap ρ.toRingHom := rfl

end GlobalTheory.Mum.Conj.PhiTw

namespace GlobalTheory.Mum.Conj.PhiTw

open GlobalTheory.FieldBaseChange GlobalTheory.Mum.Conj.FamBij

theorem phiRel_famTw : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀)
    (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) (s s' : Fam D (Kb R) N),
    PhiRel D (Kb R) N p w s s' → PhiRel D (Kb R) N p₀ (frTw D τ h w) (famTw D N τ s) (famTw D N τ s') := by
  intro R _ _ D N τ p p₀ h w s s' H α u hu hu0
  have hL := D.P.isLB
  let e : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective τ (Algebra.IsAlgebraic.algHom_bijective τ)
  let σ : Kb R →ₐ[FractionRing R] Kb R := (e.symm : Kb R →ₐ[FractionRing R] Kb R)
  have hστ : ∀ x, σ (τ x) = x := fun x => e.symm_apply_apply x
  have hτσ : ∀ x, τ (σ x) = x := fun x => e.apply_symm_apply x
  have hb₀ : twF τ ≫ p.g.b = p₀.g.b := Over.OverMorphism.ext (by
    rw [Over.comp_left, twF_left]; exact h.2.1.symm)
  have hb : twF σ ≫ p₀.g.b = p.g.b := by
    rw [← hb₀, ← Category.assoc, twF_comp_eq_id hστ, Category.id_comp]
  have hφ := famMapTw_phiφ D σ α h.1 hb
  let u' := genCast hφ (LB.pullGen D.P.L _ _ u (famMapTw D σ).left)
  have hu' : u'.IsGen := genCast_isGen _ (DVR.pullGen_isGen _ _ _ u hu _)
  have hid : (twF σ).left ≫ spMap τ.toRingHom = 𝟙 _ := by
    rw [← twF_left, ← Over.comp_left, twF_comp_eq_id hστ]; rfl
  have hz : (DegPre.zF D (Kb R)).left ≫ (famMapTw D σ).left = (twF σ).left ≫ (DegPre.zF D (Kb R)).left := by
    rw [← Over.comp_left, zF_famMapTw, Over.comp_left]
  have hu'0 : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u' (DegPre.zF D (Kb R)).left)
      (LB.mulGen D.P.L _ _ _ _ (p.g.s α) w) := corr_of_val hL fun y J hJ => by
    rw [val_pull hJ, val_genCast, val_pull hJ, Category.id_comp, hz, ← val_pull hJ, val_corr hJ hu0,
      val_mul hJ, val_mul hJ, val_corr hJ (h.2.2 α), val_pull hJ, frTw, val_genCast, val_pull hJ, hid]
  have H1 := (secRel_iff hL _ _ _ _ _ _ _ _ _ u').1 (H α u' hu' hu'0)
  refine (secRel_iff hL _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  have e1 := H1 _ (famMapTw D τ).left y J hJ
  have hTT : (famMapTw D τ).left ≫ (famMapTw D σ).left = 𝟙 _ := by
    rw [← Over.comp_left, famMapTw_comp_eq_id D hτσ]; rfl
  rw [val_genCast, val_pull hJ, hTT] at e1
  rw [← h.1] at e1
  have hc : (famMapTw D τ).left ≫ (DegPre.trPt D (Kb R) p.g.b).left =
      (DegPre.trPt D (Kb R) p₀.g.b).left ≫ (famMapTw D τ).left := by
    rw [← Over.comp_left, famMapTw_trPt D τ hb₀, Over.comp_left]
  rw [sval_famTw _ _ _ _ _ _ hJ, sval_famTw _ _ _ _ _ _ hJ]
  simp only [Category.id_comp]
  rw [e1, hc]

end GlobalTheory.Mum.Conj.PhiTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OperatorRelationPullbackGaloisAutomorphismStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.operator_relation_pullback_galois_automorphism : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀) (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) (s s' : Fam D (Kb R) N), PhiRel D (Kb R) N p w s s' → PhiRel D (Kb R) N p₀ (frTw D τ h w) (famTw D N τ s) (famTw D N τ s') := by
  first | exact @GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw | exact GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw | (intros; apply GlobalTheory.Mum.Conj.PhiTw.phiRel_famTw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistSemilinearSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistSemilinearSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem famTw_isSmul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (s s' : Fam D (Kb R) N),
    Fam.IsSmul D (Kb R) c s s' → Fam.IsSmul D (Kb R) (σ c) (famTw D N σ s) (famTw D N σ s') := by
  intro R _ _ D N σ c s s' h
  rw [ReciprocityTheory.ChartRestriction.G.DVR.isSmul_iff] at h
  subst h
  intro α j
  have e := map_smulₛₗ (GlobalTheory.FieldBaseChange.famPull D (Kb R) (TwF σ) GlobalTheory.allSixLaws.1.globalFns N) c s
  exact congrArg (fun q : Fam D (TwF σ) N => (q.s α).f j) e

end GlobalTheory.Mum.Conj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistSemilinearSmulStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_semilinear_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (s s' : Fam D (Kb R) N), Fam.IsSmul D (Kb R) c s s' → Fam.IsSmul D (Kb R) (σ c) (famTw D N σ s) (famTw D N σ s') := by
  first | exact @GlobalTheory.Mum.Conj.famTw_isSmul | exact GlobalTheory.Mum.Conj.famTw_isSmul | (intros; apply GlobalTheory.Mum.Conj.famTw_isSmul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistBijective
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistBijective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj

variable {R : Type} [CommRing R] [IsDomain R]

theorem twK_comp_twK (σ τ : Kb R →ₐ[FractionRing R] Kb R) (h : τ.comp σ = AlgHom.id _ _) :
    twK τ ≫ twK σ = 𝟙 _ := by
  ext1
  rw [Over.comp_left, twK_left, twK_left, Over.id_left, spMap, spMap, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  have : τ.toRingHom.comp σ.toRingHom = RingHom.id _ := congrArg AlgHom.toRingHom h
  rw [this]
  exact Spec.map_id _

theorem mTw_comp_mTw_left (A : PolAV (Sp (FractionRing R))) (σ τ : Kb R →ₐ[FractionRing R] Kb R)
    (h : τ.comp σ = AlgHom.id _ _) : (mTw A τ).left ≫ (mTw A σ).left = 𝟙 _ := by
  rw [← Over.comp_left]
  have : mTw A τ ≫ mTw A σ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [Category.assoc, mTw_fst, ← Category.assoc, mTw_fst, Category.assoc, twK_comp_twK σ τ h,
        Category.comp_id, Category.id_comp]
    · rw [Category.assoc, mTw_snd, mTw_snd, Category.id_comp]
  rw [this]; rfl

theorem secTw_secTw (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R)
    (h : τ.comp σ = AlgHom.id _ _) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) :
    secTw A N τ (secTw A N σ t) = t := by
  refine GlobalTheory.FieldBaseChange.sec_ext' A.isLB fun y J hJ => ?_
  refine (GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans
    ((GlobalTheory.FieldBaseChange.sval_pullOver _ _ _ _ hJ).trans ?_)
  rw [Category.assoc, mTw_comp_mTw_left A σ τ h, Category.comp_id]

theorem secTw_bijective (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) : Function.Bijective (secTw A N σ) := by
  have hσ : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let e := AlgEquiv.ofBijective σ hσ
  let τ : Kb R →ₐ[FractionRing R] Kb R := e.symm.toAlgHom
  have h1 : τ.comp σ = AlgHom.id _ _ := by
    ext x; exact e.symm_apply_apply x
  have h2 : σ.comp τ = AlgHom.id _ _ := by
    ext x; exact e.apply_symm_apply x
  exact ⟨Function.LeftInverse.injective (g := secTw A N τ) (secTw_secTw A N σ τ h1),
    Function.RightInverse.surjective (g := secTw A N τ) (secTw_secTw A N τ σ h2)⟩

end GlobalTheory.Mum.Conj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistBijectiveStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_bijective : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R), Function.Bijective (secTw A N σ) := by
  first | exact @GlobalTheory.Mum.Conj.secTw_bijective | exact GlobalTheory.Mum.Conj.secTw_bijective | (intros; apply GlobalTheory.Mum.Conj.secTw_bijective <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionPullbackThetaSectionsGaloisTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionPullbackThetaSectionsGaloisTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

variable {R : Type} [CommRing R] [IsDomain R]

theorem twK_comp_eq_id {σ τ : Kb R →ₐ[FractionRing R] Kb R} (h : σ.comp τ = AlgHom.id _ _) :
    twK σ ≫ twK τ = 𝟙 _ := by
  apply Over.OverMorphism.ext
  show spMap σ.toRingHom ≫ spMap τ.toRingHom = 𝟙 _
  rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have e : σ.toRingHom.comp τ.toRingHom = RingHom.id _ := congrArg AlgHom.toRingHom h
  rw [e]
  exact Spec.map_id _

theorem mTw_comp_eq_id (A : PolAV (Sp (FractionRing R))) {σ τ : Kb R →ₐ[FractionRing R] Kb R}
    (h : σ.comp τ = AlgHom.id _ _) : mTw A σ ≫ mTw A τ = 𝟙 _ := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [Category.assoc, mTw_fst, ← Category.assoc, mTw_fst, Category.assoc, twK_comp_eq_id h, Category.comp_id,
      Category.id_comp]
  · rw [Category.assoc, mTw_snd, mTw_snd, Category.id_comp]

theorem mTw_translT (A : PolAV (Sp (FractionRing R))) {σ τ : Kb R →ₐ[FractionRing R] Kb R}
    (h : σ.comp τ = AlgHom.id _ _) (x : TFK (R := R) (Kb R) ⟶ A.A) :
    mTw A σ ≫ translT A.A (twK τ ≫ x) = translT A.A x ≫ mTw A σ := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [translT]
    rw [Category.assoc, Category.assoc, lift_fst, mTw_fst, ← Category.assoc, lift_fst]
  · simp only [translT]
    rw [Category.assoc, Category.assoc, lift_snd, mTw_snd, lift_snd]
    simp only [translPt]
    rw [← Category.assoc, comp_lift, ← Category.assoc (mTw A σ), mTw_fst, mTw_snd, Category.assoc,
      ← Category.assoc (twK σ), twK_comp_eq_id h, Category.id_comp]

theorem isActOf_secTw : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R), σ.comp τ = AlgHom.id _ _ → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (a b : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), IsActOf A.A A.L N (thTw A N τ θ) a b → IsActOf A.A A.L N θ (secTw A N σ a) (secTw A N σ b) := by
  intro R _ _ A N σ τ hστ θ a b H
  refine twist_of_val A.isLB θ.isGen fun z J hJ => ?_
  have e1 : (𝟙 _ ≫ (mTw A σ).left) ≫ (mTw A τ).left = 𝟙 _ := by
    rw [Category.id_comp, ← Over.comp_left, mTw_comp_eq_id A hστ, Over.id_left]
  have e2 : (𝟙 _ ≫ (mTw A σ).left) ≫ (translT A.A (twK τ ≫ θ.pt)).left =
      (𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mTw A σ).left := by
    simp only [Category.id_comp, ← Over.comp_left, mTw_translT A hστ]
  have hv : val (thTw A N τ θ).φ (𝟙 _ ≫ (mTw A σ).left) z J = val θ.φ (𝟙 _) z J :=
    (val_genCast _ _ _ z J).trans ((val_pull hJ _ _ _).trans (congrArg (fun r => val θ.φ r z J) e1))
  have H' := twist_val H (𝟙 _ ≫ (mTw A σ).left) z hJ
  rw [hv] at H'
  have hb : sval (secTw A N σ b) (𝟙 _) z J = sval b (𝟙 _ ≫ (mTw A σ).left) z J :=
    GlobalTheory.FieldBaseChange.sval_pullOver _ _ b _ hJ
  have ha : sval (secTw A N σ a) (𝟙 _ ≫ (translT A.A θ.pt).left) z J =
      sval a ((𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mTw A σ).left) z J :=
    GlobalTheory.FieldBaseChange.sval_pullOver _ _ a _ hJ
  refine hb.trans (H'.trans ?_)
  rw [ha]
  exact congrArg (fun r => (val θ.φ (𝟙 _) z J).val * sval a r z J) e2

end GlobalTheory.Mum.Conj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGroupActionPullbackThetaSectionsGaloisTwistStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaGroupAction_pullbackThetaSectionsGaloisTwist : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ τ : Kb R →ₐ[FractionRing R] Kb R), σ.comp τ = AlgHom.id _ _ → ∀ (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))) (a b : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), IsActOf A.A A.L N (thTw A N τ θ) a b → IsActOf A.A A.L N θ (secTw A N σ a) (secTw A N σ b) := by
  first | exact @GlobalTheory.Mum.Conj.isActOf_secTw | exact GlobalTheory.Mum.Conj.isActOf_secTw | (intros; apply GlobalTheory.Mum.Conj.isActOf_secTw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLiftGaloisTwistOfConjugatePoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLiftGaloisTwistOfConjugatePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem symLift_thTw : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (x x' : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))), SymLift A.A A.L N N x θ → x'.left = spMap τ.toRingHom ≫ x.left → SymLift A.A A.L N N x' (thTw A N τ θ) := by
  intro R _ _ A N τ x x' θ h hx
  have ex : x' = twK τ ≫ x := Over.OverMorphism.ext (by rw [hx, Over.comp_left, twK_left])
  subst ex
  have eM : mTw A τ = twK τ ▷ A.A := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [mTw_fst, whiskerRight_fst]
    · rw [mTw_snd, whiskerRight_snd]
  exact ReciprocityTheory.ChartRestriction.G.Geo.Tor.symLift_pull A.isLB (twK τ) h _ (thTw A N τ θ).isGen fun r z J hJ => by
    show val (genCast _ _) r z J = _
    rw [val_genCast]
    exact (val_pull hJ _ _ r).trans (by rw [eM])

end GlobalTheory.Mum.Conj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetricLiftGaloisTwistOfConjugatePointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLift_galoisTwist_of_conjugatePoint : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (x x' : TFK (R := R) (Kb R) ⟶ A.A) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := R) (Kb R))), SymLift A.A A.L N N x θ → x'.left = spMap τ.toRingHom ≫ x.left → SymLift A.A A.L N N x' (thTw A N τ θ) := by
  first | exact @GlobalTheory.Mum.Conj.symLift_thTw | exact GlobalTheory.Mum.Conj.symLift_thTw | (intros; apply GlobalTheory.Mum.Conj.symLift_thTw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFramePullbackMumfordFrameGaloisTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFramePullbackMumfordFrameGaloisTwist
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem gm_comp_stalkMap {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U)
    (a : Γ(X, U)ˣ) : gm (f ≫ g) z U a = Units.map (f.stalkMap z).hom.toMonoidHom (gm g (f z) U a) := by
  apply Units.ext
  rw [gm_val (f ≫ g) z U h, Units.coe_map, gm_val g (f z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply f (g ⁻¹ᵁ U) z h ((g.app U).hom a.val)).symm

theorem val_comp_stalkMap {X Y Z W : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb L φ ε)) (f : Z ⟶ W) (r : W ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    val t (f ≫ r) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val t r (f z) (fun ψ => J (f ≫ ψ))) := by
  rw [val_of t (f ≫ r) z J (fun k => J (f ≫ r ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_comp_stalkMap f r z _ (Set.mem_iInter.2 fun k => hJ (f ≫ r ≫ φ k)) _

theorem good_comp {X Z W : Scheme.{0}} {L : LB X} (f : Z ⟶ W) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    Good L (f z) (fun ψ => J (f ≫ ψ)) := fun ψ => hJ (f ≫ ψ)

end GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem txFrame_frTw (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ)
    (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀)
    (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b) : GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p₀ (frTw D τ h w) := by
  rintro ⟨hg, h2, hN⟩
  set f : (TF (R := R) (Kb R)).left ⟶ (TF (R := R) (Kb R)).left := spMap τ.toRingHom with hf
  have hfr : ∀ (z : (TF (R := R) (Kb R)).left) (J), Good D.P.L z J →
      val (frTw D τ h w) (𝟙 _) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val w (𝟙 _) (f z) (fun ψ => J (f ≫ ψ))) := by
    intro z J hJ
    rw [frTw, val_genCast, val_pull hJ, Category.id_comp, ← Category.comp_id f]
    exact val_comp_stalkMap w f (𝟙 _) z J hJ
  have hsy : ∀ (z : (TF (R := R) (Kb R)).left) (J), Good D.P.L z J →
      val (p₀.g.s p₀.y) (𝟙 _) z J = Units.map (f.stalkMap z).hom.toMonoidHom (val (p.g.s p.y) (𝟙 _) (f z) (fun ψ => J (f ≫ ψ))) := by
    intro z J hJ
    rw [h.1, val_corr hJ (h.2.2 p.y), val_pull hJ, Category.id_comp, ← Category.comp_id f]
    exact val_comp_stalkMap _ f (𝟙 _) z J hJ
  refine ⟨genCast_isGen _ (ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen D.P.L _ _ w hg _), ?_, ?_⟩
  · intro ν hν z J hJ
    rw [hfr z J hJ, hsy z J hJ, h.2.1, val_comp_stalkMap ν f _ z J hJ, ← map_pow, ← map_mul,
      h2 ν hν (f z) _ (good_comp f hJ)]
  · intro κ hκ z J hJ
    have hpsi : val (D.psi p₀.y) (jFK (R := R) (Kb R)) z J =
        Units.map (f.stalkMap z).hom.toMonoidHom (val (D.psi p.y) (jFK (R := R) (Kb R)) (f z) (fun ψ => J (f ≫ ψ))) := by
      have e := val_comp_stalkMap (D.psi p.y) f (jFK (R := R) (Kb R)) z J hJ
      rw [h.1]
      refine Eq.trans ?_ e
      exact congrArg (fun r => val (D.psi p.y) r z J) (spMap_jFK τ).symm
    have hrig : GlobalTheory.UT.rigV D (TF (R := R) (Kb R)).hom z J =
        Units.map (f.stalkMap z).hom.toMonoidHom (GlobalTheory.UT.rigV D (TF (R := R) (Kb R)).hom (f z) (fun ψ => J (f ≫ ψ))) := by
      unfold GlobalTheory.UT.rigV
      rw [← val_comp_stalkMap _ f _ z J hJ]
      exact congrArg (fun r => val D.rig r z J) (spMap_jFKR τ).symm
    rw [id_eq, hfr z J hJ, hpsi, hrig, h.2.1, val_comp_stalkMap κ f _ z J hJ, ← map_pow,
      ← map_mul, ← map_mul]
    exact congrArg _ (hN κ hκ (f z) _ (good_comp f hJ))

end GlobalTheory.Mum.Conj

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymmetricFramePullbackMumfordFrameGaloisTwistStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSymmetricFrame_pullbackMumfordFrameGaloisTwist : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (τ : Kb R →ₐ[FractionRing R] Kb R) (p p₀ : QkPt D (Kb R) N) (h : QkExt τ.toRingHom p p₀) (w : GlobalTheory.UT.Frm D (Kb R) N p.g.b), GlobalTheory.UT.TXFrame N p w → GlobalTheory.UT.TXFrame N p₀ (frTw D τ h w) := by
  first | exact @GlobalTheory.Mum.Conj.txFrame_frTw | exact GlobalTheory.Mum.Conj.txFrame_frTw | (intros; apply GlobalTheory.Mum.Conj.txFrame_frTw <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartAdd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem secTw_add_chart : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N),
    (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  intro R _ _ A N σ t t' t'' h j
  show GlobalTheory.FieldBaseChange.pullFn _ _ (t''.f j) =
    GlobalTheory.FieldBaseChange.pullFn _ _ (t.f j) + GlobalTheory.FieldBaseChange.pullFn _ _ (t'.f j)
  rw [h j]
  exact map_add _ _ _

end GlobalTheory.Mum.Conj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartAddStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (t t' t'' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), (∀ j, t''.f j = t.f j + t'.f j) → ∀ j, (secTw A N σ t'').f j = (secTw A N σ t).f j + (secTw A N σ t').f j := by
  first | exact @GlobalTheory.Mum.Conj.secTw_add_chart | exact GlobalTheory.Mum.Conj.secTw_add_chart | (intros; apply GlobalTheory.Mum.Conj.secTw_add_chart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartSemilinear
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartSemilinear
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem secTw_chart_smul : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N),
    (∀ j, t'.f j = liftFun A.A _ (fnF (R := R) (Kb R) c) * t.f j) →
    ∀ j, (secTw A N σ t').f j = liftFun A.A _ (fnF (R := R) (Kb R) (σ c)) * (secTw A N σ t).f j := by
  intro R _ _ A N σ c t t' h j
  have ht : @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t' =
      c • @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t :=
    GlobalTheory.FieldBaseChange.SecOver.ext _ _ fun i => h i
  have e : secTw A N σ t' = σ c • @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ))))
      (secTw A N σ t) := by
    unfold secTw
    rw [show t' = @id (GlobalTheory.FieldBaseChange.SecOver (fst (TFK (R := R) (Kb R)) A.A).left
      (LB.LinComb A.L (K := Fin 1) (fun _ => (snd (TFK (R := R) (Kb R)) A.A).left) (fun _ => (N : ℤ)))) t' from rfl,
      ht, map_smulₛₗ]
    rfl
  rw [e]
  rfl

end GlobalTheory.Mum.Conj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistChartSemilinearStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_semilinear : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (c : Kb R) (t t' : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), (∀ j, t'.f j = liftFun A.A _ (fnF (R := R) (Kb R) c) * t.f j) → ∀ j, (secTw A N σ t').f j = liftFun A.A _ (fnF (R := R) (Kb R) (σ c)) * (secTw A N σ t).f j := by
  first | exact @GlobalTheory.Mum.Conj.secTw_chart_smul | exact GlobalTheory.Mum.Conj.secTw_chart_smul | (intros; apply GlobalTheory.Mum.Conj.secTw_chart_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistIsConjugate
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistIsConjugate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

theorem comp_mTw_left_eq {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R)))
    (σ : Kb R →ₐ[FractionRing R] Kb R) {Z : Scheme.{0}} {p p' : Z ⟶ (TFK (R := R) (Kb R) ⊗ A.A).left}
    (h₂ : p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p ≫ (snd (TFK (R := R) (Kb R)) A.A).left)
    (h₁ : p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left =
      p ≫ (fst (TFK (R := R) (Kb R)) A.A).left ≫ spMap σ.toRingHom) :
    p ≫ (mTw A σ).left = p' := by
  refine pullback.hom_ext (f := (TFK (R := R) (Kb R)).hom) (g := A.A.hom) ?_ ?_
  · change (p ≫ (mTw A σ).left) ≫ (fst (TFK (R := R) (Kb R)) A.A).left = p' ≫ (fst (TFK (R := R) (Kb R)) A.A).left
    rw [Category.assoc, mTw_fst_left, h₁]
  · change (p ≫ (mTw A σ).left) ≫ (snd (TFK (R := R) (Kb R)) A.A).left = p' ≫ (snd (TFK (R := R) (Kb R)) A.A).left
    rw [Category.assoc, mTw_snd_left, h₂]

theorem secTw_isTwist (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N) :
    SecTw σ t (secTw A N σ t) := by
  intro Z p p' h₂ h₁ z J hJ
  rw [← comp_mTw_left_eq A σ h₂ h₁]
  exact GlobalTheory.FieldBaseChange.sval_pullOver (mTw_fst_left A σ) (fun _ => (mTw_snd_left A σ).symm) t p hJ

end GlobalTheory.Mum.Conj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaSectionsGaloisTwistIsConjugateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaSectionsGaloisTwist_isConjugate : ∀ (R : Type) [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (t : SecK A.L (snd (TFK (R := R) (Kb R)) A.A).left N), SecTw σ t (secTw A N σ t) := by
  first | exact @GlobalTheory.Mum.Conj.secTw_isTwist | exact GlobalTheory.Mum.Conj.secTw_isTwist | (intros; apply GlobalTheory.Mum.Conj.secTw_isTwist <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistFixesIntegralFamil
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistFixesIntegralFamil
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

namespace GlobalTheory.Mum.Conj

open GlobalTheory.FieldBaseChange ReciprocityTheory.ChartRestriction.G.DVR

theorem famTw_eq_of_over : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (N : ℕ)
    (σ : Kb R →ₐ[FractionRing R] Kb R) (F₀ : IntFam I D N) (s : Fam D (Kb R) N), F₀.Over s → famTw D N σ s = s := by
  intro R _ _ I D N σ F₀ s hs
  have hL := D.P.isLB
  refine fam_ext fun α j => congrArg (fun q => LB.Sec.f q j) (sec_ext' hL fun y J hJ => ?_)
  show sval (termPull D (Kb R) (TwF σ) N α (s.s α)) (𝟙 _) y J = _
  refine (sval_pullOver _ _ _ _ hJ).trans ?_
  rw [← SectionScalarValuation.secScal_sval (hs α) _ y hJ, ← SectionScalarValuation.secScal_sval (hs α) (𝟙 _) y hJ]
  congr 1
  have e : (famMap D (Kb R) (TwF σ)).left ≫ (DegPre.prB D (Kb R)).left = (DegPre.prB D (TwF σ)).left :=
    congrArg (fun q => q.left) (famMap_snd D (Kb R) (TwF σ))
  exact (Category.assoc _ _ _).trans (congrArg (fun q => 𝟙 _ ≫ q) e)

end GlobalTheory.Mum.Conj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistFixesIntegralFamilStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_fixes_integralFamily : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (F₀ : IntFam I D N) (s : Fam D (Kb R) N), F₀.Over s → famTw D N σ s = s := by
  first | exact @GlobalTheory.Mum.Conj.famTw_eq_of_over | exact GlobalTheory.Mum.Conj.famTw_eq_of_over | (intros; apply GlobalTheory.Mum.Conj.famTw_eq_of_over <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistChartAdd
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistChartAdd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj

noncomputable section

namespace GlobalTheory.Mum.Conj

theorem famTw_add_f : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s s' s'' : Fam D (Kb R) N), (∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j) → ∀ α j, ((famTw D N σ s'').s α).f j = ((famTw D N σ s).s α).f j + ((famTw D N σ s').s α).f j := by
  intro R _ _ D N σ s s' s'' h α j
  have e : s'' = s + s' := ReciprocityTheory.ChartRestriction.G.DVR.fam_ext fun α j => (h α j).trans (ReciprocityTheory.ChartRestriction.G.DVR.add_f s s' α j).symm
  subst e
  show ((GlobalTheory.FieldBaseChange.famPull D (Kb R) (TwF σ) GlobalTheory.allSixLaws.1.globalFns N (s + s') :
    Fam D (TwF σ) N).s α).f j = _
  rw [map_add (f := _)]
  rfl

end GlobalTheory.Mum.Conj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackThetaFamilyGaloisTwistChartAddStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.Mum.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pullbackThetaFamilyGaloisTwist_chart_add : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (N : ℕ) (σ : Kb R →ₐ[FractionRing R] Kb R) (s s' s'' : Fam D (Kb R) N), (∀ α j, (s''.s α).f j = (s.s α).f j + (s'.s α).f j) → ∀ α j, ((famTw D N σ s'').s α).f j = ((famTw D N σ s).s α).f j + ((famTw D N σ s').s α).f j := by
  first | exact @GlobalTheory.Mum.Conj.famTw_add_f | exact GlobalTheory.Mum.Conj.famTw_add_f | (intros; apply GlobalTheory.Mum.Conj.famTw_add_f <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateEquivariantBijectionTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.Mum GlobalTheory.Mum.Conj in
theorem GlobalTheory.Mum.exists_eqv_conj : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ τ : Kb R →ₐ[FractionRing R] Kb R, LabExt τ lab lab) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ E', Eqv D.toPre A (Kb R) N lab E' ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre N) s, F₀.Over s → SecTw σ (E s) (E' s) := by
  intro R _ _ _ _ D A N _ lab E hE hlab σ
  have hσ : Function.Bijective σ := Algebra.IsAlgebraic.algHom_bijective σ
  let σe : Kb R ≃ₐ[FractionRing R] Kb R := AlgEquiv.ofBijective σ hσ
  let τ : Kb R →ₐ[FractionRing R] Kb R := σe.symm.toAlgHom
  have hστ : σ.comp τ = AlgHom.id _ _ := AlgHom.ext fun x => σe.apply_symm_apply x
  have hστ' : ∀ x, σ (τ x) = x := fun x => σe.apply_symm_apply x
  refine ⟨fun s => secTw A N σ (E (famTw D.toPre N τ s)), ⟨?_, ?_, ?_, hE.onto, hE.frame, hE.lift, ?_⟩, ?_⟩
  · exact (GlobalTheory.T.pullbackThetaSectionsGaloisTwist_bijective R A N σ).comp (hE.bij.comp (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_bijective R D.toPre N τ))
  · intro s s' s'' h j
    exact GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_add R A N σ _ _ _ (hE.add _ _ _ (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_chart_add R D.toPre N τ _ _ _ h)) j
  · intro c s s' h j
    have := GlobalTheory.T.pullbackThetaSectionsGaloisTwist_chart_semilinear R A N σ (τ c) _ _ (hE.smul (τ c) _ _ (GlobalTheory.T.pullbackThetaFamilyGaloisTwist_semilinear_smul R D.toPre N τ c _ _ h)) j
    rwa [hστ'] at this
  · intro p w θ s s' hw hθ hφ
    obtain ⟨p₀, hp₀⟩ := qkExtExists R D.toPre (Kb R) (Kb R) τ.toRingHom (fun r => τ.commutes r) N p
    have hx := hlab τ p p₀ hp₀
    exact GlobalTheory.T.thetaGroupAction_pullbackThetaSectionsGaloisTwist R A N σ τ hστ θ _ _ (hE.act p₀ (frTw D.toPre τ hp₀ w) (thTw A N τ θ) _ _
      (GlobalTheory.T.isSymmetricFrame_pullbackMumfordFrameGaloisTwist R D.toPre N τ p p₀ hp₀ w hw) (GlobalTheory.T.symmetricLift_galoisTwist_of_conjugatePoint R A N τ _ _ θ hθ hx) (GlobalTheory.T.operator_relation_pullback_galois_automorphism R D.toPre N τ p p₀ hp₀ w s s' hφ))
  · intro F₀ s hs
    show SecTw σ (E s) (secTw A N σ (E (famTw D.toPre N τ s)))
    rw [GlobalTheory.T.pullbackThetaFamilyGaloisTwist_fixes_integralFamily R _ D.toPre N τ F₀ s hs]
    exact GlobalTheory.T.pullbackThetaSectionsGaloisTwist_isConjugate R A N σ (E s)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGaloisConjugateEquivariantBijectionTwistStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_galoisConjugate_equivariantBijection_twist : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (N : ℕ), Odd N → ∀ (lab : QkPt D.toPre (Kb R) N → (TFK (R := R) (Kb R) ⟶ A.A)) E, Eqv D.toPre A (Kb R) N lab E → (∀ τ : Kb R →ₐ[FractionRing R] Kb R, LabExt τ lab lab) → ∀ σ : Kb R →ₐ[FractionRing R] Kb R, ∃ E', Eqv D.toPre A (Kb R) N lab E' ∧ ∀ (F₀ : IntFam (maximalIdeal R) D.toPre N) s, F₀.Over s → SecTw σ (E s) (E' s) := by
  first | exact @GlobalTheory.Mum.exists_eqv_conj | exact GlobalTheory.Mum.exists_eqv_conj | (intros; apply GlobalTheory.Mum.exists_eqv_conj <;> assumption)
end
