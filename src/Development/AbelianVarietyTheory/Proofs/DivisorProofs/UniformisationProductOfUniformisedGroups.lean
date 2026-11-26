module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedChernMeasureIntegralEqGenericFibre
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThickeningProductIsoPreservesCubicalStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpansionModIdealPowBoxProductEqBoxProduct
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoxFamilyLinearIndependentProductDegeneration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AppSurjectiveOfOmegaMapSurjectiveConnected
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupIsogenyHeightEqDualSameDegree
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionCorrectionIsTopDegreeForm

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FamDimOfExpBij
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem famDim_of_expBij : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), 1 ≤ k → U.ExpBij k → Module.finrank (FractionRing R) (Fam D.toPre (FractionRing R) k) = k ^ A.g := by
  intro R _ _ I D A G _ _ U k hk hbij
  obtain ⟨b, hex, huniq⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange R I D A G U k hk
  choose F hF using fun i => (hbij.1 (b i)).exists
  have hlin : ∀ (c : Fin (k ^ A.g) → FractionRing R) (s : U.SecK k),
      (∀ j, s.f j = ∑ i, resTop _ (scal (pullback.snd G.hom (jK R)) (c i)) * (b i).f j) →
      U.Expands k s (∑ i, c i • F i) := fun c s hs =>
    GlobalTheory.UnifPowAdm.expands_comb U k (s := b) hF (fun j => hs j)
  let φ : (Fin (k ^ A.g) → FractionRing R) →ₗ[FractionRing R] Fam D.toPre (FractionRing R) k :=
    Fintype.linearCombination (FractionRing R) F
  have hφ : ∀ c, φ c = ∑ i, c i • F i := fun c => rfl
  have hinj : Function.Injective φ := by
    intro c c' h
    obtain ⟨s, hs⟩ := hex c
    obtain ⟨s', hs'⟩ := hex c'
    have h1 := hlin c s hs
    have h2 := hlin c' s' hs'
    rw [← hφ] at h1 h2
    rw [← h] at h2
    have e : s = s' := (hbij.2 (φ c)).unique h1 h2
    subst e
    exact (huniq s).unique hs hs'
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨s, hs⟩ := (hbij.2 x).exists
    obtain ⟨c, hc⟩ := (huniq s).exists
    exact ⟨c, (hbij.1 s).unique (hlin c s hc) hs⟩
  rw [← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq]
  simp

end GlobalTheory.ProdUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsLastLast
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem even_box₂ : ∀ {B B₁ B₂ G G₁ G₂ T T₁ T₂ : Scheme.{0}} {M : LB B} {M₁ : LB B₁} {M₂ : LB B₂} {L : LB G} {L₁ : LB G₁} {L₂ : LB G₂} {b₁ : B ⟶ B₁} {b₂ : B ⟶ B₂} {g₁ : G ⟶ G₁} {g₂ : G ⟶ G₂} {p : T ⟶ B} {f : T ⟶ G} {p₁ : T₁ ⟶ B₁} {f₁ : T₁ ⟶ G₁} {p₂ : T₂ ⟶ B₂} {f₂ : T₂ ⟶ G₂} {h₁ : T ⟶ T₁} {h₂ : T ⟶ T₂} (wM : LB.Iso M (extLB M₁ M₂ b₁ b₂)) (wL : LB.Iso L (extLB L₁ L₂ g₁ g₂)) (we₁ : LB.Iso (L₁.pull f₁) (M₁.pull p₁)) (we₂ : LB.Iso (L₂.pull f₂) (M₂.pull p₂)), M.IsLB → M₁.IsLB → M₂.IsLB → L.IsLB → L₁.IsLB → L₂.IsLB → p ≫ b₁ = h₁ ≫ p₁ → p ≫ b₂ = h₂ ≫ p₂ → f ≫ g₁ = h₁ ≫ f₁ → f ≫ g₂ = h₂ ≫ f₂ → ∀ (we : LB.Iso (L.pull f) (M.pull p)), BoxSq wM wL we we₁ we₂ h₁ h₂ → ∀ (iT : T ⟶ T) (iT₁ : T₁ ⟶ T₁) (iT₂ : T₂ ⟶ T₂) {iG : G ⟶ G} {iG₁ : G₁ ⟶ G₁} {iG₂ : G₂ ⟶ G₂} {iB : B ⟶ B} {iB₁ : B₁ ⟶ B₁} {iB₂ : B₂ ⟶ B₂} (s : LB.Gen (LB.LinComb L (K := Fin 2) ![iG, 𝟙 G] ![1, -1])) (s₁ : LB.Gen (LB.LinComb L₁ (K := Fin 2) ![iG₁, 𝟙 G₁] ![1, -1])) (s₂ : LB.Gen (LB.LinComb L₂ (K := Fin 2) ![iG₂, 𝟙 G₂] ![1, -1])) (σ : LB.Gen (LB.LinComb M (K := Fin 2) ![iB, 𝟙 B] ![1, -1])) (σ₁ : LB.Gen (LB.LinComb M₁ (K := Fin 2) ![iB₁, 𝟙 B₁] ![1, -1])) (σ₂ : LB.Gen (LB.LinComb M₂ (K := Fin 2) ![iB₂, 𝟙 B₂] ![1, -1])), iT ≫ h₁ = h₁ ≫ iT₁ → iT ≫ h₂ = h₂ ≫ iT₂ → iT ≫ f = f ≫ iG → iT ≫ p = p ≫ iB → iT₁ ≫ f₁ = f₁ ≫ iG₁ → iT₁ ≫ p₁ = p₁ ≫ iB₁ → iT₂ ≫ f₂ = f₂ ≫ iG₂ → iT₂ ≫ p₂ = p₂ ≫ iB₂ → IsBoxGen wL g₁ g₂ s s₁ s₂ → IsBoxGen wM b₁ b₂ σ σ₁ σ₂ → GlobalTheory.PowUnif.EvenAlong we₁ iT₁ s₁ σ₁ → GlobalTheory.PowUnif.EvenAlong we₂ iT₂ s₂ σ₂ → GlobalTheory.PowUnif.EvenAlong we iT s σ := by
  intro B B₁ B₂ G G₁ G₂ T T₁ T₂ M M₁ M₂ L L₁ L₂ b₁ b₂ g₁ g₂ p f p₁ f₁ p₂ f₂ h₁ h₂ wM wL we₁ we₂
    hM hM₁ hM₂ hL hL₁ hL₂ e₁ e₂ e₃ e₄ we Q iT iT₁ iT₂ iG iG₁ iG₂ iB iB₁ iB₂ s s₁ s₂ σ σ₁ σ₂
    ih₁ ih₂ iF iP iF₁ iP₁ iF₂ iP₂ Hs Hσ ev₁ ev₂
  intro jS jT cS cT V k₁ k₂ k₃ k₄
  refine unit_ext fun z hz => ?_
  obtain ⟨n₁, n₂⟩ := GlobalTheory.EvenPull.even_stalk we s σ jS jT V k₁ k₂ k₃ k₄ (𝟙 T) z hz
  refine n₁.trans (Eq.trans ?_ n₂.symm)
  clear n₁ n₂
  obtain ⟨J, hJ, hJj⟩ := exists_good M hM z (fun k => p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) jT cT
    (fun k => Set.mem_iInter.1 (k₁ hz) k)
  obtain ⟨N, hN, hNj⟩ := exists_good L hL z (fun k => f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) jS cS
    (fun k => Set.mem_iInter.1 (k₄ hz) k)
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at hM₁ z
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at hM₂ z
  obtain ⟨N₁, hN₁⟩ := GlobalTheory.BoxFamily.exists_good_at hL₁ z
  obtain ⟨N₂, hN₂⟩ := GlobalTheory.BoxFamily.exists_good_at hL₂ z

  have hb₁ : (p ≫ iB) ≫ b₁ = (h₁ ≫ p₁) ≫ iB₁ := by
    rw [← iP, Category.assoc, e₁, ← Category.assoc, ih₁, Category.assoc, iP₁, Category.assoc]
  have hb₂ : (p ≫ iB) ≫ b₂ = (h₂ ≫ p₂) ≫ iB₂ := by
    rw [← iP, Category.assoc, e₂, ← Category.assoc, ih₂, Category.assoc, iP₂, Category.assoc]
  have hg₁ : (f ≫ iG) ≫ g₁ = (h₁ ≫ f₁) ≫ iG₁ := by
    rw [← iF, Category.assoc, e₃, ← Category.assoc, ih₁, Category.assoc, iF₁, Category.assoc]
  have hg₂ : (f ≫ iG) ≫ g₂ = (h₂ ≫ f₂) ≫ iG₂ := by
    rw [← iF, Category.assoc, e₄, ← Category.assoc, ih₂, Category.assoc, iF₂, Category.assoc]
  have QQ : ∀ k, om wM z J₁ J₂ J (p ≫ (![iB, 𝟙 B] : Fin 2 → _) k) *
        gw we ((![iT, 𝟙 T] : Fin 2 → _) k) z (J (p ≫ (![iB, 𝟙 B] : Fin 2 → _) k))
          (fun _ => N (f ≫ (![iG, 𝟙 G] : Fin 2 → _) k)) =
      gw we₁ ((![h₁ ≫ iT₁, h₁] : Fin 2 → _) k) z (J₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
          (fun _ => N₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k)) *
        gw we₂ ((![h₂ ≫ iT₂, h₂] : Fin 2 → _) k) z (J₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
          (fun _ => N₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k)) *
        om wL z N₁ N₂ N (f ≫ (![iG, 𝟙 G] : Fin 2 → _) k) := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · have q := Q T iT z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      rw [iP, iF, ih₁, ih₂, hb₁, hb₂, hg₁, hg₂] at q
      simpa only [Matrix.cons_val_zero] using q
    · have q := Q T (𝟙 T) z J₁ J₂ J N₁ N₂ N hJ₁ hJ₂ hJ hN₁ hN₂ hN
      simp only [Category.id_comp] at q
      rw [e₁, e₂, e₃, e₄] at q
      simpa only [Matrix.cons_val_one, Matrix.cons_val_zero, Category.comp_id] using q
  have HM := Hσ T p z J₁ J₂ J hJ₁ hJ₂ hJ
  rw [e₁, e₂] at HM
  have HL := Hs T f z N₁ N₂ N hN₁ hN₂ hN
  rw [e₃, e₄] at HL
  have H₁ : val σ₁ (h₁ ≫ p₁) z J₁ = (∏ k, gw we₁ ((![h₁ ≫ iT₁, h₁] : Fin 2 → _) k) z
      (J₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
      (fun _ => N₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
      val s₁ (h₁ ≫ f₁) z N₁ :=
    ev₁.stalk iF₁ iP₁ h₁ z _ _
      (fun a b e => congrArg N₁ ((Category.assoc _ _ _).trans ((congrArg (h₁ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun a b e => congrArg J₁ ((Category.assoc _ _ _).trans ((congrArg (h₁ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun k => hN₁ ((h₁ ≫ f₁) ≫ (![iG₁, 𝟙 G₁] : Fin 2 → _) k))
      (fun k => hJ₁ ((h₁ ≫ p₁) ≫ (![iB₁, 𝟙 B₁] : Fin 2 → _) k))
  have H₂ : val σ₂ (h₂ ≫ p₂) z J₂ = (∏ k, gw we₂ ((![h₂ ≫ iT₂, h₂] : Fin 2 → _) k) z
      (J₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
      (fun _ => N₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k)) ^ (![1, -1] : Fin 2 → ℤ) k) *
      val s₂ (h₂ ≫ f₂) z N₂ :=
    ev₂.stalk iF₂ iP₂ h₂ z _ _
      (fun a b e => congrArg N₂ ((Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun a b e => congrArg J₂ ((Category.assoc _ _ _).trans ((congrArg (h₂ ≫ ·) e).trans
        (Category.assoc _ _ _).symm)))
      (fun k => hN₂ ((h₂ ≫ f₂) ≫ (![iG₂, 𝟙 G₂] : Fin 2 → _) k))
      (fun k => hJ₂ ((h₂ ≫ p₂) ≫ (![iB₂, 𝟙 B₂] : Fin 2 → _) k))
  have R := rel_alg (![1, -1] : Fin 2 → ℤ) _ _ _ _ _ QQ HM HL H₁ H₂
  rw [val_of σ p z J jT hJj, val_of s f z N jS hNj, Fin.prod_univ_two] at R
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg] at R
  have a₀ : J (p ≫ iB) = jT 0 := hJj 0
  have a₁ : J (p ≫ 𝟙 B) = jT 1 := hJj 1
  have c₀ : N (f ≫ iG) = jS 0 := hNj 0
  have c₁ : N (f ≫ 𝟙 G) = jS 1 := hNj 1
  rw [a₀, a₁, c₀, c₁] at R
  simp only [Category.id_comp]
  rw [R, mul_right_comm, inv_mul_cancel_right]

end GlobalTheory.ProdUnif
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdUnit
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnifUnit

theorem prod_unit {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T T₀ : Over (Sp R)} (r : T₀ ⟶ T)
    (P : T ⟶ D.P.A) (h : r ≫ P = 1) (χ : D.X) {U : Type} [CommGroup U] (f : (T₀.left ⟶ D.P.A.left) → U) :
    ∏ k, f (r.left ≫ D.Oφ P χ k) ^ Oinvε k = 1 := by
  have e : ∀ k, r.left ≫ D.Oφ P χ k = D.Oφ (1 : T₀ ⟶ D.P.A) χ k := fun k => by
    rw [← h]; exact (WeightPf.Oφ_comp r P χ k).trans rfl
  have e₀ : D.Oφ (1 : T₀ ⟶ D.P.A) χ 0 = D.Oφ (1 : T₀ ⟶ D.P.A) χ 1 :=
    congrArg (fun m : T₀ ⟶ D.P.A => m.left) (_root_.one_mul (toUnit T₀ ≫ D.c χ))
  have e₂ : D.Oφ (1 : T₀ ⟶ D.P.A) χ 2 = D.Oφ (1 : T₀ ⟶ D.P.A) χ 3 := rfl
  simp only [e]
  rw [Fin.prod_univ_four, e₀, e₂]
  simp [Oinvε]

theorem unit_box : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X) (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)) (S : Scheme.{0}) (s : S ⟶ Sp R) (G G₁ G₂ : Over S) [GrpObj G] [GrpObj G₁] [GrpObj G₂] (σ₁ : G ⟶ G₁) (σ₂ : G ⟶ G₂) (P : (Over.map s).obj G ⟶ D.P.A) (P₁ : (Over.map s).obj G₁ ⟶ D₁.P.A) (P₂ : (Over.map s).obj G₂ ⟶ D₂.P.A) (χ : D.X) (t : LB.Gen (LB.LinComb D.P.L (D.Oφ P χ) Oinvε)) (t₁ : LB.Gen (LB.LinComb D₁.P.L (D₁.Oφ P₁ (q₁ χ)) Oinvε)) (t₂ : LB.Gen (LB.LinComb D₂.P.L (D₂.Oφ P₂ (q₂ χ)) Oinvε)), IsMonHom σ₁ → IsMonHom σ₂ → IsBoxGen (Y := G.left) (Y₁ := G₁.left) (Y₂ := G₂.left) w σ₁.left σ₂.left t t₁ t₂ → (Over.map s).map η[G] ≫ P = 1 → LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ t₁ (eSec G₁)) (LB.oneGen D₁.P.L) → LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ t₂ (eSec G₂)) (LB.oneGen D₂.P.L) → LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ t (eSec G)) (LB.oneGen D.P.L) := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ w S s G G₁ G₂ _ _ _ σ₁ σ₂ P P₁ P₂ χ t t₁ t₂ h₁ h₂ H e u₁ u₂
  refine corr_of_val D.P.isLB fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at D₂.P.isLB y
  have v := H _ (eSec G) y J₁ J₂ J hJ₁ hJ₂ hJ
  have o := prod_unit D ((Over.map s).map η[G]) P e χ (om w y J₁ J₂ J)
  have a₁ : eSec G ≫ σ₁.left = 𝟙 _ ≫ eSec G₁ := (SumDeg.eSec_comp σ₁).trans (Category.id_comp _).symm
  have a₂ : eSec G ≫ σ₂.left = 𝟙 _ ≫ eSec G₂ := (SumDeg.eSec_comp σ₂).trans (Category.id_comp _).symm
  have b₁ : val t₁ (eSec G ≫ σ₁.left) y J₁ = 1 := (congrArg (fun r => val t₁ r y J₁) a₁).trans
    ((val_pull hJ₁ _ _ _).symm.trans ((val_corr hJ₁ u₁ (𝟙 _)).trans (val_one _)))
  have b₂ : val t₂ (eSec G ≫ σ₂.left) y J₂ = 1 := (congrArg (fun r => val t₂ r y J₂) a₂).trans
    ((val_pull hJ₂ _ _ _).symm.trans ((val_corr hJ₂ u₂ (𝟙 _)).trans (val_one _)))
  have c : val t (eSec G) y J = 1 :=
    ((congrArg₂ (· * ·) o rfl).trans (_root_.one_mul _)).symm.trans
      (v.trans ((congrArg₂ (· * ·) b₁ b₂).trans (_root_.one_mul _)))
  exact (val_pull hJ _ _ _).trans ((congrArg (fun r => val t r y J) (Category.id_comp _)).trans
    (c.trans (val_one _).symm))

end GlobalTheory.ProdUnifUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegeneration
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegeneration
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem trF_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X → D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) (mu : D.X) :
    (DegPre.trF D F mu).left ≫ (TF (R := R) F ◁ p).left =
      (TF (R := R) F ◁ p).left ≫ (DegPre.trF D₁ F (q mu)).left := by
  refine congrArg (fun m => m.left) (?_ : DegPre.trF D F mu ≫ (TF (R := R) F ◁ p) =
    (TF (R := R) F ◁ p) ≫ DegPre.trF D₁ F (q mu))
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.trF]
  · rw [Category.assoc, Category.assoc, whiskerLeft_snd, DegPre.trF, DegPre.trF, lift_snd, lift_snd_assoc]
    have b : DegPre.prB D F ≫ p = (TF (R := R) F ◁ p) ≫ DegPre.prB D₁ F := (whiskerLeft_snd _ _).symm
    have e : (DegPre.prB D F * cP D _ mu) ≫ p = (TF (R := R) F ◁ p) ≫ (DegPre.prB D₁ F * cP D₁ _ (q mu)) := by
      rw [MonObj.mul_comp, MonObj.comp_mul, b, GlobalTheory.ProdUnif.cPoint_pr hc, comp_cP]
    exact e

theorem zF_pr {D D₁ : DegPre R} (p : D.P.A ⟶ D₁.P.A) [IsMonHom p] :
    (DegPre.zF D F).left ≫ (TF (R := R) F ◁ p).left = (DegPre.zF D₁ F).left := by
  refine congrArg (fun m => m.left) (?_ : DegPre.zF D F ≫ (TF (R := R) F ◁ p) = DegPre.zF D₁ F)
  apply CartesianMonoidalCategory.hom_ext
  · simp [DegPre.zF]
  · simp [DegPre.zF]

theorem deltaφ_pr {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X →+ D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) (k : ℕ) (α mu : D.X) (a : Fin 4 ⊕ Fin 4) :
    DegPre.deltaφ D F k α mu a ≫ p.left = (TF (R := R) F ◁ p).left ≫ DegPre.deltaφ D₁ F k (q α) (q mu) a := by
  rcases a with a | a
  · refine (GlobalTheory.ProdUnif.famφ_pr hc F (α + k • mu) a).trans ?_
    rw [map_add (f := _), map_nsmul]; rfl
  · show ((DegPre.trF D F mu).left ≫ DegPre.famφ D F α a) ≫ _ =
      _ ≫ (DegPre.trF D₁ F (q mu)).left ≫ DegPre.famφ D₁ F (q α) a
    rw [Category.assoc, GlobalTheory.ProdUnif.famφ_pr hc, ← Category.assoc, trF_pr F hc, Category.assoc]

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

section Values

variable {D D₁ D₂ : DegPre R} {p₁ : D.P.A ⟶ D₁.P.A} {p₂ : D.P.A ⟶ D₂.P.A} (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X)
  {w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)}

theorem famMult_box₂ (hrig : IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig)
    (hpsi : ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x)))
    (k : ℕ) (α mu : D.X) (y : (TF (R := R) F).left) {J₁ J₂ J}
    (hJ₁ : Good D₁.P.L y J₁) (hJ₂ : Good D₂.P.L y J₂) (hJ : Good D.P.L y J) :
    (∏ a, om w y J₁ J₂ J ((DegPre.zF D F).left ≫ DegPre.deltaφ D F k α mu a) ^ DegPre.deltaε k a) *
      val (Z := (TF (R := R) F).left) (DegPre.famMult D F k mu α) (𝟙 _) y J =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)) (𝟙 _) y J₁ *
        val (Z := (TF (R := R) F).left) (DegPre.famMult D₂ F k (q₂ mu) (q₂ α)) (𝟙 _) y J₂ := by
  have a₁ : ∀ χ, (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ D.xK χ = (cP D (TF (R := R) F) χ).left := fun χ =>
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have a₂ : (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left ≫ eSec D.P.A =
      (1 : TF (R := R) F ⟶ D.P.A).left :=
    (Category.assoc _ _ _).trans ((Category.id_comp _).trans (Category.assoc _ _ _).symm)
  have b₁ := fun χ => hpsi χ _ (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ J₂ J hJ₁ hJ₂ hJ
  have b₂ := hrig _ ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₁ J₂ J hJ₁ hJ₂ hJ
  simp only [Fintype.prod_unique, Category.comp_id] at b₁ b₂
  have r₀ : val D.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      val D.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J := val_pull hJ _ _ _
  have r₁ : val D₁.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ =
      val D₁.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₁ := val_pull hJ₁ _ _ _
  have r₂ : val D₂.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂ =
      val D₂.rig ((𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ (toUnit (TK R)).left) y J₂ := val_pull hJ₂ _ _ _
  have c₁ : ∀ χ, val (D.psi χ) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      om w y J₁ J₂ J (cP D (TF (R := R) F) χ).left *
        (val (D₁.psi (q₁ χ)) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ *
          val (D₂.psi (q₂ χ)) (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂) := fun χ => by
    have h := b₁ χ
    rw [zpow_neg_one, show (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) ≫ ptK (D.c χ) =
      (cP D (TF (R := R) F) χ).left from a₁ χ] at h
    exact inv_mul_eq_iff_eq_mul.1 h
  have c₂ : val D.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J =
      (om w y J₁ J₂ J (1 : TF (R := R) F ⟶ D.P.A).left)⁻¹ *
        (val D₁.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₁ *
          val D₂.rigK (𝟙 (TF (R := R) F).left ≫ jFK (R := R) F) y J₂) := by
    rw [r₀, r₁, r₂]
    rw [zpow_one, Category.assoc, a₂] at b₂
    exact eq_inv_mul_of_mul_eq b₂
  have c₃ := c₁ (mu + α)
  rw [map_add (f := _), map_add (f := _)] at c₃
  rw [GlobalTheory.BoxFamily.prod_delta_zero F D k α mu (om w y J₁ J₂ J), GlobalTheory.BoxFamily.famMult_val F hJ,
    GlobalTheory.BoxFamily.famMult_val F hJ₁, GlobalTheory.BoxFamily.famMult_val F hJ₂, c₃, c₁ mu, c₁ α, c₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
  module

end Values

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

variable {R : Type} [CommRing R] [IsDomain R] (F : Type) [Field F] [Algebra (FractionRing R) F]

theorem fe_along {D D₁ : DegPre R} {p : D.P.A ⟶ D₁.P.A} [IsMonHom p] {q : D.X →+ D₁.X}
    (hc : ∀ x, D.c x ≫ p = D₁.c (q x)) {k : ℕ} (E₁ : Fam D₁ F k) (mu α : D.X)
    (u₁ : LB.Gen (LB.LinComb D₁.P.L (DegPre.deltaφ D₁ F k (q α) (q mu)) (DegPre.deltaε k))) (hu₁ : u₁.IsGen)
    (hc₁ : LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ u₁ (DegPre.zF D₁ F).left)
      (DegPre.famMult D₁ F k (q mu) (q α)))
    {Z : Scheme.{0}} (r : Z ⟶ (DegPre.BF D F).left) (z : Z) {J₁} (hJ₁ : Good D₁.P.L z J₁) :
    sval (E₁.s (q (α + k • mu))) (r ≫ (TF (R := R) F ◁ p).left) z J₁ =
      sval (E₁.s (q α)) ((r ≫ (DegPre.trF D F mu).left) ≫ (TF (R := R) F ◁ p).left) z J₁ *
        (val u₁ (r ≫ (TF (R := R) F ◁ p).left) z J₁).val := by
  have h := (secRel_iff D₁.P.isLB _ _ _ _ _ _ _ _ _ u₁).1 (E₁.fe _ _ u₁ hu₁ hc₁) _
    (r ≫ (TF (R := R) F ◁ p).left) z J₁ hJ₁
  rw [map_add (f := _), map_nsmul, h, Category.assoc, Category.assoc, trF_pr F hc]

variable {D D₁ D₂ : DegPre R} {p₁ : D.P.A ⟶ D₁.P.A} {p₂ : D.P.A ⟶ D₂.P.A} {q₁ : D.X →+ D₁.X} {q₂ : D.X →+ D₂.X}
  {w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)}

theorem gen_box₂ (hS : IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂) (hw : w.IsGen)
    (hrig : IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig)
    (hpsi : ∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x))) (hG : GlobalFnsSt)
    (k : ℕ) (α mu : D.X)
    (u : LB.Gen (LB.LinComb D.P.L (DegPre.deltaφ D F k α mu) (DegPre.deltaε k))) (hu : u.IsGen)
    (hc : LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (DegPre.zF D F).left) (DegPre.famMult D F k mu α))
    (u₁ : LB.Gen (LB.LinComb D₁.P.L (DegPre.deltaφ D₁ F k (q₁ α) (q₁ mu)) (DegPre.deltaε k))) (hu₁ : u₁.IsGen)
    (hc₁ : LB.Gen.Corr D₁.P.L _ _ _ _ (LB.pullGen D₁.P.L _ _ u₁ (DegPre.zF D₁ F).left)
      (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)))
    (u₂ : LB.Gen (LB.LinComb D₂.P.L (DegPre.deltaφ D₂ F k (q₂ α) (q₂ mu)) (DegPre.deltaε k))) (hu₂ : u₂.IsGen)
    (hc₂ : LB.Gen.Corr D₂.P.L _ _ _ _ (LB.pullGen D₂.P.L _ _ u₂ (DegPre.zF D₂ F).left)
      (DegPre.famMult D₂ F k (q₂ mu) (q₂ α))) :
    IsBoxGen w (TF (R := R) F ◁ p₁).left (TF (R := R) F ◁ p₂).left u u₁ u₂ := by
  haveI := hS.hom₁
  haveI := hS.hom₂
  have z₁ : DegPre.zF D F ≫ fst _ _ = 𝟙 _ := lift_fst _ _
  refine isBoxGen_of_section w hw D₁.P.isLB D₂.P.isLB D.P.isLB (deltaφ_pr F hS.c_pr₁ k α mu)
    (deltaφ_pr F hS.c_pr₂ k α mu) hu hu₁ hu₂ (fst (TF (R := R) F) D.P.A).left (DegPre.zF D F).left
    (congrArg (fun q => q.left) z₁) (surj_appTop D F hG) ?_
  intro y J₁ J₂ J hJ₁ hJ₂ hJ
  have e := famMult_box₂ F q₁ q₂ hrig hpsi k α mu y hJ₁ hJ₂ hJ
  have v : val u (DegPre.zF D F).left y J =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D F k mu α) (𝟙 _) y J := by
    have h := val_corr hJ hc (𝟙 _)
    rwa [val_pull hJ, Category.id_comp] at h
  have v₁ : val u₁ ((DegPre.zF D F).left ≫ (TF (R := R) F ◁ p₁).left) y J₁ =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₁ F k (q₁ mu) (q₁ α)) (𝟙 _) y J₁ := by
    have h := val_corr hJ₁ hc₁ (𝟙 _)
    rw [val_pull hJ₁, Category.id_comp] at h
    rw [zF_pr]; exact h
  have v₂ : val u₂ ((DegPre.zF D F).left ≫ (TF (R := R) F ◁ p₂).left) y J₂ =
      val (Z := (TF (R := R) F).left) (DegPre.famMult D₂ F k (q₂ mu) (q₂ α)) (𝟙 _) y J₂ := by
    have h := val_corr hJ₂ hc₂ (𝟙 _)
    rw [val_pull hJ₂, Category.id_comp] at h
    rw [zF_pr]; exact h
  rw [v, v₁, v₂]
  exact e

end GlobalTheory.BoxFamSum

namespace GlobalTheory.BoxFamSum

theorem exists_isBoxFam₂ : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), w.IsGen → IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig → (∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x))) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (E₁ : Fam D₁ F k) (E₂ : Fam D₂ F k), ∃ E : Fam D F k, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k E E₁ E₂ := by
  intro R _ _ D D₁ D₂ p₁ p₂ q₁ q₂ hS w hw hrig hpsi F _ _ k E₁ E₂
  haveI := hS.hom₁
  haveI := hS.hom₂
  have hG : GlobalFnsSt := GlobalTheory.abelianSchemeLaws_all.1.globalFns
  choose s hs using fun α : D.X => exists_boxSec w hw D₁.P.isLB D₂.P.isLB D.P.isLB
    (GlobalTheory.ProdUnif.famφ_pr hS.c_pr₁ F α) (GlobalTheory.ProdUnif.famφ_pr hS.c_pr₂ F α) (E₁.s (q₁ α)) (E₂.s (q₂ α))
  refine ⟨⟨s, ?_⟩, hs⟩
  intro mu α u hu hc
  obtain ⟨u₁, hu₁, hc₁⟩ := (gen_fe (D := D₁) (F := F) hG k (q₁ mu) (q₁ α)).1
  obtain ⟨u₂, hu₂, hc₂⟩ := (gen_fe (D := D₂) (F := F) hG k (q₂ mu) (q₂ α)).1
  have hb := gen_box₂ F hS hw hrig hpsi hG k α mu u hu hc u₁ hu₁ hc₁ u₂ hu₂ hc₂
  refine (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ u).2 fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := GlobalTheory.BoxFamily.exists_good_at D₁.P.isLB y
  obtain ⟨J₂, hJ₂⟩ := GlobalTheory.BoxFamily.exists_good_at D₂.P.isLB y
  have e₁ := hs (α + k • mu) _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have e₂ := hs α _ (𝟙 _ ≫ (DegPre.trF D F mu).left) y J₁ J₂ J hJ₁ hJ₂ hJ
  have e₃ := hb _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have f₁ := fe_along F hS.c_pr₁ E₁ mu α u₁ hu₁ hc₁ (𝟙 _) y hJ₁
  have f₂ := fe_along F hS.c_pr₂ E₂ mu α u₂ hu₂ hc₂ (𝟙 _) y hJ₂
  have e₅ : (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.deltaφ D F k α mu a) ^ DegPre.deltaε k a) =
      (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.famφ D F (α + k • mu) a) ^ DegPre.famε k a) *
      (∏ a, om w y J₁ J₂ J ((𝟙 _ ≫ (DegPre.trF D F mu).left) ≫ DegPre.famφ D F α a) ^ DegPre.famε k a)⁻¹ := by
    simp only [Category.assoc]
    exact prod_sum₂ (K := Fin 4) (K' := Fin 4) _ rfl (prod_neg _ _ rfl)
  refine (∏ a, om w y J₁ J₂ J (𝟙 _ ≫ DegPre.famφ D F (α + k • mu) a) ^ DegPre.famε k a).mul_right_inj.1 ?_
  refine e₁.trans ?_
  rw [f₁, f₂]
  refine Eq.trans ?_ ((congrArg₂ (· * ·) e₂ (congrArg Units.val e₃)).symm.trans ?_)
  · rw [Units.val_mul]; ring
  · rw [e₅]; exact GlobalTheory.BoxFamily.unit_shuffle _ _ _ _

end GlobalTheory.BoxFamSum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBoxFamilyProductDegenerationStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_boxFamily_productDegeneration : ∀ (R : Type) [CommRing R] [IsDomain R] (D D₁ D₂ : DegPre R) (p₁ : D.P.A ⟶ D₁.P.A) (p₂ : D.P.A ⟶ D₂.P.A) (q₁ : D.X →+ D₁.X) (q₂ : D.X →+ D₂.X), IsSumDeg D D₁ D₂ p₁ p₂ q₁ q₂ → ∀ (w : LB.Iso D.P.L (extLB D₁.P.L D₂.P.L p₁.left p₂.left)), w.IsGen → IsBoxGen w (𝟙 _) (𝟙 _) D.rig D₁.rig D₂.rig → (∀ x, IsBoxGen w (𝟙 _) (𝟙 _) (D.psi x) (D₁.psi (q₁ x)) (D₂.psi (q₂ x))) → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ) (E₁ : Fam D₁ F k) (E₂ : Fam D₂ F k), ∃ E : Fam D F k, IsBoxFam₂ p₁ p₂ q₁ q₂ w F k E E₁ E₂ := by
  first | exact @GlobalTheory.BoxFamSum.exists_isBoxFam₂ | exact GlobalTheory.BoxFamSum.exists_isBoxFam₂ | (intros; apply GlobalTheory.BoxFamSum.exists_isBoxFam₂ <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExpBijOfBasisCard
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdUnif

theorem expBij_of_basis_card : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ), AdmBase R I → 1 ≤ k → ∀ (Λ : Type) [Fintype Λ] (b : Module.Basis Λ (FractionRing R) (Fam D.toPre (FractionRing R) k)) (σ : Λ → U.SecK k), Fintype.card Λ = k ^ A.g → (∀ l, U.Expands k (σ l) (b l)) → U.ExpBij k := by
  intro R _ _ I D A G _ _ U k hR hk Λ _ b σ hcard hσ
  classical
  obtain ⟨β, -, hβ⟩ := GlobalTheory.GenericSectionBasis.exists_secK_basis
    GlobalTheory.abelianSchemeLaws_all.1.secBaseChange R I D A G U k hk
  choose C hC using fun l => (hβ (σ l)).exists
  have hCc : ∀ l, GlobalTheory.UnifPowAdm.IsComb (pullback.snd G.hom (jK R)) (σ l) (C l) β := fun l jj => hC l jj
  let Φ : (Λ → FractionRing R) →ₗ[FractionRing R] (Fin (k ^ A.g) → FractionRing R) :=
    { toFun := fun c a => ∑ l, c l * C l a
      map_add' := fun c d => by funext a; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := fun r c => by
        funext a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _ }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    obtain ⟨s, hs⟩ := GlobalTheory.UnifPowAdm.exists_isComb (pullback.snd G.hom (jK R)) c σ
    have h1 := hs.trans hCc
    have hz : ∀ a, ∑ l, c l * C l a = 0 := fun a => congrFun hc a
    have h0 : ∀ jj, s.f jj = 0 := fun jj => by
      rw [h1 jj]
      simp [hz]
    have hE := GlobalTheory.UnifPowAdm.expands_comb U k hσ hs
    have h2 := GlobalTheory.ExpZero.main R I D A G U k hR s _ h0 hE
    exact funext fun l => Fintype.linearIndependent_iff.1 b.linearIndependent c h2 l
  have hsurj : Function.Surjective Φ := by
    rwa [← LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    simp [hcard]
  refine GlobalTheory.UnifPowAdm.expBij_of_basis U k hR b σ hσ fun s => ?_
  obtain ⟨d, hd, -⟩ := hβ s
  obtain ⟨c, rfl⟩ := hsurj d
  obtain ⟨s', hs'⟩ := GlobalTheory.UnifPowAdm.exists_isComb (pullback.snd G.hom (jK R)) c σ
  have e : s' = s := (hs'.trans hCc).unique fun jj => hd jj
  exact ⟨c, e ▸ hs'⟩

end GlobalTheory.ProdUnif
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibreProductSumPolarisedAbelianVari
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibreProductSumPolarisedAbelianVari
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif

namespace GlobalTheory.ProdGen

theorem isMonHom_of_lift {S : Scheme.{0}} {H A A₁ A₂ : Over S} [GrpObj H] [GrpObj A] [GrpObj A₁] [GrpObj A₂]
    (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsMonHom a₁] [IsMonHom a₂] [IsIso (lift a₁ a₂)] (f : H ⟶ A)
    [IsMonHom (f ≫ a₁)] [IsMonHom (f ≫ a₂)] : IsMonHom f := by
  have ext : ∀ {T : Over S} (a b : T ⟶ A), a ≫ a₁ = b ≫ a₁ → a ≫ a₂ = b ≫ a₂ → a = b :=
    fun a b h₁ h₂ => (cancel_mono (lift a₁ a₂)).1 (by rw [comp_lift, comp_lift, h₁, h₂])
  constructor
  · refine ext _ _ ?_ ?_ <;> rw [Category.assoc, IsMonHom.one_hom, IsMonHom.one_hom]
  · refine ext _ _ ?_ ?_ <;>
      rw [Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
        tensorHom_comp_tensorHom]

theorem exists_iso_prod {S S' : Scheme.{0}} (j : S' ⟶ S) (G₁ G₂ : Over S) {A A₁ A₂ : Over S'}
    (a₁ : A ⟶ A₁) (a₂ : A ⟶ A₂) [IsIso (lift a₁ a₂)] (e₁ : (Over.pullback j).obj G₁ ≅ A₁)
    (e₂ : (Over.pullback j).obj G₂ ≅ A₂) :
    ∃ e : (Over.pullback j).obj (G₁ ⊗ G₂) ≅ A,
      e.hom ≫ a₁ = (Over.pullback j).map (fst G₁ G₂) ≫ e₁.hom ∧
      e.hom ≫ a₂ = (Over.pullback j).map (snd G₁ G₂) ≫ e₂.hom := by
  have h₁ : inv (lift a₁ a₂) ≫ a₁ = fst A₁ A₂ := by rw [IsIso.inv_comp_eq, lift_fst]
  have h₂ : inv (lift a₁ a₂) ≫ a₂ = snd A₁ A₂ := by rw [IsIso.inv_comp_eq, lift_snd]
  refine ⟨prodComparisonIso (Over.pullback j) G₁ G₂ ≪≫ (e₁ ⊗ᵢ e₂) ≪≫ (asIso (lift a₁ a₂)).symm, ?_, ?_⟩
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, h₁, tensorIso_hom, tensorHom_fst,
      prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_fst_assoc]
  · simp only [Iso.trans_hom, Iso.symm_hom, asIso_inv, Category.assoc, h₂, tensorIso_hom, tensorHom_snd,
      prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_snd_assoc]


open GlobalTheory.CechPic in
theorem cls_extLB {X X₁ X₂ : Scheme.{0}} {L : LB X} {L₁ : LB X₁} {L₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
    (hL : L.IsLB) (h₁ : L₁.IsLB) (h₂ : L₂.IsLB) (w : LB.Iso L (extLB L₁ L₂ f₁ f₂)) (hw : w.IsGen) :
    cls L hL = pull f₁ (cls L₁ h₁) + pull f₂ (cls L₂ h₂) :=
  (cls_eq_iff hL (isLB_extLB h₁ h₂ f₁ f₂)).2 ⟨w, hw⟩


open GlobalTheory.CechPic in
theorem exists_gen_prod : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (A : PolAV (Sp (FractionRing R))) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ gen : (Over.pullback (jK R)).obj (G₁ ⊗ G₂) ≅ A.A, IsMonHom gen.hom ∧ gen.hom ≫ a₁ = (Over.pullback (jK R)).map (fst G₁ G₂) ≫ U₁.gen.hom ∧ gen.hom ≫ a₂ = (Over.pullback (jK R)).map (snd G₁ G₂) ≫ U₂.gen.hom ∧ ∀ (L : LB (G₁ ⊗ G₂).left) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → wL.IsGen → ∃ w : LB.Iso (A.L.pull gen.hom.left) (L.pull (pullback.fst (G₁ ⊗ G₂).hom (jK R))), w.IsGen := by
  intro R _ _ I D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ A a₁ a₂ hA
  haveI := hA.hom₁
  haveI := hA.hom₂
  haveI := hA.lim
  haveI := U₁.gen_hom
  haveI := U₂.gen_hom
  obtain ⟨e, e₁, e₂⟩ := exists_iso_prod (jK R) G₁ G₂ a₁ a₂ U₁.gen U₂.gen
  haveI : IsMonHom (e.hom ≫ a₁) := by rw [e₁]; infer_instance
  haveI : IsMonHom (e.hom ≫ a₂) := by rw [e₂]; infer_instance
  refine ⟨e, isMonHom_of_lift a₁ a₂ e.hom, e₁, e₂, fun L wL hL hwL => ?_⟩
  obtain ⟨wA, hwA⟩ := hA.w
  have cA := cls_extLB A.isLB A₁.isLB A₂.isLB wA hwA
  have cL := cls_extLB hL U₁.LG.isLB U₂.LG.isLB wL hwL
  have c₁ : pull U₁.gen.hom.left (cls _ A₁.isLB) = pull (pullback.fst G₁.hom (jK R)) (cls _ U₁.LG.isLB) :=
    (cls_eq_iff (pull_isLB A₁.isLB _) (pull_isLB U₁.LG.isLB _)).2 U₁.ext
  have c₂ : pull U₂.gen.hom.left (cls _ A₂.isLB) = pull (pullback.fst G₂.hom (jK R)) (cls _ U₂.LG.isLB) :=
    (cls_eq_iff (pull_isLB A₂.isLB _) (pull_isLB U₂.LG.isLB _)).2 U₂.ext
  have l₁ : e.hom.left ≫ a₁.left = ((Over.pullback (jK R)).map (fst G₁ G₂)).left ≫ U₁.gen.hom.left :=
    congrArg (fun z => z.left) e₁
  have l₂ : e.hom.left ≫ a₂.left = ((Over.pullback (jK R)).map (snd G₁ G₂)).left ≫ U₂.gen.hom.left :=
    congrArg (fun z => z.left) e₂
  have m₁ : ((Over.pullback (jK R)).map (fst G₁ G₂)).left ≫ pullback.fst G₁.hom (jK R) =
      pullback.fst (G₁ ⊗ G₂).hom (jK R) ≫ (fst G₁ G₂).left := pullback.lift_fst _ _ _
  have m₂ : ((Over.pullback (jK R)).map (snd G₁ G₂)).left ≫ pullback.fst G₂.hom (jK R) =
      pullback.fst (G₁ ⊗ G₂).hom (jK R) ≫ (snd G₁ G₂).left := pullback.lift_fst _ _ _
  have d₁ : pull e.hom.left (pull a₁.left (cls _ A₁.isLB)) =
      pull (pullback.fst (G₁ ⊗ G₂).hom (jK R)) (pull (fst G₁ G₂).left (cls _ U₁.LG.isLB)) :=
    (pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) l₁).trans ((pull_comp _ _ _).trans
      ((congrArg _ c₁).trans ((pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) m₁).trans
        (pull_comp _ _ _))))))
  have d₂ : pull e.hom.left (pull a₂.left (cls _ A₂.isLB)) =
      pull (pullback.fst (G₁ ⊗ G₂).hom (jK R)) (pull (snd G₁ G₂).left (cls _ U₂.LG.isLB)) :=
    (pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) l₂).trans ((pull_comp _ _ _).trans
      ((congrArg _ c₂).trans ((pull_comp _ _ _).symm.trans ((congrArg (fun f => pull f _) m₂).trans
        (pull_comp _ _ _))))))
  exact (cls_eq_iff (pull_isLB A.isLB _) (pull_isLB hL _)).1
    ((congrArg (pull e.hom.left) cA).trans ((map_add _ _ _).trans ((congrArg₂ (· + ·) d₁ d₂).trans
      ((map_add _ _ _).symm.trans (congrArg (pull (pullback.fst (G₁ ⊗ G₂).hom (jK R))) cL).symm))))

end GlobalTheory.ProdGen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenericFibreProductSumPolarisedAbelianVariStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd GlobalTheory.ProdUnif
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_genericFibre_product_sumPolarisedAbelianVariety : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D₁ : DegData R I) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : UnifPre I D₁ A₁ G₁) (D₂ : DegData R I) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : UnifPre I D₂ A₂ G₂) (A : PolAV (Sp (FractionRing R))) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ gen : (Over.pullback (jK R)).obj (G₁ ⊗ G₂) ≅ A.A, IsMonHom gen.hom ∧ gen.hom ≫ a₁ = (Over.pullback (jK R)).map (fst G₁ G₂) ≫ U₁.gen.hom ∧ gen.hom ≫ a₂ = (Over.pullback (jK R)).map (snd G₁ G₂) ≫ U₂.gen.hom ∧ ∀ (L : LB (G₁ ⊗ G₂).left) (wL : LB.Iso L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)), L.IsLB → wL.IsGen → ∃ w : LB.Iso (A.L.pull gen.hom.left) (L.pull (pullback.fst (G₁ ⊗ G₂).hom (jK R))), w.IsGen := by
  first | exact @GlobalTheory.ProdGen.exists_gen_prod | exact GlobalTheory.ProdGen.exists_gen_prod | (intros; apply GlobalTheory.ProdGen.exists_gen_prod <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationProductOfUniformisedGroups
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd

namespace GlobalTheory.ProdUnifExists

open GlobalTheory.ProdUnif

section Main

open ReciprocityTheory.ChartRestriction.G.DVR

section Generic

variable {X X₁ X₂ : Scheme.{0}} {M : LB X} {M₁ : LB X₁} {M₂ : LB X₂} {f₁ : X ⟶ X₁} {f₂ : X ⟶ X₂}
  {K : Type} [Fintype K] {ε : K → ℤ} {Y Y₁ Y₂ W W₁ W₂ : Scheme.{0}}
  {φ : K → (Y ⟶ X)} {φ₁ : K → (Y₁ ⟶ X₁)} {φ₂ : K → (Y₂ ⟶ X₂)} {ψ : K → (W ⟶ X)} {ψ₁ : K → (W₁ ⟶ X₁)}
  {ψ₂ : K → (W₂ ⟶ X₂)} {ρ₁ : Y ⟶ Y₁} {ρ₂ : Y ⟶ Y₂} {σ₁ : W ⟶ W₁} {σ₂ : W ⟶ W₂} {h : Y ⟶ W} {h₁ : Y₁ ⟶ W₁}
  {h₂ : Y₂ ⟶ W₂}

theorem corr_box (hM : M.IsLB) (hM₁ : M₁.IsLB) (hM₂ : M₂.IsLB) {w : LB.Iso M (extLB M₁ M₂ f₁ f₂)}
    (e : ∀ a, h ≫ ψ a = φ a) (e₁ : h ≫ σ₁ = ρ₁ ≫ h₁) (e₂ : h ≫ σ₂ = ρ₂ ≫ h₂)
    {s : LB.Gen (LB.LinComb M φ ε)} {s₁ : LB.Gen (LB.LinComb M₁ φ₁ ε)} {s₂ : LB.Gen (LB.LinComb M₂ φ₂ ε)}
    {t : LB.Gen (LB.LinComb M ψ ε)} {t₁ : LB.Gen (LB.LinComb M₁ ψ₁ ε)} {t₂ : LB.Gen (LB.LinComb M₂ ψ₂ ε)}
    (Hs : IsBoxGen w ρ₁ ρ₂ s s₁ s₂) (Ht : IsBoxGen w σ₁ σ₂ t t₁ t₂)
    (H₁ : LB.Gen.Corr M₁ _ _ _ _ (LB.pullGen M₁ _ _ t₁ h₁) s₁) (H₂ : LB.Gen.Corr M₂ _ _ _ _ (LB.pullGen M₂ _ _ t₂ h₂) s₂) :
    LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ t h) s := by
  refine corr_of_val hM fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at hM₂ y
  rw [val_pull hJ, Category.id_comp]
  have a := Hs _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have b := Ht _ h y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [e₁, e₂, ← val_pull hJ₁, ← val_pull hJ₂, val_corr hJ₁ H₁, val_corr hJ₂ H₂] at b
  simp only [Category.id_comp] at a
  simp only [e] at b
  exact mul_left_cancel (b.trans a.symm)

theorem secScal_box (hM : M.IsLB) (hM₁ : M₁.IsLB) (hM₂ : M₂.IsLB) {w : LB.Iso M (extLB M₁ M₂ f₁ f₂)}
    (e : ∀ a, h ≫ ψ a = φ a) (e₁ : h ≫ σ₁ = ρ₁ ≫ h₁) (e₂ : h ≫ σ₂ = ρ₂ ≫ h₂)
    {s : LB.Sec (LB.LinComb M φ ε)} {s₁ : LB.Sec (LB.LinComb M₁ φ₁ ε)} {s₂ : LB.Sec (LB.LinComb M₂ φ₂ ε)}
    {t : LB.Sec (LB.LinComb M ψ ε)} {t₁ : LB.Sec (LB.LinComb M₁ ψ₁ ε)} {t₂ : LB.Sec (LB.LinComb M₂ ψ₂ ε)}
    (Hs : IsBoxSec w ρ₁ ρ₂ s s₁ s₂) (Ht : IsBoxSec w σ₁ σ₂ t t₁ t₂)
    {R : Type} [CommRing R] {π : Y ⟶ Sp R} {π₁ : Y₁ ⟶ Sp R} {π₂ : Y₂ ⟶ Sp R} (c₁ : ρ₁ ≫ π₁ = π) (c₂ : ρ₂ ≫ π₂ = π)
    {r₁ r₂ : R} (H₁ : GeneratorPullback.SecScal M₁ φ₁ ε s₁ ψ₁ ε t₁ h₁ (scal π₁ r₁))
    (H₂ : GeneratorPullback.SecScal M₂ φ₂ ε s₂ ψ₂ ε t₂ h₂ (scal π₂ r₂)) :
    GeneratorPullback.SecScal M φ ε s ψ ε t h (scal π (r₁ * r₂)) := by
  refine BoxFamScalar.secScal_of_pointwise hM fun y J hJ => ?_
  obtain ⟨J₁, hJ₁⟩ := BoxFamily.exists_good_at hM₁ y
  obtain ⟨J₂, hJ₂⟩ := BoxFamily.exists_good_at hM₂ y
  have a := Hs _ (𝟙 _) y J₁ J₂ J hJ₁ hJ₂ hJ
  have b := Ht _ h y J₁ J₂ J hJ₁ hJ₂ hJ
  rw [e₁, e₂, BoxFamScalar.sval_of_secScal H₁ ρ₁ y hJ₁, BoxFamScalar.sval_of_secScal H₂ ρ₂ y hJ₂,
    BoxFamScalar.gs_scal π₁, BoxFamScalar.gs_scal π₂, c₁, c₂] at b
  simp only [Category.id_comp] at a ⊢
  simp only [e] at b
  have m : scal π (r₁ * r₂) = scal π r₁ * scal π r₂ := by simp only [scal, map_mul]
  rw [m, gs_mul _ y ⊤ trivial]
  refine (Units.mul_right_inj _).1 (b.trans ?_)
  rw [_root_.mul_mul_mul_comm, ← a, mul_left_comm]

end Generic

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ D : DegData R I}
  {A₁ A₂ A : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)}
  [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂]
  {p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A} {p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A} {q₁ : D.toPre.X →+ D₁.toPre.X}
  {q₂ : D.toPre.X →+ D₂.toPre.X} {a₁ : A.A ⟶ A₁.A} {a₂ : A.A ⟶ A₂.A}

theorem exists_gt (hD : IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂)
    (w : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)) (hw : w.IsGen)
    (hc : IsBoxGen (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (φ₁ := thφ D₁.toPre.P.A (x3 D₁.toPre.P.A))
      (φ₂ := thφ D₂.toPre.P.A (x3 D₂.toPre.P.A)) (ε := thε) w (p₁ ⊗ₘ p₁ ⊗ₘ p₁).left (p₂ ⊗ₘ p₂ ⊗ₘ p₂).left
      D.toPre.cub.t D₁.toPre.cub.t D₂.toPre.cub.t)
    (e : ℕ) (g₁ : GtCoord I D₁.toPre e G₁) (g₂ : GtCoord I D₂.toPre e G₂) :
    ∃ g : GtCoord I D.toPre e (G₁ ⊗ G₂),
      g.q ≫ (Over.pullback (thick R I e)).map p₁ = (Over.pullback (thick R I e)).map (fst G₁ G₂) ≫ g₁.q ∧
      g.q ≫ (Over.pullback (thick R I e)).map p₂ = (Over.pullback (thick R I e)).map (snd G₁ G₂) ≫ g₂.q ∧
      (∀ h : D₁.toPre.X → D.toPre.X, (∀ y, q₁ (h y) = y) → (∀ y, q₂ (h y) = 0) →
        ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₁.toPre.X,
          TorusHomOf h τ ∧ g.i ≫ (Over.pullback (thick R I e)).map (fst G₁ G₂) = τ ≫ g₁.i) ∧
      (∀ h : D₂.toPre.X → D.toPre.X, (∀ y, q₁ (h y) = 0) → (∀ y, q₂ (h y) = y) →
        ∃ τ : splitTorus (Sp (R ⧸ I ^ (e + 1))) D.toPre.X ⟶ splitTorus (Sp (R ⧸ I ^ (e + 1))) D₂.toPre.X,
          TorusHomOf h τ ∧ g.i ≫ (Over.pullback (thick R I e)).map (snd G₁ G₂) = τ ≫ g₂.i) ∧
      ∀ x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left)
        (Y₂ := (thickObj R I e G₂).left) w ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left
        ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left (g.t x) (g₁.t (q₁ x)) (g₂.t (q₂ x)) := by
  obtain ⟨q, i, q_hom, q_flat, q_surj, q_aff, i_hom, hker, hq₁, hq₂, hi₁, hi₂⟩ :=
    GlobalTheory.T.torusExtension_product_over_thickening_of_sumData R I e D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ G₁ G₂ g₁ g₂ hD
  have := hD.hom₁
  have := hD.hom₂
  have hp₁ := pG_pr hq₁
  have hp₂ := pG_pr hq₂
  choose t ht H using fun x : D.toPre.X => exists_boxGen w hw D₁.toPre.P.isLB D₂.toPre.P.isLB D.toPre.P.isLB
    (Oφ_pr hD.c_pr₁ hp₁ x) (Oφ_pr hD.c_pr₂ hp₂ x) (g₁.t (q₁ x)) (g₁.t_gen _) (g₂.t (q₂ x)) (g₂.t_gen _)
  have e₂ : (Over.map (thick R I e)).map η[thickObj R I e (G₁ ⊗ G₂)] ≫
      ((Over.map (thick R I e)).map q ≫ D.toPre.prBe I e) = 1 := by
    rw [← Category.assoc, ← Functor.map_comp, IsMonHom.one_hom]
    refine Over.OverMorphism.ext ((cubeMapOf (isGrpPullback_pullback D.toPre.P.A (thick R I e))).e_comm.trans ?_)
    show thick R I e ≫ η[D.toPre.P.A].left = (𝟙 _ ≫ thick R I e) ≫ η[D.toPre.P.A].left
    rw [Category.id_comp]
  have aq : ((fst (splitTorus _ D.toPre.X) (thickObj R I e (G₁ ⊗ G₂)) ≫ i) * snd _ _) ≫ q = snd _ _ ≫ q := by
    rw [MonObj.mul_comp, Category.assoc, hker.w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]
  have aO : (Over.map (thick R I e)).map (lift (fst (splitTorus _ D.toPre.X) (thickObj R I e (G₁ ⊗ G₂)) ≫ i)
        (snd _ _) ≫ μ[thickObj R I e (G₁ ⊗ G₂)]) ≫ ((Over.map (thick R I e)).map q ≫ D.toPre.prBe I e) =
      (Over.map (thick R I e)).map (snd (splitTorus _ D.toPre.X) (thickObj R I e (G₁ ⊗ G₂))) ≫
        ((Over.map (thick R I e)).map q ≫ D.toPre.prBe I e) := by
    rw [← Category.assoc, ← Functor.map_comp, ← Hom.mul_def, aq, Functor.map_comp, Category.assoc]
  choose j₁ hj₁ using fun y : D₁.toPre.X => hD.xsum.2 (y, 0)
  choose j₂ hj₂ using fun y : D₂.toPre.X => hD.xsum.2 (0, y)
  obtain ⟨τ₁, hτ₁, hκ₁⟩ := hi₁ j₁ (fun y => congrArg Prod.fst (hj₁ y)) (fun y => congrArg Prod.snd (hj₁ y))
  obtain ⟨τ₂, hτ₂, hκ₂⟩ := hi₂ j₂ (fun y => congrArg Prod.fst (hj₂ y)) (fun y => congrArg Prod.snd (hj₂ y))
  have hj : ∀ χ, j₁ (q₁ χ) + j₂ (q₂ χ) = χ := fun χ => hD.xsum.1 (by
    rw [map_add (f := _), hj₁, hj₂, Prod.mk_add_mk, add_zero, zero_add]; rfl)
  exact ⟨⟨q, q_hom, q_flat, q_surj, q_aff, i, i_hom, hker, t, ht,
    GlobalTheory.ProdUnif.tMul_of_box R _ _ _ p₁ p₂ q₁ q₂ hD w hc _ _ _ _ g₁.pG g₂.pG _ _ hp₁ hp₂ t g₁.t g₂.t H g₁.t_mul g₂.t_mul,
    fun χ => GlobalTheory.ProdUnifUnit.unit_box R _ _ _ p₁ p₂ q₁ q₂ w _ (thick R I e) _ _ _ _ _ _ g₁.pG g₂.pG χ (t χ) _ _ inferInstance
      inferInstance (H χ) e₂ (g₁.t_unit _) (g₂.t_unit _),
    fun χ => GlobalTheory.ProdUnifWeight.weight_box₂ R _ _ _ p₁ p₂ q₁ q₂ w _ (thick R I e) _ _ _ _ _ _ g₁.pG g₂.pG χ (t χ) _ _ inferInstance
      inferInstance (H χ) i g₁.i g₂.i j₁ j₂ τ₁ τ₂ (hj χ) hτ₁ hτ₂ hκ₁ hκ₂ aO (g₁.t_weight _) (g₂.t_weight _)⟩,
    hq₁, hq₂, hi₁, hi₂, H⟩

theorem thickMap_pG (hD : IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂) (U₁ : UnifPre I D₁ A₁ G₁)
    (U₂ : UnifPre I D₂ A₂ G₂) (gt : ∀ e, GtCoord I D.toPre e (G₁ ⊗ G₂))
    (h₁ : ∀ e, (gt e).pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left)
    (h₂ : ∀ e, (gt e).pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left) (e : ℕ) :
    thickMap R I e (G₁ ⊗ G₂) ≫ (gt (e + 1)).pG.left = (gt e).pG.left := by
  have := hD.lim
  have h : LevelCompat.thickMapOver I e (G₁ ⊗ G₂) ≫ (gt (e + 1)).pG = (gt e).pG := SumDeg.pt_ext p₁ p₂
    (Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (thickMap R I e (G₁ ⊗ G₂) ≫ ·) (h₁ (e + 1))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (U₁.gt (e + 1)).pG.left) (thickMap_nat I e (fst G₁ G₂))).trans
        ((Category.assoc _ _ _).trans ((congrArg (((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ ·) (U₁.gt_q e)).trans (h₁ e).symm)))))))
    (Over.OverMorphism.ext ((Category.assoc _ _ _).trans ((congrArg (thickMap R I e (G₁ ⊗ G₂) ≫ ·) (h₂ (e + 1))).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (U₂.gt (e + 1)).pG.left) (thickMap_nat I e (snd G₁ G₂))).trans
        ((Category.assoc _ _ _).trans ((congrArg (((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ ·) (U₂.gt_q e)).trans (h₂ e).symm)))))))
  exact congrArg (fun z => z.left) h


set_option maxHeartbeats 1600000 in
theorem exists_pre (hD : IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂) (hA : IsSumPolAV A A₁ A₂ a₁ a₂)
    (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂)
    (wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left))
    (hM : StrBox p₁ p₂ wM D.toPre.rig D₁.toPre.rig D₂.toPre.rig D.toPre.cub.t D₁.toPre.cub.t D₂.toPre.cub.t
      D.toPre.sym D₁.toPre.sym D₂.toPre.sym) :
    ∃ (U : UnifPre I D A (G₁ ⊗ G₂)) (wL : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)),
      IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂ ∧ wL.IsGen ∧
      (∀ e x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left)
        (Y₂ := (thickObj R I e G₂).left) wM ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left
        ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ((U.gt e).t x) ((U₁.gt e).t (q₁ x)) ((U₂.gt e).t (q₂ x))) ∧
      ∀ e, BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
        (T₂ := (thickObj R I e G₂).left) wM wL (U.w e) (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left
        ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left := by
  obtain ⟨wM_gen, mr, mc, ms⟩ := hM
  obtain ⟨gen, gen_hom, gen₁, gen₂, ext⟩ := GlobalTheory.T.exists_genericFibre_product_sumPolarisedAbelianVariety R I D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ A a₁ a₂ hA
  obtain ⟨L, c, s, wL, s_gen, s_rig, hwLgen, lr, lc, ls⟩ := GlobalTheory.T.exists_externalTensor_rigidified_cubical_product _ G₁ G₂ U₁.LG U₂.LG U₁.cubG U₂.cubG U₁.symG U₂.symG
    U₁.symG_gen U₂.symG_gen U₁.symG_rig U₂.symG_rig
  choose gt hq₁ hq₂ hi₁ hi₂ ht using fun e => exists_gt hD wM wM_gen mc e (U₁.gt e) (U₂.gt e)
  have hp₁ : ∀ e, (gt e).pG.left ≫ p₁.left = ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left ≫ (U₁.gt e).pG.left :=
    fun e => congrArg (fun z => z.left) (pG_pr (hq₁ e))
  have hp₂ : ∀ e, (gt e).pG.left ≫ p₂.left = ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ≫ (U₂.gt e).pG.left :=
    fun e => congrArg (fun z => z.left) (pG_pr (hq₂ e))
  choose w w_gen Q using fun e => GlobalTheory.T.exists_generating_boxProduct_of_restrictedIsos (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
    (T₂ := (thickObj R I e G₂).left) wM wL (U₁.w e) (U₂.w e) D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB L.isLB
    U₁.LG.isLB U₂.LG.isLB (hp₁ e) (hp₂ e) (thick_fstG I e _) (thick_fstG I e _) wM_gen hwLgen (U₁.w_gen e) (U₂.w_gen e)
  have gq := thickMap_pG hD U₁ U₂ gt hp₁ hp₂
  have := U₁.smooth
  have := U₂.smooth
  have := U₁.separated
  have := U₂.separated
  refine ⟨{
      smooth := inferInstanceAs (Smooth (pullback.fst G₁.hom G₂.hom ≫ G₁.hom))
      separated := inferInstanceAs (IsSeparated (pullback.fst G₁.hom G₂.hom ≫ G₁.hom))
      gen := gen
      gen_hom := gen_hom
      LG := L
      cubG := c
      symG := s
      symG_gen := s_gen
      symG_rig := s_rig
      ext := ext L.L wL L.isLB hwLgen
      gt := gt
      gt_q := gq
      gt_t := fun e χ => corr_box (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left)
        (Y₂ := (thickObj R I e G₂).left) (W := (thickObj R I (e + 1) (G₁ ⊗ G₂)).left)
        (W₁ := (thickObj R I (e + 1) G₁).left) (W₂ := (thickObj R I (e + 1) G₂).left)
        D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB (LevelCompat.thickMap_Oφ (gt e) (gt (e + 1)) (gq e) χ)
        (thickMap_nat I e _) (thickMap_nat I e _) (ht e χ) (ht (e + 1) χ) (U₁.gt_t e _) (U₂.gt_t e _)
      w := w
      w_gen := w_gen
      w_rig := fun e => GlobalTheory.ProdUnif.rigAlong_box (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
        (T₂ := (thickObj R I e G₂).left) wM wL (U₁.w e) (U₂.w e) D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB L.isLB
        U₁.LG.isLB U₂.LG.isLB (hp₁ e) (hp₂ e) (thick_fstG I e _) (thick_fstG I e _) (w e) (Q e)
        (eSec (thickObj R I e (G₁ ⊗ G₂))) (eSec (thickObj R I e G₁)) (eSec (thickObj R I e G₂)) (thick R I e)
        L.rig U₁.LG.rig U₂.LG.rig D.toPre.rig D₁.toPre.rig D₂.toPre.rig
        (BoxSymmetry.eSec_comp_hom ((Over.pullback (thick R I e)).map (fst G₁ G₂))) (BoxSymmetry.eSec_comp_hom ((Over.pullback (thick R I e)).map (snd G₁ G₂)))
        (UnifPullRig.eSec_fstG I e _) (UnifPullRig.eSec_pG I (gt e)) (UnifPullRig.eSec_fstG I e _)
        (UnifPullRig.eSec_pG I (U₁.gt e)) (UnifPullRig.eSec_fstG I e _) (UnifPullRig.eSec_pG I (U₂.gt e)) lr mr
        (U₁.w_rig e) (U₂.w_rig e)
      w_even := fun e => by
        have := (gt e).q_hom
        have := (U₁.gt e).q_hom
        have := (U₂.gt e).q_hom
        exact GlobalTheory.ProdUnif.even_box₂ (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
          (T₂ := (thickObj R I e G₂).left) wM wL (U₁.w e) (U₂.w e) D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB
          L.isLB U₁.LG.isLB U₂.LG.isLB (hp₁ e) (hp₂ e) (thick_fstG I e _) (thick_fstG I e _) (w e) (Q e)
          (ι[thickObj R I e (G₁ ⊗ G₂)]).left (ι[thickObj R I e G₁]).left (ι[thickObj R I e G₂]).left
          s U₁.symG U₂.symG D.toPre.sym D₁.toPre.sym D₂.toPre.sym
          (EvenPull.inv_left_comp ((Over.pullback (thick R I e)).map (fst G₁ G₂))) (EvenPull.inv_left_comp ((Over.pullback (thick R I e)).map (snd G₁ G₂)))
          (EvenPull.inv_fst _ (G₁ ⊗ G₂)) (EvenPull.inv_hom_fst _ _ (gt e).q) (EvenPull.inv_fst _ G₁)
          (EvenPull.inv_hom_fst _ _ (U₁.gt e).q) (EvenPull.inv_fst _ G₂) (EvenPull.inv_hom_fst _ _ (U₂.gt e).q) ls ms
          (U₁.w_even e) (U₂.w_even e)
      w_cub := fun e => GlobalTheory.T.thickeningProductIso_preserves_cubicalStructure R I D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ D p₁ p₂ q₁ q₂ hD wM L.L c.t wL L.isLB mc lc e (gt e) (hp₁ e)
        (hp₂ e) (w e) (Q e)
      w_compat := fun e => GlobalTheory.ProdUnif.compat_box₂ (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
        (T₂ := (thickObj R I e G₂).left) wM wL (U₁.w e) (U₂.w e) D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB L.isLB
        U₁.LG.isLB U₂.LG.isLB (hp₁ e) (hp₂ e) (thick_fstG I e _) (thick_fstG I e _) (w e) (Q e)
        (T' := (thickObj R I (e + 1) (G₁ ⊗ G₂)).left) (T₁' := (thickObj R I (e + 1) G₁).left)
        (T₂' := (thickObj R I (e + 1) G₂).left) (w (e + 1)) (U₁.w (e + 1)) (U₂.w (e + 1)) (Q (e + 1))
        (thickMap R I e (G₁ ⊗ G₂)) (thickMap R I e G₁) (thickMap R I e G₂) (thickMap_nat I e _) (thickMap_nat I e _)
        (UnifPullRig.thickMap_fstG I e _) (gq e) (UnifPullRig.thickMap_fstG I e _) (U₁.gt_q e)
        (UnifPullRig.thickMap_fstG I e _) (U₂.gt_q e) (U₁.w_compat e) (U₂.w_compat e) },
    wL, ⟨gen₁, gen₂, ⟨wL, hwLgen⟩, hq₁, hq₂, hi₁, hi₂⟩, hwLgen, ht, Q⟩


set_option maxHeartbeats 1600000 in
theorem expands_box (hD : IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂)
    {U₁ : UnifPre I D₁ A₁ G₁} {U₂ : UnifPre I D₂ A₂ G₂} {U : UnifPre I D A (G₁ ⊗ G₂)}
    {wM : LB.Iso D.toPre.P.L (extLB D₁.toPre.P.L D₂.toPre.P.L p₁.left p₂.left)} (hwM : wM.IsGen)
    {wL : LB.Iso U.LG.L (extLB U₁.LG.L U₂.LG.L (fst G₁ G₂).left (snd G₁ G₂).left)} (hwL : wL.IsGen)
    (hU : IsProdUnif U₁ U₂ U p₁ p₂ q₁ q₂ a₁ a₂)
    (ht : ∀ e x, IsBoxGen (Y := (thickObj R I e (G₁ ⊗ G₂)).left) (Y₁ := (thickObj R I e G₁).left)
        (Y₂ := (thickObj R I e G₂).left) wM ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left
        ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left ((U.gt e).t x) ((U₁.gt e).t (q₁ x)) ((U₂.gt e).t (q₂ x)))
    (Q : ∀ e, BoxSq (T := (thickObj R I e (G₁ ⊗ G₂)).left) (T₁ := (thickObj R I e G₁).left)
        (T₂ := (thickObj R I e G₂).left) wM wL (U.w e) (U₁.w e) (U₂.w e) ((Over.pullback (thick R I e)).map (fst G₁ G₂)).left
        ((Over.pullback (thick R I e)).map (snd G₁ G₂)).left) {k : ℕ} {s : U.SecK k} {s₁ : U₁.SecK k} {s₂ : U₂.SecK k}
    (hs : IsBoxSec (Y := pullback (G₁ ⊗ G₂).hom (jK R)) (Y₁ := pullback G₁.hom (jK R)) (Y₂ := pullback G₂.hom (jK R))
      wL ((Over.pullback (jK R)).map (fst G₁ G₂)).left ((Over.pullback (jK R)).map (snd G₁ G₂)).left s s₁ s₂)
    {E : Fam D.toPre (FractionRing R) k} {E₁ : Fam D₁.toPre (FractionRing R) k} {E₂ : Fam D₂.toPre (FractionRing R) k}
    (hE : IsBoxFam₂ p₁ p₂ q₁ q₂ wM (FractionRing R) k E E₁ E₂) (H₁ : U₁.Expands k s₁ E₁) (H₂ : U₂.Expands k s₂ E₂) :
    U.Expands k s E := by
  obtain ⟨r₁, hr₁, σ₁, f₁, a₁, b₁, c₁⟩ := H₁
  obtain ⟨r₂, hr₂, σ₂, f₂, a₂, b₂, c₂⟩ := H₂
  have := hD.hom₁
  have := hD.hom₂
  obtain ⟨σ, hσ⟩ := exists_boxSec (φ := fun _ : Fin 1 => 𝟙 (G₁ ⊗ G₂).left) (h₁ := (fst G₁ G₂).left)
    (h₂ := (snd G₁ G₂).left) wL hwL U₁.LG.isLB U₂.LG.isLB U.LG.isLB
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm)
    (fun _ => (Category.id_comp _).trans (Category.comp_id _).symm) σ₁ σ₂
  choose f hf using fun α => exists_boxSec wM hwM D₁.toPre.P.isLB D₂.toPre.P.isLB D.toPre.P.isLB
    (famφB_pr hD.c_pr₁ α) (famφB_pr hD.c_pr₂ α) (f₁ (q₁ α)) (f₂ (q₂ α))
  refine ⟨r₁ * r₂, mul_ne_zero hr₁ hr₂, σ, f, ?_, fun α => ?_, fun e => ?_⟩
  · refine secScal_box U.LG.isLB U₁.LG.isLB U₂.LG.isLB (fun _ => Category.comp_id _)
      (pullback.lift_fst _ _ _).symm (pullback.lift_fst _ _ _).symm hs hσ ?_ ?_ a₁ a₂
    · exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (Over.w ((Over.pullback (jK R)).map (fst G₁ G₂))))
    · exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ jK R) (Over.w ((Over.pullback (jK R)).map (snd G₁ G₂))))
  · refine secScal_box D.toPre.P.isLB D₁.toPre.P.isLB D₂.toPre.P.isLB (fun a => ?_)
      (congrArg (fun m => m.left) (whiskerLeft_snd (TF (R := R) (FractionRing R)) p₁).symm)
      (congrArg (fun m => m.left) (whiskerLeft_snd (TF (R := R) (FractionRing R)) p₂).symm) (hE α) (hf α)
      (Over.w _) (Over.w _) (b₁ _) (b₂ _)
    fin_cases a
    · exact Category.comp_id _
    · refine congrArg (fun m : DegPre.BF D.toPre (FractionRing R) ⟶ D.toPre.P.A => m.left)
        (?_ : DegPre.prB D.toPre (FractionRing R) ≫ (𝟙 _ * cP D.toPre _ α) =
          DegPre.prB D.toPre (FractionRing R) * cP D.toPre _ α)
      rw [MonObj.comp_mul, Category.comp_id, comp_cP]
    · exact congrArg (fun m => m.left) (comp_cP D.toPre (DegPre.prB D.toPre (FractionRing R)) α)
    · exact congrArg (fun m : DegPre.BF D.toPre (FractionRing R) ⟶ D.toPre.P.A => m.left)
        (MonObj.comp_one (M := D.toPre.P.A) (DegPre.prB D.toPre (FractionRing R)))
  · exact GlobalTheory.T.expansionModIdealPow_boxProduct_eq_boxProduct R I D₁ A₁ G₁ U₁ D₂ A₂ G₂ U₂ D p₁ p₂ q₁ q₂ A U hD.xsum wM wL e k
      (congrArg (fun z => z.left) (pG_pr (hU.q_pr₁ e))) (congrArg (fun z => z.left) (pG_pr (hU.q_pr₂ e))) (ht e) (Q e)
      σ σ₁ σ₂ f f₁ f₂ hσ hf (c₁ e) (c₂ e)

theorem exists_unif (hR : AdmBase R I) (hD : IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂)
    (hA : IsSumPolAV A A₁ A₂ a₁ a₂) (U₁ : Unif I D₁ A₁ G₁) (U₂ : Unif I D₂ A₂ G₂) :
    ∃ U : Unif I D A (G₁ ⊗ G₂), IsProdUnif U₁.toUnifPre U₂.toUnifPre U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ := by
  obtain ⟨wM, hM, hψ⟩ := GlobalTheory.ProdUnif.exists_strBox_of_isSumDeg R _ _ _ p₁ p₂ q₁ q₂ hD
  obtain ⟨U, wL, hU, hwL, ht, Q⟩ := exists_pre hD hA U₁.toUnifPre U₂.toUnifPre wM hM
  refine ⟨⟨U, fun k hk => ?_⟩, hU⟩
  classical
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hf₁, hd₁⟩ := GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D₁ (FractionRing R) k hk
  obtain ⟨hf₂, hd₂⟩ := GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D₂ (FractionRing R) k hk
  obtain ⟨hf, hd⟩ := GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) k hk
  have hg := GlobalTheory.ProdDim.g_eq_add _ D.toPre.P D₁.toPre.P D₂.toPre.P p₁ p₂ inferInstance hD.lim
  have hg' := GlobalTheory.ProdDim.g_eq_add _ A A₁ A₂ a₁ a₂ inferInstance hA.lim
  have hr : D.toPre.rank = D₁.toPre.rank + D₂.toPre.rank := by
    show Module.finrank ℤ D.toPre.X = Module.finrank ℤ D₁.toPre.X + Module.finrank ℤ D₂.toPre.X
    rw [(AddEquiv.ofBijective _ hD.xsum).toIntLinearEquiv.finrank_eq, Module.finrank_prod]
  have n₁ := GlobalTheory.ProdUnif.famDim_of_expBij R I D₁ A₁ G₁ U₁.toUnifPre k hk (U₁.expand k hk)
  have n₂ := GlobalTheory.ProdUnif.famDim_of_expBij R I D₂ A₂ G₂ U₂.toUnifPre k hk (U₂.expand k hk)
  let b₁ := Module.finBasisOfFinrankEq (FractionRing R) (Fam D₁.toPre (FractionRing R) k) n₁
  let b₂ := Module.finBasisOfFinrankEq (FractionRing R) (Fam D₂.toPre (FractionRing R) k) n₂
  choose σ₁ hσ₁ using fun l => ((U₁.expand k hk).2 (b₁ l)).exists
  choose σ₂ hσ₂ using fun l => ((U₂.expand k hk).2 (b₂ l)).exists
  choose b hb using fun a : Fin (k ^ A₁.g) × Fin (k ^ A₂.g) =>
    GlobalTheory.T.exists_boxFamily_productDegeneration R _ _ _ p₁ p₂ q₁ q₂ hD wM hM.1 hM.2.1 hψ (FractionRing R) k (b₁ a.1) (b₂ a.2)
  choose σ hσ using fun a : Fin (k ^ A₁.g) × Fin (k ^ A₂.g) =>
    exists_boxSec (Y := pullback (G₁ ⊗ G₂).hom (jK R)) (Y₁ := pullback G₁.hom (jK R)) (Y₂ := pullback G₂.hom (jK R))
      (φ := fun _ : Fin 1 => pullback.fst (G₁ ⊗ G₂).hom (jK R))
      (h₁ := ((Over.pullback (jK R)).map (fst G₁ G₂)).left) (h₂ := ((Over.pullback (jK R)).map (snd G₁ G₂)).left)
      wL hwL U₁.LG.isLB U₂.LG.isLB U.LG.isLB (fun _ => (pullback.lift_fst _ _ _).symm)
      (fun _ => (pullback.lift_fst _ _ _).symm) (σ₁ a.1) (σ₂ a.2)
  have hli := GlobalTheory.T.boxFamily_linearIndependent_productDegeneration R _ _ _ p₁ p₂ q₁ q₂ hD wM (FractionRing R) k _ _ b₁ b₂ b b₁.linearIndependent
    b₂.linearIndependent hb
  have hc : Fintype.card (Fin (k ^ A₁.g) × Fin (k ^ A₂.g)) = k ^ A₁.g * k ^ A₂.g := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  have hcard : Fintype.card (Fin (k ^ A₁.g) × Fin (k ^ A₂.g)) =
      Module.finrank (FractionRing R) (Fam D.toPre (FractionRing R) k) := by
    rw [hc, ← n₁, ← n₂, hd, hd₁, hd₂, hr, hg, ← pow_add, add_add_add_comm]
  haveI : Nonempty (Fin (k ^ A₁.g) × Fin (k ^ A₂.g)) := ⟨⟨0, pow_pos hk _⟩, ⟨0, pow_pos hk _⟩⟩
  refine GlobalTheory.ProdUnif.expBij_of_basis_card R I D A _ U k hR hk _ (basisOfLinearIndependentOfCardEqFinrank hli hcard) σ
    (by rw [hc, hg', pow_add]) (fun a => ?_)
  rw [coe_basisOfLinearIndependentOfCardEqFinrank]
  exact expands_box hD hM.1 hwL hU ht Q (hσ a) (hb a) (hσ₁ _) (hσ₂ _)

end Main

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), IsProdUnif U₁.toUnifPre U₂.toUnifPre U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ := by
  intro R _ _ _ hR D₁ A₁ G₁ _ _ U₁ D₂ A₂ G₂ _ _ U₂ D A p₁ p₂ q₁ q₂ a₁ a₂ hD hA
  exact exists_unif hR.1 hD hA U₁ U₂

end GlobalTheory.ProdUnifExists
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationProductOfUniformisedGroupsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Mum
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MumFam GlobalTheory.MumProd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_product_of_uniformisedGroups : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D₁ : DegData R (maximalIdeal R)) (A₁ : PolAV (Sp (FractionRing R))) (G₁ : Over (Sp R)) [GrpObj G₁] [IsCommMonObj G₁] (U₁ : Unif (maximalIdeal R) D₁ A₁ G₁) (D₂ : DegData R (maximalIdeal R)) (A₂ : PolAV (Sp (FractionRing R))) (G₂ : Over (Sp R)) [GrpObj G₂] [IsCommMonObj G₂] (U₂ : Unif (maximalIdeal R) D₂ A₂ G₂) (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (p₁ : D.toPre.P.A ⟶ D₁.toPre.P.A) (p₂ : D.toPre.P.A ⟶ D₂.toPre.P.A) (q₁ : D.toPre.X →+ D₁.toPre.X) (q₂ : D.toPre.X →+ D₂.toPre.X) (a₁ : A.A ⟶ A₁.A) (a₂ : A.A ⟶ A₂.A), IsSumDeg D.toPre D₁.toPre D₂.toPre p₁ p₂ q₁ q₂ → IsSumPolAV A A₁ A₂ a₁ a₂ → ∃ U : Unif (maximalIdeal R) D A (G₁ ⊗ G₂), IsProdUnif U₁.toUnifPre U₂.toUnifPre U.toUnifPre p₁ p₂ q₁ q₂ a₁ a₂ := by
  first | exact @GlobalTheory.ProdUnifExists.main | exact GlobalTheory.ProdUnifExists.main | (intros; apply GlobalTheory.ProdUnifExists.main <;> assumption)
end
