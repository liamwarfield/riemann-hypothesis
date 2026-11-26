module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSchemeMapOfProjectiveCoordinates
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleIdentityIso
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFiniteTorusExtensionOfModel
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLieCoordinatesLieMultIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CmTypeEigenMultiplicityOfDensePrimes

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.WeilPull

open GlobalTheory.CommPairing

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {k : ℤ}

theorem exists_psi_inv [IsIso τ] : ∃ χ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left,
    (psiO hp τ hτ).left ≫ χ = 𝟙 (T ⊗ A).left ∧ χ ≫ (psiO hp τ hτ).left = 𝟙 _ := by
  have w₁ : (snd T₀ G).left ≫ G.hom = ((fst T₀ G).left ≫ inv τ ≫ T.hom) ≫ f := by
    rw [Over.w, Category.assoc, Category.assoc, ← hτ, IsIso.inv_hom_id_assoc, Over.w]
  let a : (T₀ ⊗ G).left ⟶ A.left := hp.1.lift _ _ w₁
  have a₁ : a ≫ φ = (snd T₀ G).left := hp.1.lift_fst _ _ _
  have a₂ : a ≫ A.hom = (fst T₀ G).left ≫ inv τ ≫ T.hom := hp.1.lift_snd _ _ _
  let χ : (T₀ ⊗ G).left ⟶ (T ⊗ A).left :=
    pullback.lift ((fst T₀ G).left ≫ inv τ) a (by rw [a₂, Category.assoc])
  have c₁ : χ ≫ (fst T A).left = (fst T₀ G).left ≫ inv τ := pullback.lift_fst _ _ _
  have c₂ : χ ≫ (snd T A).left = a := pullback.lift_snd _ _ _
  have p₁ := psi_fst hp τ hτ
  have p₂ := psi_snd hp τ hτ
  refine ⟨χ, ?_, ?_⟩
  · refine pullback.hom_ext (f := T.hom) (g := A.hom) ?_ ?_
    · show (_ ≫ χ) ≫ (fst T A).left = 𝟙 _ ≫ (fst T A).left
      rw [Category.assoc, c₁, ← Category.assoc, p₁, Category.assoc, IsIso.hom_inv_id, Category.id_comp,
        Category.comp_id]
    · show (_ ≫ χ) ≫ (snd T A).left = 𝟙 _ ≫ (snd T A).left
      rw [Category.assoc, c₂, Category.id_comp]
      refine hp.1.hom_ext ?_ ?_
      · rw [Category.assoc, a₁, p₂]
      · rw [Category.assoc, a₂, ← Category.assoc, p₁, Category.assoc, IsIso.hom_inv_id_assoc, Over.w, Over.w]
  · refine pullback.hom_ext (f := T₀.hom) (g := G.hom) ?_ ?_
    · show (χ ≫ _) ≫ (fst T₀ G).left = 𝟙 _ ≫ (fst T₀ G).left
      rw [Category.assoc, p₁, ← Category.assoc, c₁, Category.assoc, IsIso.inv_hom_id, Category.id_comp,
        Category.comp_id]
    · show (χ ≫ _) ≫ (snd T₀ G).left = 𝟙 _ ≫ (snd T₀ G).left
      rw [Category.assoc, p₂, ← Category.assoc, c₂, a₁, Category.id_comp]

def Rel (w : LB.Iso L₁ (L₀.pull φ)) (θ : ThetaGrp A L₁ k T) (θ₀ : ThetaGrp G L₀ k T₀) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J₀) (J), Good L₀ z J₀ → Good L₁ z J →
    tval θ₀ (r ≫ (psiO hp τ hτ).left) z J₀ =
      (gw w (r ≫ (snd T A).left) z (J₀ ((r ≫ (snd T A).left) ≫ φ)) (J (r ≫ (snd T A).left)) ^ k *
        gw w (r ≫ (translPt A θ.pt).left) z (J₀ ((r ≫ (translPt A θ.pt).left) ≫ φ))
          (J (r ≫ (translPt A θ.pt).left)) ^ (-k)) * tval θ r z J

theorem exists_rel_down (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen)
    (x : T ⟶ A) (θ₀ : ThetaGrp G L₀ k T₀) (hx : τ ≫ θ₀.pt.left = x.left ≫ φ) :
    ∃ θ : ThetaGrp A L₁ k T, θ.pt = x ∧ Rel hp τ hτ w θ θ₀ := by
  obtain ⟨θ, rfl, m⟩ := exists_theta_move hp τ hτ hL₀ hL₁ w hw k x θ₀ hx
  refine ⟨θ, rfl, fun Z r z J₀ J hG hJ => ?_⟩
  have e₀ : (r ≫ (psiO hp τ hτ).left) ≫ (snd T₀ G).left = (r ≫ (snd T A).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, psi_snd]
  have e₁ : (r ≫ (psiO hp τ hτ).left) ≫ (translPt G θ₀.pt).left = (r ≫ (translPt A θ.pt).left) ≫ φ := by
    rw [Category.assoc, Category.assoc, psi_tr hp τ hτ _ _ hx]
  have e : ∀ i, (r ≫ (psiO hp τ hτ).left) ≫ ![(snd T₀ G).left, (translPt G θ₀.pt).left] i =
      (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i) ≫ φ := fun i => by
    fin_cases i
    · exact e₀
    · exact e₁
  calc tval θ₀ (r ≫ (psiO hp τ hτ).left) z J₀ = _ :=
        m _ r z _ (fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i)) (fun i => by
          show _ ∈ L₀.U (J₀ ((r ≫ (psiO hp τ hτ).left) ≫ _))
          rw [e i]; exact hG _) (fun i => hJ _)
    _ = _ := by
      congr 1
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [e₀, e₁]

theorem exists_rel_up [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ)) (hw : w.IsGen)
    (x₀ : T₀ ⟶ G) (θ : ThetaGrp A L₁ k T) (hx : τ ≫ x₀.left = θ.pt.left ≫ φ) :
    ∃ θ₀ : ThetaGrp G L₀ k T₀, θ₀.pt = x₀ ∧ Rel hp τ hτ w θ θ₀ := by
  obtain ⟨χ, h₁, h₂⟩ := exists_psi_inv hp τ hτ
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hL₀ hL₁
    (φ' := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ θ.isGen
  have e₀ : χ ≫ (snd T A).left ≫ φ = (snd T₀ G).left := by
    rw [← psi_snd hp τ hτ, ← Category.assoc, h₂, Category.id_comp]
  have e₁ : χ ≫ (translPt A θ.pt).left ≫ φ = (translPt G x₀).left := by
    rw [← psi_tr hp τ hτ _ _ hx, ← Category.assoc, h₂, Category.id_comp]
  obtain ⟨u, hu, hu'⟩ := exists_gen hL₀ (φ' := ![(snd T₀ G).left, (translPt G x₀).left]) (ε' := ![k, -k])
    (fun U _ g => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg (fun q => g q ^ k) e₀
      · exact congrArg (fun q => g q ^ (-k)) e₁)
    (LB.pullGen L₀ _ _ t χ) (DVR.pullGen_isGen _ _ _ _ ht _)
  refine ⟨⟨x₀, u, hu⟩, rfl, fun Z r z J₀ J hG hJ => ?_⟩
  have e : (r ≫ (psiO hp τ hτ).left) ≫ χ = r := by
    rw [Category.assoc]; exact (congrArg (r ≫ ·) h₁).trans (Category.comp_id _)
  refine ((hu' Z _ z J₀ hG).trans ((val_pull hG _ _ _).trans (congrArg (fun q => val t q z J₀) e))).trans ?_
  refine (hv Z r z _ _ (hG.mem _ r) (hJ.mem _ r)).trans ?_
  congr 1
  simp only [pw, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Category.assoc]

theorem transl_commute {x y : T ⟶ A} (h : x * y = y * x) :
    (translT A x).left ≫ (translPt A y).left = (translT A y).left ≫ (translPt A x).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  show translT A x ≫ ((fst T A ≫ y) * snd T A) = translT A y ≫ ((fst T A ≫ x) * snd T A)
  rw [MonObj.comp_mul, MonObj.comp_mul, translT, translT, lift_snd, lift_snd, ← Category.assoc, ← Category.assoc,
    lift_fst, lift_fst]
  show (fst T A ≫ y) * ((fst T A ≫ x) * snd T A) = (fst T A ≫ x) * ((fst T A ≫ y) * snd T A)
  rw [← _root_.mul_assoc, ← _root_.mul_assoc, ← MonObj.comp_mul, ← MonObj.comp_mul, h]

theorem cancel_iff {M : Type*} [CommGroup M] (P X Y Z a b c d C : M) :
    (P * X⁻¹ * a) * (X * Z⁻¹ * b) = (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C ↔ a * b = c * d * C := by
  have e₁ : (P * X⁻¹ * a) * (X * Z⁻¹ * b) = (P * Z⁻¹) * (a * b) := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  have e₂ : (P * Y⁻¹ * c) * (Y * Z⁻¹ * d) * C = (P * Z⁻¹) * (c * d * C) := by
    apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel
  rw [e₁, e₂, mul_right_inj]

theorem commIsOf_iff_of_rel [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (w : LB.Iso L₁ (L₀.pull φ))
    {θx θy : ThetaGrp A L₁ k T} {θx₀ θy₀ : ThetaGrp G L₀ k T₀} (hc : θx.pt * θy.pt = θy.pt * θx.pt)
    (hx : τ ≫ θx₀.pt.left = θx.pt.left ≫ φ) (hy : τ ≫ θy₀.pt.left = θy.pt.left ≫ φ)
    (mx : Rel hp τ hτ w θx θx₀) (my : Rel hp τ hτ w θy θy₀) (c₀ : Γ(T₀.left, ⊤)ˣ) (c : Γ(T.left, ⊤)ˣ)
    (hcc : ∀ (Z : Scheme.{0}) (r : Z ⟶ T.left) (z : Z), gm (r ≫ τ) z ⊤ c₀ = gm r z ⊤ c) :
    CommIsOf A L₁ k θx θy c ↔ CommIsOf G L₀ k θx₀ θy₀ c₀ := by
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J₀) (J), Good L₀ z J₀ → Good L₁ z J →
      (tval θx₀ (r ≫ (psiO hp τ hτ).left) z J₀ *
          tval θy₀ ((r ≫ (psiO hp τ hτ).left) ≫ (translT G θx₀.pt).left) z J₀ =
        tval θy₀ (r ≫ (psiO hp τ hτ).left) z J₀ *
          tval θx₀ ((r ≫ (psiO hp τ hτ).left) ≫ (translT G θy₀.pt).left) z J₀ *
          gm ((r ≫ (psiO hp τ hτ).left) ≫ (fst T₀ G).left) z ⊤ c₀ ↔
      tval θx r z J * tval θy (r ≫ (translT A θx.pt).left) z J =
        tval θy r z J * tval θx (r ≫ (translT A θy.pt).left) z J * gm (r ≫ (fst T A).left) z ⊤ c) := by
    intro Z r z J₀ J hG hJ
    have t : ∀ (x : T ⟶ A) (x₀ : T₀ ⟶ G), τ ≫ x₀.left = x.left ≫ φ →
        (r ≫ (psiO hp τ hτ).left) ≫ (translT G x₀).left = (r ≫ (translT A x).left) ≫ (psiO hp τ hτ).left :=
      fun x x₀ h => by rw [Category.assoc, Category.assoc, psi_transl hp τ hτ _ _ h]
    have g : gm ((r ≫ (psiO hp τ hτ).left) ≫ (fst T₀ G).left) z ⊤ c₀ = gm (r ≫ (fst T A).left) z ⊤ c := by
      rw [Category.assoc, psi_fst, ← Category.assoc, hcc]
    have s : ∀ x : T ⟶ A, (r ≫ (translT A x).left) ≫ (snd T A).left = r ≫ (translPt A x).left := fun x => by
      rw [Category.assoc, ← Over.comp_left, translT, lift_snd]
    have q : (r ≫ (translT A θx.pt).left) ≫ (translPt A θy.pt).left =
        (r ≫ (translT A θy.pt).left) ≫ (translPt A θx.pt).left := by
      rw [Category.assoc, Category.assoc, transl_commute hc]
    rw [t _ _ hx, t _ _ hy, g, mx Z _ z J₀ J hG hJ, mx Z _ z J₀ J hG hJ, my Z _ z J₀ J hG hJ, my Z _ z J₀ J hG hJ,
      s, s, q]
    simp only [zpow_neg]
    exact cancel_iff _ _ _ _ _ _ _ _ _
  rw [commIsOf_iff hL₀, commIsOf_iff hL₁]
  constructor
  · intro H Z r₀ z J₀ hG
    obtain ⟨χ, -, h₂⟩ := exists_psi_inv hp τ hτ
    choose J hJ using fun ψ : Z ⟶ A.left => exists_chart hL₁ (ψ z)
    have e : (r₀ ≫ χ) ≫ (psiO hp τ hτ).left = r₀ := by rw [Category.assoc, h₂, Category.comp_id]
    have := (key Z (r₀ ≫ χ) z J₀ J hG hJ).2 (H Z _ z J hJ)
    rwa [e] at this
  · intro H Z r z J hJ
    choose J₀ hG using fun ψ : Z ⟶ G.left => exists_chart hL₀ (ψ z)
    exact (key Z r z J₀ J hG hJ).1 (H Z _ z J₀ hG)

end GlobalTheory.WeilPull

namespace GlobalTheory

open WeilPull

theorem weilIs_grpPullback_of_commute : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB →
    IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G')
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x * y = y * x → x₀.left = x.left ≫ φ →
    y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) := by
  intro S S' G G' _ _ f φ L L' hL hL' hp ⟨w, hw⟩ T k x y x₀ y₀ c hc ex ey
  refine forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ?_
  let V₀ : (Over.mk (T.hom ≫ f)).left.Opens := V
  let τ : (overRes V).left ⟶ (overRes V₀).left := 𝟙 V.toScheme
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 V.toScheme))
  have hτ : τ ≫ (overRes V₀).hom = (overRes V).hom ≫ f := (Category.id_comp _).trans (Category.assoc _ _ _).symm
  have mv : ∀ {a : T ⟶ G'} {a₀ : Over.mk (T.hom ≫ f) ⟶ G}, a₀.left = a.left ≫ φ →
      τ ≫ (overResι V₀ ≫ a₀).left = (overResι V ≫ a).left ≫ φ := fun {a a₀} e =>
    (Category.id_comp _).trans ((congrArg (V.ι ≫ ·) e).trans (Category.assoc _ _ _).symm)
  have cm : ∀ {θx θy : ThetaGrp G' L' k (overRes V)} {θx₀ θy₀ : ThetaGrp G L k (overRes V₀)},
      θx.pt = overResι V ≫ x → θy.pt = overResι V ≫ y → θx₀.pt = overResι V₀ ≫ x₀ → θy₀.pt = overResι V₀ ≫ y₀ →
      Rel hp τ hτ w θx θx₀ → Rel hp τ hτ w θy θy₀ →
      (CommIsOf G' L' k θx θy (unitRes V c) ↔ CommIsOf G L k θx₀ θy₀ (unitRes V₀ c)) :=
    fun h₁ h₂ h₃ h₄ mx my => commIsOf_iff_of_rel hp τ hτ hL hL' w
      (by rw [h₁, h₂, ← MonObj.comp_mul, ← MonObj.comp_mul, hc]) (by rw [h₁, h₃]; exact mv ex)
      (by rw [h₂, h₄]; exact mv ey) mx my _ _ (fun Z r z => congrArg (fun q => gm q z ⊤ (unitRes V c))
        (Category.comp_id r))
  have up : ∀ {a : T ⟶ G'} {a₀ : Over.mk (T.hom ≫ f) ⟶ G}, a₀.left = a.left ≫ φ →
      ∀ θ : ThetaGrp G' L' k (overRes V), θ.pt = overResι V ≫ a →
        ∃ θ₀ : ThetaGrp G L k (overRes V₀), θ₀.pt = overResι V₀ ≫ a₀ ∧ Rel hp τ hτ w θ θ₀ :=
    fun e θ h => exists_rel_up hp τ hτ hL hL' w hw _ θ (by rw [h]; exact mv e)
  have down : ∀ {a : T ⟶ G'} {a₀ : Over.mk (T.hom ≫ f) ⟶ G}, a₀.left = a.left ≫ φ →
      ∀ θ₀ : ThetaGrp G L k (overRes V₀), θ₀.pt = overResι V₀ ≫ a₀ →
        ∃ θ : ThetaGrp G' L' k (overRes V), θ.pt = overResι V ≫ a ∧ Rel hp τ hτ w θ θ₀ :=
    fun e θ₀ h => exists_rel_down hp τ hτ hL hL' w hw _ θ₀ (by rw [h]; exact mv e)
  constructor
  · rintro ⟨⟨θx, θy, h₁, h₂⟩, H⟩
    obtain ⟨a, ha, -⟩ := up ex θx h₁
    obtain ⟨b, hb, -⟩ := up ey θy h₂
    refine ⟨⟨a, b, ha, hb⟩, fun a b ha hb => ?_⟩
    obtain ⟨a', ha', mx⟩ := down ex a ha
    obtain ⟨b', hb', my⟩ := down ey b hb
    exact (cm ha' hb' ha hb mx my).1 (H a' b' ha' hb')
  · rintro ⟨⟨θx, θy, h₁, h₂⟩, H⟩
    obtain ⟨a, ha, -⟩ := down ex θx h₁
    obtain ⟨b, hb, -⟩ := down ey θy h₂
    refine ⟨⟨a, b, ha, hb⟩, fun a b ha hb => ?_⟩
    obtain ⟨a', ha', mx⟩ := up ex a ha
    obtain ⟨b', hb', my⟩ := up ey b hb
    exact (cm ha hb ha' hb' mx my).2 (H a' b' ha' hb')

theorem weilIs_grpPullback_of_comm' : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    [IsCommMonObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB →
    IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G')
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ →
    y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) :=
  fun S S' G G' _ _ _ f φ L L' hL hL' hp hw T k x y x₀ y₀ c ex ey =>
    weilIs_grpPullback_of_commute S S' G G' f φ L L' hL hL' hp hw T k x y x₀ y₀ c (mul_comm x y) ex ey

theorem weilIs_grpPullback_of_comm : ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G']
    [IsCommMonObj G] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB →
    IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → ∀ (T : Over S') (k : ℤ) (x y : T ⟶ G')
    (x₀ y₀ : Over.mk (T.hom ≫ f) ⟶ G) (c : Γ(T.left, ⊤)ˣ), x₀.left = x.left ≫ φ →
    y₀.left = y.left ≫ φ → (Out.WeilIs G' L' k x y c ↔ Out.WeilIs G L k x₀ y₀ c) := by
  intro S S' G G' _ _ _ f φ L L' hL hL' hp hw T k x y x₀ y₀ c ex ey
  refine weilIs_grpPullback_of_commute S S' G G' f φ L L' hL hL' hp hw T k x y x₀ y₀ c ?_ ex ey
  apply Over.OverMorphism.ext
  apply hp.1.hom_ext
  · rw [← hp.2 T x y x₀ y₀ ex ey, ← hp.2 T y x y₀ x₀ ey ex, mul_comm x₀ y₀]
  · rw [Over.w, Over.w]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLinearEquivOfPeriod
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.UnifPoint

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S : Scheme.{0}} {g : ℕ}

def ReadsPeriods (t : SAB H S) {T : Over S} (c₀ : ℂˣ → Γ(T.left, ⊤)ˣ) (D : Datum H) (ty : Fin g → (E →+* ℂ))
    (P : D.La →+ (Fin g → ℂ)) (e : (Fin g → ℂ) → (T ⟶ t.G)) : Prop :=
  (∀ z, e z = 1 ↔ z ∈ P.range) ∧ (∀ (a : 𝓞 E) z, e (fun k => ty k (a : E) * z k) = e z ≫ t.act.act a) ∧
    ∀ (k : ℕ) (a a₂ : D.La) (c : ℂˣ), 0 < k →
      (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a a₂ : ℂ) / k) →
      Out.WeilIs t.G t.PP.L k (e ((k : ℂ)⁻¹ • P a)) (e ((k : ℂ)⁻¹ • P a₂)) (c₀ c)

theorem int_eq_of_exp_eq {m n : ℤ} (h : ∀ k : ℕ, 0 < k → Complex.exp (-(2 * Real.pi * Complex.I) * (m : ℂ) / k) =
    Complex.exp (-(2 * Real.pi * Complex.I) * (n : ℂ) / k)) : m = n := by
  have hk : 0 < (n - m).natAbs + 1 := Nat.succ_pos _
  obtain ⟨j, hj⟩ := Complex.exp_eq_exp_iff_exists_int.1 (h _ hk)
  have h0 : (((n - m).natAbs + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have h1 : ((n - m : ℤ) : ℂ) = ((((n - m).natAbs + 1 : ℕ) : ℤ) * j : ℤ) := by
    apply mul_left_cancel₀ Complex.two_pi_I_ne_zero
    rw [Int.cast_mul, Int.cast_natCast, Int.cast_sub]
    generalize (((n - m).natAbs + 1 : ℕ) : ℂ) = k at h0 hj
    field_simp at hj
    linear_combination (2 * Real.pi * Complex.I) * hj
  have h2 : n - m = 0 := Int.eq_zero_of_dvd_of_natAbs_lt_natAbs ⟨j, Int.cast_injective h1⟩ (by
    rw [Int.natAbs_natCast]; exact Nat.lt_succ_self _)
  omega

theorem discrete_periods {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) :
    DiscreteTopology P.range.toIntSubmodule := hP.2.2.1

theorem countable_periods {D : Datum H} {ty : Fin g → (E →+* ℂ)} {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) :
    (P.range : Set (Fin g → ℂ)).Countable :=
  have := hP.2.2.1
  countable_of_isDiscrete_finiteDimensional DiscreteTopology.isDiscrete

theorem exists_linearEquiv_of_period {t : SAB H S} {y : Sp ℂ ⟶ S} {D : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) {e : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {g₀ : ℕ} {e₀ : (Fin g₀ → ℂ) → (Over.mk y ⟶ t.G)}
    (ha : ∀ z w, e₀ (z + w) = e₀ z * e₀ w) (hs : Function.Surjective e₀)
    (hh : IsHolTo Set.univ (fun z => (e₀ z).left)) (hc : {z | e₀ z = 1}.Countable) :
    ∃ h : (Fin g₀ → ℂ) ≃ₗ[ℂ] (Fin g → ℂ), ∀ z, e (h z) = e₀ z := by
  have := t.semi.separated
  have := discrete_periods hP
  have : IsZLattice ℝ P.range.toIntSubmodule := ⟨hP.2.2.2.1⟩
  exact he.exists_linearEquiv P.range.toIntSubmodule hk ha hs hh hc

theorem exists_isometry {t : SAB H S} {y : Sp ℂ ⟶ S} {D D' : Datum H} {ty : Fin g → (E →+* ℂ)}
    {P : D.La →+ (Fin g → ℂ)} {P' : D'.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty P) (hP' : IsPeriod D' ty P')
    {e e' : (Fin g → ℂ) → (Over.mk y ⟶ t.G)} (he : IsExp e) (he' : IsExp e')
    (hr : ReadsPeriods t unitOn D ty P e) (hr' : ReadsPeriods t unitOn D' ty P' e') :
    ∃ (gam : D.La ≃ₗ[𝓞 E] D'.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) ∧
      (∀ a, P' (gam a) = h (P a)) ∧ ∀ z, e' (h z) = e z := by
  obtain ⟨h, hh⟩ := exists_linearEquiv_of_period hP' he' hr'.1 he.1 he.2.1 he.2.2.1
    ((countable_periods hP).mono fun z hz => (hr.1 z).1 hz)
  have hcomm : ∀ (a : 𝓞 E) z, h (fun k => ty k (a : E) * z k) = fun k => ty k (a : E) * h z k := fun a z => by
    have := hP'.2.2.1
    have k := realLinear_eq_of_sub_mem_discrete (Γ := P'.range) DiscreteTopology.isDiscrete
      (L := (h.toLinearMap.restrictScalars ℝ) ∘ₗ LinearMap.mulLeft ℝ (fun k => ty k (a : E)))
      (L' := LinearMap.mulLeft ℝ (fun k => ty k (a : E)) ∘ₗ (h.toLinearMap.restrictScalars ℝ)) fun x =>
        (hr'.1 _).1 ((eq_iff_sub_of_add he'.1 _ _).1
          (((hh _).trans (hr.2.1 a x)).trans (by rw [← hh]; exact (hr'.2.1 a (h x)).symm)))
    exact DFunLike.congr_fun k z
  have hmem : ∀ a, ∃ b, P' b = h (P a) := fun a => (hr'.1 _).1 ((hh _).trans ((hr.1 _).2 ⟨a, rfl⟩))
  choose r₀ hr₀ using hmem
  let r₁ : D.La →ₗ[𝓞 E] D'.La :=
    { toFun := r₀
      map_add' := fun a b => hP'.2.1 (by rw [map_add (f := _), hr₀, hr₀, hr₀, map_add (f := _), map_add (f := _)])
      map_smul' := fun c a => hP'.2.1 (by
        rw [hr₀, show P (c • a) = fun k => ty k (c : E) * P a k from funext (hP.1 c a), hcomm, ← hr₀]
        exact (funext (hP'.1 c (r₀ a))).symm) }
  have hb : Function.Bijective r₁ := by
    refine ⟨fun a b hab => hP.2.1 (h.injective (((hr₀ a).symm.trans (congrArg P' hab)).trans (hr₀ b))), fun b => ?_⟩
    obtain ⟨a, ha⟩ := (hr.1 (h.symm (P' b))).1 (by rw [← hh, h.apply_symm_apply]; exact (hr'.1 _).2 ⟨b, rfl⟩)
    exact ⟨a, hP'.2.1 ((hr₀ a).trans (by rw [ha, h.apply_symm_apply]))⟩
  refine ⟨LinearEquiv.ofBijective r₁ hb, h, fun a b => int_eq_of_exp_eq fun k hk => ?_, hr₀, hh⟩
  have w := hr.2.2 k a b (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  have w' := hr'.2.2 k (r₀ a) (r₀ b) (Units.mk0 _ (Complex.exp_ne_zero _)) hk rfl
  rw [hr₀, hr₀, ← map_smul h, ← map_smul h, hh, hh] at w'
  exact congrArg Units.val (weilIs_unique_fieldPoint _ _ _ t.PP.isLB ℂ y k _ _ _ _ w' w)

theorem div_eq_iff {L Q : Type*} [AddCommGroup L] [Group Q] {P : L →+ (Fin g → ℂ)} (hP : Function.Injective P)
    {e : (Fin g → ℂ) → Q} (he : ∀ z w, e (z + w) = e z * e w) (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n)
    (a b : L) : e ((n : ℂ)⁻¹ • P a) = e ((n : ℂ)⁻¹ • P b) ↔ ∃ x, a = b + n • x := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  rw [eq_iff_sub_of_add he, hk, ← smul_sub, ← map_sub]
  refine exists_congr fun x => ?_
  rw [eq_inv_smul_iff₀ h0, Nat.cast_smul_eq_nsmul, ← map_nsmul, hP.eq_iff, eq_sub_iff_add_eq', eq_comm]

theorem exists_div_of_pow {L Q : Type*} [AddCommGroup L] [Group Q] {P : L →+ (Fin g → ℂ)}
    {e : (Fin g → ℂ) → Q} (he : ∀ z w, e (z + w) = e z * e w) (hs : Function.Surjective e)
    (hk : ∀ z, e z = 1 ↔ z ∈ P.range) {n : ℕ} (hn : 0 < n) {x : Q} (hx : x ^ n = 1) :
    ∃ a, x = e ((n : ℂ)⁻¹ • P a) := by
  have h0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨z, rfl⟩ := hs x
  have hp : ∀ m : ℕ, e (m • z) = e z ^ m := fun m => by
    induction m with
    | zero => rw [zero_smul, pow_zero, map_zero_of_add he]
    | succ m ih => rw [succ_nsmul, he, ih, pow_succ]
  obtain ⟨a, ha⟩ := (hk _).1 ((hp n).trans hx)
  exact ⟨a, by rw [ha, ← Nat.cast_smul_eq_nsmul ℂ, inv_smul_smul₀ h0]⟩

theorem exists_pointEquiv {S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {y : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G y φ) :
    ∃ β : (𝟙_ (Over S') ⟶ G') ≃* (Over.mk y ⟶ G), ∀ x, (β x).left = x.left ≫ φ := by
  have w : ∀ x : 𝟙_ (Over S') ⟶ G', x.left ≫ G'.hom = 𝟙 S' := fun x => Over.w x
  let f : (𝟙_ (Over S') ⟶ G') → (Over.mk y ⟶ G) := fun x => Over.homMk (x.left ≫ φ) (by
    show (x.left ≫ φ) ≫ G.hom = y
    rw [Category.assoc, h.1.w, ← Category.assoc, w]
    exact Category.id_comp y)
  have hb : Function.Bijective f := by
    refine ⟨fun a b hab => Over.OverMorphism.ext (h.1.hom_ext (congrArg (·.left) hab) ((w a).trans (w b).symm)),
      fun x => ?_⟩
    have hx : x.left ≫ G.hom = 𝟙 S' ≫ y := (Over.w x).trans (Category.id_comp y).symm
    exact ⟨Over.homMk (h.1.lift x.left (𝟙 S') hx) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ hx)⟩
  refine ⟨⟨Equiv.ofBijective f hb, fun a b => Over.OverMorphism.ext ?_⟩, fun _ => rfl⟩
  exact (h.2 _ a b (pushPt h.1.w a) (pushPt h.1.w b) rfl rfl).symm.trans
    (mul_left_congr (Category.id_comp y) _ _ _ _ rfl rfl)

theorem weilIs_congr {X : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} {a b : X ⟶ S} (h : a = b) {k : ℤ}
    {x y : Over.mk a ⟶ G} {x' y' : Over.mk b ⟶ G} (hx : x.left = x'.left) (hy : y.left = y'.left)
    {c : Γ(X, ⊤)ˣ} (H : Out.WeilIs G L k x y c) : Out.WeilIs G L k x' y' c := by
  subst h
  rwa [← Over.OverMorphism.ext hx, ← Over.OverMorphism.ext hy]

end GlobalTheory.UnifPoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubeDescendsAlongEtaleIsogeny
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CubeDescent

section Descent

variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

theorem exists_gen_comp (L : LB X) (F : X' ⟶ X) (φ : K → (Y ⟶ X')) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb (L.pull F) φ ε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (fun k => φ k ≫ F) ε), u.IsGen := by
  have le : ∀ j : K → L.ι, LB.wchart L (fun k => φ k ≫ F) j ≤
      LB.wchart (L.pull F) φ (fun k _ => j k) := fun j y hy =>
    Set.mem_iInter.2 fun k => mem_pull.2 (Set.mem_iInter.1 hy k)
  refine ⟨⟨fun j => res (le j) (t.s fun k _ => j k)⟩, isGen_of_gm _ fun y j j' hj hj' => ?_⟩
  refine (gm_res (𝟙 Y) y (le j) hj _).trans ((gen_trans ht (𝟙 Y) y (le j hj) (le j' hj')).trans
    (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y) y (le j') hj' _).symm))
  refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
  exact (gm_pull_g L F (𝟙 Y ≫ φ k) y (fun _ => j k) (fun _ => j' k)
    (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k)).trans (by rw [Category.assoc])

theorem gs_appLE {Z : Scheme.{0}} (g : Z ⟶ Y) (U : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)) (z : Z) :
    gs (𝟙 Z) z ⊤ ((g.appLE U ⊤ h).hom a) = gs g z U a :=
  (gs_res (𝟙 Z) z h trivial ((g.app U).hom a)).trans
    ((gs_pull (𝟙 Z) g z U (h (x := z) trivial) a).trans (by rw [Category.id_comp]))

theorem exists_gen_descend {L : LB X} (hL : L.IsLB) (π : Y' ⟶ Y) [Flat π] [Surjective π]
    [QuasiCompact π] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (u : LB.Gen (LB.LinComb L (fun k => π ≫ φ k) ε)) (hu : u.IsGen)
    (h : ∀ (Z : Scheme.{0}) (g₁ g₂ : Z ⟶ Y') (z : Z) (J), Good L z J → g₁ ≫ π = g₂ ≫ π →
      val u g₁ z J = val u g₂ z J) :
    ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen := by
  have le : ∀ j : K → L.ι, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have desc : ∀ j : K → L.ι, ∃ a : Γ(Y, LB.wchart L φ j),
      (π.app _).hom a = (res (le j) (u.s j)).val := by
    intro j
    refine FunDescent.exists_app_eq π _ _ fun Z g₁ g₂ h₁ h₂ e => fn_ext fun z _ => ?_
    rw [gs_appLE, gs_appLE, gs_unit _ _ _ (h₁ (x := z) trivial), gs_unit _ _ _ (h₂ (x := z) trivial)]
    choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
    have c₁ := gen_trans hu g₁ z (le j (h₁ (x := z) trivial)) (Good.mem hI _ g₁)
    have c₂ := gen_trans hu g₂ z (le j (h₂ (x := z) trivial)) (Good.mem hI _ g₂)
    have c₃ : trF (fun k => π ≫ φ k) ε g₁ z j (fun k => I (g₁ ≫ π ≫ φ k)) =
        trF (fun k => π ≫ φ k) ε g₂ z j (fun k => I (g₂ ≫ π ≫ φ k)) := by
      refine Finset.prod_congr rfl fun k _ => ?_
      have : g₁ ≫ π ≫ φ k = g₂ ≫ π ≫ φ k := by rw [reassoc_of% e]
      show gm (g₁ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (g₁ ≫ π ≫ φ k))) (L.g (j k) (I (g₁ ≫ π ≫ φ k))) ^ _ =
        gm (g₂ ≫ π ≫ φ k) z (L.U (j k) ⊓ L.U (I (g₂ ≫ π ≫ φ k))) (L.g (j k) (I (g₂ ≫ π ≫ φ k))) ^ _
      rw [this]
    exact congrArg Units.val ((gm_res g₁ z (le j) (h₁ (x := z) trivial) _).trans
      ((c₁.trans ((congrArg₂ (· * ·) c₃ (h Z g₁ g₂ z I hI e)).trans c₂.symm)).trans
        (gm_res g₂ z (le j) (h₂ (x := z) trivial) _).symm))
  choose a ha using desc
  have hun : ∀ j, IsUnit (a j) := fun j =>
    FunDescent.isUnit_of_isUnit_app π _ _ (ha j ▸ Units.isUnit _)
  have hv : ∀ j (y : Y'), π y ∈ LB.wchart L φ j → gm π y (LB.wchart L φ j) (hun j).unit =
      gm (𝟙 Y') y (LB.wchart L (fun k => π ≫ φ k) j) (u.s j) := by
    intro j y hy
    have e : pullU π _ (hun j).unit = res (le j) (u.s j) := Units.ext (ha j)
    refine Eq.trans ?_ ((gm_pull (𝟙 Y') π y _ hy _).symm.trans
      ((congrArg (gm (𝟙 Y') y _) e).trans (gm_res (𝟙 Y') y (le j) hy _)))
    rw [Category.id_comp]
  refine ⟨⟨fun j => (hun j).unit⟩, fun j j' => Units.ext
    (FunDescent.app_injective π (LB.wchart L φ j ⊓ LB.wchart L φ j') ?_)⟩
  refine congrArg Units.val (unit_ext (a := pullU π _ _) (b := pullU π _ _) fun y hy => ?_)
  have hy' : π y ∈ LB.wchart L φ j ⊓ LB.wchart L φ j' := hy
  refine (gm_pull (𝟙 Y') π y _ hy' _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') π y _ hy' _).symm)
  rw [Category.id_comp]
  refine ((gm_res π y _ hy' _).trans ((hv j y hy'.1).trans
    (gen_trans hu (𝟙 Y') y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((gm_linComb L φ ε π y j j' hy'.1 hy'.2).trans ?_)
    ((gm_res π y _ hy' _).trans (hv j' y hy'.2)))
  simp only [trF, Category.id_comp]

end Descent

section Group

variable {S X : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {Q : Over S}
  {φ : K → (Q.left ⟶ X)} {ε : K → ℤ}

theorem val_eq_of_section (hL : L.IsLB) {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen)
    {P T : Over S} (p : P ⟶ T) (e : T ⟶ P) (he : e ≫ p = 𝟙 T)
    (hp : Function.Surjective p.left.appTop.hom) (a a' : P ⟶ Q)
    (hF : FormEq (fun k => a'.left ≫ φ k) ε (fun k => a.left ≫ φ k) ε)
    (h : ∀ y J, Good L y J → val u (e ≫ a).left y J = val u (e ≫ a').left y J)
    {T' : Over S} (ρ : T' ⟶ P) (z : T'.left) (J) (hJ : Good L z J) :
    val u (ρ ≫ a).left z J = val u (ρ ≫ a').left z J := by
  have := gen_unique' hL hF p.left e.left (congrArg (fun q => q.left) he) hp
    (DVR.pullGen_isGen _ _ _ _ hu a.left) (DVR.pullGen_isGen _ _ _ _ hu a'.left)
    (fun y J hJ => by rw [val_pull hJ, val_pull hJ]; exact h y J hJ) _ ρ.left z J hJ
  rw [val_pull hJ, val_pull hJ] at this
  exact this

variable {A : Over S} [GrpObj A]

theorem val_eq_of_axis (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) (hL : L.IsLB)
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) (σ : A ⊗ A ⊗ A ⟶ Q)
    (H₁ : FormEq (fun k => (lift (1 : A ⟶ A) (lift 1 1) ≫ σ).left ≫ φ k) ε
      (fun k => (lift (𝟙 A) (lift 1 1) ≫ σ).left ≫ φ k) ε)
    {T : Over S} (x x' : T ⟶ A)
    (H₂ : ∀ (T' : Over S) (ρ : T' ⟶ T) (y w : T' ⟶ A) (k : K),
      (lift (ρ ≫ x') (lift y w) ≫ σ).left ≫ φ k = (lift (ρ ≫ x) (lift y w) ≫ σ).left ≫ φ k)
    (y w : T ⟶ A) (z : T.left) (J) (hJ : Good L z J) :
    val u (lift x (lift y w) ≫ σ).left z J = val u (lift x' (lift y w) ≫ σ).left z J := by
  have face : ∀ (v : T ⟶ A) (z : T.left) (J), Good L z J →
      val u (lift v (lift 1 1) ≫ σ).left z J = val u (lift (1 : T ⟶ A) (lift 1 1) ≫ σ).left z J := by
    intro v z J hJ
    have := val_eq_of_section hL hu (toUnit A) η[A] (toUnit_unique _ _) (hG _ _ hA).2
      (lift (𝟙 A) (lift 1 1) ≫ σ) (lift (1 : A ⟶ A) (lift 1 1) ≫ σ) H₁ (fun y J _ => by
        congr 2
        simp [comp_lift_assoc, Hom.one_def]) v z J hJ
    simpa only [comp_lift_assoc, comp_lift, Category.comp_id, MonObj.comp_one] using this
  have := val_eq_of_section hL hu (snd A (A ⊗ T) ≫ snd A T) (lift 1 (lift 1 (𝟙 T))) (by simp)
    (surj_comp (surj_snd hG hA _) (surj_snd hG hA _))
    (lift ((snd A (A ⊗ T) ≫ snd A T) ≫ x) (lift (fst _ _) (snd _ _ ≫ fst _ _)) ≫ σ)
    (lift ((snd A (A ⊗ T) ≫ snd A T) ≫ x') (lift (fst _ _) (snd _ _ ≫ fst _ _)) ≫ σ)
    (fun U _ h => Finset.prod_congr rfl fun k _ => congrArg (fun q => h q ^ ε k) (H₂ _ _ _ _ k))
    (fun z J hJ => by
      have e := (face x z J hJ).trans (face x' z J hJ).symm
      simpa only [comp_lift_assoc, comp_lift, lift_fst, lift_snd_assoc, lift_snd, Category.assoc,
        Category.id_comp] using e)
    (lift y (lift w (𝟙 T))) z J hJ
  simpa only [comp_lift_assoc, comp_lift, lift_fst, lift_snd_assoc, lift_snd, Category.assoc,
    Category.id_comp] using this

variable {B : Over S} [GrpObj B] [IsCommMonObj B]

theorem exists_gen_theta [IsCommMonObj A] (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A)
    (ψ : A ⟶ B) [IsMonHom ψ] [Flat ψ.left] [Surjective ψ.left] [QuasiCompact ψ.left]
    {M : LB B.left} (hM : M.IsLB) (t : LB.Gen (Theta A (M.pull ψ.left))) (ht : t.IsGen) :
    ∃ t : LB.Gen (Theta B M), t.IsGen := by
  have := AbelianQuotient.flat_tensorHom ψ ψ
  have := AbelianQuotient.surjective_tensorHom ψ ψ
  have := AbelianQuotient.quasiCompact_tensorHom ψ ψ
  have := AbelianQuotient.flat_tensorHom ψ (ψ ⊗ₘ ψ)
  have := AbelianQuotient.surjective_tensorHom ψ (ψ ⊗ₘ ψ)
  have := AbelianQuotient.quasiCompact_tensorHom ψ (ψ ⊗ₘ ψ)
  let π : G3 A ⟶ G3 B := ψ ⊗ₘ ψ ⊗ₘ ψ
  have hπ : ∀ {T : Over S} (x y w : T ⟶ A),
      lift x (lift y w) ≫ π = lift (x ≫ ψ) (lift (y ≫ ψ) (w ≫ ψ)) := fun x y w => by
    simp [π, lift_map]
  obtain ⟨u₀, hu₀⟩ := exists_gen_comp M ψ.left (thφ A (x3 A)) thε t ht
  have hφ : ∀ I, thφ A (x3 A) I ≫ ψ.left = π.left ≫ thφ B (x3 B) I := fun I => by
    let ρ : (G3 A ⟶ A) →* (G3 A ⟶ B) := MonoidHom.mk' (· ≫ ψ) fun a b => MonObj.mul_comp a b ψ
    exact congrArg (fun q => q.left) ((psum_hom ρ (x3 A) I.down).trans
      ((congrArg (fun q => psum B q I.down) (funext fun i => by
        fin_cases i <;> simp [ρ, π, preHom, x3])).trans (psum_hom (preHom π) (x3 B) I.down).symm))
  obtain ⟨u, hu, -⟩ := exists_gen hM (φ' := fun I => π.left ≫ thφ B (x3 B) I) (ε' := thε)
    (fun U _ h => Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ thε I) (hφ I)) u₀ hu₀
  have hc : ∀ {T : Over S} (x y w : T ⟶ A) (I : thK),
      (lift x (lift y w)).left ≫ π.left ≫ thφ B (x3 B) I =
        (lift (x ≫ ψ) (lift (y ≫ ψ) (w ≫ ψ))).left ≫ thφ B (x3 B) I := fun x y w I => by
    rw [← Category.assoc, ← Over.comp_left, hπ]
  have hp : ∀ (x y w : A ⟶ A), (y = 1 ∧ w = 1 ∨ x = 1 ∧ w = 1 ∨ x = 1 ∧ y = 1) →
      ∀ (U : Type) [CommGroup U] (h : (A.left ⟶ B.left) → U),
      ∏ I, h ((lift x (lift y w)).left ≫ π.left ≫ thφ B (x3 B) I) ^ thε I = 1 := by
    intro x y w H U _ h
    refine (Finset.prod_congr rfl fun I _ => congrArg (fun q => h q ^ thε I) (hc x y w I)).trans
      ((prod_cub _ _ _ h).trans ?_)
    apply Additive.ofMul.injective
    rcases H with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      simp only [MonObj.one_comp, _root_.mul_one, _root_.one_mul, ofMul_mul, ofMul_inv, ofMul_one] <;>
      abel
  refine exists_gen_descend hM π.left (thφ B (x3 B)) thε u hu fun Z g₁ g₂ z J hJ e => ?_
  let T : Over S := Over.mk (g₂ ≫ (G3 A).hom)
  let k₂ : T ⟶ G3 A := Over.homMk g₂ rfl
  let k₁ : T ⟶ G3 A := Over.homMk g₁ (by
    change g₁ ≫ (G3 A).hom = g₂ ≫ (G3 A).hom
    rw [← Over.w π, reassoc_of% e])
  have e' : k₁ ≫ π = k₂ ≫ π := Over.OverMorphism.ext e
  obtain ⟨x, y, w, h₁⟩ : ∃ x y w, k₁ = lift x (lift y w) :=
    ⟨k₁ ≫ fst _ _, k₁ ≫ snd _ _ ≫ fst _ _, k₁ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
  obtain ⟨x', y', w', h₂⟩ : ∃ x y w, k₂ = lift x (lift y w) :=
    ⟨k₂ ≫ fst _ _, k₂ ≫ snd _ _ ≫ fst _ _, k₂ ≫ snd _ _ ≫ snd _ _, by ext <;> simp⟩
  rw [h₁, h₂, hπ, hπ] at e'
  have ex : x ≫ ψ = x' ≫ ψ := by simpa using e' =≫ fst _ _
  have ey : y ≫ ψ = y' ≫ ψ := by simpa using e' =≫ snd _ _ ≫ fst _ _
  have ew : w ≫ ψ = w' ≫ ψ := by simpa using e' =≫ snd _ _ ≫ snd _ _
  change val u k₁.left z J = val u k₂.left z J
  rw [h₁, h₂]
  let σ₁ : A ⊗ A ⊗ A ⟶ G3 A := lift (snd _ _ ≫ fst _ _) (lift (fst _ _) (snd _ _ ≫ snd _ _))
  let σ₂ : A ⊗ A ⊗ A ⟶ G3 A := lift (snd _ _ ≫ fst _ _) (lift (snd _ _ ≫ snd _ _) (fst _ _))
  have s₁ : ∀ {T : Over S} (a b c : T ⟶ A), lift a (lift b c) ≫ σ₁ = lift b (lift a c) :=
    fun a b c => by simp [σ₁]
  have s₂ : ∀ {T : Over S} (a b c : T ⟶ A), lift a (lift b c) ≫ σ₂ = lift b (lift c a) :=
    fun a b c => by simp [σ₂]
  have v₀ := val_eq_of_axis hG hA hM hu (𝟙 _) (fun U _ h => by
      simp only [Category.comp_id]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).symm) x x'
    (fun T' ρ a b I => by
      rw [Category.comp_id, Category.comp_id]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ex]) (hc _ _ _ I).symm)) y w z J hJ
  have v₁ := val_eq_of_axis hG hA hM hu σ₁ (fun U _ h => by
      simp only [s₁]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inr (.inl ⟨rfl, rfl⟩)) U h).symm) y y'
    (fun T' ρ a b I => by
      rw [s₁, s₁]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ey]) (hc _ _ _ I).symm)) x' w z J hJ
  have v₂ := val_eq_of_axis hG hA hM hu σ₂ (fun U _ h => by
      simp only [s₂]
      exact (hp _ _ _ (.inl ⟨rfl, rfl⟩) U h).trans (hp _ _ _ (.inr (.inr ⟨rfl, rfl⟩)) U h).symm) w w'
    (fun T' ρ a b I => by
      rw [s₂, s₂]
      exact (hc _ _ _ I).trans (Eq.trans (by rw [Category.assoc, Category.assoc, ew]) (hc _ _ _ I).symm)) x' y' z J hJ
  rw [Category.comp_id, Category.comp_id] at v₀
  rw [s₁, s₁] at v₁
  rw [s₂, s₂] at v₂
  exact v₀.trans (v₁.trans v₂)

end Group

end GlobalTheory.CubeDescent

namespace GlobalTheory

theorem cube_descends_along_etale_isogeny :
    Out.GlobalFnsSt → ∀ (k : Type) [Field k] [IsAlgClosed k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] [IsCommMonObj B] (ψ : A ⟶ B) (M : LB B.left) [IsCommMonObj A], IsAbelianScheme A → IsAbelianScheme B → M.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∃ t : LB.Gen (Theta A (M.pull ψ.left)), t.IsGen) → ∃ t : LB.Gen (Theta B M), t.IsGen := by
  intro hG k _ _ A B _ _ _ ψ M _ hA _ hM _ _ _ _ ⟨t, ht⟩
  exact CubeDescent.exists_gen_theta hG hA ψ hM t ht

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TorsionFormCompare

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

def RigAlong {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G]
    (ε : G' ⟶ G) (L : RigLB G) (L' : RigLB G') (w : LB.Iso L'.L (L.L.pull ε.left)) : Prop :=
  w.IsGen ∧ PMaps w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) L'.rig L.rig (𝟙 _)

variable {R : Type} [CommRing R] [IsDomain R]

def SameUnif {I : Ideal R} {D : DegData R I} {A : PolAV (Sp (FractionRing R))} {G' G : Over (Sp R)}
    [GrpObj G'] [IsCommMonObj G'] [GrpObj G] [IsCommMonObj G] (ε : G' ≅ G)
    (U : UnifPre I D A G) (U' : UnifPre I D A G') : Prop :=
  U'.gen.hom = (Over.pullback (jK R)).map ε.hom ≫ U.gen.hom ∧
    ∃ w : LB.Iso U'.LG.L (U.LG.L.pull ε.hom.left), RigAlong ε.hom U.LG U'.LG w ∧ ∀ e : ℕ,
      (U'.gt e).q = (Over.pullback (thick R I e)).map ε.hom ≫ (U.gt e).q ∧
      (∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ ((U'.gt e).t χ)
        (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) ((Over.pullback (thick R I e)).map ε.hom).left)) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
        (jL' : U'.LG.L.ι), (U'.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM →
        ε.hom.left ((fstG I e G').left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' →
        gw (U'.w e) r z jM (fun _ => jL') =
          gw (U.w e) (r ≫ ((Over.pullback (thick R I e)).map ε.hom).left) z jM (fun _ => jL) *
            gw w (r ≫ (fstG I e G').left) z jL jL'

def IsIdPull {D : DegPre R} (hD : IsPullDeg (RingHom.id R) D D) : Prop :=
  (∀ x, hD.xe x = x) ∧ hD.e.hom.left ≫ pullback.fst D.P.A.hom (specOf (RingHom.id R)) = 𝟙 _ ∧
    ∀ (Y : Scheme.{0}) (f : Y ⟶ D.P.A.left) (y : Y) (j k : D.P.L.ι), f y ∈ D.P.L.U j → f y ∈ D.P.L.U k →
      gw hD.w f y j k = gm f y _ (D.P.L.g j k)

theorem rigAlong_id {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G) :
    RigAlong (𝟙 G) L L (isoPullId (idIso L.L) rfl) := by
  have he : eSec G ≫ (𝟙 G : G ⟶ G).left = 𝟙 _ ≫ eSec G := by simp
  exact ⟨(isGen_iff _).2 (isoPullId_pgen (idIso_isGen L.isLB) rfl),
    (maps_iff _ _ (fun _ => eSec G) _ L.rig L.rig (𝟙 _) _ (rigPull_le _ _ he L.L) (fun _ => rfl)).1
      (isoPullId_maps (idIso_maps L) rfl rfl he)⟩

end GlobalTheory.TorsionFormCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CoveringAndSmoothnessIffOfSeparableSplitting
noncomputable section

namespace GlobalTheory.CoveringCompare

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

section Fibres

def SplitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (x : S) (k : Type) [Field k] [Algebra (S.residueField x) k] :
    Prop :=
  ∃ T : SplitExt (Sp k), T.IsGt ((Over.pullback
    (Spec.map (CommRingCat.ofHom (algebraMap (S.residueField x) k)) ≫ S.fromSpecResidueField x)).obj G)

theorem splitOver_of_torusExtension {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) (k : Type)
    [Field k] [Algebra (S.residueField x) k]
    (h : Nonempty (TorusExtension ((Over.pullback (spMap (algebraMap (S.residueField x) k))).obj
      ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)))) :
    SplitOver G x k := by
  obtain ⟨T⟩ := h
  obtain ⟨i, hi, -⟩ := grpPullback_iso
    ((isGrpPullback_pullback ((Over.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x)).obj G)
      (spMap (algebraMap (S.residueField x) k))).comp (isGrpPullback_pullback G _))
    (isGrpPullback_pullback G _)
  have := hG.comm
  exact exists_splitExt_isGt_of_torusExtension _ _ ⟨torusExtOfIso i T⟩

theorem exists_finite_splitOver {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G) (x : S) :
    ∃ (k : Type) (_ : Field k) (_ : Algebra (S.residueField x) k),
      FiniteDimensional (S.residueField x) k ∧ SplitOver G x k := by
  have h₀ := IsSemiAbelian.pullback (show Sp (S.residueField x) ⟶ S from S.fromSpecResidueField x) G hG
  have := h₀.smooth
  obtain ⟨k, hk, T⟩ := exists_finite_torusExtension (S.residueField x) (AlgebraicClosure (S.residueField x)) _
    inferInstance h₀.quasiCompact h₀.separated (h₀.fibres _ _)
  exact ⟨k, inferInstance, inferInstance, hk, splitOver_of_torusExtension G hG x k T⟩

end Fibres

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H}

section One

variable {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

end One

end GlobalTheory.CoveringCompare
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePoints
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.DetSpread

theorem exists_factor {S : Scheme.{0}} {R K : Type} [CommRing R] [Field K] (j : Sp R ⟶ S) [IsOpenImmersion j]
    (x : Sp K ⟶ S) (q : PrimeSpectrum R) (y : Sp K) (hy : x y = j q) :
    ∃ f : R →+* K, spMap f ≫ j = x ∧ RingHom.ker f = q.asIdeal := by
  have hsub : Set.range x ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    exact ⟨q, by rw [← hy, Subsingleton.elim z y]⟩
  have hx : IsOpenImmersion.lift j x hsub ≫ j = x := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨g, hg⟩ := Spec.map_surjective (IsOpenImmersion.lift j x hsub)
  rw [← hg] at hx
  have hq : Spec.map g y = q := by
    apply j.isOpenEmbedding.injective
    rw [← Scheme.Hom.comp_apply, hx, hy]
  refine ⟨g.hom, hx, ?_⟩
  rw [← hq]
  have hy0 : PrimeSpectrum.asIdeal y = ⊥ := by
    rcases Ideal.eq_bot_or_top (PrimeSpectrum.asIdeal (R := K) y) with e | e
    · exact e
    · exact absurd e (PrimeSpectrum.isPrime y).ne_top
  change _ = Ideal.comap g.hom (PrimeSpectrum.asIdeal y)
  rw [hy0]
  rfl

theorem eq_comp_of_spMap {S : Scheme.{0}} {o R K : Type} [CommRing o] [CommRing R] [CommRing K]
    {j : Sp R ⟶ S} {s : S ⟶ Sp o} {δ : o →+* R} (hδ : j ≫ s = spMap δ) {f : R →+* K} {β : o →+* K}
    (h : (spMap f ≫ j) ≫ s = spMap β) (a : o) : β a = f (δ a) := by
  rw [Category.assoc, hδ] at h
  have h' : CommRingCat.ofHom δ ≫ CommRingCat.ofHom f = CommRingCat.ofHom β :=
    Spec.map_injective ((Spec.map_comp _ _).trans h)
  exact (congrArg (fun z => z.hom a) h').symm

theorem detCond_of_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] (act : OAct (𝓞 E) G) {o : Type} [CommRing o] (s : S ⟶ Sp o) (ρ : o)
    (hρ : ρ ^ 2 = -(H.d : o))
    (hd : Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S)
      (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)})
    {R : Type} [CommRing R] [IsReduced R] (j : Sp R ⟶ S) [IsOpenImmersion j]
    {G' : Over (Sp R)} [GrpObj G'] [IsCommMonObj G'] (act' : OAct (𝓞 E) G') (hs : Smooth G'.hom)
    {n : ℕ} (v : Fin n → (epsR R ⟶ G')) (hv : IsLieBasis v)
    (h : ∀ (K : Type) [Field K] (y : Sp K ⟶ Sp R) (τ : 𝓞 E →+* K) (N : ℕ),
      LieMult act' y τ N ↔ LieMult act (y ≫ j) τ N)
    (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (f : R →+* K) (β : o →+* K)
    (hβ : (spMap f ≫ j) ≫ s = spMap β) : DetCond D act (spMap f ≫ j) (β ρ) := by
  obtain ⟨δ₀, hδ₀⟩ := Spec.map_surjective (j ≫ s)
  have hδ : j ≫ s = spMap δ₀.hom := hδ₀.symm
  obtain ⟨M, hM⟩ := GlobalTheory.exists_lie_coordinates_lieMult_iff (𝓞 E) R G' act' n v hs hv
  obtain ⟨M', hM', e⟩ := hM K f
  have hr : (δ₀.hom ρ) ^ 2 = -(H.d : R) := by
    have := congrArg δ₀.hom hρ
    rw [map_pow, map_neg, map_natCast] at this
    exact this
  have main := GlobalTheory.T.cmType_eigenMultiplicity_of_dense_primes E H D.p D.q n R M (δ₀.hom ρ) hr (by
    refine (hd.preimage j.isOpenEmbedding.isOpenMap).mono ?_
    rintro q ⟨L, _, _, _, x, β', ⟨y, hy⟩, hx, hdet⟩
    obtain ⟨g, rfl, hg⟩ := exists_factor j x q y hy
    obtain ⟨N', hN', e'⟩ := hM L g
    refine ⟨L, inferInstance, inferInstance, inferInstance, g, N', hg, hN', fun τ => ?_⟩
    rw [← e', ← e', h, h, ← eq_comp_of_spMap hδ hx]
    exact hdet τ) K f M' hM'
  intro τ
  rw [← h, ← h, e, e, eq_comp_of_spMap hδ hβ]
  exact main τ

theorem detCond_of_dense : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsReduced S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (act : OAct (𝓞 E) G) (o : Type) [CommRing o] (s : S ⟶ Sp o) (ρ : o), SmoothOfRelativeDimension g G.hom → ρ ^ 2 = -(H.d : o) → Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : o →+* K), x ≫ s = spMap β → DetCond D act x (β ρ) := by
  intro E _ _ _ H D S _ G _ _ g act o _ s ρ hg hρ hd K _ _ _ x β hβ
  let y : Sp K := (default : PrimeSpectrum K)
  obtain ⟨U, hU, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := x y) trivial
  let j : Sp Γ(S, U) ⟶ S := hU.fromSpec
  have : IsOpenImmersion j := hU.isOpenImmersion_fromSpec
  obtain ⟨q, hq⟩ : x y ∈ Set.range j := hU.range_fromSpec.ge hs
  have hg₁ : SmoothOfRelativeDimension g ((Over.pullback j).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg
  obtain ⟨r, hr, v, hv⟩ := GlobalTheory.LieLoc.lie_locally_free Γ(S, U) ((Over.pullback j).obj G) g hg₁ q
  let a : Sp (Localization.Away r) ⟶ Sp Γ(S, U) := spMap (algebraMap Γ(S, U) (Localization.Away r))
  have : IsOpenImmersion a := IsOpenImmersion.of_isLocalization r
  obtain ⟨q', hq'⟩ : q ∈ Set.range (PrimeSpectrum.comap (algebraMap Γ(S, U) (Localization.Away r))) := by
    rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
    exact hr
  obtain ⟨f, rfl, -⟩ := exists_factor (a ≫ j) x q' y (by
    rw [← hq, ← hq']
    rfl)
  obtain ⟨a₁, h₁⟩ := GlobalTheory.DetExtend.exists_oAct_pullback j act
  obtain ⟨a₂, h₂⟩ := GlobalTheory.DetExtend.exists_oAct_pullback a a₁
  have hg₂ : SmoothOfRelativeDimension g ((Over.pullback a).obj ((Over.pullback j).obj G)).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg₁
  refine detCond_of_basis D act s ρ hρ hd (a ≫ j) a₂ (SmoothOfRelativeDimension.smooth g _) v hv
    (fun L _ z τ N => ?_) K f β hβ
  rw [LiePull.lieMult_pull _ _ _ _ _ a _ a₁ a₂ (isGrpPullback_pullback _ a)
    (fun c => by rw [h₂]; exact pullback.lift_fst _ _ _) L z τ N,
    LiePull.lieMult_pull _ _ _ _ _ j _ act a₁ (isGrpPullback_pullback _ j)
    (fun c => by rw [h₁]; exact pullback.lift_fst _ _ _) L (z ≫ a) τ N, Category.assoc]

end GlobalTheory.DetSpread
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ModuliProofs.DeterminantConditionSpreadsOfDensePointsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.determinantCondition_spreads_of_dense_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (S : Scheme.{0}) [IsReduced S] (G : Over S) [GrpObj G] [IsCommMonObj G] (g : ℕ) (act : OAct (𝓞 E) G) (o : Type) [CommRing o] (s : S ⟶ Sp o) (ρ : o), SmoothOfRelativeDimension g G.hom → ρ ^ 2 = -(H.d : o) → Dense {p : S | ∃ (K : Type) (_ : Field K) (_ : IsAlgClosed K) (_ : CharZero K) (x : Sp K ⟶ S) (β : o →+* K), p ∈ Set.range x ∧ x ≫ s = spMap β ∧ DetCond D act x (β ρ)} → ∀ (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (x : Sp K ⟶ S) (β : o →+* K), x ≫ s = spMap β → DetCond D act x (β ρ) := by
  first | exact @GlobalTheory.DetSpread.detCond_of_dense | exact GlobalTheory.DetSpread.detCond_of_dense | (intros; apply GlobalTheory.DetSpread.detCond_of_dense <;> assumption)
end
end
