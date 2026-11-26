module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUniqueLbIsoPullEqOfCoheightLeOne

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.MulPullOfCubeOfSymm
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.MulPull

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

def HasGen {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) : Prop :=
  ∃ t : LB.Gen (LB.LinComb L φ ε), t.IsGen

section

variable {X Y Z : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
  {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}

theorem HasGen.mul (h : HasGen L φ ε) (h' : HasGen L φ' ε') :
    HasGen L (Sum.elim φ φ') (Sum.elim ε ε') := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht'⟩ := h'
  exact ⟨_, DVR.mulGen_isGen L _ _ _ _ t t' ht ht'⟩

theorem HasGen.inv (h : HasGen L φ ε) : HasGen L φ (fun k => -ε k) := by
  obtain ⟨t, ht⟩ := h
  exact ⟨_, DVR.invGen_isGen L _ _ t ht⟩

theorem HasGen.pull (h : HasGen L φ ε) (f : Z ⟶ Y) : HasGen L (fun k => f ≫ φ k) ε := by
  obtain ⟨t, ht⟩ := h
  exact ⟨_, DVR.pullGen_isGen L _ _ t ht f⟩

theorem HasGen.of_formEq (hL : L.IsLB) (h : HasGen L φ ε) (e : FormEq φ ε φ' ε') : HasGen L φ' ε' := by
  obtain ⟨t, ht⟩ := h
  obtain ⟨t', ht', -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_gen hL e t ht
  exact ⟨t', ht'⟩

end

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : LB A.left}

theorem hasGen_pow (hL : L.IsLB) (hcube : HasGen L (thφ A (x3 A)) thε) {T : Over S} (x : T ⟶ A)
    (hone : HasGen L (K := Fin 1) ![(1 : T ⟶ A).left] ![1])
    (hsym : HasGen L (K := Fin 2) ![x.left, (x⁻¹).left] ![1, -1]) (n : ℕ) :
    HasGen L (K := Fin 2) ![x.left, (x ^ n).left] ![(n : ℤ) ^ 2, -1] := by
  induction n using Nat.twoStepInduction with
  | zero =>
    exact hone.inv.of_formEq hL (fun U _ h => by simp [Fin.prod_univ_succ])
  | one =>
    exact (hone.mul hone.inv).of_formEq hL (fun U _ h => by
      simp [Fin.prod_univ_succ, Fintype.prod_sum_type])
  | more n ih₀ ih₁ =>
    refine ((hcube.pull (lift (x ^ (n + 1)) (lift x x⁻¹)).left).mul
      ((ih₁.mul ih₁).mul (ih₀.inv.mul ((hone.mul hone).mul hsym)))).of_formEq hL (fun U _ h => ?_)
    refine ((Fintype.prod_sum_type _).trans
      (congrArg₂ (· * ·) (prod_cub (x ^ (n + 1)) x x⁻¹ h) rfl)).trans ?_
    have e₁ : x ^ (n + 1) * x * x⁻¹ = x ^ (n + 1) := mul_inv_cancel_right _ _
    have e₂ : x ^ (n + 1) * x = x ^ (n + 2) := (pow_succ x (n + 1)).symm
    have e₃ : x ^ (n + 1) * x⁻¹ = x ^ n := by rw [pow_succ, mul_inv_cancel_right]
    rw [e₁, e₂, e₃, mul_inv_cancel]
    apply Additive.ofMul.injective
    simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_succ, Fin.prod_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
    push_cast
    module

theorem mulPull_of_cube_of_symm :
    (∀ (S : Scheme.{0}) (P : PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) →
    (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ nu : LB.Gen (negLB P.A P.L k T), nu.IsGen) →
    (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2)
      ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) ∧ MulPullSt := by
  intro hc hs
  have main : ∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2)
      ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen := by
    intro S P n
    have hcube : HasGen P.L (thφ P.A (x3 P.A)) thε := hc S P P.L P.isLB
    have hrig : HasGen P.L (K := PUnit) (fun _ => eSec P.A) (fun _ => 1) := P.rigid
    have hneg : HasGen P.L (K := Fin 2) ![(snd P.A P.A).left,
      (snd P.A P.A ≫ (GrpObj.inv : P.A ⟶ P.A)).left] ![1, -1] := hs S P 1 P.A
    refine hasGen_pow P.isLB hcube (𝟙 P.A) ?_ ?_ n
    · refine (hrig.pull (toUnit P.A).left).of_formEq P.isLB (fun U _ h => ?_)
      simp only [Finset.univ_unique, Finset.prod_singleton, Fin.prod_univ_succ, Fin.prod_univ_zero,
        Matrix.cons_val_zero, _root_.mul_one]
      rfl
    · refine (hneg.pull (lift (𝟙 P.A) (𝟙 P.A)).left).of_formEq P.isLB (fun U _ h => ?_)
      simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero, Matrix.cons_val_succ,
        ← Over.comp_left, lift_snd, lift_snd_assoc]
      rfl
  exact ⟨main, fun S _ P n => main S P n⟩

end GlobalTheory.MulPull
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace CubeExtension

section Group

variable {S : Scheme.{0}}

theorem smooth_tensor (A B : Over S) [Smooth A.hom] [Smooth B.hom] : Smooth (A ⊗ B).hom := by
  change Smooth (pullback.fst A.hom B.hom ≫ A.hom)
  infer_instance

theorem geometricallyConnected_tensor (A B : Over S) [Smooth A.hom] [Smooth B.hom]
    [GeometricallyConnected A.hom] [GeometricallyConnected B.hom] :
    GeometricallyConnected (A ⊗ B).hom := by
  change GeometricallyConnected (pullback.fst A.hom B.hom ≫ A.hom)
  exact GeometricallyConnected.comp _ _

variable (G : Over S) [GrpObj G] [IsCommMonObj G]

theorem eSec_comp : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]

theorem eSec_three :
    eSec (G3 G) = (lift (1 : 𝟙_ (Over S) ⟶ G) (lift (1 : 𝟙_ (Over S) ⟶ G) (1 : 𝟙_ (Over S) ⟶ G))).left := by
  unfold eSec
  congr 1
  ext <;> simp [Hom.one_def]

theorem formEq_origin :
    FormEq (K := PEmpty) (PEmpty.elim : PEmpty → ((𝟙_ (Over S)).left ⟶ G.left)) PEmpty.elim
      (fun I => eSec (G3 G) ≫ thφ G (x3 G) I) thε := by
  intro U _ h
  rw [eSec_three, prod_cub]
  simp

end Group

theorem pullGen_genPull {X Y Z : Scheme.{0}} (M : LB X) (c : LB.Gen M) (f : Y ⟶ X) (h : Z ⟶ Y) :
    LB.pullGen M _ _ (LB.genPull M c f) h = LB.genPull M c (h ≫ f) := by
  refine lbGen_ext fun j => congrArg Units.val ?_
  exact LB.pull_res_comp h f _ _ _ _ _

end CubeExtension

open CubeExtension

theorem cubical_extends_of_extension
    (h₁ : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f))
    (h₂ : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t)) : Semi.cubical_extendsSt.{0} := by
  intro V _ _ _ K _ _ _ G _ _ _ _ _ _ eA heA L t hc ht
  have s₂ := smooth_tensor G G
  have s₃ := smooth_tensor G (G ⊗ G)
  have c₂ := geometricallyConnected_tensor G G
  have c₃ := geometricallyConnected_tensor G (G ⊗ G)
  obtain ⟨ρ, hρ, hv⟩ := exists_gen L.isLB (formEq_origin G) (LB.oneGen L.L) (LB.isGen_oneGen L.L)
  refine h₂ V K (G3 G).left G.left (G3 G).hom (eSec (G3 G)) s₃ (h₁ _ _ _ s₃ c₃) (eSec_comp _) eA heA
    L.L L.isLB thK (thφ G (x3 G)) thε t ρ ht hρ (corr_of_val L.isLB fun y J hJ => ?_)
  refine (val_corr hJ hc (𝟙 _)).trans ((val_one _).trans (Eq.symm ?_))
  exact (val_pull hJ ρ _ _).trans ((hv _ _ y J hJ).trans (val_one _))

theorem extendGen_of_extension
    (h₁ : (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f))
    (h₂ : (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t)) : Semi.extendGenSt.{0} := by
  intro V _ _ _ K _ _ _ G _ _ _ _ _ _ eA heA N r hr hc
  obtain ⟨c, ⟨hc₁, hc₂⟩, hu⟩ := h₂ V K G.left G.left G.hom (eSec G) inferInstance
    (h₁ _ _ _ inferInstance inferInstance) (eSec_comp _) eA heA N.L N.isLB PUnit (fun _ => 𝟙 _)
    (fun _ => 1) r N.rig hr N.rigGen hc
  obtain ⟨r', ⟨h₃, h₄⟩, hu'⟩ := existsUnique_genPull_eq (𝟙 G.left)
    (fun _ => Function.bijective_id) N.L c hc₁
  refine ⟨r', ⟨h₃, ?_⟩, fun r'' ⟨h₅, h₆⟩ => hu' r'' ⟨h₅, hu _ ⟨LB.isGen_genPull _ _ h₅ _, ?_⟩⟩⟩
  · rw [← h₄, pullGen_genPull] at hc₂
    exact hc₂
  · rw [pullGen_genPull]
    exact h₆

theorem cubical_extends_and_extendGen :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) →
    (∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (H X : Scheme.{0}) (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H), Smooth p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K)), eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e → ∀ (L : LB X), L.IsLB → ∀ (I : Type) [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ) (t : LB.Gen (LB.LinComb L (fun i => pullback.fst p (etaK V K) ≫ φ i) ε)) (ρ : LB.Gen (LB.LinComb L (fun i => e ≫ φ i) ε)), t.IsGen → ρ.IsGen → LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K)) → ∃! c : LB.Gen (LB.LinComb L φ ε), c.IsGen ∧ LB.pullGen L _ _ c (pullback.fst p (etaK V K)) = t) →
    Semi.cubical_extendsSt.{0} ∧ Semi.extendGenSt.{0} :=
  fun h₁ h₂ => ⟨cubical_extends_of_extension h₁ h₂, extendGen_of_extension h₁ h₂⟩

end GlobalTheory
end
