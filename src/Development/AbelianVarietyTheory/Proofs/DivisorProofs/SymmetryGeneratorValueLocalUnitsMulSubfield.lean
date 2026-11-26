module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportDownLineBundleIso
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportDownLineBundleIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

namespace GlobalTheory.GenTransport

theorem exists_gen_down_pmaps : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {Ix : Type} [Fintype Ix]
    (w : LB.Iso L' (L.pull F)), w.IsGen → L.IsLB → L'.IsLB → ∀ (φ' : Ix → (Y ⟶ X')) (ε : Ix → ℤ)
    (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε), t.IsGen ∧ PMaps w φ' (fun k => φ' k ≫ F) ε a t (𝟙 Y) := by
  intro X X' Y L L' F Ix _ w hw hL hL' φ' ε a ha
  obtain ⟨t, ht, hv⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.exists_up ((isGen_iff w).1 hw) hL hL' a ha
  refine ⟨t, ht, fun Z r z p q hp hq => ?_⟩
  rw [Category.comp_id]
  exact hv Z r z p q (Set.mem_iInter.2 hp) (Set.mem_iInter.2 hq)

end GlobalTheory.GenTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTransportDownLineBundleIsoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generator_transport_down_lineBundleIso : ∀ {X X' Y : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {Ix : Type} [Fintype Ix]
    (w : LB.Iso L' (L.pull F)), w.IsGen → L.IsLB → L'.IsLB → ∀ (φ' : Ix → (Y ⟶ X')) (ε : Ix → ℤ)
    (a : LB.Gen (LB.LinComb L' φ' ε)), a.IsGen →
    ∃ t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε), t.IsGen ∧ PMaps w φ' (fun k => φ' k ≫ F) ε a t (𝟙 Y) := by
  first | exact @GlobalTheory.GenTransport.exists_gen_down_pmaps | exact GlobalTheory.GenTransport.exists_gen_down_pmaps | (intros; apply GlobalTheory.GenTransport.exists_gen_down_pmaps <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValuesMemSubfieldGaloisDescent
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValuesMemSubfieldGaloisDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.Poinc.Sep

theorem spMap_two {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem gen_unique_of_eq {X Y S₀ : Scheme.{0}} {M : LB X} (hM : M.IsLB) {Ix : Type} [Fintype Ix]
    {φ φ' : Ix → (Y ⟶ X)} {ε : Ix → ℤ} (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (hφ : φ' = φ) {u : LB.Gen (LB.LinComb M φ' ε)}
    {u' : LB.Gen (LB.LinComb M φ ε)} (hu : u.IsGen) (hu' : u'.IsGen)
    (h : ∀ y J, Good M y J → val u e y J = val u' e y J) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι)
    (hJ : Good M z J) : val u r z J = val u' r z J := by
  subst hφ
  exact gen_unique hM p e he hp hu hu' h Z r z J hJ

theorem gen_values_mem : ∀ (V₁ W₀ : Type) [CommRing V₁] [CommRing W₀] (ib : W₀ →+* V₁) (A : Over (Sp V₁)) [GrpObj A],
    IsAbelianScheme A → ∀ (B₀ : Over (Sp W₀)) (β : A.left ⟶ B₀.left), IsPullback β A.hom B₀.hom (spMap ib) →
    ∀ (M₀ : LB B₀.left), M₀.IsLB → ∀ (Ix : Type) [Fintype Ix] (φ : Ix → (A.left ⟶ B₀.left))
    (ψ : Ix → (B₀.left ⟶ B₀.left)), (∀ k, φ k = β ≫ ψ k) → ∀ (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb M₀ φ ε)),
    t.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    (∀ a, ev (ib a) ∈ k₀) → ∀ x₁ : Sp K ⟶ A.left, x₁ ≫ A.hom = spMap ev → DefOver k₀ (x₁ ≫ β) →
    (∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → val t x₁ z J = 1) →
    ∀ x : Sp K ⟶ A.left, x ≫ A.hom = spMap ev → DefOver k₀ (x ≫ β) →
    ∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → ∃ c ∈ k₀, (val t x z J).val = toStk z c := by
  intro V₁ W₀ _ _ ib A _ hA B₀ β hβ M₀ hM₀ Ix _ φ ψ hφ ε t ht K _ _ ev k₀ hk₀ hk x₁ hx₁ hd₁ h1 x hx hd z J hJ
  classical
  have hf : ∀ a, (ev.comp ib) a ∈ k₀ := hk
  let v : (Sp K ⟶ A.left) → ((Sp K ⟶ B₀.left) → M₀.ι) → K := fun x J =>
    valF x (LB.wchart M₀ φ (fun k => J (x ≫ φ k))) ((genSec t ht).f (fun k => J (x ≫ φ k)))
  have hv : ∀ x z J, Good M₀ z J → (val t x z J).val = toStk z (v x J) := fun x z J hJ =>
    (sval_genSec t ht x z hJ).symm.trans (toStk_valF_gs x _ z (hJ.mem φ x) _).symm
  have hfix : ∀ x : Sp K ⟶ A.left, DefOver k₀ (x ≫ β) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) →
      ∀ k, spMap σ.toRingHom ≫ x ≫ φ k = x ≫ φ k := by
    intro x hd σ hσ k
    obtain ⟨P₀, hP₀⟩ := hd
    rw [hφ k, ← Category.assoc x, ← hP₀, Category.assoc, ← Category.assoc (spMap σ.toRingHom),
      spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
  have hvσ : ∀ x : Sp K ⟶ A.left, DefOver k₀ (x ≫ β) → ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∀ z J, Good M₀ z J →
      (val t (spMap σ.toRingHom ≫ x) z J).val = toStk z (σ (v x J)) := fun x hd σ hσ z J hJ =>
    (sval_genSec t ht _ z hJ).symm.trans (sval_spMap _ σ.toRingHom x z hJ (hfix x hd σ hσ))
  have hsurj : Function.Surjective (pullback.snd A.hom (spMap ev)).appTop.hom :=
    fun w => TLinPf.const_pullback GlobalTheory.SemiRigid.globalFns (spMap ev) A hA w
  have key : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → σ (v x J) = v x J := by
    intro σ hσ
    have hc : (pullback.fst A.hom (spMap ev) ≫ β) ≫ B₀.hom =
        (pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom ≫ spMap ev) ≫ spMap ib := by
      simp only [Category.assoc]
      rw [hβ.w, pullback.condition_assoc, spMap_two, spMap_conj k₀ _ hf σ hσ]
    obtain ⟨l, hl1, hl2⟩ : ∃ l : pullback A.hom (spMap ev) ⟶ A.left, l ≫ β = pullback.fst A.hom (spMap ev) ≫ β ∧
        l ≫ A.hom = pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom ≫ spMap ev :=
      ⟨hβ.lift _ _ hc, hβ.lift_fst _ _ hc, hβ.lift_snd _ _ hc⟩
    obtain ⟨σt, hs1, hs2⟩ : ∃ σt : pullback A.hom (spMap ev) ⟶ pullback A.hom (spMap ev),
        σt ≫ pullback.fst A.hom (spMap ev) = l ∧
        σt ≫ pullback.snd A.hom (spMap ev) = pullback.snd A.hom (spMap ev) ≫ spMap σ.toRingHom :=
      ⟨pullback.lift l _ (by rw [hl2, Category.assoc]), pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
    have hσβ : σt ≫ pullback.fst A.hom (spMap ev) ≫ β = pullback.fst A.hom (spMap ev) ≫ β := by
      rw [reassoc_of% hs1, hl1]
    have hpt : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev), DefOver k₀ (y ≫ β) →
        pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp]) ≫ σt =
          spMap σ.toRingHom ≫ pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp]) := by
      intro y hy hd
      obtain ⟨P₀, hP₀⟩ := hd
      apply pullback.hom_ext
      · simp only [Category.assoc, hs1, pullback.lift_fst]
        apply hβ.hom_ext
        · simp only [Category.assoc, hl1, pullback.lift_fst_assoc]
          rw [← hP₀, ← Category.assoc, spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
        · simp only [Category.assoc, hl2, pullback.lift_snd_assoc, Category.id_comp, hy]
      · simp only [Category.assoc, hs2, pullback.lift_snd_assoc, Category.id_comp, pullback.lift_snd, Category.comp_id]
    let tK := LB.pullGen M₀ φ ε t (pullback.fst A.hom (spMap ev))
    have htK : tK.IsGen := DVR.pullGen_isGen _ _ _ _ ht _
    have hu : (LB.pullGen M₀ _ ε tK σt).IsGen := DVR.pullGen_isGen _ _ _ _ htK _
    have hval : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev), DefOver k₀ (y ≫ β) → ∀ z J, Good M₀ z J →
        val (LB.pullGen M₀ _ ε tK σt) (pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp])) z J =
          val t (spMap σ.toRingHom ≫ y) z J := by
      intro y hy hd z J hJ
      rw [val_pull hJ, hpt y hy hd, val_pull hJ, Category.assoc, pullback.lift_fst]
    have hvalK : ∀ (y : Sp K ⟶ A.left) (hy : y ≫ A.hom = spMap ev) z J, Good M₀ z J →
        val tK (pullback.lift y (𝟙 _) (by rw [hy, Category.id_comp])) z J = val t y z J := by
      intro y hy z J hJ
      rw [val_pull hJ, pullback.lift_fst]
    have huniq := gen_unique_of_eq hM₀ (pullback.snd A.hom (spMap ev))
      (pullback.lift x₁ (𝟙 _) (by rw [hx₁, Category.id_comp])) (pullback.lift_snd _ _ _) hsurj
      (funext fun k => by rw [hφ k]; exact (reassoc_of% hσβ) (ψ k)) hu htK (fun y J hJ => by
        rw [hval x₁ hx₁ hd₁ y J hJ, hvalK x₁ hx₁ y J hJ, h1 y J hJ]
        apply Units.ext
        have e1 := hv x₁ y J hJ
        rw [h1 y J hJ, Units.val_one, ← map_one (toStk y)] at e1
        rw [hvσ x₁ hd₁ σ hσ y J hJ, ← (toStk y).injective e1, map_one, map_one, Units.val_one])
      (Sp K) (pullback.lift x (𝟙 _) (by rw [hx, Category.id_comp])) z J hJ
    rw [hval x hx hd z J hJ, hvalK x hx z J hJ] at huniq
    have e2 := congrArg Units.val huniq
    rw [hvσ x hd σ hσ z J hJ, hv x z J hJ] at e2
    exact (toStk z).injective e2
  refine ⟨v x J, ?_, hv x z J hJ⟩
  apply mem_of_finite_conj k₀ hk₀
  apply (Set.finite_singleton (v x J)).subset
  rintro b ⟨σ, hσ, rfl⟩
  exact key σ hσ

end GlobalTheory.Poinc.Sep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeneratorValuesMemSubfieldGaloisDescentStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.generator_values_mem_subfield_galoisDescent : ∀ (V₁ W₀ : Type) [CommRing V₁] [CommRing W₀] (ib : W₀ →+* V₁) (A : Over (Sp V₁)) [GrpObj A],
    IsAbelianScheme A → ∀ (B₀ : Over (Sp W₀)) (β : A.left ⟶ B₀.left), IsPullback β A.hom B₀.hom (spMap ib) →
    ∀ (M₀ : LB B₀.left), M₀.IsLB → ∀ (Ix : Type) [Fintype Ix] (φ : Ix → (A.left ⟶ B₀.left))
    (ψ : Ix → (B₀.left ⟶ B₀.left)), (∀ k, φ k = β ≫ ψ k) → ∀ (ε : Ix → ℤ) (t : LB.Gen (LB.LinComb M₀ φ ε)),
    t.IsGen → ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    (∀ a, ev (ib a) ∈ k₀) → ∀ x₁ : Sp K ⟶ A.left, x₁ ≫ A.hom = spMap ev → DefOver k₀ (x₁ ≫ β) →
    (∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → val t x₁ z J = 1) →
    ∀ x : Sp K ⟶ A.left, x ≫ A.hom = spMap ev → DefOver k₀ (x ≫ β) →
    ∀ (z : Sp K) (J : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z J → ∃ c ∈ k₀, (val t x z J).val = toStk z c := by
  first | exact @GlobalTheory.Poinc.Sep.gen_values_mem | exact GlobalTheory.Poinc.Sep.gen_values_mem | (intros; apply GlobalTheory.Poinc.Sep.gen_values_mem <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryGeneratorValueLocalUnitsMulSubfield
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

noncomputable section

namespace GlobalTheory.USep.EvG.SymVal

theorem sym_val : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a : D.X, ∃ c ∈ k₀, (val D.sym (spMap ev ≫ (D.c a).left) z J).val =
      ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (-a)).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left)).val * toStk z c := by
  intro V₁ _ _ _ _ _ D τ₀ W₀ _ ib B₀ _ M₀ c₀ τ₁ β w hFB K _ _ ev k₀ hk₀ hk z J J₀ hJ hJ₀ a
  obtain ⟨-, hM₀, hpb, hw, hc, -, -⟩ := hFB
  set φ' : Fin 2 → (D.P.A.left ⟶ D.P.A.left) := ![(ι[D.P.A]).left, 𝟙 D.P.A.left] with hφ'
  obtain ⟨t, ht, hmap⟩ := GlobalTheory.T.exists_generator_transport_down_lineBundleIso w hw hM₀ D.P.isLB φ' ![1, -1] D.sym D.sym_gen
  have hφ : ∀ k, φ' k ≫ β = β ≫ (![(ι[B₀]).left, 𝟙 B₀.left] : Fin 2 → (B₀.left ⟶ B₀.left)) k := by
    intro k
    fin_cases k
    · exact GlobalTheory.PolDeg.SymPol.inv_comm hpb
    · simp [hφ']
  have hpt : ∀ b : D.X, (spMap ev ≫ (D.c b).left) ≫ D.P.A.hom = spMap ev := fun b => by
    rw [Category.assoc, Over.w (D.c b)]; rfl
  have hdef : ∀ b : D.X, DefOver k₀ ((spMap ev ≫ (D.c b).left) ≫ β) := fun b => by
    have e : (spMap ev ≫ (D.c b).left) ≫ β = spMap (ev.comp ib) ≫ c₀ b := by
      rw [Category.assoc]
      erw [hc b]
      rw [← Category.assoc]
      congr 1
      simp only [spMap, ← Spec.map_comp]
      rfl
    rw [e]
    exact GlobalTheory.Poinc.Sep.defOver_comp k₀ (GlobalTheory.Poinc.Sep.defOver_spMap k₀ _ hk) _

  have read : ∀ (x : Sp K ⟶ D.P.A.left) (z' : Sp K) (I : (Sp K ⟶ D.P.A.left) → D.P.L.ι)
      (I₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z' I → Good M₀ z' I₀ →
      val t x z' I₀ = gwx w z' I I₀ (x ≫ (ι[D.P.A]).left) * (gwx w z' I I₀ x)⁻¹ * val D.sym x z' I := by
    intro x z' I I₀ hI hI₀
    have H := hmap (Sp K) x z' (fun k => I₀ ((x ≫ φ' k) ≫ β)) (fun k => I (x ≫ φ' k))
      (fun k => hI₀ ((x ≫ φ' k) ≫ β)) (fun k => hI (x ≫ φ' k))
    rw [Category.comp_id, Fin.prod_univ_two] at H
    rw [val_of t x z' I₀ (fun k => I₀ ((x ≫ φ' k) ≫ β)) (fun k => by rw [Category.assoc]), H]
    simp only [hφ', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, zpow_one, zpow_neg, Category.comp_id]
    rfl
  have hx₁ : (spMap ev ≫ (D.c 0).left) ≫ (ι[D.P.A]).left = spMap ev ≫ (D.c 0).left := by
    rw [Category.assoc, ← Over.comp_left, ← GlobalTheory.PsiEvenPull.c_neg, neg_zero]
  have hnorm : ∀ (z' : Sp K) (I₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good M₀ z' I₀ →
      val t (spMap ev ≫ (D.c 0).left) z' I₀ = 1 := by
    intro z' I₀ hI₀
    choose I hI using fun χ : Sp K ⟶ D.P.A.left => exists_chart D.P.isLB (χ z')
    have hIg : Good D.P.L z' I := hI
    rw [read _ z' I I₀ hIg hI₀, hx₁, _root_.mul_inv_cancel, _root_.one_mul, GlobalTheory.Poinc.ThetaOne.c_zero]
    have e1 : (1 : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A).left = eSec D.P.A := rfl
    rw [e1, ← val_pull hIg, val_corr hIg D.sym_rig, val_one]
  obtain ⟨c, hc₀, hv⟩ := GlobalTheory.T.generator_values_mem_subfield_galoisDescent V₁ W₀ ib D.P.A D.P.isAb B₀ β hpb.1 M₀ hM₀ (Fin 2) (fun k => φ' k ≫ β) _ hφ
    ![1, -1] t ht K ev k₀ hk₀ hk _ (hpt 0) (hdef 0) hnorm _ (hpt a) (hdef a) z J₀ hJ₀
  refine ⟨c, hc₀, ?_⟩
  have r := read (spMap ev ≫ (D.c a).left) z J J₀ hJ hJ₀
  have hneg : (spMap ev ≫ (D.c a).left) ≫ (ι[D.P.A]).left = spMap ev ≫ (D.c (-a)).left := by
    rw [Category.assoc, ← Over.comp_left, ← GlobalTheory.PsiEvenPull.c_neg]
  rw [hneg] at r
  have key : val D.sym (spMap ev ≫ (D.c a).left) z J =
      (gwx w z J J₀ (spMap ev ≫ (D.c (-a)).left))⁻¹ * gwx w z J J₀ (spMap ev ≫ (D.c a).left) *
        val t (spMap ev ≫ (D.c a).left) z J₀ := by
    rw [r]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  rw [key, Units.val_mul, hv]

end GlobalTheory.USep.EvG.SymVal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymmetryGeneratorValueLocalUnitsMulSubfieldStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetryGenerator_value_localUnits_mul_subfield : ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁], IsCN V₁ → (∀ m : ℕ, m ≠ 0 → IsUnit (m : V₁)) →
    ∀ (D : DegPre V₁) (τ₀ : GlobalTheory.UChart.Gens D) (W₀ : Type) [CommRing W₀] (ib : W₀ →+* V₁) (B₀ : Over (Sp W₀)) [GrpObj B₀]
      (M₀ : LB B₀.left) (c₀ : D.X → (Sp W₀ ⟶ B₀.left))
      (τ₁ : ∀ a b : D.X, LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]))
      (β : D.P.A.left ⟶ B₀.left) (w : LB.Iso D.P.L (M₀.pull β)), GlobalTheory.USep.EvG.FromBaseWith D τ₀ ib B₀ M₀ c₀ τ₁ β w →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K), IsAlgClosed k₀ → (∀ a, ev (ib a) ∈ k₀) →
    ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ B₀.left) → M₀.ι), Good D.P.L z J → Good M₀ z J₀ →
    ∀ a : D.X, ∃ c ∈ k₀, (val D.sym (spMap ev ≫ (D.c a).left) z J).val =
      ((GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c (-a)).left))⁻¹ * GlobalTheory.USep.EvG.gwx w z J J₀ (spMap ev ≫ (D.c a).left)).val * toStk z c := by
  first | exact @GlobalTheory.USep.EvG.SymVal.sym_val | exact GlobalTheory.USep.EvG.SymVal.sym_val | (intros; apply GlobalTheory.USep.EvG.SymVal.sym_val <;> assumption)
end
