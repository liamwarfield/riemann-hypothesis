module

public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionOfIntegralSectionIsIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpandsAtDvdOfSecIsMul
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace WeightDvd

theorem gs_comp_stalkMap {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ g) z U a = (r.stalkMap z).hom (gs g (r z) U a) := by
  rw [← gs_pull r g z U h, gs_stalkMap r z _ h]
  exact congrArg _ ((gs_pull (𝟙 Y) g (r z) U h a).trans (by rw [Category.id_comp]))

theorem appLE_dvd {P T : Scheme.{0}} [IsAffine P] (p : P ⟶ T) (W : T.Opens) (e : ⊤ ≤ p ⁻¹ᵁ W) (u v : Γ(T, W))
    (h : ∀ w ∈ W, gs (𝟙 T) w W u ∣ gs (𝟙 T) w W v) : (p.appLE W ⊤ e).hom u ∣ (p.appLE W ⊤ e).hom v := by
  rw [← Ideal.mem_span_singleton, (isAffineOpen_top P).mem_ideal_iff]
  intro z hz
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
  have k : ∀ c : Γ(T, W), (P.presheaf.germ ⊤ z hz).hom ((p.appLE W ⊤ e).hom c) =
      (p.stalkMap z).hom (gs (𝟙 T) (p z) W c) := fun c =>
    ((gs_eq (𝟙 P) z ⊤ hz _).symm.trans (gs_appLE p W ⊤ e (𝟙 P) z hz c)).trans
      ((by rw [Category.id_comp] : gs (𝟙 P ≫ p) z W c = gs p z W c).trans (gs_stalkMap p z W (e hz) c))
  have := map_dvd (p.stalkMap z).hom (h (p z) (e hz))
  rw [← k, ← k] at this
  exact this

theorem dvd_of_sum {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S) {V : Y.left.Opens} (hV : IsAffineOpen V)
    (s : Finset X) (a : Γ(Y.left, V)) (h : X → Γ(Y.left, V))
    (hs : ∀ w : (splitTorus S X ⊗ Y).left, (snd (splitTorus S X) Y).left w ∈ V →
      gs (snd (splitTorus S X) Y).left w V a ∣
        ∑ χ ∈ s, gs (𝟙 _) w ⊤ (TorusInj.chiP X Y χ) * gs (snd (splitTorus S X) Y).left w V (h χ)) :
    ∀ χ ∈ s, a ∣ h χ := by
  intro χ₀ hχ₀
  have k : ∀ (w : (splitTorus S X ⊗ Y).left) (hw : (snd (splitTorus S X) Y).left w ∈ V) (c : Γ(Y.left, V)),
      gs (𝟙 _) w ((snd (splitTorus S X) Y).left ⁻¹ᵁ V) (((snd (splitTorus S X) Y).left.app V).hom c) =
        gs (snd (splitTorus S X) Y).left w V c := fun w hw c =>
    (gs_pull (𝟙 _) _ w V hw c).trans (by rw [Category.id_comp])
  have H := appLE_dvd (TorusInj.pt (X := X) hV) _ (TorusInj.pt_le hV) (((snd (splitTorus S X) Y).left.app V).hom a)
    (∑ χ ∈ s, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP X Y χ) *
      ((snd (splitTorus S X) Y).left.app V).hom (h χ)) fun w hw => by
      rw [k w hw, gs_fsum (𝟙 _) w _ hw]
      refine (hs w hw).trans (dvd_of_eq (Finset.sum_congr rfl fun χ _ => ?_))
      rw [gs_mul (𝟙 _) w _ hw, k w hw, gs_res (𝟙 _) w _ hw]
  have H' : TorusInj.ev hV (((snd (splitTorus S X) Y).left.app V).hom a) ∣ TorusInj.ev hV
      (∑ χ ∈ s, ((splitTorus S X ⊗ Y).left.presheaf.map (homOfLE le_top).op).hom (TorusInj.chiP X Y χ) *
      ((snd (splitTorus S X) Y).left.app V).hom (h χ)) :=
    map_dvd (Scheme.ΓSpecIso (TorusInj.GA (X := X) (V := V))).hom.hom H
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, TorusInj.ev_chi, TorusInj.ev_snd, AddMonoidAlgebra.single_mul_single,
    add_zero, _root_.one_mul] at H'
  obtain ⟨g, hg⟩ := H'
  have hc := congrArg (fun f => f.coeff χ₀) hg
  rw [TorusInj.coeff_sum_single X s _ χ₀ hχ₀] at hc
  refine ⟨g.coeff χ₀, hc.trans ?_⟩
  simp

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)

theorem val_act (β : D.toPre.X) (w : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left) {J}
    (hJ : Good D.toPre.P.L w J) :
    (val (tG U e β) (WeightPf.act (U.gt e)).left w J).val =
      gs (𝟙 _) w ⊤ (TorusInj.chiP D.toPre.X (thickObj R I e G) β) *
        (val (tG U e β) (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w J).val := by
  have E := val_corr hJ ((U.gt e).t_weight β) (𝟙 _)
  rw [val_mul hJ, val_pull hJ, val_pull hJ, Category.id_comp, Category.id_comp] at E
  refine (congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  have hm := hJ.mem (L := D.toPre.P.L) (K := PEmpty) (Y := (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left)
    PEmpty.elim (𝟙 _)
  exact (congrArg Units.val (gm_rp₁ (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w ⊤ _ _ hm
    (charUnit _ D.toPre.X β))).trans ((gs_unit _ w ⊤ trivial _).symm.trans
      ((gs_pull (𝟙 _) (fst (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w ⊤ trivial _).trans
        (by rw [Category.id_comp])).symm)

theorem dvd_on_group (r : R) (σ τ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) (hσ : SecIsMul G.hom r σ τ)
    (hE : U.ExpandsAt e k σ f) (α : D.toPre.X) (y : (thickObj R I e G).left) (J) (hJ : Good D.toPre.P.L y J) :
    cst (pGl U e ≫ D.toPre.P.A.hom) y r ∣ sval (f α) (pGl U e) y J := by
  classical
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f hE
  by_cases hα : α ∉ S
  · have := (hS _ (𝟙 _) y J hJ).1 α hα
    rw [Category.id_comp] at this
    rw [this]
    exact dvd_zero _
  push Not at hα
  let jf : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β a => J (pGl U e ≫ D.toPre.famφB β a)
  let jt : D.toPre.X → Fin 4 → D.toPre.P.L.ι := fun β a => J (Oφl U e β a)
  have hy : y ∈ S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) :=
    mem_finf S _ _ fun β _ => ⟨hJ.mem (D.toPre.famφB β) (pGl U e), Set.mem_iInter.2 fun a => hJ _⟩
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVW⟩ := ((thickObj R I e G).left.isBasis_affineOpens).exists_subset_of_mem_open hy
    (S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β))).2
  have hVW' : V ≤ S.inf (fun β => pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) ⊓
      LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) := hVW
  have hVf : ∀ β ∈ S, V ≤ pGl U e ⁻¹ᵁ LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β) :=
    fun β hβ => hVW'.trans ((Finset.inf_le hβ).trans inf_le_left)
  have hVt : ∀ β ∈ S, V ≤ LB.wchart D.toPre.P.L (Oφl U e β) (jt β) :=
    fun β hβ => hVW'.trans ((Finset.inf_le hβ).trans inf_le_right)
  have ex : ∀ β ∈ S, ∃ c : Γ((thickObj R I e G).left, V), ∀ (Z : Scheme.{0}) (ρ : Z ⟶ (thickObj R I e G).left) (z : Z),
      ρ z ∈ V → gs ρ z V c = gs (ρ ≫ pGl U e) z (LB.wchart D.toPre.P.L (D.toPre.famφB β) (jf β)) ((f β).f (jf β)) *
        (gm ρ z (LB.wchart D.toPre.P.L (Oφl U e β) (jt β)) ((tG U e β).s (jt β))).val := fun β hβ =>
    ⟨((pGl U e).appLE _ V (hVf β hβ)).hom ((f β).f (jf β)) * (res (hVt β hβ) ((tG U e β).s (jt β))).val,
      fun Z ρ z hz => (gs_mul ρ z V hz _ _).trans (congrArg₂ (· * ·) (gs_appLE _ _ V _ ρ z hz _)
        ((gs_unit ρ z V hz _).trans (congrArg Units.val (gm_res ρ z _ hz _))))⟩
  choose! c hc using ex
  have hpG := WeightPf.act_left_pG (U.gt e)
  have hb : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  have H := dvd_of_sum D.toPre.X (thickObj R I e G) hV S (constFn (pGl U e ≫ D.toPre.P.A.hom) V r) c (fun w hw => by
    choose d hd using fun ψ : (WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left ⟶ D.toPre.P.A.left =>
      exists_chart D.toPre.P.isLB (ψ w)
    let J₂ : ((WeightPf.Te D.toPre I e ⊗ thickObj R I e G).left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι := fun ψ =>
      if ψ w ∈ D.toPre.P.L.U (J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ)) then
        J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ) else d ψ
    have hJ₂ : Good D.toPre.P.L w J₂ := fun ψ => by
      by_cases h : ψ w ∈ D.toPre.P.L.U (J ((WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫ ψ))
      · simpa only [J₂, if_pos h] using h
      · simpa only [J₂, if_neg h] using hd ψ
    have eJ : ∀ φ : (thickObj R I e G).left ⟶ D.toPre.P.A.left,
        φ ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left w) ∈ D.toPre.P.L.U (J φ) →
        J₂ ((snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φ) = J φ := fun φ h => by
      have e₁ : (WeightPf.sec (D := D.toPre) (G := G) (I := I) (e := e)).left ≫
          (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ φ = φ := by
        rw [← Category.assoc, WeightPf.sec_left_snd, Category.id_comp]
      simp only [J₂, e₁]
      exact if_pos h
    obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB (fGl I G e ((WeightPf.act (U.gt e)).left w))
    have E := (hS _ (WeightPf.act (U.gt e)).left w J₂ hJ₂).2 jL hL
    have hs : sv U k σ ((WeightPf.act (U.gt e)).left ≫ fGl I G e) w jL =
        cst (((WeightPf.act (U.gt e)).left ≫ fGl I G e) ≫ G.hom) w r *
          sv U k τ ((WeightPf.act (U.gt e)).left ≫ fGl I G e) w jL :=
      secIsMul_gs hσ _ w (fun _ => jL) (Set.mem_iInter.2 fun _ => hL)
    have e₂ : ((WeightPf.act (U.gt e)).left ≫ fGl I G e) ≫ G.hom =
        (snd (WeightPf.Te D.toPre I e) (thickObj R I e G)).left ≫ pGl U e ≫ D.toPre.P.A.hom := by
      rw [Category.assoc, ← hb, ← Category.assoc, hpG, Category.assoc]
    rw [hs, e₂, mul_left_comm] at E
    refine (dvd_of_eq (gs_constFn _ V _ w hw r)).trans ((Dvd.intro _ E).trans
      (dvd_of_eq (Finset.sum_congr rfl fun β hβ => ?_)))
    rw [hc β hβ _ _ w hw, val_act U e β w hJ₂, mul_left_comm, hpG,
      sval_of (f β) _ w J₂ (jf β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVf β hβ hw) a)),
      val_of (tG U e β) _ w J₂ (jt β) (fun a => eJ _ (Set.mem_iInter.1 (hVt β hβ hw) a))]) α hα
  obtain ⟨g, hg⟩ := H
  have E := hc α hα _ (𝟙 _) y hyV
  rw [hg, gs_mul (𝟙 _) y V hyV, gs_constFn _ V (𝟙 _) y hyV, Category.id_comp, Category.id_comp] at E
  exact (Units.dvd_mul_right).1 (Dvd.intro _ E)

end WeightDvd

theorem expandsAt_dvd_of_secIsMul : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (r : R) (σ τ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α), SecIsMul G.hom r σ τ → U.ExpandsAt e k σ f → ∀ (α : D.toPre.X) (x : (thickObj R I e D.toPre.P.A).left) (J), Geo.Tor.Good D.toPre.P.L x J → Geo.Tor.cst ((fstG I e D.toPre.P.A).left ≫ D.toPre.P.A.hom) x r ∣ Geo.Tor.sval (f α) (fstG I e D.toPre.P.A).left x J := by
  intro R _ _ I D A G _ _ U e k r σ τ f hσ hE α x J hJ
  have := (U.gt e).q_flat
  obtain ⟨y, rfl⟩ := (U.gt e).q_surj.surj x
  choose J' hJ' using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have H := WeightDvd.dvd_on_group U e k r σ τ f hσ hE α y J' hJ'
  have hm := hJ.mem (D.toPre.famφB α) (fstG I e D.toPre.P.A).left
  have e₁ := WeightDvd.gs_comp_stalkMap (U.gt e).q.left (fstG I e D.toPre.P.A).left y _ hm
    ((f α).f fun a => J ((fstG I e D.toPre.P.A).left ≫ D.toPre.famφB α a))
  have e₂ := WeightDvd.gs_comp_stalkMap (U.gt e).q.left ((fstG I e D.toPre.P.A).left ≫ D.toPre.P.A.hom) y ⊤ trivial
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r)
  have e₃ := sec_trans (f α) (pGl U e) y hm (Good.mem hJ' (D.toPre.famφB α) (pGl U e))
  refine dvd_descend (U.gt e).q.left y ?_
  exact (dvd_of_eq e₂.symm).trans ((H.mul_left _).trans (dvd_of_eq (e₃.symm.trans e₁)))

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocal
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.IntegralExpansionLocal

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1 GlobalTheory.IntegralExpansion

theorem dvd_gs_of_dvd_sval {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (r : Z ⟶ Y) (z : Z) {c : Z.presheaf.stalk z}
    (h : ∀ J, Good L z J → c ∣ sval s r z J) (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j) :
    c ∣ gs r z (LB.wchart L φ j) (s.f j) := by
  obtain ⟨J, hJ, -⟩ := exists_good L hL z (K := PEmpty) PEmpty.elim PEmpty.elim (fun a => a.elim) (fun a => a.elim)
  rw [sec_trans s r z hj (hJ.mem φ r)]
  exact dvd_mul_of_dvd_right (h J hJ) _

theorem isUnit_cst_of_ne_zero {R : Type} [CommRing R] [IsDomain R] {Z : Scheme.{0}}
    (p : Z ⟶ Spec (CommRingCat.of (FractionRing R))) (z : Z) {r : R} (hr : r ≠ 0) :
    IsUnit (cst (p ≫ jK R) z r) := by
  have hne : algebraMap R (FractionRing R) r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2 hr
  have key : cst (p ≫ jK R) z r = cst p z (algebraMap R (FractionRing R) r) :=
    ReciprocityTheory.ChartRestriction.G.Geo.Tor.cst_comp p (algebraMap R (FractionRing R)) z r
  rw [key]
  refine isUnit_iff_exists_inv.2 ⟨cst p z (algebraMap R (FractionRing R) r)⁻¹, ?_⟩
  rw [← ReciprocityTheory.ChartRestriction.G.H1.cst_mul, mul_inv_cancel₀ hne, ReciprocityTheory.ChartRestriction.G.H1.cst_one]

private theorem injective_app_pullback_fst_of_flat {R : Type} [CommRing R] [IsDomain R] (G : Over (Spec (CommRingCat.of R))) [Flat G.hom]
    (W : G.left.Opens) : Function.Injective ((pullback.fst G.hom (jK R)).app W).hom := by
  haveI : QuasiCompact (pullback.fst G.hom (jK R)) := inferInstance
  haveI : IsSchemeTheoreticallyDominant (jK R) := by
    unfold jK
    exact SchemeDominantSpecMap.isSchemeTheoreticallyDominant_specMap _ (IsFractionRing.injective R (FractionRing R))
  haveI : IsSchemeTheoreticallyDominant (pullback.fst G.hom (jK R)) := inferInstance
  exact Scheme.Hom.app_injective _ W

private theorem isUnit_gs_scal_of_ne_zero {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : (D.BF (FractionRing R)).left)
    {r : R} (hr : r ≠ 0) : IsUnit (gs (𝟙 _) y ⊤ (scal (D.BF (FractionRing R)).hom r)) := by
  unfold scal
  erw [gs_pull (𝟙 _) (D.BF (FractionRing R)).hom y ⊤ trivial, Category.id_comp]
  unfold DegPre.BF
  change IsUnit (cst (TF (FractionRing R) ⊗ D.P.A).hom y r)
  rw [← Over.w (fst (TF (FractionRing R)) D.P.A)]
  unfold TF
  simp only [Over.mk_hom]
  rw [← Category.assoc]
  exact isUnit_cst_of_ne_zero _ y hr

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ maximalIdeal R → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (σ : H0 U.LG.L k) (s : U.SecK k), GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R)) 1 → ∀ E : Fam D.toPre (FractionRing R) k, U.Expands k s E → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ g) ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
  intro R _ _ _ _ I hI D A G _ _ U k σ s hs E hE
  obtain ⟨r, hr, σ', f, hσ', hf, hexp⟩ := hE
  have hLG : U.LG.L.IsLB := U.LG.isLB
  have hP : D.toPre.P.L.IsLB := D.toPre.P.isLB
  haveI : Smooth G.hom := U.smooth
  have hinj : ∀ W : G.left.Opens, Function.Injective ((pullback.fst G.hom (jK R)).app W).hom :=
    fun W => injective_app_pullback_fst_of_flat G W
  have hσ'' : GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ)) s
      (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)) σ' (pullback.fst G.hom (jK R))
      (scal (pullback.fst G.hom (jK R) ≫ G.hom) r) := by
    rw [pullback.condition]
    exact hσ'
  have h2 : SecIsMul G.hom r σ' σ := GlobalTheory.IntegralExpansion.secIsMul_of_secScal hLG G.hom hinj hs hσ''
  have h3 := fun e => GlobalTheory.expandsAt_dvd_of_secIsMul R I D A G U e k r σ' σ f h2 (hexp e)
  haveI : Smooth D.toPre.P.A.hom := D.toPre.P.isAb.smooth
  haveI : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  have h4 : ∀ α, ∃ g : D.toPre.SecB k α, SecIsMul D.toPre.P.A.hom r (f α) g := by
    intro α
    refine GlobalTheory.GermDiv.main R I (hI.trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge)
      D.toPre.P.A _ (linComb_isLB _ hP _ _) (f α) r hr ?_
    intro n x j hx
    exact dvd_gs_of_dvd_sval hP (f α) (fstG I n D.toPre.P.A).left x (fun J hJ => h3 n α x J hJ) j hx
  choose g hg using h4
  refine ⟨g, fun e => expandsAt_cancel_of_ne_zero R I D A G U k r hr σ σ' g f h2 hg hexp e, ?_⟩
  intro α
  have hga := hg α
  unfold SecIsMul at hga
  refine ReciprocityTheory.ChartRestriction.G.DVR.SectionScalarValuation.secScal_of_sval hP (fun y J hJ => ?_)
  have e1 := GlobalTheory.IntegralExpansion.sval_of_secScal (hf α) (𝟙 _) y hJ
  have hm := hJ.mem (D.toPre.famφB α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left)
  have e2 : sval (f α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y J =
      gs (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y ⊤ (scal D.toPre.P.A.hom r) *
        sval (g α) (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y J := by
    unfold sval
    erw [hga, gs_mul _ _ _ hm, gs_res _ _ le_top hm]
  rw [e2] at e1
  have e3 : gs (𝟙 _ ≫ (D.toPre.prB (FractionRing R)).left) y ⊤ (scal D.toPre.P.A.hom r) =
      gs (𝟙 _) y ⊤ (scal (D.toPre.BF (FractionRing R)).hom r) := by
    unfold scal
    rw [Category.id_comp]
    erw [gs_pull (D.toPre.prB (FractionRing R)).left D.toPre.P.A.hom y ⊤ trivial,
      gs_pull (𝟙 _) (D.toPre.BF (FractionRing R)).hom y ⊤ trivial, Category.id_comp, Over.w]
  rw [e3] at e1
  have hu : IsUnit (gs (𝟙 _) y ⊤ (scal (D.toPre.BF (FractionRing R)).hom r)) := isUnit_gs_scal_of_ne_zero D.toPre y hr
  exact hu.mul_left_cancel e1

end GlobalTheory.IntegralExpansionLocal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExpansionIntegralSectionIntegralNoetherianLocalStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
theorem _root_.GlobalTheory.T.expansion_integralSection_integral_noetherianLocal : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R), I ≤ maximalIdeal R → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (σ : H0 U.LG.L k) (s : U.SecK k), GeneratorPullback.SecScal U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) (fun _ => ((k : ℕ) : ℤ)) s (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((k : ℕ) : ℤ)) σ (pullback.fst G.hom (jK R)) 1 → ∀ E : Fam D.toPre (FractionRing R) k, U.Expands k s E → ∃ g : ∀ α : D.toPre.X, D.toPre.SecB k α, (∀ e, U.ExpandsAt e k σ g) ∧ ∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing R) α) (DegPre.famε k) (E.s α) (D.toPre.famφB α) (DegPre.famε k) (g α) (DegPre.prB D.toPre (FractionRing R)).left 1 := by
  first | exact @GlobalTheory.IntegralExpansionLocal.main | exact GlobalTheory.IntegralExpansionLocal.main | (intros; apply GlobalTheory.IntegralExpansionLocal.main <;> assumption)
end
