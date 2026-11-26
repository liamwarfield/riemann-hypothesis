module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CubBoxVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.XValuePf
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.NonemptyTorusExtensionOfIsPowGrp
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpFOfPull
public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineHomOfIsPullbackSpecMap
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecNeZero
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsExpansionSectionLineBundlePower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsHomOfPullbackId
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace LinearUnifIso

theorem exists_hom_of_pullback_id {S : Scheme.{0}} {G G' : Over S} [GrpObj G] [GrpObj G'] {f : S ⟶ S}
    (hf : f = 𝟙 S) (bc : G' ≅ (Over.pullback f).obj G) [IsMonHom bc.hom] :
    ∃ φ : G' ⟶ G, IsMonHom φ ∧ φ.left = bc.hom.left ≫ pullback.fst G.hom f := by
  have h₁ : IsGrpPullback G' G (𝟙 S) (bc.hom.left ≫ pullback.fst G.hom f) :=
    ((isGrpPullback_of_iso bc).comp (isGrpPullback_pullback G f)).congr ((Category.id_comp _).trans hf) rfl
  have : IsMonHom (Iso.refl G).hom := inferInstanceAs (IsMonHom (𝟙 G))
  obtain ⟨e, he, h⟩ := grpPullback_iso h₁ (isGrpPullback_of_iso (Iso.refl G))
  exact ⟨e.hom, he, (Category.comp_id _).symm.trans h⟩

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
  (g : GtCoord I D e G) (g' : GtCoord I D' e G')

theorem mono_torus : Mono g.i := by
  refine ⟨fun a b h => g.isKernel.hom_ext h (toUnit_unique _ _)⟩

theorem hom_ext_torus (hG : GlobalFnsSt) (f₁ f₂ : thickObj R I e G' ⟶ thickObj R I e G) [IsMonHom f₁] [IsMonHom f₂]
    (hq : f₁ ≫ g.q = f₂ ≫ g.q) (hi : g'.i ≫ f₁ = g'.i ≫ f₂) : f₁ = f₂ := by
  obtain ⟨τ, hτ⟩ := TorusCoord.exists_torus g f₁ f₂ hq
  have := mono_torus g
  have := g.i_hom
  have := g'.q_flat
  have := g'.q_surj
  have := g'.q_affine
  have hc : ∀ (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (a : Z ⟶ thickObj R I e G'),
      a ≫ f₁ = (a ≫ τ ≫ g.i) * (a ≫ f₂) := fun Z a => by
    rw [← MonObj.comp_mul, ← hτ]
  have h1 : τ = 1 := by
    refine (splitTorusPointsEquiv _ D.X _).injective (MonoidHom.ext fun χ => Units.ext ?_)
    rw [map_one]
    refine (splitTorusPointsEquiv_val _ D.X _ τ χ.toAdd).trans ?_
    refine eq_one_of_fibre_const_of_section hG _ _ _ (TLinPf.isAb_pullback _ _ D'.P.isAb) g'.q _
      η[thickObj R I e G'] (fun Z a b hab => ?_) ?_
    · obtain ⟨σ, hσ⟩ := TorusCoord.exists_torus g' a b hab
      have e₁ : a ≫ τ = b ≫ τ := by
        rw [← cancel_mono g.i, Category.assoc, Category.assoc]
        have ha := hc Z a
        have hb := hc Z b
        have k₁ : a ≫ f₁ = (σ ≫ g'.i ≫ f₂) * (b ≫ f₁) := by
          rw [hσ, MonObj.mul_comp, Category.assoc, hi]
        have k₂ : a ≫ f₂ = (σ ≫ g'.i ≫ f₂) * (b ≫ f₂) := by
          rw [hσ, MonObj.mul_comp, Category.assoc]
        rw [k₁, k₂, hb, mul_left_comm] at ha
        rw [mul_left_comm] at ha
        rw [mul_left_comm (a ≫ τ ≫ g.i)] at ha
        exact (mul_right_cancel (mul_left_cancel ha)).symm
      rw [← FunDescent.comp_appTop_apply, ← FunDescent.comp_appTop_apply, ← Over.comp_left,
        ← Over.comp_left, e₁]
    · have e₁ : η[thickObj R I e G'] ≫ τ = 1 := by
        rw [← cancel_mono g.i, MonObj.one_comp, Category.assoc]
        have ha := hc _ η[thickObj R I e G']
        rw [IsMonHom.one_hom f₁, IsMonHom.one_hom f₂] at ha
        exact (mul_eq_right.1 ha.symm)
      rw [← FunDescent.comp_appTop_apply, ← Over.comp_left, e₁]
      refine (splitTorusPointsEquiv_val _ D.X _ 1 χ.toAdd).symm.trans ?_
      rw [map_one]
      rfl
  rw [hτ, h1, MonObj.one_comp, _root_.one_mul]

theorem exists_torus_map (h : thickObj R I e G' ⟶ thickObj R I e G)
    (b : thickObj R I e D'.P.A ⟶ thickObj R I e D.P.A) [IsMonHom b] (hq : h ≫ g.q = g'.q ≫ b)
    {F : D'.P.A.left ⟶ D.P.A.left} (w : LB.Iso D'.P.L (D.P.L.pull F)) (xe : D'.X → D.X)
    (hψ : ∀ x κ, D'.Oφ g'.pG x κ ≫ F = h.left ≫ D.Oφ g.pG (xe x) κ)
    (H : ∀ x, PMaps w (D'.Oφ g'.pG x) (D.Oφ g.pG (xe x)) Oinvε (g'.t x) (g.t (xe x)) h.left) :
    ∃ s : splitTorus _ D'.X ⟶ splitTorus _ D.X, s ≫ g.i = g'.i ≫ h ∧
      ∀ x z, gm s.left z ⊤ (charUnit _ D.X (xe x)) = gm (𝟙 _) z ⊤ (charUnit _ D'.X x) := by
  have hd : (g'.i ≫ h) ≫ g.q = toUnit _ ≫ η[thickObj R I e D.P.A] := by
    rw [Category.assoc, hq, ← Category.assoc, g'.isKernel.w, Category.assoc, IsMonHom.one_hom]
  have hs := g.isKernel.lift_fst _ _ hd
  refine ⟨_, hs, fun x z => ?_⟩
  obtain ⟨J, hJ⟩ := TorusCoord.exists_good' D.P.isLB z
  obtain ⟨J', hJ'⟩ := TorusCoord.exists_good' D'.P.isLB z
  have v₁ := PowTorus.val_on_torus g (xe x) hJ (g.isKernel.lift _ _ hd)
  have v₂ := PowTorus.val_on_torus g' x hJ' (𝟙 _)
  rw [hs] at v₁
  rw [Category.id_comp] at v₂
  have v₃ : val (g.t (xe x)) (g'.i.left ≫ h.left) z J =
      (∏ k, gw w (g'.i.left ≫ D'.Oφ g'.pG x k) z (J ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F))
        (J' (g'.i.left ≫ D'.Oφ g'.pG x k)) ^ Oinvε k) * val (g'.t x) g'.i.left z J' :=
    (val_of _ (g'.i.left ≫ h.left) z J (fun k => J ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F)) (fun k => by
      rw [Category.assoc, Category.assoc, hψ])).trans
    (H x _ g'.i.left z _ _ (fun k => hJ ((g'.i.left ≫ D'.Oφ g'.pG x k) ≫ F))
      (fun k => hJ' (g'.i.left ≫ D'.Oφ g'.pG x k)))
  rw [PowTorus.prod_on_torus g' x (fun ψ => gw w ψ z (J (ψ ≫ F)) (J' ψ)), _root_.one_mul] at v₃
  exact v₁.symm.trans (v₃.trans v₂)

theorem gm_torusEnd {S : Scheme.{0}} {X : Type} [AddCommGroup X] {u : X → X}
    {t : splitTorus S X ⟶ splitTorus S X} (ht : TorusEndOf X u t) {Z : Scheme.{0}}
    (r : Z ⟶ (splitTorus S X).left) (z : Z) (χ : X) :
    gm (r ≫ t.left) z ⊤ (charUnit S X χ) = gm r z ⊤ (charUnit S X (u χ)) := by
  rw [← ht χ]
  exact ((gm_res r z (V := ⊤) _ trivial _).trans (gm_pull r t.left z ⊤ trivial _)).symm

theorem gm_comp_of_id {X Y Z : Scheme.{0}} (s : Y ⟶ X) (a : Γ(X, ⊤)ˣ) (a' : Γ(Y, ⊤)ˣ)
    (h : ∀ y, gm s y ⊤ a = gm (𝟙 Y) y ⊤ a') (r : Z ⟶ Y) (z : Z) : gm (r ≫ s) z ⊤ a = gm r z ⊤ a' := by
  have e : pullU s ⊤ a = a' := unit_ext fun y _ =>
    (gm_pull (𝟙 Y) s y ⊤ trivial a).trans (by rw [Category.id_comp]; exact h y)
  rw [← e]
  exact (gm_pull r s z ⊤ trivial a).symm

end LinearUnifIso


open LinearUnifIso in
theorem act_comm_of_isPullUnif_id : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom bc.hom → IsPullUnif (RingHom.id R) hD bc U U' → ∀ (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X] (ιD : D.toPre.OAct O) (ιD' : D'.toPre.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG' → (∀ (x : O) (y : D'.toPre.X), hD.xe (x • y) = x • hD.xe y) → (∀ x, (ιD'.onB.act x).left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ≫ (ιD.onB.act x).left) → ∀ x, ιG'.act x ≫ bc.hom = bc.hom ≫ (Over.pullback (specOf (RingHom.id R))).map (ιG.act x) := by
  intro hG R _ _ _ I _ hI D D' A A' G G' _ _ _ _ _ sG' U U' hD bc hbc hU O _ _ _ _ ιD ιD' ιA ιA' ιG ιG'
    lin lin' hx hB a
  have hs : specOf (RingHom.id R) = 𝟙 _ := specOf_id R
  have := hD.e_hom
  obtain ⟨φ, hφ, eφ⟩ := exists_hom_of_pullback_id hs bc
  obtain ⟨ψ, hψ, eψ⟩ := exists_hom_of_pullback_id hs hD.e
  obtain ⟨wL, -, he, -, H⟩ := (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').1 hU
  have P : ∀ (e : ℕ) {X Y : Over (Spec (CommRingCat.of R))} (c : X ⟶ Y),
      ((Over.pullback (thick R I e)).map c).left ≫ pullback.fst Y.hom (thick R I e) =
        pullback.fst X.hom (thick R I e) ≫ c.left := fun e _ _ c => pullback.lift_fst _ _ _
  have hψa : ιD'.onB.act a ≫ ψ = ψ ≫ ιD.onB.act a := Over.OverMorphism.ext (by
    rw [Over.comp_left, Over.comp_left, eψ]; exact hB a)
  have key : ιG'.act a ≫ φ = φ ≫ ιG.act a := by
    have := sG'.smooth
    have := sG'.geomConnected
    have := U.separated
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I
      (hI ▸ IsLocalRing.maximalIdeal_le_jacobson ⊥) G').2 G _ _ fun e => ?_
    obtain ⟨h, hf, ⟨hp, ht⟩, -⟩ := H e
    obtain rfl : h = ((Over.pullback (thick R I e)).map φ).left := by
      rw [← cancel_mono (pullback.fst G.hom (thick R I e)), P, eφ]
      exact hf
    have hq : (Over.pullback (thick R I e)).map φ ≫ (U.gt e).q =
        (U'.gt e).q ≫ (Over.pullback (thick R I e)).map ψ := by
      refine Over.OverMorphism.ext ?_
      rw [← cancel_mono (pullback.fst D.toPre.P.A.hom (thick R I e)), Over.comp_left, Over.comp_left,
        Category.assoc, Category.assoc, P, eψ]
      exact hp.symm.trans (Category.assoc _ _ _)
    obtain ⟨s, hsi, hsx⟩ := exists_torus_map (U.gt e) (U'.gt e) _ _ hq hD.w hD.xe (fun x => (ht x).1)
      (fun x => (ht x).2)
    obtain ⟨t, tc, ti⟩ := lin.i_lin e a
    obtain ⟨t', tc', ti'⟩ := lin'.i_lin e a
    have := ιG.hom a
    have := ιG'.hom a
    have hts : t' ≫ s = s ≫ t := by
      refine PowTorus.torus_ext _ _ fun χ z => ?_
      obtain ⟨x, rfl⟩ := hD.xe.surjective χ
      rw [Over.comp_left, Over.comp_left, gm_torusEnd tc, ← hx, hsx, gm_comp_of_id _ _ _ (hsx x),
        ← gm_torusEnd tc', Category.id_comp]
    have E : (Over.pullback (thick R I e)).map (ιG'.act a) ≫ (Over.pullback (thick R I e)).map φ =
        (Over.pullback (thick R I e)).map φ ≫ (Over.pullback (thick R I e)).map (ιG.act a) := by
      refine hom_ext_torus (U.gt e) (U'.gt e) hG _ _ ?_ ?_
      · rw [Category.assoc, Category.assoc, lin.q_lin, hq, reassoc_of% hq, reassoc_of% (lin'.q_lin e a),
          ← Functor.map_comp, ← Functor.map_comp, hψa]
      · rw [reassoc_of% ti', ← hsi, ← reassoc_of% hsi, ti, reassoc_of% hts]
    rw [← Functor.map_comp, ← Functor.map_comp] at E
    exact (P e _).symm.trans ((congrArg (fun c => c.left ≫ pullback.fst G.hom (thick R I e)) E).trans (P e _))
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have a₂ : ((Over.pullback (specOf (RingHom.id R))).map (ιG.act a)).left ≫
      pullback.fst G.hom (specOf (RingHom.id R)) = pullback.fst _ _ ≫ (ιG.act a).left :=
    pullback.lift_fst _ _ _
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, a₂, ← eφ, ← Category.assoc, ← eφ,
    ← Over.comp_left, key, Over.comp_left]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueSecOfCompatible
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor IsLocalRing
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SectionLimit

section Alg

variable {R : Type} [CommRing R] (I : Ideal R)

theorem exists_lim [IsPrecomplete I R] (c : ∀ e : ℕ, R ⧸ I ^ (e + 1))
    (hc : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (c (e + 1)) = c e) :
    ∃ a : R, ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) a = c e := by
  choose x hx using fun e => Ideal.Quotient.mk_surjective (c e)
  have h1 : ∀ e, x e - x (e + 1) ∈ I ^ (e + 1) := fun e => by
    rw [← Ideal.Quotient.eq, hx, ← hc e, ← hx, Ideal.Quotient.factor_mk]
  have h2 : ∀ m n, m ≤ n → x m - x n ∈ I ^ m := fun m n h => by
    induction n, h using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := (I ^ m).add_mem ih (Ideal.pow_le_pow_right (hmn.trans (Nat.le_succ n)) (h1 n))
      simpa using this
  obtain ⟨a, ha⟩ := IsPrecomplete.prec (I := I) (M := R) inferInstance (f := x) (fun {m n} h => by
    rw [SModEq.sub_mem]; simpa using h2 m n h)
  refine ⟨a, fun e => ?_⟩
  have h3 : x (e + 1) - a ∈ I ^ (e + 1) := by
    have := ha (e + 1)
    rw [SModEq.sub_mem] at this
    simpa using this
  rw [← hx, eq_comm, Ideal.Quotient.eq]
  simpa using (I ^ (e + 1)).add_mem (h1 e) h3

theorem eq_of_mk_eq [IsHausdorff I R] {a b : R}
    (h : ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) a = Ideal.Quotient.mk (I ^ (e + 1)) b) : a = b := by
  rw [← sub_eq_zero]
  refine IsHausdorff.haus (I := I) (M := R) inferInstance _ fun n => ?_
  rw [SModEq.zero]
  simpa using Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.1 (h n))

end Alg

section Calc

variable {X Y Y' : Scheme.{0}} {L : LB X}

theorem exists_pull {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε))
    (h : Y' ⟶ Y) (φ' : K → (Y' ⟶ X)) (e : ∀ k, h ≫ φ k = φ' k) : ∃ s' : LB.Sec (LB.LinComb L φ' ε),
      (∀ j (le : LB.wchart L φ' j ≤ h ⁻¹ᵁ LB.wchart L φ j),
        s'.f j = (Y'.presheaf.map (homOfLE le).op).hom ((h.app _).hom (s.f j))) ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → sval s' r z J = sval s (r ≫ h) z J := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  exact ⟨pullSec L φ ε s h, fun _ _ => rfl, fun Z r z J hJ => SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩

def linSec {M : LB Y} {N : ℕ} (c : Fin N → Γ(Y, ⊤)) (t : Fin N → LB.Sec M) : LB.Sec M where
  f j := ∑ i, resTop _ (c i) * (t i).f j
  compat i j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => (SecOps.secScale (c k) (t k)).compat i j

variable {C : Type} [CommRing C] {n N : ℕ}

def Rep (π : Y ⟶ X) (f : Y ⟶ Sp C) (β : Fin N → H0 L n)
    (s : LB.Sec (LB.LinComb L (K := Fin 1) (fun _ => π) (fun _ => (n : ℤ)))) (c : Fin N → C) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
    sval s r z J = ∑ i, cst (r ≫ f) z (c i) * sval (β i) (r ≫ π) z J

theorem rep_transport {π : Y ⟶ X} {f : Y ⟶ Sp C} {β : Fin N → H0 L n} (e : Y' ≅ Y)
    {π' : Y' ⟶ X} {f' : Y' ⟶ Sp C} (hπ : e.hom ≫ π = π') (hf : e.hom ≫ f = f')
    (H : ∀ s, ∃! c, Rep π f β s c) : ∀ s, ∃! c, Rep π' f' β s c := by
  subst hπ hf
  intro s'
  obtain ⟨s, -, hs⟩ := exists_pull s' e.inv (fun _ : Fin 1 => π) (fun _ => e.inv_hom_id_assoc π)
  have key : ∀ c, Rep (e.hom ≫ π) (e.hom ≫ f) β s' c ↔ Rep π f β s c := fun c => by
    constructor
    · intro h Z r z J hJ
      rw [hs Z r z J hJ, h Z _ z J hJ]
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
    · intro h Z r z J hJ
      have := h Z (r ≫ e.hom) z J hJ
      rw [hs Z _ z J hJ] at this
      simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using this
  simp only [key]
  exact H s

theorem sval_linSec {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (f : Y ⟶ Sp C) (c : Fin N → C)
    (t : Fin N → LB.Sec (LB.LinComb L φ ε)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι}
    (hJ : Good L z J) :
    sval (linSec (fun i => scal f (c i)) t) r z J = ∑ i, cst (r ≫ f) z (c i) * sval (t i) r z J := by
  rw [SectionScalarValuation.sval_lin (s := linSec (fun i => scal f (c i)) t) (fun i => scal f (c i)) t (fun _ => rfl) r z hJ]
  exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (gs_pull r f z ⊤ trivial _)

end Calc

theorem exists_basis (hS : SecBaseChangeSt) (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ) (hn : 1 ≤ n) :
    ∃ (N : ℕ) (β : Fin N → H0 P.L n), ∀ (C : Type) [CommRing C] (q : Sp C ⟶ Sp R) (Y : Scheme.{0})
      (π : Y ⟶ P.A.left) (f : Y ⟶ Sp C), IsPullback f π q P.A.hom → ∀ s, ∃! c, Rep π f β s c := by
  have hL := P.isLB
  obtain ⟨U, hU, b, hb⟩ := hS (Spec (CommRingCat.of R)) P n hn (closedPoint R)
  obtain rfl : U = ⊤ := eq_top_of_closedPoint_mem U hU
  let V := overRes (T := baseOver (Spec (CommRingCat.of R))) ⊤
  let t₀ : Spec (CommRingCat.of R) ⟶ V.left := (Spec (CommRingCat.of R)).topIso.inv
  have ht : t₀ ≫ V.hom = 𝟙 _ := by
    show (Spec (CommRingCat.of R)).topIso.inv ≫ (Scheme.Opens.ι ⊤ ≫ 𝟙 _) = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.inv_hom_id
  have ht' : V.hom ≫ t₀ = 𝟙 _ := by
    show (Scheme.Opens.ι ⊤ ≫ 𝟙 _) ≫ (Spec (CommRingCat.of R)).topIso.inv = 𝟙 _
    rw [Category.comp_id]
    exact (Spec (CommRingCat.of R)).topIso.hom_inv_id
  let u : P.A ⟶ V := Over.homMk (P.A.hom ≫ t₀) (by rw [Category.assoc, ht, Category.comp_id])
  have hu : snd V P.A ≫ u = fst V P.A := Over.OverMorphism.ext (by
    show (snd V P.A).left ≫ P.A.hom ≫ t₀ = (fst V P.A).left
    rw [← Category.assoc, Over.w (snd V P.A), ← Over.w (fst V P.A), Category.assoc, ht', Category.comp_id])
  have e₁ : lift u (𝟙 P.A) ≫ snd V P.A = 𝟙 _ := lift_snd _ _
  have e₂ : snd V P.A ≫ lift u (𝟙 P.A) = 𝟙 _ := by
    rw [comp_lift, hu, Category.comp_id, lift_fst_snd]
  choose β hβ0 hβ using fun i => exists_pull (K := Fin 1) (b i) (lift u (𝟙 P.A)).left (fun _ => 𝟙 P.A.left)
    (fun _ => congrArg CommaMorphism.left e₁)
  refine ⟨_, β, fun C _ q Y π f hp => ?_⟩
  let t : Spec (CommRingCat.of C) ⟶ V.left := q ≫ t₀
  have hq : (baseAt t).hom = q := by
    show (q ≫ t₀) ≫ V.hom = q
    rw [Category.assoc, ht, Category.comp_id]
  choose b' hb0 hb' using fun i => exists_pull (K := Fin 1) (b i) (homAt t ▷ P.A).left
      (fun _ => (snd (baseAt t) P.A).left)
      (fun _ => congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A))
  obtain ⟨hli, hsp⟩ := hb C t b' (fun i j => hb0 i j _)
  have e₃ : snd (baseAt t) P.A ≫ lift u (𝟙 P.A) = homAt t ▷ P.A := by
    rw [← whiskerRight_snd (homAt t) P.A, Category.assoc, e₂, Category.comp_id]
  have e₄ : (snd (baseAt t) P.A).left ≫ (lift u (𝟙 P.A)).left = (homAt t ▷ P.A).left :=
    congrArg CommaMorphism.left e₃
  have hp' : IsPullback f π (baseAt t).hom P.A.hom := hq ▸ hp
  refine rep_transport (Y := (baseAt t ⊗ P.A).left) (π := (snd (baseAt t) P.A).left)
    (f := (fst (baseAt t) P.A).left) hp'.isoPullback hp'.isoPullback_hom_snd hp'.isoPullback_hom_fst fun s => ?_
  have bij := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of C)).inv
  have hv : ∀ (c : Fin (n ^ P.g) → C) (Z : Scheme.{0}) (r : Z ⟶ (baseAt t ⊗ P.A).left) (z : Z) (J), Good P.L z J →
      sval (linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b') r z J =
        ∑ i, cst (r ≫ (fst (baseAt t) P.A).left) z (c i) * sval (β i) (r ≫ (snd (baseAt t) P.A).left) z J :=
    fun c Z r z J hJ => by
      rw [sval_linSec _ _ _ _ _ hJ]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb' i Z r z J hJ, hβ i Z _ z J hJ, Category.assoc, e₄]
  have key : ∀ c : Fin (n ^ P.g) → C, Rep (snd (baseAt t) P.A).left (fst (baseAt t) P.A).left β s c ↔
      ∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i)) •
        (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t)) = SecM.ofSec P.A s := fun c => by
    have ev : ∀ j, (∑ i, (show Γ((baseAt t).left, ⊤) from (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (c i)) •
        (SecM.ofSec P.A (b' i) : SecM P.A P.L n (baseAt t))).1 j =
        (linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b').f j := fun j => by
      rw [Submodule.coe_sum, Finset.sum_apply]
      rfl
    constructor
    · intro h
      refine Subtype.ext (funext fun j => (ev j).trans ?_)
      exact sec_ext_val hL (fun y J hJ => (hv c _ _ y J hJ).trans (h _ _ y J hJ).symm) j
    · intro h Z r z J hJ
      have : s = linSec (fun i => scal (fst (baseAt t) P.A).left (c i)) b' :=
        SecOps.sec_ext fun j => (congrFun (congrArg Subtype.val h) j).symm.trans (ev j)
      rw [this]
      exact hv c Z r z J hJ
  obtain ⟨r, hr⟩ := (Submodule.mem_span_range_iff_exists_fun _).1
    (hsp.ge (Submodule.mem_top : SecM.ofSec P.A s ∈ ⊤))
  choose a ha using fun i => bij.2 (r i)
  obtain rfl : (fun i => (Scheme.ΓSpecIso (CommRingCat.of C)).inv.hom (a i)) = r := funext ha
  refine ⟨a, (key a).2 hr, fun a' ha' => funext fun i => bij.1 ?_⟩
  exact Fintype.linearIndependent_iffₛ.1 hli _ _ (((key a').1 ha').trans hr.symm) i

theorem existsUnique_sec_of_compatible : SecBaseChangeSt → ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R] (P : PolAV (Spec (CommRingCat.of R))) (n : ℕ), 1 ≤ n → ∀ s : ∀ e : ℕ, LB.Sec (LB.LinComb P.L (K := Fin 1) (fun _ => (fstG I e P.A).left) (fun _ => (n : ℤ))), (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Geo.Tor.Good P.L z J → Geo.Tor.sval (s (e + 1)) (r ≫ thickMap R I e P.A) z J = Geo.Tor.sval (s e) r z J) → ∃! σ : H0 P.L n, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Geo.Tor.Good P.L z J → Geo.Tor.sval σ (r ≫ (fstG I e P.A).left) z J = Geo.Tor.sval (s e) r z J := by
  intro hS R _ _ _ I _ P n hn s hs
  have hL := P.isLB
  obtain ⟨N, β, hβ⟩ := exists_basis hS R P n hn
  have hpe : ∀ e, IsPullback (thickObj R I e P.A).hom (fstG I e P.A).left (thick R I e) P.A.hom :=
    fun e => (IsPullback.of_hasPullback P.A.hom (thick R I e)).flip
  choose c hc hcu using fun e => hβ _ _ _ _ _ (hpe e) (s e)
  have hcomp : ∀ e i, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (c (e + 1) i) = c e i :=
    fun e => congrFun (hcu e (fun i => Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))
      (c (e + 1) i)) fun Z r z J hJ => by
        have h₁ : thickMap R I e P.A ≫ (thickObj R I (e + 1) P.A).hom =
            (thickObj R I e P.A).hom ≫ thickTrans R I e := pullback.lift_snd _ _ _
        have h₂ : thickMap R I e P.A ≫ (fstG I (e + 1) P.A).left = (fstG I e P.A).left :=
          (pullback.lift_fst _ _ _).trans (Category.comp_id _)
        rw [← hs e Z r z J hJ, hc (e + 1) Z _ z J hJ, Category.assoc, Category.assoc, h₁, h₂, ← Category.assoc]
        exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (cst_comp _ _ _ _))
  choose a ha using fun i => exists_lim I (fun e => c e i) (fun e => hcomp e i)
  have down : ∀ (σ : H0 P.L n) (a : Fin N → R), Rep (𝟙 _) P.A.hom β σ a → ∀ (e : ℕ) (Z : Scheme.{0})
      (r : Z ⟶ (thickObj R I e P.A).left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J →
      sval σ (r ≫ (fstG I e P.A).left) z J = ∑ i, cst (r ≫ (thickObj R I e P.A).hom) z
        (Ideal.Quotient.mk (I ^ (e + 1)) (a i)) * sval (β i) (r ≫ (fstG I e P.A).left) z J :=
    fun σ a h e Z r z J hJ => by
      rw [h Z _ z J hJ, Category.comp_id, Category.assoc, ← (hpe e).w, ← Category.assoc]
      exact Finset.sum_congr rfl fun i _ => congrArg (· * _) (cst_comp _ _ _ _)
  have hlin : Rep (𝟙 _) P.A.hom β (linSec (fun i => scal P.A.hom (a i)) β) a := fun Z r z J hJ => by
    rw [sval_linSec _ _ _ _ _ hJ, Category.comp_id]
  refine ⟨linSec (fun i => scal P.A.hom (a i)) β, fun e Z r z J hJ => ?_, fun σ hσ => ?_⟩
  · rw [down _ a hlin e Z r z J hJ, hc e Z r z J hJ]
    simp only [ha]
  · obtain ⟨a', ha', -⟩ := hβ R (𝟙 _) _ (𝟙 _) P.A.hom (IsPullback.of_vert_isIso ⟨by simp⟩) σ
    have : a' = a := funext fun i => eq_of_mk_eq I fun e => by
      rw [ha]
      exact congrFun (hcu e (fun i => Ideal.Quotient.mk (I ^ (e + 1)) (a' i)) fun Z r z J hJ =>
        (hσ e Z r z J hJ).symm.trans (down σ a' ha' e Z r z J hJ)) i
    subst this
    exact SecOps.sec_ext (sec_ext_val hL fun y J hJ => (ha' _ _ y J hJ).trans (hlin _ _ y J hJ).symm)

end GlobalTheory.SectionLimit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DimEqAddFinrankOfKernel
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.UU

theorem dim_eq_add_finrank_of_kernel {S : Scheme.{0}} (y : S) {X : Type} [AddCommGroup X] [Module.Free ℤ X]
    [Module.Finite ℤ X] {G B : Over S} [GrpObj G] [GrpObj B] (q : G ⟶ B) (i : splitTorus S X ⟶ G) [IsMonHom q]
    [IsMonHom i] [Flat q.left] [Surjective q.left] [IsAffineHom q.left] (hk : IsPullback i (toUnit _) q (η[B]))
    {g g' : ℕ} (dG : SmoothOfRelativeDimension g G.hom) (dB : SmoothOfRelativeDimension g' B.hom) :
    g = g' + Module.finrank ℤ X := by
  have := (H1.torus_dim S X).smooth
  have : Smooth q.left := by
    refine MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact)
      ((H1.torsor_pullback i q hk).map (Over.forget _)).flip
      ⟨⟨‹_›, ‹_›⟩, inferInstanceAs (QuasiCompact q.left)⟩ ?_
    exact smooth_isStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback _ _) this
  obtain ⟨m, W, hW, d₁⟩ := H1.exists_dim q.left (eSec G y)
  have g₂ : m = Module.finrank ℤ X := H1.dim_base (hk.map (Over.forget _)) d₁ (H1.torus_dim S X) (eSec _ y)
    ((congrArg (fun k => k.left y ∈ W) (IsMonHom.one_hom i)).mpr hW)
  have d₂ : SmoothOfRelativeDimension (m + g') (W.ι ≫ G.hom) := by
    rw [← Over.w q, ← Category.assoc]; infer_instance
  have d₃ : SmoothOfRelativeDimension (0 + g) (W.ι ≫ G.hom) := inferInstance
  have := H1.dim_unique _ d₂ d₃ ⟨_, hW⟩
  omega

theorem PreU.dim_eq : (AllPre fun {_} _ _ _ {D} {A} {_} _ _ _ => A.g = D.P.g + D.rank) := by
  intro V _ _ _ _ D A G _ _ U
  have hs : Smooth G.hom := U.semi.smooth
  have : GeometricallyConnected G.hom := U.semi.geomConnected
  have : ConnectedSpace G.left := (GroupConn.connectedSpace_group _ G).1
  obtain ⟨n, hn⟩ := exists_dim_of_preconnected G.hom (Classical.arbitrary _)
  have bc : ∀ {S' : Scheme.{0}} {X : Over (Spec (CommRingCat.of V))} {m : ℕ} (f : S' ⟶ Spec (CommRingCat.of V)),
      SmoothOfRelativeDimension m X.hom → SmoothOfRelativeDimension m ((Over.pullback f).obj X).hom :=
    fun f h => (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) h
  have h₁ : n = A.g := by
    have a := A.smoothDim
    have b : SmoothOfRelativeDimension (0 + A.g) ((Over.pullback (jK V)).obj G).hom := by
      have : IsIso U.gen.hom.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.hom))
      rw [← Over.w U.gen.hom]; infer_instance
    exact (H1.dim_unique _ (bc _ hn) b (eSec _ (Classical.arbitrary (Spec (CommRingCat.of (FractionRing V)))))).trans (zero_add _)
  have : Nontrivial (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.2 (by simpa using (IsLocalRing.maximalIdeal.isMaximal V).ne_top)
  let c := U.gt 0
  have := c.q_hom
  have := c.i_hom
  have := c.q_flat
  have := c.q_surj
  have := c.q_affine
  exact h₁.symm.trans (dim_eq_add_finrank_of_kernel (Classical.arbitrary _) c.q c.i c.isKernel (bc _ hn)
    (bc _ D.P.smoothDim))

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointBalancedPowerLift
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TauBalElem

open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.BoxFamily GlobalTheory.TauBalBox

theorem tau_zero_left {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult) {y : (TK R).left} {J}
    (hJ : Good D.P.L y J) (b : D.X) : val (D.tau 0 b) (𝟙 _) y J = 1 := by
  have C : IsCub (cubV D.cub (T := TK R) y J) := isCub_cubV D.cub hJ
  have t := tauK_mul hJ hB 0 0 b
  rw [add_zero, cPoint_zero, C.face, _root_.mul_one] at t
  exact mul_eq_left.1 t.symm

end GlobalTheory.TauBalElem
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSubSum
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ConvOfProd

theorem sum_conv {X A : Type} [AddCommGroup X] [CommRing A] (s s' S : Finset X) (F G : X → A)
    (hG : ∀ v ∉ s', G v = 0) (hS : ∀ β ∈ s, ∀ v ∈ s', β + v ∈ S) :
    ∑ α ∈ S, ∑ β ∈ s, F β * G (α - β) = (∑ β ∈ s, F β) * ∑ v ∈ s', G v := by
  classical
  rw [Finset.sum_comm, Finset.sum_mul]
  refine Finset.sum_congr rfl fun β hβ => ?_
  rw [← Finset.mul_sum]
  congr 1
  symm
  refine Finset.sum_bij_ne_zero (fun v _ _ => β + v) (fun v h _ => hS β hβ v h)
    (fun a _ _ b _ _ e => add_left_cancel e) (fun α _ h => ?_) (fun v _ _ => by rw [add_sub_cancel_left])
  exact ⟨α - β, by by_contra hn; exact h (hG _ hn), h, add_sub_cancel β α⟩

theorem exists_sub_sum {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {Ix : Type}
    (S : LB.Sec (LB.LinComb L φ ε)) (p : Ix → LB.Sec (LB.LinComb L φ ε)) (s : Finset Ix) :
    ∃ d : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval d r z J = sval S r z J - ∑ i ∈ s, sval (p i) r z J := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨S, fun Z r z J _ => by rw [Finset.sum_empty, sub_zero]⟩
  | insert i s hi ih =>
    obtain ⟨d, hd⟩ := ih
    refine ⟨DVR.SecOps.secAdd d (DVR.SecOps.secNeg (p i)), fun Z r z J hJ => ?_⟩
    have hm := hJ.mem φ r
    have e : sval (DVR.SecOps.secAdd d (DVR.SecOps.secNeg (p i))) r z J = sval d r z J - sval (p i) r z J := by
      refine (gs_add r z _ hm _ _).trans ?_
      rw [sub_eq_add_neg]
      congr 1
      refine (gs_eq r z _ hm _).trans (Eq.trans ?_ (congrArg Neg.neg (gs_eq r z _ hm _)).symm)
      exact (congrArg _ (map_neg _ _)).trans (map_neg _ _)
    rw [e, hd Z r z J hJ, Finset.sum_insert hi]
    ring

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

theorem over_eq {e : ℕ} (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of R))} {Z : Scheme.{0}}
    (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left) (hr : r ≫ (snd T D.P.A).left = x ≫ g.pG.left) :
    x ≫ ((Over.map (thick R I e)).obj (thickObj R I e G)).hom = r ≫ (T ⊗ D.P.A).hom := by
  rw [← Over.w g.pG, ← Over.w (snd T D.P.A), ← Category.assoc, ← Category.assoc]
  exact congrArg (· ≫ D.P.A.hom) hr.symm

theorem prod_mul_coord {e : ℕ} (g : GtCoord I D e G) {T : Over (Spec (CommRingCat.of R))} {k l m : ℕ} {β ga α : D.X}
    (hα : β + ga = α) {a : SecBT D T k β} {b : SecBT D T l ga} {c : SecBT D T m α} (H : IsProdB a b c) {Z : Scheme.{0}}
    (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left) (hr : r ≫ (snd T D.P.A).left = x ≫ g.pG.left)
    (z : Z) (J) (hJ : Good D.P.L z J) :
    sval c r z J * (val (g.t α) x z J).val =
      sval a r z J * (val (g.t β) x z J).val * (sval b r z J * (val (g.t ga) x z J).val) := by
  subst hα
  let FinalForm : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (T ⊗ D.P.A).hom)
  let ro : FinalForm ⟶ T ⊗ D.P.A := Over.homMk r rfl
  let xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x (over_eq g x r hr)
  have h₁ := H FinalForm ro z J hJ
  have h₂ := (val_mul hJ _ _ _).symm.trans ((val_corr hJ (g.t_mul β ga) x).trans (val_mul hJ _ _ _))
  have h₃ := val_cub D.cub xo (z := z) hJ (DVR.cP D _ β) (DVR.cP D _ ga) g.pG
  have h₄ : xo ≫ g.pG = ro ≫ snd T D.P.A := Over.OverMorphism.ext hr.symm
  rw [DVR.comp_cP, DVR.comp_cP, h₄] at h₃
  have h₅ := congrArg Units.val ((congrArg (val (g.t (β + ga)) x z J * ·) h₃).symm.trans h₂)
  rw [Units.val_mul, Units.val_mul] at h₅
  refine (congrArg (· * (val (g.t (β + ga)) x z J).val) h₁).trans ?_
  rw [_root_.mul_mul_mul_comm, ← h₅]
  exact (_root_.mul_assoc _ _ _).trans (congrArg _ (mul_comm _ _))

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (T : Over (Spec (CommRingCat.of R))) (k l : ℕ) (f : ∀ α, SecBT D T k α) (g : ∀ α, SecBT D T l α) (h : ∀ α, SecBT D T (k + l) α) (σ : U.SecGT T (k + l)), U.ProdExp T f g σ → U.ExpT T (k + l) σ h → ConvT I f g h := by
  intro R _ _ I D A G _ _ U T k l f g h σ hP hE α₀
  classical
  choose p hp using fun α β => exists_isProdB R D T k l β (α - β) α (add_sub_cancel β α) (f β) (g (α - β))
  refine ⟨p α₀, hp α₀, fun e => ?_⟩
  obtain ⟨s, s', hP⟩ := hP e
  obtain ⟨s'', hE⟩ := hE e
  have key : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ (T ⊗ D.P.A).left),
      r ≫ (snd T D.P.A).left = x ≫ (U.gt e).pG.left → ∀ (z : Z) (J), Good D.P.L z J →
      (∀ α ∉ s, sval (f α) r z J = 0) ∧ (∀ α ∉ s', sval (g α) r z J = 0) ∧ (∀ α ∉ s'', sval (h α) r z J = 0) ∧
      ∑ α ∈ s'', sval (h α) r z J * (val ((U.gt e).t α) x z J).val =
        (∑ α ∈ s, sval (f α) r z J * (val ((U.gt e).t α) x z J).val) *
          ∑ α ∈ s', sval (g α) r z J * (val ((U.gt e).t α) x z J).val := by
    intro Z x r hr z J hJ
    let FinalForm : Over (Spec (CommRingCat.of R)) := Over.mk (r ≫ (T ⊗ D.P.A).hom)
    let ro : FinalForm ⟶ T ⊗ D.P.A := Over.homMk r rfl
    let xo : FinalForm ⟶ (Over.map (thick R I e)).obj (thickObj R I e G) := Over.homMk x (over_eq (U.gt e) x r hr)
    let rG : FinalForm ⟶ T ⊗ G := lift (ro ≫ fst _ _) (xo ≫ fstG I e G)
    have e₁ : rG.left ≫ (snd T G).left = x ≫ (fstG I e G).left := congrArg (fun q : FinalForm ⟶ G => q.left) (lift_snd _ _)
    have e₂ : r ≫ (fst T D.P.A).left = rG.left ≫ (fst T G).left :=
      congrArg (fun q : FinalForm ⟶ T => q.left) (lift_fst (ro ≫ fst _ _) (xo ≫ fstG I e G)).symm
    choose JG hJG using fun χ : Z ⟶ G.left => exists_chart U.P.L.isLB (χ z)
    obtain ⟨a₁, a₂, a₃⟩ := hP Z x rG.left r e₁ hr e₂ z JG J hJG hJ
    obtain ⟨b₁, b₂⟩ := hE Z x rG.left r e₁ hr e₂ z JG J hJG hJ
    exact ⟨a₁, a₂, b₁, b₂.symm.trans a₃⟩
  choose d hd using fun α => exists_sub_sum (h α) (p α) s
  let S : Finset D.X := insert α₀ (s'' ∪ Finset.image₂ (· + ·) s s')
  have hd0 := GlobalTheory.sval_eq_zero_of_sum_mul_coord R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) (Fin 4)
    (famφT D T) (DegPre.famε (k + l)) d S (fun Z x r hr z J hJ => by
      obtain ⟨-, k₂, k₃, k₄⟩ := key Z x r hr z J hJ
      have c := sum_conv s s' S (fun β => sval (f β) r z J * (val ((U.gt e).t β) x z J).val)
        (fun β => sval (g β) r z J * (val ((U.gt e).t β) x z J).val)
        (fun v hv => by rw [k₂ v hv, zero_mul])
        (fun β hβ v hv => Finset.mem_insert_of_mem (Finset.mem_union_right _ (Finset.mem_image₂_of_mem hβ hv)))
      have c' : ∑ α ∈ s'', sval (h α) r z J * (val ((U.gt e).t α) x z J).val =
          ∑ α ∈ S, sval (h α) r z J * (val ((U.gt e).t α) x z J).val :=
        Finset.sum_subset (fun a ha => Finset.mem_insert_of_mem (Finset.mem_union_left _ ha))
          (fun a _ ha => by rw [k₃ a ha, zero_mul])
      rw [← sub_eq_zero.2 (c'.symm.trans (k₄.trans c.symm)), ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [hd α Z r z J hJ, sub_mul, Finset.sum_mul]
      exact congrArg _ (Finset.sum_congr rfl fun β _ =>
        prod_mul_coord (U.gt e) (add_sub_cancel β α) (hp α β) x r hr z J hJ)) α₀ (Finset.mem_insert_self _ _)
  refine ⟨s, fun Z r hl z J hJ => ⟨fun β hβ => ?_, ?_⟩⟩
  · refine GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (p α₀ β)
      (fun Z x r hr z J hJ => ?_) Z r hl z J hJ
    have c := prod_mul_coord (U.gt e) (add_sub_cancel β α₀) (hp α₀ β) x r hr z J hJ
    rw [(key Z x r hr z J hJ).1 β hβ, zero_mul, zero_mul] at c
    exact (Units.mul_left_eq_zero _).1 c
  · have c := GlobalTheory.LiftTest.main R I D e G (U.gt e) (T ⊗ D.P.A) (snd T D.P.A) _ D.P.L D.P.isLB _ _ _ (d α₀) hd0 Z r hl z J hJ
    rw [hd α₀ Z r z J hJ] at c
    exact sub_eq_zero.1 c

end GlobalTheory.ConvOfProd
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombBijective
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
noncomputable section
namespace GlobalTheory.UU.ExpExt

section Decomp
open GlobalTheory.QCoh.Qcqs TopologicalSpace
variable {V W : Type} [CommRing V] [CommRing W] [Algebra V W] {n : ℕ} (b : Module.Basis (Fin n) V W)
  {X Y : Scheme.{0}} {p : X ⟶ Spec (.of V)} {q : Y ⟶ Spec (.of W)} {π : Y ⟶ X}

abbrev cst (w : W) : Γ(Spec (.of W), ⊤) := (Scheme.ΓSpecIso (.of W)).inv.hom w

def comb (q : Y ⟶ Spec (.of W)) (π : Y ⟶ X) (U : X.Opens) (a : Fin n → Γ(X, U)) : Γ(Y, π ⁻¹ᵁ U) :=
  ∑ i, (π.app U).hom (a i) * (baseRingHom q (π ⁻¹ᵁ U)).hom (b i)

theorem gs_comb (U : X.Opens) (a : Fin n → Γ(X, U)) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (h : r z ∈ π ⁻¹ᵁ U) :
    gs r z _ (comb b q π U a) = ∑ i, gs (r ≫ q) z ⊤ (cst (b i)) * gs (r ≫ π) z U (a i) := by
  have e : ∀ i, gs r z _ ((π.app U).hom (a i) * (baseRingHom q (π ⁻¹ᵁ U)).hom (b i)) =
      gs (r ≫ q) z ⊤ (cst (b i)) * gs (r ≫ π) z U (a i) := fun i => by
    rw [gs_mul r z _ h, gs_pull r π z U h, mul_comm]
    refine congrArg (· * _) ?_
    exact (gs_res r z (U := q ⁻¹ᵁ ⊤) le_top h ((q.app ⊤).hom (cst (b i)))).trans (gs_pull r q z ⊤ trivial _)
  rw [← Finset.sum_congr rfl fun i _ => e i]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [comb, gs_eq r z _ h, map_sum]

variable (H : IsPullback π q p (Spec.map (CommRingCat.ofHom (algebraMap V W))))
include H

theorem comb_bijective {U : X.Opens} (hU : IsAffineOpen U) : Function.Bijective (comb b q π U) := by
  have po := (isIso_pushoutSection_iff H (US := ⊤) (UT := ⊤) (UX := U) (UY := π ⁻¹ᵁ U) le_top
    le_top (by simp)).mp (isIso_pushoutSection_of_isAffineOpen H _ _ _ (isAffineOpen_top _)
      (isAffineOpen_top _) hU)
  have po' : IsPushout (baseRingHom p U) (CommRingCat.ofHom (algebraMap V W)) (π.app U)
      (baseRingHom q (π ⁻¹ᵁ U)) := by
    refine po.of_iso (Scheme.ΓSpecIso _) (Iso.refl _) (Scheme.ΓSpecIso _) (Iso.refl _) ?_ ?_ ?_ ?_
    · simp [baseRingHom]
    · rw [← Scheme.ΓSpecIso_naturality, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    · simp [Scheme.Hom.app_eq_appLE]
    · simp [baseRingHom]
  let := (π.app U).hom.toAlgebra
  let := (baseRingHom p U).hom.toAlgebra
  let := (baseRingHom q (π ⁻¹ᵁ U)).hom.toAlgebra
  let := (baseRingHom (π ≫ p) (π ⁻¹ᵁ U)).hom.toAlgebra
  have : IsScalarTower V Γ(X, U) Γ(Y, π ⁻¹ᵁ U) :=
    .of_algebraMap_eq fun r ↦ (app_baseRingHom π p U r).symm
  have : IsScalarTower V W Γ(Y, π ⁻¹ᵁ U) :=
    .of_algebraMap_eq fun r ↦ (baseRingHom_algebraMap (R := .of V) (L := .of W) H _ r).symm
  have hP : Algebra.IsPushout V Γ(X, U) W Γ(Y, π ⁻¹ᵁ U) := CommRingCat.isPushout_iff_isPushout.mp po'
  let b' := hP.out.basis b
  have : comb b q π U = b'.equivFun.symm := by
    funext v
    rw [Module.Basis.equivFun_symm_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [IsBaseChange.basis_apply, Algebra.smul_def]
    rfl
  rw [this]
  exact b'.equivFun.symm.bijective

theorem comb_inj {U : X.Opens} {a a' : Fin n → Γ(X, U)}
    (h : ∀ y ∈ π ⁻¹ᵁ U, ∑ i, gs (𝟙 Y ≫ q) y ⊤ (cst (b i)) * gs (𝟙 Y ≫ π) y U (a i) =
      ∑ i, gs (𝟙 Y ≫ q) y ⊤ (cst (b i)) * gs (𝟙 Y ≫ π) y U (a' i)) : a = a' := by
  funext i
  refine fn_ext fun x hx => ?_
  obtain ⟨_, ⟨O, hO, rfl⟩, hxO, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
  have hle' : O ≤ U := hle
  have e : (fun i => (X.presheaf.map (homOfLE hle').op).hom (a i)) =
      fun i => (X.presheaf.map (homOfLE hle').op).hom (a' i) := (comb_bijective b H hO).1 (fn_ext fun y hy => by
    rw [gs_comb b O _ (𝟙 Y) y hy, gs_comb b O _ (𝟙 Y) y hy]
    simp only [gs_res (𝟙 Y ≫ π) y hle' hy]
    exact h y (hle' hy))
  exact (gs_res (𝟙 X) x hle' hxO _).symm.trans ((congrArg _ (congrFun e i)).trans (gs_res (𝟙 X) x hle' hxO _))

theorem comb_surj {U : X.Opens} (s : Γ(Y, π ⁻¹ᵁ U)) : ∃ a : Fin n → Γ(X, U),
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ π ⁻¹ᵁ U →
      gs r z _ s = ∑ i, gs (r ≫ q) z ⊤ (cst (b i)) * gs (r ≫ π) z U (a i) := by
  let I := {O : X.Opens // IsAffineOpen O ∧ O ≤ U}
  have cov : ∀ x ∈ U, ∃ O : I, x ∈ O.1 := fun x hx => by
    obtain ⟨_, ⟨O, hO, rfl⟩, hxO, hle⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.isOpen
    exact ⟨⟨O, hO, hle⟩, hxO⟩
  choose u hu using fun O : I => (comb_bijective b H O.2.1).2
    ((Y.presheaf.map (homOfLE (π.preimage_mono O.2.2)).op).hom s)
  have hv : ∀ (O : I) (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ π ⁻¹ᵁ O.1 →
      gs r z _ s = ∑ i, gs (r ≫ q) z ⊤ (cst (b i)) * gs (r ≫ π) z O.1 (u O i) := fun O Z r z hz => by
    rw [← gs_comb b O.1 _ r z hz, hu, gs_res r z _ hz]
  have hc : ∀ O O' : I, (fun i => (X.presheaf.map (homOfLE (inf_le_left : O.1 ⊓ O'.1 ≤ O.1)).op).hom (u O i)) =
      fun i => (X.presheaf.map (homOfLE (inf_le_right : O.1 ⊓ O'.1 ≤ O'.1)).op).hom (u O' i) := fun O O' =>
    comb_inj b H fun y hy => by
      simp only [gs_res (𝟙 Y ≫ π) y (inf_le_left : O.1 ⊓ O'.1 ≤ O.1) hy,
        gs_res (𝟙 Y ≫ π) y (inf_le_right : O.1 ⊓ O'.1 ≤ O'.1) hy]
      exact (hv O _ (𝟙 Y) y hy.1).symm.trans (hv O' _ (𝟙 Y) y hy.2)
  choose a ha using fun i => (X.sheaf.existsUnique_gluing' (fun O : I => O.1) U (fun O => homOfLE O.2.2)
    (fun x hx => Opens.mem_iSup.2 (cov x hx)) (fun O => u O i) (fun O O' => congrFun (hc O O') i)).exists
  refine ⟨a, fun Z r z hz => ?_⟩
  obtain ⟨O, hO⟩ := cov _ hz
  rw [hv O Z r z hO]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  exact (congrArg (gs (r ≫ π) z O.1) (ha i O)).symm.trans (gs_res (r ≫ π) z O.2.2 hO _)

theorem sec_decomp {X₀ : Scheme.{0}} {L : LB X₀} {K : Type} [Fintype K] (φ : K → (X ⟶ X₀)) {ε : K → ℤ}
    {φ' : K → (Y ⟶ X₀)} (hφ : ∀ k, π ≫ φ k = φ' k) (σ : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ τ : Fin n → LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval σ r z J = ∑ i, gs (r ≫ q) z ⊤ (cst (b i)) * sval (τ i) (r ≫ π) z J := by
  obtain rfl : (fun k => π ≫ φ k) = φ' := funext hφ
  have l : ∀ j, π ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => π ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  choose a ha using fun j => comb_surj b H ((Y.presheaf.map (homOfLE (l j)).op).hom (σ.f j))
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ π ⁻¹ᵁ LB.wchart L φ j →
      gs r z (LB.wchart L (fun k => π ≫ φ k) j) (σ.f j) =
        ∑ i, gs (r ≫ q) z ⊤ (cst (b i)) * gs (r ≫ π) z _ (a j i) := fun j Z r z hz =>
    (gs_res r z (l j) hz _).symm.trans (ha j Z r z hz)
  have hc : ∀ j j', (fun i => (X.presheaf.map (homOfLE (inf_le_left :
        LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j)).op).hom (a j i)) =
      fun i => @id Γ(X, LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val * (X.presheaf.map (homOfLE (inf_le_right :
        LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j')).op).hom (a j' i) := fun j j' =>
    comb_inj b H fun y hy => by
      have e : ∀ i, gs (𝟙 Y ≫ π) y (LB.wchart L φ j ⊓ LB.wchart L φ j') (@id Γ(X, LB.wchart L φ j ⊓ LB.wchart L φ j') ((LB.LinComb L φ ε).g j j').val *
          (X.presheaf.map (homOfLE (inf_le_right :
            LB.wchart L φ j ⊓ LB.wchart L φ j' ≤ LB.wchart L φ j')).op).hom (a j' i)) =
          (trF (fun k => π ≫ φ k) ε (𝟙 Y) y j j').val * gs (𝟙 Y ≫ π) y _ (a j' i) := fun i =>
        (gs_mul _ y _ hy _ _).trans (congrArg₂ (· * ·) ((gs_unit _ y _ hy _).trans
          (congrArg Units.val (gm_linComb L φ ε (𝟙 Y ≫ π) y j j' hy.1 hy.2))) (gs_res _ y _ hy _))
      refine (Finset.sum_congr rfl fun i _ => congrArg _ (gs_res (𝟙 Y ≫ π) y inf_le_left hy _)).trans
        (Eq.trans ?_ (Finset.sum_congr rfl fun i _ => congrArg _ (e i)).symm)
      rw [← hv j _ (𝟙 Y) y hy.1, sec_trans σ (𝟙 Y) y (l j hy.1) (l j' hy.2), hv j' _ (𝟙 Y) y hy.2, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => mul_left_comm _ _ _
  refine ⟨fun i => ⟨fun j => a j i, fun j j' => congrFun (hc j j') i⟩, fun Z r z J hJ => ?_⟩
  refine (hv _ Z r z (Set.mem_iInter.2 fun k => hJ (r ≫ π ≫ φ k))).trans
    (Finset.sum_congr rfl fun i _ => congrArg _ ?_)
  exact (sval_of (L := L) (φ := φ) (ε := ε) ⟨fun j => a j i, fun j j' => congrFun (hc j j') i⟩ (r ≫ π) z J
    (fun k => J (r ≫ π ≫ φ k)) (fun k => by rw [Category.assoc])).symm

end Decomp

theorem gs_scal {W F : Type} [CommRing W] [CommRing F] {Y Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z)
    (p : Y ⟶ Spec (.of F)) (φ : Spec (.of F) ⟶ Spec (.of W)) (w : W) :
    gs r z ⊤ (scal p ((Scheme.ΓSpecIso (.of F)).hom.hom (φ.appTop.hom (cst w)))) = gs (r ≫ p ≫ φ) z ⊤ (cst w) := by
  have e : scal p ((Scheme.ΓSpecIso (.of F)).hom.hom (φ.appTop.hom (cst w))) = (p ≫ φ).appTop.hom (cst w) := by
    rw [scal, Iso.hom_inv_id_apply]; rfl
  rw [e]
  exact gs_pull r (p ≫ φ) z ⊤ trivial _

theorem main : Laws → Laws2 → (AllPre fun {V} _ _ _ {_} {_} {_} _ _ U => ∀ (W : Type) [CommRing W] [IsLocalRing W] [Algebra V W], FinExt V W → ∀ k, 1 ≤ k → ∀ σ, ∃ f, U.ExpT (TA V W) k σ f ∧ ∀ (F : Type) [Field F] [Algebra (FractionRing V) F] (φ : TF (R := V) F ⟶ TA V W) t s, U.PullG F φ k σ t → PullB _ F φ k f s → U.ExpF F k t s) := by
  classical
  intro hL hL2 V _ _ _ hV D A G _ _ U W _ _ _ hW k hk σ
  have := hW.1
  have := hW.2.1
  let b := Module.finBasis V W
  obtain ⟨τ, hτ⟩ := sec_decomp b (p := G.hom) (q := (fst (TA V W) G).left) (π := (snd (TA V W) G).left)
    (IsPullback.of_hasPullback (TA V W).hom G.hom).flip (fun _ : Fin 1 => 𝟙 G.left) (fun _ => Category.comp_id _) σ
  choose σ' hσ' using fun i => exists_pullSec_sval (τ i) (snd (𝟙_ _) G).left (fun _ => (snd (𝟙_ _) G).left)
    (fun _ => Category.comp_id _)
  have hσ : ∀ (Z : Scheme.{0}) (r : Z ⟶ (TA V W ⊗ G).left) (r' : Z ⟶ (𝟙_ _ ⊗ G).left) (z : Z) (J),
      Good U.P.L.L z J → r' ≫ (snd _ G).left = r ≫ (snd _ G).left →
      sval σ r z J = ∑ i, gs (r ≫ (fst (TA V W) G).left) z ⊤ (cst (b i)) * sval (σ' i) r' z J :=
    fun Z r r' z J hJ h => (hτ Z r z J hJ).trans (Finset.sum_congr rfl fun i _ => by rw [hσ' i Z r' z J hJ, h])
  choose g hg using fun i => GlobalTheory.T.exists_expansion_section_lineBundle_power hL hL2 V hV D A G U k hk (σ' i)
  choose g' hg' using fun i α => exists_pullSec_sval (g i α) (toUnit (TA V W) ▷ D.P.A).left (famφT D (TA V W) α)
    (whisker_famφT D _ α)
  have s1 : ∀ (T B : Over (Spec (CommRingCat.of V))), (toUnit T ▷ B).left ≫ (snd (𝟙_ _) B).left = (snd T B).left :=
    fun T B => congrArg CommaMorphism.left (whiskerRight_snd (toUnit T) B)
  have s2 : ∀ {T T' : Over (Spec (CommRingCat.of V))} (ρ : T' ⟶ T) (B : Over (Spec (CommRingCat.of V))),
      (ρ ▷ B).left ≫ (fst T B).left = (fst T' B).left ≫ ρ.left := fun ρ B =>
    congrArg CommaMorphism.left (whiskerRight_fst ρ B)
  let f : ∀ α, SecBT D (TA V W) k α := fun α =>
    ExpLin.secComb (fun i => (fst (TA V W) D.P.A).left.appTop.hom (cst (b i))) (fun i => g' i α)
  have hf : ∀ α (Z : Scheme.{0}) (r : Z ⟶ (TA V W ⊗ D.P.A).left) (z : Z) (J), Good D.P.L z J →
      sval (f α) r z J = ∑ i, gs (r ≫ (fst (TA V W) D.P.A).left) z ⊤ (cst (b i)) *
        sval (g i α) (r ≫ (toUnit (TA V W) ▷ D.P.A).left) z J := fun α Z r z J hJ =>
    (ExpLin.sval_secComb (fst (TA V W) D.P.A).left (fun i => cst (b i)) (fun i => g' i α) r z hJ).trans
      (Finset.sum_congr rfl fun i _ => congrArg _ (hg' i α Z r z J hJ))
  refine ⟨f, fun e => ?_, fun F _ _ φ t s hG hB => ?_⟩
  · choose s hs using fun i => hg i e
    refine ⟨Finset.univ.biUnion s, fun Z x rG rB h₁ h₂ h₃ z JG J hG hJ => ?_⟩
    have H := fun i => hs i Z x (rG ≫ (toUnit (TA V W) ▷ G).left) (rB ≫ (toUnit (TA V W) ▷ D.P.A).left)
      (by rw [Category.assoc, s1, h₁]) (by rw [Category.assoc, s1, h₂])
      (by rw [Category.assoc, s2, Category.assoc, s2, ← Category.assoc, h₃, Category.assoc]) z JG J hG hJ
    refine ⟨fun α hα => ?_, ?_⟩
    · rw [hf α Z rB z J hJ]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [(H i).1 α (fun hi => hα (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hi⟩)), mul_zero]
    · rw [hσ Z rG (rG ≫ (toUnit (TA V W) ▷ G).left) z JG hG (by rw [Category.assoc, s1])]
      refine Eq.trans ?_ (Finset.sum_congr rfl fun α _ => (congrArg (· * _) (hf α Z rB z J hJ)).symm)
      rw [h₃]
      exact ExpLin.sum_comb _ _ _ s (fun i α => sval (g i α) (rB ≫ (toUnit (TA V W) ▷ D.P.A).left) z J) _
        (fun i => (H i).1) (fun i => (H i).2)
  · refine ⟨_, fun i => (Scheme.ΓSpecIso (.of F)).hom.hom (φ.left.appTop.hom (cst (b i))), σ', g, hg, ?_, ?_⟩
    · intro Z rA y rG h₁ h₂ z JA JG hJA hJG
      have e₂ : φ.left ≫ (TA V W).hom = jFK (R := V) F ≫ jK V := Over.w φ
      have e₃ : (fst (TFK (R := V) F) A.A).left ≫ jFK (R := V) F = (snd (TFK (R := V) F) A.A).left ≫ A.A.hom :=
        (Over.w (fst (TFK (R := V) F) A.A)).trans (Over.w (snd (TFK (R := V) F) A.A)).symm
      have e₄ : U.gen.hom.left ≫ A.A.hom = pullback.snd G.hom (jK V) := Over.w U.gen.hom
      have w : (rA ≫ (fst (TFK (R := V) F) A.A).left ≫ φ.left) ≫ (TA V W).hom =
          (y ≫ pullback.fst G.hom (jK V)) ≫ G.hom := (calc
        (y ≫ pullback.fst G.hom (jK V)) ≫ G.hom = y ≫ pullback.fst G.hom (jK V) ≫ G.hom := Category.assoc _ _ _
        _ = y ≫ (U.gen.hom.left ≫ A.A.hom) ≫ jK V := by rw [e₄]; exact congrArg (y ≫ ·) pullback.condition
        _ = (rA ≫ (snd (TFK (R := V) F) A.A).left) ≫ A.A.hom ≫ jK V := by rw [h₁]; simp only [Category.assoc]
        _ = rA ≫ ((fst (TFK (R := V) F) A.A).left ≫ jFK (R := V) F) ≫ jK V := by rw [e₃]; simp only [Category.assoc]
        _ = rA ≫ (fst (TFK (R := V) F) A.A).left ≫ φ.left ≫ (TA V W).hom := by
          rw [e₂]; exact congrArg (rA ≫ ·) (Category.assoc _ _ _)
        _ = _ := (congrArg (rA ≫ ·) (Category.assoc _ _ _).symm).trans (Category.assoc _ _ _).symm).symm
      let r : Z ⟶ (TA V W ⊗ G).left := pullback.lift _ _ w
      have r₁ : r ≫ (fst (TA V W) G).left = rA ≫ (fst (TFK (R := V) F) A.A).left ≫ φ.left := pullback.lift_fst _ _ _
      have r₂ : r ≫ (snd (TA V W) G).left = y ≫ pullback.fst G.hom (jK V) := pullback.lift_snd _ _ _
      refine (hG Z rA y r h₁ r₂ r₁ z JA JG hJA hJG).trans ((hσ Z r rG z JG hJG (h₂.trans r₂.symm)).trans ?_)
      refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      rw [r₁]
      exact (gs_scal rA z (fst (TFK (R := V) F) A.A).left φ.left (b i)).symm
    · intro α Z rF rB h z J hJ
      have e : rB = (rF ≫ (φ ▷ D.P.A).left) ≫ (toUnit (TA V W) ▷ D.P.A).left := by
        have w : (φ ▷ D.P.A).left ≫ (snd _ D.P.A).left = (snd _ D.P.A).left :=
          congrArg CommaMorphism.left (whiskerRight_snd φ D.P.A)
        have i : IsIso (snd (𝟙_ (Over (Spec (CommRingCat.of V)))) D.P.A).left := by
          rw [← leftUnitor_hom]; exact inferInstanceAs (IsIso ((Over.forget _).map (λ_ D.P.A).hom))
        rw [← cancel_mono (snd (𝟙_ (Over (Spec (CommRingCat.of V)))) D.P.A).left, Category.assoc, s1,
          Category.assoc, w, h]
      have e' : sval (s α) rF z J = sval (f α) (rF ≫ (φ ▷ D.P.A).left) z J := by
        rw [IntExp.sval_comp (f α) _ rF z J hJ, ← hB α (rF z) _ (fun ψ => hJ (rF ≫ ψ)),
          ← IntExp.sval_comp (s α) _ rF z J hJ, Category.comp_id]
      rw [e', hf α Z _ z J hJ, e]
      refine Finset.sum_congr rfl fun i _ => congrArg (· * _) ?_
      rw [Category.assoc, s2]
      exact (gs_scal rF z (fst (TF (R := V) F) D.P.A).left φ.left (b i)).symm

end GlobalTheory.UU.ExpExt
end
end
