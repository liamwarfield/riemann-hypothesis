module

public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecLinOfSecScal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupConn

theorem connectedSpace_of_section {X S : Scheme.{0}} (f : X ⟶ S) [GeometricallyConnected f]
    [ConnectedSpace S] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) : ConnectedSpace X := by

  have hsec : ∀ y : S, f (s y) = y := fun y => by
    simpa using congrArg (fun g : S ⟶ S => g y) hs
  obtain ⟨y₀⟩ := (inferInstance : Nonempty S)
  refine connectedSpace_iff_connectedComponent.mpr ⟨s y₀, Set.eq_univ_iff_forall.mpr fun x => ?_⟩
  have hbase : s (f x) ∈ connectedComponent (s y₀) :=
    (isPreconnected_range s.continuous).subset_connectedComponent ⟨y₀, rfl⟩ ⟨f x, rfl⟩
  have hfib : x ∈ connectedComponent (s (f x)) :=
    (f.isConnected_preimage_singleton (f x)).isPreconnected.subset_connectedComponent
      (show f (s (f x)) = f x from hsec (f x)) rfl
  rw [connectedComponent_eq hbase]
  exact hfib

theorem connectedSpace_tensor {S : Scheme.{0}} (G : Over S) [GrpObj G] [GeometricallyConnected G.hom]
    (Y : Over S) [ConnectedSpace Y.left] : ConnectedSpace (G ⊗ Y).left := by

  have : GeometricallyConnected (snd G Y).left :=
    show GeometricallyConnected (pullback.snd G.hom Y.hom) from inferInstance
  have hsec : (lift (toUnit Y ≫ η[G]) (𝟙 Y)).left ≫ (snd G Y).left = 𝟙 Y.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  exact connectedSpace_of_section (snd G Y).left _ hsec

theorem connectedSpace_group : ∀ (S : Scheme.{0}) [ConnectedSpace S] (G : Over S) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom], ConnectedSpace G.left ∧ ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (Y : Over S), ConnectedSpace Y.left → ConnectedSpace (splitTorus S X ⊗ Y).left ∧ ConnectedSpace (G ⊗ Y).left := by
  intro S _ G _ _ _
  refine ⟨connectedSpace_of_section (S := S) (X := G.left) G.hom η[G].left (Over.w _),
    fun X _ _ Y _ => ⟨?_, connectedSpace_tensor G Y⟩⟩

  have : UniqueSums X :=
    UniqueSums.of_injective_addHom (Module.Free.chooseBasis ℤ X).repr.toAddEquiv.toAddHom
      (Module.Free.chooseBasis ℤ X).repr.injective inferInstance
  exact connectedSpace_tensor (splitTorus S X) Y

end GlobalTheory.GroupConn
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ExpTrans

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Generic

variable {X X' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X}

def om (w : LB.Iso L' (L.pull F)) (z : Z) (J : (Z ⟶ X) → L.ι) (J' : (Z ⟶ X') → L'.ι) (ψ : Z ⟶ X') :
    (Z.presheaf.stalk z)ˣ := gw w ψ z (J (ψ ≫ F)) (J' ψ)

variable (w : LB.Iso L' (L.pull F)) {K : Type} [Fintype K] {Y Y' : Scheme.{0}} (φ' : K → (Y' ⟶ X'))
  (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y' ⟶ Y)

theorem sec_val (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L' φ' ε))
    (r : Z ⟶ Y') (z : Z)
    (H : ∀ (p : K → L.ι) (q : K → L'.ι), (∀ κ, F (φ' κ (r z)) ∈ L.U (p κ)) → (∀ κ, φ' κ (r z) ∈ L'.U (q κ)) →
      gs (r ≫ h) z (LB.wchart L φ p) (s.f p) =
        (∏ κ, gw w (r ≫ φ' κ) z (p κ) (q κ) ^ ε κ).val * gs r z (LB.wchart L' φ' q) (s'.f q))
    {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    sval s (r ≫ h) z J = (∏ κ, om w z J J' (r ≫ φ' κ) ^ ε κ).val * sval s' r z J' := by
  rw [sval_of s (r ≫ h) z J (fun κ => J ((r ≫ φ' κ) ≫ F))
    (fun κ => by rw [Category.assoc, Category.assoc, hc])]
  exact H _ (fun κ => J' (r ≫ φ' κ)) (fun κ => hJ ((r ≫ φ' κ) ≫ F)) (fun κ => hJ' (r ≫ φ' κ))

theorem gen_val (hc : ∀ κ, φ' κ ≫ F = h ≫ φ κ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L' φ' ε))
    (H : PMaps w φ' φ ε t' t h) (z : Y') {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t h z J = (∏ κ, om w z J J' (φ' κ) ^ ε κ) * val t' (𝟙 _) z J' := by
  have := H _ (𝟙 _) z (fun κ => J (φ' κ ≫ F)) (fun κ => J' (φ' κ)) (fun κ => hJ (φ' κ ≫ F)) (fun κ => hJ' (φ' κ))
  simp only [Category.id_comp] at this
  rw [val_of t h z J (fun κ => J (φ' κ ≫ F)) (fun κ => by rw [hc]),
    val_of t' (𝟙 _) z J' (fun κ => J' (φ' κ)) (fun κ => by rw [Category.id_comp])]
  exact this

end Generic

theorem prod_fam {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ)
    {M : Type} [CommGroup M] (ω : ((thickObj R I e G).left ⟶ D.toPre.P.A.left) → M) (α : D.toPre.X) :
    (∏ a, ω (pGl U e ≫ D.toPre.famφB α a) ^ DegPre.famε k a) * ∏ a, ω (Oφl U e α a) ^ Oinvε a =
      ω (pGl U e) ^ k := by
  have a₀ : pGl U e ≫ D.toPre.famφB α 0 = pGl U e := Category.comp_id _
  have a₁ : pGl U e ≫ D.toPre.famφB α 1 = Oφl U e α 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul (U.gt e).pG (𝟙 _) (cP D.toPre _ α)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D.toPre _ α)))
  have a₂ : pGl U e ≫ D.toPre.famφB α 2 = Oφl U e α 1 :=
    congrArg (fun z => z.left) (comp_cP D.toPre (U.gt e).pG α)
  have a₃ : pGl U e ≫ D.toPre.famφB α 3 = Oφl U e α 3 :=
    congrArg (fun z : _ ⟶ D.toPre.P.A => z.left) (MonObj.comp_one (M := D.toPre.P.A) (U.gt e).pG)
  have a₄ : Oφl U e α 2 = pGl U e := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

end GlobalTheory.ExpTrans

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans in
set_option maxHeartbeats 1600000 in
theorem expandsAt_transport : ∀ (R R' : Type) [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] (I : Ideal R) (I' : Ideal R') (D : DegData R I) (D' : DegData R' I') (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (A' : PolAV (Spec (CommRingCat.of (FractionRing R')))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of R'))) [GrpObj G'] [IsCommMonObj G'] (U : UnifPre I D A G) (U' : UnifPre I' D' A' G') (Φ : D'.toPre.P.A.left ⟶ D.toPre.P.A.left) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ)) (xe : D'.toPre.X ≃+ D.toPre.X) (Ψ : G'.left ⟶ G.left) (wL : LB.Iso U'.LG.L (U.LG.L.pull Ψ)), w.IsGen → wL.IsGen → (∀ x κ, D'.toPre.famφB x κ ≫ Φ = Φ ≫ D.toPre.famφB (xe x) κ) → ∀ (e e' k : ℕ) (h : (thickObj R' I' e' G').left ⟶ (thickObj R I e G).left), (h ≫ (fstG I e G).left = (fstG I' e' G').left ≫ Ψ ∧ ((U'.gt e').pG.left ≫ Φ = h ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e').pG x κ ≫ Φ = h ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧ Geo.Tor.PMaps w (D'.toPre.Oφ (U'.gt e').pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U'.gt e').t x) ((U.gt e).t (xe x)) h) ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R' I' e' G').left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (Φ) ((U'.gt e').pG.left (r z)) ∈ D.toPre.P.L.U jM → (U'.gt e').pG.left (r z) ∈ D'.toPre.P.L.U jM' → (Ψ) ((fstG I' e' G').left (r z)) ∈ U.LG.L.U jL → (fstG I' e' G').left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e').pG.left) z jM jM' * Geo.Tor.gw (U'.w e') r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) (r ≫ h) z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I' e' G').left) z jL jL')) → ∀ (σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (σ' : LB.Sec (LB.LinComb U'.LG.L (K := Fin 1) (fun _ => 𝟙 G'.left) (fun _ => (k : ℤ)))) (f : ∀ α, D.toPre.SecB k α) (f' : ∀ α, D'.toPre.SecB k α), (∀ (Z : Scheme.{0}) (r : Z ⟶ G'.left) (z : Z) (p : Fin 1 → U.LG.L.ι) (q : Fin 1 → U'.LG.L.ι), (∀ κ, (Ψ) ((fun _ : Fin 1 => 𝟙 G'.left) κ (r z)) ∈ U.LG.L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 G'.left) κ (r z) ∈ U'.LG.L.U (q κ)) → Geo.Tor.gs (r ≫ Ψ) z (LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) p) ((σ).f p) = (∏ κ, Geo.Tor.gw wL (r ≫ (fun _ : Fin 1 => 𝟙 G'.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (k : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart U'.LG.L (fun _ : Fin 1 => 𝟙 G'.left) q) ((σ').f q)) → (∀ x : D'.toPre.X, (∀ (Z : Scheme.{0}) (r : Z ⟶ D'.toPre.P.A.left) (z : Z) (p : Fin 4 → D.toPre.P.L.ι) (q : Fin 4 → D'.toPre.P.L.ι), (∀ κ, (Φ) ((D'.toPre.famφB x) κ (r z)) ∈ D.toPre.P.L.U (p κ)) → (∀ κ, (D'.toPre.famφB x) κ (r z) ∈ D'.toPre.P.L.U (q κ)) → Geo.Tor.gs (r ≫ Φ) z (LB.wchart D.toPre.P.L (D.toPre.famφB (xe x)) p) ((f (xe x)).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (D'.toPre.famφB x) κ) z (p κ) (q κ) ^ (DegPre.famε k) κ).val * Geo.Tor.gs r z (LB.wchart D'.toPre.P.L (D'.toPre.famφB x) q) ((f' x).f q))) → U.ExpandsAt e k σ f → U'.ExpandsAt e' k σ' f' := by
  intro R R' _ _ _ _ I I' D D' A A' G _ _ G' _ _ U U' Φ w xe Ψ wL _ _ hφ e e' k h ⟨hG, ⟨hq, hO⟩, hW⟩ σ σ' f f' hσ hf hE
  classical
  obtain ⟨S, hS⟩ := expandsAt_val U e k σ f hE
  refine expandsAt_of_val U' e' k σ' f' (S.map xe.symm.toEquiv.toEmbedding) fun y J' hJ' => ?_
  choose J hJ using fun ψ : (thickObj R' I' e' G').left ⟶ D.toPre.P.A.left => exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hq : pGl U' e' ≫ Φ = h ≫ pGl U e := hq
  have hG : h ≫ fGl I G e = fGl I' G' e' ≫ Ψ := hG
  have hF : ∀ α', sval (f (xe α')) (h ≫ pGl U e) y J =
      (∏ a, om w y J J' (pGl U' e' ≫ D'.toPre.famφB α' a) ^ DegPre.famε k a).val * sval (f' α') (pGl U' e') y J' := by
    intro α'
    rw [← hq]
    exact sec_val w _ _ _ Φ (hφ α') (f (xe α')) (f' α') (pGl U' e') y (hf α' _ (pGl U' e') y) hJ hJ'
  have hT : ∀ α', val (tG U e (xe α')) h y J =
      (∏ a, om w y J J' (Oφl U' e' α' a) ^ Oinvε a) * val (tG U' e' α') (𝟙 _) y J' := fun α' =>
    gen_val w (Oφl U' e' α') (Oφl U e (xe α')) Oinvε h (hO α').1 (tG U e (xe α')) (tG U' e' α') (hO α').2 y hJ hJ'
  have hω := prod_fam U' e' k (om w y J J')
  refine ⟨fun α' hα => ?_, fun jL' hL' => ?_⟩
  · have hi : xe α' ∉ S := fun hc => hα (Finset.mem_map.2 ⟨xe α', hc, xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').symm.trans ((hS _ h y J hJ).1 _ hi))
  · obtain ⟨jL, hL⟩ := exists_chart U.LG.isLB (Ψ (fGl I' G' e' y))
    have hL₁ : fGl I G e (h y) ∈ U.LG.L.U jL := (congrArg (fun g => g y ∈ U.LG.L.U jL) hG).mpr hL
    have W' : om w y J J' (pGl U' e') * wv U' e' (𝟙 _) y (J' (pGl U' e')) jL' =
        wv U e h y (J (h ≫ pGl U e)) jL * gw wL (fGl I' G' e') y jL jL' := by
      have := hW _ (𝟙 _) y (J (pGl U' e' ≫ Φ)) (J' (pGl U' e')) jL jL' (hJ (pGl U' e' ≫ Φ)) (hJ' (pGl U' e')) hL hL'
      simp only [Category.id_comp] at this
      rw [← hq]
      exact this
    have Sg : sv U k σ (h ≫ fGl I G e) y jL =
        (gw wL (fGl I' G' e') y jL jL' ^ k).val * sv U' k σ' (fGl I' G' e') y jL' := by
      have := hσ _ (fGl I' G' e') y (fun _ => jL) (fun _ => jL') (fun _ => hL) (fun _ => hL')
      simp only [Category.comp_id, Fin.prod_univ_one, zpow_natCast] at this
      rw [hG]
      exact this
    refine (om w y J J' (pGl U' e') ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_mul, ← mul_pow, W', mul_pow, Units.val_mul, _root_.mul_assoc, ← Sg,
      (hS _ h y J hJ).2 jL hL₁, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    obtain ⟨α', rfl⟩ := xe.surjective x
    have e₀ : xe.symm.toEquiv.toEmbedding (xe α') = α' := xe.symm_apply_apply α'
    rw [e₀, hF α', hT α', ← hω α', Units.val_mul, Units.val_mul, _root_.mul_mul_mul_comm]

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CorrOfValFieldExtension
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem stalkMap_injective_of_flat' {Y Z : Scheme.{0}} (ρ : Z ⟶ Y) [Flat ρ] (z : Z) :
    Function.Injective (ρ.stalkMap z).hom := by

  let _ := (ρ.stalkMap z).hom.toAlgebra
  have : Module.Flat (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z) := Flat.stalkMap ρ z
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z)) :=
    (by infer_instance : IsLocalHom (ρ.stalkMap z).hom)
  have : Module.FaithfullyFlat (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective (Y.presheaf.stalk (ρ z)) (Z.presheaf.stalk z)

theorem corr_of_val_flat_surjective {X Y Z : Scheme.{0}} (ρ : Z ⟶ Y) [Flat ρ] [Surjective ρ] {L : LB X}
    (hL : L.IsLB) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)}
    {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}
    (h : ∀ z J, Good L z J → val t ρ z J = val t' ρ z J) : LB.Gen.Corr L φ ε φ' ε' t t' := by

  have : Epi ρ := Flat.epi_of_flat_of_surjective ρ
  refine corr_of_val hL fun y J hJ => ?_
  obtain ⟨z, rfl⟩ := ρ.surjective y
  obtain ⟨J', hJ', hJJ'⟩ := exists_good L hL z (fun ψ : Y ⟶ X => ρ ≫ ψ) J
    (fun a b hab => congrArg J ((cancel_epi ρ).1 hab)) (fun ψ => by simpa using hJ ψ)
  have hpull : (fun ψ : Y ⟶ X => J' (ρ ≫ ψ)) = J := funext hJJ'
  have e₁ := (values_natural X Y Y Z L K φ ε (𝟙 Y) ρ z J' hJ').2.2.1 t
  have e₂ := (values_natural X Y Y Z L K' φ' ε' (𝟙 Y) ρ z J' hJ').2.2.1 t'
  rw [Category.comp_id, hpull] at e₁ e₂

  apply Units.ext
  apply stalkMap_injective_of_flat' ρ z
  rw [← e₁, ← e₂, h z J' hJ']

theorem corr_of_val_field_extension : ∀ (K₀ F : Type) [Field K₀] [Field F] (f : K₀ →+* F) (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K K' : Type) [Fintype K] [Fintype K'] (φ : K → (Spec (CommRingCat.of K₀) ⟶ X)) (ε : K → ℤ) (φ' : K' → (Spec (CommRingCat.of K₀) ⟶ X)) (ε' : K' → ℤ) (t : LB.Gen (LB.LinComb L φ ε)) (t' : LB.Gen (LB.LinComb L φ' ε')), (∀ z J, Good L z J → val t (Spec.map (CommRingCat.ofHom f)) z J = val t' (Spec.map (CommRingCat.ofHom f)) z J) → LB.Gen.Corr L φ ε φ' ε' t t' := by
  intro K₀ F _ _ f X L hL K K' _ _ φ ε φ' ε' t t' h

  have hff : (CommRingCat.ofHom f).hom.FaithfullyFlat := by
    let _ := f.toAlgebra
    show Module.FaithfullyFlat K₀ F
    infer_instance
  obtain ⟨h₁, h₂⟩ := (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom f)).2 hff
  exact corr_of_val_flat_surjective (Spec.map (CommRingCat.ofHom f)) hL h

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalEqZeroOfSumMulCoord
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace WeightVal

theorem eq_zero_of_stalk_sum {S : Scheme.{0}} (X : Type) [AddCommGroup X] (Y : Over S) {V : Y.left.Opens}
    (s : Finset X) (h : X → Γ(Y.left, V))
    (hs : ∀ w : (splitTorus S X ⊗ Y).left, (snd (splitTorus S X) Y).left w ∈ V →
      ∑ χ ∈ s, gs (𝟙 _) w ⊤ (TorusInj.chiP X Y χ) * gs (snd (splitTorus S X) Y).left w V (h χ) = 0) :
    ∀ χ ∈ s, h χ = 0 := by
  refine TorusInj.eq_zero_of_sum X Y s h (fn_ext fun w hw => ?_)
  have k : ∀ c : Γ(Y.left, V),
      gs (𝟙 _) w ((snd (splitTorus S X) Y).left ⁻¹ᵁ V) (((snd (splitTorus S X) Y).left.app V).hom c) =
        gs (snd (splitTorus S X) Y).left w V c := fun c =>
    (gs_pull (𝟙 _) _ w V hw c).trans (by rw [Category.id_comp])
  rw [DVR.gs_fsum (𝟙 _) w _ hw, gs_eq (𝟙 _) w _ hw 0, map_zero, map_zero]
  refine Eq.trans (Finset.sum_congr rfl fun χ _ => ?_) (hs w hw)
  rw [gs_mul (𝟙 _) w _ hw, k, gs_res (𝟙 _) w _ hw]

theorem gs_chiP_whisker {S : Scheme.{0}} (X : Type) [AddCommGroup X] {Z Y : Over S} (x : Z ⟶ Y) (χ : X)
    (w : (splitTorus S X ⊗ Z).left) :
    gs (splitTorus S X ◁ x).left w ⊤ (TorusInj.chiP X Y χ) = gs (𝟙 _) w ⊤ (TorusInj.chiP X Z χ) := by
  refine (gs_pull (splitTorus S X ◁ x).left (fst (splitTorus S X) Y).left w ⊤ trivial _).trans
    (Eq.trans ?_ (gs_pull (𝟙 _) (fst (splitTorus S X) Z).left w ⊤ trivial _).symm)
  rw [Category.id_comp, ← Over.comp_left, whiskerLeft_fst]

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G)

theorem val_act (β : D.X) {W : Scheme.{0}} (ρ : W ⟶ (WeightPf.Te D I e ⊗ thickObj R I e G).left) (w : W) {J}
    (hJ : Good D.P.L w J) :
    (val (g.t β) (ρ ≫ (WeightPf.act g).left) w J).val =
      gs ρ w ⊤ (TorusInj.chiP D.X (thickObj R I e G) β) *
        (val (g.t β) (ρ ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left) w J).val := by
  have E := val_corr hJ (g.t_weight β) ρ
  rw [val_mul hJ, val_pull hJ, val_pull hJ] at E
  refine (congrArg Units.val E).trans ((Units.val_mul _ _).trans (congrArg₂ (· * ·) ?_ rfl))
  have hm := hJ.mem (L := D.P.L) (K := PEmpty) (Y := (WeightPf.Te D I e ⊗ thickObj R I e G).left)
    PEmpty.elim ρ
  exact (congrArg Units.val ((gm_res ρ w _ hm _).trans
    (gm_pull ρ (fst (WeightPf.Te D I e) (thickObj R I e G)).left w ⊤ trivial (charUnit _ D.X β)))).trans
      ((gs_unit _ w ⊤ trivial _).symm.trans
      (gs_pull ρ (fst (WeightPf.Te D I e) (thickObj R I e G)).left w ⊤ trivial _).symm)

theorem coeff_eq_zero_over {Y : Over (Spec (CommRingCat.of R))} (p : Y ⟶ D.P.A) {K : Type} [Fintype K]
    {φ : D.X → K → (Y.left ⟶ D.P.A.left)} {ε : K → ℤ} (d : ∀ α, LB.Sec (LB.LinComb D.P.L (φ α) ε)) (s : Finset D.X)
    (H : ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left →
      ∀ (z : Z) (J), Good D.P.L z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z J).val = 0)
    (α : D.X) (hα : α ∈ s) (Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (x : Z ⟶ thickObj R I e G)
    (r : Z.left ⟶ Y.left) (hr : r ≫ p.left = x.left ≫ g.pG.left) (z : Z.left) (J) (hJ : Good D.P.L z J) :
    sval (d α) r z J = 0 := by
  classical
  let jf : D.X → K → D.P.L.ι := fun β a => J (r ≫ φ β a)
  let jt : D.X → Fin 4 → D.P.L.ι := fun β a => J (x.left ≫ D.Oφ g.pG β a)
  let V : Z.left.Opens := s.inf (fun β => r ⁻¹ᵁ LB.wchart D.P.L (φ β) (jf β) ⊓
      x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β))
  have hz : z ∈ V := DVR.mem_finf s _ _ fun β _ => ⟨hJ.mem (φ β) r, hJ.mem (D.Oφ g.pG β) x.left⟩
  have hVf : ∀ β ∈ s, V ≤ r ⁻¹ᵁ LB.wchart D.P.L (φ β) (jf β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_left
  have hVt : ∀ β ∈ s, V ≤ x.left ⁻¹ᵁ LB.wchart D.P.L (D.Oφ g.pG β) (jt β) :=
    fun β hβ => (Finset.inf_le hβ).trans inf_le_right
  have ex : ∀ β ∈ s, ∃ c : Γ(Z.left, V), ∀ (W : Scheme.{0}) (ρ : W ⟶ Z.left) (w : W),
      ρ w ∈ V → gs ρ w V c = gs (ρ ≫ r) w (LB.wchart D.P.L (φ β) (jf β)) ((d β).f (jf β)) *
        (gm (ρ ≫ x.left) w (LB.wchart D.P.L (D.Oφ g.pG β) (jt β)) ((g.t β).s (jt β))).val := fun β hβ =>
    ⟨(r.appLE _ V (hVf β hβ)).hom ((d β).f (jf β)) * (x.left.appLE _ V (hVt β hβ)).hom ((g.t β).s (jt β)).val,
      fun W ρ w hw => (gs_mul ρ w V hw _ _).trans (congrArg₂ (· * ·) (gs_appLE _ _ V _ ρ w hw _)
        ((gs_appLE _ _ V _ ρ w hw _).trans (gs_unit (ρ ≫ x.left) w _ (hVt β hβ hw) _)))⟩
  choose! c hc using ex
  have hsn : (WeightPf.Te D I e ◁ x).left ≫ (snd (WeightPf.Te D I e) (thickObj R I e G)).left =
      (snd (WeightPf.Te D I e) Z).left ≫ x.left := by
    rw [← Over.comp_left, ← Over.comp_left, whiskerLeft_snd]
  let σ : Z ⟶ WeightPf.Te D I e ⊗ Z := lift (toUnit _ ≫ η[WeightPf.Te D I e]) (𝟙 _)
  have hσ : σ.left ≫ (snd (WeightPf.Te D I e) Z).left = 𝟙 _ := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  have H0 := eq_zero_of_stalk_sum D.X Z s c (fun w hw => by
    choose j hj using fun ψ : (WeightPf.Te D I e ⊗ Z).left ⟶ D.P.A.left => exists_chart D.P.isLB (ψ w)
    let J₂ : ((WeightPf.Te D I e ⊗ Z).left ⟶ D.P.A.left) → D.P.L.ι := fun ψ =>
      if ψ w ∈ D.P.L.U (J (σ.left ≫ ψ)) then J (σ.left ≫ ψ) else j ψ
    have hJ₂ : Good D.P.L w J₂ := fun ψ => by
      by_cases h : ψ w ∈ D.P.L.U (J (σ.left ≫ ψ))
      · simpa only [J₂, if_pos h] using h
      · simpa only [J₂, if_neg h] using hj ψ
    have eJ : ∀ ψ : Z.left ⟶ D.P.A.left, ψ ((snd (WeightPf.Te D I e) Z).left w) ∈ D.P.L.U (J ψ) →
        J₂ ((snd (WeightPf.Te D I e) Z).left ≫ ψ) = J ψ := fun ψ h => by
      have e₁ : σ.left ≫ (snd (WeightPf.Te D I e) Z).left ≫ ψ = ψ := by
        rw [← Category.assoc, hσ, Category.id_comp]
      simp only [J₂, e₁]
      exact if_pos h
    have E := H _ ((WeightPf.Te D I e ◁ x).left ≫ (WeightPf.act g).left) ((snd (WeightPf.Te D I e) Z).left ≫ r)
      (by rw [Category.assoc, Category.assoc, hr, WeightPf.act_left_pG, ← Category.assoc, ← Category.assoc, hsn])
      w J₂ hJ₂
    refine Eq.trans (Finset.sum_congr rfl fun β hβ => ?_) E
    rw [hc β hβ _ _ w hw, val_act g β _ w hJ₂, mul_left_comm, hsn, gs_chiP_whisker,
      sval_of (d β) _ w J₂ (jf β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVf β hβ hw) a)),
      val_of (g.t β) _ w J₂ (jt β) (fun a => by
        rw [Category.assoc]; exact eJ _ (Set.mem_iInter.1 (hVt β hβ hw) a))]) α hα
  have E := hc α hα _ (𝟙 _) z hz
  rw [H0, gs_eq _ z V hz, map_zero, map_zero, Category.id_comp, Category.id_comp] at E
  exact (Units.mul_left_eq_zero _).1 E.symm

end WeightVal

theorem sval_eq_zero_of_sum_mul_coord : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (Y : Over (Spec (CommRingCat.of R))) (p : Y ⟶ D.P.A) (K : Type) [Fintype K] (φ : D.X → K → (Y.left ⟶ D.P.A.left)) (ε : K → ℤ) (d : ∀ α, LB.Sec (LB.LinComb D.P.L (φ α) ε)) (s : Finset D.X), (∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good D.P.L z J → ∑ α ∈ s, sval (d α) r z J * (val (g.t α) x z J).val = 0) → ∀ α ∈ s, ∀ (Z : Scheme.{0}) (x : Z ⟶ (thickObj R I e G).left) (r : Z ⟶ Y.left), r ≫ p.left = x ≫ g.pG.left → ∀ (z : Z) (J), Good D.P.L z J → sval (d α) r z J = 0 := by
  intro R _ _ I D e G _ _ g Y p K _ φ ε d s H α hα Z x r hr z J hJ
  exact WeightVal.coeff_eq_zero_over g p d s H α hα (Over.mk (x ≫ (thickObj R I e G).hom)) (Over.homMk x rfl) r hr z J hJ

end GlobalTheory
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfSvalWhiskerRightEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfSvalWhiskerRightEqZero
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem sec_eq_zero_of_sval_eq_zero_of_app_injective {X Y Z : Scheme.{0}} (r : Z ⟶ Y)
    (hr : ∀ U : Y.Opens, Function.Injective (r.app U).hom) (L : LB X) (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ (z : Z) (J), Good L z J → sval d r z J = 0) (j : K → L.ι) : d.f j = 0 := by
  apply hr (LB.wchart L φ j)
  refine fn_ext fun z hz => ?_
  choose I hI using fun χ : Z ⟶ X => exists_chart hL (χ z)
  have hz' : r z ∈ LB.wchart L φ j := hz
  have e₁ : gs r z (LB.wchart L φ j) (d.f j) = 0 :=
    (sec_trans d r z hz' (Good.mem hI φ r)).trans ((congrArg _ (h z I hI)).trans (mul_zero _))
  have e₂ : gs r z (LB.wchart L φ j) 0 = 0 := by
    rw [gs_eq r z _ hz', map_zero, map_zero]
  refine (gs_pull (𝟙 Z) r z _ hz' _).trans (Eq.trans ?_ (gs_pull (𝟙 Z) r z _ hz' _).symm)
  rw [Category.id_comp]
  exact e₁.trans e₂.symm

theorem sec_eq_zero_of_sval_whiskerRight_eq_zero :
    ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (ψ : T' ⟶ T), Function.Injective ψ.left.appTop.hom → ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → ((T ⊗ B).left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (z : (T' ⊗ B).left) (J), Good L z J → sval d (ψ ▷ B).left z J = 0) → ∀ j, d.f j = 0 := by
  intro S B T T' _ _ _ ψ hψ X L hL K _ φ ε d h j
  exact sec_eq_zero_of_sval_eq_zero_of_app_injective (ψ ▷ B).left
    (app_whiskerRight_injective_of_flat S B T T' ψ hψ) L hL φ ε d h j

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SecEqZeroOfSvalWhiskerRightEqZeroStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
theorem _root_.GlobalTheory.T.sec_eq_zero_of_sval_whiskerRight_zero : ∀ (S : Scheme.{0}) (B T T' : Over S) [Flat B.hom] [IsAffine T.left] [IsAffine T'.left] (ψ : T' ⟶ T), Function.Injective ψ.left.appTop.hom → ∀ (X : Scheme.{0}) (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → ((T ⊗ B).left ⟶ X)) (ε : K → ℤ) (d : LB.Sec (LB.LinComb L φ ε)), (∀ (z : (T' ⊗ B).left) (J), Good L z J → sval d (ψ ▷ B).left z J = 0) → ∀ j, d.f j = 0 := by
  first | exact @GlobalTheory.sec_eq_zero_of_sval_whiskerRight_eq_zero | exact GlobalTheory.sec_eq_zero_of_sval_whiskerRight_eq_zero | (intros; apply GlobalTheory.sec_eq_zero_of_sval_whiskerRight_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SvalNeZeroOfIsIso
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem gs_eq_stalkMap_gs_id {Y Y' : Scheme.{0}} (τ : Y' ⟶ Y) (y : Y') (U : Y.Opens) (hy : τ y ∈ U) (a : Γ(Y, U)) :
    gs τ y U a = (τ.stalkMap y).hom (gs (𝟙 Y) (τ y) U a) := by
  have e : gs (𝟙 Y) (τ y) U a = (Y.presheaf.germ U (τ y) hy).hom a := gs_eq (𝟙 Y) (τ y) U hy a
  rw [e, gs_eq τ y U hy]
  exact (Scheme.Hom.germ_stalkMap_apply τ U y hy a).symm

theorem sval_ne_zero_of_isIso : ∀ (X Y : Scheme.{0}) [IsIntegral Y] (L : LB X), L.IsLB → ∀ (K : Type) [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : LB.Sec (LB.LinComb L φ ε)), (∃ j, s.f j ≠ 0) → ∀ (Y' : Scheme.{0}) (τ : Y' ⟶ Y) [IsIso τ] (y : Y') (J), Good L y J → sval s τ y J ≠ 0 := by
  intro X Y _ L hL K _ φ ε s hs Y' τ _ y J hJ h0
  have hG : Good L (τ y) (fun χ : Y ⟶ X => J (τ ≫ χ)) := fun χ => hJ (τ ≫ χ)
  have h1 := (exists_ne_zero_iff_sval_ne_zero s hG).1 hs
  rw [sval_of s (𝟙 Y) (τ y) _ (fun k => J (τ ≫ φ k)) (fun k => by rw [Category.id_comp])] at h1
  apply h1
  have h2 : gs τ y (LB.wchart L φ (fun k => J (τ ≫ φ k))) (s.f (fun k => J (τ ≫ φ k))) = 0 := h0
  have h3 := (gs_eq_stalkMap_gs_id τ y _ (hJ.mem φ τ) _).symm.trans h2
  have hinj : Function.Injective (τ.stalkMap y).hom :=
    (ConcreteCategory.bijective_of_isIso (τ.stalkMap y)).1
  exact (map_eq_zero_iff _ hinj).1 h3

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtIffStalks
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

private theorem gs_res_global_scal_eq_cst {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (q : Z ⟶ Y) (z : Z) (V : Y.Opens) (hz : q z ∈ V) (c : R) :
    gs q z V (resTop V (scal p c)) = cst (q ≫ p) z c := by
  unfold resTop
  rw [gs_res q z le_top hz]
  unfold scal cst
  exact gs_pull q p z ⊤ trivial _

theorem gs_of_eq_sum_scal {R : Type} [CommRing R] {Y Z : Scheme.{0}} (p : Y ⟶ Spec (CommRingCat.of R))
    (q : Z ⟶ Y) (z : Z) (V : Y.Opens) (hz : q z ∈ V) {n : ℕ} (c : Fin n → R) {a : Γ(Y, V)} {b : Fin n → Γ(Y, V)}
    (h : a = ∑ i, resTop V (scal p (c i)) * b i) :
    gs q z V a = ∑ i, cst (q ≫ p) z (c i) * gs q z V (b i) := by
  subst h
  rw [gs_fsum q z V hz]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [gs_mul q z V hz, gs_res_global_scal_eq_cst p q z V hz]

theorem expandsAt_iff_stalks {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (e k : ℕ) (σ : H0 U.LG.L k) (f : ∀ α : D.toPre.X, D.toPre.SecB k α) :
    U.ExpandsAt e k σ f ↔ ∃ S : Finset D.toPre.X, ∀ (y : (thickObj R I e G).left) (J), Good D.toPre.P.L y J →
      (∀ α ∉ S, sval (f α) (pGl U e) y J = 0) ∧ ∀ jL, (fGl I G e) y ∈ U.LG.L.U jL →
        (wv U e (𝟙 _) y (J (pGl U e)) jL ^ k).val * sv U k σ (fGl I G e) y jL =
          ∑ α ∈ S, sval (f α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := expandsAt_val U e k σ f h
    refine ⟨S, fun y J hJ => ?_⟩
    have hy := hS _ (𝟙 _) y J hJ
    simp only [Category.id_comp] at hy
    exact hy
  · rintro ⟨S, hS⟩
    exact expandsAt_of_val U e k σ f S hS

theorem expandsAt_linear : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k e n : ℕ) (c : Fin n → R) (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f : Fin n → ∀ α, D.toPre.SecB k α) (σ₀ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ : ∀ α, D.toPre.SecB k α), (∀ i, U.ExpandsAt e k (σ i) (f i)) → (∀ j, σ₀.f j = ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j) → (∀ α j, (f₀ α).f j = ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j) → U.ExpandsAt e k σ₀ f₀ := by
  intro R _ _ I D A G _ _ U k e n c σ f σ₀ f₀ hE hσ hf
  classical
  have hE' := fun i => (expandsAt_iff_stalks U e k (σ i) (f i)).1 (hE i)
  choose S hS using hE'
  refine (expandsAt_iff_stalks U e k σ₀ f₀).2 ⟨Finset.univ.biUnion S, fun y J hJ => ?_⟩
  have hc : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom := (Over.w _).trans (Over.w _).symm
  have key₀ : ∀ α, sval (f₀ α) (pGl U e) y J =
      ∑ i, cst (pGl U e ≫ D.toPre.P.A.hom) y (c i) * sval (f i α) (pGl U e) y J := fun α =>
    gs_of_eq_sum_scal D.toPre.P.A.hom (pGl U e) y _ (Good.mem hJ _ _) c (hf α _)
  refine ⟨fun α hα => ?_, fun jL hjL => ?_⟩
  · rw [key₀ α]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [(hS i y J hJ).1 α (fun h => hα (Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, h⟩)), mul_zero]
  · have hmem : fGl I G e y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => jL) :=
      Set.mem_iInter.2 fun _ => hjL
    have keyσ : sv U k σ₀ (fGl I G e) y jL =
        ∑ i, cst (fGl I G e ≫ G.hom) y (c i) * sv U k (σ i) (fGl I G e) y jL :=
      gs_of_eq_sum_scal G.hom (fGl I G e) y _ hmem c (hσ _)
    have hR : ∑ α ∈ Finset.univ.biUnion S, sval (f₀ α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val =
        ∑ i, ∑ α ∈ Finset.univ.biUnion S,
          cst (fGl I G e ≫ G.hom) y (c i) * sval (f i α) (pGl U e) y J * (val (tG U e α) (𝟙 _) y J).val := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [key₀ α, Finset.sum_mul, hc]
    rw [hR, keyσ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_left_comm, (hS i y J hJ).2 jL hjL,
      Finset.sum_subset (Finset.subset_biUnion_of_mem S (Finset.mem_univ i))
        (fun α _ hα => by rw [(hS i y J hJ).1 α hα, zero_mul]), Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [_root_.mul_assoc]

end GlobalTheory
end
end
