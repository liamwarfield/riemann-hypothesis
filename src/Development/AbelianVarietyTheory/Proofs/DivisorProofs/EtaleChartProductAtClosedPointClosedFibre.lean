module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoordinatesDescendAlongProperMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordTensorDataFactorInclusionProjectionProps
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFromBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleNearPointOfEtaleOnFibreSmooth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateMapEtaleNearProperFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateMapEtaleNearProperFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.FibEt

@[reassoc]
theorem map_fst' {X Y Z X' Y' Z' : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z') (h1 : f ≫ i₃ = i₁ ≫ f') (h2 : g ≫ i₃ = i₂ ≫ g') :
    pullback.map f g f' g' i₁ i₂ i₃ h1 h2 ≫ pullback.fst f' g' = pullback.fst f g ≫ i₁ :=
  pullback.lift_fst _ _ _

@[reassoc]
theorem map_snd' {X Y Z X' Y' Z' : Scheme.{0}} (f : X ⟶ Z) (g : Y ⟶ Z) (f' : X' ⟶ Z') (g' : Y' ⟶ Z') (i₁ : X ⟶ X')
    (i₂ : Y ⟶ Y') (i₃ : Z ⟶ Z') (h1 : f ≫ i₃ = i₁ ≫ f') (h2 : g ≫ i₃ = i₂ ≫ g') :
    pullback.map f g f' g' i₁ i₂ i₃ h1 h2 ≫ pullback.snd f' g' = pullback.snd f g ≫ i₂ :=
  pullback.lift_snd _ _ _

end GlobalTheory.Mum.FibEt

namespace GlobalTheory.Mum.FibEt

theorem exists_residue_factor {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} (π : S ⟶ Sp R) (s : S)
    (hs : π s = closedPoint R) :
    ∃ κ : ResidueField R →+* S.residueField s, S.fromSpecResidueField s ≫ π = spMap (κ.comp (residue R)) := by
  let φ := Spec.preimage (S.fromSpecResidueField s ≫ π)
  have hφ : Spec.map φ = S.fromSpecResidueField s ≫ π := Spec.map_preimage _
  have hpt : ∀ t : Spec (S.residueField s), (Spec.map φ) t = closedPoint R := by
    intro t
    rw [hφ, Scheme.Hom.comp_apply]
    have : S.fromSpecResidueField s t = s := by
      have := Set.mem_range_self (f := ⇑(S.fromSpecResidueField s)) t
      rwa [Scheme.range_fromSpecResidueField] at this
    rw [this, hs]
  have hker : ∀ r ∈ maximalIdeal R, φ.hom r = 0 := by
    intro r hr
    let t : Spec (S.residueField s) := closedPoint (S.residueField s)
    have h1 : (PrimeSpectrum.comap φ.hom t) = closedPoint R := hpt t
    have h2 : r ∈ (PrimeSpectrum.comap φ.hom t).asIdeal := by rw [h1]; exact hr
    simpa [t, closedPoint] using h2
  refine ⟨Ideal.Quotient.lift (maximalIdeal R) φ.hom hker, ?_⟩
  rw [← hφ]
  rfl

end GlobalTheory.Mum.FibEt

namespace GlobalTheory.Mum.FibEt

theorem smooth_affineSpace_sp (R : Type) [CommRing R] (g : ℕ) : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := by
  have e : (𝔸(Fin g; Sp R) ↘ Sp R) = (AffineSpace.isoOfIsAffine (Fin g) (Sp R)).hom ≫
      Spec.map (CommRingCat.ofHom MvPolynomial.C) ≫ (Sp R).isoSpec.inv := by
    rw [← AffineSpace.isoOfIsAffine_inv_over (n := Fin g) (S := Sp R), Iso.hom_inv_id_assoc]
  rw [e]
  haveI : Algebra.Smooth Γ(Sp R, ⊤) (MvPolynomial (Fin g) Γ(Sp R, ⊤)) := ⟨inferInstance, inferInstance⟩
  have : Smooth (Spec.map (CommRingCat.ofHom (MvPolynomial.C (R := Γ(Sp R, ⊤)) (σ := Fin g)))) := by
    rw [HasRingHomProperty.Spec_iff (P := @Smooth)]
    exact RingHom.smooth_algebraMap.mpr inferInstance
  infer_instance

end GlobalTheory.Mum.FibEt


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mum.fibre_etale_near : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), a ≫ b = X.ι ≫ E.f → ∀ (x : P') (y : E.Y.left), E.j y = b x → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (W0 : (PSpace R E.N).Opens) (g : ℕ) (τ0 : W0.toScheme ⟶ 𝔸(Fin g; Sp R)) (O : E.Y.left.Opens) (e : O.toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) (spMap (residue R))), y ∈ O → (O : Set E.Y.left) ⊆ E.j ⁻¹' W0 → τ0 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = W0.ι ≫ PSpace.str R E.N → Etale e → e ≫ pullback.snd _ _ = O.ι ≫ E.Y.hom → (∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (w : T ⟶ W0.toScheme), w ≫ W0.ι = t ≫ O.ι ≫ E.j → t ≫ e ≫ pullback.fst _ _ = w ≫ τ0) → ∀ (c : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π), c ≫ pullback.fst _ _ = (a ∣_ (b ⁻¹ᵁ W0)) ≫ (b ∣_ W0) ≫ τ0 → c ≫ pullback.snd _ _ = (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom → ∀ z : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme, ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c) := by
  intro R _ _ _ hR M G' _ _ hG E P' b X a hab x y hyb hx0 W0 g τ0 O e hyO hOW hτ0 he he2 he3 c hc1 hc2 z hz
  haveI : Smooth G'.hom := hG.smooth
  haveI : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := FibEt.smooth_affineSpace_sp R g
  haveI : Etale e := he
  let iV : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ G'.left := (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι
  let p : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ M.S := iV ≫ G'.hom
  have hh : c ≫ pullback.snd (𝔸(Fin g; Sp R) ↘ Sp R) M.π = p := by
    rw [hc2]; simp only [p, iV, Category.assoc]
  have hp : Smooth p := by dsimp only [p, iV]; infer_instance
  have key : a ≫ b ≫ PSpace.str R E.N = X.ι ≫ E.H.ι ≫ G'.hom ≫ M.π := by rw [reassoc_of% hab, E.f_over]
  have hs : M.π (p z) = closedPoint R := by
    have h1 := congrArg (fun f : X.toScheme ⟶ Sp R => f ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι z)) key
    simp only [Scheme.Hom.comp_apply] at h1 hz ⊢
    simp only [p, iV, Scheme.Hom.comp_apply]
    rw [← h1, hz]
    simpa [Scheme.Hom.comp_apply] using hx0
  obtain ⟨κ, hκ⟩ := FibEt.exists_residue_factor M.π (p z) hs
  obtain ⟨Ω', _, io, eG, l, -, hl1, hl2⟩ := E.fib (M.S.residueField (p z)) (M.S.fromSpecResidueField (p z)) κ hκ

  let Vs := (a ⁻¹ᵁ (b ⁻¹ᵁ W0))
  let x' : Sp Ω' ⟶ M.S := spMap io ≫ M.S.fromSpecResidueField (p z)
  let k' : Sp Ω' ⟶ Sp (ResidueField R) := spMap (io.comp κ)
  have hxk : x' ≫ M.π = k' ≫ spMap (residue R) := by
    simp only [x', k', Category.assoc, hκ, ← Spec.map_comp]; rfl
  have hpt : x' (closedPoint Ω') = p z := by
    simp only [x', Scheme.Hom.comp_apply]
    have := Set.mem_range_self (f := ⇑(M.S.fromSpecResidueField (p z))) ((spMap io) (closedPoint Ω'))
    rwa [Scheme.range_fromSpecResidueField] at this
  obtain ⟨w, hw1, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := x') z (closedPoint Ω') hpt.symm
  let mG : pullback p x' ⟶ pullback G'.hom x' :=
    pullback.map p x' G'.hom x' iV (𝟙 _) (𝟙 _) (by simp [p]) (by simp)
  let gm : pullback p x' ⟶ pullback E.Y.hom k' := mG ≫ eG.hom.left
  have hgms : gm ≫ pullback.snd E.Y.hom k' = pullback.snd p x' := by
    have hA : eG.hom.left ≫ pullback.snd E.Y.hom k' = pullback.snd G'.hom x' := Over.w eG.hom
    simp only [gm, Category.assoc, hA, mG, FibEt.map_snd', Category.comp_id]
  have E1 : mG ≫ l = pullback.fst p x' ≫ Vs.ι ≫ X.ι := by
    rw [← cancel_mono E.H.ι, Category.assoc, hl1]
    exact FibEt.map_fst' _ _ _ _ _ _ _ _ _
  have E2 : gm ≫ pullback.fst E.Y.hom k' ≫ E.j = pullback.fst p x' ≫ Vs.ι ≫ a ≫ b := by
    simp only [gm, Category.assoc]
    erw [← hl2]
    rw [reassoc_of% E1, hab]
  have hgmw : (gm ≫ pullback.fst E.Y.hom k') w = y := by
    haveI : IsImmersion E.j := E.imm
    apply E.j.isEmbedding.injective
    have h := congrArg (fun f : pullback p x' ⟶ PSpace R E.N => f w) E2
    simp only [Scheme.Hom.comp_apply] at h hz ⊢
    rw [h, hw1, hz, hyb]
  let Wo : (pullback p x').Opens := (gm ≫ pullback.fst E.Y.hom k') ⁻¹ᵁ O
  have hwW : w ∈ Wo := by
    show (gm ≫ pullback.fst E.Y.hom k') w ∈ O
    rw [hgmw]; exact hyO

  let A := 𝔸(Fin g; Sp R) ↘ Sp R
  let Oy := pullback (O.ι ≫ E.Y.hom) k'
  let eΩ : Oy ⟶ pullback (pullback.snd A (spMap (residue R))) k' :=
    pullback.map (O.ι ≫ E.Y.hom) k' (pullback.snd A (spMap (residue R))) k' e (𝟙 _) (𝟙 _)
      (by rw [Category.comp_id, he2]) (by simp)
  haveI : MorphismProperty.IsStableUnderComposition @Etale := MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  have heΩ : Etale eΩ :=
    MorphismProperty.pullbackMap (P := @Etale) (f := O.ι ≫ E.Y.hom) (g := k') (f' := pullback.snd A (spMap (residue R)))
      (g' := k') (i₁ := e) (i₂ := 𝟙 _) he inferInstance he2.symm (by simp)
  let θ : pullback (pullback.snd A (spMap (residue R))) k' ⟶ pullback (pullback.snd A M.π) x' :=
    (pullbackLeftPullbackSndIso A (spMap (residue R)) k').hom ≫ (pullback.congrHom rfl hxk.symm).hom ≫
      (pullbackLeftPullbackSndIso A M.π x').inv
  have hθ1 : θ ≫ pullback.fst (pullback.snd A M.π) x' ≫ pullback.fst A M.π =
      pullback.fst (pullback.snd A (spMap (residue R))) k' ≫ pullback.fst A (spMap (residue R)) := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_fst, pullback.congrHom_hom, FibEt.map_fst',
      Category.comp_id, pullbackLeftPullbackSndIso_hom_fst]
  have hθ2 : θ ≫ pullback.fst (pullback.snd A M.π) x' ≫ pullback.snd A M.π =
      pullback.snd (pullback.snd A (spMap (residue R))) k' ≫ x' := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd, pullback.congrHom_hom, FibEt.map_snd'_assoc,
      Category.id_comp]
    simp
  have hθ3 : θ ≫ pullback.snd (pullback.snd A M.π) x' = pullback.snd (pullback.snd A (spMap (residue R))) k' := by
    simp only [θ, Category.assoc, pullbackLeftPullbackSndIso_inv_snd_snd, pullback.congrHom_hom, FibEt.map_snd',
      Category.comp_id]
    simp

  let ψ : Wo.toScheme ⟶ Oy :=
    pullback.lift ((gm ≫ pullback.fst E.Y.hom k') ∣_ O) (Wo.ι ≫ gm ≫ pullback.snd E.Y.hom k') (by
      rw [← Category.assoc, morphismRestrict_ι]
      simp only [Category.assoc, pullback.condition]
      rfl)
  have hψ1 : ψ ≫ pullback.fst (O.ι ≫ E.Y.hom) k' = (gm ≫ pullback.fst E.Y.hom k') ∣_ O := pullback.lift_fst _ _ _
  have hψ2 : ψ ≫ pullback.snd (O.ι ≫ E.Y.hom) k' = Wo.ι ≫ gm ≫ pullback.snd E.Y.hom k' := pullback.lift_snd _ _ _
  let jO : Oy ⟶ pullback E.Y.hom k' :=
    pullback.map (O.ι ≫ E.Y.hom) k' E.Y.hom k' O.ι (𝟙 _) (𝟙 _) (by simp) (by simp)
  haveI : IsOpenImmersion jO :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (f := O.ι ≫ E.Y.hom) (g := k') (f' := E.Y.hom) (g' := k')
      (i₁ := O.ι) (i₂ := 𝟙 _) inferInstance inferInstance rfl (by simp)
  haveI : IsOpenImmersion mG :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) (f := p) (g := x') (f' := G'.hom) (g' := x')
      (i₁ := iV) (i₂ := 𝟙 _) (by dsimp only [iV]; infer_instance) inferInstance rfl (by simp)
  haveI : IsIso eG.hom.left := by
    show IsIso ((Over.forget _).map eG.hom); infer_instance
  have hψj : ψ ≫ jO = Wo.ι ≫ gm := by
    apply pullback.hom_ext
    · dsimp only [jO]
      rw [Category.assoc, FibEt.map_fst', reassoc_of% hψ1, morphismRestrict_ι]
      simp only [Category.assoc]
      rfl
    · dsimp only [jO]
      rw [Category.assoc, FibEt.map_snd', Category.comp_id, hψ2]
      simp only [Category.assoc]
  haveI : IsOpenImmersion (ψ ≫ jO) := by rw [hψj]; dsimp only [gm]; infer_instance
  haveI : IsOpenImmersion ψ := IsOpenImmersion.of_comp ψ jO
  have hEq : Wo.ι ≫ pullback.map p x' (pullback.snd A M.π) x' c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hh]) (by simp) = ψ ≫ eΩ ≫ θ := by
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · have hcond : (Wo.ι ≫ pullback.fst p x' ≫ (a ∣_ (b ⁻¹ᵁ W0)) ≫ (b ∣_ W0)) ≫ W0.ι =
            ((gm ≫ pullback.fst E.Y.hom k') ∣_ O) ≫ O.ι ≫ E.j := by
          simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc]
          rw [E2]
        simp only [Category.assoc]
        rw [hθ1, FibEt.map_fst'_assoc, hc1]
        dsimp only [eΩ]
        rw [FibEt.map_fst'_assoc, reassoc_of% hψ1, he3 _ _ _ hcond]
        simp only [Category.assoc]
      · simp only [Category.assoc]
        rw [hθ2, FibEt.map_fst'_assoc, hh]
        dsimp only [eΩ]
        rw [FibEt.map_snd'_assoc, Category.id_comp, reassoc_of% hψ2]
        rw [reassoc_of% hgms, pullback.condition]
    · simp only [Category.assoc]
      rw [hθ3, FibEt.map_snd', Category.comp_id]
      dsimp only [eΩ]
      rw [FibEt.map_snd', Category.comp_id, hψ2, hgms]
  have hEt : Etale (Wo.ι ≫ pullback.map p x' (pullback.snd A M.π) x' c (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hh]) (by simp)) := by
    rw [hEq]; infer_instance
  obtain ⟨U, hU, hUe⟩ := GlobalTheory.Mum.etale_near_of_etale_fibre M.S Vs.toScheme _ p (pullback.snd A M.π) c hh hp inferInstance Ω' x' Wo w hwW hEt
  exact ⟨U, hw1 ▸ hU, hUe⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateMapEtaleNearProperFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coordinateMap_etale_near_properFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), a ≫ b = X.ι ≫ E.f → ∀ (x : P') (y : E.Y.left), E.j y = b x → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (W0 : (PSpace R E.N).Opens) (g : ℕ) (τ0 : W0.toScheme ⟶ 𝔸(Fin g; Sp R)) (O : E.Y.left.Opens) (e : O.toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) (spMap (residue R))), y ∈ O → (O : Set E.Y.left) ⊆ E.j ⁻¹' W0 → τ0 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = W0.ι ≫ PSpace.str R E.N → Etale e → e ≫ pullback.snd _ _ = O.ι ≫ E.Y.hom → (∀ (T : Scheme.{0}) (t : T ⟶ O.toScheme) (w : T ⟶ W0.toScheme), w ≫ W0.ι = t ≫ O.ι ≫ E.j → t ≫ e ≫ pullback.fst _ _ = w ≫ τ0) → ∀ (c : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π), c ≫ pullback.fst _ _ = (a ∣_ (b ⁻¹ᵁ W0)) ≫ (b ∣_ W0) ≫ τ0 → c ≫ pullback.snd _ _ = (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom → ∀ z : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme, ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c) := by
  first | exact @GlobalTheory.Mum.fibre_etale_near | exact GlobalTheory.Mum.fibre_etale_near | (intros; apply GlobalTheory.Mum.fibre_etale_near <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFibreOfGeometricLifting
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFibreOfGeometricLifting
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem exists_mem_fibre_of_geometric_lifting :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] (S P' X : Scheme.{0}) (π : S ⟶ Sp R) (h : P' ⟶ Sp R) (a : X ⟶ P') (q : X ⟶ S), Surjective π → ∀ x : P', h x = closedPoint R → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ h = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ q = s) → ∃ z : X, a z = x := by
  intro R _ _ S P' X π h a q hπ x hx H
  obtain ⟨s₀, hs₀⟩ := π.surjective (h x)
  obtain ⟨w, hw, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := h) (g := π) x s₀ hs₀.symm
  let Ω : Type := AlgebraicClosure ((pullback h π).residueField w)
  let t : Sp Ω ⟶ pullback h π :=
    Spec.map (CommRingCat.ofHom (algebraMap ((pullback h π).residueField w) Ω)) ≫
      (pullback h π).fromSpecResidueField w
  have ht : ∀ y, t y = w := by
    intro y
    simp only [t, Scheme.Hom.comp_apply]
    exact Scheme.fromSpecResidueField_apply _ _
  have hξ : ∀ y, (t ≫ pullback.fst h π) y = x := by
    intro y
    rw [Scheme.Hom.comp_apply, ht, hw]
  obtain ⟨p, hp, -⟩ := H Ω (t ≫ pullback.fst h π) (t ≫ pullback.snd h π)
    (by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        exact hξ u
      · rintro rfl
        exact ⟨closedPoint Ω, hξ _⟩)
    (by simp [pullback.condition])
  refine ⟨p (closedPoint Ω), ?_⟩
  have h₀ := hξ (closedPoint Ω)
  rw [← hp] at h₀
  exact (Scheme.Hom.comp_apply p a _).symm.trans h₀

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemFibreOfGeometricLiftingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_mem_fiber_of_geometric_lifting : ∀ (R : Type) [CommRing R] [IsLocalRing R] (S P' X : Scheme.{0}) (π : S ⟶ Sp R) (h : P' ⟶ Sp R) (a : X ⟶ P') (q : X ⟶ S), Surjective π → ∀ x : P', h x = closedPoint R → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ S), Set.range ξ = {x} → ξ ≫ h = s ≫ π → ∃ p : Sp Ω ⟶ X, p ≫ a = ξ ∧ p ≫ q = s) → ∃ z : X, a z = x := by
  first | exact @GlobalTheory.Mum.exists_mem_fibre_of_geometric_lifting | exact GlobalTheory.Mum.exists_mem_fibre_of_geometric_lifting | (intros; apply GlobalTheory.Mum.exists_mem_fibre_of_geometric_lifting <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackMorphismRestrictImageOfRestrictRestric
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackMorphismRestrictImageOfRestrictRestric
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isPullback_morphismRestrict_image_of_restrict_restrict :
    ∀ (P' X S T : Scheme.{0}) (a : X ⟶ P') (W : P'.Opens) (V : W.toScheme.Opens) (q : X ⟶ S)
      (h : P' ⟶ T) (π : S ⟶ T),
      IsPullback ((a ∣_ W) ∣_ V) (((a ∣_ W) ⁻¹ᵁ V).ι ≫ (a ⁻¹ᵁ W).ι ≫ q) (V.ι ≫ W.ι ≫ h) π →
      IsPullback (a ∣_ (W.ι ''ᵁ V)) ((a ⁻¹ᵁ (W.ι ''ᵁ V)).ι ≫ q) ((W.ι ''ᵁ V).ι ≫ h) π := by
  intro P' X S T a W V q h π H
  have e1hom : ((a ⁻¹ᵁ W).ι.isoImage ((a ∣_ W) ⁻¹ᵁ V) ≪≫
      X.isoOfEq (image_morphismRestrict_preimage a W V)).hom ≫ (a ⁻¹ᵁ (W.ι ''ᵁ V)).ι =
      ((a ∣_ W) ⁻¹ᵁ V).ι ≫ (a ⁻¹ᵁ W).ι := by
    simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]
  refine IsPullback.of_iso H
    ((a ⁻¹ᵁ W).ι.isoImage ((a ∣_ W) ⁻¹ᵁ V) ≪≫ X.isoOfEq (image_morphismRestrict_preimage a W V))
    (W.ι.isoImage V) (Iso.refl S) (Iso.refl T) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (W.ι ''ᵁ V).ι]
    simp only [Category.assoc, Scheme.Hom.isoImage_hom_ι, morphismRestrict_ι]
    rw [reassoc_of% e1hom, morphismRestrict_ι_assoc, morphismRestrict_ι]
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [reassoc_of% e1hom]
  · simp only [Iso.refl_hom, Category.comp_id, Scheme.Hom.isoImage_hom_ι_assoc]
  · simp

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackMorphismRestrictImageOfRestrictRestricStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPullback_restrict_image_of_restrict_restrict : ∀ (P' X S T : Scheme.{0}) (a : X ⟶ P') (W : P'.Opens) (V : W.toScheme.Opens) (q : X ⟶ S) (h : P' ⟶ T) (π : S ⟶ T), IsPullback ((a ∣_ W) ∣_ V) (((a ∣_ W) ⁻¹ᵁ V).ι ≫ (a ⁻¹ᵁ W).ι ≫ q) (V.ι ≫ W.ι ≫ h) π → IsPullback (a ∣_ (W.ι ''ᵁ V)) ((a ⁻¹ᵁ (W.ι ''ᵁ V)).ι ≫ q) ((W.ι ''ᵁ V).ι ≫ h) π := by
  first | exact @GlobalTheory.isPullback_morphismRestrict_image_of_restrict_restrict | exact GlobalTheory.isPullback_morphismRestrict_image_of_restrict_restrict | (intros; apply GlobalTheory.isPullback_morphismRestrict_image_of_restrict_restrict <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleRestrictOfUniversallyClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleRestrictOfUniversallyClosed
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem exists_open_etale_restrict_of_universallyClosed : ∀ (X P' T : Scheme.{0}) (a : X ⟶ P') (W1 : P'.Opens) (c : (a ⁻¹ᵁ W1).toScheme ⟶ T) (x : P'), UniversallyClosed a → x ∈ W1 → (∀ z : (a ⁻¹ᵁ W1).toScheme, ((a ⁻¹ᵁ W1).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c)) → ∃ W : P'.Opens, W ≤ W1 ∧ x ∈ W ∧ ∀ hle : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ W1, Etale (X.homOfLE hle ≫ c) := by
  intro X P' T a W1 c x ha hx hloc
  have hEt : IsZariskiLocalAtSource @Etale := HasRingHomProperty.instIsZariskiLocalAtSource
  let S : Set (a ⁻¹ᵁ W1).toScheme := {z | ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c)}
  have hS : IsOpen S := by
    rw [isOpen_iff_forall_mem_open]
    rintro z ⟨U, hz, hU⟩
    exact ⟨U, fun y hy => ⟨U, hy, hU⟩, U.isOpen, hz⟩
  let Z : Set X := ((a ⁻¹ᵁ W1).ι '' S)ᶜ
  have hZ : IsClosed Z := ((a ⁻¹ᵁ W1).ι.isOpenEmbedding.isOpenMap _ hS).isClosed_compl
  have haZ : IsClosed (a '' Z) := a.isClosedMap _ hZ
  refine ⟨W1 ⊓ ⟨(a '' Z)ᶜ, haZ.isOpen_compl⟩, inf_le_left, ⟨hx, ?_⟩, ?_⟩
  · rintro ⟨z, hzZ, hzx⟩
    apply hzZ
    have hz1 : z ∈ a ⁻¹ᵁ W1 := by
      show a z ∈ W1
      rw [hzx]; exact hx
    have hι : (a ⁻¹ᵁ W1).ι ⟨z, hz1⟩ = z := Scheme.Opens.ι_apply _ _
    refine ⟨⟨z, hz1⟩, hloc ⟨z, hz1⟩ ?_, hι⟩
    exact (Scheme.Hom.comp_apply _ _ _).trans (by rw [hι]; exact hzx)
  · intro hle
    have hcov : ∀ w : (a ⁻¹ᵁ (W1 ⊓ ⟨(a '' Z)ᶜ, haZ.isOpen_compl⟩)).toScheme,
        ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, X.homOfLE hle w ∈ U ∧ Etale (U.ι ≫ c) := by
      intro w
      have hw : a w.1 ∉ a '' Z := w.2.2
      have hw' : w.1 ∉ Z := fun h => hw ⟨w.1, h, rfl⟩
      simp only [Z, Set.mem_compl_iff, not_not] at hw'
      obtain ⟨s, ⟨U, hsU, hU⟩, hs⟩ := hw'
      refine ⟨U, ?_, hU⟩
      have : X.homOfLE hle w = s :=
        Subtype.ext ((Scheme.homOfLE_apply hle w).trans (hs.symm.trans (Scheme.Opens.ι_apply _ s)))
      rw [this]; exact hsU
    choose U hwU hU using hcov
    refine IsZariskiLocalAtSource.of_iSup_eq_top (fun w => (X.homOfLE hle) ⁻¹ᵁ (U w)) ?_ fun w => ?_
    · rw [eq_top_iff]
      intro w _
      exact TopologicalSpace.Opens.mem_iSup.mpr ⟨w, hwU w⟩
    · rw [← Category.assoc, ← Scheme.Hom.resLE_comp_ι (X.homOfLE hle) (le_refl ((X.homOfLE hle) ⁻¹ᵁ U w)), Category.assoc]
      haveI : IsOpenImmersion ((X.homOfLE hle).resLE (U w) ((X.homOfLE hle) ⁻¹ᵁ U w) le_rfl) := by
        have h2 : IsOpenImmersion ((X.homOfLE hle).resLE (U w) ((X.homOfLE hle) ⁻¹ᵁ U w) le_rfl ≫ (U w).ι) := by
          rw [Scheme.Hom.resLE_comp_ι]; infer_instance
        exact IsOpenImmersion.of_comp _ (U w).ι
      exact IsZariskiLocalAtSource.comp (hU w) _

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOpenEtaleRestrictOfUniversallyClosedStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_etale_restrict_of_universallyClosed' : ∀ (X P' T : Scheme.{0}) (a : X ⟶ P') (W1 : P'.Opens) (c : (a ⁻¹ᵁ W1).toScheme ⟶ T) (x : P'), UniversallyClosed a → x ∈ W1 → (∀ z : (a ⁻¹ᵁ W1).toScheme, ((a ⁻¹ᵁ W1).ι ≫ a) z = x → ∃ U : (a ⁻¹ᵁ W1).toScheme.Opens, z ∈ U ∧ Etale (U.ι ≫ c)) → ∃ W : P'.Opens, W ≤ W1 ∧ x ∈ W ∧ ∀ hle : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ W1, Etale (X.homOfLE hle ≫ c) := by
  first | exact @GlobalTheory.exists_open_etale_restrict_of_universallyClosed | exact GlobalTheory.exists_open_etale_restrict_of_universallyClosed | (intros; apply GlobalTheory.exists_open_etale_restrict_of_universallyClosed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartProductAtClosedPointClosedFibre
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.EtChart

theorem mvPolynomial_stdSmooth (R : Type) [CommRing R] (n : ℕ) :
    Algebra.IsStandardSmoothOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  haveI : IsEmpty Empty := Empty.instIsEmpty
  let P₀ : Algebra.Presentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := Algebra.Generators.mvPolynomial R (Fin n)
      relation := Empty.elim
      span_range_relation_eq_ker := by
        rw [Algebra.Generators.ker_mvPolynomial]
        simp }
  let P₁ : Algebra.PreSubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₀
      map := Empty.elim
      map_inj := fun a => a.elim }
  let P₂ : Algebra.SubmersivePresentation R (MvPolynomial (Fin n) R) (Fin n) Empty :=
    { __ := P₁
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det]
        simp }
  exact P₂.isStandardSmoothOfRelativeDimension (by simp [Algebra.Presentation.dimension])


set_option backward.isDefEq.respectTransparency false in
theorem affineSpace_smooth (S : Scheme.{0}) (n : ℕ) : Smooth (𝔸(Fin n; S) ↘ S) := by
  have : SmoothOfRelativeDimension n (𝔸(Fin n; S) ↘ S) := by
    have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} n
    refine MorphismProperty.pullback_fst (P := @SmoothOfRelativeDimension n) _ _ ?_
    have := isIso_of_isTerminal specULiftZIsTerminal.{0} terminalIsTerminal (terminal.from _)
    rw [← terminal.comp_from (Spec.map (CommRingCat.ofHom MvPolynomial.C)),
      MorphismProperty.cancel_right_of_respectsIso (P := @SmoothOfRelativeDimension n),
      HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)]
    refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
    exact (RingHom.isStandardSmoothOfRelativeDimension_algebraMap n).2
      (mvPolynomial_stdSmooth (ULift ℤ) n)
  exact SmoothOfRelativeDimension.smooth n _

end GlobalTheory.Mum.EtChart

namespace GlobalTheory.Mum

theorem etale_chart_at_closed_point : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), IsSeparated b → LocallyOfFiniteType b → IsProper a → (∀ V : P'.Opens, Function.Bijective (a.app V).hom) → a ≫ b = X.ι ≫ E.f → Function.Bijective M.π.appTop.hom → Surjective M.π → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X.toScheme), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ X.ι ≫ E.H.ι ≫ G'.hom = p' ≫ X.ι ≫ E.H.ι ≫ G'.hom → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s) → ∃ V : P'.Opens, x ∈ V ∧ Smooth (V.ι ≫ b ≫ PSpace.str R E.N) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (V.ι ≫ b ≫ PSpace.str R E.N) M.π := by
  intro R _ _ _ hR M G' _ _ hG E P' b X a hbsep hblft ha hsec hab hπΓ hπs x hx hx0 hinj hlift
  haveI := hbsep
  haveI := hblft
  haveI := ha
  haveI : IsProper M.π := M.proper
  haveI : IsProper (PSpace.str R E.N) := isProper_str R E.N
  have key : a ≫ b ≫ PSpace.str R E.N = X.ι ≫ E.H.ι ≫ G'.hom ≫ M.π := by
    rw [reassoc_of% hab, E.f_over]
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_mem_fiber_of_geometric_lifting R M.S P' X.toScheme M.π (b ≫ PSpace.str R E.N) a (X.ι ≫ E.H.ι ≫ G'.hom) hπs x hx0 hlift
  have hz0 : M.π (G'.hom (E.H.ι (X.ι z))) = closedPoint R := by
    have h1 := congrArg (fun f : X.toScheme ⟶ Sp R => f z) key
    simp only [Scheme.Hom.comp_apply] at h1
    rw [← h1, hz]
    simpa [Scheme.Hom.comp_apply] using hx0
  obtain ⟨y, hy⟩ := (GlobalTheory.T.closedPoint_range_eq_fixedGroup_image R M.S M.π G' E).1 (X.ι z) hz0
  have hyb : E.j y = b x := by
    rw [← hy, ← hz]
    have h1 := congrArg (fun f : X.toScheme ⟶ PSpace R E.N => f z) hab
    simpa [Scheme.Hom.comp_apply] using h1.symm
  obtain ⟨W0, g, τ0, O, e, hyO, hOW, hτ0, he, he2, he3⟩ := GlobalTheory.T.exists_etale_coordinates_through_immersion R E.N E.Y E.smooth E.j E.imm E.j_over y
  have hxW1 : x ∈ b ⁻¹ᵁ W0 := by
    show b x ∈ W0
    rw [← hyb]; exact hOW hyO
  let τ1 : (b ⁻¹ᵁ W0).toScheme ⟶ 𝔸(Fin g; Sp R) := (b ∣_ W0) ≫ τ0
  have hτ1 : τ1 ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = (b ⁻¹ᵁ W0).ι ≫ b ≫ PSpace.str R E.N := by
    simp only [τ1, Category.assoc, hτ0, morphismRestrict_ι_assoc]
  let c1 : (a ⁻¹ᵁ (b ⁻¹ᵁ W0)).toScheme ⟶ pullback (𝔸(Fin g; Sp R) ↘ Sp R) M.π :=
    pullback.lift ((a ∣_ (b ⁻¹ᵁ W0)) ≫ τ1) ((a ⁻¹ᵁ (b ⁻¹ᵁ W0)).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (by
      rw [Category.assoc, hτ1, morphismRestrict_ι_assoc, key]
      simp only [Category.assoc])
  have hF := GlobalTheory.T.coordinateMap_etale_near_properFibre R hR M G' hG E P' b X a hab x y hyb hx0 W0 g τ0 O e hyO hOW hτ0 he he2 he3 c1
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
  obtain ⟨W, hWW1, hxW, hWet⟩ := GlobalTheory.T.exists_open_etale_restrict_of_universallyClosed' X.toScheme P' _ a (b ⁻¹ᵁ W0) c1 x inferInstance hxW1 hF
  have hle : a ⁻¹ᵁ W ≤ a ⁻¹ᵁ (b ⁻¹ᵁ W0) := fun _ hp => hWW1 hp
  let c := X.toScheme.homOfLE hle ≫ c1
  let τ := P'.homOfLE hWW1 ≫ τ1
  let U : Over (Sp R) := Over.mk (W.ι ≫ b ≫ PSpace.str R E.N)
  have hsq : X.toScheme.homOfLE hle ≫ (a ∣_ (b ⁻¹ᵁ W0)) = (a ∣_ W) ≫ P'.homOfLE hWW1 := by
    rw [← cancel_mono (b ⁻¹ᵁ W0).ι, Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc,
      Category.assoc, Scheme.homOfLE_ι, morphismRestrict_ι]
  obtain ⟨x', hx'⟩ : x ∈ Set.range W.ι := by rw [Scheme.Opens.range_ι]; exact hxW
  have hLFT : LocallyOfFiniteType U.hom := by
    show LocallyOfFiniteType (W.ι ≫ b ≫ PSpace.str R E.N); infer_instance
  have hSep : IsSeparated U.hom := by
    show IsSeparated (W.ι ≫ b ≫ PSpace.str R E.N); infer_instance
  have hPr : IsProper (a ∣_ W) := inferInstance
  have hSec : ∀ V : U.left.Opens, Function.Bijective ((a ∣_ W).app V).hom := by
    intro V
    rw [morphismRestrict_app]
    exact (ConcreteCategory.bijective_of_isIso (X.toScheme.presheaf.map (eqToHom (image_morphismRestrict_preimage a W V)).op)).comp (hsec (W.ι ''ᵁ V))
  have hτ : τ ≫ (𝔸(Fin g; Sp R) ↘ Sp R) = U.hom := by
    simp only [τ, Category.assoc, hτ1]
    rw [Scheme.homOfLE_ι_assoc]
    rfl
  have hc1 : c ≫ pullback.fst _ _ = (a ∣_ W) ≫ τ := by
    simp only [c, τ, c1, Category.assoc, pullback.lift_fst]
    rw [← Category.assoc, hsq, Category.assoc]
  have hc2 : c ≫ pullback.snd _ _ = (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom := by
    simp only [c, c1, Category.assoc, pullback.lift_snd]
    rw [Scheme.homOfLE_ι_assoc]
  have hcl : IsClosed ({x'} : Set U.left) := by
    have : ({x'} : Set U.left) = W.ι ⁻¹' {x} := by
      ext p
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      exact ⟨fun h => h ▸ hx', fun h => W.ι.isOpenEmbedding.injective (h.trans hx'.symm)⟩
    rw [this]
    exact hx.preimage W.ι.continuous
  have hx'0 : U.hom x' = closedPoint R := by
    show (W.ι ≫ b ≫ PSpace.str R E.N) x' = closedPoint R
    simpa [Scheme.Hom.comp_apply, hx'] using hx0
  have hrange : ∀ (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ U.left), Set.range ξ = {x'} → Set.range (ξ ≫ W.ι) = {x} := by
    intro Ω _ ξ hr
    rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
    erw [hr]
    rw [Set.image_singleton, hx']
  have hinj' : ∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ (a ⁻¹ᵁ W).toScheme), Set.range (p ≫ (a ∣_ W)) = {x'} →
      p ≫ (a ∣_ W) = p' ≫ (a ∣_ W) → p ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom = p' ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom →
      p = p' := by
    intro Ω _ p p' hr he hb
    have hr' : Set.range ((p ≫ (a ⁻¹ᵁ W).ι) ≫ a) = {x} := by
      rw [Category.assoc, ← morphismRestrict_ι, ← Category.assoc]
      exact hrange Ω _ hr
    have h2 : (p ≫ (a ⁻¹ᵁ W).ι) ≫ a = (p' ≫ (a ⁻¹ᵁ W).ι) ≫ a := by
      simp only [Category.assoc, ← morphismRestrict_ι]
      rw [reassoc_of% he]
    have := hinj Ω (p ≫ (a ⁻¹ᵁ W).ι) (p' ≫ (a ⁻¹ᵁ W).ι) hr' h2 (by simpa only [Category.assoc] using hb)
    exact (cancel_mono _).1 this
  have hlift' : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ U.left) (s : Sp Ω ⟶ M.S), Set.range ξ = {x'} →
      ξ ≫ U.hom = s ≫ M.π → ∃ p : Sp Ω ⟶ (a ⁻¹ᵁ W).toScheme, p ≫ (a ∣_ W) = ξ ∧ p ≫ (a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
    intro Ω _ _ ξ s hr hs
    obtain ⟨p, hp1, hp2⟩ := hlift Ω (ξ ≫ W.ι) s (hrange Ω ξ hr) (by rw [Category.assoc]; exact hs)
    have hsub : Set.range p.base ⊆ Set.range (a ⁻¹ᵁ W).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      show a (p t) ∈ W
      have h3 : a (p t) = W.ι (ξ t) := by
        have h4 := congrArg (fun f : Sp Ω ⟶ P' => f t) hp1
        simpa [Scheme.Hom.comp_apply] using h4
      rw [h3]
      have h5 := Set.mem_range_self (f := W.ι) (ξ t)
      rwa [Scheme.Opens.range_ι] at h5
    refine ⟨IsOpenImmersion.lift (a ⁻¹ᵁ W).ι p hsub, ?_, ?_⟩
    · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, IsOpenImmersion.lift_fac_assoc, hp1]
    · rw [IsOpenImmersion.lift_fac_assoc]; exact hp2
  obtain ⟨V, hxV, hVet, hVpb⟩ := GlobalTheory.T.etaleCoordinates_descend_along_proper_map R hR M.S (a ⁻¹ᵁ W).toScheme M.π U (a ∣_ W)
    ((a ⁻¹ᵁ W).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) g τ c M.proper hπs hπΓ hLFT hSep hPr hSec hτ hc1 hc2 (hWet hle)
    x' hcl hx'0 hinj' hlift'
  refine ⟨W.ι ''ᵁ V, ⟨x', hxV, hx'⟩, ?_, ?_⟩
  · haveI : Etale (V.ι ≫ τ) := hVet
    haveI : Smooth (𝔸(Fin g; Sp R) ↘ Sp R) := GlobalTheory.Mum.EtChart.affineSpace_smooth (Sp R) g
    have e1 : (W.ι ''ᵁ V).ι ≫ b ≫ PSpace.str R E.N =
        (W.ι.isoImage V).inv ≫ (V.ι ≫ τ) ≫ (𝔸(Fin g; Sp R) ↘ Sp R) := by
      rw [Category.assoc, hτ, Iso.eq_inv_comp, ← Category.assoc, Scheme.Hom.isoImage_hom_ι, Category.assoc]
      rfl
    rw [e1]
    infer_instance
  · exact GlobalTheory.T.isPullback_restrict_image_of_restrict_restrict P' X.toScheme M.S (Sp R) a W V (X.ι ≫ E.H.ι ≫ G'.hom) (b ≫ PSpace.str R E.N) M.π hVpb

end GlobalTheory.Mum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleChartProductAtClosedPointClosedFibreStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_open_nbhd_isPullback_at_closedPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (E : Emb M.π G') (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), IsSeparated b → LocallyOfFiniteType b → IsProper a → (∀ V : P'.Opens, Function.Bijective (a.app V).hom) → a ≫ b = X.ι ≫ E.f → Function.Bijective M.π.appTop.hom → Surjective M.π → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → (∀ (Ω : Type) [Field Ω] (p p' : Sp Ω ⟶ X.toScheme), Set.range (p ≫ a) = {x} → p ≫ a = p' ≫ a → p ≫ X.ι ≫ E.H.ι ≫ G'.hom = p' ≫ X.ι ≫ E.H.ι ≫ G'.hom → p = p') → (∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s) → ∃ V : P'.Opens, x ∈ V ∧ Smooth (V.ι ≫ b ≫ PSpace.str R E.N) ∧ IsPullback (a ∣_ V) ((a ⁻¹ᵁ V).ι ≫ X.ι ≫ E.H.ι ≫ G'.hom) (V.ι ≫ b ≫ PSpace.str R E.N) M.π := by
  first | exact @GlobalTheory.Mum.etale_chart_at_closed_point | exact GlobalTheory.Mum.etale_chart_at_closed_point | (intros; apply GlobalTheory.Mum.etale_chart_at_closed_point <;> assumption)
end
