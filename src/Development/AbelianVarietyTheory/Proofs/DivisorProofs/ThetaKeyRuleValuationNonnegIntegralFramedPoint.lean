module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusExtensionPointActionPeriodValueFractionFiel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulipointLiftToFinerLevelCompleteDVR

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleIsUnitAtBadLevelPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedDataCompleteDVRExtension
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedDataCompleteDVRExtension
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

noncomputable section

namespace GlobalTheory.FramedExt

theorem eSec_hom {S : Scheme.{0}} (X : Over S) [GrpObj X] : eSec X ≫ X.hom = 𝟙 _ := by
  simp [eSec]

theorem dualMapR_comp_algebraMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (Chart.dualMapR f).comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := by
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_ext {R R' : Type} [CommRing R] [CommRing R'] (F₁ F₂ : DualNumber R →+* DualNumber R')
    (h : ∀ a : R, F₁ (algebraMap R (DualNumber R) a) = F₂ (algebraMap R (DualNumber R) a))
    (hε : F₁ DualNumber.eps = F₂ DualNumber.eps) : F₁ = F₂ := by
  refine RingHom.ext fun x => ?_
  have hx : x = algebraMap R (DualNumber R) x.fst + algebraMap R (DualNumber R) x.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  rw [hx, map_add (f := _), map_add (f := _), map_mul, map_mul, h, h, hε]

theorem generates_of_flat {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {R R₂ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing R₂] [IsDomain R₂] (φ : R →+* R₂) (hφ : Function.Injective φ) (G : SAB H (Sp R)) (G₂ : SAB H (Sp R₂)) (m : SABMap G₂ G (spMap φ)) (wI : G₂.PP.L.Iso (G.PP.L.pull m.φ)) (hwI : LB.Gen.IsGen wI) (θ : G.PP.L.Sec) (θ₂ : G₂.PP.L.Sec) (hθ : IsoMaps wI θ₂ (thfPull G.PP.L m.φ θ)) : Generates (X := G.G) θ → Generates (X := G₂.G) θ₂ := by
  intro hgen
  letI := φ.toAlgebra
  have : FaithfulSMul R R₂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hφ
  have : Module.Flat R R₂ := inferInstance
  haveI : IsSeparated G.G.hom := G.semi.separated
  haveI : QuasiCompact G.G.hom := G.semi.quasiCompact
  haveI : CompactSpace G.G.left := QuasiCompact.compactSpace_of_compactSpace G.G.hom
  have hinter : ∀ U W : G.G.left.Opens, IsAffineOpen U → IsAffineOpen W → IsAffineOpen (U ⊓ W) :=
    fun U W hU hW => isAffineHom_diagonal_iff.mp (inferInstance : IsAffineHom (pullback.diagonal G.G.hom)) ⊤
      (isAffineOpen_top _) U le_top W le_top hU hW
  have Hpb : IsPullback m.φ G₂.G.hom G.G.hom (Spec.map (CommRingCat.ofHom (algebraMap R R₂))) := m.cart.1
  exact fun s' => ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.flatBC_iso G.G.hom G₂.G.hom m.φ Hpb hinter G.PP.L G.PP.isLB θ hgen
    G₂.PP.L G₂.PP.isLB wI hwI θ₂ _ hθ (fun _ _ => rfl) s'

theorem isFibreOf_trans {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (hL : L.IsLB) (rig : (L.pull (eSec G)).Gen) (θ : L.Sec) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (k : KeyIn R') (k' : KeyIn R'') (f : R →+* R') (g : R' →+* R'') : IsFibreOf k G L rig θ w f → KeyPB k' k g → IsFibreOf k' G L rig θ w (g.comp f) := by
  intro H H'
  obtain ⟨φ, he, w₀, hg, F, hp, hw, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨φ', he', w', hg', F', hp', hw', hr', hs', hF', hε', hv'⟩ := H'
  have g₀ := (isGen_iff w₀).1 hw
  have g' := (isGen_iff w').1 hw'
  obtain ⟨w'', T⟩ := exists_comp k.P.isLB w₀ w' g₀ g' hL k'.P.isLB
  have he'' : eSec k'.P.A ≫ φ' ≫ φ = spMap (g.comp f) ≫ eSec G := by
    rw [← Category.assoc, he', Category.assoc, he, spMap_comp, Category.assoc]
  refine ⟨φ' ≫ φ, he'', w'', hg'.trans hg, F'.comp F, (hp'.comp hp).congr (spMap_comp f g).symm rfl,
    (isGen_iff w'').2 (T.pgen_comp k.P.isLB g₀ g'), ?_, ?_, fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff w₀ _ (fun _ => eSec G) _ k.rig rig (spMap f) _
      (rigPull_le φ (spMap f) he L) (fun _ => rfl)).1 hr
    have r₁ := (maps_iff w' _ (fun _ => eSec k.P.A) _ k'.rig k.rig (spMap g) _
      (rigPull_le φ' (spMap g) he' k.P.L) (fun _ => rfl)).1 hr'
    have r₂ := T.pmaps_comp k.P.isLB (fun _ => he') r₀ r₁
    rw [← spMap_comp] at r₂
    exact (maps_iff w'' _ (fun _ => eSec G) _ k'.rig rig (spMap (g.comp f)) _
      (rigPull_le (φ' ≫ φ) (spMap (g.comp f)) he'' L) (fun _ => rfl)).2 r₂
  · refine GlobalTheory.KeyPow.appLE_eq_of_stalk w'' θ k'.th fun z j k₀ hj hk => ?_
    obtain ⟨i, hi⟩ := exists_chart k.P.isLB (φ' z)
    have a := GlobalTheory.KeyComp.stalk_of_appLE_eq w₀ θ k.th hs (𝟙 _ ≫ φ') z j i hj hi
    have b := GlobalTheory.KeyComp.stalk_of_appLE_eq w' k.th k'.th hs' (𝟙 _) z i k₀ hi hk
    rw [T _ (𝟙 _) z j i k₀ hj hi hk, ← Category.assoc, a, b, Units.val_mul, _root_.mul_assoc]
  · rw [RingHom.comp_apply, hF, hF', RingHom.comp_apply]
  · rw [RingHom.comp_apply, hε, hε']
  · rw [← Category.assoc, hv', Category.assoc, hv, spMap_comp, Category.assoc]
    rfl

theorem isFibreOf_descend {R R₂ K : Type} [CommRing R] [CommRing R₂] [CommRing K] (φ : R →+* R₂) (f : R₂ →+* K) (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (G₂ : Over (Sp R₂)) [GrpObj G₂] [IsCommMonObj G₂] (L : LB G.left) (hL : L.IsLB) (rig : (L.pull (eSec G)).Gen) (L₂ : LB G₂.left) (hL₂ : L₂.IsLB) (rig₂ : (L₂.pull (eSec G₂)).Gen) (ψ : G₂.left ⟶ G.left) (hψ : IsGrpPullback G₂ G (spMap φ) ψ) (he : eSec G₂ ≫ ψ = spMap φ ≫ eSec G) (wI : L₂.Iso (L.pull ψ)) (hwI : LB.Gen.IsGen wI) (hrig : LB.Gen.Maps (LB.linCombIso wI (fun _ => eSec G₂) fun _ => 1) rig₂ (rigPullOf ψ (spMap φ) he L rig)) (θ : L.Sec) (θ₂ : L₂.Sec) (hθ : IsoMaps wI θ₂ (thfPull L ψ θ)) {n : ℕ} (w : Fin n → (epsR R ⟶ G)) (w₂ : Fin n → (epsR R₂ ⟶ G₂)) (hw : ∀ i, (w₂ i).left ≫ ψ = spMap (Chart.dualMapR φ) ≫ (w i).left) (k : KeyIn K) : IsFibreOf k G L rig θ w (f.comp φ) → IsFibreOf k G₂ L₂ rig₂ θ₂ w₂ f := by
  intro H
  obtain ⟨φk, hek, e, hg, F, hp, hgen, hr, hs, hF, hε, hv⟩ := H
  obtain ⟨ψ₂, hfac, hbase⟩ : ∃ ψ₂ : k.P.A.left ⟶ G₂.left, ψ₂ ≫ ψ = φk ∧ ψ₂ ≫ G₂.hom = k.P.A.hom ≫ spMap f :=
    ⟨hψ.1.lift φk (k.P.A.hom ≫ spMap f) (by rw [hp.1.w, spMap_comp, Category.assoc]),
      hψ.1.lift_fst _ _ _, hψ.1.lift_snd _ _ _⟩
  subst hfac
  have hp₂ : IsGrpPullback k.P.A G₂ (spMap f) ψ₂ := hψ.cancel (hp.congr (spMap_comp φ f) rfl) hbase
  have he₂ : eSec k.P.A ≫ ψ₂ = spMap f ≫ eSec G₂ := by
    apply hψ.1.hom_ext
    · rw [Category.assoc, hek, Category.assoc, he, spMap_comp, Category.assoc]
    · rw [Category.assoc, hbase, ← Category.assoc, eSec_hom, Category.assoc, eSec_hom]
      simp
  have gI := (isGen_iff wI).1 hwI
  have g₀ := (isGen_iff e).1 hgen
  obtain ⟨e₂, T⟩ := exists_cancel hL wI e gI g₀ hL₂ k.P.isLB
  have hFe : F = (Chart.dualMapR f).comp (Chart.dualMapR φ) := dual_ext _ _ (fun a => by
      simp only [hF, RingHom.comp_apply]
      ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl])
    (by rw [hε]; ext <;> simp [Chart.dualMapR])
  refine ⟨ψ₂, he₂, e₂, hg, Chart.dualMapR f, hp₂, (isGen_iff e₂).2 (T.pgen_cancel hL gI g₀), ?_, ?_,
    fun a => ?_, ?_, fun i => ?_⟩
  · have r₀ := (maps_iff wI _ (fun _ => eSec G) _ rig₂ rig (spMap φ) _
      (rigPull_le ψ (spMap φ) he L) (fun _ => rfl)).1 hrig
    have r'' := (maps_iff e _ (fun _ => eSec G) _ k.rig rig (spMap (f.comp φ)) _
      (rigPull_le (ψ₂ ≫ ψ) (spMap (f.comp φ)) hek L) (fun _ => rfl)).1 hr
    rw [spMap_comp] at r''
    have r₂ := T.pmaps_cancel hL (fun _ => he₂) r₀ r''
    exact (maps_iff e₂ _ (fun _ => eSec G₂) _ k.rig rig₂ (spMap f) _
      (rigPull_le ψ₂ (spMap f) he₂ L₂) (fun _ => rfl)).2 r₂
  · have hθ' : ∀ (j : (L.pull ψ).ι) (i : L₂.ι) (hle : (L.pull ψ).U j ⊓ L₂.U i ≤ ψ ⁻¹ᵁ L.U (j PUnit.unit)),
        (Scheme.Hom.appLE ψ (L.U (j PUnit.unit)) ((L.pull ψ).U j ⊓ L₂.U i) hle).hom (θ.f (j PUnit.unit)) =
          (show Γ(G₂.left, (L.pull ψ).U j ⊓ L₂.U i) from (wI.s (j, i)).val) * resG _ inf_le_right (θ₂.f i) := by
      intro j i hle
      refine Eq.trans ?_ (hθ j i)
      dsimp only [thfPull]
      first
        | (erw [Scheme.Hom.appLE_map])
        | (simp only [Scheme.Hom.appLE_map])
        | (rw [← Scheme.Hom.appLE_map ψ _ (homOfLE inf_le_left).op]; rfl)
    refine GlobalTheory.KeyPow.appLE_eq_of_stalk e₂ θ₂ k.th fun z j k₀ hj hk => ?_
    obtain ⟨jL, hjL⟩ := exists_chart hL (ψ (ψ₂ z))
    have a := GlobalTheory.KeyComp.stalk_of_appLE_eq e θ k.th hs (𝟙 _) z jL k₀ hjL hk
    have b := GlobalTheory.KeyComp.stalk_of_appLE_eq wI θ θ₂ hθ' (𝟙 _ ≫ ψ₂) z jL j hjL hj
    rw [Category.assoc] at b
    rw [T _ (𝟙 _) z jL j k₀ hjL hj hk, b, Units.val_mul, _root_.mul_assoc] at a
    exact (Units.mul_right_inj _).1 a
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]
  · apply hψ.1.hom_ext
    · rw [Category.assoc, hv i, Category.assoc, hw, ← Category.assoc, hFe, spMap_comp]
    · rw [Category.assoc, hbase, ← Category.assoc, Over.w (k.v i), Category.assoc, Over.w (w₂ (Fin.cast hg i))]
      simp only [epsR, Over.mk_hom]
      rw [← spMap_comp, ← spMap_comp, dualMapR_comp_algebraMap]

theorem exists_framed_ext : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V), (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ (G' : SAB H (Sp T'.V)) (t'' : SAB H (Sp T'.Fr)) (_ : SABMap t'' t' (spMap iT)) (_ : SABMap t'' G' (spMap (algebraMap T'.V T'.Fr))) (n' : ℕ) (w' : Fin n' → (epsR T'.V ⟶ G'.G)) (θ' : G'.PP.L.Sec) (k' : KeyIn T'.Fr), IsLieBasis w' ∧ Generates (X := G'.G) θ' ∧ IsFibreOf k' G'.G G'.PP.L G'.PP.rig θ' w' (algebraMap T'.V T'.Fr) ∧ KeyPB k' k iT := by
  intro E _ _ _ H T T' iT φ hφ G t' m2 n w hw θ hθ k hk
  have hφ' : (algebraMap T'.V T'.Fr).comp φ = iT.comp (algebraMap T.V T.Fr) := RingHom.ext hφ
  have hsq : spMap iT ≫ spMap (algebraMap T.V T.Fr) = spMap (algebraMap T'.V T'.Fr) ≫ spMap φ := by
    rw [← spMap_comp, ← spMap_comp, hφ']
  have tr : ∀ {S S' : Scheme.{0}} {s : SAB H S} {s' : SAB H S'} {f g : S' ⟶ S}, f = g → SABMap s' s f →
      Nonempty (SABMap s' s g) := by
    intro S S' s s' f g h m
    subst h
    exact ⟨m⟩
  obtain ⟨G₂, ⟨m⟩⟩ : ∃ G₂ : SAB H (Sp T'.V), Nonempty (SABMap G₂ G (spMap φ)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap φ) G
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨t₂, ⟨p⟩⟩ : ∃ t₂ : SAB H (Sp T'.Fr), Nonempty (SABMap t₂ t' (spMap iT)) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull (spMap iT) t'
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨a₂, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m2 p
  obtain ⟨b₂⟩ := tr hsq a₂
  obtain ⟨m2', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m b₂
  obtain ⟨w', hw', hww⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ φ G.G G₂.G m.φ m.cart G.semi.smooth n w hw
  obtain ⟨k', hk'⟩ := GlobalTheory.KeyPow.exists_keyPB_ring k iT
  obtain ⟨wI, hwI, hrI, -⟩ := m.lin
  obtain ⟨θ₂, hθ₂⟩ := GlobalTheory.ArcQ.NormalForm.exists_isoMaps wI hwI G.PP.isLB G₂.PP.isLB (thfPull G.PP.L m.φ θ)
  have he : eSec G₂.G ≫ m.φ = spMap φ ≫ eSec G.G := m.cm.e_comm.trans (congrArg (· ≫ eSec G.G) m.base)
  have hr : ∀ (e : Sp T'.V ⟶ Sp T.V) (_ : m.cm.e = e) (he : eSec G₂.G ≫ m.φ = e ≫ eSec G.G),
      rigPullOf m.φ e he G.PP.L G.PP.rig = m.cm.rigPull G.PP.L G.PP.rig := by
    rintro _ rfl _
    rfl
  have hrig : LB.Gen.Maps (LB.linCombIso wI (fun _ => eSec G₂.G) fun _ => 1) G₂.PP.rig
      (rigPullOf m.φ (spMap φ) he G.PP.L G.PP.rig) := by
    rw [hr _ m.base he]; exact hrI
  have h1 := isFibreOf_trans G.G G.PP.L G.PP.isLB G.PP.rig θ w k k' (algebraMap T.V T.Fr) iT hk hk'
  rw [← hφ'] at h1
  have hinj : Function.Injective φ := fun a b hab => IsFractionRing.injective T.V T.Fr
    (iT.injective (by rw [← hφ a, ← hφ b, hab]))
  exact ⟨G₂, t₂, p, m2', n, w', θ₂, k', hw', generates_of_flat φ hinj G G₂ m wI hwI θ θ₂ hθ₂ hθ,
    isFibreOf_descend φ (algebraMap T'.V T'.Fr) G.G G₂.G G.PP.L G.PP.isLB G.PP.rig G₂.PP.L G₂.PP.isLB G₂.PP.rig m.φ
      m.cart he wI hwI hrig θ θ₂ hθ₂ w w' hww k' h1, hk'⟩

end GlobalTheory.FramedExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedDataCompleteDVRExtensionStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralFramedData_completeDVR_extension : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (T T' : CDVR) (iT : T.Fr →+* T'.Fr) (φ : T.V →+* T'.V), (∀ a : T.V, algebraMap T'.V T'.Fr (φ a) = iT (algebraMap T.V T.Fr a)) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ (G' : SAB H (Sp T'.V)) (t'' : SAB H (Sp T'.Fr)) (_ : SABMap t'' t' (spMap iT)) (_ : SABMap t'' G' (spMap (algebraMap T'.V T'.Fr))) (n' : ℕ) (w' : Fin n' → (epsR T'.V ⟶ G'.G)) (θ' : G'.PP.L.Sec) (k' : KeyIn T'.Fr), IsLieBasis w' ∧ Generates (X := G'.G) θ' ∧ IsFibreOf k' G'.G G'.PP.L G'.PP.rig θ' w' (algebraMap T'.V T'.Fr) ∧ KeyPB k' k iT := by
  first | exact @GlobalTheory.FramedExt.exists_framed_ext | exact GlobalTheory.FramedExt.exists_framed_ext | (intros; apply GlobalTheory.FramedExt.exists_framed_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleIsUnitAtBadLevelPlace
noncomputable section

namespace GlobalTheory.KeyBadPrime

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels

theorem key_unit_bad : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (κ : KeyRule), IsKeyRule κ → 1 ≤ Dw.p + Dw.q → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → ¬ l.GoodAt p → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' Xo.univ.t x → SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  intro E _ _ _ H Dw l Xo c κ hκ hpq la p hp hpl hbad T io e ho x hxs G t' m1 m2 n w hw θ hθ k hk
  obtain ⟨l₂, hd, hA, hg₂⟩ := GlobalTheory.T.exists_goodLevel_multiple_same_adelicPart E H l
  obtain ⟨Xo₂⟩ := GlobalTheory.Moduli.moduli_scheme_exists E H Dw l₂ hpq
  obtain ⟨c₂, la₂, T', iT, φ, e', io₂, e₂, x₂, r, m, he', hv, hφ, ho₂, hxs₂, hx₂⟩ :=
    GlobalTheory.T.modulipoint_lift_to_finerLevel_completeDVR E H Dw l l₂ Xo Xo₂ c hpq hd hA la T io e ho x hxs
  obtain ⟨G', t'', mt, m2', n', w', θ', k', hw', hθ', hk', hpb⟩ := GlobalTheory.T.exists_integralFramedData_completeDVR_extension E H T T' iT φ hφ G t' m2 n w hw θ hθ k hk
  obtain ⟨a₁, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m1 mt
  obtain ⟨m1', -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m (PullbackSections.sabMapCast a₁ hx₂.symm)
  obtain ⟨u', hu'⟩ := GlobalTheory.KeyIntegralVal.key_unit hκ hpq hg₂ ho₂ hxs₂ m1' m2' hw' hθ' k' hk'
  have h1 : (κ T'.Fr k' : T'.Fr) = iT (κ T.Fr k : T.Fr) := hκ.2.1 T.Fr T'.Fr iT k k' hpb
  set a : T.Fr := (κ T.Fr k : T.Fr) with ha
  have ha0 : a ≠ 0 := Units.ne_zero _
  have hu0 : ∀ (V : CDVR) (u : V.Vˣ), vV V.V (algebraMap V.V V.Fr u) = 0 := by
    intro V u
    have hne : ∀ u : V.Vˣ, algebraMap V.V V.Fr u ≠ 0 := fun u => (u.isUnit.map _).ne_zero
    have nn : ∀ b : V.V, 0 ≤ vV V.V (algebraMap V.V V.Fr b) := fun b => by
      by_cases h : algebraMap V.V V.Fr b = 0
      · simp [h, vV]
      have := (WithZero.log_le_log (valV_ne_zero (V := V.V) h) one_ne_zero).2
        (IsDedekindDomain.HeightOneSpectrum.valuation_le_one _ b)
      rw [WithZero.log_one] at this
      rw [vV]; omega
    have h := vV_mul (V := V.V) (hne u) (hne u⁻¹)
    rw [← map_mul, Units.mul_inv, map_one, show vV V.V (1 : V.Fr) = 0 by simp [vV]] at h
    have := nn u
    have := nn (u⁻¹ : V.Vˣ)
    omega
  have hva : vV T.V a = 0 := by
    have h2 := hv a
    rw [← h1, hu', hu0] at h2
    have : (0 : ℤ) < e' := by exact_mod_cast he'
    nlinarith
  have hvi : vV T.V a⁻¹ = 0 := by
    have h := vV_mul (V := T.V) ha0 (inv_ne_zero ha0)
    rw [mul_inv_cancel₀ ha0, show vV T.V (1 : T.Fr) = 0 by simp [vV], hva] at h
    omega
  obtain ⟨b, hb⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) hva.ge
  obtain ⟨b', hb'⟩ := Formalism.L2.PjFree.mem_range_of_vV_nonneg (V := T.V) hvi.ge
  have hbb : b * b' = 1 := IsFractionRing.injective T.V T.Fr (by rw [map_mul, hb, hb', mul_inv_cancel₀ ha0, map_one])
  exact ⟨⟨b, b', hbb, by rw [mul_comm]; exact hbb⟩, hb.symm⟩

end GlobalTheory.KeyBadPrime
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleIsUnitAtBadLevelPlaceStatement
open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_isUnit_at_bad_level_place : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (κ : KeyRule), IsKeyRule κ → 1 ≤ Dw.p + Dw.q → ∀ (la : HeightOneSpectrum (𝓞 c.F)) (p : ℕ), p.Prime → (p : 𝓞 c.F) ∈ la.asIdeal → ¬ l.GoodAt p → ∀ (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la T.V io e → ∀ (x : Sp T.Fr ⟶ Xo.X), x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom) → ∀ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)), SABMap t' Xo.univ.t x → SABMap t' G (spMap (algebraMap T.V T.Fr)) → ∀ (n : ℕ) (w : Fin n → (epsR T.V ⟶ G.G)), IsLieBasis w → ∀ (θ : G.PP.L.Sec), Generates (X := G.G) θ → ∀ (k : KeyIn T.Fr), IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr) → ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  first | exact @GlobalTheory.KeyBadPrime.key_unit_bad | exact GlobalTheory.KeyBadPrime.key_unit_bad | (intros; apply GlobalTheory.KeyBadPrime.key_unit_bad <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValuationNonnegIntegralFramedPoint
noncomputable section

namespace GlobalTheory.KeyValAny

section Model

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem exists_model_at (Xo : Moduli Dw l) (c : Coeff l) (hpq : 1 ≤ Dw.p + Dw.q)
    (la : HeightOneSpectrum (𝓞 c.F)) {p : ℕ} (hp : p.Prime) (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (hgp : l.GoodAt p) :
    ∃ (W : ValuationSubring ℂ) (Y : Model Xo c (c.V W).subtype),
      c.V W = (la.valuation c.F).valuationSubring ∧ Y.LevelStructureConditions p ∧ Y.N3 ∧ Y.N4 ∧ Y.SplitFibres := by
  classical
  obtain ⟨W, hWe, hWn⟩ := GlobalTheory.Reg.exists_valuationSubring_comap_eq_nonunits c.F.val.toRingHom
    (la.valuation c.F).valuationSubring
  have hpU : (p : c.F) ∈ (la.valuation c.F).valuationSubring.nonunits := by
    rw [ValuationSubring.mem_nonunits_iff,
      ← (Valuation.isEquiv_valuation_valuationSubring (la.valuation c.F)).lt_one_iff_lt_one]
    have := (la.valuation_lt_one_iff_mem (K := c.F) (p : 𝓞 c.F)).2 hpl
    simpa using this
  have hW : (p : ℂ) ∈ W.nonunits := by simpa using hWn _ hpU
  have key : ∀ X : ∀ l : Level H, Moduli Dw l, ∃ Y : Model (X l) c (c.V W).subtype,
      Y.LevelStructureConditions p ∧ Y.N3 ∧ Y.N4 ∧ Y.SplitFibres := fun X => by
    obtain ⟨Y, hY, -⟩ := GlobalTheory.partI_closed.2 E H Dw hpq X
    obtain ⟨h1, h2⟩ := hY p W hp hW
    obtain ⟨h3, h4, h5⟩ := h2 ⟨l, c, hgp⟩
    exact ⟨_, h1.1 ⟨l, c, hgp⟩, h4, h5, h3⟩
  have h := key (Function.update (fun l' => Classical.choice (GlobalTheory.Moduli.moduli_scheme_exists E H Dw l' hpq)) l Xo)
  rw [Function.update_self] at h
  obtain ⟨Y, hY⟩ := h
  exact ⟨W, Y, hWe, hY⟩

theorem key_unit_at {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q)
    {la : HeightOneSpectrum (𝓞 c.F)} {p : ℕ} (hp : p.Prime) (hpl : (p : 𝓞 c.F) ∈ la.asIdeal) (hgp : l.GoodAt p)
    {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    {x : Sp T.Fr ⟶ Xo.X} (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) {n : ℕ} {w : Fin n → (epsR T.V ⟶ G.G)} (hw : IsLieBasis w)
    {θ : G.PP.L.Sec} (hθ : Generates (X := G.G) θ) (k : KeyIn T.Fr)
    (hk : IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr)) :
    ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  obtain ⟨W, Y, hW, h2, h3, h4, h5⟩ := exists_model_at Xo c hpq la hp hpl hgp
  obtain ⟨b, hb⟩ := GlobalTheory.EtaVal.exists_base_map_of_overLa (β := (c.V W).subtype)
    (fun a => (Valuation.mem_valuationSubring_iff _ _).1 (hW ▸ a.2)) T io e ho
  have hcond : x ≫ Xo.s = spMap io ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [hxs, GlobalTheory.EtaVal.spMap_comp_spMap]
  let z : Sp T.Fr ⟶ Xo.XF c := pullback.lift x (spMap io) hcond
  have hzs : z ≫ pullback.snd _ _ = spMap io := pullback.lift_snd _ _ _
  have hzf : z ≫ pullback.fst _ _ = x := pullback.lift_fst _ _ _
  have hx : z ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b := by
    show z ≫ (Y.jQ ≫ pullback.fst _ _) ≫ Y.s = _
    rw [Category.assoc, pullback.condition, ← Category.assoc Y.jQ, Y.jQ_over, ← Category.assoc, hzs]
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hb]
  obtain ⟨yt, h1, -⟩ := extPt Y T b z hx
  obtain ⟨tP, ⟨mP'⟩⟩ : ∃ t : SAB H (Sp T.V), Nonempty (SABMap t Y.t yt) := by
    obtain ⟨_, _, _, _, _, m, -⟩ := sabPull Out.CubePf.cubePull yt Y.t
    exact ⟨_, ⟨m⟩⟩
  obtain ⟨mF, -⟩ := sabCancel pullCubCancel E H _ _ _ Xo.univ.t Y.oF.t t' (pullback.fst _ _) z Y.m0.toSABMap
    (PullbackSections.sabMapCast m1 hzf.symm)
  obtain ⟨mJ, -⟩ := sabComp pullCubComp E H _ _ _ Y.t Y.oF.t t' (Y.jQ ≫ pullback.fst _ _) z Y.m mF
  have hj : z ≫ Y.jQ ≫ pullback.fst _ _ = Out.jK T.V ≫ yt := h1.symm
  obtain ⟨mK, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t tP t' yt (Out.jK T.V) mP' (PullbackSections.sabMapCast mJ hj)
  have hprop : IsProper t'.G.hom :=
    MorphismProperty.of_isPullback (P := @IsProper) m1.cart.1 Xo.univ.proper
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H T.V inferInstance G tP t' hprop m2 mK
  obtain ⟨n', -⟩ := sabComp pullCubComp E H _ _ _ Y.t tP G yt (𝟙 _) mP' ψ
  exact (((GlobalTheory.T.thetaKeyScalar_isUnit_on_integralModels κ hκ E H Dw l Xo c _ _ Y p hpq (isBaseRing_local c W) hp h2 h3 h4 h5).1 T.V T.Fr z yt h1 G
    (PullbackSections.sabMapCast n' (Category.id_comp yt)) n w hw θ k hk).1 hθ).1

end Model

end GlobalTheory.KeyValAny

noncomputable section

namespace GlobalTheory.KeyValAny

section Any

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.Pj GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels
open GlobalTheory.KeyIntegralVal

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem key_unit_any {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q)
    {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {e : ℕ} (ho : OverLa la T.V io e)
    {x : Sp T.Fr ⟶ Xo.X} (hxs : x ≫ Xo.s = spMap (io.comp (IntermediateField.inclusion c.le).toRingHom))
    {G : SAB H (Sp T.V)} {t' : SAB H (Sp T.Fr)} (m1 : SABMap t' Xo.univ.t x)
    (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))) {n : ℕ} {w : Fin n → (epsR T.V ⟶ G.G)} (hw : IsLieBasis w)
    {θ : G.PP.L.Sec} (hθ : Generates (X := G.G) θ) (k : KeyIn T.Fr)
    (hk : IsFibreOf k G.G G.PP.L G.PP.rig θ w (algebraMap T.V T.Fr)) :
    ∃ u : T.Vˣ, (κ T.Fr k : T.Fr) = algebraMap T.V T.Fr u := by
  obtain ⟨p, hp, hpl⟩ := GlobalTheory.Reg.exists_prime_natCast_mem la
  by_cases hgp : l.GoodAt p
  · exact key_unit_at hκ hpq hp hpl hgp ho hxs m1 m2 hw hθ k hk
  · exact GlobalTheory.T.thetaKeyRule_isUnit_at_bad_level_place E H Dw l Xo c κ hκ hpq la p hp hpl hgp T io e ho x hxs G t' m1 m2 n w hw θ hθ k hk

theorem exists_tied_det_any {κ : KeyRule} (hκ : IsKeyRule κ) (hpq : 1 ≤ Dw.p + Dw.q)
    {g : ℕ} (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ))
    {la : HeightOneSpectrum (𝓞 c.F)} {T : CDVR} {io : c.F →+* T.Fr} {r : ℕ} (ho : OverLa la T.V io r)
    (τ' : (E →+* ℂ) → (𝓞 E →+* T.V)) (hτ : ∀ τ a, algebraMap T.V T.Fr (τ' τ a) = io (embK c τ a))
    (y : letI := io.toAlgebra; FrPt Xo c T.Fr) (hy : Integral T io y) :
    letI := io.toAlgebra
    ∃ (Φ : FibKey Xo T.Fr y.x) (A : 𝓞 E →+* Matrix (Fin g) (Fin g) T.V)
      (U : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → Fin g → T.V) (u : T.Vˣ), Tied e y.s y.u Φ ∧
      (∀ τ (x : Fin g → T.V), (∀ a, (A a).mulVec x = τ' τ a • x) →
        ∃ cf : Fin (Dw.mult τ) → T.V, x = ∑ k, cf k • U τ k) ∧
      (∀ τ k a, (A a).mulVec (U τ k) = τ' τ a • U τ k) ∧
      (κ T.Fr Φ.key : T.Fr) =
        algebraMap T.V T.Fr ((Matrix.of fun j k => U (e j).1 (e j).2 k).det ^ 4 * (u : T.V)) := by
  letI := io.toAlgebra
  obtain ⟨G, t', m1, m2, ⟨ub, u1, u2, u3, u4⟩, θ, hθ, w1, w2, σ, s1, θ2, r1, r2, i1, i2, hp, hs⟩ := hy
  obtain ⟨U₀, hU₀, hg₀⟩ := GlobalTheory.CM.exists_pat_of_obj E H Dw l _ _ _ _ Xo.univ
  obtain ⟨⟨P, rfl, hPg⟩, -⟩ := GlobalTheory.CM.PAT.exists_of_sabMap E H _ _ y.x U₀ t' (hU₀ ▸ m1)
  obtain ⟨Ψ, -, hΨ, -⟩ := exists_tied E H Dw l Xo c g e T.Fr y hpq
  have hgp : 1 ≤ g := hΨ ▸ Ψ.g_pos
  obtain rfl : P.g = g := hPg.trans (hg₀.trans (card_frame_index Dw e))
  have ht : SecTie m1 σ y.s := ⟨w1, s1, r1, i1, hs⟩
  have hne := ((SecTieEx.secTie_exists_unique E H Dw l Xo T.Fr y.x P.t m1).2.2 σ _ ht).2.1
    (GlobalTheory.Frames.secNZ_of_secGen GlobalTheory.lawsFieldsSeparately.2.1 E H Dw l Xo T.Fr _ _ y.gen)
  have hB := (GlobalTheory.Frames.eigBasis_iff_tanBasis E H Dw l Xo c T.Fr y.x y.u P.g e y.tan y.eig).1 y.basis
  obtain ⟨-, hb⟩ := GlobalTheory.Frames.lieBasis_iff_tanBasis E H Dw l Xo T.Fr y.x P.t.G m1.φ m1.cart
  choose u' hu₁ hu₂ using u4
  have hov : ∀ τ i, u' τ i ≫ P.t.G.hom = (epsR T.Fr).hom := fun τ i => by
    have : IsPreimmersion (spMap (algebraMap T.V T.Fr)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors T.V)
    rw [← cancel_mono (spMap (algebraMap T.V T.Fr)), Category.assoc, ← m2.cart.1.w, ← Category.assoc, hu₂,
      Category.assoc, Over.w]
    exact (GlobalTheory.EtaVal.spMap_comp_spMap _ _).trans ((congrArg spMap (RingHom.ext fun a => by
      ext <;> simp [Formalism.L2.Pj.dualMap, TrivSqZeroExt.algebraMap_eq_inl])).trans (GlobalTheory.EtaVal.spMap_comp_spMap _ _).symm)
  let v : Fin P.g → (epsR T.Fr ⟶ P.t.G) := fun j => Over.homMk (u' (e j).1 (e j).2) (hov _ _)
  have hv : IsLieBasis v := (hb _ v).2 (by
    rw [show (fun j => (v j).left ≫ m1.φ) = fun j => y.u (e j).1 (e j).2 from funext fun j => hu₁ _ _]
    exact hB)
  obtain ⟨n, w, hw⟩ := Chart.exists_isLieBasis G.G G.semi.smooth
  obtain ⟨w', hw', hww⟩ := GlobalTheory.exists_isLieBasis_baseChange _ _ _ G.G P.t.G m2.φ m2.cart G.semi.smooth n w hw
  obtain rfl : P.g = n := by
    simpa using Fintype.card_congr ((GlobalTheory.Serre.Lie.basis P.t.act hv).indexEquiv (GlobalTheory.Serre.Lie.basis P.t.act hw'))
  have inj := IsFractionRing.injective T.V T.Fr
  obtain ⟨A, U, a1, a2, a3⟩ := exists_lie_matrices G.act hw τ' (m := Dw.mult) ub
    (fun τ k => (isTan_iff_isTangent _).1 (u1 τ k)) (fun τ k a => u2 τ k a _ (hτ τ a))
    (fun τ x hx he => (u3 τ x ((isTan_iff_isTangent _).2 hx) fun a z hz => by
      rw [inj (hz.trans (hτ τ a).symm)]
      exact he a).exists)
  obtain ⟨u, hu⟩ := key_unit_any hκ hpq ho y.x_over m1 m2 hw hθ _
    (isFibreOf_of_sabMap _ P m2 hgp hne r2 i2 hp hw' hww)
  refine ⟨⟨P, m1, hgp, σ, hne, v, hv⟩, A, U, u, ⟨ht, rfl, fun j => hu₁ _ _⟩, a1, a2, ?_⟩
  have h := hκ.1 T.Fr P.pol hgp P.t.PP.rig P.t.PP.rigGen σ hne w' hw' σ hne v hv 1
    ((Matrix.of fun j k => U (e j).1 (e j).2 k).map (algebraMap T.V T.Fr)) (fun i => by simp [constFn])
    (fun j => Chart.comb_baseChange _ m2.cart (a3 (e j).1 (e j).2) hww (hu₂ _ _))
  rw [one_pow, one_mul, hu] at h
  rw [map_mul, map_pow, RingHom.map_det]
  exact h

end Any

section Main

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD _root_.Formalism.L2.Pj Formalism.BasicNotions Formalism.BasicNotions.TH _root_.Formalism.L2.Theta GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.IndefiniteRowSideFullHecke.ComponentMassSum GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects
open GlobalTheory.KeyIntegralVal

theorem key_valuation_nonneg : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : (Rul Xo c)ˣ), 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ GlobalTheory.AllWt.secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (K : Rul Xo c) := by
  intro κ hκ E _ _ _ H Dw l Xo c g e K hpq _ hK w v hv
  classical
  obtain ⟨⟨_, T, io, r, ho, y, -, η, -, rfl⟩, rfl⟩ := hv
  letI := io.toAlgebra
  choose τ' hτ using fun τ : E →+* ℂ => GlobalTheory.EtaVal.exists_base_map_of_overLa (β := embK c τ)
    (fun a => w.valuation_le_one (K := c.F) (RingOfIntegers.mapRingHom (embF c τ) a)) T io r ho
  replace hτ : ∀ τ a, algebraMap T.V T.Fr (τ' τ a) = io (embK c τ a) := fun τ a => DFunLike.congr_fun (hτ τ) a
  have hinj : Function.Injective τ' := fun τ₁ τ₂ h =>
    IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a =>
      congrArg Subtype.val (io.injective ((hτ τ₁ a).symm.trans ((h ▸ rfl : _ = _).trans (hτ τ₂ a)))))
  obtain ⟨Φ, A, U, u, hΦ, a1, a2, hu⟩ := exists_tied_det_any hκ hpq e ho τ' hτ y.1 y.2.2
  choose δ hδ hδ0 hδv using fun τ : E →+* ℂ => exists_mem_different_vLa (embF c τ) w
  have hD := GlobalTheory.ColengthDifferent.colength_dvd E T.Fr T.V (E →+* ℂ) τ' Dw.mult g e A U hinj (Embeddings.card E ℂ) inferInstance a1 a2 δ hδ
  have hb := nval_bounds ho (fun τ => embF c τ (δ τ)) (fun τ => τ' τ (δ τ)) Dw.mult _ u
    (fun τ => (map_ne_zero _).2 (RingOfIntegers.coe_ne_zero_iff.2 (hδ0 τ))) (fun τ => hτ τ (δ τ)) hD
  rw [← hu, ← hK T.Fr y.1 Φ hΦ] at hb
  exact hb.1

end Main

end GlobalTheory.KeyValAny
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValuationNonnegIntegralFramedPointStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.ShFam GlobalTheory.LamT GlobalTheory.KeyFourth
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaKeyRule_valuation_nonneg_integral_framed_point : ∀ (κ : GlobalTheory.KeyCl.Rule), GlobalTheory.IndefiniteRowSideFullHecke.FibreFramesOnModels.IsKeyRule κ → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (g : ℕ) (e : Fin g ≃ Σ τ : E →+* ℂ, Fin (Dw.mult τ)) (K : (Rul Xo c)ˣ), 1 ≤ Dw.p + Dw.q → (K : Rul Xo c) ∈ GlobalTheory.AllWt.secZ Xo c ((4 : ℤ) • keyEx Dw) → (∀ (F : Type) [Field F] [CharZero F] [Algebra c.F F] (y : FrPt Xo c F) (Φ : FibKey Xo F y.x), Tied e y.s y.u Φ → evR Xo c (K : Rul Xo c) y = (κ F Φ.key : F)) → ∀ (w : HeightOneSpectrum (𝓞 c.F)), ∀ v ∈ valSet Xo c (algCls Xo c) w, 0 ≤ v (K : Rul Xo c) := by
  first | exact @GlobalTheory.KeyValAny.key_valuation_nonneg | exact GlobalTheory.KeyValAny.key_valuation_nonneg | (intros; apply GlobalTheory.KeyValAny.key_valuation_nonneg <;> assumption)
end
