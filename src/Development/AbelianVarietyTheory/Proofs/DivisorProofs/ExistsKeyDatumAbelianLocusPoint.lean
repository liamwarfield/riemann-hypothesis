module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeightSectionsNonvanishingOpen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomFramesChangeStageZero
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsSmoothFanInt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModModT
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatIntegrandFlippedTensorLocallyConstantCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteInfiniteScalarBounds

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumAbelianLocusPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullMulAddPullMulInv
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.EndOnTorsion
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SquareSemiOpen

theorem isAb_pullback_open {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsSemiAbelian A) (U : S.Opens)
    (hU : IsProper (A.hom ∣_ U)) : IsAbelianScheme ((Over.pullback U.ι).obj A) := by
  have hB := ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsSemiAbelian.pullback U.ι A hA
  refine ⟨hB.comm, hB.smooth, ?_, hB.geomConnected⟩
  change IsProper (pullback.snd A.hom U.ι)
  rw [← pullbackRestrictIsoRestrict_hom_morphismRestrict]
  infer_instance

end GlobalTheory.SquareSemiOpen
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumAbelianLocusPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.KeyDatumAb

theorem exists_keyOn : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing B] (f : A →+* B) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G)), 1 ≤ g → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsOpen (abLocus G) → L.IsSymmetric → PolOnAb G L.L → IsLieBasis y → NzFib σ → Set.range (spMap f) ⊆ abLocus G → ∃ (x : KeyIn B) (hg : x.P.g = g), KeyOn f x G L σ (fun i => y (i.cast hg)) := by
  intro A B _ _ _ _ _ f G _ _ L σ g y hg1 hG hd hO hs hpol hy hσ hr
  let W : (Sp A).Opens := ⟨abLocus G, hO⟩
  have hWsub : (W : Set (Sp A)) ⊆ abLocus G := subset_rfl
  have hprop : IsProper (G.hom ∣_ W) := GlobalTheory.AbLocusProperNormal.isProper_restrict_of_subset_abLocus A G hG W hWsub
  have hGW : IsAbelianScheme ((Over.pullback W.ι).obj G) := GlobalTheory.SquareSemiOpen.isAb_pullback_open G hG W hprop
  haveI : IsProper ((Over.pullback W.ι).obj G).hom := hGW.proper
  obtain ⟨ha, hk⟩ := hpol W hWsub
  obtain ⟨x', hx'⟩ : ∃ x' : Sp B ⟶ W.toScheme, x' ≫ W.ι = spMap f :=
    ⟨IsOpenImmersion.lift W.ι (spMap f) (by rw [Scheme.Opens.range_ι]; exact hr), IsOpenImmersion.lift_fac _ _ _⟩
  have h := isGrpPullback_pullback G (spMap f)
  have h₀ := isGrpPullback_pullback G W.ι
  have h₂ := h.congr hx'.symm rfl
  let φ : ((Over.pullback (spMap f)).obj G).left ⟶ G.left := pullback.fst G.hom (spMap f)
  let ψ : ((Over.pullback (spMap f)).obj G).left ⟶ ((Over.pullback W.ι).obj G).left :=
    h₀.1.lift _ _ (h₂.1.w.trans (Category.assoc _ _ _).symm)
  have hψ : ψ ≫ pullback.fst G.hom W.ι = φ := h₀.1.lift_fst _ _ _
  have h₃ : IsGrpPullback ((Over.pullback (spMap f)).obj G) ((Over.pullback W.ι).obj G) x' ψ :=
    h₀.cancel (h₂.congr rfl hψ.symm) (h₀.1.lift_snd _ _ _)
  have hL := pull_isLB L.isLB φ
  have hL₀ := pull_isLB L.isLB (pullback.fst G.hom W.ι)
  obtain ⟨w, hw⟩ : LBIso (L.L.pull φ) ((L.L.pull (pullback.fst G.hom W.ι)).pull ψ) :=
    LBIso.chartPull (chartPullId _)
      (chartPullLinComb L.L _ (fun _ : PUnit => ψ) (fun _ => φ) (fun _ => 1) (𝟙 _)
        fun _ => hψ.trans (Category.id_comp _).symm)
      (PolBaseChange.lbIso_refl hL)
  have hamp₀ : RelAmple (Over.mk ((Over.pullback (spMap f)).obj G).hom) ((L.L.pull (pullback.fst G.hom W.ι)).pull ψ) :=
    GlobalTheory.AmpleBaseChange.relAmple_of_isPullback hL₀ ha h₃.1
  have hLψ := pull_isLB hL₀ ψ
  obtain ⟨w', hw'⟩ : LBIso (L.L.pull φ) (((L.L.pull (pullback.fst G.hom W.ι)).pull ψ).pull (𝟙 _)) :=
    LBIso.chartPull (chartPullId _) (Geo.Tor.chartPullPull _ _ _ rfl) ⟨w, hw⟩
  have hamp : RelAmple ((Over.pullback (spMap f)).obj G) (L.L.pull φ) :=
    relAmple_pull (A' := (Over.pullback (spMap f)).obj G) (A := Over.mk ((Over.pullback (spMap f)).obj G).hom)
      (IsPullback.id_horiz _) hLψ hL ((isGen_iff w').1 hw') ⊤ (isAffineOpen_top _) (fun _ => trivial) hamp₀
  have hsa := IsSemiAbelian.pullback (spMap f) G hG
  have hA : IsAbelianScheme ((Over.pullback (spMap f)).obj G) :=
    { comm := hsa.comm, smooth := hsa.smooth,
      proper := MorphismProperty.of_isPullback (P := @IsProper) h₃.1 hGW.proper
      geomConnected := hsa.geomConnected }
  haveI := hsa.comm
  let P : PolAV (Sp B) :=
    { A := (Over.pullback (spMap f)).obj G
      isAb := hA
      g := g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 hd
      L := L.L.pull φ
      isLB := hL
      rigid := PolBaseChange.rigidified_pull h ⟨L.rig, L.rigGen⟩
      sym := PolBaseChange.sym_pull h (CechPic.sym_of_isSymmetric L hs)
      ample := hamp
      ktriv := kTriv_pull h₃ hL₀ hL ((isGen_iff w).1 hw) hk }
  have he : eSec P.A ≫ φ = spMap f ≫ eSec G := PolBaseChange.eSec_comm h
  have hr' : (rigPullOf φ (spMap f) he L.L L.rig).IsGen :=
    Out.LBxP.isGen_pullAlong L.L φ (spMap f) (fun _ : PUnit => eSec G) (fun _ => 1) (fun _ => eSec P.A)
      (fun _ => he) L.rig L.rigGen
  have hw0 := (isGen_iff _).1 (idIso_isGen hL)
  obtain ⟨th', hth'⟩ := sec_pull_down hw0 L.isLB hL σ
  obtain ⟨v', hv', hv'φ⟩ := GlobalTheory.exists_isLieBasis_baseChange A B f G P.A φ h hG.smooth g y hy
  have := hA.smooth
  refine ⟨⟨P, hg1, _, hr', th', fun s => ?_, v', hv'⟩, rfl, φ, he, idIso _, Chart.dualMapR f, h, idIso_isGen hL,
    fun p => hr' p.1 p.2, GlobalTheory.KeyPow.appLE_eq_of_stalk _ σ th' (hth' _ (𝟙 _)), fun a => ?_, ?_, fun i => hv'φ i⟩
  · obtain ⟨z, hz, hz'⟩ := hσ (spMap f s)
    obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
    obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
    refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
    have u₁ : IsUnit (gs φ y _ (σ.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
    have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  · ext <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]
  · ext <;> simp [Chart.dualMapR]

end GlobalTheory.KeyDatumAb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeyDatumAbelianLocusPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.KeyEven
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyDatum_abelianLocus_point : ∀ (A B : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [CommRing B] (f : A →+* B) (G : Over (Sp A)) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (σ : L.L.Sec) (g : ℕ) (y : Fin g → (epsR A ⟶ G)), 1 ≤ g → IsSemiAbelian G → SmoothOfRelativeDimension g G.hom → IsOpen (abLocus G) → L.IsSymmetric → PolOnAb G L.L → IsLieBasis y → NzFib σ → Set.range (spMap f) ⊆ abLocus G → ∃ (x : KeyIn B) (hg : x.P.g = g), KeyOn f x G L σ (fun i => y (i.cast hg)) := by
  first | exact @GlobalTheory.KeyDatumAb.exists_keyOn | exact GlobalTheory.KeyDatumAb.exists_keyOn | (intros; apply GlobalTheory.KeyDatumAb.exists_keyOn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleRootOfUnityTwist
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.BottomFrames

attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BottomRebase

theorem isFrame_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    {Λ : Submodule (𝓞 E) (Fin n → E)} (h : ∀ y, y ∈ Λ ↔ ∀ i, ∃ b : 𝓞 E, (b : E) = y i) :
    Formalism.L2.DIV.IsFrame (1 : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F))) Λ := by
  have e : Λ = Formalism.UG.stdLat (n := Fin n) (A := E) (𝓞 E) := by
    ext y
    rw [h, Formalism.UG.stdLat, Submodule.mem_pi]
    exact ⟨fun H i _ => H i, fun H i => H i trivial⟩
  exact e ▸ Formalism.L2.DIV.frame_standard F E n


set_option maxHeartbeats 4000000 in
theorem frame_change {D : D7} {T : Type} {A A' WW : HSp D} (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (hθ : IsInfFam θ)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → Formalism.L2.Host.HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E))
    (Y : Tri T A A' WW) (hI : Y.Is ψ θ α β νH S) (b : GL (Fin WW.rank) (EAf D)) (fW : Formalism.L2.DIV.IsFrame b Y.rW.Λ) :
    ∃ (Z : Tri T A A' WW) (v : T → ℂ), Z.Is ψ θ α β νH S ∧ Z.rA = Y.rA ∧ Z.rA' = Y.rA' ∧ Z.rW = ⟨Y.rW.Λ, b, Y.rW.s, Y.rW.B⟩ ∧
      (∀ t, ∃ n : ℕ, 0 < n ∧ v t ^ n = 1) ∧ ∀ c : T → ℂ, Y.IsConst ψ θ c → Z.IsConst ψ θ (fun t => v t * c t) := by
  classical
  have fA := hI.rigA.2.1
  have fA' := hI.rigA'.2.1
  have hee : ∀ t, Y.e t * Y.e t = Y.e t := fun t => GlobalTheory.PlaceDatum.idemSum_mul_self (hI.idem t)
  choose k hk1 hk2 hk3 hk4 using fun t =>
    GlobalTheory.T.exists_unitaryStabilizer_transition_selfDualFrames (Y.e t) (S t) (hI.idem t) WW Y.rW.Λ hI.rigW.1 Y.rW.β b hI.rigW.2.1 fW
  choose x1 hx1 hx1' using fun t => GlobalTheory.T.standardThetaPair_first_frameChange_unitTranslate (α t / β t) (Y.e t) (S t) (hI.idem t) (Y.ideal S t) A WW
    Y.rA.Λ Y.rA.β Y.rA.β hI.rigA.2.1 fA Y.rW.β b (k t) (hk1 t) (hk3 t)
  choose x2 hx2 hx2' using fun t => GlobalTheory.T.standardThetaPair_second_frameChange_unitTranslate (α t / β t) (Y.e t) (S t) (hI.idem t) (Y.ideal S t) A.rank
    A' WW Y.rA'.Λ Y.rA'.β Y.rA'.β hI.rigA'.2.1 fA' Y.rW.β b (k t) (hk1 t) (hk3 t)
  set y : T → (AE D)ˣ := fun t => GlobalTheory.VecInv.detAt (Y.e t) (hee t) WW (k t) with hy
  have hy1 : ∀ t, IsDetAt (Y.e t) WW (k t) (y t) := fun t => GlobalTheory.VecInv.isDetAt_detAt _ _ _ _
  set c1 : T → ℂ := fun t => (((α t / β t) (x1 t) : Circle) : ℂ) * (((β t (y t) : Circle) : ℂ))⁻¹ with hc1
  set c2 : T → ℂ := fun t => (((α t / β t) (x2 t) : Circle) : ℂ) * (((α t (y t) : Circle) : ℂ))⁻¹ with hc2

  have hψ : IsStdChar D ψ (-1) := hI.isVac.1
  have hSdA := selfDual_neg hI.rigA.1
  have hinf : ∀ t, infPart D (Y.e t) = 0 := fun t => GlobalTheory.PlaceDatum.infPart_idemSum (hI.idem t)
  have hinf' : ∀ t, infPart D (cA D (Y.e t)) = 0 := fun t => GlobalTheory.PlaceDatum.infPart_cA (hinf t)
  have hee' : ∀ t, cA D (Y.e t) * cA D (Y.e t) = cA D (Y.e t) := fun t => by rw [← RingHom.map_mul, hee t]
  have hSB : ∀ t, IsSBHalf (Y.e t) (latO (GlobalTheory.Grid.neg A) WW (Y.rA.Λ : Set (Fin A.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW Y.rA.β Y.rW.β) := fun t => by
    obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := GlobalTheory.Grid.neg A)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSdA)
      (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ (hI.rigW.1)) Y.rA.β Y.rW.β
    exact StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_isSB (hI.weil' t).hecT.1 (hI.idem t) (GlobalTheory.ConstRatio.ideal_ne_bot Y S t)
      A WW Y.rA.β Y.rW.β _ (GlobalTheory.PlaceDatum.exists_den_frMapO (S := GlobalTheory.Grid.neg A) hSdA.1.fg hI.rigW.1.1.fg Y.rA.β Y.rW.β)
      ⟨K, hK, fun t' ht => hC t' (GlobalTheory.PlaceDatum.infPart_of_half (hinf t) ht)⟩
  have hSB' : ∀ t, IsSBHalf (cA D (Y.e t)) (latO A' WW (Y.rA'.Λ : Set (Fin A'.rank → D.host.E)) (Y.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)
      (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW Y.rA'.β Y.rW.β) := fun t =>
    GlobalTheory.T.standardThetaPair_second_isSchwartzBruhat_conjHalf _ (hI.weil' t).hecT.1 (Y.e t) (S t) (hI.idem t) _ (GlobalTheory.ConstRatio.ideal_ne_bot Y S t) A.rank A' WW
      Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 Y.rA'.β Y.rW.β
  have thY : ∀ t, IsThetaFunO ψ (GlobalTheory.Grid.neg A) WW (Y.f t) := fun t => by
    obtain ⟨Tm, hTm⟩ := (hI.fst t).1
    rw [(hI.fst t).2 Tm hTm]
    exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ (GlobalTheory.Grid.neg A) WW Y.rA.Λ Y.rW.Λ hSdA hI.rigW.1 (Y.e t) (hee t) (hinf t)
      Y.vac hI.isVac.2.theta Tm hTm _ (hSB t)
  have thY' : ∀ t, IsThetaFunO ψ A' WW (Y.f' t) := fun t => by
    obtain ⟨Tm, hTm⟩ := (hI.snd t).1
    rw [(hI.snd t).2 Tm hTm]
    exact GlobalTheory.SchrTheta.isTheta_placeModel D ψ hψ A' WW Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 (cA D (Y.e t)) (hee' t) (hinf' t)
      Y.vac' hI.isVac'.2.theta Tm hTm _ (hSB' t)
  let Z : Tri T A A' WW :=
    ⟨⟨Y.rA.Λ, Y.rA.β, Y.rA.s, Y.rA.B⟩, ⟨Y.rA'.Λ, Y.rA'.β, Y.rA'.s, Y.rA'.B⟩, ⟨Y.rW.Λ, b, Y.rW.s, Y.rW.B⟩, Y.ω, Y.ω',
      Y.vac, Y.vac', Y.e, Y.c, fun t => c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t), fun t => c2 t • Y.ω' t (1, k t) (Y.f' t),
      Y.m, Y.fd, Y.m', Y.fd'⟩
  have hZI : Z.Is ψ θ α β νH S := by
    refine ⟨hI.rank, ⟨hI.rigA.1, fA, hI.rigA.2.2⟩, ⟨hI.rigA'.1, fA', hI.rigA'.2.2⟩, ⟨hI.rigW.1, fW, hI.rigW.2.2⟩, hI.weil,
      hI.weil', hI.isVac, hI.isVac', hI.idem, hI.expo, fun t => ?_, fun t => ?_, hI.meas, hI.meas'⟩
    · refine ⟨(hI.fst t).1, fun Tm hTm => ?_⟩
      have hY := (hI.fst t).2 Tm hTm
      have hLaw := ((GlobalTheory.WeilSplit.weilSplitFormula D ψ θ (GlobalTheory.Grid.neg A) WW (β t) (β t / α t) ((Y.ω t).toSgn true)
        (hI.weil t) (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.Λ Y.rW.Λ hSdA hI.rigW.1 Y.vac hI.isVac (Y.e t)
        (Or.inr ⟨_, hI.idem t⟩)).1 Tm hTm) 1 (k t) (suppAt_one' _ _) (hk1 t) (stabLat_one' _ _) (hk2 t) 1 (y t)
        (isDetAt_one' _ _) (hy1 t) _ (hSB t)
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW Y.rA.β b =
          (((α t / β t) (x1 t) : Circle) : ℂ) • fun s => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW
            Y.rA.β Y.rW.β (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt (GlobalTheory.Grid.neg A) WW 1 (k t) s) := funext fun s => hx1' t s
      show c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t) = Tm (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (α t / β t) (Y.e t) (Y.ideal S t) A WW Y.rA.β b)
      rw [hY, hLaw, e1, map_smul, smul_smul]
      congr 1
      rw [hc1, map_one, Circle.coe_one, inv_one, one_mul, mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), mul_one]
    · refine ⟨(hI.snd t).1, fun Tm hTm => ?_⟩
      have hY := (hI.snd t).2 Tm hTm
      have hLaw := ((GlobalTheory.WeilSplit.weilSplitFormula D ψ θ A' WW (α t) (α t / β t) (Y.ω' t)
        (hI.weil' t) Y.rA'.s Y.rW.s Y.rA'.Λ Y.rW.Λ hI.rigA'.1 hI.rigW.1 Y.vac' hI.isVac' (Y.e t)
        (Or.inr ⟨_, hI.idem t⟩)).2 Tm hTm) 1 (k t) (suppAt_one' _ _) (hk1 t) (stabLat_one' _ _) (hk2 t) 1 (y t)
        (isDetAt_one' _ _) (hy1 t) _ (hSB' t)
      have e1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW Y.rA'.β b =
          (((α t / β t) (x2 t) : Circle) : ℂ) • fun s => GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW
            Y.rA'.β Y.rW.β (GlobalTheory.IndefiniteRowSideFullHecke.SplitSumStabLattice.pullPt A' WW 1 (k t) s) := funext fun s => hx2' t s
      show c2 t • Y.ω' t (1, k t) (Y.f' t) = Tm (GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdSnd (α t / β t) (Y.e t) (Y.ideal S t) A.rank A' WW Y.rA'.β b)
      rw [hY, hLaw, e1, map_smul, smul_smul]
      congr 1
      rw [hc2, map_one, Circle.coe_one, inv_one, one_mul, mul_assoc, inv_mul_cancel₀ (Circle.coe_ne_zero _), mul_one]

  have tsg : ∀ t (h' : GA D WW), (Y.ω t).toSgn true (1, h') = Y.ω t (1, h') := fun t h' => by
    show Y.ω t ((GlobalTheory.Grid.ofSgn true A) 1, h') = _
    rw [map_one]
  have kerZ : ∀ t P h' g, Z.ker ψ θ t P h' g = c1 t * Y.ker ψ θ t P (h' * k t) g := by
    intro t P h' g
    have hop := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ (GlobalTheory.Grid.neg A) WW _ _ ((Y.ω t).toSgn true) (hI.weil t) hθ
      (fun τ => -Y.rA.s τ) (fun τ => -Y.rA.s τ) Y.rA.B Y.rA.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B 1 (k t)
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp θ (hinf t) (hk1 t), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp θ (hinf t) (hk1 t), Matrix.one_mul]) (Y.f t) (thY t) P).2
    have hm : ∀ F, Y.ω t (g, h') (Y.ω t (1, k t) F) = Y.ω t (g, h' * k t) F := fun F => by
      have e := (Y.ω t).map_mul (g, h') (1, k t)
      rw [Prod.mk_mul_mk, mul_one] at e
      rw [e]; rfl
    have e1 : pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B
        (c1 t • (Y.ω t).toSgn true (1, k t) (Y.f t)) P = c1 t • (Y.ω t) (1, k t)
        (pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P) := by
      rw [GlobalTheory.SeeSaw.Resc.pureTensorO_smul, LinearMap.smul_apply, ← tsg, hop]
    calc Z.ker ψ θ t P h' g = (Y.ω t (g, h') (c1 t • Y.ω t (1, k t)
          (pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P))) 0 := by
          rw [← e1]; rfl
      _ = c1 t * (Y.ω t (g, h') (Y.ω t (1, k t)
          (pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P))) 0 := by
          rw [LinearMap.map_smul]; rfl
      _ = c1 t * Y.ker ψ θ t P (h' * k t) g :=
          congrArg (c1 t * ·) (congrFun (hm (pureTensorO ψ θ (GlobalTheory.Grid.neg A) WW (fun τ => -Y.rA.s τ) Y.rW.s Y.rA.B Y.rW.B (Y.f t) P)) 0)
  have kerZ' : ∀ t P h' g, Z.ker' ψ θ t P h' g = c2 t * Y.ker' ψ θ t P (h' * k t) g := by
    intro t P h' g
    have hw' : IsWeilDatumO ψ A' WW (α t) (α t / β t) (Y.ω' t) := hI.weil' t
    have hop := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ A' WW (α t) (α t / β t) (Y.ω' t) hw' hθ
      Y.rA'.s Y.rA'.s Y.rA'.B Y.rA'.B Y.rW.s Y.rW.s Y.rW.B Y.rW.B 1 (k t)
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp θ (hinf t) (hk1 t), Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.one_mul])
      (fun τ => by rw [compAt_supp θ (hinf t) (hk1 t), Matrix.one_mul]) (Y.f' t) (thY' t) P).2
    have hm : ∀ F, Y.ω' t (g, h') (Y.ω' t (1, k t) F) = Y.ω' t (g, h' * k t) F := fun F => by
      have e : Y.ω' t ((g, h') * (1, k t)) = Y.ω' t (g, h') * Y.ω' t (1, k t) := map_mul _ _ _
      rw [Prod.mk_mul_mk, mul_one] at e
      rw [e]; rfl
    have e1 : pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B
        (c2 t • Y.ω' t (1, k t) (Y.f' t)) P = c2 t • (Y.ω' t) (1, k t)
        (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P) := by
      rw [GlobalTheory.SeeSaw.Resc.pureTensorO_smul, LinearMap.smul_apply, hop]
    calc Z.ker' ψ θ t P h' g = (Y.ω' t (g, h') (c2 t • Y.ω' t (1, k t)
          (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P))) 0 := by
          rw [← e1]; rfl
      _ = c2 t * (Y.ω' t (g, h') (Y.ω' t (1, k t)
          (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P))) 0 := by
          rw [LinearMap.map_smul]; rfl
      _ = c2 t * Y.ker' ψ θ t P (h' * k t) g :=
          congrArg (c2 t * ·) (congrFun (hm (pureTensorO ψ θ A' WW Y.rA'.s Y.rW.s Y.rA'.B Y.rW.B (Y.f' t) P)) 0)
  have IZ : ∀ t P h', Z.I ψ θ t P h' = c1 t * Y.I ψ θ t P (h' * k t) := fun t P h' => by
    show ∫ g in Y.fd, Z.ker ψ θ t P h' g ∂Y.m = _
    simp only [kerZ]
    exact MeasureTheory.integral_const_mul _ _
  have IZ' : ∀ t P h', Z.I' ψ θ t P h' = c2 t * Y.I' ψ θ t P (h' * k t) := fun t P h' => by
    show ∫ g in Y.fd', Z.ker' ψ θ t P h' g ∂Y.m' = _
    simp only [kerZ']
    exact MeasureTheory.integral_const_mul _ _
  have c1ne : ∀ t, c1 t ≠ 0 := fun t => mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))
  have c2ne : ∀ t, c2 t ≠ 0 := fun t => mul_ne_zero (Circle.coe_ne_zero _) (inv_ne_zero (Circle.coe_ne_zero _))

  refine ⟨Z, fun t => c1 t / c2 t, hZI, rfl, rfl, rfl, fun t => ?_, fun c hc => ?_⟩
  · obtain ⟨-, -, -, m, hm, H⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D (α t / β t) (hI.weil' t).hecT.1
    have H' : ∀ x, Formalism.L2.Pj.FinUnit x → (((α t / β t) x : Circle) : ℂ) ^ m = 1 := fun x hx => by
      rw [← Circle.coe_pow, H x hx, Circle.coe_one]
    refine ⟨m, hm, ?_⟩
    have e : c1 t / c2 t = (((α t / β t) (x1 t) : Circle) : ℂ) * (((α t / β t) (y t) : Circle) : ℂ) /
        (((α t / β t) (x2 t) : Circle) : ℂ) := by
      rw [MonoidHom.div_apply (α t) (β t) (y t), Circle.coe_div]
      exact (ratio_alg (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)).symm
    show (c1 t / c2 t) ^ m = 1
    rw [e, div_pow, mul_pow, H' _ (hx1 t), H' _ (hx2 t), H' _ (hk4 t _ (hy1 t))]
    simp
  · obtain ⟨⟨t0, ht0⟩, P, P', H⟩ := hc
    refine ⟨⟨t0, mul_ne_zero (div_ne_zero (c1ne t0) (c2ne t0)) ht0⟩, P, P', fun t => ⟨fun h' => ⟨?_, ?_⟩, ?_, fun h' => ?_⟩⟩
    · have e : Z.ker ψ θ t P h' = fun g => c1 t * Y.ker ψ θ t P (h' * k t) g := funext (kerZ t P h')
      rw [e]
      exact ((H t).1 (h' * k t)).1.const_mul _
    · have e : Z.ker' ψ θ t P' h' = fun g => c2 t * Y.ker' ψ θ t P' (h' * k t) g := funext (kerZ' t P' h')
      rw [e]
      exact ((H t).1 (h' * k t)).2.const_mul _
    · obtain ⟨h0, hh0⟩ := (H t).2.1
      refine ⟨h0 * (k t)⁻¹, ?_⟩
      rw [IZ', inv_mul_cancel_right]
      exact mul_ne_zero (c2ne t) hh0
    · show Z.I ψ θ t P h' = c1 t / c2 t * c t * Z.I' ψ θ t P' h'
      rw [IZ, IZ', (H t).2.2]
      exact const_alg (c2ne t)

end GlobalTheory.BottomRebase

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantSmoothProjFanNoSelfIntersections
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantSmoothProjFanNoSelfIntersections
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PolDeg.exists_inv_smooth_fan_noSelfInt : ∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ :=
  GlobalTheory.CompanionTheory.Ar.Fan.exists_smooth_fan_int
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantSmoothProjFanNoSelfIntersectionsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_smoothProjFan_noSelfIntersections : ∀ g : ℕ, ∃ φ : InvFun ℤ, IsPolFan (id : ℤ → ℤ) g φ ∧ NoSelfInt (id : ℤ → ℤ) g φ := by
  first | exact @GlobalTheory.PolDeg.exists_inv_smooth_fan_noSelfInt | exact GlobalTheory.PolDeg.exists_inv_smooth_fan_noSelfInt | (intros; apply GlobalTheory.PolDeg.exists_inv_smooth_fan_noSelfInt <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdMassNeZero
open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem std_mass_ne_zero : ∀ (D : D7) (N : ℕ), mass D N ≠ 0 := by
  intro D N
  haveI := (GlobalTheory.NormSum.cls_finite_card_le D N).1
  haveI := Fintype.ofFinite (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))
  have hne : (Finset.univ : Finset (GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N))).Nonempty :=
    ⟨DoubleCoset.mk _ _ 1, Finset.mem_univ _⟩
  have hpos : (0 : ℝ) < ∑ x : GlobalTheory.NormSum.Cls D N (GlobalTheory.NormSum.intG D N),
      ((GlobalTheory.NormSum.gam D (GlobalTheory.NormSum.intG D N) x.out : ℝ))⁻¹ :=
    Finset.sum_pos (fun x _ => inv_pos.2 (Nat.cast_pos.2 (Nat.pos_of_ne_zero
      (GlobalTheory.StabOrder.gam_ne_zero_dvd_invariant D N _ le_rfl x.out).1))) hne
  unfold mass
  rw [finsum_eq_sum_of_fintype]
  have h := Complex.ofReal_ne_zero.2 hpos.ne'
  push_cast at h
  exact h

end GlobalTheory.NormRatio
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockIpSelfRePos
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OpenKLeFockStab
open NumberField MeasureTheory Finset
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum
open GlobalTheory.NormSum (Pair Tup)
open GlobalTheory.FunObj.SqNum GlobalTheory.SqTop
open GlobalTheory.CMVal (IsHeckeL)

noncomputable section
namespace GlobalTheory.NormAdelic
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ t0 : ℂ} {Q : ℕ} {P : Pair D cc δ t0 Q}

theorem minorPol_ne_zero {a d : ℕ} {n : D.what₂.Tau → ℕ} (T : Tup D a d n) : GlobalTheory.NormSum.minorPol D T ≠ 0 := by
  unfold GlobalTheory.NormSum.minorPol
  refine Finset.prod_ne_zero_iff.2 fun τ _ => Finset.prod_ne_zero_iff.2 fun j _ => ?_
  set f : Fin a × Fin a → Formalism.MainNotions.GL3Theta.Idx D a d := fun p => (τ, (T τ j).1 p.1, p.2) with hf
  have hfi : Function.Injective f := by
    intro p q e
    simp only [hf, Prod.mk.injEq] at e
    exact Prod.ext ((T τ j).2.injective e.2.1) e.2.2
  have e : (Matrix.of fun i i' : Fin a => (MvPolynomial.X (τ, (T τ j).1 i, i') : MvPolynomial (Formalism.MainNotions.GL3Theta.Idx D a d) ℂ)) =
      (MvPolynomial.rename f).toRingHom.mapMatrix (Matrix.mvPolynomialX (Fin a) (Fin a) ℂ) := by
    ext i i'
    simp [Matrix.mvPolynomialX, hf]
  rw [e, ← RingHom.map_det]
  intro h0
  exact Matrix.det_mvPolynomialX_ne_zero (Fin a) ℂ
    ((MvPolynomial.rename_injective f hfi) (h0.trans (map_zero _).symm))

end GlobalTheory.NormAdelic
end
end

noncomputable section

open NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum GlobalTheory.NormRatio
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormRatio

theorem fockIp_self_re_pos {ι : Type} {p : MvPolynomial ι ℂ} (hp : p ≠ 0) :
    0 < (GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp p p).re := by
  unfold GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting.fockIp
  rw [Complex.re_sum]
  refine Finset.sum_pos (fun k hk => ?_) (MvPolynomial.support_nonempty.2 hp)
  rw [Complex.mul_conj, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
  refine mul_pos (Complex.normSq_pos.2 (MvPolynomial.mem_support_iff.1 hk)) ?_
  exact Nat.cast_pos.2 (Finset.prod_pos fun _ _ => Nat.factorial_pos _)

theorem fockSum_ne_zero : ∀ (D : D7) (a d : ℕ) (n : D.what₂.Tau → ℕ), a ≤ d → fockSum D a d n ≠ 0 := by
  intro D a d n had h0
  have hpos : 0 < (fockSum D a d n).re := by
    unfold fockSum
    rw [Complex.re_sum]
    haveI : Nonempty (GlobalTheory.NormSum.Tup D a d n) := ⟨fun _ _ => ⟨Fin.castLE had, fun _ _ h => h⟩⟩
    exact Finset.sum_pos (fun T _ => fockIp_self_re_pos (GlobalTheory.NormAdelic.minorPol_ne_zero T)) (by
      classical exact ⟨fun _ _ => ⟨Fin.castLE had, fun _ _ h => h⟩, by simp⟩)
  rw [h0] at hpos
  exact lt_irrefl _ hpos

end GlobalTheory.NormRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeSemiAbelianDvrNoSpecialTorus
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeSemiAbelianDvrNoSpecialTorus
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ToricRankZero

theorem isProper_of_torusExtension_of_finrank_eq_zero {k : Type} [Field k] (G : Over (Sp k)) [GrpObj G]
    (E : TorusExtension G) (hX : (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0) : IsProper G.hom := by
  letI := E.addCommGroup
  letI := E.free
  letI := E.finite
  letI := E.grpB
  haveI := E.q_hom
  have hsub : Subsingleton E.X := Module.finrank_zero_iff.1 hX
  have hp := E.isKernel
  have : Mono E.q := ⟨fun {Y} x y hxy => by
    have h1 : (x * y⁻¹) ≫ E.q = toUnit _ ≫ η[E.B] := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, hxy, mul_inv_cancel]
      rfl
    have h2 : hp.lift _ _ h1 = 1 := by
      apply (GlobalTheory.splitTorusPointsEquiv (Sp k) E.X Y).injective
      refine MonoidHom.ext fun a => ?_
      have ha1 : a = 1 := by
        show a = Multiplicative.ofAdd 0
        rw [← ofAdd_toAdd a, Subsingleton.elim (Multiplicative.toAdd a) 0]
      rw [ha1, map_one, map_one]
    have h3 := hp.lift_fst _ _ h1
    haveI := E.i_hom
    rw [h2, MonObj.one_comp] at h3
    exact mul_inv_eq_one.1 h3.symm⟩
  have : Mono E.q.left := inferInstanceAs (Mono ((Over.forget _).map E.q))
  have := E.isAbelian.proper
  have : Flat E.q.left := E.q_flat
  have : Surjective E.q.left := E.q_surjective
  have : QuasiCompact E.q.left := E.q_quasiCompact
  have : IsIso E.q.left := Flat.isIso_of_surjective_of_mono E.q.left
  rw [← Over.w E.q]
  infer_instance

theorem isAbelianScheme_of_finrank_eq_zero : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], IsSemiAbelian G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ E : TorusExtension (GlobalTheory.SS.spFibre G), (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0 → IsAbelianScheme G := by
  intro W L _ _ _ _ _ _ G _ hG hgen E hE
  have hS : GlobalTheory.SS.SmConn G := ⟨hG.comm, hG.smooth, hG.separated, hG.quasiCompact, hG.geomConnected⟩
  have hsp : IsProper (GlobalTheory.SS.spFibre G).hom := isProper_of_torusExtension_of_finrank_eq_zero _ E hE
  exact GlobalTheory.SmConnProper.isAbelianScheme_of_smConn_of_isProper _ G hS
    (GlobalTheory.GoodRedProper.isProper_of_proper_fibres W L G hS hgen hsp)

end GlobalTheory.ToricRankZero
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeSemiAbelianDvrNoSpecialTorusStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.UU GlobalTheory.LN GlobalTheory.Raynaud IsLocalRing
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isAbelianScheme_semiAbelian_dvr_noSpecialTorus : ∀ (W L : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field L] [Algebra W L] [IsFractionRing W L] (G : Over (Sp W)) [GrpObj G], IsSemiAbelian G → IsProper ((Over.pullback (spMap (algebraMap W L))).obj G).hom → ∀ E : TorusExtension (GlobalTheory.SS.spFibre G), (letI := E.addCommGroup; Module.finrank ℤ E.X) = 0 → IsAbelianScheme G := by
  first | exact @GlobalTheory.ToricRankZero.isAbelianScheme_of_finrank_eq_zero | exact GlobalTheory.ToricRankZero.isAbelianScheme_of_finrank_eq_zero | (intros; apply GlobalTheory.ToricRankZero.isAbelianScheme_of_finrank_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionPointsPullbackAbelianScheme
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomOver
noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et.CovChar

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

variable {R} {X Y : Scheme.{0}} (f : Y ⟶ X)

end GlobalTheory.Et.CovChar

namespace GlobalTheory.AV.AbVar

open ReciprocityTheory.ChartRestriction.G.Geo.Tor MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory

variable {K : Type} [Field K]

abbrev geomX (A : AbVar K) : Scheme.{0} := GlobalTheory.Et.geom (AlgebraicClosure K) A.X.hom

abbrev geomOver (A : AbVar K) : Over (Sp K) :=
  Over.mk (pullback.fst A.X.hom (spMap (algebraMap K (AlgebraicClosure K))) ≫ A.X.hom)

def transl (A : AbVar K) (a : A.Pt) : geomX A ⟶ geomX A :=
  pullback.lift
    ((lift (Over.homMk (pullback.fst _ _) : geomOver A ⟶ A.X)
      (Over.homMk (pullback.snd _ _ ≫ a.left) (by
        rw [Category.assoc, Over.w a]; exact pullback.condition.symm) : geomOver A ⟶ A.X) ≫ μ[A.X]).left)
    (pullback.snd _ _) (by
      rw [Over.w]; exact pullback.condition)

end GlobalTheory.AV.AbVar
end
end

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.Et GlobalTheory.Et.CovChar
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open GlobalTheory.AV GlobalTheory.AV.AbVar
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KerConst

open GlobalTheory.LevelCompare

theorem finite_etale_ker {S : Scheme.{0}} (A : Over S) [GrpObj A] (k : ℕ)
    (hf : IsFinite (𝟙 A ^ k).left) (he : Etale (𝟙 A ^ k).left) :
    IsFinite (Ker A k).hom ∧ Etale (Ker A k).hom := by
  have h := (IsPullback.of_hasPullback (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A]).map (Over.forget S)
  have h₁ : IsFinite (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k).left := hf
  have h₁' : Etale (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k).left := he
  have h₂ : IsFinite (pullback.snd (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A]).left :=
    MorphismProperty.of_isPullback (P := @IsFinite) h h₁
  have h₂' : Etale (pullback.snd (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A]).left :=
    MorphismProperty.of_isPullback (P := @Etale) h h₁'
  rw [← Over.w (pullback.snd (GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureForms.mulBy A k) η[A])]
  exact ⟨MorphismProperty.comp_mem @IsFinite _ _ h₂ (inferInstanceAs (IsFinite (𝟙 S))),
    by haveI := h₂'; haveI : Etale (𝟙_ (Over S)).hom := inferInstanceAs (Etale (𝟙 S)); infer_instance⟩

end GlobalTheory.KerConst

namespace GlobalTheory.KerConst

open GlobalTheory.LevelCompare

theorem isPullback_const_ker (Ω : Type) [Field Ω] [IsAlgClosed Ω]
    (G : Over (Spec (CommRingCat.of Ω))) [GrpObj G] : IsAbelianScheme G → ∀ (n : ℕ), (n : Ω) ≠ 0 →
    IsPullback (Sigma.desc (f := fun _ : {x : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ G // x ^ n = 1} =>
      𝟙_ (Over (Spec (CommRingCat.of Ω)))) fun x => x.1) (toUnit _) (𝟙 G ^ n) η[G] := by
  intro hG n hn
  have := hG.comm
  have := hG.smooth
  have := hG.proper
  have hu : IsUnit (n : Γ(Spec (CommRingCat.of Ω), ⊤)) := by
    have h1 : IsUnit (n : Ω) := hn.isUnit
    simpa using h1.map (Scheme.ΓSpecIso (CommRingCat.of Ω)).inv.hom
  obtain ⟨hfin, het⟩ := finite_etale_ker G n (GlobalTheory.GrpTangent.isFinite_id_pow G hu)
    (GlobalTheory.GrpTangent.etale_id_pow G hu)
  refine (isKer_iff (A := G) (k := n) (fun x : {x : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ G // x ^ n = 1} => x.1)
    (fun x => x.2)).2 ?_
  haveI := formallyUnramified_ker G hu
  haveI := locallyOfFiniteType_ker G n
  apply isIso_desc_of_lists
  intro K _ _ s u
  letI : Algebra Ω K := (Spec.preimage s).hom.toAlgebra
  have hs : s = spMap (algebraMap Ω K) := (Spec.map_preimage s).symm
  have hts : ∀ (T : Over (Spec (CommRingCat.of Ω))), (toUnit T).left = T.hom := fun T => by
    simpa using Over.w (toUnit T)
  obtain ⟨x₀, hx₀, hx⟩ := GlobalTheory.FinEtPoints.exists_point_of_finite_etale Ω K (Ker G n).left
    (Ker G n).hom hfin het u.left (by rw [Over.w u]; exact hs)
  let t₀ : 𝟙_ (Over (Spec (CommRingCat.of Ω))) ⟶ Ker G n := Over.homMk x₀ hx₀
  have hp : (t₀ ≫ pullback.fst _ _) ^ n = 1 := by
    rw [← comp_mulBy, Category.assoc, pullback.condition, ← Category.assoc, Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  refine existsUnique_of_exists_of_unique ⟨⟨_, hp⟩, ?_⟩ ?_
  · have e : kerPt (t₀ ≫ pullback.fst _ _) hp = t₀ := ker_ext (kerPt_fst _ _)
    show toUnit _ ≫ kerPt (t₀ ≫ pullback.fst _ _) hp = u
    rw [e]
    apply Over.OverMorphism.ext
    rw [Over.comp_left, hts]
    show s ≫ x₀ = u.left
    exact (congrArg (· ≫ x₀) hs).trans hx
  · intro i j hi hj
    have h1 := congrArg (fun v => v ≫ pullback.fst _ _) (hi.trans hj.symm)
    simp only [Category.assoc, kerPt_fst] at h1
    have h2 := congrArg CommaMorphism.left h1
    simp only [Over.comp_left, hts] at h2
    haveI : Epi s := hs ▸ GlobalTheory.FinEtPoints.epi_spMap_field Ω K (algebraMap Ω K)
    exact Subtype.ext (Over.OverMorphism.ext ((cancel_epi s).mp h2))

end GlobalTheory.KerConst
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverse
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

noncomputable section

namespace GlobalTheory.NormRatio.ChrFin

open _root_.Formalism.L2.JoinChr

theorem toFinE_inc (D : D7) (a : D.host.E) :
    GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D a) = algebraMap D.host.E _ a :=
  (GlobalTheory.LFun.toFinAd_tmul 1 a).trans (by rw [map_one, one_mul])

theorem toFinE_int (D : D7) {r : Formalism.MainNotions.StandardLatticesGL3.AE D} (hr : r ∈ Formalism.MainNotions.StandardLatticesGL3.OhE D) (P : HeightOneSpectrum (𝓞 D.host.E)) :
    Valued.v (GlobalTheory.BotFormula.toFinE D r P) ≤ 1 := by
  let S : Subring (Formalism.MainNotions.StandardLatticesGL3.AE D) := (Formalism.UG.intAd D.host.E).comap (GlobalTheory.BotFormula.toFinE D).toRingHom
  have hS : Formalism.MainNotions.StandardLatticesGL3.OhE D ≤ S := by
    refine Subring.closure_le.2 ?_
    rintro z (⟨⟨x, hx⟩, rfl⟩ | ⟨⟨y, hy⟩, rfl⟩)
    · obtain ⟨x', rfl⟩ := hx
      intro Q
      change GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D _) Q ∈ _
      rw [toFinE_inc, HeightOneSpectrum.mem_adicCompletionIntegers]
      change Valued.v ((algebraMap D.host.E (Q.adicCompletion D.host.E)) _) ≤ 1
      exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' Q _).trans_le (Q.valuation_le_one x')
    · intro Q
      have h := (GlobalTheory.LFun.mem_int_iff (F := ℚ) (E := D.host.E) (y ⊗ₜ[ℚ] ((1 : 𝓞 D.host.E) : D.host.E))).1
        (AddSubgroup.subset_closure ⟨y, fun v => hy v, 1, rfl⟩) Q
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact h
  exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).1 (hS hr P)

theorem adEquiv_eq (D : D7) (z : Formalism.MainNotions.StandardLatticesGL3.AE D) :
    GlobalTheory.Mem.Col2.SplitChar.adEquiv D z = GlobalTheory.BotFormula.toFinE D z := by
  refine GlobalTheory.PlaceIdem.adele_ext fun P => ?_
  let f1 : Formalism.MainNotions.StandardLatticesGL3.AE D →+* P.adicCompletion D.host.E :=
    (RestrictedProduct.evalRingHom _ P).comp (GlobalTheory.Mem.Col2.SplitChar.adEquiv D).toRingHom
  let f2 : Formalism.MainNotions.StandardLatticesGL3.AE D →+* P.adicCompletion D.host.E :=
    (RestrictedProduct.evalRingHom _ P).comp (GlobalTheory.BotFormula.toFinE D).toRingHom
  change f1 z = f2 z
  by_contra hne
  have hd : Valued.v (f1 z - f2 z) ≠ 0 := (Valuation.ne_zero_iff _).2 (sub_ne_zero.2 hne)
  obtain ⟨n, hn, hv⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_nat_val_lt P hd
  obtain ⟨a, r, hr, hz⟩ := GlobalTheory.Mem.Col2.SplitChar.exists_approx z hn
  have ha : f1 (Formalism.MainNotions.StandardLatticesGL3.inc D a) = f2 (Formalism.MainNotions.StandardLatticesGL3.inc D a) := by
    change GlobalTheory.Mem.Col2.SplitChar.adEquiv D (Formalism.MainNotions.StandardLatticesGL3.inc D a) P = GlobalTheory.BotFormula.toFinE D (Formalism.MainNotions.StandardLatticesGL3.inc D a) P
    rw [GlobalTheory.Mem.Col2.SplitChar.adEquiv_inc, toFinE_inc]
  have e1 : f1 z - f2 z = (n : P.adicCompletion D.host.E) * (f1 r - f2 r) := by
    rw [hz, map_add (f := _), map_add (f := _), map_mul, map_mul, map_natCast, map_natCast, ha]
    ring
  have h1 : Valued.v (f1 r) ≤ 1 := GlobalTheory.Mem.Col2.SplitChar.vl_le hr P
  have h2 : Valued.v (f2 r) ≤ 1 := toFinE_int D hr P
  have h3 : Valued.v (f1 r - f2 r) ≤ 1 := Valuation.map_sub_le _ h1 h2
  have h4 : Valued.v ((n : P.adicCompletion D.host.E)) = P.valuation D.host.E (n : D.host.E) := by
    rw [← map_natCast (algebraMap D.host.E (P.adicCompletion D.host.E)) n]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P _
  have h5 : Valued.v (f1 z - f2 z) ≤ P.valuation D.host.E (n : D.host.E) := by
    rw [e1, map_mul, h4]
    exact mul_le_of_le_one_right' h3
  exact absurd (h5.trans_lt hv) (lt_irrefl _)

theorem chrEq_of_finPart : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ)
    (ν : Formalism.L2.Host.HChar D.host.E),
    IsHeckeChar D χ → HasFinPart χ c (-e) → (∀ x, c.f x ^ e = (ν⁻¹).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) →
      ChrEq χ ν := by
  intro D χ N c e ν hχ hf hν
  refine ⟨hχ, fun P ε hε k x hx => ?_⟩
  have hι : ∀ x : D.host.E, GlobalTheory.LFun.finAdEquiv D.host.F D.host.E ((1 : Af D.host.F) ⊗ₜ[D.host.F] x) =
      algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) x :=
    fun x => (GlobalTheory.LFun.toFinAd_tmul 1 x).trans (by rw [map_one, one_mul])
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.HeckeTensorRead.isPlIdem_parts D (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E) hι
    GlobalTheory.LFun.mem_int_iff hε
  have hinf : infPart D (x : AE D) = 1 := by
    rw [hx, locE, GlobalTheory.HeckeTensorRead.map_loc (infPart D), h1, zero_mul, add_zero]
  have hfin : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) =
      Neutral.B1.finiteSingle D.host.E P (algebraMap D.host.E _ (k : D.host.E)) := by
    have h4 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (incA D (k : D.host.E))) =
        algebraMap D.host.E _ (k : D.host.E) := hι _
    have h5 : GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (locE D ε (k : D.host.E))) =
        1 + GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D ε) *
          (GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (incA D (k : D.host.E))) - 1) :=
      GlobalTheory.HeckeTensorRead.map_loc ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)) ε _
    rw [hx, h5]
    exact GlobalTheory.HeckeTensorRead.loc_eq_finSingle P _ _ _ h4 h2 h3
  let u : (FiniteAdeleRing (𝓞 D.host.E) D.host.E)ˣ :=
    Units.map ((GlobalTheory.LFun.finAdEquiv D.host.F D.host.E).toRingHom.comp (finPart D)).toMonoidHom x
  let y : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ := Units.map (GlobalTheory.BotFormula.toFinE D).symm.toRingHom.toMonoidHom u
  have hy1 : GlobalTheory.BotFormula.toFinE D (y : Formalism.MainNotions.StandardLatticesGL3.AE D) =
      GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) :=
    (GlobalTheory.BotFormula.toFinE D).apply_symm_apply _
  have hxy : IsFinIdl x y := ⟨hinf, hy1.symm⟩
  have hval := hf x y hxy
  have hy : GlobalTheory.Mem.Col2.SplitChar.finIdl D y = Neutral.B1.localIdele D.host.E P (Formalism.L2.Host.atFin P k) := by
    refine Units.ext (Prod.ext rfl ?_)
    rw [GlobalTheory.Mem.Col2.SplitChar.finIdl_snd, adEquiv_eq, hy1, hfin]
    rfl
  have hc : c.f y ^ (-e) = ν.1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D y) := by
    rw [zpow_neg, hν y]
    rfl
  rw [hval, hc, hy]
  rfl

end GlobalTheory.NormRatio.ChrFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharEqOfFinitePartPowerInverseStatement
open NumberField MeasureTheory IsDedekindDomain UniqueFactorizationMonoid
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open GlobalTheory.NormSum (Pair Tup minorPol ratG intG Cls gam)
open GlobalTheory.NormDict GlobalTheory.NormExact GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum
open GlobalTheory.SqTop (modT)
open GlobalTheory.BottomIPData (sfB)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl Lat IsFockVec IsSphOff volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip)
open GlobalTheory.Core.Rk.IP (openOff integrand wcoef)
open GlobalTheory.StdLoc (glVol blockIdx)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.NormRatio

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeCharEq_of_finitePart_power_inverse : ∀ {D : D7} (χ : (AE D)ˣ →* Circle) {N : ℕ} (c : Formalism.MainNotions.StandardLatticesGL3.HeckeU D N) (e : ℤ) (ν : Formalism.L2.Host.HChar D.host.E),
  IsHeckeChar D χ → HasFinPart χ c (-e) → (∀ x, c.f x ^ e = (ν⁻¹).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x)) → ChrEq χ ν := by
  first | exact @GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart | exact GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart | (intros; apply GlobalTheory.NormRatio.ChrFin.chrEq_of_finPart <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossFinsetSumAndInvPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossFinsetSumAndInvPow
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

namespace GlobalTheory.LossSum

theorem lossLe_sum_and_pow : ∀ {D : D7} (w : PlL D),
    (∀ {ι : Type} (s : Finset ι) (z : ι → ℂ) (a : ℝ), (∀ i ∈ s, LossLe w (z i) a) → LossLe w (∑ i ∈ s, z i) a) ∧
    ∀ q M : ℕ, 0 < q → LossLe w ((((q : ℝ)⁻¹ ^ M : ℝ)) : ℂ) ((M : ℝ) * (vw w ((q : ℕ) : D.what₂.LL) : ℝ)) := by
  intro D w
  refine ⟨?_, ?_⟩
  · intro ι s z a h
    classical
    induction s using Finset.induction_on with
    | empty => exact ⟨0, by simp, Or.inl rfl⟩
    | insert j s hj ih =>
      rw [Finset.sum_insert hj]
      obtain ⟨y1, e1, h1⟩ := h j (Finset.mem_insert_self _ _)
      obtain ⟨y2, e2, h2⟩ := ih fun i hi => h i (Finset.mem_insert_of_mem hi)
      refine ⟨y1 + y2, by rw [map_add (f := _), e1, e2], ?_⟩
      by_cases hy1 : y1 = 0
      · subst hy1; simpa using h2
      by_cases hy2 : y2 = 0
      · subst hy2; simpa using h1
      have h1' := h1.resolve_left hy1
      have h2' := h2.resolve_left hy2
      by_cases h3 : y1 + y2 = 0
      · exact Or.inl h3
      right
      have h4 := Formalism.AtG.ValuationJets.vw_add w y1 y2 hy1 hy2 h3
      have h5 : ((min (vw w y1) (vw w y2) : ℤ) : ℝ) ≤ (vw w (y1 + y2) : ℝ) := by exact_mod_cast h4
      push_cast at h5
      exact le_trans (le_min h1' h2') h5
  · intro q M hq
    refine ⟨((q : D.what₂.LL)⁻¹) ^ M, by push_cast; simp, Or.inr ?_⟩
    have hq0 : ((q : D.what₂.LL)⁻¹) ≠ 0 := inv_ne_zero (by exact_mod_cast hq.ne')
    rw [GlobalTheory.ScalAA.vw_pow' w hq0, GlobalTheory.ScalAA.vw_inv']
    push_cast; ring_nf; rfl

end GlobalTheory.LossSum
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffValuationLossFinsetSumAndInvPowStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RowTest GlobalTheory.SumSize GlobalTheory.RowClaim
open Formalism.DivisionValues (vw lw)
open MeasureTheory ValuativeRel GlobalTheory.UnfoldLoss

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.FunObj.borelKw
  GlobalTheory.FunObj.borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coeffValuationLoss_finsetSum_and_invPow : ∀ {D : D7} (w : PlL D),
    (∀ {ι : Type} (s : Finset ι) (z : ι → ℂ) (a : ℝ), (∀ i ∈ s, LossLe w (z i) a) → LossLe w (∑ i ∈ s, z i) a) ∧
    ∀ q M : ℕ, 0 < q → LossLe w ((((q : ℝ)⁻¹ ^ M : ℝ)) : ℂ) ((M : ℝ) * (vw w ((q : ℕ) : D.what₂.LL) : ℝ)) := by
  first | exact @GlobalTheory.LossSum.lossLe_sum_and_pow | exact GlobalTheory.LossSum.lossLe_sum_and_pow | (intros; apply GlobalTheory.LossSum.lossLe_sum_and_pow <;> assumption)
end
end
