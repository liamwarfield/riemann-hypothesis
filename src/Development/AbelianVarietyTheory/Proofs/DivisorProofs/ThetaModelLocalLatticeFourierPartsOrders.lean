module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatTensorSupportBoundedByUniformizerPow
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEighthPowerTraitLatticeEquivLocalExt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveLatticeCoordMapEquivariantDvr
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAdicCompletion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinimalPsiCoordinateAssociatedFourierPower

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankFormMinimalTuplesAtClosedPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveDiagonalLatticeMapTrait
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveDiagonalLatticeMapTrait
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.TraitOne

theorem factor_stalk (X : Scheme.{0}) (x : X) (V : Type) [CommRing V] [IsLocalRing V] (ξ : Sp V ⟶ X)
    (hx : ξ (IsLocalRing.closedPoint V) ⤳ x) :
    ∃ f : X.presheaf.stalk x →+* V, spMap f ≫ X.fromSpecStalk x = ξ := by
  refine ⟨(Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.stalkSpecializes hx).hom, ?_⟩
  have e1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk ξ
  have e2 := Scheme.SpecMap_stalkSpecializes_fromSpecStalk hx
  conv_rhs => rw [← e1, ← e2]
  show Spec.map (CommRingCat.ofHom _) ≫ _ = _
  rw [← Category.assoc, ← Spec.map_comp]
  rfl

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (a : A →+* B) (b : B →+* C) :
    spMap (b.comp a) = spMap b ≫ spMap a := by
  rw [← Spec.map_comp]
  rfl

theorem subset_abLocus {o' Ω : Type} [CommRing o'] [Field Ω] [Algebra o' Ω] {S : ThetaSys o' Ω} {ρ : S.Real}
    {M : RatModel o' Ω} {U₀ : M.Z.Opens} {EE : M.Lat S.J} (FinalForm : ZHOut ρ M U₀ EE) :
    (U₀ : Set M.Z) ⊆ abLocus FinalForm.G := by
  intro z hz
  obtain ⟨z', rfl⟩ : z ∈ Set.range U₀.ι := by rw [Scheme.Opens.range_ι]; exact hz
  rw [abLocus_pullback (G' := (Over.pullback FinalForm.u₀).obj ρ.P.A) abLocusOne FinalForm.semi FinalForm.cart.1]
  intro K _ _ t _
  haveI := ρ.P.isAb.proper
  show IsProper (pullback.snd (pullback.snd ρ.P.A.hom FinalForm.u₀) t)
  infer_instance

theorem main : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X), (∀ a b, ∃ (f : FinalForm.G ⟶ FinalForm.G) (fR : G ⟶ G), MatOn FinalForm pr a b f ∧ IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left ∧ EndChar U fR (m a b)) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : T.V →+* V') (g' : R →+* V') (ρT : D.toPre.X →+ (Fin 8 → T.D.toPre.X)), Function.Injective h ∧ Irreducible (h T.ϖ) ∧ spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ ∧ Function.Surjective ρT ∧ (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (g' r) (h T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  intro g n hg hn hodd F W hW o' Ω _ _ _ hA S ρ hBig M U₀ EE FinalForm hAdm hEE x hx u c pr hS R _ _ _ j hR hj G _ _ gm hgm
    D A U hLB hPsi m hm T ξ hξU hsp
  set ξR : Sp R ⟶ M.Z := spMap j ≫ M.Z.fromSpecStalk x with hξR
  obtain ⟨hft, hpj⟩ := GlobalTheory.UPoinc.ClosedPt.closedPoint_cpl_residueChar o' Ω M x hx
  obtain ⟨-, p, hp, hpm⟩ := hpj R j hj
  obtain ⟨f, hf⟩ := factor_stalk M.Z x T.V ξ hsp
  obtain ⟨V', _, _, _, h, g', hc, hinj, hloc, hcomp, hirr⟩ :=
    GlobalTheory.TraitLift.exists_lift_of_isCpl (M.Z.presheaf.stalk x) R T.V j hj f
  have heq : spMap g' ≫ ξR = spMap h ≫ ξ := by
    rw [hξR, ← hf, ← Category.assoc, ← Category.assoc, ← spMap_comp', ← spMap_comp', hcomp]
  haveI : CharZero V' := (RingHom.charZero_iff hinj).1 inferInstance
  have hBV : GlobalTheory.Mum.Base V' := ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩
  have hle : nonZeroDivisors T.V ≤ (nonZeroDivisors V').comap h :=
    nonZeroDivisors_le_comap_nonZeroDivisors_of_injective h hinj
  let hK : FractionRing T.V →+* FractionRing V' := IsLocalization.map (FractionRing V') h hle
  have hKc : ∀ a, hK (algebraMap T.V _ a) = algebraMap V' _ (h a) := IsLocalization.map_eq hle
  have hjK : spMap hK ≫ jK T.V = jK V' ≫ spMap h := by
    show spMap hK ≫ spMap (algebraMap T.V (FractionRing T.V)) = spMap (algebraMap V' (FractionRing V')) ≫ spMap h
    rw [← spMap_comp', ← spMap_comp']
    congr 1
    ext a
    exact hKc a
  obtain ⟨ξ₀, hξ₀, hξ₀y⟩ := hξU
  set ξ' : Sp V' ⟶ M.Z := spMap g' ≫ ξR with hξ'
  have hξ₀' : (spMap hK ≫ ξ₀) ≫ U₀.ι = jK V' ≫ ξ' := by
    rw [Category.assoc, hξ₀, ← Category.assoc, hjK, Category.assoc, heq]
  have hsub := subset_abLocus FinalForm
  let w' : Sp V' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum V')
  have hw'U : ξ' w' ∈ (U₀ : Set M.Z) := by
    have e1 : w' = jK V' (IsLocalRing.closedPoint (FractionRing V')) := by
      apply PrimeSpectrum.ext
      show (⊥ : Ideal V') = Ideal.comap (algebraMap V' (FractionRing V')) (IsLocalRing.closedPoint (FractionRing V')).asIdeal
      rw [Ideal.eq_bot_of_prime (IsLocalRing.closedPoint (FractionRing V')).asIdeal, ← RingHom.ker_eq_comap_bot]
      exact ((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective V' (FractionRing V'))).symm
    rw [e1]
    show (jK V' ≫ ξ') (IsLocalRing.closedPoint (FractionRing V')) ∈ (U₀ : Set M.Z)
    rw [← hξ₀']
    show U₀.ι ((spMap hK ≫ ξ₀) (IsLocalRing.closedPoint (FractionRing V'))) ∈ (U₀ : Set M.Z)
    rw [← Scheme.Opens.range_ι]
    exact ⟨_, rfl⟩
  obtain ⟨D', A', U', hLB', hPsi'⟩ := FinalForm.unif V' inferInstance inferInstance hc ξ' ⟨w', hsub hw'U⟩
  have hG'semi : IsSemiAbelian ((Over.pullback ξ').obj FinalForm.G) := IsSemiAbelian.pullback ξ' FinalForm.G FinalForm.semi
  have hpb' := isGrpPullback_pullback FinalForm.G ξ'
  have h'' : IsGrpPullback ((Over.pullback (spMap g')).obj G) FinalForm.G ξ' (pullback.fst G.hom (spMap g') ≫ gm) :=
    (isGrpPullback_pullback G (spMap g')).comp hgm
  obtain ⟨e, he1, he2⟩ := grpPullback_iso hpb' h''
  haveI := he1
  set β : ((Over.pullback ξ').obj FinalForm.G).left ⟶ G.left := e.hom.left ≫ pullback.fst G.hom (spMap g') with hβdef
  have hβ : IsGrpPullback ((Over.pullback ξ').obj FinalForm.G) G (spMap g') β :=
    ((isGrpPullback_of_iso e).comp (isGrpPullback_pullback G (spMap g'))).congr (Category.id_comp _) rfl
  have hβgm : β ≫ gm = pullback.fst FinalForm.G.hom ξ' := by
    rw [hβdef, Category.assoc, he2]
  clear_value β
  have hGsemi : IsSemiAbelian G := by
    obtain ⟨e2, he21, -⟩ := grpPullback_iso hgm (isGrpPullback_pullback FinalForm.G ξR)
    haveI := he21
    exact GlobalTheory.isSemiAbelian_of_grpIso e2 (IsSemiAbelian.pullback ξR FinalForm.G FinalForm.semi)
  have hLBβ : LBIso U'.LG.L (U.LG.L.pull β) := by
    have h1 : LBIso (U.LG.L.pull β) (FinalForm.L.L.pull (pullback.fst FinalForm.G.hom ξ')) :=
      GlobalTheory.Ex.GenericFibre.lbIso_pull hLB β hβgm.symm
    exact LBIso.trans U'.LG.isLB (pull_isLB FinalForm.L.isLB _) (pull_isLB U.LG.isLB _) hLB' (LBIso.symm h1)
  have hWo : IsOpen (ξR ⁻¹' (U₀ : Set M.Z)) := U₀.isOpen.preimage ξR.continuous
  have hPsiWo : ∀ y, PsiUnitOn D.toPre y (ξR ⁻¹' (U₀ : Set M.Z)) := fun y j' V hV hVW =>
    hPsi y j' V hV (hVW.trans (Set.preimage_mono hsub))
  have hker : (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) ∈ ξR ⁻¹' (U₀ : Set M.Z) := by
    have e3 : (⟨RingHom.ker g', RingHom.ker_isPrime g'⟩ : PrimeSpectrum R) = spMap g' w' :=
      PrimeSpectrum.ext (RingHom.ker_eq_comap_bot g')
    show ξR _ ∈ (U₀ : Set M.Z)
    rw [e3]
    exact hw'U
  obtain ⟨ρ0, hsurj, hcoord, hequiv⟩ := GlobalTheory.T.exists_surjective_lattice_coordMap_equivariant_dvr R hR G hGsemi D A U V' hBV inferInstance
    ((Over.pullback ξ').obj FinalForm.G) hG'semi D' A' U' g' β p hp hpm _ hWo hPsiWo hker hβ hLBβ
  obtain ⟨c', pr', hS', hmat⟩ := GlobalTheory.Poinc.Eq8.PullAlong.main g n _ _ F W o' Ω S ρ u c pr hS M U₀ EE FinalForm V' hBV
    ((Over.pullback ξ').obj FinalForm.G) hG'semi D' A' U' ξ' (pullback.fst FinalForm.G.hom ξ') hpb' hLB' (spMap hK ≫ ξ₀) hξ₀'
  have hpt : (spMap hK ≫ ξ₀) ≫ FinalForm.u₀ ≫ u = spMap hK ≫ T.y := by
    rw [Category.assoc, hξ₀y]
  have key : ∀ (v : Sp (FractionRing V') ⟶ F.X), v = spMap hK ≫ T.y → ∀ c₁ pr₁, SharpBy F W A' v c₁ pr₁ →
      ∃ e : D'.toPre.X ≃+ (Fin 8 → T.D.toPre.X), (∀ y r, PsiCoord D'.toPre y r → 0 ≤ qW W T.β (e y) ∧
        Associated r (h T.ϖ ^ (qW W T.β (e y)).toNat)) ∧ ∀ (a b : Fin 8) (f : (Over.pullback ξ').obj FinalForm.G ⟶ (Over.pullback ξ').obj FinalForm.G)
        (f₁ : A'.A ⟶ A'.A) (m : D'.toPre.X →+ D'.toPre.X), IsMonHom f → MatEnd pr₁ a b f₁ →
        (Over.pullback (jK V')).map f ≫ U'.gen.hom = U'.gen.hom ≫ f₁ → EndChar U' f m → ∀ y, MatRel W a b (e y) (e (m y)) := by
    rintro v rfl c₁ pr₁ hS₁
    exact GlobalTheory.T.exists_eighthPowerTrait_lattice_equiv_localExt g n _ _ F W hW T V' hBV inferInstance _ hG'semi D' A' U' h hK hloc hKc c₁ pr₁ hS₁
  obtain ⟨e8, hord, hrel⟩ := key _ hpt c' pr' hS'
  refine ⟨V', inferInstance, inferInstance, inferInstance, h, g', e8.toAddMonoidHom.comp ρ0, hinj, hirr _ T.irr, heq,
    e8.surjective.comp hsurj, ?_, ?_⟩
  · intro y r hr
    obtain ⟨⟨r', hr', -⟩, -⟩ := GlobalTheory.PsiCoordLocal.main V' D' inferInstance (ρ0 y)
    obtain ⟨h0, has⟩ := hord (ρ0 y) r' hr'
    exact ⟨h0, (hcoord y r r' hr hr').trans has⟩
  · intro a b y
    obtain ⟨f, fR, hMO, hfR, hcomm, hEC⟩ := hm a b
    haveI : IsMonHom f := hMO.1
    let f' : (Over.pullback ξ').obj FinalForm.G ⟶ (Over.pullback ξ').obj FinalForm.G := (Over.pullback ξ').map f
    have hf'fst : f'.left ≫ pullback.fst FinalForm.G.hom ξ' = pullback.fst FinalForm.G.hom ξ' ≫ f.left := pullback.lift_fst _ _ _
    have hf' : IsMonHom f' := PullGtPf.isMonHom_of_grpPullback hpb' hpb' f f' hf'fst
    have hf'β : f'.left ≫ β = β ≫ fR.left := by
      apply hgm.1.hom_ext
      · calc (f'.left ≫ β) ≫ gm = f'.left ≫ (β ≫ gm) := Category.assoc _ _ _
          _ = pullback.fst FinalForm.G.hom ξ' ≫ f.left := by rw [hβgm, hf'fst]
          _ = (β ≫ gm) ≫ f.left := by rw [hβgm]
          _ = (β ≫ fR.left) ≫ gm := by rw [Category.assoc, Category.assoc, hcomm]
      · calc (f'.left ≫ β) ≫ G.hom = f'.left ≫ (β ≫ G.hom) := Category.assoc _ _ _
          _ = ((Over.pullback ξ').obj FinalForm.G).hom ≫ spMap g' := by rw [hβ.1.w, ← Category.assoc, Over.w f']
          _ = β ≫ G.hom := hβ.1.w.symm
          _ = (β ≫ fR.left) ≫ G.hom := by rw [Category.assoc, Over.w fR]
    obtain ⟨m', hm'⟩ := endChar_exists_of_isMonHom V' hBV _ hG'semi D' A' U' f' hf'
    have hq := hequiv fR f' hfR hf' hf'β (m a b) m' hEC hm' y
    obtain ⟨f₁, hf₁, hf₁c⟩ := hmat a b f f' hMO hf'fst
    have hr := hrel a b f' f₁ m' hf' hf₁ hf₁c hm' (ρ0 y)
    simpa [hq] using hr

end GlobalTheory.Poinc.Eq8.TraitOne
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSurjectiveDiagonalLatticeMapTraitStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_surjective_diagonal_lattice_map_trait : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real), S.Big → ∀ (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∀ (u : Sp S.R ⟶ F.X) c pr, SharpBy F W ρ.P u c pr → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (j : M.Z.presheaf.stalk x →+* R), GlobalTheory.Mum.Base R → IsCpl j → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G] (gm : G.left ⟶ FinalForm.G.left), IsGrpPullback G FinalForm.G (spMap j ≫ M.Z.fromSpecStalk x) gm → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G), LBIso U.LG.L (FinalForm.L.L.pull gm) → (∀ y, PsiUnitOn D.toPre y ((spMap j ≫ M.Z.fromSpecStalk x) ⁻¹' abLocus FinalForm.G)) → ∀ m : Fin 8 → Fin 8 → (D.toPre.X →+ D.toPre.X), (∀ a b, ∃ (f : FinalForm.G ⟶ FinalForm.G) (fR : G ⟶ G), MatOn FinalForm pr a b f ∧ IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left ∧ EndChar U fR (m a b)) → ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (h : T.V →+* V') (g' : R →+* V') (ρT : D.toPre.X →+ (Fin 8 → T.D.toPre.X)), Function.Injective h ∧ Irreducible (h T.ϖ) ∧ spMap g' ≫ (spMap j ≫ M.Z.fromSpecStalk x) = spMap h ≫ ξ ∧ Function.Surjective ρT ∧ (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (g' r) (h T.ϖ ^ (qW W T.β (ρT y)).toNat)) ∧ ∀ a b y, MatRel W a b (ρT y) (ρT (m a b y)) := by
  first | exact @GlobalTheory.Poinc.Eq8.TraitOne.main | exact GlobalTheory.Poinc.Eq8.TraitOne.main | (intros; apply GlobalTheory.Poinc.Eq8.TraitOne.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankFormMinimalTuplesAtClosedPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Clocx

theorem exists_pull_endo {S S' : Scheme.{0}} {s : S' ⟶ S} {G : Over S'} {H : Over S} [GrpObj G] [GrpObj H]
    {gm : G.left ⟶ H.left} (hp : IsGrpPullback G H s gm) (f : H ⟶ H) [IsMonHom f] :
    ∃ fR : G ⟶ G, IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left := by
  let l : G.left ⟶ G.left := hp.1.lift (gm ≫ f.left) G.hom (by rw [Category.assoc, Over.w f, hp.1.w])
  let fR : G ⟶ G := Over.homMk l (hp.1.lift_snd _ _ _)
  have e : fR.left ≫ gm = gm ≫ f.left := hp.1.lift_fst _ _ _
  exact ⟨fR, PullGtPf.isMonHom_of_grpPullback hp hp f fR e, e⟩

theorem isSemiAbelian_of_isGrpPullback {S S' : Scheme.{0}} {s : S' ⟶ S} {G : Over S'} {H : Over S} [GrpObj G]
    [IsCommMonObj G] [GrpObj H] {gm : G.left ⟶ H.left} (hp : IsGrpPullback G H s gm) (hH : IsSemiAbelian H) :
    IsSemiAbelian G := by
  let e : G ≅ (Over.pullback s).obj H := Over.isoMk hp.1.isoPullback (by simp)
  haveI : IsMonHom e.hom := PullGtPf.isMonHom_of_grpPullback hp (isGrpPullback_pullback H s) (𝟙 H) e.hom
    (by simp [e])
  exact GlobalTheory.isSemiAbelian_of_grpIso e (IsSemiAbelian.pullback s H hH)

theorem le_of_assoc_pow {V' : Type} [CommRing V'] [IsDomain V'] {p x y : V'} (hp : Irreducible p) {a b : ℤ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : Associated x (p ^ a.toNat)) (hy : Associated y (p ^ b.toNat)) (hxy : x ∣ y) :
    a ≤ b := by
  have h1 : p ^ a.toNat ∣ p ^ b.toNat := (hx.symm.dvd.trans hxy).trans hy.dvd
  rw [pow_dvd_pow_iff hp.ne_zero hp.not_isUnit] at h1
  omega

theorem congMod_iff {X A B : Type} [AddCommGroup X] (φ : X ≃+ (A → B → ℤ)) (N : ℕ) (y y' : X) :
    CongMod N y y' ↔ ∀ u i, (N : ℤ) ∣ φ y u i - φ y' u i := by
  constructor
  · rintro ⟨w, rfl⟩ u i
    exact ⟨φ w u i, by simp [map_add (f := _), map_nsmul]⟩
  · intro h
    choose d hd using h
    refine ⟨φ.symm d, φ.injective ?_⟩
    funext u i
    have := hd u i
    simp only [map_add (f := _), map_nsmul, AddEquiv.apply_symm_apply]
    change φ y u i = φ y' u i + N • d u i
    rw [nsmul_eq_mul]
    linarith

theorem mem_maximalIdeal_of_square {X : Scheme.{0}} (x : X) [IsNoetherianRing (X.presheaf.stalk x)] {R : Type}
    [CommRing R] [IsLocalRing R] (j : X.presheaf.stalk x →+* R) (hj : IsCpl j) {V V' : Type} [CommRing V]
    [IsLocalRing V] [CommRing V'] [IsLocalRing V'] (h : V →+* V') [IsLocalHom h] (g' : R →+* V') (ξ : Sp V ⟶ X)
    (hξ : ξ (closedPoint V) = x) (hsq : spMap g' ≫ spMap j ≫ X.fromSpecStalk x = spMap h ≫ ξ) :
    ∀ r ∈ maximalIdeal R, g' r ∈ maximalIdeal V' := by
  obtain ⟨pV, hpV⟩ : ∃ p : Sp V', p = IsLocalRing.closedPoint V' := ⟨_, rfl⟩
  have hpt := congrArg (fun φ : Sp V' ⟶ X => φ pV) hsq
  simp only [Scheme.Hom.comp_apply] at hpt
  have h1 : (spMap h) pV = closedPoint V := hpV ▸ IsLocalRing.comap_closedPoint h
  rw [h1, hξ] at hpt
  have h2 := (X.fromSpecStalk x).isEmbedding.injective (hpt.trans (Scheme.fromSpecStalk_closedPoint (x := x)).symm)

  have h3 : (maximalIdeal (X.presheaf.stalk x)) ≤ (maximalIdeal V').comap (g'.comp j) := by
    have := congrArg PrimeSpectrum.asIdeal h2
    intro a ha
    have e : ((spMap j) ((spMap g') pV)).asIdeal = (maximalIdeal V').comap (g'.comp j) := by subst hpV; rfl
    rw [← e, this]
    exact ha
  obtain ⟨e, he⟩ := hj
  have hm : maximalIdeal R ≤ (maximalIdeal (X.presheaf.stalk x)).map j := by
    intro r hr
    have hr' : e.symm r ∈ maximalIdeal (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) := by
      intro hu
      exact hr (by simpa using hu.map e)
    rw [AdicCompletion.maximalIdeal_eq_map] at hr'
    have := Ideal.mem_map_of_mem (e : _ →+* R) hr'
    rw [Ideal.map_map] at this
    have hj' : (e : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) →+* R).comp
        (algebraMap _ _) = j := RingHom.ext fun a => he a
    rw [hj'] at this
    simpa using this
  intro r hr
  have h4 : (maximalIdeal (X.presheaf.stalk x)).map (g'.comp j) ≤ maximalIdeal V' := Ideal.map_le_iff_le_comap.2 h3
  rw [← Ideal.map_map] at h4
  exact h4 (Ideal.mem_map_of_mem g' (hm hr))

end GlobalTheory.Poinc.Clocx

namespace GlobalTheory.Poinc.Clocx

theorem ordEq_of_assoc {g n : ℕ} {o : Type} [CommRing o] {ζ : o} {F : SFam g n ζ} {o' Ω : Type} [CommRing o']
    [Field Ω] [Algebra o' Ω] (M : RatModel o' Ω) (x : M.Z) (T : Trait F) (ξ : Sp T.V ⟶ M.Z)
    (hs : ξ (IsLocalRing.closedPoint T.V) ⤳ x) {V' : Type} [CommRing V'] [IsDomain V'] (h : T.V →+* V')
    (g' : M.Z.presheaf.stalk x →+* V') (hinj : Function.Injective h) (hirr : Irreducible (h T.ϖ))
    (hsq : spMap g' ≫ M.Z.fromSpecStalk x = spMap h ≫ ξ) (a : M.Z.presheaf.stalk x) (q : ℕ)
    (ha : Associated (g' a) (h T.ϖ ^ q)) : OrdEq M T ξ (M.stalkHom x a) q := by
  set v := RatModel.valLoc ξ x hs (M.stalkEquiv x a) with hv
  have e1 : M.val (jK T.V ≫ ξ) (M.stalkHom x a) = algebraMap T.V (FractionRing T.V) v :=
    RatModel.val_spMap_comp (algebraMap T.V (FractionRing T.V)) ξ hs (M.stalkEquiv x a)
  have e2 : M.val (spMap ((algebraMap V' (FractionRing V')).comp h) ≫ ξ) (M.stalkHom x a) =
      (algebraMap V' (FractionRing V')).comp h v :=
    RatModel.val_spMap_comp _ ξ hs (M.stalkEquiv x a)
  have e3 : spMap ((algebraMap V' (FractionRing V')).comp h) ≫ ξ = jK V' ≫ spMap g' ≫ M.Z.fromSpecStalk x := by
    rw [hsq, ← Category.assoc]
    congr 1
    rw [← Spec.map_comp]
    rfl
  rw [e3, GlobalTheory.Poinc.Sep.GalVal.val_stalkHom] at e2
  have e4 : h v = g' a := (IsFractionRing.injective V' (FractionRing V') e2).symm
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, map_zero] at e4
    rw [← e4] at ha
    exact pow_ne_zero q hirr.ne_zero (ha.eq_zero_iff.1 rfl)
  obtain ⟨k, u, hku⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hv0 T.irr
  have hk : k = q := by
    have h5 : Associated (h T.ϖ ^ k) (h T.ϖ ^ q) := by
      have : Associated (h T.ϖ ^ k) (h v) := by
        rw [hku, map_mul, map_pow]
        exact ⟨(Units.map h.toMonoidHom u), by simp [mul_comm]⟩
      exact (this.trans (e4 ▸ ha))
    apply le_antisymm
    · exact (pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h5.dvd
    · exact (pow_dvd_pow_iff hirr.ne_zero hirr.not_isUnit).1 h5.symm.dvd
  refine ⟨u, ?_⟩
  rw [e1, hku, hk, mul_comm]

theorem isLocalHom_of_irreducible {V V' : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CommRing V']
    (h : V →+* V') {ϖ : V} (hϖ : Irreducible ϖ) (hh : Irreducible (h ϖ)) : IsLocalHom h := by
  refine ⟨fun a ha => ?_⟩
  by_contra hna
  have hm : a ∈ maximalIdeal V := hna
  rw [(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).1 hϖ, Ideal.mem_span_singleton] at hm
  obtain ⟨b, rfl⟩ := hm
  rw [map_mul] at ha
  exact hh.not_isUnit (isUnit_of_mul_isUnit_left ha)

end GlobalTheory.Poinc.Clocx


open GlobalTheory.Poinc.Clocx GlobalTheory.Poinc.Eq8.DiagMat in
theorem GlobalTheory.Poinc.Clocx.exists_at_closedPoint : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∀ (_ : NeZero S.N) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (r : ℕ) (b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : (Fin 8 → Fin r → ZMod S.N) → (Fin 8 → Fin r → ℤ)) (e : (Fin 8 → Fin r → ZMod S.N) → Ω), r ≤ g ∧ (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧ (∀ c u i, ((μ c u i : ℤ) : ZMod S.N) = c u i) ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) ∧ (∀ c, e c ≠ 0 ∧ ∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e c = S.FF T₀ c' κ / S.th x₀) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : (Fin r → ℤ) →+ T.D.toPre.X, Function.Surjective π ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) α) ∧ ∀ c, 0 ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ∧ OrdEq M T ξ (e c ^ S.N) (qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c)).toNat := by
  intro g n hg hn hodd F W hW o' Ω _ _ _ _ S ρ u hBig hsharp _ hN M U₀ EE FinalForm hAdm hEE x hx
  have hU : (U₀ : Set M.Z).Nonempty := hAdm.1.ne
  obtain ⟨c, pr, hSB⟩ := (sharpOver_iff F W ρ.P u).1 hsharp
  obtain ⟨R, _, _, _, j, G, _, _, gm, D, A, U, hB, hcpl, hpb, hLB, hpsiU⟩ :=
    GlobalTheory.Poinc.CompletedStalk.exists_completion_unif o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx
  haveI : CharZero R := hB.2
  have hRi : IsIntegrallyClosed R := hB.1.2.2.1
  have hGsemi : IsSemiAbelian G := isSemiAbelian_of_isGrpPullback hpb FinalForm.semi
  have hm : ∀ a b, ∃ (mab : D.toPre.X →+ D.toPre.X), ∃ (f : FinalForm.G ⟶ FinalForm.G) (fR : G ⟶ G), MatOn FinalForm pr a b f ∧
      IsMonHom fR ∧ fR.left ≫ gm = gm ≫ f.left ∧ EndChar U fR mab := by
    intro a b
    obtain ⟨f, hf⟩ := matOn_exists o' Ω S ρ M U₀ EE FinalForm hU c.A pr hSB.2.1 hSB.2.2.1 a b
    haveI : IsMonHom f := hf.1
    obtain ⟨fR, hfR, hfR'⟩ := exists_pull_endo hpb f
    obtain ⟨mab, hmab⟩ := endChar_exists_of_isMonHom R hB G hGsemi D A U fR hfR
    exact ⟨mab, f, fR, hf, hfR, hfR', hmab⟩
  choose m hm using hm
  have key := fun (T : Trait F) (ξ : Sp T.V ⟶ M.Z) (hT : ThroughU M U₀ FinalForm.u₀ u T ξ)
      (hs : ξ (IsLocalRing.closedPoint T.V) ⤳ x) =>
    GlobalTheory.T.exists_surjective_diagonal_lattice_map_trait g n hg hn hodd F W hW o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx u c pr hSB R j hB hcpl G gm hpb D A U
      hLB hpsiU m hm T ξ hT hs

  obtain ⟨T₀, ξ₀, hT₀, hξ₀⟩ :=
    GlobalTheory.Poinc.TraitCen.exists_trait_cen g n _ (zetaAway n) F o' Ω M U₀ hU (Sp S.R) FinalForm.u₀ u x hx
  obtain ⟨V₀, _, _, _, h₀, g₀, ρ₀, hh₀, hirr₀, hsq₀, hρ₀s, hord₀, hrel₀⟩ := key T₀ ξ₀ hT₀ (hξ₀ ▸ specializes_rfl)
  haveI := GlobalTheory.Poinc.TraitCen.isNoetherianRing_stalk M x
  haveI := isLocalHom_of_irreducible h₀ T₀.irr hirr₀
  have hloc₀ := mem_maximalIdeal_of_square x j hcpl h₀ g₀ ξ₀ hξ₀ hsq₀
  have hρ₀i : Function.Injective ρ₀ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hy0
    obtain ⟨r, hr, -, hrm, -⟩ := (GlobalTheory.PsiCoordLocal.main R D hRi y).1
    have h1 := (hord₀ y r hr).2
    have h0 : qW W T₀.β (ρ₀ y) = 0 := by rw [hy]; simp [qW]
    rw [h0, Int.toNat_zero, pow_zero, associated_one_iff_isUnit] at h1
    exact (hloc₀ r (hrm hy0)) h1
  let e₀ : D.toPre.X ≃+ (Fin 8 → T₀.D.toPre.X) := AddEquiv.ofBijective ρ₀ ⟨hρ₀i, hρ₀s⟩
  let rk := Module.finrank ℤ T₀.D.toPre.X
  let ι : T₀.D.toPre.X ≃ₗ[ℤ] (Fin rk → ℤ) := (Module.finBasis ℤ T₀.D.toPre.X).equivFun
  let κE : D.toPre.X ≃+ (Fin 8 → Fin rk → ℤ) := e₀.trans (AddEquiv.piCongrRight fun _ => ι.toAddEquiv)
  have hκ : ∀ y u, κE y u = ι (ρ₀ y u) := fun _ _ => rfl
  have hκ' : ∀ y u, ι.symm (κE y u) = ρ₀ y u := fun y u => by rw [hκ]; exact ι.symm_apply_apply _
  let cz : (Fin 8 → Fin rk → ZMod S.N) → (Fin 8 → Fin rk → ℤ) := fun cl u i => ((cl u i).val : ℤ)
  have hcz : ∀ cl u i, ((cz cl u i : ℤ) : ZMod S.N) = cl u i := fun cl u i => by simp [cz]
  have hQ : ∀ cl : Fin 8 → Fin rk → ZMod S.N, ∃ (mu : D.toPre.X) (ee : Ω) (aa : M.Z.presheaf.stalk x),
      CongMod S.N mu (κE.symm (cz cl)) ∧
      (∀ α, CongMod S.N α (κE.symm (cz cl)) → ∀ r s, PsiCoord D.toPre mu r → PsiCoord D.toPre α s → r ∣ s) ∧
      ee ≠ 0 ∧ (∃ (T₁ : AddSubgroup S.Gam) (c' : T₁ →+ ZMod S.N) (κ : S.J × (T₁ → ZMod ((S.r * S.N) ^ 2)))
        (x₀ : S.Gam), S.IsoFree T₁ ∧ ee = S.FF T₁ c' κ / S.th x₀) ∧
      M.stalkHom x aa = ee ^ S.N ∧ ∀ r, PsiCoord D.toPre mu r → Associated (j aa) r := by
    intro cl
    obtain ⟨mu, h1, h2, ee, aa, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_minimal_psiCoordinate_associated_fourierPower o' Ω S ρ hBig M U₀ EE FinalForm hAdm hEE x hx R j hB hcpl G
      gm hpb D A U hLB hpsiU (κE.symm (cz cl))
    exact ⟨mu, ee, aa, h1, h2, h3, h4, h5, h6⟩
  choose mu ee aa hmuC hmuMin hee hFF hEa hassoc using hQ
  have hcong : ∀ cl (y : D.toPre.X), CongMod S.N y (κE.symm (cz cl)) ↔ ∀ u i, ((κE y u i : ℤ) : ZMod S.N) = cl u i := by
    intro cl y
    rw [congMod_iff κE]
    simp only [AddEquiv.apply_symm_apply]
    refine forall_congr' fun u => forall_congr' fun i => ?_
    rw [← hcz cl u i, eq_comm, ZMod.intCast_eq_intCast_iff_dvd_sub]
  let b₀ : LinearMap.BilinForm ℤ (Fin rk → ℤ) := T₀.β.compl₁₂ ι.symm.toLinearMap ι.symm.toLinearMap
  have hqb : ∀ v, qW W b₀ v = qW W T₀.β (fun u => ι.symm (v u)) := fun v => rfl
  have cmp : ∀ (T : Trait F) (V' : Type) [CommRing V'] [IsDomain V'] (h : T.V →+* V') (g' : R →+* V')
      (ρT : D.toPre.X →+ (Fin 8 → T.D.toPre.X)), Irreducible (h T.ϖ) →
      (∀ y r, PsiCoord D.toPre y r → 0 ≤ qW W T.β (ρT y) ∧ Associated (g' r) (h T.ϖ ^ (qW W T.β (ρT y)).toNat)) →
      ∀ cl y, CongMod S.N y (κE.symm (cz cl)) → qW W T.β (ρT (mu cl)) ≤ qW W T.β (ρT y) := by
    intro T V' _ _ h g' ρT hirr hord cl y hy
    obtain ⟨r₁, hr₁, -⟩ := (GlobalTheory.PsiCoordLocal.main R D hRi (mu cl)).1
    obtain ⟨r₂, hr₂, -⟩ := (GlobalTheory.PsiCoordLocal.main R D hRi y).1
    obtain ⟨h1, a1⟩ := hord _ _ hr₁
    obtain ⟨h2, a2⟩ := hord _ _ hr₂
    exact le_of_assoc_pow hirr h1 h2 a1 a2 (map_dvd g' (hmuMin cl y hy r₁ r₂ hr₁ hr₂))
  refine ⟨rk, b₀, fun cl => κE (mu cl), ee, Trait.finrank_le_of_three_le g n F hn T₀, fun _ _ => T₀.symm _ _,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    exact Trait.beta_pos g n _ (zetaAway n) F T₀ (ι.symm v) ((LinearEquiv.map_ne_zero_iff ι.symm).2 hv)
  · intro cl u i
    exact (hcong cl (mu cl)).1 (hmuC cl) u i
  · intro cl α hα
    have hy : CongMod S.N (κE.symm α) (κE.symm (cz cl)) := (hcong cl _).2 (by simpa using hα)
    have h1 := cmp T₀ V₀ h₀ g₀ ρ₀ hirr₀ hord₀ cl _ hy
    have e1 : (fun u => ι.symm (κE (mu cl) u)) = ρ₀ (mu cl) := funext (hκ' _)
    have e2 : (fun u => ι.symm (α u)) = ρ₀ (κE.symm α) := by
      funext u; rw [← hκ', AddEquiv.apply_symm_apply]
    rw [hqb, hqb, e1, e2]
    exact h1
  · intro cl
    exact ⟨hee cl, hFF cl⟩
  · intro T ξ hT hs
    obtain ⟨V', _, _, _, h, g', ρT, hinj, hirr, hsq, hsurj, hord, hrel⟩ := key T ξ hT hs
    obtain ⟨πT, hπs, hπ⟩ := exists_diag_of_matRel W hW D.toPre.X T₀.D.toPre.X T.D.toPre.X m e₀ ρT hsurj
      (fun a b y => hrel₀ a b y) hrel
    let π : (Fin rk → ℤ) →+ T.D.toPre.X := πT.comp ι.symm.toLinearMap.toAddMonoidHom
    have hqπ : ∀ v, qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) v =
        qW W T.β (fun u => πT (ι.symm (v u))) := fun v => rfl
    have hρT : ∀ y, (fun u => πT (ι.symm (κE y u))) = ρT y := fun y => funext fun u => by
      rw [hκ', hπ]; rfl
    refine ⟨π, hπs.comp ι.symm.surjective, ?_, ?_⟩
    · intro cl α hα
      have hy : CongMod S.N (κE.symm α) (κE.symm (cz cl)) := (hcong cl _).2 (by simpa using hα)
      have h1 := cmp T V' h g' ρT hirr hord cl _ hy
      have e2 : (fun u => πT (ι.symm (α u))) = ρT (κE.symm α) := by rw [← hρT, AddEquiv.apply_symm_apply]
      rw [hqπ, hqπ, hρT, e2]
      exact h1
    · intro cl
      rw [hqπ, hρT]
      obtain ⟨r₁, hr₁, -⟩ := (GlobalTheory.PsiCoordLocal.main R D hRi (mu cl)).1
      obtain ⟨h1, a1⟩ := hord _ _ hr₁
      refine ⟨h1, ?_⟩
      rw [← hEa cl]
      have hsq' : spMap (g'.comp j) ≫ M.Z.fromSpecStalk x = spMap h ≫ ξ := by
        rw [← hsq, ← Category.assoc]
        congr 1
        rw [← Spec.map_comp]
        rfl
      exact ordEq_of_assoc M x T ξ hs h (g'.comp j) hinj hirr hsq' (aa cl) _ (((hassoc cl r₁ hr₁).map g').trans a1)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRankFormMinimalTuplesAtClosedPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rank_form_minimalTuples_at_closedPoint : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∀ (_ : NeZero S.N) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, IsClosed ({x} : Set M.Z) → ∃ (r : ℕ) (b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : (Fin 8 → Fin r → ZMod S.N) → (Fin 8 → Fin r → ℤ)) (e : (Fin 8 → Fin r → ZMod S.N) → Ω), r ≤ g ∧ (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧ (∀ c u i, ((μ c u i : ℤ) : ZMod S.N) = c u i) ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) ∧ (∀ c, e c ≠ 0 ∧ ∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e c = S.FF T₀ c' κ / S.th x₀) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : (Fin r → ℤ) →+ T.D.toPre.X, Function.Surjective π ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) α) ∧ ∀ c, 0 ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ∧ OrdEq M T ξ (e c ^ S.N) (qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c)).toNat := by
  first | exact @GlobalTheory.Poinc.Clocx.exists_at_closedPoint | exact GlobalTheory.Poinc.Clocx.exists_at_closedPoint | (intros; apply GlobalTheory.Poinc.Clocx.exists_at_closedPoint <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelLocalLatticeFourierPartsOrders
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

namespace GlobalTheory.Poinc

theorem local_lattice_orders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∀ (_ : NeZero S.N) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, ∃ (r : ℕ) (b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : (Fin 8 → Fin r → ZMod S.N) → (Fin 8 → Fin r → ℤ)) (e : (Fin 8 → Fin r → ZMod S.N) → Ω), r ≤ g ∧ (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧ (∀ c u i, ((μ c u i : ℤ) : ZMod S.N) = c u i) ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) ∧ (∀ c, e c ≠ 0 ∧ ∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e c = S.FF T₀ c' κ / S.th x₀) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : (Fin r → ℤ) →+ T.D.toPre.X, Function.Surjective π ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) α) ∧ ∀ c, 0 ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ∧ OrdEq M T ξ (e c ^ S.N) (qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c)).toNat := by
  intro g n hg hn hodd F W hW o' Ω _ _ _ _ S ρ u hS hsh hgen hN M U₀ EE FinalForm hadm hEE x
  have hc : CompactSpace M.Z := by
    have := M.qc
    exact QuasiCompact.compactSpace_of_compactSpace M.s
  obtain ⟨y, hy, hyc⟩ := (isClosed_closure (s := ({x} : Set M.Z))).exists_closed_singleton
    ⟨x, subset_closure rfl⟩
  have hxy : x ⤳ y := specializes_iff_mem_closure.2 hy
  obtain ⟨r, b₀, μ, e, h1, h2, h3, h4, h5, h6, h7⟩ :=
    GlobalTheory.T.exists_rank_form_minimalTuples_at_closedPoint g n hg hn hodd F W hW o' Ω S ρ u hS hsh hgen hN M U₀ EE FinalForm hadm hEE y hyc
  exact ⟨r, b₀, μ, e, h1, h2, h3, h4, h5, h6, fun T ξ hT hξ => h7 T ξ hT (hξ.trans hxy)⟩

end GlobalTheory.Poinc
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaModelLocalLatticeFourierPartsOrdersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
open Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaModel_local_lattice_fourierParts_orders : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (o' Ω : Type) [CommRing o'] [Field Ω] [Algebra o' Ω] [ArithBase o' Ω] (S : ThetaSys o' Ω) (ρ : S.Real) (u : Sp S.R ⟶ F.X), S.Big → SharpOver F W ρ.P u → (∀ w, (spMap S.R.val.toRingHom ≫ u) w ∈ genericPoints F.X) → ∀ (_ : NeZero S.N) (M : RatModel o' Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J) (FinalForm : ZHOut ρ M U₀ EE), S.admitted M U₀ → S.IsEE M U₀ EE → ∀ x : M.Z, ∃ (r : ℕ) (b₀ : LinearMap.BilinForm ℤ (Fin r → ℤ)) (μ : (Fin 8 → Fin r → ZMod S.N) → (Fin 8 → Fin r → ℤ)) (e : (Fin 8 → Fin r → ZMod S.N) → Ω), r ≤ g ∧ (∀ x y, b₀ x y = b₀ y x) ∧ (∀ x, x ≠ 0 → 0 < b₀ x x) ∧ (∀ c u i, ((μ c u i : ℤ) : ZMod S.N) = c u i) ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W b₀ (μ c) ≤ qW W b₀ α) ∧ (∀ c, e c ≠ 0 ∧ ∃ (T₀ : AddSubgroup S.Gam) (c' : T₀ →+ ZMod S.N) (κ : S.J × (T₀ → ZMod ((S.r * S.N) ^ 2))) (x₀ : S.Gam), S.IsoFree T₀ ∧ e c = S.FF T₀ c' κ / S.th x₀) ∧ ∀ (T : Trait F) (ξ : Sp T.V ⟶ M.Z), ThroughU M U₀ FinalForm.u₀ u T ξ → ξ (IsLocalRing.closedPoint T.V) ⤳ x → ∃ π : (Fin r → ℤ) →+ T.D.toPre.X, Function.Surjective π ∧ (∀ c (α : Fin 8 → Fin r → ℤ), (∀ u i, ((α u i : ℤ) : ZMod S.N) = c u i) → qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) α) ∧ ∀ c, 0 ≤ qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c) ∧ OrdEq M T ξ (e c ^ S.N) (qW W (T.β.compl₁₂ π.toIntLinearMap π.toIntLinearMap) (μ c)).toNat := by
  first | exact @GlobalTheory.Poinc.local_lattice_orders | exact GlobalTheory.Poinc.local_lattice_orders | (intros; apply GlobalTheory.Poinc.local_lattice_orders <;> assumption)
end
