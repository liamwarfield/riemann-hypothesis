module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniformisedModel
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsProperOfPowerSeriesArcsOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisedTestDimensionsAndSplitFibre
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullDegCancelTowerOfFields

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExpansionCoefMemAdicPow
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExpansionCoefMemAdicPow
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem eq_zero_of_cst_eq_zero {S : Type} [CommRing S] [IsLocalRing S] {X : Scheme.{0}} (p : X ⟶ Sp S) [Flat p] (x : X)
    (hx : p x = IsLocalRing.closedPoint S) {a : S} (ha : cst p x a = 0) : a = 0 := by
  let φ : S →+* X.presheaf.stalk x := (p.stalkMap x).hom.comp
    (((Sp S).presheaf.germ ⊤ (p x) trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom)
  have hφ : ∀ c, φ c = cst p x c := fun c => by
    rw [cst, gs_stalkMap p x ⊤ trivial, gs_eq _ _ ⊤ trivial]; rfl
  have fl : φ.Flat := by
    refine RingHom.Flat.comp (RingHom.Flat.comp (RingHom.Flat.of_bijective
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of S)).inv)) ?_) (Flat.stalkMap p x)
    have hU := isAffineOpen_top (Sp S)
    let _ := (Sp S).presheaf.algebra_section_stalk (U := ⊤) ⟨p x, trivial⟩
    have := hU.isLocalization_stalk ⟨p x, trivial⟩
    exact IsLocalization.flat ((Sp S).presheaf.stalk ((⟨p x, trivial⟩ : (⊤ : (Sp S).Opens)) : Sp S))
      (hU.primeIdealOf ⟨p x, trivial⟩).asIdeal.primeCompl
  let _ := φ.toAlgebra
  have : Module.Flat S (X.presheaf.stalk x) := fl
  have : IsLocalHom (algebraMap S (X.presheaf.stalk x)) := ⟨fun c hc => by
    by_contra h
    exact cst_not_isUnit p x hx h (hφ c ▸ hc)⟩
  have : Module.FaithfullyFlat S (X.presheaf.stalk x) := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact FaithfulSMul.algebraMap_injective S (X.presheaf.stalk x) ((hφ a).trans (ha.trans (map_zero _).symm))

theorem coef_mem_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), U.ExpT (𝟙_ _) 1 σ f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ e : ℕ, ∃ s : Finset D.X, ∀ χ ∉ s, ∀ (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (b : R), Coef D χ u th (f χ) b → b ∈ I ^ (e + 1) := by
  intro R _ _ _ I hI D A G _ _ U σ f th hE hth e
  obtain ⟨s, hs⟩ := hE e
  refine ⟨s, fun χ hχ u b hb => ?_⟩
  have hI' : I ^ (e + 1) ≠ ⊤ := fun h => hI (top_unique (h ▸ Ideal.pow_le_self e.succ_ne_zero))
  haveI : Nontrivial (R ⧸ I ^ (e + 1)) := Ideal.Quotient.nontrivial_iff.2 hI'
  haveI : IsLocalRing (R ⧸ I ^ (e + 1)) := IsLocalRing.of_surjective' _ Ideal.Quotient.mk_surjective
  haveI : IsLocalHom (Ideal.Quotient.mk (I ^ (e + 1))) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hcl : thick R I e (IsLocalRing.closedPoint _) = IsLocalRing.closedPoint R :=
    IsLocalRing.comap_closedPoint (Ideal.Quotient.mk (I ^ (e + 1)))
  haveI := U.semi.smooth
  haveI : Flat (thickObj R I e G).hom := inferInstanceAs (Flat (pullback.snd G.hom (thick R I e)))
  obtain ⟨z₀, hz₀, hnz⟩ := hth (IsLocalRing.closedPoint R)
  let T := (Over.map (thick R I e)).obj (thickObj R I e G)
  let y : T ⟶ D.P.A := (U.gt e).pG
  let m : 𝟙_ _ ⊗ D.P.A ⟶ D.P.A := snd (𝟙_ _) D.P.A * (cT D _ χ)⁻¹
  let τ : D.P.A ⟶ 𝟙_ _ ⊗ D.P.A := lift (toUnit _) (𝟙 _ * cT D _ χ)
  have hc : ∀ {T₁ T₂ : Over (Spec (CommRingCat.of R))} (g : T₁ ⟶ T₂), g ≫ cT D _ χ = cT D _ χ := fun g => by
    rw [cT, ← Category.assoc, toUnit_unique (g ≫ toUnit _) (toUnit _)]
  have hmτ : m ≫ τ = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, hc, Category.comp_id, inv_mul_cancel_right, Category.id_comp]
  have hyτ : y ≫ τ = lift (toUnit T) (y * cT D T χ) := by
    apply CartesianMonoidalCategory.hom_ext
    · exact toUnit_unique _ _
    · rw [Category.assoc, lift_snd, MonObj.comp_mul, hc, Category.comp_id, lift_snd]
  have h1 : D.P.A.hom (m.left z₀) = IsLocalRing.closedPoint R := by
    rw [← Scheme.Hom.comp_apply, Over.w m]; exact hz₀
  obtain ⟨w, hw, hw'⟩ := Scheme.Pullback.exists_preimage_pullback (f := D.P.A.hom) (g := thick R I e)
    (m.left z₀) (IsLocalRing.closedPoint (R ⧸ I ^ (e + 1))) (h1.trans hcl.symm)
  obtain ⟨z, rfl⟩ := (U.gt e).q_surj.1 w
  have hy : y.left z = m.left z₀ := hw
  have hz : (thickObj R I e G).hom z = IsLocalRing.closedPoint _ := by
    rw [← Over.w (U.gt e).q, Scheme.Hom.comp_apply]; exact hw'
  have h2 : (lift (toUnit T) (y * cT D T χ)).left z = z₀ := by
    rw [← hyτ, Over.comp_left, Scheme.Hom.comp_apply, hy, ← Scheme.Hom.comp_apply, ← Over.comp_left, hmτ]
    rfl
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := T.left) D.P.isLB z
  obtain ⟨JG, hJG⟩ := exists_good_pt (Z := T.left) U.P.L.isLB z
  have hu := (MulPullSec.mem_nonzeroLocus_iff th (lift (toUnit T) (y * cT D T χ)).left z hJ).1 (h2 ▸ hnz)
  have h0 := (hs T.left (𝟙 _) (lift (toUnit T) (fstG I e G)).left (lift (toUnit T) y).left
    (by rw [← Over.comp_left, lift_snd, Category.id_comp])
    (by rw [← Over.comp_left, lift_snd, Category.id_comp])
    (by rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]) z JG J hJG hJ).1 χ hχ
  have h3 := hb T y z J hJ
  rw [h0] at h3
  have h4 : cst T.hom z b = 0 := ((Units.isUnit _).mul hu).mul_left_eq_zero.1 h3.symm
  have h5 : cst (thickObj R I e G).hom z (Ideal.Quotient.mk _ b) = 0 :=
    (cst_comp (thickObj R I e G).hom (Ideal.Quotient.mk (I ^ (e + 1))) z b).symm.trans h4
  exact Ideal.Quotient.eq_zero_iff_mem.1 (eq_zero_of_cst_eq_zero _ z hz h5)

end GlobalTheory.PsiRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExpansionCoefMemAdicPowStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansionCoef_mem_adic_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (σ : U.SecGT (𝟙_ _) 1) (f : ∀ α, SecBT D (𝟙_ _) 1 α) (th : SecBT D (𝟙_ _) 1 0), U.ExpT (𝟙_ _) 1 σ f → FibNZ (𝟙_ _ ⊗ D.P.A).hom th → ∀ e : ℕ, ∃ s : Finset D.X, ∀ χ ∉ s, ∀ (u : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => (D.c χ).left) (fun _ => -1))) (b : R), Coef D χ u th (f χ) b → b ∈ I ^ (e + 1) := by
  first | exact @GlobalTheory.PsiRing.coef_mem_pow | exact GlobalTheory.PsiRing.coef_mem_pow | (intros; apply GlobalTheory.PsiRing.coef_mem_pow <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsExpansionTermUnitClosedFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsExpansionTermUnitClosedFibre
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

namespace GlobalTheory.PsiRing

theorem exists_thick_eq_closedPoint (R : Type) [CommRing R] [IsLocalRing R] (I : Ideal R) (hI : I ≠ ⊤) (e : ℕ) :
    ∃ p, thick R I e p = IsLocalRing.closedPoint R := by
  have h : IsLocalRing.closedPoint R ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (I ^ (e + 1)))) := by
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, PrimeSpectrum.mem_zeroLocus]
    exact fun x hx => IsLocalRing.le_maximalIdeal hI (Ideal.pow_le_self (Nat.succ_ne_zero e) hx)
  exact h

theorem exists_unit_term :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → FibNZ (𝟙_ _ ⊗ G).hom σ → ∃ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (α : D.X), Good D.P.L z J ∧ T.hom z = IsLocalRing.closedPoint R ∧ (∀ b ∈ I, Geo.Tor.cst T.hom z b = 0) ∧ IsUnit (sval (f α) (lift (toUnit T) y).left z J) := by
  intro R _ _ _ I hI D A G _ _ U k σ f hE hF
  obtain ⟨z₀, hz₀, hn⟩ := hF (IsLocalRing.closedPoint R)
  obtain ⟨p, hp⟩ := exists_thick_eq_closedPoint R I hI 0
  have h₁ : G.hom ((snd (𝟙_ _) G).left z₀) = thick R I 0 p := by
    rw [hp, ← hz₀, ← Scheme.Hom.comp_apply, Over.w]
  obtain ⟨z, hz, hz'⟩ := Scheme.Pullback.exists_preimage_pullback _ _ h₁
  let T : Over (Spec (CommRingCat.of R)) := (Over.map (thick R I 0)).obj (thickObj R I 0 G)
  let y : T ⟶ D.P.A := (U.gt 0).pG
  let x : T ⟶ G := fstG I 0 G
  have hG : (lift (toUnit T) x).left ≫ (snd _ G).left = x.left := by rw [← Over.comp_left, lift_snd]
  have hB : (lift (toUnit T) y).left ≫ (snd _ D.P.A).left = y.left := by rw [← Over.comp_left, lift_snd]
  have hf : (lift (toUnit T) y).left ≫ (fst _ D.P.A).left = (lift (toUnit T) x).left ≫ (fst _ G).left := by
    rw [← Over.comp_left, ← Over.comp_left, lift_fst, lift_fst]
  have hr : (lift (toUnit T) x).left z = z₀ := by
    have hi : lift (toUnit T) x = x ≫ (λ_ G).inv := by ext1 <;> simp [toUnit_unique]
    have hj : (snd (𝟙_ _) G).left ≫ (λ_ G).inv.left = 𝟙 _ := by
      rw [← Over.comp_left, ← leftUnitor_hom, Iso.hom_inv_id, Over.id_left]
    have hx : x.left z = (snd (𝟙_ _) G).left z₀ := hz
    rw [hi, Over.comp_left, Scheme.Hom.comp_apply, hx, ← Scheme.Hom.comp_apply, hj]
    rfl
  obtain ⟨JG, hJG⟩ := exists_good_pt (Z := T.left) U.P.L.isLB z
  obtain ⟨J, hJ⟩ := exists_good_pt (Z := T.left) D.P.isLB z
  obtain ⟨s, hs⟩ := hE 0
  obtain ⟨-, hsum⟩ := hs T.left (𝟙 _) _ _ (hG.trans (Category.id_comp _).symm) (hB.trans (Category.id_comp _).symm)
    hf z JG J hJG hJ
  have hu : IsUnit (sval σ (lift (toUnit T) x).left z JG) :=
    (MulPullSec.mem_nonzeroLocus_iff σ _ z hJG).1 (hr ▸ hn)
  obtain ⟨α, -, hα⟩ := IsLocalRing.exists_of_isUnit_sum
    ((congrArg IsUnit hsum).mp (((Units.isUnit _).pow k).mul hu))
  refine ⟨T, y, z, J, α, hJ, ?_, fun b hb => ?_, isUnit_of_mul_isUnit_left hα⟩
  · have : T.hom = pullback.snd G.hom (thick R I 0) ≫ thick R I 0 := rfl
    rw [this, Scheme.Hom.comp_apply, hz', hp]
  · refine (Geo.Tor.cst_comp (pullback.snd G.hom (thick R I 0)) (Ideal.Quotient.mk (I ^ (0 + 1))) z b).trans ?_
    rw [Ideal.Quotient.eq_zero_iff_mem.2 (by simpa using hb), Geo.Tor.cst, map_zero, gs_eq _ _ ⊤ trivial, map_zero,
      map_zero]

end GlobalTheory.PsiRing
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsExpansionTermUnitClosedFibreStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_expansionTerm_unit_closedFibre : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), I ≠ ⊤ → ∀ (D : DegPre R) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : PreU I D A G) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → FibNZ (𝟙_ _ ⊗ G).hom σ → ∃ (T : Over (Spec (CommRingCat.of R))) (y : T ⟶ D.P.A) (z : T.left) (J : (T.left ⟶ D.P.A.left) → D.P.L.ι) (α : D.X), Good D.P.L z J ∧ T.hom z = IsLocalRing.closedPoint R ∧ (∀ b ∈ I, Geo.Tor.cst T.hom z b = 0) ∧ IsUnit (sval (f α) (lift (toUnit T) y).left z J) := by
  first | exact @GlobalTheory.PsiRing.exists_unit_term | exact GlobalTheory.PsiRing.exists_unit_term | (intros; apply GlobalTheory.PsiRing.exists_unit_term <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfComparison
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfComparison
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing

noncomputable section

namespace GlobalTheory.PsiRing

theorem exists_isPullDeg_of_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D.TauBimult → ∃ hD : IsPullDeg φ D D', hD.e.hom.left ≫ pullback.fst _ _ = β ∧ HEq hD.w v ∧ hD.xe = xe := by
  intro R V _ _ _ _ φ D D' β v xe gp hv hc hr gam hgam hψ hB
  obtain ⟨e, me, he⟩ := grpPullback_iso gp (isGrpPullback_pullback D.P.A (specOf φ))
  subst he
  have hE : eSec D'.P.A ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = specOf φ ≫ eSec D.P.A :=
    (cubeMapOf gp).e_comm
  obtain ⟨W, hW, ⟨ψW⟩⟩ := PsiSpread.exists_psiOn D hB
  obtain ⟨gW, hgW⟩ : ∃ gW : (TK R).left ⟶ (TW W).left, gW ≫ W.ι = jK R :=
    ⟨IsOpenImmersion.lift W.ι (jK R) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact TauPull.jK_mem y W ⟨_, hW⟩), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨lam, l₁, l₂⟩ : ∃ lam : (TK R).left ⟶ (jK R ⁻¹ᵁ W).toScheme, lam ≫ (jK R ⁻¹ᵁ W).ι = 𝟙 _ ∧
      lam ≫ (jK R ∣_ W) = gW :=
    ⟨(isPullback_morphismRestrict (jK R) W).lift _ _ (hgW.trans (Category.id_comp _).symm),
      (isPullback_morphismRestrict (jK R) W).lift_snd _ _ _,
      (isPullback_morphismRestrict (jK R) W).lift_fst _ _ _⟩
  refine ⟨⟨e, me, v, hv, hE, ?_, xe, hc, W, ψW, gam ≫ gW,
    (Category.assoc _ _ _).trans ((congrArg (gam ≫ ·) hgW).trans hgam), fun x => ?_⟩, rfl, HEq.rfl, rfl⟩
  · exact (maps_iff v _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
      (rigPull_le (G' := D'.P.A) (G := D.P.A) _ (specOf φ) hE D.P.L) (fun _ => rfl)).2 hr
  · obtain ⟨b, -, vb⟩ := exists_up ((isGen_iff v).1 hv) D.P.isLB D'.P.isLB (D'.psi x) (D'.psi_gen x)
    have hx : D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ) = gam ≫ D.xK (xe x) :=
      (Category.assoc _ _ _).trans ((congrArg (jK V ≫ ·) (hc x)).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ (D.c (xe x)).left) hgam.symm).trans (Category.assoc _ _ _))))
    refine ⟨b, fun jN jL => unit_ext fun y hy => ?_, corr_of_val D.P.isLB fun y J hJ => ?_⟩
    · have e₁ := vb _ (𝟙 _) y jN (fun _ => jL) (GeneratorPullback.mapsAt_le_b _ _ _ _ jN jL hy) (GeneratorPullback.mapsAt_le_a _ _ _ _ jN jL hy)
      rw [pw, Fintype.prod_unique] at e₁
      refine (gm_res _ y _ hy _).trans (e₁.trans (Eq.symm ((map_mul _ _ _).trans
        (congrArg₂ (· * ·) ?_ (gm_res _ y _ hy _)))))
      exact (map_zpow _ _ _).trans (congrArg (· ^ (-1 : ℤ)) (gm_pull _ _ y _ hy _))
    · obtain ⟨q, hq⟩ := exists_chart D'.P.isLB (D'.xK x y)
      obtain ⟨p, hp⟩ : ∃ p, p = J (D'.xK x ≫ e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) := ⟨_, rfl⟩
      have mp : (e.hom.left ≫ pullback.fst D.P.A.hom (specOf φ)) (D'.xK x y) ∈ D.P.L.U p := hp ▸ hJ _
      have e₁ := vb _ (𝟙 _) y (fun _ => p) (fun _ => q) (Set.mem_iInter.2 fun _ => mp) (Set.mem_iInter.2 fun _ => hq)
      have e₂ := hψ x _ (𝟙 _) y (fun _ => p) (fun _ => q) (fun _ => mp) (fun _ => hq)
      have w₁ := (val_pull hJ _ _ _).symm.trans ((val_corr hJ (ψW.psi_eq (xe x)) (gam ≫ lam)).trans (val_pull hJ _ _ _))
      rw [Category.assoc, Category.assoc, l₁, l₂, Category.comp_id] at w₁
      refine (val_of b _ y J (fun _ => p) (fun _ => by rw [Category.id_comp, hp])).trans (e₁.trans (e₂.symm.trans
        (Eq.trans ?_ (val_pull hJ _ _ _).symm)))
      rw [Category.id_comp, Category.id_comp]
      exact (val_of (D.psi (xe x)) gam y J (fun _ => p) (fun _ => by rw [hp, hx])).symm.trans w₁.symm

end GlobalTheory.PsiRing

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfComparisonStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
open GlobalTheory.PsiRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isPullDeg_of_comparison : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (φ : R →+* V) (D : DegPre R) (D' : DegPre V) (β : D'.P.A.left ⟶ D.P.A.left) (v : LB.Iso D'.P.L (D.P.L.pull β)) (xe : D'.X ≃+ D.X), IsGrpPullback D'.P.A D.P.A (spMap φ) β → v.IsGen → (∀ x, (D'.c x).left ≫ β = spMap φ ≫ (D.c (xe x)).left) → RigCmp φ D D' β v → ∀ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ → PsiCmp D D' β v xe gam → D.TauBimult → ∃ hD : IsPullDeg φ D D', hD.e.hom.left ≫ pullback.fst _ _ = β ∧ HEq hD.w v ∧ hD.xe = xe := by
  first | exact @GlobalTheory.PsiRing.exists_isPullDeg_of_cmp | exact GlobalTheory.PsiRing.exists_isPullDeg_of_cmp | (intros; apply GlobalTheory.PsiRing.exists_isPullDeg_of_cmp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegDataPsiOfSectionNonzeroFibres
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
noncomputable section
namespace GlobalTheory.PsiRing

theorem ne_zero_of_secCmp {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V} {D : DegPre R}
    {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left} {v : LB.Iso D'.P.L (D.P.L.pull β)} {xe : D'.X ≃+ D.X}
    (hw : β ≫ D.P.A.hom = D'.P.A.hom ≫ spMap φ) {f : ∀ α, SecBT D (𝟙_ _) 1 α} {f' : ∀ α, SecBT D' (𝟙_ _) 1 α}
    (h : SecCmp D D' β v xe f f') (h' : ∀ α, ∃ j, (f' α).f j ≠ 0) (α : D.X) : ∃ j, (f α).f j ≠ 0 := by
  obtain ⟨x, rfl⟩ := xe.surjective α
  by_contra h0
  push Not at h0
  obtain ⟨j, hj⟩ := h' x
  refine hj (ThetaScalar.eq_zero_of_sval D'.P.isLB _ (fun y J' hJ' => ?_) j)
  obtain ⟨J, hJ⟩ := exists_good_pt D.P.isLB y
  let T : Over (Spec (CommRingCat.of R)) := Over.mk (((snd (𝟙_ _) D'.P.A).left ≫ β) ≫ D.P.A.hom)
  let p : T ⟶ D.P.A := Over.homMk ((snd (𝟙_ _) D'.P.A).left ≫ β) rfl
  have e := h x _ (𝟙 _) (lift (toUnit T) p).left
    ((congrArg (fun q => q.left) (lift_snd (toUnit T) p)).trans (Category.id_comp _).symm) y J J' hJ hJ'
  rw [ThetaScalar.sval_eq_zero _ h0 _ y hJ] at e
  exact (Units.mul_right_eq_zero _).1 e.symm

theorem exists_generic_map {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] {φ : R →+* V}
    (hφ : Function.Injective φ) : ∃ gam : (TK V).left ⟶ (TK R).left, gam ≫ jK R = jK V ≫ spMap φ := by
  have hi : Function.Injective ((algebraMap V (FractionRing V)).comp φ) :=
    (IsFractionRing.injective V (FractionRing V)).comp hφ
  obtain ⟨g, e⟩ : ∃ g : FractionRing R →+* FractionRing V,
      g.comp (algebraMap R (FractionRing R)) = (algebraMap V (FractionRing V)).comp φ :=
    ⟨IsLocalization.lift (M := nonZeroDivisors R) (g := (algebraMap V (FractionRing V)).comp φ) fun y =>
      IsUnit.mk0 _ ((map_ne_zero_iff _ hi).2 (nonZeroDivisors.coe_ne_zero y)), IsLocalization.lift_comp _⟩
  have e' : spMap g ≫ jK R = jK V ≫ spMap φ := by
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, e]
  exact ⟨spMap g, e'⟩

theorem exists_degData_of_thetaNZ : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ φ : R →+* V, Function.Injective φ → (IsLocalRing.maximalIdeal V).comap φ = I → ∀ (D : DegPre R) (D' : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A' G') (U₀ : Unif (IsLocalRing.maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), Under U' U₀.toUnifPre → ThetaNZ G U.P.L.L → ∃ (psi : _) (h : _) (Dd : DegData R I) (hD : IsPullDeg φ (withPsi D psi h) D'.toPre), Dd.toPre = withPsi D psi h ∧ hD.e.hom.left ≫ pullback.fst _ _ = C.β ∧ HEq hD.w C.v ∧ hD.xe = C.xe := by
  intro h₁ h₂ hE R _ _ _ I hA V _ _ _ hV φ hφ hI D D' A A' G _ _ G' _ _ U U' U₀ F C hU hθ
  obtain ⟨hR, -, -, hP, -⟩ := hA
  have := hV.1
  have hV' : AdmBase V (IsLocalRing.maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hV.2.1⟩
  have hm : IsLocalRing.maximalIdeal V ≠ ⊤ := (IsLocalRing.maximalIdeal.isMaximal V).ne_top
  have hIm : I.map φ ≤ IsLocalRing.maximalIdeal V := Ideal.map_le_iff_le_comap.2 hI.ge
  obtain ⟨hσ₁, hσ₂⟩ := GlobalTheory.T.fibrewiseNonzeroSection_prod_and_baseChange R V I _ φ D D'.toPre A G A' G' U U' F C
  obtain ⟨σ, hσ⟩ := hσ₁ hθ
  obtain ⟨f, hf, -⟩ := CompleteBaseExpansion.main h₁ h₂ hE R I hR hP.ne_top D A G U 1 σ
  obtain ⟨σ', f', hf', hσσ, hff⟩ := ExpCmp.expT_cmp R V I _ φ hIm D D'.toPre A A' G G' U U' F C 1 σ f hf
  have hcmp : SecCmp D D'.toPre C.β C.v C.xe f f' := hff
  have hrel' := GlobalTheory.T.psiRel_of_expT' h₁ h₂ V _ hV' D' A' G' U' U₀ hU σ' f' hf'
  have hne' : ∀ α, ∃ j, (f' α).f j ≠ 0 := by
    refine GlobalTheory.T.forall_term_ne_zero_of_psiRelation V D'.toPre f' hrel' ?_
    obtain ⟨T, y, z, J, α, hJ, -, -, hu⟩ := GlobalTheory.T.exists_expansionTerm_unit_closedFibre V _ hm D'.toPre A' G' U' 1 σ' f' hf' (hσ₂ 1 σ σ' hσσ hσ)
    refine ⟨α, ?_⟩
    by_contra h0
    push Not at h0
    rw [ThetaScalar.sval_eq_zero _ h0 _ z hJ] at hu
    exact not_isUnit_zero hu
  obtain ⟨psi, h, hrel⟩ := exists_psi_psiRel h₁ h₂ R D f (ne_zero_of_secCmp C.pbB.1.w hcmp hne')
  let E : DegPre R := withPsi D psi h
  have hrelE : PsiRel E (𝟙_ _) f := hrel
  have hrig : RigCmp φ E D'.toPre C.β C.v := GlobalTheory.T.rigidification_comparison_uniformisation R V I _ φ hm hIm D D'.toPre A G A' G' U U' F C
  obtain ⟨gam, hgam⟩ := exists_generic_map hφ
  have hpsi : PsiCmp E D'.toPre C.β C.v C.xe gam :=
    GlobalTheory.T.psiCmp_of_secCmp' R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig f f' hcmp hrelE hrel' (hne' 0) gam hgam
  have hev : E.PsiEven :=
    GlobalTheory.T.psiEven_descend_baseChange h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi D'.psi_even
  have hbi : E.TauBimult :=
    GlobalTheory.T.tauBimult_of_baseChange' h₁.globalFns R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi D'.tau_bimult
  obtain ⟨hD, hD₁, hD₂, hD₃⟩ :=
    GlobalTheory.T.exists_isPullDeg_of_comparison R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr hrig gam hgam hpsi hbi
  obtain ⟨ga, a, hS⟩ := exists_psiScal R E
  obtain ⟨th, hth, hmul⟩ := GlobalTheory.T.exists_thetaSection_nonzeroFibres_localRing h₂.secTwist R D
  obtain ⟨q, hq⟩ := hmul (f 0)
  choose b hb using fun χ : D.X => GlobalTheory.T.exists_twistedSection_thetaTranslate_coef R D th hmul χ (ga χ) (hS χ).1 (f χ)
  have hab : ∀ χ, algebraMap R (FractionRing R) q * (a χ).val = algebraMap R (FractionRing R) (b χ) := fun χ =>
    GlobalTheory.T.psiScalar_eq_expansionCoef_ratio R E ga a f th hS hrelE hth χ q (b χ) hq (hb χ)
  have hbI : ∀ χ : D.X, χ ≠ 0 → b χ ∈ I := fun χ hχ => by
    obtain ⟨x, rfl⟩ := C.xe.surjective χ
    obtain ⟨m, hm₁, hm₂⟩ := GlobalTheory.T.psiScalar_mem_of_psi_mem_ideal R V φ E D'.toPre C.β C.v C.xe C.pbB C.v_gen C.c_pr gam hgam hpsi ga a hS x _
      (D'.psi_pos x fun h0 => hχ (by rw [h0, map_zero])) _ q (hab _)
    refine hI.le (Ideal.mem_comap.2 ?_)
    exact (congrArg (· ∈ IsLocalRing.maximalIdeal V) hm₂).mpr (Ideal.mul_mem_left _ _ hm₁)
  have hqu : IsUnit q := by
    obtain ⟨T, y, z, J, α, hJ, hz, h0, hu⟩ := GlobalTheory.T.exists_expansionTerm_unit_closedFibre R I hP.ne_top D A G U 1 σ f hf hσ
    by_cases hα : α = 0
    · subst hα
      rw [hq _ _ z J hJ, show (lift (toUnit T) y).left ≫ (𝟙_ _ ⊗ D.P.A).hom = T.hom from Over.w _] at hu
      by_contra hn
      exact cst_not_isUnit T.hom z hz hn (isUnit_of_mul_isUnit_left hu)
    · rw [hb α T y z J hJ, h0 _ (hbI α hα), MulZeroClass.zero_mul] at hu
      exact absurd hu not_isUnit_zero
  obtain ⟨q, rfl⟩ := hqu
  have hin : ∀ (χ : D.X) (J : Ideal R), b χ ∈ J → E.PsiIn χ J := fun χ J hJ =>
    (PsiScalIn.main_local E ga a hS χ J).2 ⟨(q⁻¹).val * b χ, J.mul_mem_left _ hJ, by
      rw [map_mul]
      refine (congrArg (_ * ·) (hab χ).symm).trans ?_
      rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]⟩
  refine ⟨psi, h, ⟨E, hev, hbi, fun χ hχ => hin χ I (hbI χ hχ), fun n => ?_⟩, hD, rfl, hD₁, hD₂, hD₃⟩
  obtain ⟨s, hs⟩ := GlobalTheory.T.expansionCoef_mem_adic_pow R I hP.ne_top D A G U σ f th hf hth n
  refine s.finite_toSet.subset fun χ hχ => ?_
  by_contra hn
  exact hχ (hin χ _ (Ideal.pow_le_pow_right (Nat.le_succ n) (hs χ hn _ _ (hb χ))))

end GlobalTheory.PsiRing
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsDegDataPsiOfSectionNonzeroFibresStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_degData_psi_of_section_nonzero_fibres : Laws → Laws2 → Ega → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), admitted R I → ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], CDvr V → ∀ φ : R →+* V, Function.Injective φ → (IsLocalRing.maximalIdeal V).comap φ = I → ∀ (D : DegPre R) (D' : DegData V (IsLocalRing.maximalIdeal V)) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU (IsLocalRing.maximalIdeal V) D'.toPre A' G') (U₀ : Unif (IsLocalRing.maximalIdeal V) D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F), Under U' U₀.toUnifPre → ThetaNZ G U.P.L.L → ∃ (psi : _) (h : _) (Dd : DegData R I) (hD : IsPullDeg φ (withPsi D psi h) D'.toPre), Dd.toPre = withPsi D psi h ∧ hD.e.hom.left ≫ pullback.fst _ _ = C.β ∧ HEq hD.w C.v ∧ hD.xe = C.xe := by
  first | exact @GlobalTheory.PsiRing.exists_degData_of_thetaNZ | exact GlobalTheory.PsiRing.exists_degData_of_thetaNZ | (intros; apply GlobalTheory.PsiRing.exists_degData_of_thetaNZ <;> assumption)
end
