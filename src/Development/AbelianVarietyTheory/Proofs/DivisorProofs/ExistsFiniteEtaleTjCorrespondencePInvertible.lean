module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjCorrespondenceTargetFiniteEtal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionSymmBundleExtensionOnFactor
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionIdempotentFactorTraitUnif
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEquivOfKer

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleTjCorrespondencePInvertible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleTjCorrespondencePInvertible
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_tjCorr_finiteEtale : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∃ T : TjCorr M.toRepFam r w j c, IsFinite T.s ∧ Etale T.s ∧ Surjective T.s ∧ IsFinite T.t ∧ Etale T.t ∧ ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ T.Y, y ≫ T.s = x ∧ ∃ (m₀ : ObjMap o₁ T.o y) (m₁ : ObjMap o₁' T.o' y), m₀.φ ≫ T.ψ.left = ψ₁.left ≫ m₁.φ := by
  intro p _ D R _ _ b N hN hNp hp r w j c hw hu hj hc hm M
  haveI : LocallyOfFiniteType M.s := by
    haveI : Smooth M.s := M.smooth.smooth
    infer_instance
  haveI : IsLocallyNoetherian M.X := LocallyOfFiniteType.isLocallyNoetherian M.s
  obtain ⟨Y, o₀, m₀, o', ψ, hfin, het, hisog, htj, huniv⟩ :=
    GlobalTheory.T.harrisTaylor_typeTj_isogenies_representable p D R b N hN hNp hp r w j c hw hu hj hc hm M.X M.s M.univ
  obtain ⟨t, ⟨ht, ⟨mt⟩⟩, -⟩ := M.rep Y.left (Y.hom ≫ M.s) o'
  obtain ⟨h3, h4⟩ := GlobalTheory.T.harrisTaylor_typeTj_correspondence_target_finite_etale p D R b N hN hNp hp r w j c hw hu hj hc hm M Y.left Y.hom t ht.symm o₀ o' m₀ mt ψ
    hisog htj hfin het huniv
  have hsurj : Surjective Y.hom := by
    refine ⟨fun x => ?_⟩
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point M.X x
    obtain ⟨o₁, ⟨m⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N M.X (Sp k) M.s a M.univ
    obtain ⟨o₁', ψ₁, h1, h2⟩ := GlobalTheory.T.harrisTaylor_exists_typeTj_pIsogeny p D R b N hN hNp hp r w j c hw hu hj hc hm k (a ≫ M.s) o₁
    obtain ⟨y, ⟨hy, -⟩, -⟩ := huniv (Sp k) a o₁ o₁' m ψ₁ h1 h2
    have hx : x ∈ Set.range a.base := by rw [ha]; rfl
    obtain ⟨z', rfl⟩ := hx
    exact ⟨y.base z', by rw [← hy]; rfl⟩
  let T : TjCorr M.toRepFam r w j c :=
    { Y := Y.left, s := Y.hom, t := t, st := ht.symm, o := o₀, o' := o', ms := m₀, mt := mt, ψ := ψ,
      isog := hisog, tj := htj, wPrime := hw.isPrime, uLe := hu,
      pReg := fun U f hf => pReg_of_isUnit (Y.hom ≫ M.s) hp U f hf, sFin := hfin, tFin := h3, sSurj := hsurj }
  exact ⟨T, hfin, het, hsurj, h3, h4, fun S x o₁ o₁' m ψ₁ _ h1 h2 => huniv S x o₁ o₁' m ψ₁ h1 h2⟩

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleTjCorrespondencePInvertibleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
theorem _root_.GlobalTheory.T.exists_finiteEtale_Tj_correspondence_p_invertible : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∃ T : TjCorr M.toRepFam r w j c, IsFinite T.s ∧ Etale T.s ∧ Surjective T.s ∧ IsFinite T.t ∧ Etale T.t ∧ ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ T.Y, y ≫ T.s = x ∧ ∃ (m₀ : ObjMap o₁ T.o y) (m₁ : ObjMap o₁' T.o' y), m₀.φ ≫ T.ψ.left = ψ₁.left ≫ m₁.φ := by
  first | exact @GlobalTheory.UPel.HT.ES.exists_tjCorr_finiteEtale | exact GlobalTheory.UPel.HT.ES.exists_tjCorr_finiteEtale | (intros; apply GlobalTheory.UPel.HT.ES.exists_tjCorr_finiteEtale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfIdempotentFactorBiex
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfGenericPolarisationE
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfGenericPolarisationE
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum.EvenPackage

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {ρ : R →+* R'}

theorem jK_sq (hρ : Function.Injective ρ) : jK R' ≫ spMap ρ =
    spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R := by
  simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp [IsFractionRing.map, IsLocalization.map_eq]

theorem exists_genericMap (hρ : Function.Injective ρ) {G : Over (Sp R)} {G₁ : Over (Sp R')} {β : G₁.left ⟶ G.left}
    (w : β ≫ G.hom = G₁.hom ≫ spMap ρ) : ∃ κ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R),
      κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β := by
  refine ⟨pullback.lift _ (pullback.snd _ _ ≫
    spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) ?_, pullback.lift_fst _ _ _⟩
  rw [Category.assoc, w, ← Category.assoc, pullback.condition, Category.assoc, Category.assoc, jK_sq hρ]

theorem isGrpPullback_generic (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] {G₁ : Over (Sp R')} [GrpObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β) :
    IsGrpPullback ((Over.pullback (jK R')).obj G₁) ((Over.pullback (jK R)).obj G)
      (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) κ₁ := by
  have hsq := jK_sq hρ
  have hmono : Mono (jK R) := EvenDesc.mono_jK R
  have w : κ₁ ≫ ((Over.pullback (jK R)).obj G).hom = ((Over.pullback (jK R')).obj G₁).hom ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) := by
    apply (cancel_mono (jK R)).1
    rw [Category.assoc, Category.assoc]
    change κ₁ ≫ pullback.snd G.hom (jK R) ≫ jK R = pullback.snd G₁.hom (jK R') ≫
      spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ) ≫ jK R
    rw [← pullback.condition, ← Category.assoc, hκf, Category.assoc, hβ.1.w, ← Category.assoc, pullback.condition,
      Category.assoc, hsq]
  exact (isGrpPullback_pullback G (jK R)).cancel
      (((isGrpPullback_pullback G₁ (jK R')).comp hβ).congr hsq hκf.symm) w

theorem exists_square_extLam (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G] [IsCommMonObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁] [IsCommMonObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β)
    (L : LB ((Over.pullback (jK R)).obj G).left) (PP : LB (G2 G).left) (hL : L.IsLB) (hExt : ExtLam G L PP) :
    ∃ β₂ : (G2 G₁).left ⟶ (G2 G).left, Geo.Tor.IsSquare β β₂ ∧ ExtLam G₁ (L.pull κ₁) (PP.pull β₂) := by
  have hκ := isGrpPullback_generic hρ hβ hκf
  have : IsCommMonObj ((Over.pullback (jK R)).obj G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback (jK R')).obj G₁) := Functor.isCommMonObj_obj
  obtain ⟨β₂κ, hsqκ, Hκ⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R')).obj G₁) κ₁ hκ
  obtain ⟨β₂, hsqβ, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G G₁ β hβ
  obtain ⟨g₂, hg₂, -⟩ := lbIso_lam_pull_of_isGrpPullback _ _ _ G ((Over.pullback (jK R)).obj G) _ (isGrpPullback_pullback G (jK R))
  refine ⟨β₂, hsqβ, pull_isLB hExt.1 β₂, fun κ₂ hκ₂ => ?_⟩
  have hN := pull_isLB hL κ₁
  have H1 := Hκ L (L.pull κ₁) _ PP g₂ hL hN hExt.1 (GlobalTheory.PolBaseChange.lbIso_refl hN) (hExt.2 g₂ hg₂)
  have e : β₂κ ≫ g₂ = κ₂ ≫ β₂ := by
    apply pullback.hom_ext
    · show (β₂κ ≫ g₂) ≫ (fst G G).left = (κ₂ ≫ β₂) ≫ (fst G G).left
      rw [Category.assoc, hg₂.1, ← Category.assoc, hsqκ.1, Category.assoc, hκf, Category.assoc, hsqβ.1,
        reassoc_of% hκ₂.1]
    · show (β₂κ ≫ g₂) ≫ (snd G G).left = (κ₂ ≫ β₂) ≫ (snd G G).left
      rw [Category.assoc, hg₂.2, ← Category.assoc, hsqκ.2, Category.assoc, hκf, Category.assoc, hsqβ.2,
        reassoc_of% hκ₂.2]
  exact LBIso.trans (DVR.linComb_isLB _ hN _ _) (pull_isLB hExt.1 _) (pull_isLB (pull_isLB hExt.1 _) _) H1
    (LBIso.chartPull (chartPullSame PP _ (fun _ => β₂) _ κ₂ fun _ => e) (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ κ₂ κ₂ rfl)
      (GlobalTheory.PolBaseChange.lbIso_refl (pull_isLB hExt.1 β₂)))

theorem exists_generic_pol (hρ : Function.Injective ρ) {G : Over (Sp R)} [GrpObj G]
    {G₁ : Over (Sp R')} [GrpObj G₁]
    {β : G₁.left ⟶ G.left} {κ₁ : pullback G₁.hom (jK R') ⟶ pullback G.hom (jK R)}
    (hβ : IsGrpPullback G₁ G (spMap ρ) β) (hκf : κ₁ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β)
    (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A) (hgen : IsMonHom gen.hom) :
    ∃ (A' : PolAV (Sp (FractionRing R'))) (gen' : (Over.pullback (jK R')).obj G₁ ≅ A'.A), IsMonHom gen'.hom ∧
      LBIso (A'.L.pull gen'.hom.left) ((A.L.pull gen.hom.left).pull κ₁) := by
  have hκ := isGrpPullback_generic hρ hβ hκf
  obtain ⟨A', gA, pA, -, mA, tA⟩ := GlobalTheory.polBaseChange_holds _ _
    (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) A
  have gpA : IsGrpPullback A'.A A.A (spMap (IsFractionRing.map (K := FractionRing R) (L := FractionRing R') hρ)) gA :=
    ⟨pA, fun T x y x₀ y₀ hx hy => by
      have e₁ : x₀ = Out.toBase pA.w x := Over.OverMorphism.ext hx
      have e₂ : y₀ = Out.toBase pA.w y := Over.OverMorphism.ext hy
      rw [e₁, e₂, ← mA]; rfl⟩
  have tA' : LBIso (A.L.pull gA) A'.L := tA
  obtain ⟨e, he, hee⟩ := grpPullback_iso ((hκ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl) gpA
  refine ⟨A', e, he, ?_⟩
  exact LBIso.trans (pull_isLB A'.isLB _) (pull_isLB A.isLB _) (pull_isLB (pull_isLB A.isLB _) _)
    (GlobalTheory.GenSpread.lbIso_pull_of_lbIso tA'.symm e.hom.left hee.symm)
    (GlobalTheory.GenSpread.lbIso_pull_pull A.isLB κ₁ rfl)

end GlobalTheory.Mum.EvenPackage


set_option maxHeartbeats 1000000 in
open GlobalTheory.Mum.EvenPackage in
theorem GlobalTheory.Mum.exists_even_package_of_ext : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∀ (R₃ : Type) [CommRing R₃] [IsDomain R₃] [IsLocalRing R₃] (ρ₃ : R →+* R₃) (G₃ : Over (Sp R₃)) [GrpObj G₃] [IsCommMonObj G₃] (β₃ : G₃.left ⟶ G.left) (κ₃ : pullback G₃.hom (jK R₃) ⟶ pullback G.hom (jK R)) (L₃ : LB G₃.left), FinExt ρ₃ → IsGrpPullback G₃ G (spMap ρ₃) β₃ → κ₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₃ → L₃.IsLB → LBIso (L₃.pull (pullback.fst G₃.hom (jK R₃))) ((A.L.pull gen.hom.left).pull κ₃) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ ∧ IsGrpPullback G₉ G (spMap ρ) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P.L.L) (PP.pull β₉₂) ∧ EvenOn P ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  intro R _ _ _ hR G _ _ hG A gen hgen PP hPP W _ _ _ φ GW _ _ βW DW AW UW κ hW hφi hφl hGW hκ hUW
    R₃ _ _ _ ρ₃ G₃ _ _ β₃ κ₃ L₃ hρ₃ hβ₃ hκ₃ hL₃ hL₃g
  have hR₃ : Base R₃ := by
    haveI := hR.2
    exact ⟨hρ₃.1, charZero_of_injective_ringHom hρ₃.2.1⟩
  have hG₃ : IsSemiAbelian G₃ := EvenDesc.isSemiAbelian_of_isGrpPullback hβ₃ hG
  obtain ⟨R₉, i1, i2, i3, ρ₄, G₉, i4, i5, β₄, X, i6, i7, i8, hρ₄, hβ₄, hTQ⟩ :=
    exists_finExt_tq_closedFibre R₃ hR₃ G₃ hG₃
  have hρ : FinExt (ρ₄.comp ρ₃) := ⟨hρ₄.1, hρ₄.2.1.comp hρ₃.2.1, hρ₄.2.2.comp hρ₃.2.2⟩
  have hβ : IsGrpPullback G₉ G (spMap (ρ₄.comp ρ₃)) (β₄ ≫ β₃) :=
    (hβ₄.comp hβ₃).congr (TraitExt.spMap_comp _ _) rfl
  have hG₉ : IsSemiAbelian G₉ := EvenDesc.isSemiAbelian_of_isGrpPullback hβ hG
  obtain ⟨κ₄, hκ₄⟩ := exists_genericMap hρ₄.2.1 hβ₄.1.w
  have hκ₉ : (κ₄ ≫ κ₃) ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₄ ≫ β₃ := by
    rw [Category.assoc, hκ₃, ← Category.assoc, hκ₄, Category.assoc]
  have hN : (A.L.pull gen.hom.left).IsLB := pull_isLB A.isLB _
  have hL₉ : (L₃.pull β₄).IsLB := pull_isLB hL₃ _
  have hL₉g : LBIso ((L₃.pull β₄).pull (pullback.fst G₉.hom (jK R₉))) ((A.L.pull gen.hom.left).pull (κ₄ ≫ κ₃)) :=
    LBIso.trans (pull_isLB hL₉ _) (pull_isLB hL₃ _) (pull_isLB hN _)
      (GlobalTheory.GenSpread.lbIso_pull_pull hL₃ (pullback.fst G₉.hom (jK R₉)) rfl).symm
      (GlobalTheory.GenSpread.lbIso_pull_comp κ₄ hκ₄.symm rfl hL₃g)
  obtain ⟨A₉, gen₉, hgen₉, hA₉⟩ := exists_generic_pol hρ.2.1 hβ hκ₉ A gen hgen
  have hA₉' : LBIso (A₉.L.pull gen₉.hom.left) ((L₃.pull β₄).pull (pullback.fst G₉.hom (jK R₉))) :=
    LBIso.trans (pull_isLB A₉.isLB _) (pull_isLB hN _) (pull_isLB hL₉ _) hA₉ hL₉g.symm
  have hprop : IsProper (pullback.snd G₉.hom (jK R₉)) := by
    have hi : IsIso gen₉.hom.left := ((Over.forget _).mapIso gen₉).isIso_hom
    have := A₉.isAb.proper
    have hw : pullback.snd G₉.hom (jK R₉) = gen₉.hom.left ≫ A₉.A.hom := (Over.w gen₉.hom).symm
    rw [hw]; infer_instance
  have hsym := GlobalTheory.sym_of_lbIso_pull_hom _ _ _ gen₉.hom hgen₉ _ _ A₉.isLB (pull_isLB hL₉ _) A₉.sym hA₉'
  haveI : IsNoetherianRing R₉ := hρ.1.1
  haveI : IsIntegrallyClosed R₉ := hρ.1.2.2.1
  obtain ⟨P, hP⟩ := GlobalTheory.CubSymPkg.exists_cp_of_generic_sym R₉ G₉ hG₉ hprop _ hL₉ hsym
  obtain ⟨β₂, hsq, hE⟩ := exists_square_extLam hρ.2.1 hβ hκ₉ _ PP hN hPP
  refine ⟨R₉, i1, i2, i3, ρ₄.comp ρ₃, G₉, i4, i5, β₄ ≫ β₃, β₂, P, A₉, gen₉, hρ, hβ, hsq, hG₉, ?_, ?_, hgen₉, ?_⟩
  · rw [hP]
    exact lbIso_lam_of_extLam R₉ G₉ hG₉ _ _ _ hL₉ (pull_isLB hN _) hL₉g.symm hE
  · refine evenOn_of_trait_unif R hR G hG A gen hgen W φ GW βW DW AW UW κ hW hφi hφl hGW hκ hUW R₉ _ G₉ _ _ P hρ hβ hκ₉
      ?_ X hTQ
    rw [hP]; exact hL₉g
  · rw [hP]; exact hA₉'

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfGenericPolarisationEStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_evenCubicalStructure_of_genericPolarisation_extension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (A : PolAV (Sp (FractionRing R))) (gen : ((Over.pullback (jK R)).obj G) ≅ A.A), IsMonHom gen.hom → ∀ PP : LB (G2 G).left, ExtLam G (A.L.pull gen.hom.left) PP → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (φ : R →+* W) (GW : Over (Sp W)) [GrpObj GW] [IsCommMonObj GW] (βW : GW.left ⟶ G.left) (DW : DegData W (maximalIdeal W)) (AW : PolAV (Sp (FractionRing W))) (UW : Unif (maximalIdeal W) DW AW GW) (κ : pullback GW.hom (jK W) ⟶ pullback G.hom (jK R)), GlobalTheory.LN.CDvr W → Function.Injective φ → IsLocalHom φ → IsGrpPullback GW G (spMap φ) βW → κ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ βW → LBIso (UW.LG.L.pull (pullback.fst GW.hom (jK W))) ((A.L.pull gen.hom.left).pull κ) → ∀ (R₃ : Type) [CommRing R₃] [IsDomain R₃] [IsLocalRing R₃] (ρ₃ : R →+* R₃) (G₃ : Over (Sp R₃)) [GrpObj G₃] [IsCommMonObj G₃] (β₃ : G₃.left ⟶ G.left) (κ₃ : pullback G₃.hom (jK R₃) ⟶ pullback G.hom (jK R)) (L₃ : LB G₃.left), FinExt ρ₃ → IsGrpPullback G₃ G (spMap ρ₃) β₃ → κ₃ ≫ pullback.fst _ _ = pullback.fst _ _ ≫ β₃ → L₃.IsLB → LBIso (L₃.pull (pullback.fst G₃.hom (jK R₃))) ((A.L.pull gen.hom.left).pull κ₃) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ ∧ IsGrpPullback G₉ G (spMap ρ) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P.L.L) (PP.pull β₉₂) ∧ EvenOn P ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  first | exact @GlobalTheory.Mum.exists_even_package_of_ext | exact GlobalTheory.Mum.exists_even_package_of_ext | (intros; apply GlobalTheory.Mum.exists_even_package_of_ext <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfIdempotentFactorBiex
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_finExt_evenCP_of_factor_extLam : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ ∧ IsGrpPullback G₉ G (spMap ρ₉) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P₉ ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  intro R _ _ _ hR D D' F A' G' _ _ hG' U' oA oG hOL G _ _ hG inc pr hinc hpr hip hpi R₁ _ _ _ ρ₁ G₁ _ _ β₁ β₁₂ A₁ gen₁ hρ₁ hβ₁ hsq₁ hgen₁ hE
  obtain ⟨R₂, _, _, _, ρ₂, D₂, D₂', F₂, A₂', G₂', _, _, U₂', oA₂, oG₂, G₂, _, _, inc₂, pr₂, β₂, β₂₂, A₂, gen₂, W, _, _, _,
    φ, GW, _, _, βW, DW, AW, UW, κ, hρ₂, hR₂, hG₂', hOL₂, hG₂, hinc₂, hpr₂, hip₂, hpi₂, hβ₂, hsq₂, hgen₂, hE₂, hPP₂,
    hW, hφ, hφl, hβW, hκ, hUW⟩ :=
    GlobalTheory.T.exists_finiteExtension_idempotentFactor_trait_unif R hR D D' F A' G' hG' U' oA oG hOL G hG inc pr hinc hpr hip hpi R₁ ρ₁ G₁ β₁ β₁₂ A₁ gen₁ hρ₁ hβ₁ hsq₁ hgen₁ hE
  obtain ⟨R₃, _, _, _, ρ₃, G₃, _, _, β₃, κ₃, L₃, hρ₃, hβ₃, hκ₃, hL₃, hL₃iso⟩ :=
    GlobalTheory.T.exists_finiteExtension_symmBundle_extension_on_factor R₂ hR₂ D₂ D₂' F₂ A₂' G₂' hG₂' U₂' oA₂ oG₂ hOL₂ G₂ hG₂ inc₂ pr₂ hinc₂ hpr₂ hip₂ hpi₂ A₂ gen₂ hgen₂ hE₂
      W hW φ hφ hφl GW βW DW AW UW κ hβW hκ hUW
  obtain ⟨R₉, _, _, _, ρ, G₉, _, _, β₉, β₉₂, P, A₉, gen₉, hρ, hβ₉, hsq₉, hG₉, hlam, hev, hgen₉, hiso₉⟩ :=
    GlobalTheory.T.exists_evenCubicalStructure_of_genericPolarisation_extension R₂ hR₂ G₂ hG₂ A₂ gen₂ hgen₂ _ hE₂ W φ GW βW DW AW UW κ hW hφ hφl hβW hκ hUW R₃ ρ₃ G₃ β₃ κ₃ L₃ hρ₃ hβ₃ hκ₃
      hL₃ hL₃iso
  have hΛ : (abelian₂ G' U'.LG.L).IsLB := LB.isLB_linComb U'.LG.isLB _ _
  have hΛ₂ : (abelian₂ G₂' U₂'.LG.L).IsLB := LB.isLB_linComb U₂'.LG.isLB _ _
  refine ⟨R₉, inferInstance, inferInstance, inferInstance, ρ.comp ρ₂, G₉, inferInstance, inferInstance, β₉ ≫ β₂,
    β₉₂ ≫ β₂₂, P, A₉, gen₉, ⟨hρ.1, hρ.2.1.comp hρ₂.2.1, hρ.2.2.comp hρ₂.2.2⟩, ?_, ?_, hG₉, ?_, hev, hgen₉, hiso₉⟩
  · rw [spMap_comp]
    exact hβ₉.comp hβ₂
  · exact ⟨by rw [Category.assoc, hsq₂.1, ← Category.assoc, hsq₉.1, Category.assoc],
      by rw [Category.assoc, hsq₂.2, ← Category.assoc, hsq₉.2, Category.assoc]⟩
  · have a := GlobalTheory.GenSpread.lbIso_pullback hPP₂ β₉₂
    have b := GlobalTheory.GenSpread.lbIso_pull_pull (pull_isLB hΛ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) β₉₂ (a' := β₉₂ ≫ β₂₂) rfl
    have c := GlobalTheory.GenSpread.lbIso_pull_pull hΛ (β₉₂ ≫ β₂₂)
      (a' := (β₉₂ ≫ β₂₂) ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left) rfl
    have hL : (abelian₂ G₉ P.L.L).IsLB := LB.isLB_linComb P.L.isLB _ _
    refine LBIso.trans hL (pull_isLB (pull_isLB hΛ₂ _) _) (pull_isLB hΛ _) hlam ?_
    refine LBIso.trans (pull_isLB (pull_isLB hΛ₂ _) _) (pull_isLB (pull_isLB (pull_isLB hΛ _) _) _) (pull_isLB hΛ _) a ?_
    refine LBIso.trans (pull_isLB (pull_isLB (pull_isLB hΛ _) _) _) (pull_isLB (pull_isLB hΛ _) _) (pull_isLB hΛ _)
      (LBIso.symm b) (LBIso.symm c)

end GlobalTheory.Mum
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvenCubicalStructureOfIdempotentFactorBiexStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_evenCubicalStructure_of_idempotentFactor_biextension : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) (F : Factor D.toPre D'.toPre) (A' : PolAV (Sp (FractionRing R))) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (U' : Unif (maximalIdeal R) D' A' G') (oA : A'.OAct F.O) (oG : RingAct G' F.O), U'.toUnifPre.OLinear F.O F.o oA oG → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (inc : G ⟶ G') (pr : G' ⟶ G), IsMonHom inc → IsMonHom pr → inc ≫ pr = 𝟙 G → pr ≫ inc = oG.act F.e → ∀ (R₁ : Type) [CommRing R₁] [IsDomain R₁] [IsLocalRing R₁] (ρ₁ : R →+* R₁) (G₁ : Over (Sp R₁)) [GrpObj G₁] [IsCommMonObj G₁] (β₁ : G₁.left ⟶ G.left) (β₁₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R₁))) (gen₁ : (Over.pullback (jK R₁)).obj G₁ ≅ A₁.A), FinExt ρ₁ → IsGrpPullback G₁ G (spMap ρ₁) β₁ → Geo.Tor.IsSquare β₁ β₁₂ → IsMonHom gen₁.hom → ExtLam G₁ (A₁.L.pull gen₁.hom.left) (((abelian₂ G' U'.LG.L).pull (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left).pull β₁₂) → ∃ (R₉ : Type) (_ : CommRing R₉) (_ : IsDomain R₉) (_ : IsLocalRing R₉) (ρ₉ : R →+* R₉) (G₉ : Over (Sp R₉)) (_ : GrpObj G₉) (_ : IsCommMonObj G₉) (β₉ : G₉.left ⟶ G.left) (β₉₂ : (G2 G₉).left ⟶ (G2 G).left) (P₉ : GlobalTheory.UU.CP G₉) (A₉ : PolAV (Sp (FractionRing R₉))) (gen₉ : (Over.pullback (jK R₉)).obj G₉ ≅ A₉.A), FinExt ρ₉ ∧ IsGrpPullback G₉ G (spMap ρ₉) β₉ ∧ Geo.Tor.IsSquare β₉ β₉₂ ∧ IsSemiAbelian G₉ ∧ LBIso (abelian₂ G₉ P₉.L.L) ((abelian₂ G' U'.LG.L).pull (β₉₂ ≫ (lift (fst G G ≫ inc) (snd G G ≫ inc ≫ oG.act F.f) : G2 G ⟶ G2 G').left)) ∧ EvenOn P₉ ∧ IsMonHom gen₉.hom ∧ LBIso (A₉.L.pull gen₉.hom.left) (P₉.L.L.pull (pullback.fst G₉.hom (jK R₉))) := by
  first | exact @GlobalTheory.Mum.exists_finExt_evenCP_of_factor_extLam | exact GlobalTheory.Mum.exists_finExt_evenCP_of_factor_extLam | (intros; apply GlobalTheory.Mum.exists_finExt_evenCP_of_factor_extLam <;> assumption)
end
end
