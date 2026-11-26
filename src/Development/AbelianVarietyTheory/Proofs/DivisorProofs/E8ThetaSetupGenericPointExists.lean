module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitLiftThetaSetupModelAfterExtension
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTraitModuliOfStalkCompleteDVR
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyFlatFinrank
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PlaceEmbeddingsBijectiveInfinitePlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeckeFormOfDoubling
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineSmoothLiftOfRelations

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.E8ThetaSetupGenericPointExists
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

noncomputable section

namespace GlobalTheory.Poinc.GSetup

open GlobalTheory.ThetaSysOfObj

theorem exists_big_ge (g n : ℕ) (hn : 2 ≤ n) (B : ℕ) : ∃ k j₁ : ℕ, 2 ≤ k ∧ B ≤ (n ^ k) ^ 2 ∧ 1 ≤ j₁ ∧ ∀ j ≥ j₁,
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω),
      S.g = g → S.N = (n ^ k) ^ 2 → S.r = n ^ j → S.Big := by
  have lt : ∀ m : ℕ, m < n ^ m := fun m => Nat.lt_pow_self hn
  obtain ⟨k₀, hk₀⟩ := exists_nat_gt (1 + 2 * (g : ℝ) * (2 : ℝ) ^ ((g : ℝ) / 2))
  set K := max k₀ B with hK
  set N := (n ^ (K + 2)) ^ 2 with hN
  have hN₁ : K + 2 < N := (lt _).trans_le (Nat.le_self_pow two_ne_zero _)
  obtain ⟨j₀, hj₀⟩ := exists_nat_gt
    (2 * ((N ^ g * g.factorial : ℕ) : ℝ) * ((g : ℝ) * (3 / 2 : ℝ) ^ g * (2 : ℝ) ^ ((g : ℝ) / 2 - 1)))
  refine ⟨K + 2, j₀ + 6 * (N ^ g * g.factorial) + 1, by omega, ?_, by omega, fun j hj o Ω _ _ _ S hg hS hr => ?_⟩
  · have : B ≤ K := le_max_right _ _
    omega
  have hj' := lt j
  unfold ThetaSys.Big
  rw [hg, hS, hr, ← hN]
  have hk₀K : k₀ ≤ K := le_max_left _ _
  refine ⟨hk₀.trans (by exact_mod_cast (by omega : k₀ < N)), ?_, ?_⟩
  · rw [Nat.cast_mul (n ^ j)]
    exact mul_lt_mul_of_pos_right (hj₀.trans (by exact_mod_cast (by omega : j₀ < n ^ j)))
      (by exact_mod_cast (by omega : 0 < N))
  · exact lt_of_lt_of_le (by omega) (Nat.le_mul_of_pos_right _ (by omega))

theorem exists_big_thetaSys_ge : ∀ (ℓ g : ℕ), ℓ.Prime → Odd ℓ → ∀ B : ℕ, ∃ k j₀ : ℕ, B ≤ (ℓ ^ k) ^ 2 ∧ ∀ j ≥ j₀, ∀ (o Ω : Type) [CommRing o]
    [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω) (J : Type) (b : TBase o ((ℓ ^ j) ^ 2))
    (u : TObj g ((ℓ ^ j) ^ 2) J b (spMap (algebraMap o R))) (w w' : J), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ c ∈ R, x = a / c) →
    u.Prim w w' → ∃ (S : ThetaSys o Ω) (ρ : S.Real) (hR : R ≤ S.R) (φ : ρ.P.A.left ⟶ u.A.left), S.Big ∧
      S.N = (ℓ ^ k) ^ 2 ∧ IsGrpPullback ρ.P.A u.A (spMap (Subalgebra.inclusion hR).toRingHom) φ ∧ LBIso ρ.P.L (u.L.pull φ) := by
  intro n g hn ho B
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨k, j₁, hk, hBk, hj₁, big⟩ := exists_big_ge g n hn.two_le B
  refine ⟨k, j₁ + 2 * k, hBk, fun j hj => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j', j = j' + k * 2 := ⟨j - k * 2, by omega⟩
  rw [pow_add, pow_mul]
  intro o Ω _ _ _ hb R J b u w₁ w₂ hR hΩ hpr
  have := u.ab.comm
  have : NeZero ((n ^ j * (n ^ k) ^ 2) ^ 2) := ⟨by have := hn.pos; positivity⟩
  have hS : ZH.HypS u.A u.L := ⟨u.act w₁, u.act w₂, u.hom w₁, u.hom w₂, hpr.1, hpr.2.2, hpr.2.1⟩
  have hun : IsUnit (n : o) := isUnit_of_dvd_unit (Nat.cast_dvd_cast
    (((dvd_pow_self n (by omega : j ≠ 0)).trans (dvd_mul_right _ _)).trans (dvd_pow_self _ two_ne_zero))) b.unit
  obtain ⟨lev, -⟩ := exists_level R u
  obtain ⟨S, ρ, h, φ, -, hN, hr, hg, hp, hlb, -⟩ :=
    GlobalTheory.ThetaReal.exists_thetaSys_real hL hL₂ o Ω R hR hΩ u.pol n k j b.ζ hn ho hk (by omega) hun hS lev
  exact ⟨S, ρ, h, φ, big j (by omega) o Ω S hg hN hr, hN, hp, hlb⟩

theorem exists_thetaSys_at : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ),
    IsE8 W → ∀ η ∈ genericPoints F.X, ∀ B : ℕ, ∃ (o₁ Ω₁ : Type) (_ : CommRing o₁) (_ : Field Ω₁) (_ : Algebra o₁ Ω₁)
      (_ : ArithBase o₁ Ω₁) (κ : cycAway n →+* o₁) (S : ThetaSys o₁ Ω₁) (ρ : S.Real) (u : Sp S.R ⟶ F.X),
      S.Big ∧ B ≤ S.N ∧ SharpOver F W ρ.P u ∧ (∀ w, (spMap S.R.val.toRingHom ≫ u) w = η) ∧
      spMap S.R.val.toRingHom ≫ u ≫ F.s = spMap ((algebraMap o₁ Ω₁).comp κ) ∧ κ.Finite ∧
      ((spMap S.R.val.toRingHom ≫ u).stalkMap (genericPoint (Sp Ω₁))).hom.Finite := by
  intro g n hg hn ho F W hW η hη B
  obtain ⟨ℓ, hℓ, hℓo, H⟩ := GlobalTheory.T.exists_chart_siegelLevelCover_sharpTheta g n hg hn ho F W hW η hη
  obtain ⟨k, j₀, hBk, Hs⟩ := exists_big_thetaSys_ge ℓ (8 * g) hℓ hℓo B
  obtain ⟨o, Ω, i₁, i₂, i₃, i₄, κ, R, J, b, t, w, w', x, hfg, hfr, hprim, hsh, hηx, hbase, hκ, hst⟩ :=
    H (max j₀ 1) (le_max_right _ _)
  obtain ⟨S, ρ, hR, φ, hbig, hN, hpb, hL⟩ := Hs (max j₀ 1) (le_max_left _ _) o Ω R J b t w w' hfg hfr hprim
  have ef : spMap S.R.val.toRingHom ≫ spMap (Subalgebra.inclusion hR).toRingHom = spMap R.val.toRingHom :=
    (Spec.map_comp (CommRingCat.ofHom (Subalgebra.inclusion hR).toRingHom) (CommRingCat.ofHom S.R.val.toRingHom)).symm
  refine ⟨o, Ω, i₁, i₂, i₃, i₄, κ, S, ρ, spMap (Subalgebra.inclusion hR).toRingHom ≫ x, hbig, hN ▸ hBk,
    hsh _ _ ρ.P φ hpb hL, ?_, ?_, hκ, ?_⟩
  · intro w
    rw [← Category.assoc, ef]
    exact hηx w
  · rw [Category.assoc, ← Category.assoc (spMap S.R.val.toRingHom), ef]
    exact hbase
  · rw [← Category.assoc, ef]
    exact hst

theorem exists_setup : ∀ (g n : ℕ), 1 ≤ g → 3 ≤ n → Odd n → ∀ (F : SFam g n (zetaAway n)) (Z : Scheme.{0}) (z : Z ⟶ Sp (cycAway n))
    (i : F.X ⟶ Z), IsProjOver z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → IsOpenImmersion i → i ≫ z = F.s →
    Dense (Set.range i) → ∀ W : Matrix (Fin 8) (Fin 8) ℤ, IsE8 W → ThetaInt F W i →
    ∀ η ∈ genericPoints F.X, ∀ B : ℕ, ∃ X₁ : Setup F W i, B ≤ X₁.S.N ∧ ∀ w, (spMap X₁.S.R.val.toRingHom ≫ X₁.u) w = η := by
  intro g n hg hn ho F Z z i hproj hZn hopen hiz hden W hW hT η hη B
  obtain ⟨o₁, Ω₁, _, _, _, _, κ, S, ρ, u, hbig, hB, hsharp, hgen, hbase, hκ, hstalk⟩ :=
    exists_thetaSys_at g n hg hn ho F W hW η hη B
  haveI : IsDedekindDomain (cycAway n) := GlobalTheory.CycAwayReg.isDedekindDomain_cycAway _
  haveI : IsProper z := ((isProjOver_iff_isProper_and_exists_isAmpleLB z).1 hproj).1
  have hp : (spMap S.R.val.toRingHom ≫ u ≫ i) ≫ z = spMap ((algebraMap o₁ Ω₁).comp κ) := by
    simp only [Category.assoc, hiz]
    simpa only [Category.assoc] using hbase
  have hst : ((spMap S.R.val.toRingHom ≫ u ≫ i).stalkMap (genericPoint (Sp Ω₁))).hom.Finite := by
    rw [← Category.assoc, Scheme.Hom.stalkMap_comp]
    exact RingHom.Finite.comp hstalk (RingHom.Finite.of_surjective _
      (ConcreteCategory.bijective_of_isIso (i.stalkMap _)).2)
  obtain ⟨M, π, hMn, hπ, hcomp⟩ := GlobalTheory.T.exists_normal_model_normalisation_dedekind (cycAway n) o₁ Ω₁ κ hκ Z z inferInstance inferInstance inferInstance
    (spMap S.R.val.toRingHom ≫ u ≫ i) hp hst
  exact ⟨Setup.mk o₁ Ω₁ S ρ hbig u hsharp (fun w => (hgen w).symm ▸ hη) M (GlobalTheory.IsNormalScheme.of_pred hMn) π hπ hcomp
    hg hn ho z hproj (GlobalTheory.IsNormalScheme.of_pred hZn) hopen hiz hden hW hT κ hbase, hB, hgen⟩

end GlobalTheory.Poinc.GSetup
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineDeRhamAbelianStructureOfStatements
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeOfHyp
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbelianBaseChange

variable {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {X X' : Scheme.{0}}

theorem isPull1_unique {s : X ⟶ Sp R} {s' : X' ⟶ Sp R'} {φ : X' ⟶ X}
    {w : φ ≫ s = s' ≫ spMap (algebraMap R R')} (hu : Function.Injective (pullHyp1 (pairRes φ s')))
    {c : HH1 s} {c₁ c₂ : HH1 s'} (h₁ : IsPull1 w c c₁) (h₂ : IsPull1 w c c₂) : c₁ = c₂ :=
  hu (h₁.symm.trans h₂)

theorem core (s₀ s : X ⟶ Sp R) (hs : s = s₀) (s₀' s' : X' ⟶ Sp R') (hs' : s' = s₀') (φ : X' ⟶ X)
    (hpb : φ ≫ s₀ = s₀' ≫ spMap (algebraMap R R'))
    (m : IsMor (dp0 R) s (dp0 R') s' (algebraMap R R') φ)
    (hcmp : Function.Bijective (cmp1 s)) (hcmp' : Function.Bijective (cmp1 s'))
    (hO : Function.Injective (cmpO s)) (hu : Function.Injective (pullHyp1 (pairRes φ s')))
    (hcl : ClosedForm s₀ = ⊤) (hcl' : ClosedForm s₀' = ⊤)
    (e : R' ⊗[R] HH1 s₀ ≃ₗ[R'] HH1 s₀') (he : ∀ c, IsPull1 hpb c (e (1 ⊗ₜ c)))
    (e' : R' ⊗[R] GlobForm s₀ ≃ₗ[R'] GlobForm s₀') (he' : ∀ c, IsPullForm hpb c (e' (1 ⊗ₜ c))) :
    Function.Bijective (liftSemi m.pull1) ∧
      F1 s' = Submodule.span R' (m.pull1 '' (F1 s : Set (FirstDeRham s))) := by
  subst hs hs'

  have key : ∀ c : FirstDeRham s, cmp1 s' (m.pull1 c) = e (1 ⊗ₜ cmp1 s c) := fun c ↦
    isPull1_unique hu (comparison_pullback m c) (he _)
  let C := LinearEquiv.ofBijective (cmp1 s) hcmp
  let C' := LinearEquiv.ofBijective (cmp1 s') hcmp'
  have hsq : (cmp1 s') ∘ₗ liftSemi m.pull1 =
      e.toLinearMap ∘ₗ (LinearEquiv.baseChange R R' _ _ C).toLinearMap := by
    refine LinearMap.ext fun z ↦ ?_
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; rw [hx, hy]
    | tmul x c =>
      simp only [LinearMap.coe_comp, Function.comp_apply, liftSemi_tmul, map_smul,
        LinearEquiv.coe_coe, LinearEquiv.baseChange_tmul, key]
      rw [← map_smul, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rfl
  refine ⟨?_, ?_⟩
  · have hb : Function.Bijective ((cmp1 s') ∘ liftSemi m.pull1) := by
      have := congrArg DFunLike.coe hsq
      rw [LinearMap.coe_comp] at this
      rw [this, LinearMap.coe_comp]
      exact (e.bijective).comp (LinearEquiv.baseChange R R' _ _ C).bijective
    exact (Function.Bijective.of_comp_iff' hcmp' _).1 hb
  · refine le_antisymm ?_ (Submodule.span_le.2 ?_)
    · intro c' hc'
      have h1 : cmp1 s' c' ∈ CechHodgeFiltration s' := comparison_mem_cechHodgeFiltration s' hc'
      rw [cechHodgeFiltration_eq_range] at h1
      obtain ⟨ω', hω'⟩ := h1
      let Φ : GlobForm s' →ₗ[R'] HH1 s' :=
        clForm s' ∘ₗ (LinearEquiv.ofTop _ hcl').symm.toLinearMap
      let Ψ : R' ⊗[R] GlobForm s →ₗ[R'] FirstDeRham s' := C'.symm.toLinearMap ∘ₗ Φ ∘ₗ e'.toLinearMap
      have hΦ : ∀ ω : ClosedForm s', Φ ω.1 = clForm s' ω := fun ω ↦ by
        simp only [Φ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
          LinearEquiv.ofTop_symm_apply]
      obtain ⟨z, hz⟩ := e'.surjective ω'.1
      have hc'z : c' = Ψ z := by
        apply hcmp'.1
        simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hz, hΦ]
        rw [← hω']
        exact (C'.apply_symm_apply _).symm
      rw [hc'z]
      clear hc'z hz
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
      | tmul x ω =>
        rw [show x ⊗ₜ[R] ω = x • (1 ⊗ₜ[R] ω) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          map_smul]
        refine Submodule.smul_mem _ x (Submodule.subset_span ?_)
        let ωc : ClosedForm s := ⟨ω, hcl ▸ trivial⟩
        refine ⟨C.symm (clForm s ωc), ?_, ?_⟩
        · have hF : clForm s ωc ∈ CechHodgeFiltration s := by rw [cechHodgeFiltration_eq_range]; exact ⟨ωc, rfl⟩
          change toH1O s _ = 0
          apply hO
          rw [← structureSheaf_comparison_comm, map_zero]
          have : cmp1 s (C.symm (clForm s ωc)) = clForm s ωc := C.apply_symm_apply _
          rw [this]
          exact hF
        · apply hcmp'.1
          let ωc' : ClosedForm s' := ⟨e' (1 ⊗ₜ ω), hcl' ▸ trivial⟩
          have h2 : IsPull1 hpb (clForm s ωc) (clForm s' ωc') := IsPullForm.cl (he' ω)
          have h3 := comparison_pullback m (C.symm (clForm s ωc))
          have h4 : cmp1 s (C.symm (clForm s ωc)) = clForm s ωc := C.apply_symm_apply _
          rw [h4] at h3
          rw [isPull1_unique hu h3 h2]
          simp only [Ψ, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
          rw [hΦ ωc']
          exact (C'.apply_symm_apply _).symm
    · rintro _ ⟨c, hc, rfl⟩
      exact m.pullback1_mem_hodgeFiltration hc

end GlobalTheory.AbelianBaseChange

namespace GlobalTheory.AbelianBaseChange

theorem abelianDeRham_baseChange_of_smoothLift (H₁ : GlobalTheory.Published.CrystallineSmoothLift) (H₂ : GlobalTheory.Published.AbelianHodgeDeRham) :
    GlobalTheory.Published.AbelianDeRham.BaseChange := by
  intro R _ A _ g hA hg R' _ _ A' _ φ h
  have hA' : IsAbelianScheme A' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hA h
  have hg' : SmoothOfRelativeDimension g A'.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := g)).of_isPullback h.1 hg
  have hF := GlobalTheory.AbelianPrim.abelianDeRham_free (GlobalTheory.T.abelianDeRhamFree_of_crystalline_comparison H₁ H₂)
  have hP : primDR A = ⊤ := (hF R A g hA hg).1
  have hP' : primDR A' = ⊤ := (hF R' A' g hA' hg').1
  have geom : ∀ {S : Type} [CommRing S] (B : Over (Sp S)) [GrpObj B], IsAbelianScheme B →
      Smooth (B.hom ≫ 𝟙 _) ∧ IsSeparated (B.hom ≫ 𝟙 _) ∧ QuasiCompact (B.hom ≫ 𝟙 _) := by
    intro S _ B _ hB
    rw [Category.comp_id]
    haveI := hB.smooth
    haveI := hB.proper
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨sm, se, sq⟩ := geom A hA
  obtain ⟨sm', se', sq'⟩ := geom A' hA'
  have hcmp := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth H₁ R A.left (A.hom ≫ 𝟙 _) sm se sq).1
  have hcmp' := (GlobalTheory.CechDR.cechDeRham_comparison_bijective_cup_smooth H₁ R' A'.left (A'.hom ≫ 𝟙 _) sm' se' sq').1
  obtain ⟨-, -, -, -, ⟨hcl, -, -⟩, hbc⟩ := H₂ R A g hA hg
  obtain ⟨-, -, -, -, ⟨hcl', -, -⟩, -⟩ := H₂ R' A' g hA' hg'
  obtain ⟨⟨e, he⟩, ⟨e', he'⟩, -⟩ := hbc R' A'.left A'.hom φ h.1
  let m := (GlobalTheory.Published.AbelianDeRham.bcMor h).isMor
  obtain ⟨hB, hF1⟩ := core A.hom (A.hom ≫ 𝟙 _) (Category.comp_id _) A'.hom (A'.hom ≫ 𝟙 _)
    (Category.comp_id _) φ h.1.w m hcmp hcmp' (GlobalTheory.T.structure_sheaf_comparison_injective R A.left _)
    (GlobalTheory.T.affinePairRestriction_injective_firstCohomology φ (A'.hom ≫ 𝟙 _)).2.2 hcl hcl' e he e' he'
  refine ⟨?_, ?_⟩
  · have hsq : (LinearEquiv.ofTop _ hP').toLinearMap ∘ₗ liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor h).pull =
        liftSemi m.pull1 ∘ₗ (LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofTop _ hP)).toLinearMap := by
      refine LinearMap.ext fun z ↦ ?_
      induction z using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _)] at hx hy ⊢; rw [hx, hy]
      | tmul x c => rfl
    have hb : Function.Bijective
        ((LinearEquiv.ofTop _ hP') ∘ liftSemi (GlobalTheory.Published.AbelianDeRham.bcMor h).pull) := by
      have := congrArg DFunLike.coe hsq
      rw [LinearMap.coe_comp] at this
      rw [LinearEquiv.coe_toLinearMap] at this
      rw [this, LinearMap.coe_comp]
      exact hB.comp (LinearEquiv.baseChange R R' _ _ (LinearEquiv.ofTop _ hP)).bijective
    exact (Function.Bijective.of_comp_iff' (LinearEquiv.ofTop _ hP').bijective _).1 hb
  · apply Submodule.map_injective_of_injective (primDR A').injective_subtype
    rw [PrimitiveSubmodule, Submodule.map_comap_eq, Submodule.range_subtype,
      inf_eq_right.2 (by rw [hP']; exact le_top), hF1,
      Submodule.map_span, Set.image_image]
    congr 1
    ext x
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨⟨c, by rw [show prim (dp0 R) (𝟙 (Sp R)) A = ⊤ from hP]; trivial⟩, hc, rfl⟩
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.1, hc, rfl⟩

end GlobalTheory.AbelianBaseChange
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineDeRhamAbelianStructureOfStatements
namespace GlobalTheory.Published

theorem abelianDeRhamStructure_crystallineDeRham_of_hypotheses :
    CrystallineSmoothLift → AbelianHodgeDeRham → AbelianDeRhamStructure ∧ CrystallineDeRham :=
  fun hL hH =>
    ⟨⟨GlobalTheory.Proof.abelianDeRhamFree_of_hodge hL hH, GlobalTheory.T.abelian_hodge_de_rham_of_crystalline_lift hL hH,
      GlobalTheory.AbelianBaseChange.abelianDeRham_baseChange_of_smoothLift hL hH⟩,
     GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift hL⟩

end GlobalTheory.Published
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineDeRhamAbelianStructureOfStatementsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.crystallineDeRham_abelianStructure_of_statements : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.AbelianHodgeDeRham → GlobalTheory.Published.AbelianDeRhamStructure ∧ GlobalTheory.Published.CrystallineDeRham := by
  first | exact @GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses | exact GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses | (intros; apply GlobalTheory.Published.abelianDeRhamStructure_crystallineDeRham_of_hypotheses <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBounded
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBounded
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem continuous_val_mul_conj (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (P : Pair p)
    (a b : ℤ) (σ : k →+* ℂ) (f : X.functionField) (hf : f ∈ P.H a b) (g : X.functionField) (hg : g ∈ P.H a b) :
    Continuous fun y : CxPts p σ => val P a b σ y f * (starRingEnd ℂ) (val P a b σ y g) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  set i := pick (P.L.φ σ).isLB y₀
  set j := pick (P.A.φ σ).isLB y₀
  have hi : y₀ ∈ ptsIn p σ (P.L.B.U i) := mem_pick _ y₀
  have hj : y₀ ∈ ptsIn p σ (P.A.B.U j) := mem_pick _ y₀
  have hW : IsOpen (ptsIn p σ (P.L.B.U i) ∩ ptsIn p σ (P.A.B.U j)) := (isOpen_ptsIn _).inter (isOpen_ptsIn _)
  have hWn := hW.mem_nhds ⟨hi, hj⟩
  have hrf : ContinuousAt (fun y : CxPts p σ => ratVal (P.loc a b f i j) y) y₀ :=
    (GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P a b σ f hf i j).1.continuousAt hWn
  have hrg : ContinuousAt (fun y : CxPts p σ => ratVal (P.loc a b g i j) y) y₀ :=
    (GlobalTheory.T.sectionLocalFunction_continuousOn_holomorphicChart k X p P a b σ g hg i j).1.continuousAt hWn
  have hφ : ContinuousAt ((P.L.φ σ).φ i) y₀ := CInfAt.continuousAt (P.L.cInf σ i y₀ hi)
  have hψ : ContinuousAt ((P.A.φ σ).φ j) y₀ := CInfAt.continuousAt (P.A.cInf σ j y₀ hj)
  have he : ContinuousAt (fun y : CxPts p σ =>
      ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ)) y₀ :=
    Complex.continuous_ofReal.continuousAt.comp (Real.continuous_exp.continuousAt.comp
      (((continuousAt_const.mul hφ).add (continuousAt_const.mul hψ)).neg.div_const 2))
  have hF : ContinuousAt (fun y : CxPts p σ =>
      ratVal (P.loc a b f i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) *
        (starRingEnd ℂ) (ratVal (P.loc a b g i j) y *
          ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ))) y₀ :=
    (hrf.mul he).mul (Complex.continuous_conj.continuousAt.comp (hrg.mul he))
  refine hF.congr ?_
  filter_upwards [hWn] with y hy
  obtain ⟨θ, hθ, hv⟩ := GlobalTheory.T.sectionValueUnitFrame_eq_localFunction_unitScalar k X p P a b σ y i j hy.1 hy.2
  have h1 : θ * (starRingEnd ℂ) θ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hθ]; simp
  rw [hv f hf, hv g hg]
  generalize ratVal (P.loc a b f i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) = A
  generalize ratVal (P.loc a b g i j) y * ((Real.exp (-(a * (P.L.φ σ).φ i y + b * (P.A.φ σ).φ j y) / 2) : ℝ) : ℂ) = B
  rw [map_mul]
  linear_combination (-(A * (starRingEnd ℂ) B)) * h1

theorem nu_eq_sqrt {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} (P : Pair p)
    (a b : ℤ) (σ : k →+* ℂ) (y : CxPts p σ) (f : X.functionField) :
    P.nu a b σ y f = Real.sqrt ((val P a b σ y f * (starRingEnd ℂ) (val P a b σ y f)).re) := by
  rw [← norm_val, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

theorem continuous_val_and_bounded : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ),
      (∀ (σ : k →+* ℂ), ∀ f ∈ P.H a b, ∀ g ∈ P.H a b,
        Continuous fun y : CxPts p σ => val P a b σ y f * (starRingEnd ℂ) (val P a b σ y g)) ∧
      ∀ f ∈ P.H a b, (∀ σ, Continuous fun y : CxPts p σ => P.nu a b σ y f) ∧
        ∃ C : ℝ, ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ C := by
  intro k _ X _ p D hX P a b
  refine ⟨fun σ f hf g hg => continuous_val_mul_conj k X p P a b σ f hf g hg, fun f hf => ?_⟩
  have hc : ∀ σ, Continuous fun y : CxPts p σ => P.nu a b σ y f := fun σ => by
    simp_rw [nu_eq_sqrt]
    exact Real.continuous_sqrt.comp (Complex.continuous_re.comp (continuous_val_mul_conj k X p P a b σ f hf f hf))
  refine ⟨hc, ?_⟩
  have hb : ∀ σ : k →+* ℂ, ∃ C : ℝ, ∀ y : CxPts p σ, P.nu a b σ y f ≤ C := fun σ => by
    haveI := hX.compactSpace σ
    obtain ⟨C, hC⟩ := (isCompact_range (hc σ)).bddAbove
    exact ⟨C, fun y => hC ⟨y, rfl⟩⟩
  choose C hC using hb
  haveI := hX.finite_emb
  obtain ⟨M, hM⟩ := (Set.finite_range C).bddAbove
  exact ⟨M, fun σ y => (hC σ y).trans (hM ⟨σ, rfl⟩)⟩

end GlobalTheory.HSAmp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousHermSectionValueMulConjAndNormBoundedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.continuous_hermSectionValue_mul_conj_and_norm_bounded : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), ∀ (a b : ℤ), (∀ (σ : k →+* ℂ), ∀ f ∈ P.H a b, ∀ g ∈ P.H a b, Continuous fun y : CxPts p σ => val P a b σ y f * (starRingEnd ℂ) (val P a b σ y g)) ∧ ∀ f ∈ P.H a b, (∀ σ, Continuous fun y : CxPts p σ => P.nu a b σ y f) ∧ ∃ C : ℝ, ∀ (σ : k →+* ℂ) (y : CxPts p σ), P.nu a b σ y f ≤ C := by
  first | exact @GlobalTheory.HSAmp.continuous_val_and_bounded | exact GlobalTheory.HSAmp.continuous_val_and_bounded | (intros; apply GlobalTheory.HSAmp.continuous_val_and_bounded <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernel
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem exists_factor_of_isogeny : ∀ (K : Type) [Field K] (A B C : AbVar K) (q : A ⟶ B) (f : A ⟶ C), IsIsogeny q → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 → x ≫ f.hom = 1) → ∃ g : B ⟶ C, q ≫ g = f := by
  intro K _ A B C q f hq hker
  have hflat : Flat q.hom.left := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B q hq).2.1
  have hfin : IsFinite q.hom.left := hq.1
  have hsurj : Surjective q.hom.left := hq.2
  have hqc : QuasiCompact q.hom.left := inferInstance
  obtain ⟨⟨ψ, hψ, hc⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective _ A.X B.X C.X q.hom f.hom
    inferInstance inferInstance hflat hsurj hqc hker
  refine ⟨Hom.mk ψ, ?_⟩
  apply Subtype.ext
  exact hc

end GlobalTheory.AV.AbVar
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorThroughIsogenyOfKillsKernelStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_through_isogeny_of_kills_kernel : ∀ (K : Type) [Field K] (A B C : AbVar K) (q : A ⟶ B) (f : A ⟶ C), IsIsogeny q → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ q.hom = 1 → x ≫ f.hom = 1) → ∃ g : B ⟶ C, q ≫ g = f := by
  first | exact @GlobalTheory.AV.AbVar.exists_factor_of_isogeny | exact GlobalTheory.AV.AbVar.exists_factor_of_isogeny | (intros; apply GlobalTheory.AV.AbVar.exists_factor_of_isogeny <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenProductOfLocalLevelsUnitary
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenProductOfLocalLevelsUnitary
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT

theorem isOpen_globLev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S K' : Set (finU (E := E) (n := n))) := by
  intro E _ _ _ hU n S K' hK
  have hT : {w : Pl E | ¬ K' w = KL n w}.Finite := Filter.eventually_cofinite.1 hK.2
  let f : ∀ w : Pl E, finU (E := E) (n := n) → UL n w := fun w x => ⟨cLoc w x.1, GlobalTheory.BCT.ThBasic.cLoc_mem_UL hU n w x.1⟩
  have hf : ∀ w, Continuous (f w) := fun w =>
    Continuous.subtype_mk ((GlobalTheory.DefU.Inert.continuous_cLoc w).comp continuous_subtype_val) _
  have h1 : ∀ w, f w 1 = 1 := fun w => Subtype.ext (by simp [f])
  have hA : ∀ᶠ k : finU (E := E) (n := n) in nhds 1, ∀ w : Pl E, cLoc w (k : UA E n) ∈ GlobalTheory.LFun.KGL w (n := n) := by
    filter_upwards [(UpperTheory.unitaryAdelic_localComponents_continuous_levels_open E n).2.2] with k hk w
    exact (SetLike.ext_iff.1 (GlobalTheory.SmGL.SphCompletion.KO_completion w n) _).1 (hk w)
  have hB : ∀ᶠ k : finU (E := E) (n := n) in nhds 1, ∀ w ∈ {w : Pl E | ¬ K' w = KL n w}, f w k ∈ K' w := by
    refine (Filter.eventually_all_finite hT).2 fun w _ => ?_
    have ho : IsOpen ((f w) ⁻¹' (K' w : Set (UL n w))) := ((hK.1 w).1).preimage (hf w)
    exact ho.mem_nhds (by simp [h1])
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [hA, hB] with x hxA hxB
  refine Subgroup.mem_iInf.2 fun w => Subgroup.mem_iInf.2 fun _ => ?_
  refine Subgroup.mem_comap.2 (Subgroup.mem_map.2 ⟨f w x, ?_, rfl⟩)
  by_cases hw : K' w = KL n w
  · rw [hw]
    exact Subgroup.mem_subgroupOf.2 (hxA w)
  · exact hxB w hw

end GlobalTheory.BCT
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenProductOfLocalLevelsUnitaryStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_productOfLocalLevelsUnitary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ) (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → IsOpen (globLev S K' : Set (finU (E := E) (n := n))) := by
  first | exact @GlobalTheory.BCT.isOpen_globLev | exact GlobalTheory.BCT.isOpen_globLev | (intros; apply GlobalTheory.BCT.isOpen_globLev <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeEqCardKernelOfKilledByInvertible
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeEqCardKernelOfKilledByInvertible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.DegSep

variable {S : Scheme.{0}}

theorem one_left' (T : Over S) (G : Over S) [GrpObj G] : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  have h := Over.w (toUnit T)
  change (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left]
  congr 1

theorem comp_pow_id (T G : Over S) [GrpObj G] (x : T ⟶ G) (n : ℕ) : x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, pow_succ, MonObj.comp_mul, ih, Category.comp_id]

end GlobalTheory.AV.DegSep

namespace GlobalTheory.AV.DegSep

theorem isUnit_natCast_Γ (K : Type) [Field K] (n : ℕ) (hn : (n : K) ≠ 0) : IsUnit (n : Γ(Sp K, ⊤)) := by
  have h : IsUnit (n : K) := hn.isUnit
  have := h.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  simpa using this

theorem deg_eq_card_ker (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ) (hn : (n : K) ≠ 0)
    (hiso : IsIsogeny f) (hker : ∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) :
    deg f = Nat.card (ptMap f).ker := by
  have hfl : Flat f.hom.left := (GlobalTheory.T.dim_eq_flat_finrank_eq_deg_of_isIsogeny K A B f hiso).2.1
  have hfin : IsFinite f.hom.left := hiso.1
  have hprop : IsProper B.X.hom := B.ab.proper
  let e : Sp K ⟶ B.X.left := η[B.X].left
  have he1 : e ≫ B.X.hom = 𝟙 _ := Over.w η[B.X]
  have hecl : IsClosedImmersion e := by
    have : IsClosedImmersion (e ≫ B.X.hom) := by rw [he1]; infer_instance
    exact IsClosedImmersion.of_comp e B.X.hom
  let p := pullback.snd f.hom.left e
  let i := pullback.fst f.hom.left e
  have hpi : i ≫ A.X.hom = p := by
    calc i ≫ A.X.hom = i ≫ f.hom.left ≫ B.X.hom := by rw [Over.w f.hom]
      _ = p ≫ e ≫ B.X.hom := by rw [← Category.assoc, pullback.condition, Category.assoc]
      _ = p := by rw [he1, Category.comp_id]
  have hifu : FormallyUnramified i := inferInstance

  let T : Over (Sp K) := Over.mk (i ≫ A.X.hom)
  let x : T ⟶ A.X := Over.homMk i
  have hx1 : x ≫ f.hom = 1 := by
    ext1
    rw [Over.comp_left, one_left']
    change i ≫ f.hom.left = (i ≫ A.X.hom) ≫ e
    rw [hpi, pullback.condition]
  have hxn := hker T x hx1
  have hleft : i ≫ (Out.mulA A.X n).left = p ≫ η[A.X].left := by
    have h : (x ^ n).left = (1 : T ⟶ A.X).left := by rw [hxn]
    rw [← comp_pow_id, one_left'] at h
    change i ≫ (Out.mulA A.X n).left = _ at h
    rw [h]
    change (i ≫ A.X.hom) ≫ _ = _
    rw [hpi]
  let j : pullback f.hom.left e ⟶ pullback (Out.mulA A.X n).left η[A.X].left :=
    pullback.lift i p hleft
  have hmu : FormallyUnramified (Out.mulA A.X n).left :=
    GlobalTheory.formallyUnramified_mulA (Sp K) A.X n (isUnit_natCast_Γ K n hn)
  have hsnd : FormallyUnramified (pullback.snd (Out.mulA A.X n).left η[A.X].left) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) hmu
  have hjfu : FormallyUnramified j := by
    have : FormallyUnramified (j ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; exact hifu
    exact FormallyUnramified.of_comp j (pullback.fst _ _)
  have hpfu : FormallyUnramified p := by
    have : j ≫ pullback.snd _ _ = p := pullback.lift_snd _ _ _
    rw [← this]
    exact MorphismProperty.comp_mem (@FormallyUnramified) _ _ hjfu hsnd
  have hpet : Etale p := Etale.of_formallyUnramified_of_flat p

  let t : Sp (AlgebraicClosure K) ⟶ Sp K := (ptOver K (AlgebraicClosure K)).hom
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank p t (IsLocalRing.closedPoint _)
  rw [Scheme.Hom.finrank_pullback_snd] at hcard
  have horig : e (t (IsLocalRing.closedPoint _)) = B.origin := by
    rw [origin, one_left']
    change e _ = (𝟙 (Sp K) ≫ e) _
    rw [Category.id_comp]
    congr 1
    exact Subsingleton.elim _ _
  rw [horig] at hcard
  rw [deg, if_pos hiso, ← hcard]
  symm
  refine Nat.card_congr ?_
  exact
    { toFun := fun y => ⟨pullback.lift y.1.left t (by
          have h := y.2
          rw [MonoidHom.mem_ker, ptMap_apply] at h
          have h2 : (y.1 ≫ f.hom).left = (1 : ptOver K (AlgebraicClosure K) ⟶ B.X).left := by rw [h]
          rw [Over.comp_left, one_left'] at h2
          exact h2), pullback.lift_snd _ _ _⟩
      invFun := fun y => ⟨Over.homMk (y.1 ≫ i) (by
          change (y.1 ≫ i) ≫ A.X.hom = t
          rw [Category.assoc, hpi, y.2]), by
          rw [MonoidHom.mem_ker, ptMap_apply]
          ext1
          rw [Over.comp_left, one_left']
          change (y.1 ≫ i) ≫ f.hom.left = t ≫ e
          rw [Category.assoc, pullback.condition, ← Category.assoc, y.2]⟩
      left_inv := fun y => by
        apply Subtype.ext
        ext1
        exact pullback.lift_fst _ _ _
      right_inv := fun y => by
        apply Subtype.ext
        apply pullback.hom_ext
        · exact pullback.lift_fst _ _ _
        · rw [pullback.lift_snd]; exact y.2.symm }

end GlobalTheory.AV.DegSep

namespace GlobalTheory.AV.DegSep

theorem deg_eq_card_ker_of_killed : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ), (n : K) ≠ 0 →
    IsIsogeny f → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) →
    deg f = Nat.card (ptMap f).ker :=
  fun K _ A B f n hn hiso hker => deg_eq_card_ker K A B f n hn hiso hker

end GlobalTheory.AV.DegSep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyDegreeEqCardKernelOfKilledByInvertibleStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isogenyDegree_eq_card_kernel_of_killed_by_invertible : ∀ (K : Type) [Field K] (A B : AbVar K) (f : A ⟶ B) (n : ℕ), (n : K) ≠ 0 → IsIsogeny f → (∀ (T : Over (Sp K)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ n = 1) → deg f = Nat.card (ptMap f).ker := by
  first | exact @GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed | exact GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed | (intros; apply GlobalTheory.AV.DegSep.deg_eq_card_ker_of_killed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeFormAnisoOfGlobalEuler
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantOneMemCuspFormsOfWittIndexZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantOneMemCuspFormsOfWittIndexZero
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

namespace GlobalTheory

theorem constant_one_mem_cuspForms_of_wittIndex_zero : ∀ {D : D7} {θ : InfFam D} {A B : HSp D} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A}, HidaSetting θ A B sA sB t cA → wittIndex A = 0 → (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := by
  intro D θ A B sA sB t cA _ h
  rw [wittIndex_eq_zero_iff_isAniso] at h
  exact (mem_cuspForms).2 ⟨⟨isAutFunSm_const θ A 1, fun r C hC => absurd hC (h r C)⟩, .of_invariant fun _ _ _ => rfl⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantOneMemCuspFormsOfWittIndexZeroStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_mem_A0_of_wittIndex_eq_zero : ∀ {D : D7} {θ : InfFam D} {A B : HSp D} {sA : RealMat A} {sB : RealMat B} {t : ℕ} {cA : CptF A}, HidaSetting θ A B sA sB t cA → wittIndex A = 0 → (fun _ : GA D A => (1 : ℂ)) ∈ A0 θ A cA := by
  intro D θ A B sA sB t cA h h0
  exact GlobalTheory.constant_one_mem_cuspForms_of_wittIndex_zero (B := B) (sA := sA) (sB := sB) (t := t) h h0
end
end

open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.BottomRallis

variable {D : D7}

theorem siegelWeilFockAniso_of_siegelWeilAnisotropic (hSW : GlobalTheory.Published.SiegelWeilAnisotropicUnitary) (D : D7) :
    SiegelWeilFockAniso D := by
  intro ψ A B ha hab hB χB omh homh a hmaj θ sS sB hθ hS hBc hKc ν 𝓕 hcov mH hmH φ hF
  have hK := GlobalTheory.T.fock_vector_finite_under_compact_commuting_cartan D ψ θ (dblSp A) B 1 χB omh sS sB homh hθ hS hBc (Khat A a) (isCompact_Khat A a) hKc φ hF
  have hI : HasIwasawa D.sp.cm.sig (dblSp A).gram (Khat A a) :=
    GlobalTheory.T.adelicIwasawa_doubledGroup_selfDualLattice D A (frameLat A) a (GlobalTheory.WeilAtPlace.isSelfDualC_frameLat A) hmaj
  have hB' : IsAniso B := wittIndex_eq_zero_iff_isAniso.1 hB
  obtain ⟨hint, hv⟩ := hSW D ψ A B ha (ha.trans hab.le) hB' χB omh homh a hmaj hI ν 𝓕 hcov mH hmH φ hF.1 hK
  rw [if_pos hab, one_smul] at hv
  exact ⟨hint, hv⟩

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

variable {D : D7}

theorem heckeFormAniso_of_global_euler (D : D7) (hG : GlobalFormAniso D) (hE : EulerRight D) : HeckeFormAniso D := by
  intro ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP hw LA LB Sf Φ₁ Φ₂ hF₁ hF₂ hU m mH hm hmH u₁ hu₁ u₂ hu₂ par hpar
    hsph hs
  obtain ⟨s₁, hs₁, hint⟩ := hs
  obtain ⟨hUp₁, hUp₂, hZint, z, hz, hpet⟩ :=
    hG A LA hU.sdA ψ θ B χA χB sA sB t cA a om ν 𝓕 hP hw m mH hm hmH Φ₁ Φ₂ hF₁ hF₂ u₁ hu₁ u₂ hu₂
  obtain ⟨hA1, ht1, hB, -⟩ := hP.setting
  have hs0 : sZero A B = (t : ℂ) / 2 := by
    simp only [sZero, hB]; push_cast; ring
  have hs0re : (sZero A B).re = (t : ℝ) / 2 := by rw [hs0]; simp
  obtain ⟨hcont, hbd, -⟩ := GlobalTheory.T.doubledLatticeHeightFun_properties D A LA a hU.sdA hP.maj
  have hflat : ∀ s, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s =
      GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
        (fun g => (hgtL A LA a g : ℝ)) (sZero A B) s := by
    intro s; funext g
    simp only [integrand, GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand, npow]; ring
  have hmeas : Measurable (fun g => (hgtL A LA a g : ℝ)) := (NNReal.continuous_coe.comp hcont).measurable
  have hfz := GlobalTheory.T.flatFamilyZeta_convergence_holomorphy (GA D A) (m.restrict (openOff A LA Sf)) (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g)
    (fun g => (hgtL A LA a g : ℝ)) (sZero A B) (s₁ : ℂ) hmeas (fun g => by exact_mod_cast (hbd g).1)
    (fun g => by exact_mod_cast (hbd g).2) (by rw [← hflat]; exact hint)
  have hint0 : IntegrableOn (fun g => wcoef om ν 𝓕 Φ₁ Φ₂ g * rcoef m u₁ u₂ g) (openOff A LA Sf) m := by
    have := hfz.1.1 (sZero A B) (by simp only [Set.mem_setOf_eq, Complex.ofReal_re, hs0re]; linarith)
    rwa [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatIntegrand_self] at this
  refine ⟨hUp₁, hUp₂, hint0, fun l hl => ?_⟩
  have hd := GlobalTheory.T.partialNormalizingFactorProduct_analytic_ne_zero D (Sf : Set (FinPl D)) A.rank B.rank
  have hER : EqRight (fun s => ∫ g, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (fun s => LFun.LSD D Sf par χB (s + 1 / 2) / LFun.dSfun D.host.E (Sf : Set (FinPl D)) A.rank B.rank s *
        ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m) := by
    refine ⟨(A.rank : ℝ) + 1, fun s hs => ?_⟩
    have hs' : (A.rank : ℝ) + 1 < s.re := hs
    refine hE ψ θ A B χA χB sA sB t cA a om ν 𝓕 hP LA LB Sf Φ₁ Φ₂ hF₁.1 hF₂.1 hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph s hs'
      (hZint s ?_)
    have : (0 : ℝ) ≤ A.rank := Nat.cast_nonneg _
    linarith
  have hY : DifferentiableOn ℂ (fun s => ∫ g in openOff A LA Sf, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m)
      (rightOf s₁) := by
    have h2 := hfz.2.1
    simp only [Complex.ofReal_re] at h2
    refine h2.congr fun s _ => ?_
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.flatZeta, hflat]
  have hL : HolValueAt (fun s => LFun.LSD D Sf par χB (s + 1 / 2)) (sZero A B) l := by rw [hs0]; exact hl
  have hmain := GlobalTheory.T.holomorphicContinuationValue_eq_div_mul _ _ _ _ (sZero A B) z l s₁ (by rw [hs0re]; positivity) (by rw [hs0re]; exact hs₁)
    hd.1 (fun s hs => (hd.2 s hs).1) hY hER hz hL
  rw [hpet, hmain, ← hs0]
  simp only [integrand_sZero]
  ring

theorem rcoef_one {A : HSp D} (m : Measure (GA D A)) (g : GA D A) :
    rcoef m (fun _ : GA D A => (1 : ℂ)) (fun _ => 1) g = (volQ A m : ℂ) := by
  simp [rcoef, petersson, pet, rTr, GlobalTheory.AutomorphicL2Unitary.descend, volQ]

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

variable {D : D7}

end GlobalTheory.BottomRallis

namespace GlobalTheory.BottomRallis

theorem prod_range_sub_eq_prod_Icc (f : ℤ → ℂ) (a h : ℕ) (e : ℤ) (he : (a : ℤ) = h + e) :
    ∏ i ∈ Finset.range a, f ((h : ℤ) - i) = ∏ s ∈ Finset.Icc (1 - e) (h : ℤ), f s := by
  refine Finset.prod_nbij' (fun i => (h : ℤ) - i) (fun s => ((h : ℤ) - s).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range] at hi
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc]
    omega
  · intro s hs
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hs
    simp only [Finset.coe_range, Set.mem_Iio, Finset.mem_coe, Finset.mem_range]
    omega
  · intro i _
    simp
  · intro s hs
    simp only [Finset.coe_Icc, Set.mem_Icc, Finset.mem_coe, Finset.mem_Icc] at hs
    omega
  · intro i _
    rfl

end GlobalTheory.BottomRallis
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianDualCrystalOfDualAbelianScheme
namespace GlobalTheory

theorem abelianDualCrystal_of_dualAbelianScheme :
    GlobalTheory.Published.DualAbelianScheme → GlobalTheory.Published.AbelianDualCrystal :=
  fun h ↦ ⟨h, GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.toCrystallineDeRham⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelian
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelian
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PtExt

theorem toH1O_surjective_of_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) := by
  intro hH R _ A _ g hab hdim
  rw [Category.comp_id]
  have hsm : Smooth A.hom := hab.smooth
  have hsep : IsSeparated A.hom := by haveI := hab.proper; infer_instance
  have hqc : QuasiCompact A.hom := by haveI := hab.proper; infer_instance
  have hcmp := GlobalTheory.Published.CrystallineSmoothLift.bijective_cechDeRhamComparison_degreeOne
    GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations A.hom hsm hsep hqc
  have hsurj : Function.Surjective (GlobalTheory.CechDR.toHO1 A.hom) := (hH R A g hab hdim).2.2.2.2.1.2.2
  intro u
  obtain ⟨h, hh⟩ := hsurj (GlobalTheory.CechDR.cmpO A.hom u)
  obtain ⟨c, rfl⟩ := hcmp.2 h
  refine ⟨c, GlobalTheory.CechDR.cmpO_injective R A.left A.hom ?_⟩
  rw [← GlobalTheory.CechDR.structureSheaf_comparison_comm, hh]

end GlobalTheory.PtExt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamToH1StructureSurjectiveAbelianStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.de_rham_to_h1_structure_surjective_abelian : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → Function.Surjective (toH1O (A.hom ≫ 𝟙 _)) := by
  first | exact @GlobalTheory.PtExt.toH1O_surjective_of_abelian | exact GlobalTheory.PtExt.toH1O_surjective_of_abelian | (intros; apply GlobalTheory.PtExt.toH1O_surjective_of_abelian <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamComparisonBijectiveComplexA
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamComparisonBijectiveComplexA
set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem crystallineCechDeRhamComparison_bijective_complexAbelian :
    ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → Function.Bijective (cmp1 (str A)) := by
  intro A _ hA
  have := hA.smooth
  have := hA.proper
  exact GlobalTheory.SmoothLift.crystallineSmoothLift_of_relations.bijective_cechDeRhamComparison_degreeOne (str A)
    inferInstance inferInstance inferInstance

end GlobalTheory.CechPer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineCechDeRhamComparisonBijectiveComplexAStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bijective_cmp1_of_isAbelianScheme_over_complex : ∀ (A : Over (Sp ℂ)) [GrpObj A], IsAbelianScheme A → Function.Bijective (cmp1 (str A)) := by
  first | exact @GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian | exact GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian | (intros; apply GlobalTheory.CechPer.crystallineCechDeRhamComparison_bijective_complexAbelian <;> assumption)
end
end
