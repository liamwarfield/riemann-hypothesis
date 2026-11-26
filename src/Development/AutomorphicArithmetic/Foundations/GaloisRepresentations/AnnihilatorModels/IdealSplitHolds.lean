module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MUKerW
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTjExF
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.DivCOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTorsFree
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobIsog
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MTanOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLineC
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MCotanOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SpMapAlgComp
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MQuasiInv
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.CongKSOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtChart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSameNormRing
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PMatching

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLevPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.levPull_of :
    PullKer → LevPull := by
  intro _ p _ D R _ b N S S' s s' f o o₁ m 𝔞 ρ lv h
  exact GlobalTheory.UPel.HT.EtLev.isEtLev_exists_pull m h
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MGrCard
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.grCard_of :
    GrCard := by
  intro k H _ _ _ _ n j hn
  have hdim : Module.finrank k H = Module.finrank k (Fin n → k) := by simp [hn]
  let e : H ≃ₗ[k] (Fin n → k) := LinearEquiv.ofFinrankEq H (Fin n → k) hdim
  apply Nat.card_congr
  refine (Submodule.orderIsoMapComap e).toEquiv.subtypeEquiv ?_
  intro D
  change Module.finrank k D = j ↔ Module.finrank k (D.map (e : H →ₗ[k] (Fin n → k))) = j
  rw [LinearEquiv.finrank_map_eq]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRepOfFF
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.repOfFF_of :
    AlgOf → RepOfFF := by
  rintro hA κ _ A P ⟨K, i, hm, hfin, hfl, hP⟩
  obtain ⟨B, _, _, k, hf, hfr, pb⟩ := hA (Sp κ) K.left K.hom hfin hfl κ (𝟙 _)
  have hk : IsIso k := pb.isIso_fst_of_isIso
  have hw : k ≫ K.hom = spMap (algebraMap κ B) := by
    simpa using pb.w
  let e : algPt κ B ≅ K := Over.isoMk (asIso k) hw
  refine ⟨Module.finrank κ B, B, ‹_›, ‹_›, hf, hfr, rfl, e.hom ≫ i, inferInstance, fun T g => ?_⟩
  rw [← hP T g]
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y ≫ e.hom, by simpa using hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y ≫ e.inv, by simpa using hy⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MGenDown
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private lemma closed_iff {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {X : Scheme.{0}} (s : X ⟶ Spec (CommRingCat.of O)) (z : X) :
    s z = IsLocalRing.closedPoint O ↔ z ∉ X.basicOpen (fn s ϖ) := by
  have key : z ∈ X.basicOpen (fn s ϖ) ↔ ϖ ∉ (s z).asIdeal := by
    rw [show X.basicOpen (fn s ϖ) = s ⁻¹ᵁ (Spec (CommRingCat.of O)).basicOpen
        ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) from (Scheme.preimage_basicOpen_top s _).symm]
    change s z ∈ (Spec (CommRingCat.of O)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of O)).inv ϖ) ↔ _
    rw [basicOpen_eq_of_affine]
    exact PrimeSpectrum.mem_basicOpen _ _
  rw [key, not_not]
  constructor
  · intro h
    have hm : (s z).asIdeal = IsLocalRing.maximalIdeal O := congrArg PrimeSpectrum.asIdeal h
    rw [hm]
    exact (IsLocalRing.mem_maximalIdeal _).mpr hϖ.not_isUnit
  · intro h
    have hne : (s z).asIdeal ≠ ⊥ := fun hb0 => hϖ.ne_zero (by simpa [hb0] using h)
    exact PrimeSpectrum.ext (IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne (s z).2))

theorem UpperTheory.Gal.crystallineComparison.Mod.genDown_of :
    GenDown := by
  intro O _ _ _ ϖ hϖ X Y s h hflat y hy
  have hc : ∀ y' : Y, s (h y') = IsLocalRing.closedPoint O ↔
      y' ∉ Y.basicOpen (fn (h ≫ s) ϖ) := by
    intro y'
    rw [← closed_iff hϖ (h ≫ s) y', Scheme.Hom.comp_apply]
  refine ⟨(hc y).mpr hy.1, fun z' hz' hsp => ?_⟩
  obtain ⟨y', hy'sp, rfl⟩ := Flat.generalizingMap h hsp
  have := hy.2 y' ((hc y').mp hz') hy'sp
  rw [this]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MFrobRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.frobRing_of :
    FrobRing := by
  intro p f hp κ _ _ A _ B Λ _ _ _ _ i hi ε₀ hε ν g hg
  have hpΛ : (p : Λ) = 0 := by
    have h := map_natCast (algebraMap κ Λ) p
    rw [CharP.cast_eq_zero κ p, map_zero] at h
    exact h.symm
  let σ : Λ →+* Λ := GlobalTheory.SS.FrobField.powHom Λ p f hp hpΛ
  have hσ : ∀ c, σ c = c ^ p ^ f := fun _ => rfl
  have h0 : (p : Γ(Sp Λ, ⊤)) = 0 := GlobalTheory.SS.FrobField.cast_zero_sp Λ hpΛ
  have hfr : GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 = spMap σ :=
    GlobalTheory.SS.FrobField.absFrob_spec Λ p f hp h0 σ hσ
  have hmono : Mono i.left := (Over.forget _).map_mono i
  have h1 : (1 : algPt κ Λ ⟶ A).left = spMap (algebraMap κ Λ) ≫ spMap ε₀.toRingHom ≫ i.left := by
    have e : (1 : algPt κ Λ ⟶ A) = toUnit (algPt κ Λ) ≫ (1 : 𝟙_ (Over (Sp κ)) ⟶ A) := by
      simp
    have e2 : (toUnit (algPt κ Λ)).left = spMap (algebraMap κ Λ) := by
      have := Over.w (toUnit (algPt κ Λ))
      simpa using this
    rw [e, Over.comp_left, e2]
    exact congrArg (spMap (algebraMap κ Λ) ≫ ·) hε.symm
  have sc : ∀ {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (u : R →+* S) (v : S →+* T),
      spMap v ≫ spMap u = spMap (v.comp u) := by
    intro R S T _ _ _ u v
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  have key : FrobKill p f hp g ↔ σ.comp ν.toRingHom = (σ.comp (algebraMap κ Λ)).comp ε₀.toRingHom := by
    constructor
    · intro h
      have h2 := h h0
      change GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 ≫ g.left =
        GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp h0 ≫ (1 : algPt κ Λ ⟶ A).left at h2
      rw [hfr, hg, h1] at h2
      simp only [← Category.assoc] at h2
      have h3 := (cancel_mono i.left).1 h2
      rw [sc, sc, sc] at h3
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective h3)
    · intro h hh
      change GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh ≫ g.left =
        GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh ≫ (1 : algPt κ Λ ⟶ A).left
      rw [show GlobalTheory.SS.FrobField.absFrob (Sp Λ) p f hp hh = spMap σ from hfr, hg, h1]
      simp only [← Category.assoc]
      rw [sc, sc, sc, h]
  rw [key]
  constructor
  · intro h x hx
    have := RingHom.congr_fun h x
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, hx, map_zero] at this
    rw [hσ] at this
    exact this
  · intro h
    ext x
    have hy : ε₀ (x - algebraMap κ B (ε₀ x)) = 0 := by
      simp
    have h2 := h _ hy
    have h3 : σ (ν (x - algebraMap κ B (ε₀ x))) = 0 := by rw [hσ]; exact h2
    rw [map_sub, map_sub, AlgHom.commutes, sub_eq_zero] at h3
    simpa using h3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MRingHomog
noncomputable section

namespace UpperTheory.Gal.crystallineComparison.Mod

private theorem exists_algHom_ker (κ B : Type) [Field κ] [IsAlgClosed κ] [CommRing B] [Algebra κ B]
    [Module.Finite κ B] (p : PrimeSpectrum B) :
    ∃ ε : B →ₐ[κ] κ, RingHom.ker ε.toRingHom = p.asIdeal := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime p.asIdeal
  letI : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field _
  have hb : Function.Bijective (algebraMap κ (B ⧸ p.asIdeal)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e := AlgEquiv.ofBijective (Algebra.ofId κ (B ⧸ p.asIdeal)) hb
  refine ⟨(e.symm : (B ⧸ p.asIdeal) →ₐ[κ] κ).comp (Ideal.Quotient.mkₐ κ p.asIdeal), ?_⟩
  ext x
  change x ∈ RingHom.ker _ ↔ x ∈ p.asIdeal
  simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem ringHomog_of : RingHomog := by
  intro κ B _ _ _ _ _ ε₀ _ hτ
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI hfin : Module.Finite κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) :=
    Module.Finite.of_surjective
      (Algebra.algHom κ B (Localization.AtPrime (RingHom.ker ε₀.toRingHom))).toLinearMap
      (IsArtinianRing.localization_surjective (RingHom.ker ε₀.toRingHom).primeCompl
        (Localization.AtPrime (RingHom.ker ε₀.toRingHom)))
  have hm : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) =
        (Module.finrank κ (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) : ℕ∞) := by
    intro p
    obtain ⟨ε, hε⟩ := exists_algHom_ker κ B p
    obtain ⟨τ, hτε⟩ := hτ ε
    rw [GlobalTheory.FinSchemeRank.finrank_eq_length_of_isLocalRing κ]
    have hmap : p.asIdeal.primeCompl.map τ.toRingEquiv.toMonoidHom =
        (RingHom.ker ε₀.toRingHom).primeCompl := by
      ext y
      simp only [Submonoid.mem_map, Ideal.mem_primeCompl_iff, ← hε, RingHom.mem_ker, ← hτε]
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact hx
      · intro hy
        refine ⟨τ.symm y, ?_, ?_⟩
        · simpa using hy
        · simp
    exact GlobalTheory.FinSchemeRank.length_self_eq_of_ringEquiv
      (IsLocalization.ringEquivOfRingEquiv (Localization.AtPrime p.asIdeal)
        (Localization.AtPrime (RingHom.ker ε₀.toRingHom)) τ.toRingEquiv hmap)
  have h := GlobalTheory.FinSchemeRank.finrank_eq_card_mul κ B _ hm
  rw [← GlobalTheory.FinSchemeRank.card_algHom_eq_card_primeSpectrum κ B] at h
  exact_mod_cast h

end UpperTheory.Gal.crystallineComparison.Mod
end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MChainRing
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.chainRing_of :
    ChainLoc → ChainRing := by
  intro hC κ B B' Λ _ _ _ _ _ _ _ _ _ π ε' _ q hπ hq hex εΛ g hg
  obtain ⟨t, ht, htm⟩ := hex
  set m : Ideal B := RingHom.ker (ε'.comp π).toRingHom with hm
  set m' : Ideal B' := RingHom.ker ε'.toRingHom with hm'
  haveI : m.IsPrime := RingHom.ker_isPrime _
  haveI : IsArtinianRing B := IsArtinianRing.of_finite κ B
  haveI : Module.Finite κ B' := Module.Finite.of_surjective π.toLinearMap hπ
  haveI : IsArtinianRing B' := IsArtinianRing.of_finite κ B'
  have hsurj : Function.Surjective (algebraMap B (Localization.AtPrime m)) :=
    IsArtinianRing.localization_surjective m.primeCompl _
  have hsurj' : Function.Surjective (algebraMap B' (Localization.AtPrime m')) :=
    IsArtinianRing.localization_surjective m'.primeCompl _
  haveI : Module.Finite κ (Localization.AtPrime m) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom κ B (Localization.AtPrime m)).toLinearMap hsurj
  haveI : IsArtinianRing (Localization.AtPrime m) := IsArtinianRing.of_finite κ _
  have hmem : ∀ x, x ∈ m ↔ ε' (π x) = 0 := fun x => by simp [m, RingHom.mem_ker]
  have hmem' : ∀ y, y ∈ m' ↔ ε' y = 0 := fun y => by simp [m', RingHom.mem_ker]
  have hunit : ∀ s, ε' (π s) ≠ 0 → IsUnit (g s) := by
    intro s hs
    by_contra hns
    have hker : (RingHom.ker εΛ.toRingHom).IsMaximal :=
      RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨algebraMap κ Λ c, by simp⟩)
    have heq : RingHom.ker εΛ.toRingHom = IsLocalRing.maximalIdeal Λ := IsLocalRing.eq_maximalIdeal hker
    have hin : g s ∈ RingHom.ker εΛ.toRingHom := by
      rw [heq]
      exact (IsLocalRing.mem_maximalIdeal _).2 hns
    have h2 : εΛ (g s) = ε' (π s) := by
      simpa using congrArg (fun f : B →ₐ[κ] κ => f s) hg
    apply hs
    rw [← h2]
    simpa [RingHom.mem_ker] using hin
  have hφu : ∀ y : m.primeCompl,
      IsUnit (((IsScalarTower.toAlgHom κ B' (Localization.AtPrime m')).comp π) y) := by
    rintro ⟨y, hy⟩
    have hy' : π y ∈ m'.primeCompl := by
      show π y ∉ m'
      rw [hmem']
      exact fun h => hy ((hmem y).2 h)
    exact IsLocalization.map_units (Localization.AtPrime m') (⟨π y, hy'⟩ : m'.primeCompl)
  let φ : Localization.AtPrime m →ₐ[κ] Localization.AtPrime m' := IsLocalization.liftAlgHom hφu
  have hφ : ∀ x, φ (algebraMap B _ x) = algebraMap B' (Localization.AtPrime m') (π x) := fun x => by
    simp [φ, IsLocalization.lift_eq]
  have hφs : Function.Surjective φ := by
    intro z
    obtain ⟨y, rfl⟩ := hsurj' z
    obtain ⟨x, rfl⟩ := hπ y
    exact ⟨_, hφ x⟩
  have hεu : ∀ y : m.primeCompl, IsUnit ((ε'.comp π) y) := by
    rintro ⟨y, hy⟩
    exact isUnit_iff_ne_zero.2 (fun h => hy ((hmem y).2 h))
  let ε : Localization.AtPrime m →ₐ[κ] κ := IsLocalization.liftAlgHom hεu
  have hmapm : m.map (algebraMap B (Localization.AtPrime m)) =
      IsLocalRing.maximalIdeal (Localization.AtPrime m) := Localization.AtPrime.map_eq_maximalIdeal
  have hmax : IsLocalRing.maximalIdeal (Localization.AtPrime m) =
      Ideal.span {algebraMap B (Localization.AtPrime m) t} := by
    apply le_antisymm
    · apply Submodule.le_of_le_smul_of_le_jacobson_bot (I := IsLocalRing.maximalIdeal (Localization.AtPrime m))
        (IsNoetherian.noetherian _)
      · exact (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).ge
      · rw [Ideal.smul_eq_mul, ← hmapm]
        calc m.map (algebraMap B (Localization.AtPrime m))
            ≤ (Ideal.span {t} ⊔ m ^ 2).map (algebraMap B (Localization.AtPrime m)) := Ideal.map_mono htm
          _ = _ := by rw [Ideal.map_sup, Ideal.map_span, Ideal.map_pow, Set.image_singleton, sq]
    · rw [Ideal.span_le, Set.singleton_subset_iff, ← hmapm]
      exact Ideal.mem_map_of_mem _ ht
  have hJ : RingHom.ker φ = Ideal.span {(algebraMap B (Localization.AtPrime m) t) ^ q} := by
    apply hC κ (Localization.AtPrime m) ε (algebraMap B _ t) hmax (RingHom.ker φ) q
    rw [← hq]
    exact LinearEquiv.finrank_eq (Ideal.quotientKerAlgEquivOfSurjective hφs).toLinearEquiv
  have hfac : ∀ x y : B, algebraMap B (Localization.AtPrime m) x = algebraMap B _ y → g x = g y := by
    intro x y h
    rw [← sub_eq_zero, ← map_sub] at h
    obtain ⟨⟨u, hu⟩, hu0⟩ := (IsLocalization.map_eq_zero_iff m.primeCompl (Localization.AtPrime m) (x - y)).1 h
    have hu' : ε' (π u) ≠ 0 := fun h0 => hu ((hmem u).2 h0)
    have h1 := congrArg g hu0
    rw [map_mul, map_sub, map_zero] at h1
    exact sub_eq_zero.1 ((hunit u hu').mul_right_eq_zero.1 h1)
  constructor
  · intro hker x hx
    have ht1 : (algebraMap B (Localization.AtPrime m) t) ^ q ∈ RingHom.ker φ := by
      rw [hJ]
      exact Ideal.mem_span_singleton_self _
    rw [RingHom.mem_ker, ← map_pow, hφ, map_pow] at ht1
    rw [← map_pow] at ht1
    obtain ⟨⟨u', hu'⟩, hu0⟩ := (IsLocalization.map_eq_zero_iff m'.primeCompl (Localization.AtPrime m') _).1 ht1
    obtain ⟨v, rfl⟩ := hπ u'
    have hv : ε' (π v) ≠ 0 := fun h0 => hu' ((hmem' _).2 h0)
    have h1 : g (v * t ^ q) = 0 := hker _ (by rw [map_mul]; exact hu0)
    rw [map_mul, map_pow] at h1
    have hgt : g t ^ q = 0 := (hunit v hv).mul_right_eq_zero.1 h1
    have hx' : algebraMap B (Localization.AtPrime m) x ∈ Ideal.span {algebraMap B (Localization.AtPrime m) t} := by
      rw [← hmax, ← hmapm]
      exact Ideal.mem_map_of_mem _ ((hmem x).2 hx)
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hx'
    obtain ⟨y, rfl⟩ := hsurj z
    have he := hfac x (y * t) (by rw [map_mul, hz])
    rw [he, map_mul, mul_pow, hgt, mul_zero]
  · intro hq' x hx
    have hgt : g t ^ q = 0 := hq' t ((hmem t).1 ht)
    have hx' : algebraMap B (Localization.AtPrime m) x ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, hφ, hx, map_zero]
    rw [hJ] at hx'
    obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hx'
    obtain ⟨y, rfl⟩ := hsurj z
    have he := hfac x (y * t ^ q) (by rw [map_mul, map_pow, hz])
    rw [he, map_mul, map_pow, hgt, mul_zero]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MLiftFF
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.liftFF_of :
    AlgOf → LiftPt → LiftFF := by
  intro hAlg hPt S K h hfin hflat V _ _ _ _ z g hg
  obtain ⟨B, _, _, k, hfinB, hfreeB, hp⟩ := hAlg S K h hfin hflat V z
  haveI : Module.Finite V B := hfinB
  haveI : Module.Free V B := hfreeB
  let u : Sp (IsLocalRing.ResidueField V) ⟶ Sp B := hp.lift g (resPt V) hg
  have huk : u ≫ k = g := hp.lift_fst _ _ _
  have hua : u ≫ spMap (algebraMap V B) = resPt V := hp.lift_snd _ _ _
  let χ : B →+* IsLocalRing.ResidueField V := (Spec.preimage u).hom
  have hχ : spMap χ = u := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage u).hom) = u
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have hχa : χ.comp (algebraMap V B) = IsLocalRing.residue V := by
    have h1 : Spec.map (CommRingCat.ofHom (χ.comp (algebraMap V B))) =
        Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) := by
      rw [CommRingCat.ofHom_comp, Spec.map_comp]
      exact (congrArg (· ≫ spMap (algebraMap V B)) hχ).trans hua
    have h2 := Spec.map_injective h1
    exact congrArg CommRingCat.Hom.hom h2
  obtain ⟨z₀, hz₀⟩ := hPt V B χ hχa
  refine ⟨spMap z₀.toRingHom ≫ k, ?_, ?_⟩
  · have hc : z₀.toRingHom.comp (algebraMap V B) = RingHom.id V := by
      ext x
      exact z₀.commutes x
    have h3 : spMap z₀.toRingHom ≫ spMap (algebraMap V B) = 𝟙 _ := by
      show Spec.map (CommRingCat.ofHom z₀.toRingHom) ≫ Spec.map (CommRingCat.ofHom (algebraMap V B)) = 𝟙 _
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hc]
      exact Spec.map_id _
    rw [Category.assoc, hp.w, ← Category.assoc, h3, Category.id_comp]
  · have h4 : resPt V ≫ spMap z₀.toRingHom = u := by
      rw [← hχ, ← hz₀]
      show Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)) ≫ Spec.map (CommRingCat.ofHom z₀.toRingHom) =
        Spec.map (CommRingCat.ofHom ((IsLocalRing.residue V).comp z₀.toRingHom))
      rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [← Category.assoc, h4, huk]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.MChainLoc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

private theorem finrank_quotient_eq_add_finrank_ker_factor (κ Λ : Type) [Field κ] [CommRing Λ] [Algebra κ Λ]
    [Module.Finite κ Λ] (I J : Ideal Λ) (h : I ≤ J) :
    Module.finrank κ (Λ ⧸ I) = Module.finrank κ (Λ ⧸ J) +
      Module.finrank κ (LinearMap.ker (Ideal.Quotient.factorₐ κ h).toLinearMap) := by
  haveI : Module.Finite κ (Λ ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ I).toLinearMap Ideal.Quotient.mk_surjective
  have hs : Function.Surjective (Ideal.Quotient.factorₐ κ h).toLinearMap :=
    Ideal.Quotient.factor_surjective h
  rw [← LinearMap.finrank_range_add_finrank_ker (Ideal.Quotient.factorₐ κ h).toLinearMap,
    LinearMap.range_eq_top.mpr hs, finrank_top]

set_option maxHeartbeats 400000 in
private theorem ideal_eq_span_pow_of_finrank (κ Λ : Type) [Field κ] [CommRing Λ] [IsLocalRing Λ] [Algebra κ Λ]
    [Module.Finite κ Λ] (ε : Λ →ₐ[κ] κ) (t : Λ)
    (ht : IsLocalRing.maximalIdeal Λ = Ideal.span {t}) (q : ℕ) :
    ∀ J : Ideal Λ, Module.finrank κ (Λ ⧸ J) = q → J = Ideal.span {t ^ q} := by
  classical
  intro J hJ
  haveI : IsArtinianRing Λ := IsArtinianRing.of_finite κ Λ
  haveI hfin : ∀ I : Ideal Λ, Module.Finite κ (Λ ⧸ I) := fun I ↦
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ κ I).toLinearMap Ideal.Quotient.mk_surjective
  have tm : t ∈ IsLocalRing.maximalIdeal Λ := by
    rw [ht]
    exact Ideal.subset_span rfl
  have mem_m : ∀ a, a ∈ IsLocalRing.maximalIdeal Λ ↔ ∃ b, b * t = a := fun a ↦ by
    rw [ht, Ideal.mem_span_singleton']
  have mem_pow : ∀ k x, x ∈ Ideal.span {t ^ k} ↔ ∃ a, a * t ^ k = x := fun k x ↦
    Ideal.mem_span_singleton'
  have unit_of : ∀ a : Λ, a ∉ IsLocalRing.maximalIdeal Λ → IsUnit a := fun a ha ↦ by
    by_contra hu
    exact ha ((IsLocalRing.mem_maximalIdeal a).2 hu)
  have hker : ∀ a : Λ, a - algebraMap κ Λ (ε a) ∈ IsLocalRing.maximalIdeal Λ := by
    intro a
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    have := hu.map ε
    simp at this
  have dec : ∀ a : Λ, ∃ b, a = algebraMap κ Λ (ε a) + b * t := by
    intro a
    obtain ⟨b, hb⟩ := (mem_m _).1 (hker a)
    exact ⟨b, by rw [hb]; ring⟩
  have drop : ∀ k, t ^ k ∈ Ideal.span {t ^ (k + 1)} → t ^ k = 0 := by
    intro k hk
    obtain ⟨a, ha⟩ := (mem_pow _ _).1 hk
    have hu : IsUnit (1 - a * t) := unit_of _ (fun h ↦ by
      have h1 : (1 : Λ) ∈ IsLocalRing.maximalIdeal Λ := by
        have := (IsLocalRing.maximalIdeal Λ).add_mem h
          ((IsLocalRing.maximalIdeal Λ).mul_mem_left a tm)
        simpa using this
      exact (IsLocalRing.mem_maximalIdeal _).1 h1 isUnit_one)
    have e : t ^ k * (1 - a * t) = 0 := by
      calc t ^ k * (1 - a * t) = t ^ k - a * t ^ (k + 1) := by ring
        _ = 0 := by rw [ha, sub_self]
    exact hu.mul_left_eq_zero.1 e
  have hNex : ∃ N, t ^ N = 0 := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := Λ)
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, ht] at hN
    refine ⟨N, ?_⟩
    have h := Ideal.pow_mem_pow (Ideal.subset_span rfl : t ∈ Ideal.span {t}) N
    rw [hN] at h
    simpa using h
  obtain ⟨n, hn, hlt⟩ : ∃ n, t ^ n = 0 ∧ ∀ k < n, t ^ k ≠ 0 :=
    ⟨Nat.find hNex, Nat.find_spec hNex, fun k hk ↦ Nat.find_min hNex hk⟩
  have dimB : ∀ k ≤ n, Module.finrank κ (Λ ⧸ Ideal.span {t ^ k}) = k := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [pow_zero, Ideal.span_singleton_one]
      haveI : Subsingleton (Λ ⧸ (⊤ : Ideal Λ)) := Ideal.Quotient.subsingleton_iff.mpr rfl
      exact Module.finrank_zero_of_subsingleton
    | succ k ih =>
      intro hk
      have hle : Ideal.span {t ^ (k + 1)} ≤ Ideal.span {t ^ k} :=
        Ideal.span_singleton_le_span_singleton.2 (pow_dvd_pow t (Nat.le_succ k))
      rw [finrank_quotient_eq_add_finrank_ker_factor κ Λ _ _ hle, ih (by omega)]
      congr 1
      set v := Ideal.Quotient.mk (Ideal.span {t ^ (k + 1)}) (t ^ k) with hv
      apply le_antisymm
      · have hsub : LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap ≤ κ ∙ v := by
          intro z hz
          obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
          rw [LinearMap.mem_ker] at hz
          have hx : x ∈ Ideal.span {t ^ k} := by
            rw [← Ideal.Quotient.eq_zero_iff_mem]
            simpa using hz
          obtain ⟨a, rfl⟩ := (mem_pow _ _).1 hx
          obtain ⟨b, hb⟩ := dec a
          rw [Submodule.mem_span_singleton]
          refine ⟨ε a, ?_⟩
          have e : a * t ^ k = algebraMap κ Λ (ε a) * t ^ k + b * t ^ (k + 1) := by
            linear_combination (t ^ k) * hb
          have hb0 : Ideal.Quotient.mk (Ideal.span {t ^ (k + 1)}) (b * t ^ (k + 1)) = 0 :=
            Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mul_mem_left _ b (Ideal.subset_span rfl))
          rw [e, map_add (f := _), hb0, add_zero, map_mul, Algebra.smul_def, Ideal.Quotient.mk_algebraMap]
        exact (Submodule.finrank_mono hsub).trans
          (by simpa using finrank_span_le_card ({v} : Set (Λ ⧸ Ideal.span {t ^ (k + 1)})))
      · have hvk : v ∈ LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap := by
          rw [LinearMap.mem_ker]
          simp only [v, AlgHom.toLinearMap_apply, Ideal.Quotient.factorₐ_apply_mk]
          exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
        have hv0 : v ≠ 0 := by
          intro h0
          exact hlt k (by omega) (drop k (Ideal.Quotient.eq_zero_iff_mem.1 h0))
        have hne : LinearMap.ker (Ideal.Quotient.factorₐ κ hle).toLinearMap ≠ ⊥ := fun hb ↦
          hv0 ((Submodule.mem_bot κ).1 (hb ▸ hvk))
        exact Nat.one_le_iff_ne_zero.2 (fun h ↦ hne (Submodule.finrank_eq_zero.1 h))
  have factA : ∃ k ≤ n, J = Ideal.span {t ^ k} := by
    by_cases h0 : J ≤ Ideal.span {t ^ n}
    · refine ⟨n, le_rfl, le_antisymm h0 ?_⟩
      rw [hn, Ideal.span_singleton_eq_bot.2 rfl]
      exact bot_le
    · have hex : ∃ k, ¬ J ≤ Ideal.span {t ^ k} := ⟨n, h0⟩
      obtain ⟨k0, hk0, hk0n, hmin⟩ : ∃ k0, ¬ J ≤ Ideal.span {t ^ k0} ∧ k0 ≤ n ∧
          ∀ j < k0, J ≤ Ideal.span {t ^ j} :=
        ⟨Nat.find hex, Nat.find_spec hex, Nat.find_min' hex h0,
          fun j hj ↦ not_not.1 (Nat.find_min hex hj)⟩
      have hk0pos : k0 ≠ 0 := by
        intro hz
        apply hk0
        rw [hz, pow_zero, Ideal.span_singleton_one]
        exact le_top
      obtain ⟨k, rfl⟩ : ∃ k, k0 = k + 1 := Nat.exists_eq_succ_of_ne_zero hk0pos
      have hJk : J ≤ Ideal.span {t ^ k} := hmin k (by omega)
      obtain ⟨x, hxJ, hx⟩ := SetLike.not_le_iff_exists.1 hk0
      obtain ⟨a, rfl⟩ := (mem_pow _ _).1 (hJk hxJ)
      have ha : a ∉ IsLocalRing.maximalIdeal Λ := by
        intro ham
        obtain ⟨b, rfl⟩ := (mem_m _).1 ham
        apply hx
        rw [mem_pow]
        exact ⟨b, by ring⟩
      obtain ⟨u, hu⟩ := unit_of a ha
      refine ⟨k, by omega, le_antisymm hJk ?_⟩
      rw [Ideal.span_le, Set.singleton_subset_iff]
      have e : t ^ k = ↑u⁻¹ * (a * t ^ k) := by
        rw [← hu, ← _root_.mul_assoc, Units.inv_mul, _root_.one_mul]
      rw [e]
      exact J.mul_mem_left _ hxJ
  obtain ⟨k, hkn, rfl⟩ := factA
  rw [dimB k hkn] at hJ
  rw [hJ]

theorem UpperTheory.Gal.crystallineComparison.Mod.chainLoc_of :
    ChainLoc := by
  intro κ Λ _ _ _ _ _ ε t ht J q hq
  exact ideal_eq_span_pow_of_finrank κ Λ ε t ht q J hq
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.GenericMulOfProdHolds
section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PTelescope
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

private theorem telescope_core {P : Type} (q n : ℕ) (F : P → P) (T A : ℕ → Multiset P)
    (h0 : T 0 = A 0)
    (hs : ∀ j, j < n → T (j + 1) = (A j).map F + q ^ (j + 1) • A (j + 1)) (m : ℕ) (hm : m ≤ n) :
    (Even m →
      ∑ j ∈ Finset.range (m + 1), (if Even j then q ^ (j.choose 2) else 0) • (T j).map F^[n - j] =
        ∑ j ∈ Finset.range (m + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T j).map F^[n - j] +
          q ^ ((m + 1).choose 2) • (A m).map F^[n - m]) ∧
    (¬ Even m →
      ∑ j ∈ Finset.range (m + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T j).map F^[n - j] =
        ∑ j ∈ Finset.range (m + 1), (if Even j then q ^ (j.choose 2) else 0) • (T j).map F^[n - j] +
          q ^ ((m + 1).choose 2) • (A m).map F^[n - m]) := by
  induction m with
  | zero =>
    refine ⟨fun _ => ?_, fun h => absurd ⟨0, rfl⟩ h⟩
    simp [h0]
  | succ m ih =>
    have hmn : m < n := hm
    obtain ⟨ihE, ihO⟩ := ih (by omega)
    have key : (T (m + 1)).map F^[n - (m + 1)] =
        (A m).map F^[n - m] + q ^ (m + 1) • (A (m + 1)).map F^[n - (m + 1)] := by
      rw [hs m hmn, Multiset.map_add (f := _), Multiset.map_nsmul, Multiset.map_map]
      congr 2
      have e : n - m = (n - (m + 1)) + 1 := by omega
      rw [e, Function.iterate_succ]
    have hc : (m + 1 + 1).choose 2 = (m + 1).choose 2 + (m + 1) := by
      rw [Nat.choose_succ_succ', Nat.choose_one_right, add_comm]
    simp only [Finset.sum_range_succ _ (m + 1), key, hc, pow_add, smul_add, mul_smul]
    rcases Nat.even_or_odd m with he | ho
    · have hne : ¬ Even (m + 1) := Nat.not_even_iff_odd.mpr he.add_one
      simp only [hne, if_false, zero_smul, add_zero, if_true]
      refine ⟨fun h => h.elim, fun _ => ?_⟩
      rw [ihE he]
      abel
    · have hne : ¬ Even m := Nat.not_even_iff_odd.mpr ho
      have hev : Even (m + 1) := ho.add_one
      simp only [hev, if_false, zero_smul, add_zero, if_true]
      refine ⟨fun _ => ?_, fun h => absurd trivial h⟩
      rw [ihO hne]
      abel

theorem UpperTheory.Gal.crystallineComparison.telescope_of :
    Telescope := by
  intro q n P F T A hAn h0 hs
  let T' : ℕ → Multiset P := fun j => if h : j < n + 1 then T ⟨j, h⟩ else 0
  have hT : ∀ j : Fin (n + 1), T j = T' j := fun j => by
    simp only [T', dif_pos j.isLt, Fin.eta]
  have h0' : T' 0 = A 0 := by simpa [T'] using h0
  have hs' : ∀ j, j < n → T' (j + 1) = (A j).map F + q ^ (j + 1) • A (j + 1) := by
    intro j hj
    have hh := hs ⟨j, hj⟩
    simpa [T', hj, Fin.succ] using hh
  have hE : ∑ j : Fin (n + 1), wEv q j • (T j).map F^[n - j] =
      ∑ j ∈ Finset.range (n + 1), (if Even j then q ^ (j.choose 2) else 0) • (T' j).map F^[n - j] := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (if Even j then q ^ (j.choose 2) else 0) • (T' j).map F^[n - j])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j]
    rfl
  have hO : ∑ j : Fin (n + 1), wOd q j • (T j).map F^[n - j] =
      ∑ j ∈ Finset.range (n + 1), (if Even j then 0 else q ^ (j.choose 2)) • (T' j).map F^[n - j] := by
    rw [← Fin.sum_univ_eq_sum_range (fun j => (if Even j then 0 else q ^ (j.choose 2)) • (T' j).map F^[n - j])]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hT j]
    rfl
  obtain ⟨h1, h2⟩ := telescope_core q n F T' A h0' hs' n le_rfl
  rw [hE, hO]
  by_cases he : Even n
  · rw [h1 he]
    simp [hAn]
  · rw [h2 he]
    simp [hAn]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.POrdCount
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ordCount_of :
    OrdDecomp → Telescope → OrdCount := by
  intro hD hT q n P F I _ v hR
  obtain ⟨A, hA, h0, hs⟩ := hD q n P F I v hR
  have key := hT q n P F (fun j => Multiset.map (v j) Finset.univ.val) A hA h0 hs
  simp only [Multiset.map_map] at key
  exact key
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.POrdDecomp
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison

private theorem val_map_sum {α P : Type} (s : Finset α) (f : α → P) :
    s.val.map f = ∑ x ∈ s, ({f x} : Multiset P) := by
  rw [Finset.sum_eq_multiset_sum]
  have h := Multiset.sum_map_singleton (s.val.map f)
  rw [Multiset.map_map] at h
  exact h.symm

open Classical in
private theorem partIn (hIn : CountIn) {k H P : Type} [Field k] [AddCommGroup H] [Module k H]
    [Module.Finite k H] (C : Submodule k H) (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] [Fintype (Submodule k (H ⧸ C))]
    (g : Submodule k (H ⧸ C) → Multiset P) (j : ℕ) :
    ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j + 1).filter
        (fun D => C ≤ D), g (D.map C.mkQ)
      = ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j), g E := by
  obtain ⟨hbij, hrk, -⟩ := hIn k H C hC
  refine Finset.sum_bij (fun D _ => D.map C.mkQ) ?_ ?_ ?_ ?_
  · intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
    have := hrk D hD.2
    omega
  · intro D₁ h₁ D₂ h₂ he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact Subtype.ext_iff.mp (@hbij.1 ⟨D₁, h₁.2⟩ ⟨D₂, h₂.2⟩ he)
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
    obtain ⟨⟨D, hD⟩, hDE⟩ := hbij.2 E
    refine ⟨D, ?_, hDE⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hD⟩
    have := hrk D hD
    simp only at hDE
    rw [hDE] at this
    omega
  · intro D hD
    rfl

open Classical in
private theorem partZero (hIn : CountIn) {k H : Type} [Field k] [AddCommGroup H] [Module k H]
    [Module.Finite k H] (C : Submodule k H) (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] :
    (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = 0).filter
        (fun D => C ≤ D) = ∅ := by
  ext D
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
  intro hD hCD
  have := Submodule.finrank_mono hCD
  omega

open Classical in
private theorem partOut (hIn : CountIn) (hOut : CountOut) {k H P : Type} [Field k] [Finite k]
    [AddCommGroup H] [Module k H] [Module.Finite k H] (C : Submodule k H)
    (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] [Fintype (Submodule k (H ⧸ C))]
    (g : Submodule k (H ⧸ C) → Multiset P) (j : ℕ) :
    ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j).filter
        (fun D => ¬ C ≤ D), g (D.map C.mkQ)
      = Nat.card k ^ j •
        ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j), g E := by
  obtain ⟨-, -, hrk⟩ := hIn k H C hC
  have hmaps : ∀ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j).filter
      (fun D => ¬ C ≤ D), D.map C.mkQ ∈
        Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j) := by
    intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
    rw [← hrk D hD.2]
    exact hD.1
  rw [Finset.smul_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl ?_
  intro E hE
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
  rw [Finset.sum_congr rfl (g := fun _ => g E) (fun D hD => by rw [(Finset.mem_filter.mp hD).2])]
  rw [Finset.sum_const]
  congr 1
  have hc : Nat.card k ^ j = Nat.card { D // ¬C ≤ D ∧ Submodule.map C.mkQ D = E } := by
    rw [hOut k H C hC E, hE]
  rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext D
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    refine ⟨⟨?_, h2⟩, h3⟩
    rw [hrk D h2, h3, hE]

end UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ordDecomp_of :
    CountIn → CountOut → OrdDecomp := by
  intro hIn hOut q n P F I _ v hv
  obtain ⟨k, H, _, _, _, _, _, C, A', e, hq, hn, hC, hve⟩ := hv
  classical
  haveI : Finite H := Module.finite_of_finite k
  haveI : Finite (Submodule k H) :=
    Finite.of_injective (fun S : Submodule k H => (S : Set H)) SetLike.coe_injective
  haveI : Finite (H ⧸ C) := Module.finite_of_finite k
  haveI : Finite (Submodule k (H ⧸ C)) :=
    Finite.of_injective (fun S : Submodule k (H ⧸ C) => (S : Set (H ⧸ C))) SetLike.coe_injective
  letI : Fintype (Submodule k H) := Fintype.ofFinite _
  letI : Fintype (Submodule k (H ⧸ C)) := Fintype.ofFinite _
  letI hG : ∀ m : ℕ, Fintype (Gr k H m) := fun m =>
    (inferInstance : Fintype {D : Submodule k H // Module.finrank k D = m})
  have key : ∀ j : Fin (n + 1), Multiset.map (v j) Finset.univ.val =
      ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ)).filter
        (fun D => C ≤ D), ({F (A' (D.map C.mkQ))} : Multiset P) +
      ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ)).filter
        (fun D => ¬ C ≤ D), ({A' (D.map C.mkQ)} : Multiset P) := by
    intro j
    rw [← Finset.sum_ite]
    rw [val_map_sum, ← Equiv.sum_comp (e j).symm]
    rw [Finset.sum_subtype (F := hG j)
      (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ))
      (p := fun D : Submodule k H => Module.finrank k D = (j : ℕ)) (by simp)]
    refine Finset.sum_congr rfl ?_
    intro D _
    have h := hve j ((e j).symm D)
    rw [Equiv.apply_symm_apply] at h
    by_cases hCD : C ≤ D.1
    · rw [h.1 hCD]
      simp [hCD]
    · rw [h.2 hCD]
      simp [hCD]
  refine ⟨fun j => ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
    ({A' E} : Multiset P), ?_, ?_, ?_⟩
  · apply Finset.sum_eq_zero
    intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
    exfalso
    have h1 := Submodule.finrank_le E
    have h2 := Submodule.finrank_quotient_add_finrank C
    omega
  · rw [key 0]
    simp only [Fin.val_zero]
    have h0 := partZero hIn C hC
    have h1 := partOut hIn hOut C hC (fun E => ({A' E} : Multiset P)) 0
    simp only [pow_zero, one_smul] at h1
    convert congrArg₂ (· + ·) (congrArg (fun s => ∑ D ∈ s, ({F (A' (D.map C.mkQ))} : Multiset P)) h0) h1
    all_goals first
      | rfl
      | simp
      | (ext x; simp)
  · intro j
    rw [key j.succ]
    simp only [Fin.val_succ]
    have h2 := partIn hIn C hC (fun E => ({F (A' E)} : Multiset P)) j
    have h3 := partOut hIn hOut C hC (fun E => ({A' E} : Multiset P)) (j + 1)
    rw [hq] at h3
    have h4 : ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
        ({F (A' E)} : Multiset P) = Multiset.map F
          (∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
            ({A' E} : Multiset P)) := by
      rw [← val_map_sum, ← val_map_sum, Multiset.map_map]
      rfl
    rw [← h4]
    convert congrArg₂ (· + ·) h2 h3
    all_goals first
      | rfl
      | simp
      | (ext x; simp)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PPtOrd
open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

theorem UpperTheory.Gal.crystallineComparison.ptOrd_of :
    OrdCount → PtIdOfOrd := by
  intro hC l q n Y π T hO V _ _ _ _ hl y hy φ hφ I _ z hz
  apply hC
  obtain ⟨k, H, x, hk, x2, x3, hf, C, A, e, h1, h2, h3, h4⟩ := hO V hl y hy φ hφ
  exact ⟨k, H, x, hk, x2, x3, hf, C, A, fun j => (Equiv.ofBijective (z j) (hz j)).trans (e j),
    h1, h2, h3, fun j i => h4 j (z j i)⟩
end

namespace UpperTheory.Gal.crystallineComparison

theorem ordCount_holds : OrdCount := ordCount_of (ordDecomp_of countIn_of countOut_of) telescope_of
theorem ptIdOfOrd_holds : PtIdOfOrd := ptOrd_of ordCount_holds

end UpperTheory.Gal.crystallineComparison
end

namespace UpperTheory.Gal.crystallineComparison.Mod

theorem wModEx_holds  : WModEx := wModEx_of
theorem valPtsX_holds  : ValPtsX := valPtsX_of
theorem wVal_holds  : WVal := wVal_of valPtsX_holds
theorem rankN_holds  : RankN := rankN_of wVal_holds
theorem secCard_holds  : SecCard := secCard_of
theorem objTri_holds  : ObjTri := objTri_of
theorem pairCalc_holds  : PairCalc := pairCalc_of
theorem pullIsog_holds  : PullIsog := pullIsog_of
theorem pullKer_holds  : PullKer := pullKer_of
theorem pulledEx_holds  : PulledEx := pulledEx_of objTri_holds pullIsog_holds pullKer_holds
theorem pulledRead_holds  : PulledRead := pulledRead_of pullKer_holds
theorem uElt_holds  : UElt := uElt_of
theorem divC_holds  : DivC := divC_of
theorem torsFree_holds  : TorsFree := torsFree_of divC_holds
theorem adjoint_holds  : Adjoint := adjoint_of pairCalc_holds torsFree_holds
theorem kerFromU_holds  : KerFromU := kerFromU_of uElt_holds pairCalc_holds adjoint_holds divC_holds
theorem isoOfKer_holds  : IsoOfKer := isoOfKer_of pairCalc_holds adjoint_holds divC_holds torsFree_holds
theorem secInj_holds  : SecInj := secInj_of pulledEx_holds pulledRead_holds pullKer_holds kerFromU_holds isoOfKer_holds
theorem constSub_holds  : ConstSub := constSub_of
theorem oMod_holds  : OMod := oMod_of
theorem secSurj_holds (h4 : QuotObj) : SecSurj := secSurj_of constSub_holds oMod_holds h4 objTri_holds pullKer_holds
theorem secEquiv_holds (h4 : QuotObj) : SecEquiv := secEquiv_of wVal_holds rankN_holds valPtsX_holds secCard_holds secInj_holds (secSurj_holds h4)
theorem grCard_holds  : GrCard := grCard_of
theorem powExt_holds  : PowExt := powExt_of
theorem genDown_holds  : GenDown := genDown_of
theorem resClosed_holds  : ResClosed := resClosed_of
theorem ordReadOf_holds  : OrdReadOf := ordReadOf_of countIn_of countOut_of
theorem algOf_holds  : AlgOf := algOf_of
theorem liftPt_holds  : LiftPt := liftPt_of
theorem liftFF_holds  : LiftFF := liftFF_of algOf_holds liftPt_holds
theorem lineC_holds  : LineC := lineC_of rankN_holds liftFF_holds
theorem kerU_holds  : KerU := kerU_of uElt_holds
theorem fFRead_holds  : FFRead := fFRead_of algOf_holds
theorem kerRead_holds  : KerRead := kerRead_of kerU_holds fFRead_holds liftFF_holds pullKer_holds wVal_holds
theorem redPts_holds  : RedPts := redPts_of
theorem killLocal_holds  : KillLocal := killLocal_of
theorem splitAlg_holds  : SplitAlg := splitAlg_of
theorem infE_holds  : InfE := infE_of splitAlg_holds
theorem sameE_holds  : SameE := sameE_of killLocal_holds infE_holds
theorem imgEq_holds  : ImgEq := imgEq_of objTri_holds
theorem caseE_holds  : CaseE := caseE_of sameE_holds kerU_holds kerFromU_holds isoOfKer_holds imgEq_holds pulledRead_holds
theorem ringHomog_holds  : RingHomog := ringHomog_of
theorem cotanOne_holds  : CotanOne := cotanOne_of
theorem chainLoc_holds  : ChainLoc := chainLoc_of
theorem chainRing_holds  : ChainRing := chainRing_of chainLoc_holds
theorem repHomog_holds  : RepHomog := repHomog_of
theorem frobRing_holds  : FrobRing := frobRing_of
theorem infW_holds  : InfW := infW_of ringHomog_holds cotanOne_holds chainRing_holds repHomog_holds frobRing_holds
theorem frobPass_holds  : FrobPass := frobPass_of infE_holds
theorem repOfFF_holds  : RepOfFF := repOfFF_of algOf_holds
theorem tanOne_holds  : TanOne := tanOne_of uElt_holds
theorem sameW_holds  : SameW := sameW_of killLocal_holds infW_holds frobPass_holds kerU_holds repOfFF_holds tanOne_holds
theorem frobHom_holds  : FrobHom := frobHom_of
theorem frobFin_holds  : FrobFin := frobFin_of
theorem picFrob_holds  : PicFrob := picFrob_of
theorem quasiInv_holds  : QuasiInv := quasiInv_of pairCalc_holds divC_holds
theorem frobIsog_holds  : FrobIsog := frobIsog_of frobHom_holds frobFin_holds picFrob_holds quasiInv_holds
theorem isogComp_holds  : IsogComp := isogComp_of pairCalc_holds
theorem caseW_holds  : CaseW := caseW_of sameW_holds frobIsog_holds isogComp_holds kerFromU_holds isoOfKer_holds imgEq_holds pulledRead_holds
theorem eW_holds (h4 : QuotObj) : EW := ew_of wModEx_holds rankN_holds lineC_holds (secEquiv_holds h4) kerRead_holds redPts_holds countIn_of pulledEx_holds caseE_holds caseW_holds
theorem corrBC_holds (h4 : QuotObj) : CorrBC := corrBC_of wModEx_holds rankN_holds (secEquiv_holds h4) grCard_holds
theorem ordEmb_holds (h3 : OrdGen) (h4 : QuotObj) : OrdEmb := ordEmb_of h3 genDown_holds resClosed_holds ordReadOf_holds (eW_holds h4)
theorem levPull_holds  : LevPull := levPull_of pullKer_holds
theorem etInj_holds  : EtInj := etInj_of objTri_holds levPull_holds
theorem ordKSE_holds (h3 : OrdGen) (h4 : QuotObj) : OrdKSE := ordKSE_of (corrBC_holds h4) (ordEmb_holds h3 h4) powExt_holds etInj_holds
theorem tjExF_holds (h1 : EsNorm) (h2 : EsGen) : TjExF := tjExF_of h1 h2 objTri_holds pullIsog_holds pullKer_holds
theorem uKerW_holds  : UKerW := uKerW_of kerU_holds pullKer_holds
theorem idealSplit_holds  : IdealSplit := idealSplit_of
theorem levPush_holds  : LevPush := levPush_of idealSplit_holds
theorem tjEEx_holds  : TjEEx := tjEEx_of objTri_holds pulledEx_holds pullKer_holds uKerW_holds levPull_holds levPush_holds
theorem congKS_holds (h1 : EsNorm) (h2 : EsGen) (h3 : OrdGen) (h4 : QuotObj) : CongKS :=
  congKS_of (tjExF_holds h1 h2) tjEEx_holds (ordKSE_holds h3 h4) ptIdOfOrd_holds

end UpperTheory.Gal.crystallineComparison.Mod
