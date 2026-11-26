module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterGridData
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepFamilyBounded
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualCoefficientSpaceUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStableRationalLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistIndexOfCoefficientFieldPlace
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverRealSubfieldSplit
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingsCharactersClassGroups
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StateB2OfRationalData

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsToricCharactersInTwistCoefficientRings
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFullTeich
noncomputable section

namespace GlobalTheory.LamTie.TrueList

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions Formalism.FrobeniusOrbits _root_.Formalism.L2.Host GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricRational
open GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.HeightCounting

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_twL_full_teich (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : RatioConj) (D : D7) (N : NData D.R D.host D.what₂)
    (hE : IsEmpty N.Loc) (T : TwR D.LL0 N) (Z : LamDat D) (hZ : Z.Ok)
    (art : Ideles D.host.E →* Gab D.host.E N.Om) (ha : IsGlobalArtin art)
    (κ : ∀ i, FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : ∀ i, Qbar (T.l i) ≃+* ℂ)
    (hκ : ∀ i (z : ℤ_[T.l i]), κ i (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
      algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i]))
    (hι : ∀ i (x : D.LL0), ι i (κ i (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)))
    (hδ : ∀ i, IsGal art (κ i) (ι i) (Z.C.delAt (T.l i)) 0 (T.delta i))
    (hS : ∀ i P, (below P).asIdeal ∣ cond0 D.host Z.w0 → P ∈ T.S0 i)
    (hT : Z.Teich) :
    ∃ (L : TwL T) (e : ∀ i, L.abelian₂ i ≃ Idx D.R),
      (∀ i lam, L.jL i lam = (e i lam).1.1 + 1 ∧ L.sideL i lam = (e i lam).2.2.2 ∧ L.s2 i lam = 2 * ((e i lam).2.2.1.1 : ℤ) ∧
        (∃ n r, IsGal art (κ i) (sideIso (ι i) (e i lam).2.2.2) (Z.lam0 (T.l i) (e i lam).1 (e i lam).2.1) n r ∧
          L.lamG i lam = (Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) ∧
        ∀ P, L.qs i lam P = ((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) ∧
      ∀ F : TwF T, IsLamTieFull (T.ntw hE F L) Z :=
  exists_twL_full hA hR D N hE T Z hZ art ha κ ι hκ hι hμ hχ hδ hS fun a w hw => ⟨w, rfl, hT a w hw⟩

end GlobalTheory.LamTie.TrueList
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SideBKeep
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LamInstall
open ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2.NT

variable {D : D7} (hE : IsEmpty D.nd.Loc) {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)}
  {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) (F : TwF T)

abbrev recE (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
    (th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex) : TwNew D :=
  ⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩

abbrev recL (L : TwL T) (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)))
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)
    (th' : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L) ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L))) :
    TwNew D :=
  ⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩

variable {hE Sp F} {L : TwL T} {ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))}
  {h0 : ∀ g : G0g D.nd, D.what₂.embLL ((ex.eLL0 g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g}
  {th : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T)) ex}
  {th' : NTh D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L) ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L))}


set_option maxHeartbeats 4000000 in
def twFC (X : TwFrameC (recE hE Sp F ex h0 th).toD7) : TwFrameC (recL hE Sp F L ex h0 th').toD7 := { X with }


set_option maxHeartbeats 4000000 in
def expC (X : NExpTied (recE hE Sp F ex h0 th).toD7) : NExpTied (recL hE Sp F L ex h0 th').toD7 :=
  { X with
    mtV := fun i j b k Q ψ h1 h2 h =>
      letI := X.acgWt i j b
      letI : Module (FractionRing ((recL hE Sp F L ex h0 th').toD7.ntw.O i)) (X.Wt i j b) := X.modWt i j b
      { X.mtV i j b k Q ψ h1 h2 h with } }


set_option maxHeartbeats 4000000 in
theorem sideB_keep {Rw : RowSide D} {low : Finset ℕ}
    {Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host} {S : RatDat D.ntw}
    {hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)} {eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0}
    {θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ}
    (B : SideB (recE hE Sp F ex h0 th).toD7 ((recE hE Sp F ex h0 th).cf cf) ((recE hE Sp F ex h0 th).row Rw) low Pq
      ((recE hE Sp F ex h0 th).rat S) hL eig θ)
    (chiI : ∀ s, L.abelian₂ s → NC.HC D.host.E)
    (hqs : ∀ i lam P, P ∉ T.S0 i →
      B.twF.iCq i (L.qs i lam P) = ((((Ideal.absNorm P.asIdeal : ℕ) : ℝ) ^ (-(L.s2 i lam : ℝ) / 2) : ℝ) : ℂ))
    (hlam : ∀ s lam, NC.Read D.nd.plOm.1 (L.lamG s lam) (algebraMap (T.O s) (FractionRing (T.O s)))
      (B.chiD.embO s (L.sideL s lam)) (NC.complexEmbeddingRestrictedToSubfield D) (id (α := NC.HC D.host.E) (B.chiD.mu0 (L.jL s lam)) * id (α := NC.HC D.host.E) (B.chiD.del s) * (chiI s lam)⁻¹) 0) :
    Nonempty (SideB (recL hE Sp F L ex h0 th').toD7 ((recL hE Sp F L ex h0 th').cf cf) ((recL hE Sp F L ex h0 th').row Rw) low Pq
      ((recL hE Sp F L ex h0 th').rat S) hL eig θ) :=
  ⟨{ B with
      twF := twFC B.twF
      tw := { B.tw with qs_pos := hqs }
      chiD := { B.chiD with chiI := chiI }
      chi := { B.chi with lamG := hlam }
      exp := expC B.exp }⟩

end GlobalTheory.LamInstall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterEqGaloisOfLadicUnitaryHecke
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterEqGaloisOfLadicUnitaryHecke
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar

noncomputable section

namespace GlobalTheory.HeckeRead

theorem read_of_isGal_side : ∀ {D : D7} {N : NData D.R D.host D.what₂} {T : TwR D.LL0 N} {art : Ideles D.host.E →* Gab D.host.E N.Om}, IsGlobalArtin art → ∀ {i : T.Tw} (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ), (∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) → ∀ (b : Bool) (embO : ↥D.LL0 →+* FractionRing (T.O i)), (∀ (x : ↥D.LL0) (y : T.O0 i), algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = (if b then T.emb0 i else T.emb0b i) x → embO x = algebraMap (T.O i) (FractionRing (T.O i)) (algebraMap (T.O0 i) (T.O i) y)) → ∀ (χ : HChar D.host.E), χ.IsUnitary → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), (∀ P ∉ S, χ.UnrAt P ∧ ∃ y : ↥D.LL0, embLL0 D y = ((χ.val P : ℂˣ) : ℂ)) → ∀ (H : Formalism.L2.NC.HC D.host.E), (∀ x, H.χ x = χ.1 x) → ∀ {n : (D.host.E →+* ℂ) → ℤ} {r : Neutral.B1.G D.host.E N.Om →* (T.O0 i)ˣ}, IsGal art κ (sideIso ι b) χ n r → Formalism.L2.NC.Read N.plOm.1 ((Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) (algebraMap (T.O i) (FractionRing (T.O i))) embO (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D) H 0 := by
  intro D N T art ha i κ ι hι b embO hO χ hχu S hS H hH n r hr
  classical
  have hfin := Formalism.L2.NC.finite_placesOver (E := D.host.E) (T.l i)
  refine ⟨hfin.toFinset ∪ S, fun P hP => ?_⟩
  simp only [Finset.mem_union, not_or, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hP
  obtain ⟨hu, y, hy⟩ := hS P hP.2
  have hAt := (GlobalTheory.HeckeUnifVal.at_val_and_unr_iff χ H (MonoidHom.ext hH) P).1 hu
  have hyC : D.what₂.embLL ((y : D.LL0) : D.what₂.LL) = ((χ.val P : ℂˣ) : ℂ) := hy
  have hyi : D.what₂.embLL ((y⁻¹ : D.LL0) : D.what₂.LL) = ((χ.val P : ℂˣ) : ℂ)⁻¹ := by
    rw [IntermediateField.coe_inv, map_inv₀, hyC]
  refine ⟨_, hAt, y⁻¹, ?_, fun σ hσ => ?_⟩
  · rw [zpow_zero, mul_one]
    exact hyi
  · have hl : ((T.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := hP.1
    have hf := hr.frob ha (Or.inl hl) hu (N.plOm.2 P) hσ
    have inj : Function.Injective (fun z : FractionRing (T.O0 i) => ι (κ z)) := ι.injective.comp κ.injective
    have hkey : algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i) =
        (if b then T.emb0 i else T.emb0b i) y⁻¹ := by
      cases b
      · have hf' : ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i))) =
            ((χ.val P : ℂˣ) : ℂ) := by
          have e1 : starRingEnd ℂ (ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i)))) =
              ((χ.val P : ℂˣ) : ℂ)⁻¹ := hf
          have hn : ‖((χ.val P : ℂˣ) : ℂ)‖ = 1 := hχu _
          rw [Complex.inv_eq_conj hn] at e1
          have := congrArg (starRingEnd ℂ) e1
          simpa only [Complex.conj_conj] using this
        have hst : ((y : D.LL0) : D.what₂.LL) = star ((y⁻¹ : D.LL0) : D.what₂.LL) := by
          apply D.what₂.embLL.injective
          rw [D.starLL_cx, hyi, hyC]
          have hn : ‖((χ.val P : ℂˣ) : ℂ)‖ = 1 := hχu _
          rw [Complex.inv_eq_conj hn, Complex.conj_conj]
        show _ = T.emb0b i y⁻¹
        rw [T.restX_coefficientEmbedding_conj i y⁻¹ y hst]
        apply inj
        show ι (κ _) = ι (κ _)
        rw [hf', hι, hyC]
      · have hf' : ι (κ (algebraMap (T.O0 i) (FractionRing (T.O0 i)) ((r σ : (T.O0 i)ˣ) : T.O0 i))) =
            ((χ.val P : ℂˣ) : ℂ)⁻¹ := hf
        show _ = T.emb0 i y⁻¹
        apply inj
        show ι (κ _) = ι (κ _)
        rw [hf', hι, hyi]
    rw [hO y⁻¹ _ hkey]
    rfl

end GlobalTheory.HeckeRead

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistCharacterEqGaloisOfLadicUnitaryHeckeStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistCharacter_eq_galois_of_ladic_unitaryHecke : ∀ {D : D7} {N : NData D.R D.host D.what₂} {T : TwR D.LL0 N} {art : Ideles D.host.E →* Gab D.host.E N.Om}, IsGlobalArtin art → ∀ {i : T.Tw} (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ), (∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) → ∀ (b : Bool) (embO : ↥D.LL0 →+* FractionRing (T.O i)), (∀ (x : ↥D.LL0) (y : T.O0 i), algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = (if b then T.emb0 i else T.emb0b i) x → embO x = algebraMap (T.O i) (FractionRing (T.O i)) (algebraMap (T.O0 i) (T.O i) y)) → ∀ (χ : HChar D.host.E), χ.IsUnitary → ∀ (S : Finset (HeightOneSpectrum (𝓞 D.host.E))), (∀ P ∉ S, χ.UnrAt P ∧ ∃ y : ↥D.LL0, embLL0 D y = ((χ.val P : ℂˣ) : ℂ)) → ∀ (H : Formalism.L2.NC.HC D.host.E), (∀ x, H.χ x = χ.1 x) → ∀ {n : (D.host.E →+* ℂ) → ℤ} {r : Neutral.B1.G D.host.E N.Om →* (T.O0 i)ˣ}, IsGal art κ (sideIso ι b) χ n r → Formalism.L2.NC.Read N.plOm.1 ((Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) (algebraMap (T.O i) (FractionRing (T.O i))) embO (Formalism.L2.NC.complexEmbeddingRestrictedToSubfield D) H 0 := by
  first | exact @GlobalTheory.HeckeRead.read_of_isGal_side | exact GlobalTheory.HeckeRead.read_of_isGal_side | (intros; apply GlobalTheory.HeckeRead.read_of_isGal_side <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsToricCharactersInTwistCoefficientRings
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.LamInstall
open ReciprocityTheory.Aut Formalism.AUTREP _root_.Formalism.L2.NT Neutral.B1 GlobalTheory.HeckeGal GlobalTheory.GalChar GlobalTheory.LamTie GlobalTheory.LamTie.TrueList

attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

theorem exists_reading {D : D7} {N : NData D.R D.host D.what₂} (T : TwR D.LL0 N) (i : T.Tw) :
    ∃ (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ),
      (∀ z : ℤ_[T.l i], κ (algebraMap (T.O0 i) _ (algebraMap ℤ_[T.l i] (T.O0 i) z)) =
        algebraMap ℚ_[T.l i] (Qbar (T.l i)) (z : ℚ_[T.l i])) ∧
      ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL) := by
  haveI : CharZero (FractionRing (T.O0 i)) := (T.emb0 i).charZero_iff (T.emb0 i).injective |>.1 inferInstance
  let f : ℤ_[T.l i] →+* FractionRing (T.O0 i) :=
    (algebraMap (T.O0 i) (FractionRing (T.O0 i))).comp (algebraMap ℤ_[T.l i] (T.O0 i))
  have hf : Function.Injective f := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    by_contra h0
    rw [PadicInt.unitCoeff_spec h0, map_mul, map_pow, map_natCast] at hz
    rcases mul_eq_zero.1 hz with h | h
    · exact ((PadicInt.unitCoeff h0).isUnit.map f).ne_zero h
    · exact (pow_ne_zero _ (Nat.cast_ne_zero.2 (T.lPrime i).out.ne_zero)) h
  have hf0 : Function.Injective (algebraMap ℤ_[T.l i] (T.O0 i)) :=
    Function.Injective.of_comp (f := algebraMap (T.O0 i) (FractionRing (T.O0 i))) hf
  haveI : Module.IsTorsionFree ℤ_[T.l i] (T.O0 i) := Module.isTorsionFree_iff_algebraMap_injective.2 hf0
  haveI : Module.IsTorsionFree ℤ_[T.l i] (Qbar (T.l i)) := Module.isTorsionFree_iff_algebraMap_injective.2
    (by rw [IsScalarTower.algebraMap_eq ℤ_[T.l i] ℚ_[T.l i] (Qbar (T.l i))]
        exact (algebraMap ℚ_[T.l i] (Qbar (T.l i))).injective.comp Subtype.val_injective)
  let g : T.O0 i →ₐ[ℤ_[T.l i]] Qbar (T.l i) := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have hg : Function.Injective g := by
    refine (RingHom.injective_iff_ker_eq_bot g.toRingHom).2 (Ideal.eq_bot_of_comap_eq_bot (R := ℤ_[T.l i]) ?_)
    rw [eq_bot_iff]
    intro z hz
    have h1 : algebraMap ℤ_[T.l i] (Qbar (T.l i)) z = 0 := (g.commutes z).symm.trans hz
    exact (map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective _ _)).1 h1
  haveI : Countable ↥D.LL0 := (Module.finBasis ℚ ↥D.LL0).equivFun.injective.countable
  let κ : FractionRing (T.O0 i) →+* Qbar (T.l i) := IsFractionRing.lift (g := g.toRingHom) hg
  obtain ⟨ι, hι⟩ := GlobalTheory.exists_padicAlgCl_ringEquiv_complex_comp_eq_of_countable (T.l i) ↥D.LL0
    (κ.comp (T.emb0 i)) (embLL0 D)
  exact ⟨κ, ι, fun z => (IsFractionRing.lift_algebraMap hg _).trans (g.commutes z), hι⟩

theorem delta_isGal (hC : GlobalTheory.Published.ChebotarevDegreeOne) {D : D7} {cf : CharFrame D} {b0 b1 : Big D} {Sx : Finset (PlE D.host)}
    {T : TwR D.LL0 D.nd} (Sp : RingSpec D cf b0 b1 Sx T) {art : Ideles D.host.E →* Gab D.host.E D.nd.Om}
    (ha : IsGlobalArtin art) (i : T.Tw) (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ)
    (hι : ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL)) :
    IsGal art κ ι (cf.delAt (T.l i)) 0 (T.delta i) := GlobalTheory.T.twist_character_is_ladic_of_finite_order_hecke hC Sp ha i κ ι hι

theorem read_of_isGal {D : D7} {N : NData D.R D.host D.what₂} {T : TwR D.LL0 N} {art : Ideles D.host.E →* Gab D.host.E N.Om}
    (ha : IsGlobalArtin art) {i : T.Tw} (κ : FractionRing (T.O0 i) →+* Qbar (T.l i)) (ι : Qbar (T.l i) ≃+* ℂ)
    (hι : ∀ x : D.LL0, ι (κ (T.emb0 i x)) = D.what₂.embLL (x : D.what₂.LL))
    (b : Bool) (embO : ↥D.LL0 →+* FractionRing (T.O i))
    (hO : ∀ (x : ↥D.LL0) (y : T.O0 i), algebraMap (T.O0 i) (FractionRing (T.O0 i)) y = (if b then T.emb0 i else T.emb0b i) x →
      embO x = algebraMap (T.O i) (FractionRing (T.O i)) (algebraMap (T.O0 i) (T.O i) y))
    (χ : HChar D.host.E) (hu : χ.IsUnitary) (S : Finset (HeightOneSpectrum (𝓞 D.host.E)))
    (hv : ∀ P ∉ S, χ.UnrAt P ∧ ∃ y : ↥D.LL0, embLL0 D y = ((χ.val P : ℂˣ) : ℂ))
    (H : NC.HC D.host.E) (hH : ∀ x, H.χ x = χ.1 x) {n : (D.host.E →+* ℂ) → ℤ} {r : Neutral.B1.G D.host.E N.Om →* (T.O0 i)ˣ}
    (hr : IsGal art κ (sideIso ι b) χ n r) :
    NC.Read N.plOm.1 ((Units.map (algebraMap (T.O0 i) (T.O i)).toMonoidHom).comp r) (algebraMap (T.O i) (FractionRing (T.O i)))
      embO (NC.complexEmbeddingRestrictedToSubfield D) H 0 := GlobalTheory.T.twistCharacter_eq_galois_of_ladic_unitaryHecke ha κ ι hι b embO hO χ hu S hv H hH hr


set_option maxHeartbeats 4000000 in
theorem exists_twL_installed : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.ToricRational.RatioConj → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (Z : GlobalTheory.LamTie.LamDat D), Z.C = cf → Z.Ok → (∀ a, GlobalTheory.LamTie.TeichTriv D.host (Z.chi a)) → ValLL0 D cf → (∀ a, (Z.chi a).ValuesIn 0 (embLL0 D)) → (∀ i P, (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → P ∈ T.S0 i) → ∃ L : TwL T, ∀ F : TwF T, GlobalTheory.LamTie.IsLamTieFull (T.ntw hE F L) Z ∧ ∀ (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))) (h0 : _) th, Nonempty (SideB (⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) → ∀ th', Nonempty (SideB (⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) := by
  intro hC hA hR D hE cf Rw low Pq S hL eig θ b0 b1 Sx T Sp Z hZC hZ hT hV hχv hS
  subst hZC
  obtain ⟨art, ha⟩ := hA D.host.E D.nd.Om
  choose κ ι hκ hι using fun i => exists_reading T i
  have hμ : ∀ i j, (Z.C.mu0 j).ValuesIn 0 ((ι i).toRingHom.comp (κ i)) := fun i j v hv' => by
    obtain ⟨y, hy⟩ := hV.mu0 j v hv'
    exact ⟨T.emb0 i y, by rw [← hy]; exact hι i y⟩
  have hχ : ∀ i a, (Z.chi a).ValuesIn 0 ((ι i).toRingHom.comp (κ i)) := fun i a v hv' => by
    obtain ⟨y, hy⟩ := hχv a v hv'
    exact ⟨T.emb0 i y, by rw [← hy]; exact hι i y⟩
  have hδ := fun i => delta_isGal hC Sp ha i (κ i) (ι i) (hι i)
  obtain ⟨L, e, hcl, hfull⟩ := exists_twL_full_teich hA hR D D.nd hE T Z hZ art ha κ ι hκ hι hμ hχ hδ hS hT
  refine ⟨L, fun F => ⟨hfull F, fun ex h0 th hB th' => ?_⟩⟩
  obtain ⟨B⟩ := hB
  refine sideB_keep B (fun s lam => FitTw.toHC (Z.chi (e s lam).2.1)) ?_ ?_
  · intro i lam P _
    obtain ⟨-, -, h2, -, h4⟩ := hcl i lam
    rw [h4 P, h2]
    let f : FractionRing (T.O i) →+* ℂ := B.twF.iCq i
    show f (((Ideal.absNorm P.asIdeal : ℕ) : FractionRing (T.O i)) ^ (-((e i lam).2.2.1.1 : ℤ))) = _
    rw [map_zpow₀, map_natCast]
    have e2 : (-(((2 * ((e i lam).2.2.1.1 : ℤ) : ℤ) : ℝ)) / 2) = ((-((e i lam).2.2.1.1 : ℤ) : ℤ) : ℝ) := by
      push_cast; ring
    rw [e2, Real.rpow_intCast, Complex.ofReal_zpow, Complex.ofReal_natCast]
  · intro s lam
    obtain ⟨h1, h2, -, ⟨n, r, hr, hG⟩, -⟩ := hcl s lam
    let C : GlobalTheory.Mem.Chr.HFrame D.host (fun j => eExp D j) :=
      ⟨Z.C.P, Z.C.W, Z.C.mu0, Z.C.eta, Z.C.chiPsi, Z.C.del, Z.C.del', Z.C.isMu0, Z.C.isEta, Z.C.isChi, Z.C.isDel, Z.C.isDel'⟩
    have hpD : ∀ v, v ∈ T.pD s ↔ OverP D.host (if T.l s = D.host.pde then D.host.pde' else D.host.pde) v := fun v => by
      rw [← Finset.mem_coe, T.pD_eq]; rfl
    have hmu : ∀ P, P ∉ T.S0 s → (Z.C.mu0 (e s lam).1).UnrAt P := fun P hP =>
      (Z.C.isMu0 _).unr P fun k hk => hP (T.placesOver_subset_exceptional s k hk)
    have hde : ∀ P, P ∉ T.S0 s → (Z.C.delAt (T.l s)).UnrAt P := fun P hP =>
      (inertialOrderFifteenChar_auxiliaryPrime_spec C (l := T.l s)).2.2.2.2.unr P fun hk => hP (T.primes_subset_exceptional s ((hpD P).2 hk))
    have hcu : ∀ P, P ∉ T.S0 s → (Z.chi (e s lam).2.1).UnrAt P := fun P hP =>
      chi_unr hZ _ fun h => hP (hS s P h)
    have hdel : (Z.C.delAt (T.l s)).ValuesIn 0 (embLL0 D) := by
      unfold CharFrame.delAt
      split_ifs
      exacts [hV.del', hV.del]
    rw [hG, h2]
    refine read_of_isGal ha (κ s) (ι s) (hι s) _ _ (fun x y h => B.chi.ringSpec_sidedEmbedding_fixedField s _ x y h)
      (Z.lam0 (T.l s) (e s lam).1 (e s lam).2.1) ?_ (T.S0 s) ?_ _ ?_ hr
    · intro x
      have e1 := (Z.C.isMu0 (e s lam).1).unitary x
      have e2 := Z.C.delAt_unitary (T.l s) x
      have e3 := (hZ.aux (e s lam).2.1).unitary x
      show ‖(((Z.C.mu0 (e s lam).1).1 x * (Z.C.delAt (T.l s)).1 x * ((Z.chi (e s lam).2.1).1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
      rw [Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val, norm_mul, norm_mul, norm_inv, e1, e2, e3]
      norm_num
    · intro P hP
      refine ⟨((hmu P hP).mul (hde P hP)).mul (hcu P hP).inv, ?_⟩
      obtain ⟨y1, hy1⟩ := hV.mu0 (e s lam).1 P (hmu P hP)
      obtain ⟨y2, hy2⟩ := hdel P (hde P hP)
      obtain ⟨y3, hy3⟩ := hχv (e s lam).2.1 P (hcu P hP)
      simp only [HChar.valTw, Complex.ofReal_zero, neg_zero, Complex.cpow_zero, mul_one] at hy1 hy2 hy3
      refine ⟨y1 * y2 * y3⁻¹, ?_⟩
      rw [map_mul, map_mul, map_inv₀, hy1, hy2, hy3, LamDat.lam0, HChar.val_mul, HChar.val_mul, HChar.val_inv,
        Units.val_mul, Units.val_mul, Units.val_inv_eq_inv_val]
    · intro x
      rw [h1]
      have e1 : (B.chiD.mu0 ((e s lam).1.1 + 1)).χ x = (Z.C.mu0 (e s lam).1).1 x := B.ringSpec_normalisedCharacter_eq _ x
      have e2 : (B.chiD.del s).χ x = (Z.C.delAt (T.l s)).1 x := B.del_eq s x
      show (B.chiD.mu0 ((e s lam).1.1 + 1)).χ x * (B.chiD.del s).χ x * ((Z.chi (e s lam).2.1).1 x)⁻¹ = _
      rw [e1, e2]
      rfl

end GlobalTheory.LamInstall
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsToricCharactersInTwistCoefficientRingsStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.TwInputs GlobalTheory.SeriesTie NumberField IsDedekindDomain Polynomial
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_toricCharacters_in_twistCoefficientRings : GlobalTheory.Published.ChebotarevDegreeOne → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.ToricRational.RatioConj → ∀ (D : D7) (hE : IsEmpty D.nd.Loc) (cf : CharFrame D) (Rw : RowSide D) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T) (Z : GlobalTheory.LamTie.LamDat D), Z.C = cf → Z.Ok → (∀ a, GlobalTheory.LamTie.TeichTriv D.host (Z.chi a)) → ValLL0 D cf → (∀ a, (Z.chi a).ValuesIn 0 (embLL0 D)) → (∀ i P, (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → P ∈ T.S0 i) → ∃ L : TwL T, ∀ F : TwF T, GlobalTheory.LamTie.IsLamTieFull (T.ntw hE F L) Z ∧ ∀ (ex : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F (TwL.empty T))) (h0 : _) th, Nonempty (SideB (⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F (TwL.empty T), ex, h0, th, Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) → ∀ th', Nonempty (SideB (⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).toD7 ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).cf cf) ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).row Rw) low Pq ((⟨T.ntw hE F L, ({ ex with } : NExp D.R D.host D.what₂ D.LL0 D.nd (T.ntw hE F L)), h0, th', Sp.br, Sp.br_ind⟩ : TwNew D).rat S) hL eig θ) := by
  first | exact @GlobalTheory.LamInstall.exists_twL_installed | exact GlobalTheory.LamInstall.exists_twL_installed | (intros; apply GlobalTheory.LamInstall.exists_twL_installed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorPrimesInLowSet
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorPrimesInLowSet
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem GlobalTheory.LamTie.cond0_primes_lowAll : ∀ (D : D7) (Z : GlobalTheory.LamTie.LamDat D), Z.Ok → Z.q0 = AbsolutelyIrreducibleSpan.q0 D → ∀ P : HeightOneSpectrum (𝓞 D.host.E), (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → ∃ p ∈ lowAll D, P ∈ placesOver D.host.E p := by
  intro D Z hZ hq P hP
  have hPr : Prime (GlobalTheory.ToricDenom.below P).asIdeal := (GlobalTheory.ToricDenom.below P).prime

  have key : ∀ n : ℕ, ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) →
      ((n : 𝓞 D.host.E) ∈ P.asIdeal) := by
    intro n hn
    have h1 : algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal := hn
    simpa using h1
  have key' : ∀ n : ℕ, ((n : 𝓞 D.host.E) ∈ P.asIdeal) →
      ((n : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below P).asIdeal) := by
    intro n hn
    show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) (n : GlobalTheory.CMVal.OF D.host.E) ∈ P.asIdeal
    simpa using hn
  unfold GlobalTheory.LamTie.cond0 at hP
  rcases hPr.dvd_or_dvd hP with h | h
  · have h2 := hPr.dvd_of_dvd_pow h
    rw [Ideal.dvd_span_singleton] at h2
    have h3 := key _ (by exact_mod_cast h2)
    push_cast at h3
    have hpr := P.isPrime
    rcases hpr.mem_or_mem h3 with h4 | h4
    · rcases hpr.mem_or_mem h4 with h5 | h5
      · rcases hpr.mem_or_mem h5 with h6 | h6
        · exact ⟨D.host.g 0, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
        · exact ⟨D.host.g 1, by simp [GlobalTheory.HeightCounting.lowAll], h6⟩
      · exact ⟨D.host.pde, by simp [GlobalTheory.HeightCounting.lowAll], h5⟩
    · exact ⟨D.host.pde', by simp [GlobalTheory.HeightCounting.lowAll], h4⟩
  · have hle : (GlobalTheory.ToricDenom.below Z.w0).asIdeal ≤ (GlobalTheory.ToricDenom.below P).asIdeal :=
      Ideal.le_of_dvd h
    have heq : (GlobalTheory.ToricDenom.below Z.w0).asIdeal = (GlobalTheory.ToricDenom.below P).asIdeal :=
      ((GlobalTheory.ToricDenom.below Z.w0).isMaximal).eq_of_le (GlobalTheory.ToricDenom.below P).isPrime.ne_top hle
    have hw : ((Z.q0 : ℕ) : 𝓞 D.host.E) ∈ Z.w0.asIdeal := hZ.places.referencePlaceOverPrime
    have hb : ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ (GlobalTheory.ToricDenom.below Z.w0).asIdeal := by
      show algebraMap (GlobalTheory.CMVal.OF D.host.E) (𝓞 D.host.E) ((Z.q0 : ℕ) : GlobalTheory.CMVal.OF D.host.E) ∈ Z.w0.asIdeal
      simpa using hw
    rw [heq] at hb
    refine ⟨Z.q0, ?_, key _ hb⟩
    rw [hq]
    simp [GlobalTheory.HeightCounting.lowAll, lowPr]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorPrimesInLowSetStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conductor_primes_in_low_set : ∀ (D : D7) (Z : GlobalTheory.LamTie.LamDat D), Z.Ok → Z.q0 = AbsolutelyIrreducibleSpan.q0 D → ∀ P : HeightOneSpectrum (𝓞 D.host.E), (GlobalTheory.ToricDenom.below P).asIdeal ∣ GlobalTheory.LamTie.cond0 D.host Z.w0 → ∃ p ∈ lowAll D, P ∈ placesOver D.host.E p := by
  first | exact @GlobalTheory.LamTie.cond0_primes_lowAll | exact GlobalTheory.LamTie.cond0_primes_lowAll | (intros; apply GlobalTheory.LamTie.cond0_primes_lowAll <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormLeOneOfMemClC
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Df NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Df

open _root_.Formalism.L2.TwC

theorem norm_le_one_of_mem_clC' (l : ℕ) [Fact l.Prime] (F : IntermediateField ℚ_[l] (PadicAlgCl l)) {z : ℂ_[l]}
    (hz : z ∈ clC l F) : ‖z‖ ≤ 1 := by
  have hm : z ∈ PadicComplexInt l := (Subring.mem_inf.1 hz).2
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff] at hm
  rw [PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff).2 hm

theorem exists_iC_of_clC (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsDomain O]
    (F : IntermediateField ℚ_[l] (PadicAlgCl l)) (e : O ≃+* clC l F)
    (hratio : ∀ x ∈ clC l F, ∀ y ∈ clC l F, ‖x‖ ≤ ‖y‖ → x / y ∈ clC l F) :
    ∃ iC : FractionRing O →+* ℂ_[l],
      ∀ x, ‖iC x‖ ≤ 1 ↔ x ∈ (algebraMap O (FractionRing O)).range := by
  let ψ : O →+* ℂ_[l] := (clC l F).subtype.comp e.toRingHom
  have hψ : Function.Injective ψ := fun a b h => e.injective (Subtype.ext h)
  let iC : FractionRing O →+* ℂ_[l] := IsFractionRing.lift hψ
  have hiC : ∀ a : O, iC (algebraMap O (FractionRing O) a) = ψ a := fun a => IsFractionRing.lift_algebraMap hψ a
  refine ⟨iC, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := O) x
    have hb0 : algebraMap O (FractionRing O) b ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    have hψb : ψ b ≠ 0 := by
      rw [← hiC]; exact (map_ne_zero iC).2 hb0
    rw [map_div₀, hiC, hiC, norm_div, div_le_one (norm_pos_iff.2 hψb)] at hx
    have hmem := hratio _ (e a).2 _ (e b).2 hx
    refine ⟨e.symm ⟨_, hmem⟩, ?_⟩
    apply iC.injective
    rw [hiC, map_div₀, hiC, hiC]
    show ((e (e.symm ⟨_, hmem⟩) : clC l F) : ℂ_[l]) = _
    rw [e.apply_symm_apply]
    rfl
  · rintro ⟨a, rfl⟩
    rw [hiC]
    exact norm_le_one_of_mem_clC' l F (e a).2

end GlobalTheory.Mem.Df

namespace GlobalTheory.Mem.Df

open _root_.Formalism.L2.TwC

end GlobalTheory.Mem.Df
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisCoordLattice
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal _root_.Formalism.L2.Host NumberField IsDedekindDomain Polynomial

theorem exists_basis_coord_lattice {O V : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
    [AddCommGroup V] [Module (FractionRing O) V] [Module O V] [IsScalarTower O (FractionRing O) V]
    (B : Submodule O V) (hfg : B.FG)
    (hsp : Submodule.span (FractionRing O) (B : Set V) = ⊤) :
    ∃ (n : ℕ) (e : Module.Basis (Fin n) (FractionRing O) V),
      ∀ f : V, f ∈ B ↔ ∀ t, e.repr f t ∈ (algebraMap O (FractionRing O)).range := by
  classical
  have hfin : Module.Finite O B := Module.Finite.iff_fg.2 hfg
  have htf : Module.IsTorsionFree O V := Module.IsTorsionFree.trans_faithfulSMul O (FractionRing O) V
  have hfree : Module.Free O B := inferInstance
  let bO := Module.finBasis O B
  let v : Fin (Module.finrank O B) → V := fun t => (bO t : V)
  have hliO : LinearIndependent O v := bO.linearIndependent.map' B.subtype (Submodule.ker_subtype B)
  have hliK : LinearIndependent (FractionRing O) v :=
    (LinearIndependent.iff_fractionRing O (FractionRing O)).1 hliO
  have hBspan : B = Submodule.span O (Set.range v) := by
    have h1 : Submodule.map B.subtype (Submodule.span O (Set.range bO)) = B := by
      rw [bO.span_eq, Submodule.map_top, Submodule.range_subtype]
    rw [Submodule.map_span, ← Set.range_comp] at h1
    exact h1.symm
  have hle : (⊤ : Submodule (FractionRing O) V) ≤ Submodule.span (FractionRing O) (Set.range v) := by
    rw [← hsp, Submodule.span_le]
    intro x hx
    have hx' : x ∈ Submodule.span O (Set.range v) := hBspan ▸ hx
    exact Submodule.span_subset_span O (FractionRing O) (Set.range v) hx'
  let e := Module.Basis.mk hliK hle
  have he : ∀ t, e t = v t := fun t => by simp [e]
  refine ⟨_, e, fun f => ⟨fun hf => ?_, fun hf => ?_⟩⟩
  · rw [hBspan] at hf
    induction hf using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨t, rfl⟩ := hx
      intro s
      rw [← he, e.repr_self]
      by_cases h : t = s
      · subst h; exact ⟨1, by simp⟩
      · exact ⟨0, by simp [h]⟩
    | zero => intro s; exact ⟨0, by simp⟩
    | add x y _ _ hx hy =>
      intro s
      rw [map_add (f := _), Finsupp.add_apply]
      exact add_mem (hx s) (hy s)
    | smul a x _ hx =>
      intro s
      rw [← algebraMap_smul (FractionRing O) a x, map_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_mem ⟨a, rfl⟩ (hx s)
  · choose c hc using hf
    rw [← e.sum_repr f]
    refine sum_mem fun t _ => ?_
    rw [← hc t, algebraMap_smul, he]
    exact B.smul_mem _ (hBspan ▸ Submodule.subset_span ⟨t, rfl⟩)

section SideCoord

variable {K C : Type} [Field K] [Field C] (iC : K →+* C) {V : Bool → Type}
  [∀ b, AddCommGroup (V b)] [∀ b, Module K (V b)] {n : Bool → ℕ}
  (e : ∀ b, Module.Basis (Fin (n b)) K (V b))

def sideEv (b : Bool) : V b →+ ((Σ b', Fin (n b')) → C) where
  toFun f y := if h : y.1 = b then iC ((e b).repr f (h ▸ y.2)) else 0
  map_zero' := by
    funext y
    by_cases h : y.1 = b <;> simp [h]
  map_add' f g := by
    funext y
    by_cases h : y.1 = b <;> simp [h]

@[simp] theorem sideEv_same (b : Bool) (f : V b) (t : Fin (n b)) :
    sideEv iC e b f ⟨b, t⟩ = iC ((e b).repr f t) := by
  simp [sideEv]

theorem sideEv_other {b b' : Bool} (h : b' ≠ b) (f : V b) (t : Fin (n b')) :
    sideEv iC e b f ⟨b', t⟩ = 0 := by
  simp [sideEv, h]

theorem sideEv_smul (b : Bool) (a : K) (f : V b) (y : Σ b', Fin (n b')) :
    sideEv iC e b (a • f) y = iC a * sideEv iC e b f y := by
  obtain ⟨b', t⟩ := y
  by_cases h : b' = b
  · subst h; simp
  · simp [sideEv_other iC e h]

theorem sideEv_inj (b : Bool) : Function.Injective (sideEv iC e b) := by
  intro f g hfg
  apply (e b).repr.injective
  ext t
  have := congrFun hfg ⟨b, t⟩
  exact iC.injective (by simpa using this)

def sideU (b : Bool) (T : Module.End K (V b)) (c y : Σ b', Fin (n b')) : C :=
  if h : c.1 = b then sideEv iC e b (T (e b (h ▸ c.2))) y else 0

theorem sideEv_end (b : Bool) (T : Module.End K (V b)) (f : V b) (y : Σ b', Fin (n b')) :
    sideEv iC e b (T f) y = ∑ c, sideU iC e b T c y * sideEv iC e b f c := by
  classical
  have h0 : T f = ∑ t, (e b).repr f t • T (e b t) := by
    conv_lhs => rw [← (e b).sum_repr f]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul]
  have h1 : sideEv iC e b (T f) y =
      ∑ t, iC ((e b).repr f t) * sideEv iC e b (T (e b t)) y := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h0, map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun t _ => sideEv_smul iC e b _ _ y
  rw [h1, Fintype.sum_sigma, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp [sideU, mul_comm]
  · intro b' _ hb
    refine Finset.sum_eq_zero fun t _ => ?_
    simp [sideEv_other iC e hb]
  · simp

end SideCoord

theorem exists_nth_of_fg_full : ∀ (D : D7) (tw : NTw D.R D.host D.what₂ D.LL0 D.nd)
    (ex : NExp D.R D.host D.what₂ D.LL0 D.nd tw),
    (∀ i : tw.Tw, ∃ iC : FractionRing (tw.O i) →+* ℂ_[tw.l i], ∀ x, ‖iC x‖ ≤ 1 ↔
      x ∈ (algebraMap (tw.O i) (FractionRing (tw.O i))).range) →
    (∀ i j b, (ex.Bsup i j b).FG ∧
      Submodule.span (FractionRing (tw.O i)) (ex.Bsup i j b : Set (ex.Fm i j b)) = ⊤) →
    Nonempty (NTh D.R D.host D.what₂ D.LL0 D.nd tw ex) := by
  classical
  intro D tw ex hi hB
  choose iC hiC using hi
  have hex := fun i j b =>
    exists_basis_coord_lattice (ex.Bsup i j b) (hB i j b).1 (hB i j b).2
  choose n e he using hex
  have hsup : ∀ i j b, {f : ex.Fm i j b | f ∈ (⊤ : AddSubgroup (ex.Fm i j b)) ∧
      ∀ y, ‖sideEv (iC i) (e i j) b f y‖ ≤ 1} = (ex.Bsup i j b : Set (ex.Fm i j b)) := by
    intro i j b
    ext f
    simp only [Set.mem_ofPred_eq, AddSubgroup.mem_top, true_and, SetLike.mem_coe]
    rw [he i j b f]
    constructor
    · intro h t
      have := h ⟨b, t⟩
      rw [sideEv_same] at this
      exact (hiC i _).1 this
    · intro h y
      obtain ⟨b', t⟩ := y
      by_cases hb : b' = b
      · subst hb
        rw [sideEv_same]
        exact (hiC i _).2 (h t)
      · rw [sideEv_other _ _ hb]
        simp
  exact ⟨{
    iC := iC
    iC_int := hiC
    aL := fun i => if ∃ k, tw.l i = D.host.g k then 1 else 0
    aL_g := fun i k h => if_pos ⟨k, h⟩
    aL_off := fun i h => if_neg (not_exists.2 h)
    Pt := fun i j => Σ b, Fin (n i j b)
    ev := fun i j b => sideEv (iC i) (e i j) b
    ev_smul := fun i j b a f y => sideEv_smul _ _ b a f y
    ev_inj := fun i j b => sideEv_inj _ _ b
    Lt := fun _ _ => PUnit
    acgLt := fun _ _ => inferInstance
    modLt := fun _ _ => inferInstance
    freeLt := fun _ _ => inferInstance
    finLt := fun _ _ => inferInstance
    Let := fun _ _ => PEmpty
    finLet := fun _ _ => inferInstance
    Harm := fun _ _ => Set.univ
    Ctr := fun _ _ => PEmpty
    ctrC := fun _ _ κ => κ.elim
    Harm_def := fun i j P => ⟨fun _ κ => κ.elim, fun _ => Set.mem_univ _⟩
    thV := fun _ _ _ _ _ => 0
    thV_add := fun _ _ _ _ _ _ => by simp
    thV_smul := fun _ _ _ _ _ _ => by simp
    thV_addP := fun _ _ _ _ _ _ => by simp
    thV_smulP := fun _ _ _ _ _ _ => by simp
    datPhi := fun _ _ _ _ => 0
    datP := fun _ _ _ _ => 0
    recDet := fun _ _ _ => 1
    Kq := fun _ _ _ => PUnit
    grpKq := fun _ _ _ => inferInstance
    actK := fun _ _ _ _ y => y
    actK_one := fun _ _ _ _ => rfl
    actK_mul := fun _ _ _ _ _ _ => rfl
    recDetq := fun _ _ _ _ => 1
    recDetq_mem := fun _ _ _ _ => one_mem _
    recDet_act := fun _ _ _ _ _ _ _ _ _ _ => rfl
    recDetq_act := fun _ _ _ _ _ _ _ _ _ _ _ _ => rfl
    hkIdx := fun i j _ _ => Σ b, Fin (n i j b)
    finHk := fun _ _ _ _ => inferInstance
    hkMove := fun _ _ _ _ c _ => c
    hkU := fun i j b k P c y => sideU (iC i) (e i j) b (ex.hkF i j b k P) c y
    hk_ev := fun i j b k P _ _ _ _ f y => sideEv_end _ _ b _ f y
    MaximalUnramifiedExtension := fun _ => ⊤
    FmUr := fun _ _ _ => ⊤
    FmUr_smul := fun _ _ _ _ _ _ _ => AddSubgroup.mem_top _
    FmUr_span := fun i j b => by
      rw [AddSubgroup.coe_top, Submodule.span_univ]
    Bsup_def := fun i j b => by
      rw [hsup i j b, Submodule.span_eq] }⟩

end GlobalTheory.HeightCounting

end
end

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.Up.PointwiseSettings
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem exists_Sx (D : D7) : ∃ Sx : Finset (PlE D.host), (∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑Sx) ∧
    OverSet D Sx (lowAll D) ∧ (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) := by
  have hne : ∀ p ∈ lowAll D, p ≠ 0 := by
    intro p hp
    simp only [lowAll, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl
    · exact lowPr_ne_zero D p hp
    · exact (D.host.g_prime 0).ne_zero
    · exact (D.host.g_prime 1).ne_zero
    · exact D.host.pde_prime.ne_zero
    · exact D.host.pde'_prime.ne_zero
  have hfin : (⋃ p ∈ (lowAll D : Set ℕ), placesOver D.host.E p).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => Formalism.L2.TwC.placesOver_finite' D.host.E p (hne p hp)
  refine ⟨hfin.toFinset, fun p hp Q hQ => ?_, fun Q hQ => ?_, fun Q Q' hQ hc => ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 hp) hQ
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact ⟨p, hp, hQp⟩
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact (Set.Finite.mem_toFinset hfin).2 (Set.mem_biUnion hp (placesOver_conj D p hQp hc))


end GlobalTheory.HeightCounting.Up.PointwiseSettings
