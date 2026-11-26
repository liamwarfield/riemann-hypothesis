module

public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FrobeniusLabelsShape
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.LocalizationModelOverPlace
public import Development.WeilBound.CoreStatements.HodgeTatePoints.PflagZ
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsIsometricHermLine
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RealTowerConvI2
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ImageCptReflOfGenPt
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginComparisonSubset
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DegreeLatticesPrimeCompare
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginHeightComparisonThree
public import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootOriginHeightComparisonTwo

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompRootModelPrimes
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishOfTrivialFlags
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagFramePointDimension
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagFramePointDimension
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = e → genNum F (pointIdeal F y) b (∑ i, X i ^ k) Q = 0 := by
  intro hS F _ Ω _ _ K _ _ ι _ y e hP hdim N w b hb k hk Q hQ
  obtain ⟨R, hR, hsum⟩ := psum_eq_sum_hsymm_neg N k hk
  rw [hsum, (genNum_linear F K ι (Fin N) (pointIdeal F y) b Q).2.2.1]
  refine Finset.sum_eq_zero fun a ha => ?_
  obtain ⟨ha1, hak⟩ := Finset.mem_Icc.mp ha
  rw [genNum_mul_expand]
  refine Finset.sum_eq_zero fun μ hμ => ?_
  have hlen : (classList b μ).length = k - a :=
    PositivityTheory.HtPt.Pflag.length_classList_of_hom b (hR a) hμ
  have hl : a + (classList b μ ++ Q).length = e := by
    rw [List.length_append, hlen]
    omega
  rw [PositivityTheory.HtPt.Pflag.genNum_neg F K ι (pointIdeal F y) e hP hdim b _ a
      (PositivityTheory.HtPt.Pflag.isHomogeneous_hsymm_real N a) _ hl,
    PositivityTheory.HtPt.Pflag.genNum_hsymm,
    hsymm_dualRoots_triv_numZero hS F Ω K ι y e hP hdim N w b hb a ha1 _ hl]
  simp
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagFramePointDimensionStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_frame_point_dimension : NumericalSegre.Statement → ∀ (F : Type) [Field F] (Ω : Type) [Field Ω] [Algebra F Ω] (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (y : (Σ k, ι k) → Ω) (e : ℕ), IsMultiProjPrime (pointIdeal F y) → ringKrullDim (MRing ι F ⧸ pointIdeal F y) = ((e + Fintype.card K : ℕ) : WithBot ℕ∞) → ∀ (N : ℕ) (w : Module.Basis (Fin N) Ω (Fin N → Ω)) (b : Fin N → K → ℤ), IsFlagFrame y (scaledTrivBundle F (segreVec y) N (one_ne_zero (α := Ω))) w b → ∀ k : ℕ, 1 ≤ k → ∀ Q : List (K → ℤ), Q.length + k = e → genNum F (pointIdeal F y) b (∑ i, X i ^ k) Q = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension | exact GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension | (intros; apply GlobalTheory.CompanionTheory.Relay.flag_frame_point_dimension <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishOfTrivialFlags
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.ZTop

theorem isFibreComp_variety {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {ϖ : O}
    (hϖ : Irreducible ϖ) {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι O)} {d : ℕ} (hP : IsModelOver P d) {W : Ideal (MRing ι O)} (hW : IsFibreComp P W) :
    IsMultiProjPrime (specialIdeal W) ∧
      ringKrullDim (MRing ι (IsLocalRing.ResidueField O) ⧸ specialIdeal W) =
        ((d + Fintype.card K : ℕ) : WithBot ℕ∞) := by
  obtain ⟨hmin, hrel⟩ := hW
  rw [hϖ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton] at hmin
  refine PairNumberJoinLeft.verticalComponentFibre O ϖ hϖ K ι P d hP (C ϖ) 0
    (isWeightedHomogeneous_C _ _) (fun h => hϖ.ne_zero ?_) W hmin hrel
    (hmin.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
  exact Ideal.mem_bot.mp (hP.noTorsion ▸ Ideal.mem_comap.mpr h)

theorem cast_classNum {K : Type} [DecidableEq K] {ι : K → Type} {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {σ : Type} (cls : σ → K → ℤ) (H : MvPolynomial σ ℤ) (Q : List (K → ℤ))
    (W : Ideal (MRing ι O)) :
    ((classNum cls H Q W : ℤ) : ℝ) =
      genNum (IsLocalRing.ResidueField O) (specialIdeal W) cls (MvPolynomial.map (Int.castRingHom ℝ) H) Q := by
  unfold classNum genNum
  rw [MvPolynomial.support_map_of_injective _ (RingHom.injective_int (Int.castRingHom ℝ))]
  push_cast
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [MvPolynomial.coeff_map]
  rfl

theorem powerSumsVanish_of_trivFlagAt :
    NumericalSegre.Statement → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O),
      Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (N : ℕ) (x : Fin N → K → ℤ),
      (∀ W, IsFibreComp P W → TrivFlagAt W x) → PowerSumsVanish P d x := by
  intro hS O _ _ _ ϖ hϖ K _ _ ι _ P d hP N x hx W hW k hk Q hQ
  obtain ⟨Ω, _, _, y, w, hy, hflag⟩ := hx W hW
  obtain ⟨hprime, hdim⟩ := isFibreComp_variety hϖ hP hW
  have h := GlobalTheory.T.flag_frame_point_dimension hS (IsLocalRing.ResidueField O) Ω K ι y d (hy ▸ hprime) (hy ▸ hdim) N w x hflag
    k hk Q hQ
  have hmap : MvPolynomial.map (Int.castRingHom ℝ) (psum (Fin N) ℤ k) = ∑ i, X i ^ k := by
    simp [psum]
  have h2 := cast_classNum x (psum (Fin N) ℤ k) Q W
  rw [hmap, ← hy, h] at h2
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.Num.ZTop
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.PowerSumsVanishOfTrivialFlagsStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_sums_vanish_of_trivial_flags : NumericalSegre.Statement → ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (ϖ : O), Irreducible ϖ → ∀ (K : Type) [Fintype K] [DecidableEq K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι O)) (d : ℕ), IsModelOver P d → ∀ (N : ℕ) (x : Fin N → K → ℤ), (∀ W, IsFibreComp P W → TrivFlagAt W x) → PowerSumsVanish P d x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt | exact GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.ZTop.powerSumsVanish_of_trivFlagAt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompRootModelPrimes
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem linked_two_levels : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → HodgeLatticeFlagBound → TrivFlagOnHodge → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S S₀ : Finset ℕ) [Fintype (CMType H)] [DecidableEq (CMType H)] (M : RootModel (CMType H) (D.p + D.q)) [DecidableEq M.K] (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (R : SecondRoots M), Fl.TwoLevels S₀ R.pairs → (∀ p ∈ S, p ∉ S₀ → HT.HTFree 𝔐 p ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ NumberField.discr E) → ∀ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p ∈ S, p ∉ S₀ → IsFrobLabels c p (φ p)) → R.pairs.IsVertOff M.P ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧ R.LocalAtPlaces D.p ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) φ := by
  intro hseg hM3 hTriv E _ _ _ H D l Xo c O₀ _ β Y S S₀ _ _ M instK 𝔐 Fl R hTL hloc φ hφ
  obtain rfl : instK = (fun a b => Classical.propDecidable (a = b) : DecidableEq M.K) := Subsingleton.elim _ _
  classical
  refine ⟨?_, ?_⟩
  · obtain ⟨_, _, _, _, _, _, _, _, hvert⟩ := hTL
    exact hvert
  · obtain ⟨hded, hfin, hinj, hcst, -⟩ := GlobalTheory.T.arith_variety_coord_ideal E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 (dimFl (CMType H) (D.p + D.q)) M.arith (integralClosure ℤ M.Ω)
    refine ⟨integralClosure ℤ M.Ω, inferInstance, hded, hfin, inferInstance, hinj, hcst, ?_⟩
    intro p hp m _ hpm O _ _ _ _ _ _ _
    have hp' : (p : ℕ) ∈ S ∧ (p : ℕ) ∉ S₀ := Finset.mem_sdiff.1 (Finset.mem_preimage.1 hp)
    obtain ⟨hHT, h2, hd⟩ := hloc p hp'.1 hp'.2
    obtain ⟨_, _, _, e₀, e, _, hrl, _, _⟩ := id hTL
    refine ⟨?_, ?_⟩
    · exact hM3 E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 _ M.arith Fl S₀ R.pairs hTL p hp'.1 hp'.2 hHT h2 hd (φ p) (hφ p hp'.1 hp'.2) (integralClosure ℤ M.Ω) m hpm O
    · intro τ
      obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
      have hmod := (GlobalTheory.T.localization_model_over_place M.K M.ι M.Ω M.y (integralClosure ℤ M.Ω) hinj hcst _ M.arith m O).2.1
      exact GlobalTheory.T.power_sums_vanish_of_trivial_flags hseg O ϖ hϖ M.K M.ι _ _ hmod _ _ fun W hW =>
        hTriv E H D l Xo c O₀ β Y S M.Ω M.K M.ι M.y 𝔐 _ M.arith Fl R.pairs.x' e hrl p hp'.1 hHT (integralClosure ℤ M.Ω) m hpm O τ W hW

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCompRootModelPrimesStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver divCycle)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mseg fnField)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_comp_root_model_primes : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement → HodgeLatticeFlagBound → TrivFlagOnHodge → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S S₀ : Finset ℕ) [Fintype (CMType H)] [DecidableEq (CMType H)] (M : RootModel (CMType H) (D.p + D.q)) [DecidableEq M.K] (𝔐 : HodgeCpt Y S M.y) (Fl : 𝔐.Flag) (R : SecondRoots M), Fl.TwoLevels S₀ R.pairs → (∀ p ∈ S, p ∉ S₀ → HT.HTFree 𝔐 p ∧ p ≠ 2 ∧ ¬ (p : ℤ) ∣ NumberField.discr E) → ∀ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), (∀ p ∈ S, p ∉ S₀ → IsFrobLabels c p (φ p)) → R.pairs.IsVertOff M.P ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧ R.LocalAtPlaces D.p ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels | exact GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.linked_two_levels <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagHeightBoundArithVar
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagHeightBoundArithVar
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {V : Type} [AddCommGroup V]
  [Module Ω V]

theorem patch_eq_of_subset {S₀ S : Finset ℕ} (h : S₀ ⊆ S) (L₀ : Lat ξ V) (Lp : ℕ → Lat ξ V) {q : Cpt ξ}
    (hq : ∀ p ∈ S, p ∉ S₀ → ¬ InFibre ξ p q) : Lat.patch S₀ L₀ Lp q = Lat.patch S L₀ Lp q := by
  have hmem : ∀ p, (p ∈ S₀ ∧ InFibre ξ p q) ↔ (p ∈ S ∧ InFibre ξ p q) := fun p =>
    ⟨fun ⟨a, b⟩ => ⟨h a, b⟩, fun ⟨a, b⟩ => ⟨by_contra fun c => hq p a c b, b⟩⟩
  have hex : (∃ p ∈ S₀, InFibre ξ p q) ↔ ∃ p ∈ S, InFibre ξ p q := exists_congr hmem
  simp only [Lat.patch]
  by_cases hc : ∃ p ∈ S, InFibre ξ p q
  · rw [if_pos hc, if_pos (hex.2 hc)]
    refine le_antisymm (le_iInf₂ fun p hp => le_iInf fun hf => ?_) (le_iInf₂ fun p hp => le_iInf fun hf => ?_)
    · exact iInf₂_le_of_le p ((hmem p).2 ⟨hp, hf⟩).1 (iInf_le _ hf)
    · exact iInf₂_le_of_le p (h hp) (iInf_le _ hf)
  · rw [if_neg hc, if_neg (fun c => hc (hex.1 c))]

theorem gr_congr_at {L L' : Lat ξ V} {r : ℕ} (b : Fin r → V) (i : Fin r) {q : Cpt ξ} (hq : L q = L' q) :
    L.gr b i q = L'.gr b i q := by
  simp only [Lat.gr, hq]

theorem tens_congr_at {I : Type} [Fintype I] {Λ Λ' : I → Lat ξ Ω} (a : I → ℤ) {q : Cpt ξ}
    (hq : ∀ i, Λ i q = Λ' i q) : Lat.tens Λ a q = Lat.tens Λ' a q := by
  simp only [Lat.tens, Lat.IsGenAt, hq]

end General

theorem rootLat_shrink_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), Geo.IsArithVar (mCoordIdeal y) (d + 1) → ∀ (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (q : Cpt 𝔐.ξ), (∀ p ∈ S, p ∉ S₀ → ¬ InFibre 𝔐.ξ p q) → ∀ r, (Fl.shrink S₀ h hvb hsub).rootLat r q = Fl.rootLat r q := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d _ Fl S₀ h hvb hsub q hq r
  refine tens_congr_at (Λ := fun _ : Unit => (𝔐.VAt S₀ (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1)
    (HodgeCpt.rootIdx D r).2) (Λ' := fun _ : Unit => (𝔐.V (HodgeCpt.rootIdx D r).1).gr (Fl.b (HodgeCpt.rootIdx D r).1)
    (HodgeCpt.rootIdx D r).2) _ fun _ => gr_congr_at _ _ ?_
  exact patch_eq_of_subset h _ _ hq

end GlobalTheory.CompanionTheory.Ar.Num

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagHeightBoundArithVarStatement
open AlgebraicGeometry CategoryTheory NumberField MvPolynomial ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.NumbersDVR (pointIdeal segreVec IsFlagFrame IsFlagPair SameGenericFibre IsModelOver)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_bound_arith_var : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), Geo.IsArithVar (mCoordIdeal y) (d + 1) → ∀ (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (q : Cpt 𝔐.ξ), (∀ p ∈ S, p ∉ S₀ → ¬ InFibre 𝔐.ξ p q) → ∀ r, (Fl.shrink S₀ h hvb hsub).rootLat r q = Fl.rootLat r q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.rootLat_shrink_eq | exact GlobalTheory.CompanionTheory.Ar.Num.rootLat_shrink_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.rootLat_shrink_eq <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightBoundOfArithVar
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightBoundOfArithVar
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem rootLines_vert_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), Geo.IsArithVar (mCoordIdeal y) (d + 1) → ∀ (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (x x' : CMType H × Fin (D.p + D.q) → K → ℤ) (e₀ e : CMType H × Fin (D.p + D.q) → Ω), (Fl.shrink S₀ h hvb hsub).RootLines x e₀ → Fl.RootLines x' e → ∃ f g : CMType H × Fin (D.p + D.q) → MvPolynomial (Σ k, J k) ℤ, (∀ r, aeval y (f r) = e r / e₀ r * aeval y (g r)) ∧ (⟨x, x', f, g⟩ : LocPair J ℤ (CMType H × Fin (D.p + D.q))).IsVertOff (mCoordIdeal y) ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) := by
  intro E _ _ _ H D l Xo c O₀ _ β Y S Ω _ K _ _ J _ y 𝔐 d ha Fl S₀ h hvb hsub x x' e₀ e h₀ h₁
  have key : ∀ r, ∃ f g : MvPolynomial (Σ k, J k) ℤ,
      (⟨fun _ => x r, fun _ => x' r, fun _ => f, fun _ => g⟩ : LocPair J ℤ Unit).IsVertOff (mCoordIdeal y)
        ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧
      aeval y f = e r / e₀ r * aeval y g := by
    intro r
    refine GlobalTheory.T.degree_lattices_prime_compare 𝔐.X Ω 𝔐.ξ K J y 𝔐.tie d ha ((Fl.shrink S₀ h hvb hsub).rootLat r) (Fl.rootLat r)
      (x r) (x' r) (e₀ r) (e r) (h₀ r) (h₁ r) _ ?_
    intro q hq
    exact GlobalTheory.T.flag_height_bound_arith_var E H D l Xo c O₀ β Y S Ω K J y 𝔐 d ha Fl S₀ h hvb hsub q
      (fun p hp hp' hf => hq ⟨p, 𝔐.S_prime p hp⟩ (Finset.mem_preimage.2 (Finset.mem_sdiff.2 ⟨hp, hp'⟩)) hf) r
  choose f g hv hr using key
  exact ⟨f, g, hr, fun r => hv r ()⟩

end GlobalTheory.CompanionTheory.Ar.Num
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.FlagHeightBoundOfArithVarStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.flag_height_bound_of_arith_var : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O₀ : Type) [CommRing O₀] (β : O₀ →+* c.F) (Y : Model Xo c β) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] [DecidableEq K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (d : ℕ), Geo.IsArithVar (mCoordIdeal y) (d + 1) → ∀ (Fl : 𝔐.Flag) (S₀ : Finset ℕ) (h : S₀ ⊆ S) (hvb : ∀ s, (𝔐.VAt S₀ s).IsVB (labelRk D s) (𝔐.Vgen s)) (hsub : ∀ s, (𝔐.VAt S₀ s).IsFlagVBOn Set.univ (Fl.b s)) (x x' : CMType H × Fin (D.p + D.q) → K → ℤ) (e₀ e : CMType H × Fin (D.p + D.q) → Ω), (Fl.shrink S₀ h hvb hsub).RootLines x e₀ → Fl.RootLines x' e → ∃ f g : CMType H × Fin (D.p + D.q) → MvPolynomial (Σ k, J k) ℤ, (∀ r, aeval y (f r) = e r / e₀ r * aeval y (g r)) ∧ (⟨x, x', f, g⟩ : LocPair J ℤ (CMType H × Fin (D.p + D.q))).IsVertOff (mCoordIdeal y) ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.rootLines_vert_ratio | exact GlobalTheory.CompanionTheory.Ar.Num.rootLines_vert_ratio | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.rootLines_vert_ratio <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoEqRelinedIsometricVert
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoEqRelinedIsometricVert
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num.Swap

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem arList_swap_one {P : Ideal (MvPolynomial (Σ k, ι k) ℤ)}
    {I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) (T : LocPair ι ℤ Unit)
    (hT : T.IsVertOff P ∅) {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A')
    (hiso : T.IsIsometric P (fun _ => A) (fun _ => A'))
    (pre post : List (HermLine ι)) (hpre : ∀ b ∈ pre, IsSmoothHerm b)
    (hpost : ∀ b ∈ post, IsSmoothHerm b) (hP : Geo.IsArithVar P ((pre ++ post).length + 1)) :
    arList I P (pre ++ A :: post) = arList I P (pre ++ A' :: post) := by
  have hL : ∀ j, IsSmoothHerm ((pre ++ post).get j) := fun j => by
    rcases List.mem_append.1 (List.get_mem _ j) with h | h
    · exact hpre _ h
    · exact hpost _ h
  have hsnoc : ∀ B : HermLine ι, IsSmoothHerm B → arList I P (pre ++ B :: post) =
      I P ((pre ++ post).length + 1) (Fin.snoc (pre ++ post).get B) := by
    intro B hB
    refine arList_eq_of_perm hP hI _ _ ?_ ?_
    · intro j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simpa using hB
      · simpa using hL i
    · rw [List.ofFn_succ']
      simp only [Fin.snoc_castSucc, Fin.snoc_last, List.ofFn_get, List.concat_eq_append]
      exact List.perm_middle.trans (List.perm_append_singleton _ _).symm
  rw [hsnoc A hA, hsnoc A' hA']
  have h := GlobalTheory.T.isometric_vertical_intersection_eq K ι P _ hP I hI ∅ T hT A A' hA hA' hiso (pre ++ post).get hL
  simpa [sub_eq_zero] using h

theorem arList_swap_map {J : Type} {P : Ideal (MvPolynomial (Σ k, ι k) ℤ)}
    {I : Ideal (MvPolynomial (Σ k, ι k) ℤ) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) (T : LocPair ι ℤ Unit)
    (hT : T.IsVertOff P ∅) {A A' : HermLine ι} (hA : IsSmoothHerm A) (hA' : IsSmoothHerm A')
    (hiso : T.IsIsometric P (fun _ => A) (fun _ => A')) (F G : J → HermLine ι)
    (hF : ∀ j, IsSmoothHerm (F j)) (hG : ∀ j, IsSmoothHerm (G j))
    (hFG : ∀ j, F j = G j ∨ (F j = A ∧ G j = A')) (l : List J) :
    ∀ (pre : List (HermLine ι)), (∀ b ∈ pre, IsSmoothHerm b) →
      Geo.IsArithVar P (pre.length + l.length) →
      arList I P (pre ++ l.map F) = arList I P (pre ++ l.map G) := by
  induction l with
  | nil => intro pre _ _; rfl
  | cons j l ih =>
    intro pre hpre hP
    have e1 : pre ++ (j :: l).map F = (pre ++ [F j]) ++ l.map F := by simp
    have e2 : (pre ++ [F j]) ++ l.map G = pre ++ F j :: l.map G := by simp
    have hpre' : ∀ b ∈ pre ++ [F j], IsSmoothHerm b := fun b hb => by
      rcases List.mem_append.1 hb with h | h
      · exact hpre b h
      · rw [List.mem_singleton.1 h]; exact hF j
    have hlen : (pre ++ [F j]).length + l.length = pre.length + (j :: l).length := by
      simp; omega
    rw [e1, ih _ hpre' (hlen ▸ hP), e2, List.map_cons]
    rcases hFG j with h | ⟨h, h'⟩
    · rw [h]
    · rw [h, h']
      refine arList_swap_one hI T hT hA hA' hiso pre _ hpre ?_ ?_
      · intro b hb
        obtain ⟨i, -, rfl⟩ := List.mem_map.1 hb
        exact hG i
      · have : (pre ++ l.map G).length + 1 = pre.length + (j :: l).length := by
          simp; omega
        exact this ▸ hP

theorem ofFn_monoLines {J : Type} (ℓ : J → HermLine ι) (m : J →₀ ℕ) (d : ℕ)
    (hd : (Finsupp.toMultiset m).toList.length = d) :
    List.ofFn (monoLines ℓ m d) = (Finsupp.toMultiset m).toList.map ℓ := by
  subst hd
  apply List.ext_get (by simp)
  intro n h₁ h₂
  simp [monoLines]

end GlobalTheory.CompanionTheory.Ar.Num.Swap

namespace GlobalTheory.CompanionTheory.Ar.Num.Link

open GlobalTheory.CompanionTheory.Ar.Top.Link

theorem arMono_swapA : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) [DecidableEq M.K] (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (A' : HermLine M.ι) (hs : IsSmoothHerm A') (hc : IsConjInvariantH A') (T : LocPair M.ι ℤ Unit), T.IsVertOff M.P ∅ → T.IsIsometric M.P (fun _ => M.A) (fun _ => A') → ∀ (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ), M.arMono II t m = (Link.reline M M.xdeg M.x M.x_deg M.x_smooth M.x_conj A' hs hc).arMono II t m := by
  intro Ψ _ N M _ II hII A' hs hc T hT hiso t m
  set M' := Link.reline M M.xdeg M.x M.x_deg M.x_smooth M.x_conj A' hs hc with hM'
  have hI : IsIntersectionFamily (II M.K M.ι) := hII.1 M.K M.ι
  have hP : Geo.IsArithVar M.P (dimFl Ψ N + 1) := M.arith
  have hF : ∀ j, IsSmoothHerm (M.line t j) := fun j => by
    cases j with
    | none => exact M.A_smooth
    | some r => exact M.x_smooth t r
  have hG : ∀ j, IsSmoothHerm (M'.line t j) := fun j => by
    cases j with
    | none => exact hs
    | some r => exact M.x_smooth t r
  have hFG : ∀ j, M.line t j = M'.line t j ∨ (M.line t j = M.A ∧ M'.line t j = A') := fun j => by
    cases j with
    | none => exact Or.inr ⟨rfl, rfl⟩
    | some r => exact Or.inl rfl
  show (if m.degree = dimFl Ψ N + 1 then
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines (M.line t) m (dimFl Ψ N + 1)) /
        ((M.δ : ℝ) * (M.kA : ℝ) ^ m none) else 0) =
    (if m.degree = dimFl Ψ N + 1 then
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines (M'.line t) m (dimFl Ψ N + 1)) /
        ((M.δ : ℝ) * (M.kA : ℝ) ^ m none) else 0)
  split_ifs with hd
  swap
  · rfl
  have hlen : (Finsupp.toMultiset m).toList.length = dimFl Ψ N + 1 := by
    rw [Multiset.length_toList, Finsupp.card_toMultiset, ← hd]
    rfl
  have hmono : ∀ ℓ : Option (Ψ × Fin N) → HermLine M.ι, (∀ j, IsSmoothHerm (ℓ j)) →
      II M.K M.ι M.P (dimFl Ψ N + 1) (monoLines ℓ m (dimFl Ψ N + 1)) =
        arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map ℓ) := by
    intro ℓ hℓ
    symm
    refine arList_eq_of_perm hP hI _ _ ?_ ?_
    · intro j
      unfold monoLines
      split_ifs with h
      · exact hℓ _
      · exact absurd (by have := j.2; omega) h
    · rw [Swap.ofFn_monoLines ℓ m _ hlen]
  have key : arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map (M.line t)) =
      arList (II M.K M.ι) M.P ((Finsupp.toMultiset m).toList.map (M'.line t)) :=
    Swap.arList_swap_map hI T hT M.A_smooth hs hiso _ _ hF hG hFG _ [] (by simp) (by simpa [hlen] using hP)
  exact congrArg (· / ((M.δ : ℝ) * (M.kA : ℝ) ^ m none))
    ((hmono _ hF).trans (key.trans (hmono (M'.line t) hG).symm))

end GlobalTheory.CompanionTheory.Ar.Num.Link
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.ArMonoEqRelinedIsometricVertStatement
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arMono_eq_relined_isometric_vert : ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) [DecidableEq M.K] (II : IntersectionSystem), IsFullIntersectionSystem II → ∀ (A' : HermLine M.ι) (hs : IsSmoothHerm A') (hc : IsConjInvariantH A') (T : LocPair M.ι ℤ Unit), T.IsVertOff M.P ∅ → T.IsIsometric M.P (fun _ => M.A) (fun _ => A') → ∀ (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ), M.arMono II t m = (Link.reline M M.xdeg M.x M.x_deg M.x_smooth M.x_conj A' hs hc).arMono II t m := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.Link.arMono_swapA | exact GlobalTheory.CompanionTheory.Ar.Num.Link.arMono_swapA | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.Link.arMono_swapA <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelBlockPullback
section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelBlockPullback
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Num.PullModel

noncomputable section

open ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.ChartRestriction.G.AI.I1

section Lines

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]

theorem smooth_trivLine : IsSmoothHerm (trivLine ι) := contDiffOn_const

theorem pull_trivLine (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) :
    IsPullHerm κ v (trivLine ι) (trivLine ι') := by
  refine ⟨?_, fun _ => rfl⟩
  funext k
  simp [trivLine, pullDeg]

theorem pull_oneLine (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) :
    IsPullHerm κ v (ReciprocityTheory.ChartRestriction.G.Geo.oneLine : HermLine ι) (ReciprocityTheory.ChartRestriction.G.Geo.oneLine : HermLine ι') := by
  refine ⟨?_, fun _ => rfl⟩
  funext k
  simp [ReciprocityTheory.ChartRestriction.G.Geo.oneLine, HermLine.ofWeight, pullDeg]

theorem smooth_monoLines {J : Type} {ℓ : J → HermLine ι} (h : ∀ j, IsSmoothHerm (ℓ j)) (m : J →₀ ℕ) (d : ℕ)
    (k : Fin d) : IsSmoothHerm (monoLines ℓ m d k) := by
  unfold monoLines
  split_ifs
  · exact h _
  · exact smooth_trivLine

theorem pull_monoLines {J : Type} {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {ℓ : J → HermLine ι}
    {ℓ' : J → HermLine ι'} (h : ∀ j, IsPullHerm κ v (ℓ j) (ℓ' j)) (m : J →₀ ℕ) (d : ℕ) (k : Fin d) :
    IsPullHerm κ v (monoLines ℓ m d k) (monoLines ℓ' m d k) := by
  unfold monoLines
  split_ifs
  · exact h _
  · exact pull_trivLine κ v

theorem snoc_oneLine {I : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) → (n : ℕ) → (Fin n → HermLine ι) → ℝ}
    (hI : IsIntersectionFamily I) {P : Ideal (ReciprocityTheory.ChartRestriction.G.Geo.MRing ι)} {n : ℕ} (L : Fin n → HermLine ι)
    (hP : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar P (n + 1)) (hL : ∀ j, IsSmoothHerm (L j)) :
    I P (n + 1) (Fin.snoc (α := fun _ => HermLine ι) L ReciprocityTheory.ChartRestriction.G.Geo.oneLine) =
      -ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
  have h1 : (1 : ReciprocityTheory.ChartRestriction.G.Geo.MRing ι) ∉ P :=
    fun h => hP.2.1.1.ne_top ((Ideal.eq_top_iff_one P).mpr h)
  rw [hI.2.2 P n L ReciprocityTheory.ChartRestriction.G.Geo.oneLine 1 (fun _ => 0) hP hL ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_oneLine
    (fun k => by simp [ReciprocityTheory.ChartRestriction.G.Geo.oneLine, HermLine.ofWeight])
    ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomog_one h1]
  have hint : arInt P 1 ReciprocityTheory.ChartRestriction.G.Geo.oneLine L =
      ptsIntegral P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
    unfold arInt
    congr 1
    funext z
    exact ReciprocityTheory.ChartRestriction.G.Geo.logNorm_oneLine z
  unfold recR
  rw [ReciprocityTheory.ChartRestriction.G.Geo.divSupp_one, finsum_mem_empty, hint]
  ring

end Lines

variable {Ψ : Type} [Fintype Ψ] {N : ℕ}

theorem smooth_line (M : RootModel Ψ N) (t : ℝ) (r : Option (Ψ × Fin N)) : IsSmoothHerm (M.line t r) := by
  cases r with
  | none => exact M.A_smooth
  | some r => exact M.x_smooth t r

section Cover

variable {M M' : RootModel Ψ N} [CharZero M'.Ω] {II : IntersectionSystem}
  {κ : M.K → M'.K} {v : (Σ k, M.ι k) → (Σ k, M'.ι k)}

abbrev coverDeg (M M' : RootModel Ψ N) [CharZero M'.Ω] (v : (Σ k, M.ι k) → (Σ k, M'.ι k)) : ℕ :=
  IntermediateField.relfinrank (blockFnField (M'.y ∘ v)) (blockFnField M'.y)

theorem coverDeg_ne_zero (hδ : M'.δ = coverDeg M M' v * M.δ) : coverDeg M M' v ≠ 0 := by
  intro h
  have := M'.δ_pos
  rw [hδ, h, zero_mul] at this
  exact lt_irrefl _ this

theorem arMono_eq (hII : ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II) (hb : IsBlockMap κ v)
    (hP : imageZ v M'.P = M.P) (hl : ∀ t r, IsPullHerm κ v (M.line t r) (M'.line t r))
    (hk : M'.kA = M.kA) (hδ : M'.δ = coverDeg M M' v * M.δ) (t : ℝ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M'.arMono II t m = M.arMono II t m := by
  have hP' : imageZ v (mCoordIdeal M'.y) = M.P := hP
  have he : (coverDeg M M' v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (coverDeg_ne_zero hδ)
  have hδ0 : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.δ_pos.ne'
  have hk0 : (M.kA : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.kA_pos.ne'
  have hpf := hII.2.2.1 M.K M.ι M'.K M'.ι κ v M'.Ω M'.y (dimFl Ψ N + 1)
    (monoLines (M.line t) m (dimFl Ψ N + 1)) (monoLines (M'.line t) m (dimFl Ψ N + 1)) hb M'.arith
    (by rw [hP']; exact M.arith) (smooth_monoLines (smooth_line M t) m _) (pull_monoLines (hl t) m _)
  rw [hP'] at hpf
  unfold RootModel.arMono
  split_ifs
  · change ReciprocityTheory.ChartRestriction.G.Geo.IntersectionSystem at II
    have hpf' : II M'.K M'.ι M'.P (dimFl Ψ N + 1) (monoLines (M'.line t) m (dimFl Ψ N + 1)) = _ := hpf
    rw [hpf', hk, hδ]
    push_cast
    field_simp
  · rfl

theorem geoMono_eq (hII : ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II) (hb : IsBlockMap κ v)
    (hP : imageZ v M'.P = M.P) (hl : ∀ t r, IsPullHerm κ v (M.line t r) (M'.line t r))
    (hk : M'.kA = M.kA) (hδ : M'.δ = coverDeg M M' v * M.δ) (m : Option (Ψ × Fin N) →₀ ℕ) :
    M'.geoMono m = M.geoMono m := by
  have hP' : imageZ v (mCoordIdeal M'.y) = M.P := hP
  have he : (coverDeg M M' v : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (coverDeg_ne_zero hδ)
  have hδ0 : (M.δ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.δ_pos.ne'
  have hk0 : (M.kA : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr M.kA_pos.ne'
  unfold RootModel.geoMono
  split_ifs
  · set L := monoLines (M.line 1) m (dimFl Ψ N) with hLdef
    set L' := monoLines (M'.line 1) m (dimFl Ψ N) with hL'def
    have hLs : ∀ j, IsSmoothHerm (L j) := smooth_monoLines (smooth_line M 1) m _
    have hL's : ∀ j, IsSmoothHerm (L' j) := smooth_monoLines (smooth_line M' 1) m _
    have hLp : ∀ j, IsPullHerm κ v (L j) (L' j) := pull_monoLines (hl 1) m _
    have hpf := hII.2.2.1 M.K M.ι M'.K M'.ι κ v M'.Ω M'.y (dimFl Ψ N + 1)
      (Fin.snoc (α := fun _ => HermLine M.ι) L ReciprocityTheory.ChartRestriction.G.Geo.oneLine)
      (Fin.snoc (α := fun _ => HermLine M'.ι) L' ReciprocityTheory.ChartRestriction.G.Geo.oneLine) hb M'.arith
      (by rw [hP']; exact M.arith)
      (fun j => by
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa using ReciprocityTheory.ChartRestriction.G.Geo.isSmoothHerm_oneLine
        · simpa using hLs i)
      (fun j => by
        refine Fin.lastCases ?_ (fun i => ?_) j
        · simpa using pull_oneLine κ v
        · simpa using hLp i)
    rw [hP'] at hpf
    have e1 := snoc_oneLine (hII.1 M'.K M'.ι) L' M'.arith hL's
    have e2 : II M.K M.ι M.P (dimFl Ψ N + 1)
        (Fin.snoc (α := fun _ => HermLine M.ι) L ReciprocityTheory.ChartRestriction.G.Geo.oneLine) =
        -ptsIntegral M.P (fun j z => Real.log ((L j).h z)) (fun _ => 1) :=
      snoc_oneLine (hII.1 M.K M.ι) L M.arith hLs
    have hpf' := hpf
    rw [e1, e2] at hpf'
    have hpts : ptsIntegral (mCoordIdeal M'.y) (fun j z => Real.log ((L' j).h z)) (fun _ => 1) =
        (coverDeg M M' v : ℝ) * ptsIntegral M.P (fun j z => Real.log ((L j).h z)) (fun _ => 1) := by
      linarith
    change ptsIntegral (mCoordIdeal M'.y) (fun j z => Real.log ((L' j).h z)) (fun _ => 1) / _ = _
    rw [hpts, hk, hδ]
    push_cast
    field_simp
  · rfl

end Cover

end

theorem numbers_of_cover : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M M' : RootModel Ψ N) [CharZero M'.Ω] (II : IntersectionSystem), ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II → ∀ (κ : M.K → M'.K) (v : (Σ k, M.ι k) → (Σ k, M'.ι k)), ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v → ReciprocityTheory.ChartRestriction.G.AI.I4.imageZ v M'.P = M.P → (∀ t r, ReciprocityTheory.ChartRestriction.G.AI.I4.IsPullHerm κ v (M.line t r) (M'.line t r)) → M'.kA = M.kA → M'.δ = IntermediateField.relfinrank (ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (M'.y ∘ v)) (ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField M'.y) * M.δ → (∀ t, M'.arFun II t = M.arFun II t) ∧ M'.PP II = M.PP II ∧ (M.Converges II → M'.Converges II) ∧ M'.geoFun = M.geoFun := by
  intro Ψ _ _ N M M' _ II hII κ v hb hP hl hk hδ
  have hm : ∀ t, M'.arMono II t = M.arMono II t := fun t => funext fun m =>
    arMono_eq hII hb hP hl hk hδ t m
  have hg : M'.geoMono = M.geoMono := funext fun m => geoMono_eq hII hb hP hl hk hδ m
  refine ⟨fun t => ?_, ?_, fun hc m => ?_, ?_⟩
  · unfold RootModel.arFun
    rw [hm t]
  · unfold RootModel.PP
    congr 2
    funext m
    congr 1
    funext t
    exact congrFun (hm t) m
  · obtain ⟨L, hL⟩ := hc m
    exact ⟨L, by simpa only [hm] using hL⟩
  · unfold RootModel.geoFun
    rw [hg]

end GlobalTheory.CompanionTheory.Ar.Num.PullModel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelBlockPullbackStatement
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR GlobalTheory.CompanionTheory.Ar.Num GlobalTheory.CompanionTheory.Ar.Top GroundTheory.Heights₂.Heights.ModelLeaves
open ReciprocityTheory.ChartRestriction.G.Geo (HermLine IsSmoothHerm IsArithVar IsHorizontal mcPts mCoordIdeal IsIntersectionFamily IsIntersectionSystem IntersectionSystem ptsIntegral geoNum charOf recR arInt ChartBundle chartRing)
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_model_block_pullback : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ) (M M' : RootModel Ψ N) [CharZero M'.Ω] (II : IntersectionSystem), ReciprocityTheory.ChartRestriction.G.Geo.IsFullIntersectionSystem II → ∀ (κ : M.K → M'.K) (v : (Σ k, M.ι k) → (Σ k, M'.ι k)), ReciprocityTheory.ChartRestriction.G.AI.I1.IsBlockMap κ v → ReciprocityTheory.ChartRestriction.G.AI.I4.imageZ v M'.P = M.P → (∀ t r, ReciprocityTheory.ChartRestriction.G.AI.I4.IsPullHerm κ v (M.line t r) (M'.line t r)) → M'.kA = M.kA → M'.δ = IntermediateField.relfinrank (ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField (M'.y ∘ v)) (ReciprocityTheory.ChartRestriction.G.AI.I4.blockFnField M'.y) * M.δ → (∀ t, M'.arFun II t = M.arFun II t) ∧ M'.PP II = M.PP II ∧ (M.Converges II → M'.Converges II) ∧ M'.geoFun = M.geoFun := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Num.PullModel.numbers_of_cover | exact GlobalTheory.CompanionTheory.Ar.Num.PullModel.numbers_of_cover | (intros; apply GlobalTheory.CompanionTheory.Ar.Num.PullModel.numbers_of_cover <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalConditions
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
open MvPolynomial Filter Topology
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm blockFnField)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter (pullHerm)
open GlobalTheory.CompanionTheory.Ar.Num

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Top.Link

theorem mCoordIdeal_map {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {Ω₀ Ω : Type} [Field Ω₀] [Field Ω]
    (i : Ω₀ →+* Ω) (y₀ : (Σ k, J k) → Ω₀) : mCoordIdeal (fun p => i (y₀ p)) = mCoordIdeal y₀ := by
  have key : ∀ f : MRing J, mConeMap (fun p => i (y₀ p)) f = MvPolynomial.map i (mConeMap y₀ f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp only [map_add (f := _), hp, hq]
    | mul_X p n hp => simp only [map_mul, hp]; simp [mConeMap]
  ext f
  show mConeMap _ f = 0 ↔ mConeMap _ f = 0
  rw [key]
  exact map_eq_zero_iff _ (MvPolynomial.map_injective i i.injective)

theorem imageZ_of_restr {K₀ K : Type} [Fintype K₀] [Fintype K] {J₀ : K₀ → Type} {J : K → Type} [∀ k, Fintype (J₀ k)]
    [∀ k, Fintype (J k)] {Ω₀ Ω : Type} [Field Ω₀] [Field Ω] (i : Ω₀ →+* Ω) (y₀ : (Σ k, J₀ k) → Ω₀) (y : (Σ k, J k) → Ω)
    {κ : K₀ → K} {v : (Σ k, J₀ k) → Σ k, J k} (hv : IsBlockMap κ v) (hy : ∀ p, y (v p) = i (y₀ p)) :
    imageZ v (mCoordIdeal y) = mCoordIdeal y₀ := by
  rw [← GroundTheory.Heights₂.Heights.Inter.BlockRatioAlgebraic.mCoordIdeal_comp_v hv y, ← mCoordIdeal_map i y₀]
  congr 1
  funext p
  exact hy p

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} [DecidableEq (CMType H)]


open Classical in
theorem link_step (hSeg : GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement) (hM3 : HodgeLatticeFlagBound) (hTv : TrivFlagOnHodge)
    (S₀ S : Finset ℕ) (M₀ M₁ Rf : RootModel (CMType H) (D.p + D.q))
    (Sys : PB.AnSys (dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys)
    (o₀ : RootOrigin Y S₀ M₀ Fx) (o₁ : RootOrigin Y S M₁ Fx) (oR : RootOrigin Y ∅ Rf Fx)
    (II : IntersectionSystem) (hII : IsFullIntersectionSystem II)
    (hS : S₀ ⊆ S) (hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ S₀)
    (hom₀ : o₀.𝔐.OmVB) (hom₁ : o₁.𝔐.OmVB) (hR : ∀ p ∈ S₀, o₀.𝔐.R p = o₁.𝔐.R p) (hdeg : oR.Fl.deg = 1)
    (hJ₀ : o₀.Re.J = ⊤) (hJ₁ : o₁.Re.J = ⊤) (hJR : oR.Re.J = ⊤)
    (hc₀ : M₀.Converges II) (hc₁ : M₁.Converges II) (h2 : ∀ p ∈ S, p ∉ S₀ → p ≠ 2)
    (φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H)) (hφ : ∀ p ∈ S, p ∉ S₀ → IsFrobLabels c p (φ p)) :
    ∃ (M : RootModel (CMType H) (D.p + D.q)) (R : SecondRoots M),
      M.Converges II ∧ R.model.Converges II ∧
      (∀ F : RP (CMType H) (D.p + D.q), M.PP II (toA F) = M₀.PP II (toA F)) ∧
      (∀ F : RP (CMType H) (D.p + D.q), R.model.PP II (toA F) = M₁.PP II (toA F)) ∧
      (∀ F : RP (CMType H) (D.p + D.q), M.geoFun (toA F) = M₀.geoFun (toA F)) ∧
      R.IsChange ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) ∧
      R.LocalAtPlaces D.p ((S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn) φ := by
  obtain ⟨Ω, _, _, K, _, J, _, y, κ₀, v₀, κ₁, v₁, κR, vR, i₀, i₁, iR, 𝔐, Fl, hv₀, hv₁, hvR, hy₀, hy₁, hyR, hg₀, hg₁,
    hd0, hdeq, ⟨h, hvb, hsub, hl₀⟩, hl₁, hfr⟩ := GlobalTheory.T.root_origin_comparison_subset E H D l Xo c Y S₀ S M₀ M₁ Rf Sys Fx o₀ o₁ oR hS hdisc hom₀ hom₁ hR hdeg
  have hβ : Function.Injective (algebraMap (𝓞 c.F) c.F) := RingOfIntegers.coe_injective
  have : Nonempty K := ⟨κ₀ o₀.k₀⟩
  obtain ⟨hbir, harith⟩ := GlobalTheory.T.hodge_cpt_birational_arith_var E H D l Xo c _ _ Y S Ω K J y 𝔐 Fl hβ
  have ha : ReciprocityTheory.ChartRestriction.G.Geo.IsArithVar (mCoordIdeal y) (dimFl (CMType H) (D.p + D.q) + 1) := harith
  have hδ : 0 < IntermediateField.relfinrank (blockFnField (y ∘ v₀)) (blockFnField y) * M₀.δ :=
    Nat.mul_pos (Nat.pos_of_ne_zero hd0) M₀.δ_pos
  let M : RootModel (CMType H) (D.p + D.q) := pullModel M₀ y ha hbir hv₀ _ hδ
  obtain ⟨f, g, hfg, hvert⟩ := GlobalTheory.T.flag_height_bound_of_arith_var E H D l Xo c (𝓞 c.F) (algebraMap _ _) Y S Ω K J y 𝔐 _ ha Fl S₀ h hvb hsub _ _ _ _ hl₀ hl₁
  let Sp : Finset Nat.Primes := (S \ S₀).preimage (fun p : Nat.Primes => (p : ℕ)) Subtype.val_injective.injOn
  let Tr : CMType H × Fin (D.p + D.q) → LocPair J ℤ Unit := fun r =>
    ⟨fun _ => pullDeg κ₀ (M₀.xdeg r), fun _ => pullDeg κ₁ (M₁.xdeg r), fun _ => f r, fun _ => g r⟩
  have hTr : ∀ r, (Tr r).IsVertOff (mCoordIdeal y) Sp := fun r _ => hvert r
  have htw : ∀ (t : ℝ) (r : CMType H × Fin (D.p + D.q)), ∃ A' : HermLine J, IsSmoothHerm A' ∧ IsConjInvariantH A' ∧
      (Tr r).IsIsometric (mCoordIdeal y) (fun _ => M.x t r) (fun _ => A') := fun t r =>
    GlobalTheory.T.exists_isometric_herm_line K J (mCoordIdeal y) _ ha Sp (Tr r) (hTr r) (M.x t r) (M.x_deg t r) (M.x_smooth t r) (M.x_conj t r)
  choose tw tws twc twi using htw
  have ht₀ : 0 < Sys.t₀ := (Sys.reg none).1
  let x' : ℝ → CMType H × Fin (D.p + D.q) → HermLine J := fun t r =>
    if 0 < t ∧ t ≤ Sys.t₀ then pullHerm hv₁ (M₁.x t r) else tw t r
  have hx'deg : ∀ t r, (x' t r).a = pullDeg κ₁ (M₁.xdeg r) := fun t r => by
    by_cases ht : 0 < t ∧ t ≤ Sys.t₀
    · simp only [x', ite_eq_left ht]
      show pullDeg κ₁ (M₁.x t r).a = _
      rw [M₁.x_deg]
    · simp only [x', ite_eq_right ht]
      exact ((twi t r) ()).2.1
  have hx's : ∀ t r, IsSmoothHerm (x' t r) := fun t r => by
    by_cases ht : 0 < t ∧ t ≤ Sys.t₀
    · simp only [x', ite_eq_left ht]
      exact Chg.isSmoothHerm_pull hv₁ (M₁.x_smooth t r)
    · simp only [x', ite_eq_right ht]
      exact tws t r
  have hx'c : ∀ t r, IsConjInvariantH (x' t r) := fun t r => by
    by_cases ht : 0 < t ∧ t ≤ Sys.t₀
    · simp only [x', ite_eq_left ht]
      exact Chg.isConj_pull hv₁ (M₁.x_conj t r)
    · simp only [x', ite_eq_right ht]
      exact twc t r
  let R : SecondRoots M :=
    { xdeg := fun r => pullDeg κ₁ (M₁.xdeg r), x := x', x_deg := hx'deg, x_smooth := hx's, x_conj := hx'c, f := f, g := g }
  have hTL : Fl.TwoLevels S₀ (⟨fun r => pullDeg κ₀ (M₀.xdeg r), fun r => pullDeg κ₁ (M₁.xdeg r), f, g⟩ :
      LocPair J ℤ (CMType H × Fin (D.p + D.q))) :=
    ⟨h, hvb, hsub, _, _, hl₀, hl₁, hfg, hvert⟩
  obtain ⟨hvert', hloc⟩ := GlobalTheory.T.hodge_comp_root_model_primes hSeg hM3 hTv E H D l Xo c _ _ Y S S₀ M 𝔐 Fl R hTL
    (fun p hp hp' => ⟨hfr p hp, h2 p hp hp', fun hd => hp' (hdisc p (𝔐.S_prime p hp) hd)⟩) φ hφ
  have hIso : ∀ t, 0 < t → R.pairs.IsIsometric M.P (M.x t) (R.x t) := fun t ht r => by
    refine ⟨M.x_deg t r, R.x_deg t r, fun z hz => ?_⟩
    by_cases ht' : t ≤ Sys.t₀
    · obtain ⟨⟨bf, bg, hbf, hbg, hb⟩, hfP, hgP, -⟩ := hvert r
      have e1 : (R.x t r).h z = (M₁.x t r).h (fun p => z (v₁ p)) := by
        show (x' t r).h z = _
        simp only [x', ite_eq_left (And.intro ht ht')]
        rfl
      rw [e1]
      exact GlobalTheory.T.root_origin_height_comparison_three E H D l Xo c Y S₀ S M₀ M₁ Rf Sys Fx o₀ o₁ oR Ω K J y κ₀ v₀ κ₁ v₁ κR vR i₀ i₁ iR hv₀ hv₁ hvR hy₀ hy₁ hyR hg₀ hg₁
        hJ₀ hJ₁ hJR hdeg ha r (f r) (g r) bf bg hbf hbg hb hfP hgP (hfg r) t ht ht' z hz
    · have e1 : R.x t r = tw t r := by
        show x' t r = _
        simp only [x', ite_eq_right (fun hh : 0 < t ∧ t ≤ Sys.t₀ => ht' hh.2)]
      rw [e1]
      exact ((twi t r) ()).2.2 z hz

  obtain ⟨T, hTx, hTx', hTv', hTi⟩ := GlobalTheory.T.root_origin_height_comparison_two E H D l Xo c Y S₀ S M₀ M₁ Sys Fx o₀ o₁ Ω K J y κ₀ v₀ κ₁ v₁ i₀ i₁ hv₀ hv₁ hy₀ hy₁
    (by rw [hg₀, hg₁]) ha
  have hAs := Chg.isSmoothHerm_pull hv₁ M₁.A_smooth
  have hAc := Chg.isConj_pull hv₁ M₁.A_conj
  let Rm := R.model
  let R2 := reline Rm Rm.xdeg Rm.x Rm.x_deg Rm.x_smooth Rm.x_conj (pullHerm hv₁ M₁.A) hAs hAc
  let M₁' := reline Rm Rm.xdeg (fun t r => pullHerm hv₁ (M₁.x t r))
    (fun t r => by
      show pullDeg κ₁ (M₁.x t r).a = _
      rw [M₁.x_deg]
      rfl) (fun t r => Chg.isSmoothHerm_pull hv₁ (M₁.x_smooth t r))
    (fun t r => Chg.isConj_pull hv₁ (M₁.x_conj t r)) (pullHerm hv₁ M₁.A) hAs hAc
  have hkA : M₁'.kA = M₁.kA := by
    show M₀.kA = M₁.kA
    rw [o₀.kA_eq, o₁.kA_eq]
  have : CharZero M₁'.Ω := ‹CharZero Ω›
  obtain ⟨-, hPP₁, hCv₁, -⟩ := GlobalTheory.T.root_model_block_pullback _ _ M₁ M₁' II hII κ₁ v₁ hv₁ (imageZ_of_restr i₁ M₁.y y hv₁ hy₁)
    (fun t r => by
      cases r with
      | none => exact ⟨rfl, fun _ => rfl⟩
      | some r => exact ⟨rfl, fun _ => rfl⟩) hkA hdeq
  have hev : ∀ m, ∀ᶠ t in 𝓝[>] (0 : ℝ), M₁'.arMono II t m = Rm.arMono II t m := fun m => by
    filter_upwards [Ioo_mem_nhdsGT ht₀] with t ht
    rw [GlobalTheory.T.arMono_eq_relined_isometric_vert _ _ Rm II hII (pullHerm hv₁ M₁.A) hAs hAc T hTv' hTi t m]
    refine arMono_reline Rm II t m (fun r => ?_) rfl
    show pullHerm hv₁ (M₁.x t r) = x' t r
    simp only [x', ite_eq_left (And.intro ht.1 ht.2.le)]
  have hCv : Rm.Converges II := fun m => by
    obtain ⟨L, hL⟩ := hCv₁ hc₁ m
    exact ⟨L, hL.congr' (hev m)⟩
  have : CharZero M.Ω := ‹CharZero Ω›
  obtain ⟨-, hPP₀, hCv₀, hgeo⟩ := GlobalTheory.T.root_model_block_pullback _ _ M₀ M II hII κ₀ v₀ hv₀ (imageZ_of_restr i₀ M₀.y y hv₀ hy₀)
    (fun t r => by
      cases r with
      | none => exact ⟨rfl, fun _ => rfl⟩
      | some r => exact ⟨rfl, fun _ => rfl⟩) rfl rfl
  refine ⟨M, R, hCv₀ hc₀, hCv, fun F => by rw [hPP₀], fun F => ?_, fun F => by rw [hgeo], ⟨hvert', hIso⟩, hloc⟩
  rw [← hPP₁]
  refine (Indep.pp_toA_eq_of_tendsto M₁' Rm II (hCv₁ hc₁) (fun m => ?_) F).symm
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [hev (m.mapDomain some)] with t ht
  rw [ht, sub_self]

end GlobalTheory.CompanionTheory.Ar.Top.Link

namespace GlobalTheory.CompanionTheory.Ar.Top.Link

theorem goodOrigin_linked {P : Prop} : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → PB.AgreementPos → HodgeLatticeFlagBound → TrivFlagOnHodge →
    ((PartI ∧ N1ab ∧ N1c ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H),
      ToroidalLevelCompatibility (D := D) ∧ ToroidalHeckeCompatibility (D := D)) ∧ KeyFormula ∧ GlobalTheory.Published.SemiAbelianHomExtension ∧
    GroundTheory.Heights₂.Heights.NumbersDVR.NumericalSegre.Statement ∧ ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement ∧ ReciprocityTheory.ChartRestriction.G.SA.SAStatement ∧
    HT.FarguesHodgeTate ∧ Flat.GagaSections ∧ SlopeBoundSt ∧ PB.Inputs ∧ Prov.HS ∧ Prov.An ∧ Prov.ZhangDimensionPushDownGrassmannianHeightBounds ∧
    P) → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∃ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), FrobShape (fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ)) ∧ Num.LinkedTower T II φ := by
  intro _ hA hM3 hTv hG E _ _ _ _ H D Xo l c Y _ T o II _ hX hII _ _
  obtain ⟨-, -, -, hSeg, -, -, -, -, -, hIn, -⟩ := hG
  obtain ⟨φ, hφ, hsh⟩ := GlobalTheory.T.frobenius_labels_shape E (fun a b => IsMulCommutative.is_comm.comm a b) H l c
  refine ⟨φ, hsh, ?_⟩
  intro B₀ B h2 hB a
  have hConv : T.Conv II := (GlobalTheory.T.real_tower_conv_I2 hA hIn II hII _ _ T (realOf o.toTowerOrigin)).1
  have hmem : ∀ (B' p : ℕ), p ∈ o.S B' ↔ p.Prime ∧ (p ≤ B' ∨ p ∈ T.bad) := fun B' p => o.S_iff B' p
  have hsub : o.S B₀ ⊆ o.S B := fun p hp => by
    obtain ⟨h1, h3⟩ := (hmem _ _).1 hp
    exact (hmem _ _).2 ⟨h1, h3.imp (fun h => h.trans hB) id⟩
  have hdisc : ∀ p : ℕ, p.Prime → (p : ℤ) ∣ NumberField.discr E → p ∈ o.S B₀ := fun p hp hd =>
    (hmem _ _).2 ⟨hp, Or.inr ((o.bad_iff p).2 ⟨hp, Dvd.dvd.mul_right (Dvd.dvd.mul_left hd 2) _⟩)⟩
  have hRR : ∀ p ∈ o.S B₀, (o.Or B₀ a).𝔐.R p = (o.Or B a).𝔐.R p := fun p hp => by
    rw [hX.2 B₀ a p hp, hX.2 B a p (hsub hp)]
  have h2' : ∀ p ∈ o.S B, p ∉ o.S B₀ → p ≠ 2 := fun p _ hp' e => by
    subst e
    exact hp' ((hmem _ _).2 ⟨Nat.prime_two, Or.inr T.two_mem⟩)
  obtain ⟨M, R, c1, c2, c3, c4, c5, c6, c7⟩ := link_step hSeg hM3 hTv (o.S B₀) (o.S B) (T.M B₀ a) (T.M B a) (o.R a) (o.Sys a) (o.Fx a)
    (o.Or B₀ a) (o.Or B a) (o.refOr a) II hII hsub hdisc (o.omVB B₀ a) (o.omVB B a) hRR (o.ref_deg a) (o.smooth B₀ a).1
    (o.smooth B a).1 (o.ref_top a) (hConv B₀ a) (hConv B a) h2' φ (fun p hp _ => hφ p ((hmem _ _).1 hp).1)
  refine ⟨M, R, _, fun p => ?_, c1, c2, c3, c4, c5, c6, ?_⟩
  · refine Finset.mem_preimage.trans ?_
    rw [Finset.mem_sdiff, hmem, hmem]
    have hp : (p : ℕ).Prime := p.2
    constructor
    · rintro ⟨⟨-, h3⟩, h4⟩
      have h5 : ¬ ((p : ℕ) ≤ B₀ ∨ (p : ℕ) ∈ T.bad) := fun h => h4 ⟨hp, h⟩
      push_neg at h5
      exact ⟨h5.1, h3.resolve_right h5.2, h5.2⟩
    · rintro ⟨h3, h4, h5⟩
      exact ⟨⟨hp, Or.inl h4⟩, fun h => h.2.elim (fun h' => absurd h' (not_le.2 h3)) h5⟩
  · rw [o.j_eq]
    exact c7

end GlobalTheory.CompanionTheory.Ar.Top.Link
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.GoodTowerGlobalConditionsStatement
attribute [-instance] GlobalTheory.CompHt.fintypePsi
open AlgebraicGeometry CategoryTheory NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top
open GroundTheory.Heights₂.Heights.LowerBoundFree (ComponentData ComponentSetting degMu ArLimExists slX)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.good_tower_global_conditions : GlobalTheory.CompanionTheory.Ar.Cmp.CmpSt → PB.AgreementPos → HodgeLatticeFlagBound → TrivFlagOnHodge → Given → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (H : Host E) (D : Datum H) (Xo : ∀ l : Level H, Moduli D l) (l : Level H) (c : Coeff l) (Y : Model (Xo l) c (algebraMap (𝓞 c.F) c.F)) [DecidableEq (CMType H)] (T : RootTower (CMType H) (D.p + D.q)) (o : GoodOrigin Y T) (II : IntersectionSystem), IsGlobal Xo l c Y → o.Extra → IsFullIntersectionSystem II → 1 ≤ D.p → 1 ≤ D.q → ∃ φ : ℕ → Equiv.Perm (CMType H ⊕ CMType H), FrobShape (fun p τ n => (φ p ^ (n + 1)) (Sum.inl τ)) ∧ Num.LinkedTower T II φ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Top.Link.goodOrigin_linked | exact GlobalTheory.CompanionTheory.Ar.Top.Link.goodOrigin_linked | (intros; apply GlobalTheory.CompanionTheory.Ar.Top.Link.goodOrigin_linked <;> assumption)
end
