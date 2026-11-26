module

public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
public import Formalism.LocalToGlobal.Columns.TwQLevU
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemPrinCongOfSm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReductionModPrimeLevelPrimeSmulEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResCharConj
public import Formalism.LocalToGlobal.UnitaryNorms.LeastSplitAuxiliaryPrimeThetaChainSpec
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FamilyClassSevenDutiesAndStableLattices
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetFramesInvariantRationalUnitary

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

namespace GlobalTheory.ChebSplitDense

theorem chebSplit (hC : GlobalTheory.Published.ChebotarevDegreeOne) {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
    (N : NData R H what₂) : GlobalTheory.RowTie.ChebSplit N := by
  intro S
  obtain ⟨A, hA, hsp⟩ := GlobalTheory.FrobDense.exists_finite_split H
  refine (hC.dense (F := H.E) (Ω := N.Om) (hA.union S.finite_toSet)).mono ?_
  rintro σ ⟨v, hv, hd, B, hB, hσ⟩
  simp only [Set.mem_union, Finset.mem_coe, not_or] at hv
  exact ⟨v, hv.2, hsp v hv.1 hd, B, hB, hσ⟩

theorem chebSplit_nd : GlobalTheory.Published.ChebotarevDegreeOne → ∀ D : D7, GlobalTheory.RowTie.ChebSplit D.nd :=
  fun hC D => chebSplit hC D.nd

end GlobalTheory.ChebSplitDense
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.WeilDeligne NumberField IsDedekindDomain Polynomial

theorem eventually_natCast_notMem (E : Type) [Field E] [NumberField E] (l : ℕ) [hl : Fact l.Prime] :
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ((l : ℕ) : 𝓞 E) ∉ w.asIdeal := by
  have h0 : (Ideal.span {((l : ℕ) : 𝓞 E)} : Ideal (𝓞 E)) ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact Nat.cast_ne_zero.2 hl.out.ne_zero
  rw [Filter.eventually_cofinite]
  refine (Ideal.finite_factors h0).subset fun w hw => ?_
  simpa [Ideal.dvd_span_singleton] using hw

end GlobalTheory.HeightCounting

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NeZeroTop
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.UG GlobalTheory.Mem GlobalTheory.Mem.Col2 Matrix

namespace GlobalTheory.Mem.Col2.TopCh

section Loc

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {n : ℕ}

theorem phi_int (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) ≤ 1 := by

  have h : Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) =
      P.valuation E (algebraMap (𝓞 E) E r) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := P) _
  rw [h]
  exact HeightOneSpectrum.valuation_le_one (K := E) (v := P) r

theorem phi_lt (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) < 1 ↔ r ∈ P.asIdeal := by
  have h : Valued.v ((algebraMap E (P.adicCompletion E)) (algebraMap (𝓞 E) E r)) =
      P.valuation E (algebraMap (𝓞 E) E r) :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := P) _
  rw [h]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) (v := P) r

def locLev (P : HeightOneSpectrum (𝓞 E)) (Θ : LevI E K n P) (d : E) : Subgroup (GL (Fin n) (P.adicCompletion E)) :=
  qbU (F := E) P (algebraMap E (P.adicCompletion E)) (phi_int P) (phi_lt P) Θ (algebraMap E (P.adicCompletion E) d)

abbrev iotaP (P : HeightOneSpectrum (𝓞 E)) : ↥(GLint E n P) →* GL (Fin n) (P.adicCompletion E) :=
  qbIota (F := E) P (algebraMap E (P.adicCompletion E))

def locChr (P : HeightOneSpectrum (𝓞 E)) (Θ : LevI E K n P) (d : E) (hd : d ≠ 0) {N : ℕ} (hdN : P.valuation E d ≤ WithZero.exp (-(N : ℤ)))
    (hΘ : ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ Θ.H, Θ.lam ⟨g, h⟩ = 1) : locLev P Θ d →* Kˣ :=
  qbChr (F := E) P (algebraMap E (P.adicCompletion E)) (phi_int P) (phi_lt P) Θ d hd hdN hΘ

end Loc

section Ad

variable {F E K : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] [Field K] {n : ℕ}
  {Q : Finset (HeightOneSpectrum (𝓞 E))}


variable (F) in
abbrev rhoP (P : HeightOneSpectrum (𝓞 E)) : GL (Fin n) (AfE F E) →* GL (Fin n) (P.adicCompletion E) := bc (adAt F P)


variable (F) in
def rhoT (P : HeightOneSpectrum (𝓞 E)) (t : GL (Fin n) (AfE F E)) : GL (Fin n) (AfE F E) →* GL (Fin n) (P.adicCompletion E) :=
  (rhoP F P).comp (MulAut.conj t⁻¹).toMonoidHom

def topU (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) : Subgroup (GL (Fin n) (AfE F E)) :=
  U ⊓ ⨅ P : Q, (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t)

theorem topU_le (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) : topU U t Θ d ≤ U :=
  inf_le_left

theorem rhoT_mem {U : Subgroup (GL (Fin n) (AfE F E))} {t : GL (Fin n) (AfE F E)} {Θ : LevQFam E K n Q} {d : Q → E}
    {x : GL (Fin n) (AfE F E)} (hx : x ∈ topU U t Θ d) (P : Q) : rhoT F P.1 t x ∈ locLev P.1 (Θ P) (d P) := by
  have hx' : x ∈ U ⊓ ⨅ P : Q, (locLev P.1 (Θ P) (d P)).comap (rhoT F P.1 t) := hx
  exact Subgroup.mem_comap.mp (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hx').2 P)

def topChi (σ : K →+* ℂ) (U : Subgroup (GL (Fin n) (AfE F E))) (t : GL (Fin n) (AfE F E)) (Θ : LevQFam E K n Q) (d : Q → E) (hd : ∀ P, d P ≠ 0)
    (N : Q → ℕ) (hdN : ∀ P : Q, P.1.valuation E (d P) ≤ WithZero.exp (-(N P : ℤ)))
    (hΘ : ∀ (P : Q) (g : ↥(GLint E n P.1)), lqPrinc P.1 (N P) (g : Sp E n ≃ₗ[E] Sp E n) → ∃ h : g ∈ (Θ P).H, (Θ P).lam ⟨g, h⟩ = 1) :
    topU U t Θ d →* ℂˣ :=
  (∏ P : Q, (Units.map (σ : K →* ℂ)).comp ((locChr P.1 (Θ P) (d P) (hd P) (hdN P) (hΘ P)).comp
    (((rhoT F P.1 t).comp (topU U t Θ d).subtype).codRestrict _ fun x => rhoT_mem x.2 P)))⁻¹

end Ad

instance neZero_top (R : Ranks) : NeZero (R.N R.m) := ⟨by have := N_m_succ R; omega⟩

end GlobalTheory.Mem.Col2.TopCh

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsOfFinOrderFbar
noncomputable section

namespace GlobalTheory.ParRay

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

@[reducible] def algK (D : D7) (jE : D.host.E →+* Qb) {M : Fld} (h : KQbar D jE ≤ M) : Algebra D.host.K M :=
  ((IntermediateField.inclusion h).toRingHom.comp (D.host.K.equivMap jE.toRatAlgHom).toRingHom).toAlgebra

theorem nfOf {M : Fld} (h : FiniteDimensional ℚ M) : NumberField M where
  to_finiteDimensional := h

theorem isOfFinOrder_fbar {g : ℕ} [Fact g.Prime] {x : Formalism.CyclotomicNorms.Fbar g} (hx : x ≠ 0) : IsOfFinOrder x := by
  have hint : IsIntegral (ZMod g) x := Algebra.IsIntegral.isIntegral x
  have := IntermediateField.adjoin.finiteDimensional hint
  have : Finite (IntermediateField.adjoin (ZMod g) {x}) := Module.finite_of_finite (ZMod g)
  let y : IntermediateField.adjoin (ZMod g) {x} := ⟨x, IntermediateField.mem_adjoin_simple_self _ x⟩
  have hy : y ≠ 0 := fun h => hx (congrArg Subtype.val h)
  have h1 : IsOfFinOrder (Units.mk0 y hy) := isOfFinOrder_of_finite _
  exact ((IntermediateField.adjoin (ZMod g) {x}).val.toMonoidHom.comp (Units.coeHom _)).isOfFinOrder h1

section Iota

theorem mem_of_monoidHom {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g : ℕ} [Fact g.Prime]
    (t : Formalism.CyclotomicNorms.Fbar g →* Ω) (x : Formalism.CyclotomicNorms.Fbar g) : t x ∈ B := by
  rcases eq_or_ne x 0 with rfl | hx
  · have h : t 0 * t 0 = t 0 := by rw [← map_mul, mul_zero]
    rcases eq_or_ne (t 0) 0 with h0 | h0
    · rw [h0]; exact zero_mem _
    · rw [(mul_eq_left₀ h0).1 h]; exact one_mem _
  · exact mem_of_pow_eq_one B (isOfFinOrder_fbar hx).orderOf_pos
      (by rw [← map_pow, pow_orderOf_eq_one, map_one])

def redHom {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g l : ℕ} [Fact g.Prime] [Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (t : Formalism.CyclotomicNorms.Fbar g →* Ω) :
    Formalism.CyclotomicNorms.Fbar g →* Formalism.CyclotomicNorms.Fbar l where
  toFun x := redThrough B κ (t x)
  map_one' := by rw [map_one]; exact redThrough_one B κ
  map_mul' x y := by
    rw [map_mul]; exact redThrough_mul B κ (mem_of_monoidHom B t x) (mem_of_monoidHom B t y)

end Iota

theorem redHom_inj {Ω : Type} [Field Ω] (B : ValuationSubring Ω) {g l : ℕ} [Fact g.Prime] [hl : Fact l.Prime]
    (κ : IsLocalRing.ResidueField B ≃+* Formalism.CyclotomicNorms.Fbar l) (t : Formalism.CyclotomicNorms.Fbar g →* Ω)
    (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (x y : Formalism.CyclotomicNorms.Fbar g) (hx : x ≠ 0) (hy : y ≠ 0)
    (cx : (orderOf x).Coprime l) (cy : (orderOf y).Coprime l) (h : redHom B κ t x = redHom B κ t y) : x = y := by
  let ρ : B →+* Formalism.CyclotomicNorms.Fbar l := κ.toRingHom.comp (IsLocalRing.residue B)
  have hρ : ∀ z (hz : z ∈ B), redThrough B κ z = ρ ⟨z, hz⟩ := fun z hz => by
    unfold redThrough; rw [dite_eq_left hz]; rfl
  have hz : x * y⁻¹ ≠ 0 := mul_ne_zero hx (inv_ne_zero hy)
  set n := orderOf (x * y⁻¹) with hn
  have hnpos : 0 < n := (isOfFinOrder_fbar hz).orderOf_pos
  have hcop : n.Coprime l := by
    refine Nat.Coprime.coprime_dvd_left ?_ (Nat.Coprime.mul_left cx cy)
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [mul_pow, inv_pow, pow_mul, pow_orderOf_eq_one, mul_comm (orderOf x), pow_mul, pow_orderOf_eq_one]
    simp
  have hmem := mem_of_monoidHom B t (x * y⁻¹)
  have hprim : IsPrimitiveRoot (t (x * y⁻¹)) n := by
    refine ⟨by rw [← map_pow, hn, pow_orderOf_eq_one, map_one], fun m hm => orderOf_dvd_of_pow_eq_one ?_⟩
    refine ht _ _ (pow_ne_zero _ hz) one_ne_zero ?_
    rw [map_pow, map_one]
    exact hm
  have hprimB : IsPrimitiveRoot (⟨t (x * y⁻¹), hmem⟩ : B) n :=
    IsPrimitiveRoot.coe_submonoidClass_iff.1 hprim
  have hred1 : ρ ⟨t (x * y⁻¹), hmem⟩ = 1 := by
    have hxy : x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
    have hy0 : redHom B κ t y ≠ 0 := by
      intro h0
      have hyo := (isOfFinOrder_fbar hy).orderOf_pos
      have : redHom B κ t y ^ orderOf y = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
      rw [h0, zero_pow hyo.ne'] at this
      exact zero_ne_one this
    have h2 : redHom B κ t (x * y⁻¹) * redHom B κ t y = 1 * redHom B κ t y := by
      rw [← map_mul, ← hxy, one_mul, h]
    have h3 := mul_right_cancel₀ hy0 h2
    rw [← hρ]
    exact h3
  have : NeZero ((n : ℕ) : Formalism.CyclotomicNorms.Fbar l) := ⟨fun h0 =>
    (Nat.Prime.coprime_iff_not_dvd hl.out).1 hcop.symm ((CharP.cast_eq_zero_iff _ l n).1 h0)⟩
  have h3 : IsPrimitiveRoot (1 : Formalism.CyclotomicNorms.Fbar l) n := by
    rw [← Polynomial.isRoot_cyclotomic_iff, ← hred1, ← Polynomial.map_cyclotomic n ρ, Polynomial.IsRoot,
      Polynomial.eval_map, Polynomial.eval₂_hom]
    rw [(hprimB.isRoot_cyclotomic hnpos).eq_zero, map_zero]
  have hn1 : n = 1 := IsPrimitiveRoot.one_left_iff.1 h3
  rw [hn, orderOf_eq_one_iff] at hn1
  calc x = x * y⁻¹ * y := by rw [mul_assoc, inv_mul_cancel₀ hy, mul_one]
    _ = y := by rw [hn1, one_mul]

end GlobalTheory.ParRay

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLaws
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLaws
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Ker GlobalTheory.ThetaMove.Moved

namespace GlobalTheory.Mem.NatEqui

variable {D : D7}

theorem chi_smulLat {χ : IdE D → ℂ} (hχ : IsChi D χ) {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E,
      χ (detId D (stdL D n) (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)) =
        (∏ τ : D.what₂.Tau, (embT D τ (γ : Matrix (Fin n) (Fin n) D.host.E).det)⁻¹) * χ (detId D (stdL D n) L) := by
  letI := D.host.cmStar
  intro γ
  have hst : ∀ x : D.host.E, star x = D.host.conj x := GlobalTheory.NormSum.AdLattice.star_eq_conj D
  let z : unitary D.host.E := ⟨_, Matrix.det_of_mem_unitary γ.2⟩
  rw [GlobalTheory.Mem.Col2.ChiFacLaw.detId_image D (stdL D n) L (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L)
    (γ : Matrix (Fin n) (Fin n) D.host.E)
    (star (γ : Matrix (Fin n) (Fin n) D.host.E)) γ.2.2 (fun x hx => ⟨x, hx, rfl⟩) ?_,
    hχ.1 _ _ (GlobalTheory.Mem.Col2.ChiFacLaw.norm_one_span D z.1 (by rw [← hst]; exact z.2.2))
      (GlobalTheory.RelDetIdeal.detId_normOne_mul D n _ _ _ (sd_stdL D n) hL hL).1, hχ.2 z]
  rintro _ ⟨y, hy, rfl⟩
  change (star (γ : Matrix (Fin n) (Fin n) D.host.E)).mulVec ((γ : Matrix (Fin n) (Fin n) D.host.E).mulVec y) ∈ L
  rwa [Matrix.mulVec_mulVec, γ.2.1, Matrix.one_mulVec]

theorem sd_smulLat {n : ℕ} {L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hL : SD D L) : letI := D.host.cmStar
    ∀ γ : Matrix.unitaryGroup (Fin n) D.host.E, SD D (SDLat.smulLat (γ : Matrix (Fin n) (Fin n) D.host.E) L) := by
  intro γ
  obtain ⟨g, hg⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D n L hL
  obtain ⟨γA, hγ⟩ := GlobalTheory.TrueTheta.exists_rat γ
  exact GlobalTheory.VacuumScalar.sd_of_moves (GlobalTheory.TrueTheta.moves_smulLat hγ hg)

theorem chiFac_ne_zero {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L'} (h : SD D L) (h' : SD D L') :
    Base.chiFac χ N N' L L' ≠ 0 :=
  mul_ne_zero (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N) h))
    (zpow_ne_zero _ (chi_detId_ne_zero hχ (sd_stdL D N') h'))

theorem chiFac_right {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} (L) {L' L''} (h' : SD D L') (h'' : SD D L'') :
    Base.chiFac χ N N' L L'' = χ (detId D L' L'') ^ (-((N / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N') h' h'', mul_zpow]
  ring

theorem chiFac_left {χ : IdE D → ℂ} (hχ : IsChi D χ) {N N' : ℕ} {L L₁} (L') (h : SD D L) (h₁ : SD D L₁) :
    Base.chiFac χ N N' L₁ L' = χ (detId D L L₁) ^ (((N' / 2 : ℕ) : ℤ)) * Base.chiFac χ N N' L L' := by
  unfold Base.chiFac
  rw [chi_detId_mul hχ (sd_stdL D N) h h₁, mul_zpow]
  ring

theorem eqP : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ),
    IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ := by
  intro D cc δ B χ hc hδ hχ
  letI := D.host.cmStar
  have hC : Crv D cc δ := ⟨hc, hδ⟩
  obtain ⟨χ', e, hχ', hv, q1, q2, q3⟩ := GlobalTheory.T.exists_thetaVectorFamily_of_curveDatum D cc δ hC
  have key : ∀ N N', Even N → Even N' → ∃ a : ℂ, ∀ L L', SD D L → SD D L' → B.eNat χ N N' L L' =
      fun z => (a * (Base.chiFac χ N N' L L' / Base.chiFac χ' N N' L L')) * e N N' L L' z := by
    intro N N' hN hN'
    have s := sd_stdL D N
    have s' := sd_stdL D N'
    obtain ⟨v1, v2, -⟩ := hv N N' _ _ ⟨hN, hN', s, s'⟩
    obtain ⟨a, ha⟩ := (GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hC N N' _
      (Or.inr ⟨_, _, s, s', rfl⟩)).1 _
      (GlobalTheory.Mem.Col2.WeilVac.thZero_mem B (GlobalTheory.FourthRootStd.stdOK_of_crv D cc δ B hC) N N') _ v1 v2
    refine ⟨a, fun L L' h h' => funext fun z => ?_⟩
    have e3 := q3 N N' ⟨_, s⟩ ⟨L, h⟩ ⟨_, s'⟩ hN hN'
    have e2 := congrFun (q2 N N' ⟨L, h⟩ ⟨_, s'⟩ ⟨L', h'⟩ hN hN') z
    dsimp only at e2 e3
    rw [e3, iop_mul, ← mul_assoc, mul_comm (χ' _ ^ _)] at e2
    have hh : B.thHalf N N' L = fun w => a * Iop D (tor0 D cc δ) (La D (tor0 D cc δ) (stdL D N) (stdL D N'))
        (La D (tor0 D cc δ) L (stdL D N')) (e N N' (stdL D N) (stdL D N')) w := by
      funext w
      rw [Base.thHalf, ha]
      exact iop_mul D _ _ _ a _ w
    have h0 := chiFac_ne_zero hχ' h h'
    change Base.chiFac χ N N' L L' * B.thMoved N N' L L' z = _
    rw [Base.thMoved, hh, iop_mul, e2]
    change _ = a * (_ / Base.chiFac χ' N N' L L') * (Base.chiFac χ' N N' L L' * _)
    field_simp
  refine ⟨fun N N' L L' hN hN' γ γ' => ?_, fun N N' L L' L'' hN hN' => ?_, fun N N' L L₁ L' hN hN' => ?_⟩
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ (sd_smulLat L.2 γ) (sd_smulLat L'.2 γ'), ← q1 N N' L L' hN hN' γ γ']
    have h1 := chiFac_ne_zero hχ' (sd_smulLat L.2 γ) (sd_smulLat L'.2 γ')
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    funext z
    change _ * pull D _ _ _ (e N N' L.1 L'.1) z = _
    congr 2
    rw [div_eq_div_iff h0 h1]
    unfold Base.chiFac
    rw [chi_smulLat hχ L.2, chi_smulLat hχ L'.2, chi_smulLat hχ' L.2, chi_smulLat hχ' L'.2]
    simp only [mul_zpow]
    ring
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ L.2 L''.2, q2 N N' L L' L'' hN hN']
    funext z
    have h1 := zpow_ne_zero (-((N / 2 : ℕ) : ℤ)) (chi_detId_ne_zero hχ' L'.2 L''.2)
    rw [iop_mul, chiFac_right hχ _ L'.2 L''.2, chiFac_right hχ' _ L'.2 L''.2]
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    generalize χ' _ ^ _ = u at h1 ⊢
    field_simp
  · obtain ⟨a, ha⟩ := key N N' hN hN'
    rw [ha _ _ L.2 L'.2, ha _ _ L₁.2 L'.2, q3 N N' L L₁ L' hN hN']
    funext z
    have h1 := zpow_ne_zero (((N' / 2 : ℕ) : ℤ)) (chi_detId_ne_zero hχ' L.2 L₁.2)
    rw [iop_mul, chiFac_left hχ _ L.2 L₁.2, chiFac_left hχ' _ L.2 L₁.2]
    have h0 := chiFac_ne_zero hχ' L.2 L'.2
    generalize χ' _ ^ _ = u at h1 ⊢
    field_simp

end GlobalTheory.Mem.NatEqui
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalisedFamilySatisfiesEquivarianceLawsStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalisedFamily_satisfies_equivarianceLaws : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : IdE D → ℂ), IsCurveIdeal D cc → IsDiscriminantTwelfthRootOfIdealLattice D cc δ → IsChi D χ → B.EqP χ := by
  first | exact @GlobalTheory.Mem.NatEqui.eqP | exact GlobalTheory.Mem.NatEqui.eqP | (intros; apply GlobalTheory.Mem.NatEqui.eqP <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrime
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

noncomputable section

namespace GlobalTheory.Mem.Col2.BasePoint

open GlobalTheory.Mem.Col2.PtExist

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]

private lemma mem_divs_iff' {E : Type} [Field E] [NumberField E] {π : 𝓞 E} {P : HeightOneSpectrum (𝓞 E)}
    (h : P ∈ divs π) : π ∈ P.asIdeal := by
  unfold divs at h
  split_ifs at h with hf
  · simpa using h
  · simp at h

private lemma false_of_mem_of_conj_mem_of_isCoprime {E : Type} [Field E] [NumberField E] [StarRing E] {π : 𝓞 E} (hcp : IsCoprime π (cO E π))
    (P : HeightOneSpectrum (𝓞 E)) (h1 : π ∈ P.asIdeal) (h2 : cO E π ∈ P.asIdeal) : False := by
  obtain ⟨u, v, h⟩ := hcp
  apply P.isPrime.ne_top
  rw [Ideal.eq_top_iff_one, ← h]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)

private lemma valued_algebraMap_int_le_one' {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E) :
    Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) ≤ 1 := by
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
  exact HeightOneSpectrum.intValuation_le_one P r

private lemma valued_algebraMap_eq_one_of_not_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E)
    (hr : r ∉ P.asIdeal) : Valued.v (algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E r)) = 1 := by
  erw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation, HeightOneSpectrum.valuation_of_algebraMap]
  have h2 : ¬ P.intValuation r < 1 := fun h => hr ((HeightOneSpectrum.intValuation_lt_one_iff_mem P r).1 h)
  exact le_antisymm (HeightOneSpectrum.intValuation_le_one P r) (not_lt.1 h2)

private lemma valued_inv_algebraMap_le_one_of_not_mem {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (r : 𝓞 E)
    (hr : r ∉ P.asIdeal) : Valued.v (algebraMap E (P.adicCompletion E) ((algebraMap (𝓞 E) E r)⁻¹)) ≤ 1 := by
  rw [map_inv₀, map_inv₀, valued_algebraMap_eq_one_of_not_mem P r hr, inv_one]

private lemma mem_RInt_of_valued_le_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (y : AfE F E)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), Valued.v (adAt F P y) ≤ 1) : y ∈ RInt F E :=
  (GlobalTheory.Mem.Col2.mem_rInt_iff F E y).2 h

theorem exists_unit (hc : Formalism.BasicNotions.CMData F E) {π : 𝓞 E} (h0 : π ≠ 0) (h1 : cO E π ≠ 0) (hcp : IsCoprime π (cO E π)) :
    ∃ a a' : AfE F E, a' * a = 1 ∧ sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a = a' ∧ a ∈ RInt F E ∧ a' ∈ RInt F E ∧
      (∀ P ∈ divs π, adAt F P a' = algebraMap E _ (algebraMap (𝓞 E) E (cO E π))) ∧
      ∀ w : HeightOneSpectrum (𝓞 E), π * cO E π ∉ w.asIdeal → adAt F w a = 1 := by
  classical
  have hmem : ∀ {P : HeightOneSpectrum (𝓞 E)}, P ∈ divs π → π ∈ P.asIdeal := fun h => mem_divs_iff' h
  have hQ : ∀ P ∈ divs π, conjPrime₂ P ∉ divs π := by
    intro P hP hP'
    exact false_of_mem_of_conj_mem_of_isCoprime hcp P (hmem hP) ((mem_conjP P π).1 (hmem hP'))
  have hc0 : (algebraMap (𝓞 E) E (cO E π)) ≠ 0 := by
    intro h
    exact h1 ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective (𝓞 E) E)).1 h)
  have hst : star (algebraMap (𝓞 E) E (cO E π)) = algebraMap (𝓞 E) E π := by
    change star (starRingEnd E (algebraMap (𝓞 E) E π)) = _
    rw [starRingEnd_apply, star_star]
  let α : HeightOneSpectrum (𝓞 E) → E := fun _ => (algebraMap (𝓞 E) E (cO E π))⁻¹
  let β : HeightOneSpectrum (𝓞 E) → E := fun _ => algebraMap (𝓞 E) E (cO E π)
  let a := GlobalTheory.Mem.Col2.PtExist.glue hc (divs π) 1 α β
  have ha : ∀ w, adAt F w a = if w ∈ divs π then algebraMap E _ (α w)
      else if conjPrime₂ w ∈ divs π then algebraMap E _ (star (β (conjPrime₂ w))) else 1 := fun w => by
    rw [GlobalTheory.Mem.Col2.PtExist.adAt_glue hc (divs π) hQ 1 α β w, map_one]
  have ha' : ∀ w, adAt F w (sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a) = if w ∈ divs π then algebraMap E _ (β w)
      else if conjPrime₂ w ∈ divs π then algebraMap E _ (star (α (conjPrime₂ w))) else 1 := fun w => by
    rw [GlobalTheory.Mem.Col2.PtExist.sig_glue hc (divs π) 1 α β, map_one,
      GlobalTheory.Mem.Col2.PtExist.adAt_glue hc (divs π) hQ 1 β α w, map_one]
  refine ⟨a, sigR hc.sig (FiniteAdeleRing (𝓞 F) F) a, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · apply GlobalTheory.Mem.Col2.PtExist.ad_ext
    intro w
    rw [map_mul, ha, ha', map_one]
    split_ifs with hw hw'
    · rw [← map_mul, mul_inv_cancel₀ hc0, map_one]
    · rw [← map_mul, star_inv₀, inv_mul_cancel₀ (star_ne_zero.2 hc0), map_one]
    · rw [mul_one]
  · apply mem_RInt_of_valued_le_one
    intro P
    rw [ha]
    split_ifs with hw hw'
    · exact valued_inv_algebraMap_le_one_of_not_mem P _ (fun h => false_of_mem_of_conj_mem_of_isCoprime hcp P (hmem hw) h)
    · rw [hst]
      exact valued_algebraMap_int_le_one' P π
    · rw [map_one]
  · apply mem_RInt_of_valued_le_one
    intro P
    rw [ha']
    split_ifs with hw hw'
    · exact valued_algebraMap_int_le_one' P _
    · rw [star_inv₀, hst]
      exact valued_inv_algebraMap_le_one_of_not_mem P π (fun h => false_of_mem_of_conj_mem_of_isCoprime hcp P h ((mem_conjP P π).1 (hmem hw')))
    · rw [map_one]
  · intro P hP
    rw [ha', if_pos hP]
  · intro w hw
    rw [ha]
    split_ifs with h2 h3
    · exact absurd (Ideal.mul_mem_right _ _ (hmem h2)) hw
    · exact absurd (Ideal.mul_mem_left _ _ ((mem_conjP w π).1 (hmem h3))) hw
    · rfl

def stdPt (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : DecoF E n ∅ ∅ ∅ :=
  ⟨(⟨⟨stdLat E n, fun _ _ => 0, fun _ _ _ => 0⟩, stdLat_lattice, stdLat_unimodular,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim, fun P => (Finset.notMem_empty _ P.2).elim,
      fun P => (Finset.notMem_empty _ P.2).elim⟩, fun _ => 1), fun P => (Finset.notMem_empty _ P.2).elim⟩

theorem exists_base (hc : Formalism.BasicNotions.CMData F E) {π : 𝓞 E} {T : ℕ} (hT : T ≠ 0) (hπ : π * cO E π = T)
    (hcp : IsCoprime π (cO E π)) (n : ℕ) :
    ∃ k : GL (Fin n) (AfE F E), (∃ p : DecoF E n ∅ ∅ ∅, IsPtOf hc k p ∧ p.deco.1.N = stdLat E n) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), (T : 𝓞 F) ∉ v.asIdeal → bc (prV (E := E) v) k = 1) ∧
      ∀ (P : divs π) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt F P.1 ((k⁻¹).1 r j))
        (if j = r then Ideal.Quotient.mk P.1.asIdeal (cO E π) else 0) := by
  classical
  have hT0 : ((T : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hT
  have h0 : π ≠ 0 := fun h => hT0 (by rw [← hπ, h, zero_mul])
  have h1 : cO E π ≠ 0 := fun h => hT0 (by rw [← hπ, h, mul_zero])
  obtain ⟨a, a', haa, hσ, hai, hai', hP, hw⟩ := exists_unit hc h0 h1 hcp
  let d : Fin n → AfE F E := fun i => if i.1 + 1 = n then a else 1
  let d' : Fin n → AfE F E := fun i => if i.1 + 1 = n then a' else 1
  have hd : ∀ i, d' i * d i = 1 := fun i => by
    simp only [d, d']
    split_ifs
    · exact haa
    · exact mul_one 1
  have hd' : ∀ i, d i * d' i = 1 := fun i => by rw [mul_comm]; exact hd i
  have hdi : ∀ i, d i ∈ RInt F E := fun i => by
    simp only [d]
    split_ifs
    · exact hai
    · exact one_mem _
  have hdi' : ∀ i, d' i ∈ RInt F E := fun i => by
    simp only [d']
    split_ifs
    · exact hai'
    · exact one_mem _
  let k : GL (Fin n) (AfE F E) := ⟨Matrix.diagonal d, Matrix.diagonal d',
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hd']; exact Matrix.diagonal_one,
    by rw [Matrix.diagonal_mul_diagonal]; simp only [hd]; exact Matrix.diagonal_one⟩
  have hk : ((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = Matrix.diagonal d := rfl
  have hk' : ((k⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) = Matrix.diagonal d' := rfl
  refine ⟨k, ⟨stdPt E n, ?_, rfl⟩, ?_, ?_⟩
  · constructor
    · apply (GlobalTheory.Mem.Col2.PtExist.mem_uad_iff k).2
      unfold Formalism.UG.cT
      rw [hk, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal,
        ← Matrix.diagonal_one]
      congr 1
      funext i
      dsimp [d]
      split_ifs
      · rw [hσ, haa]
      · rw [map_one, one_mul]
    · intro x
      unfold Formalism.L2.Herm.hatL
      change x ∈ Formalism.UG.latS (F := F) (Formalism.L2.Herm.Af F) (Formalism.L2.Herm.intAf F E) (Formalism.L2.Col.stdLat E n) ↔ _
      rw [Formalism.L2.Col.mem_latS_std, Formalism.L2.Col.mem_latS_std, hk']
      constructor
      · intro h i
        rw [Matrix.mulVec_diagonal]
        exact mul_mem (hdi' i) (h i)
      · intro h i
        have := mul_mem (hdi i) (h i)
        rwa [Matrix.mulVec_diagonal, ← mul_assoc, hd' i, one_mul] at this
    all_goals intro P; exact (Finset.notMem_empty _ P.2).elim
  · intro v hv
    have hpa : prV (E := E) v a = 1 := by
      have h := ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v (a - 1)).1).2 (fun w hwv => by
        have hnot : π * cO E π ∉ w.asIdeal := by
          intro hmw
          apply hv
          rw [← hwv]
          change algebraMap (𝓞 F) (𝓞 E) (T : 𝓞 F) ∈ w.asIdeal
          rw [map_natCast, ← hπ]
          exact hmw
        rw [map_sub, hw w hnot, map_one, sub_self])
      rwa [map_sub, map_one, sub_eq_zero] at h
    apply Units.ext
    rw [Units.val_one]
    change (Matrix.diagonal d).map (prV (E := E) v) = 1
    rw [Matrix.diagonal_map (map_zero _), ← Matrix.diagonal_one]
    congr 1
    funext i
    dsimp [d]
    split_ifs
    · exact hpa
    · exact map_one _
  · intro P r j hr
    rw [hk']
    unfold HasRes
    by_cases hj : j = r
    · subst hj
      rw [Matrix.diagonal_apply_eq, if_pos rfl]
      simp only [d', if_pos hr]
      rw [hP P.1 P.2]
      exact ⟨cO E π, rfl, by rw [sub_self, map_zero]; exact zero_lt_one⟩
    · rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), if_neg hj, map_zero]
      exact ⟨0, map_zero _, by rw [map_zero, map_zero, sub_self, map_zero]; exact zero_lt_one⟩

end General

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

theorem exists_kStd : ∀ {B : Base} (X : PreX B.toPre), (B.primes X).Ok → ∀ (u : B.Word) (n : ℕ), ∃ k : GA B n, (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) ∧ (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) ∧ ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) := by
  intro B X hX u n
  exact exists_base B.sp.cm (π := X.piT u) (T := B.T u) (hX.T_prime u).ne_zero (hX.piT_norm u) (hX.piT_cop u) n

end GlobalTheory.Mem.Col2.BasePoint
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryDiagonalBasePointLevelPrimeStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_diagonal_basePoint_levelPrime : ∀ {B : Base} (X : PreX B.toPre), (B.primes X).Ok → ∀ (u : B.Word) (n : ℕ), ∃ k : GA B n, (∃ p : DecoF B.fields.E n ∅ ∅ ∅, PtOf k p ∧ p.deco.1.N = stdLat B.fields.E n) ∧ (∀ v : HeightOneSpectrum (𝓞 B.host.F), (B.T u : 𝓞 B.host.F) ∉ v.asIdeal → bc (prV (E := B.host.E) v) k = 1) ∧ ∀ (P : (B.primes X).vT u) (r j : Fin n), r.1 + 1 = n → HasRes P.1 (adAt B.host.F P.1 ((k⁻¹ : GA B n).1 r j)) (if j = r then Ideal.Quotient.mk P.1.asIdeal (B.fields.conjO (X.piT u)) else 0) := by
  first | exact @GlobalTheory.Mem.Col2.BasePoint.exists_kStd | exact GlobalTheory.Mem.Col2.BasePoint.exists_kStd | (intros; apply GlobalTheory.Mem.Col2.BasePoint.exists_kStd <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelTiedOfLevEx
open Formalism.BasicNotions GlobalTheory.Mem.HD

theorem GlobalTheory.Mem.HD.levelTied_of_levEx : ∀ D : D7, LevEx D → Formalism.L2.Host.LevelTied D :=
  fun D h => ⟨fun p => by
    have hq : Formalism.MainNotions.q0Av D = Formalism.MainNotions.AbsolutelyIrreducibleSpan.q0 D := rfl
    simpa [hq] using h p⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal

namespace GlobalTheory.IntNormFinExt

theorem mem_OL_iff_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (x : ↥K.1), x ∈ Loc.OL K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 :=
  fun l _ K x => GlobalTheory.EmbThroughCompletion.mem_OL_iff K x

end GlobalTheory.IntNormFinExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemFiniteExtPadicRingOfIntegersIffNormLeOneStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.L2.NT Formalism.L2.TwC GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial GlobalTheory.GalChar Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_finiteExtPadic_ringOfIntegers_iff_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (K : Loc.FinExt l) (x : ↥K.1), x ∈ Loc.OL K ↔ ‖(x : PadicAlgCl l)‖ ≤ 1 := by
  first | exact @GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one | exact GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one | (intros; apply GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsOfLocMv
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.TC.ChTw

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def LocMv (u : B.Word) (a : I.ι) (i : ℕ) (c : (I.stp u a i).Cl) (s : GA B (B.R.N i)) (κ : (I.stp u a i).G c.1) : Prop :=
  (I.stp u a i).gam c.1 κ = 1 ∧
    cosetIn ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)) = cosetIn ((I.stp u a i).rep c) ∧
    ∀ g : GA B (B.R.N i), PtOf g ((I.stp u a i).rep c).1.1 → PtOf (g * s) ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1

theorem reads_of_locMv (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ} {Ch : Type} {chOf : (I.stp u a i).Cl → Ch}
    {Lb : Ch → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)} {U : Ch → Subgroup (GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ}
    {y : (I.stp u a i).Cl → GA B (B.R.N i)} {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E}
    {k : Ch → GA B (B.R.N i)} (hR : I.Reads u a i chOf Lb U chi y st k) (c : (I.stp u a i).Cl) (x : GA B (B.R.N i))
    (κ : (I.stp u a i).G c.1) (h : LocMv I u a i c ((k (chOf c))⁻¹ * x * k (chOf c)) κ) :
    ∃ hx : x ∈ U (chOf c), ((chi (chOf c) ⟨x, hx⟩ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ : B.LLˣ) : B.LL) := by
  have hd : Disjoint (B.primes X).vGs (I.Q a) :=
    Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) (GlobalTheory.Mem.LevTwist.levOk_twists B X I hI).2.1
  have hp : PtOf (y c * k (chOf c)) ((I.stp u a i).rep c).1.1 :=
    IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  have e : y c * k (chOf c) * ((k (chOf c))⁻¹ * x * k (chOf c)) = y c * x * k (chOf c) := by group
  have hq := h.2.2 _ hp
  rw [e] at hq
  have hx : x ∈ U (chOf c) := (hR.lev c x _ hq).2 ⟨κ, h.1, rfl, h.2.1⟩
  exact ⟨hx, hR.chr c ⟨x, hx⟩ κ h.1 hq⟩

end GlobalTheory.Mem.Col2.TC.ChTw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevExOfOver
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Fld GlobalTheory.Mem.HD NumberField IsDedekindDomain
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.HD

private theorem levEx_of_levelPrimes_eq (D : D7) (S : Finset ℕ) (g : Fin 2 → ℕ) (a b c : ℕ) (hS : S = {g 0, g 1, a, b, c})
    (hlev : ∀ p, p ∈ D.host.levelPrimes ↔ p ∈ S ∨ ∃ u, p = (D.mem u).A.T)
    (hg : ∀ i, D.host.g i = g i) (ha : D.host.pde = a) (hb : D.host.pde' = b) (hc : q0Av D = c) : LevEx D := by
  intro p
  rw [hlev, hS]
  simp only [Finset.mem_insert, Finset.mem_singleton, hg, ha, hb, hc, Fin.exists_fin_two]
  tauto

theorem levEx_of_over : ∀ (D : D7) (P : PreCh) (Lv : LevCh P), Over D P Lv →
    P.H.levelPrimes = {P.H.g 0, P.H.g 1, P.H.pde, P.H.pde', DC.q0H P.H} → LevEx D ∧ ∀ N h, LevEx (setDiv D N h) := by
  intro D P Lv hO hlev
  obtain ⟨sp, hT, hY, hA, hV, hz, X, hX, rfl⟩ := hO
  refine (fun hD => ⟨hD, fun _ _ => hD⟩) ?_
  obtain ⟨B, C, W, V, S, Ns, G⟩ := X
  cases B
  dsimp only at hX
  subst hX
  refine levEx_of_levelPrimes_eq _ P.H.levelPrimes P.H.g P.H.pde P.H.pde' (DC.q0H P.H) hlev ?_ (fun _ => rfl) rfl rfl ?_
  · intro p
    have hT' := C.A_T
    show p ∈ P.H.levelPrimes ∪ Finset.univ.image Lv.T ↔ _
    rw [Finset.mem_union, Finset.mem_image]
    exact or_congr Iff.rfl
      ⟨fun ⟨u, _, hu⟩ => ⟨u, hu.symm.trans (hT' u).symm⟩, fun ⟨u, hu⟩ => ⟨u, Finset.mem_univ _, (hT' u).symm.trans hu.symm⟩⟩
  · unfold q0Av DC.q0H rPrAv DC.rPrH LevelStarExponents.condE
    rfl

end GlobalTheory.Mem.HD
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcPrVEqOneOfAdAt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.AdPlace

theorem bc_prV_eq_one_of_adAt : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (η : GL (Fin n) (AfE F E)), (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → ∀ i j, adAt F w (η.1 i j) = if i = j then 1 else 0) → bc (prV (E := E) v) η = 1 := by
  intro F E _ _ _ _ _ n v η h
  refine Units.ext (Matrix.ext fun i j => ?_)
  change prV (E := E) v (η.1 i j) = (1 : Matrix (Fin n) (Fin n) (E ⊗[F] v.adicCompletion F)) i j
  rw [Matrix.one_apply, ← sub_eq_zero]
  have e : (if i = j then (1 : E ⊗[F] v.adicCompletion F) else 0) = prV (E := E) v (if i = j then 1 else 0) := by
    split_ifs <;> simp
  rw [e, ← map_sub]
  refine ((GlobalTheory.Mem.Col2.AdComp.prV_zero_int_iff F E v _).1).2 fun w hw => ?_
  rw [map_sub, h w hw i j]
  split_ifs <;> simp

end GlobalTheory.Mem.Col2.AdPlace
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointDecoratedLatticeAllTwists
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointDecoratedLatticeAllTwists
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.PtTwist

open GlobalTheory.Mem.Col2.PtExist

theorem exists_ptOf_twists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (n : ℕ)
    (p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs I.SQ), ∃ g : GA B n, PtOf g p := by
  classical
  intro B X I hI u n p
  have hPr := (GlobalTheory.BasePrimes.primes_ok B X).1
  obtain ⟨hlev, hGQ, -⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I hI
  have hT0 : (B.primes X).piT u ≠ 0 := fun h => by
    have := hPr.piT_norm u
    rw [h, zero_mul] at this
    exact (hPr.T_prime u).ne_zero (Nat.cast_eq_zero.1 this.symm)

  have hTin : ∀ P ∈ (B.primes X).vT u, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := fun P hP => by
    have h1 : (B.primes X).piT u ∈ P.asIdeal := (mem_divs hT0 P).1 hP
    rw [← hPr.piT_norm u]
    exact Ideal.mul_mem_right _ _ h1

  have hcj : ∀ (P : HeightOneSpectrum (𝓞 B.fields.E)) (m : ℕ),
      ((m : ℕ) : 𝓞 B.fields.E) ∈ (conjPrime₂ P).asIdeal ↔ ((m : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := fun P m => by
    rw [mem_conjP, map_natCast]

  have hG : ∀ P ∈ (B.primes X).vGs, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP =>
    T_notMem_vGs hPr u ⟨P, hP⟩

  have hQ : ∀ P ∈ I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP h => by
    have hg := (GlobalTheory.Mem.LevTwist.good_of_mem hI hP).2
    have e := (ReadTwist.plc_under_eq_iff (F := B.host.F) P (hPr.T_prime u)).2 h
    refine hg.2.2 ?_
    rw [e]
    exact hI.T_mem u
  have hTG : Disjoint ((B.primes X).vT u) (B.primes X).vGs :=
    Finset.disjoint_left.2 fun P h1 h2 => hG P h2 (hTin P h1)
  have hTQ : Disjoint ((B.primes X).vT u) I.SQ :=
    Finset.disjoint_left.2 fun P h1 h2 => hQ P h2 (hTin P h1)
  have hout : ∀ P ∈ uSG (B.primes X).vGs I.SQ, (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∉ P.asIdeal := fun P hP => by
    rcases Finset.mem_union.1 hP with h | h
    exacts [hG P h, hQ P h]
  refine PtExist.exists_isPtOf_cm _ n _ _ _ p hTG hTQ hGQ fun P hP hP' => ?_
  rcases Finset.mem_union.1 hP with h1 | h1 <;> rcases Finset.mem_union.1 hP' with h2 | h2
  ·
    have a1 : (B.primes X).piT u ∈ P.asIdeal := (mem_divs hT0 P).1 h1
    have a2 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal := (mem_divs hT0 _).1 h2
    rw [mem_conjP] at a2
    obtain ⟨a, b, hab⟩ := hPr.piT_cop u
    have : (1 : 𝓞 B.fields.E) ∈ P.asIdeal := by
      rw [← hab]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ a1) (Ideal.mul_mem_left _ _ a2)
    exact P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 this)
  · exact hout _ h2 ((hcj P _).2 (hTin P h1))
  · exact hout P h1 ((hcj P _).1 (hTin _ h2))
  · exact hlev.split P h1 h2

end GlobalTheory.Mem.Col2.PtTwist
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdelicPointDecoratedLatticeAllTwistsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adelicPoint_decoratedLattice_allTwists : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (u : B.Word) (n : ℕ) (p : DecoF B.fields.E n ((B.primes X).vT u) (B.primes X).vGs I.SQ), ∃ g : GA B n, PtOf g p := by
  first | exact @GlobalTheory.Mem.Col2.PtTwist.exists_ptOf_twists | exact GlobalTheory.Mem.Col2.PtTwist.exists_ptOf_twists | (intros; apply GlobalTheory.Mem.Col2.PtTwist.exists_ptOf_twists <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsPtOfOfMem
noncomputable section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 2000000

namespace GlobalTheory.Mem.Col2.ChiFinTop

open GlobalTheory.Mem.Col2.PtExist

theorem exists_isPtOf_of_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : Formalism.BasicNotions.CMData F E) {n : ℕ} [NeZero n] {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} (hQ : Q = ∅)
    {g : GL (Fin n) (AfE F E)} (hg : g ∈ UAd hc n) : ∃ p : DecoF E n ST SG Q, IsPtOf hc g p := by
  classical
  obtain ⟨p, hd, -⟩ := GlobalTheory.Mem.ColAd.exists_near (ST := ST) (SG := SG) (Q := Q) hc 0 hg
  have hN : Formalism.UG.CS.globLat g (stdLat E n) = p.deco.1.N := congrArg Deco.N hd
  refine ⟨p, hg, hN ▸ carries_globLat g, fun P v hv i hi => ?_, fun P v hv i => ?_, fun P => absurd P.2 (by simp [hQ])⟩
  · have e : lastIdx n = i := Fin.ext (by simp [lastIdx]; omega)
    rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv), e]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)
  · rw [← hN] at hv
    rw [← hd]
    simp only [decoRaw]
    rw [if_pos (le_locP _ _ hv)]
    exact hasRes_redA _ ((mem_globLat g v).1 hv i)

end GlobalTheory.Mem.Col2.ChiFinTop

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemOfOrderDvd
noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Mem GlobalTheory.Mem.Fld GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.Mem.ValFin

theorem locInf_eq_one {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (w : InfinitePlace E) (x : (w.Completion)ˣ) : χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w x) = 1 := by
  let e := InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (e x) hn
  have hz' : (e.symm z) ^ n = x := by rw [← map_pow, hz, e.symm_apply_apply]
  have h0 : e.symm z ≠ 0 := fun h0 => x.ne_zero (by rw [← hz', h0, zero_pow hn.ne'])
  have hx : x = Units.mk0 _ h0 ^ n := Units.ext hz'.symm
  rw [hx, map_pow, map_pow]
  exact congrArg (fun χ : HChar E => χ.1 (ReciprocityTheory.Neutral.Bridge.HCFR.infIdele E w (Units.mk0 _ h0))) h

theorem inf_eq_one {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) {n : ℕ} (hn : 0 < n)
    (h : χ.OrderDvd n) (k : Eˣ) : χ.inf k = 1 := by
  show χ.1 (infDiag k) = 1
  simp [infDiag, map_prod, locInf_eq_one χ hn h]

theorem mem_of_orderDvd : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (χ : HChar E) (M : IntermediateField ℚ ℂ), (∃ n : ℕ, 0 < n ∧ χ.OrderDvd n) → valueField χ 0 ≤ M → ∀ x, ((χ.1 x : ℂˣ) : ℂ) ∈ M := by
  intro E _ _ _ χ M hn hM x
  obtain ⟨n, hn0, hord⟩ := hn
  have hinf : ∀ k : Eˣ, ((χ.inf k : ℂˣ) : ℂ) ∈ M := fun k => by
    rw [inf_eq_one χ hn0 hord k, Units.val_one]
    exact one_mem M
  rw [← GlobalTheory.Mem.ReadEx.map_finPartI hn0 hord x]
  exact GlobalTheory.T.heckeCharacter_finiteIdele_value_mem_field E χ M hM hinf (GlobalTheory.Mem.Chr.finPartI E x) fun w => by
    rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl

end GlobalTheory.Mem.ValFin

end
end
