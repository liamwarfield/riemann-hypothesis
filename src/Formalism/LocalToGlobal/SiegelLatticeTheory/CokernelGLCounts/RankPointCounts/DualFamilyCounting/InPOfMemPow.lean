module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiffProd
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlmostEverywhereSpherical
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.MMatEntryMeasurable
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.UnipBasis
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSLocSB
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsBasisOfPid

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.InPOfMemPow
open NumberField Module Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.GluingBases

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.HU

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem jι_eq' (t : 𝓞 F) :
    algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := by
  have e := UnimodularLocalization.algebraMap_smul_K (K := K) t (1 : K)
  rwa [Algebra.smul_def, mul_one, mul_one] at e

theorem inP_of_mem_pow {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {k : ℕ} {t : 𝓞 F} (ht : t ∈ 𝔭 ^ k) :
    InP 𝔭 k (algebraMap F K (t : F)) := by
  rw [← jι_eq']
  apply inP_jK
  rw [extP, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ht

theorem inP_vF {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {t : 𝓞 F} (ht : t ≠ 0) :
    InP 𝔭 (vF 𝔭 t) (algebraMap F K (t : F)) := by
  have := h𝔭.isPrime
  exact inP_of_mem_pow ((G1.mem_pow_iff h𝔭 ht _).2 le_rfl)

theorem mem_SP_of_inP {𝔭 : Ideal (𝓞 F)} [𝔭.IsPrime] {π s₀ : 𝓞 F} (hu : IsUnif0 𝔭 π s₀) {k : ℕ}
    {x : K} (hx : InP 𝔭 k x) : (algebraMap F K (π : F))⁻¹ ^ k * x ∈ SP K 𝔭 := by
  obtain ⟨s, hs, rfl⟩ := (mem_noncompactPart_iff hu k x).1 hx
  have h0 : algebraMap F K (π : F) ≠ 0 := by
    rw [← jι_eq']; exact jι_ne_zero hu.ne_zero
  rw [jι_eq', ← mul_assoc, ← mul_pow, inv_mul_cancel₀ h0, one_pow, one_mul]
  exact hs

theorem star_fix (hF : IsFixF K F) (x : F) : star (algebraMap F K x) = algebraMap F K x :=
  (hF _).2 ⟨x, rfl⟩

theorem star_inv_pow (hF : IsFixF K F) (x : F) (k : ℕ) :
    star ((algebraMap F K x)⁻¹ ^ k) = (algebraMap F K x)⁻¹ ^ k := by
  rw [← map_inv₀, ← map_pow]; exact star_fix hF _

theorem form_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (r : K) (x y : V) :
    h (r • x) y = star r * h x y := by
  rw [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]

theorem form_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : K) (x y : V) :
    h x (r • y) = r * h x y := by
  rw [map_smul, smul_eq_mul]

theorem form_smul_smul (h : V →ₗ⋆[K] V →ₗ[K] K) (r r' : K) (x y : V) :
    h (r • x) (r' • y) = star r * r' * h x y := by
  rw [form_smul_left, form_smul_right]; ring

end Formalism.L2.SG.Pf.GluingBases
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcXOmVSt
noncomputable section

namespace Formalism.L2.SG.Pf.NcX.OmVSt

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocVol Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  MeasureTheory NumberField IsDedekindDomain
open scoped TensorProduct

variable {D : D7} (X : HidaSetting D) (u' : D.what₂.Word) (ψ : AddChar (AF X.B.I.F) ℂ)

def scl (v : PlX X) : Fin (D.R.rS + 1 + D.R.rS) → Fv X.B.I.F v :=
  Fin.append (alp v D.R.rS) (fun b : Fin D.R.rS => (alp v D.R.rS b.castSucc)⁻¹)

def yTup (v : PlX X) : TupV (E := X.B.I.E) v X.B.I.n (D.R.rS + 1 + D.R.rS) :=
  fun i => sc (E := X.B.I.E) v (scl X v i) • ratTup (Fv X.B.I.F v) (tupH (frameOf X u')) i

def localGramMatrixFrame (v : PlX X) : Matrix (Fin (D.R.rS + 1 + D.R.rS)) (Fin (D.R.rS + 1 + D.R.rS)) (Fv X.B.I.F v ⊗[X.B.I.F] X.B.I.E) :=
  (gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v))

abbrev abelian₂ : Set (Fin X.B.I.n → X.B.I.E) := (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def OmVStd : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → StdHyp X.B.I.cm.sig X.B.I.J ψ

def OmVLat : Prop :=
  ∃ L : Submodule (𝓞 X.B.I.E) (Fin X.B.I.n → X.B.I.E), Submodule.IsLattice X.B.I.E L ∧ (L : Set (Fin X.B.I.n → X.B.I.E)) = abelian₂ X

def OmVSD : Prop := ∀ v : PlX X, IsSDLoc X.B.I.cm.sig X.B.I.J v (abelian₂ X)

def OmVUnram : Prop := ∀ v : PlX X, UnramAt (E := X.B.I.E) v

def OmVPrim : Prop := ∀ v : PlX X, IsPrim v (abelian₂ X) (yTup X u' v)

def OmVGram : Prop := ∀ v : PlX X, gramR (Fv X.B.I.F v) X.B.I.cm.sig X.B.I.J (yTup X u' v) = localGramMatrixFrame X u' v

def OmVDet : Prop :=
  ∀ v : PlX X, ¬ (((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal) →
    ∃ w ∈ OEv (E := X.B.I.E) v, (localGramMatrixFrame X u' v).det ∈ OEv (E := X.B.I.E) v ∧ (localGramMatrixFrame X u' v).det * w = 1

def OmVScale : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X,
    omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))} =
      omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v}

def OmVBadT : Prop :=
  IsCharAF X.B.I.F ψ → IsStdChar ψ → ∀ v : PlX X, ((Tw u' : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal →
    IsSDLoc X.B.I.cm.sig X.B.I.J v (abelian₂ X) → UnramAt (E := X.B.I.E) v → IsPrim v (abelian₂ X) (yTup X u' v) →
    omAt X.B.I.cm.sig X.B.I.J ψ v (localGramMatrixFrame X u' v)
        {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (abelian₂ X) v, Y = k • yTup X u' v} =
      ENNReal.ofReal (absV v (dV v) ^ ((X.B.I.n : ℝ) * (D.R.rS + 1 + D.R.rS : ℕ) - ((D.R.rS + 1 + D.R.rS : ℕ) : ℝ) ^ 2 / 2) *
        ∏ j ∈ Finset.Icc (X.B.I.n - (D.R.rS + 1 + D.R.rS)) X.B.I.n,
          (1 - (etaV (E := X.B.I.E) v : ℝ) ^ j * ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-(j : ℤ))))

def OmVLocU : Prop :=
  ∀ (v : PlX X) (a : ℕ) (Y : TupV (E := X.B.I.E) v X.B.I.n a),
    Formalism.L2.SG.Pf.NcLoc.OmLocU X.B.I.cm.sig X.B.I.J ψ v (abelian₂ X) a Y

end Formalism.L2.SG.Pf.NcX.OmVSt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcValDiffProd
noncomputable section

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

section General

variable (F : Type) [Field F] [NumberField F]

abbrev mDiff (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  (Associates.mk v.asIdeal).count (Associates.mk (differentIdeal ℤ (𝓞 F))).factors

lemma differentIdeal_ne_zero' : differentIdeal ℤ (𝓞 F) ≠ 0 := by
  exact differentIdeal_ne_bot

variable {F}

lemma pow_mDiff_dvd (v : HeightOneSpectrum (𝓞 F)) :
    v.asIdeal ^ mDiff F v ∣ differentIdeal ℤ (𝓞 F) := by
  have hD : Associates.mk (differentIdeal ℤ (𝓞 F)) ≠ 0 := Associates.mk_ne_zero.mpr (differentIdeal_ne_zero' F)
  have hirr : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  rw [← Associates.mk_dvd_mk, Associates.mk_pow]
  exact (Associates.prime_pow_dvd_iff_le hD hirr).mpr le_rfl

lemma not_pow_succ_mDiff_dvd (v : HeightOneSpectrum (𝓞 F)) :
    ¬ v.asIdeal ^ (mDiff F v + 1) ∣ differentIdeal ℤ (𝓞 F) := by
  have hD : Associates.mk (differentIdeal ℤ (𝓞 F)) ≠ 0 := Associates.mk_ne_zero.mpr (differentIdeal_ne_zero' F)
  have hirr : Irreducible (Associates.mk v.asIdeal) := Associates.irreducible_mk.mpr v.irreducible
  intro h
  rw [← Associates.mk_dvd_mk, Associates.mk_pow] at h
  have := (Associates.prime_pow_dvd_iff_le hD hirr).mp h
  exact Nat.lt_irrefl _ (Nat.lt_of_succ_le this)

lemma intValuation_le_of_mem_different (v : HeightOneSpectrum (𝓞 F)) {x : 𝓞 F}
    (hx : x ∈ differentIdeal ℤ (𝓞 F)) : v.intValuation x ≤ exp (-(mDiff F v : ℤ)) := by
  rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd]
  exact dvd_trans (pow_mDiff_dvd v) (Ideal.dvd_iff_le.mpr ((Ideal.span_singleton_le_iff_mem _).mpr hx))

lemma exists_mem_different_intValuation_eq (v : HeightOneSpectrum (𝓞 F)) :
    ∃ x ∈ differentIdeal ℤ (𝓞 F), v.intValuation x = exp (-(mDiff F v : ℤ)) := by
  have hnot := not_pow_succ_mDiff_dvd v
  rw [Ideal.dvd_iff_le, IsConcreteLE.not_le_iff_exists] at hnot
  obtain ⟨x, hxD, hxv⟩ := hnot
  refine ⟨x, hxD, le_antisymm (intValuation_le_of_mem_different v hxD) ?_⟩
  have h1 : ¬ v.intValuation x ≤ WithZero.exp (-((mDiff F v + 1 : ℕ) : ℤ)) := by
    rw [IsDedekindDomain.HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_iff_le,
      Ideal.span_singleton_le_iff_mem]
    exact hxv
  have hx0 : v.intValuation x ≠ 0 := by
    intro h0
    apply h1
    rw [h0]
    exact zero_le
  rw [← WithZero.exp_log hx0] at h1 ⊢
  rw [WithZero.exp_le_exp] at h1 ⊢
  push_cast at h1
  omega

lemma valued_algebraMap_coe (v : HeightOneSpectrum (𝓞 F)) (x : 𝓞 F) :
    Valued.v (algebraMap F (Fv F v) (x : F)) = v.intValuation x := by
  rw [← IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap (K := F)]
  exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (x : F)

lemma valued_dV (v : HeightOneSpectrum (𝓞 F)) : Valued.v (dV v) = exp (-(mDiff F v : ℤ)) := by
  obtain ⟨x, hxD, hxv⟩ := exists_mem_different_intValuation_eq v
  have hex : ∃ d, IsDiffVal v d := by
    refine ⟨algebraMap F (Fv F v) (x : F), ?_, ?_, x, hxD, rfl⟩
    · intro h0
      have := valued_algebraMap_coe v x
      rw [h0, map_zero, hxv] at this
      exact WithZero.exp_ne_zero this.symm
    · intro y hy
      rw [valued_algebraMap_coe, valued_algebraMap_coe, hxv]
      exact intValuation_le_of_mem_different v hy
  have hd : IsDiffVal v (dV v) := by
    unfold dV
    rw [dite_eq_left hex]
    exact hex.choose_spec
  obtain ⟨-, hle, y, hyD, hyv⟩ := hd
  apply le_antisymm
  · rw [← hyv, valued_algebraMap_coe]
    exact intValuation_le_of_mem_different v hyD
  · have := hle x hxD
    rwa [valued_algebraMap_coe, hxv] at this

lemma absV_of_valued_eq (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) (n : ℤ) (h : Valued.v x = exp n) :
    absV v x = ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ n := by
  have hx : Valued.v x ≠ 0 := by
    rw [h]
    exact WithZero.exp_ne_zero
  unfold absV
  rw [dite_eq_right hx]
  congr 1
  have hu : WithZero.unzero hx = Multiplicative.ofAdd n := by
    apply WithZero.coe_injective
    rw [WithZero.coe_unzero, h]
    rfl
  rw [hu, toAdd_ofAdd]

lemma absV_dV (v : HeightOneSpectrum (𝓞 F)) :
    absV v (dV v) = ((Ideal.absNorm (v.maxPowDividing (differentIdeal ℤ (𝓞 F))) : ℕ) : ℝ)⁻¹ := by
  rw [absV_of_valued_eq v _ _ (valued_dV v), IsDedekindDomain.HeightOneSpectrum.maxPowDividing, map_pow,
    zpow_neg, zpow_natCast, Nat.cast_pow]


variable (F) in
theorem hasProd_absV_dV :
    HasProd (fun v : HeightOneSpectrum (𝓞 F) => absV v (dV v)) (|(discr F : ℝ)|⁻¹) := by
  have hD := differentIdeal_ne_zero' F
  have hfin : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      v.maxPowDividing (differentIdeal ℤ (𝓞 F))).Finite := Ideal.hasFiniteMulSupport hD
  have hfac : ∏ v ∈ hfin.toFinset, v.maxPowDividing (differentIdeal ℤ (𝓞 F)) = differentIdeal ℤ (𝓞 F) := by
    rw [← finprod_eq_prod_of_mulSupport_subset _ (fun v hv => hfin.mem_toFinset.mpr hv)]
    exact Ideal.finprod_heightOneSpectrum_factorization hD
  have hone : ∀ v ∉ hfin.toFinset, absV v (dV v) = 1 := by
    intro v hv
    rw [absV_dV]
    have h1 : v.maxPowDividing (differentIdeal ℤ (𝓞 F)) = 1 := by
      by_contra hc
      exact hv (hfin.mem_toFinset.mpr hc)
    rw [h1, map_one]
    simp
  have hval : ∏ v ∈ hfin.toFinset, absV v (dV v) = |(discr F : ℝ)|⁻¹ := by
    rw [Finset.prod_congr rfl (fun v _ => absV_dV v), Finset.prod_inv_distrib, ← Nat.cast_prod, ← map_prod, hfac,
      NumberField.absNorm_differentIdeal F (𝓞 F), Nat.cast_natAbs, Int.cast_abs]
  have key : HasProd (fun v : HeightOneSpectrum (𝓞 F) => absV v (dV v)) (∏ v ∈ hfin.toFinset, absV v (dV v)) :=
    hasProd_prod_of_ne_finset_one hone
  rw [hval] at key
  exact key

end General

section Loc

variable {D : D7} (X : HidaSetting D)

theorem diffProd_holds : DiffProd X := by
  exact hasProd_absV_dV _

end Loc

end Formalism.L2.SG.Pf.NcVal
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcArith
noncomputable section

open Classical

namespace Formalism.L2.SG.Pf.NcVal

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.LocVol Formalism.L2.SG.MassDataConc Formalism.L2.SG.TypedSets Formalism.L2.SG.Sub Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def FieldDict {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word) : Prop :=
  |(NumberField.discr X.B.I.F : ℝ)| = |(NumberField.discr D.host.F : ℝ)| ∧
  Fintype.card (NumberField.InfinitePlace X.B.I.F) = Module.finrank ℚ D.host.F ∧
  (∀ i : ℕ, 2 ≤ i → HasProd (fun v : PlX X =>
      (1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ i / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ i)⁻¹)
      (Formalism.HermitianLattices.Ext.L3.lValEtaF D.host.E D.host.F i)) ∧
  HasProd (fun v : PlX X => if (((D.mem u).A.T : ℕ) : 𝓞 X.B.I.F) ∈ v.asIdeal then
      1 - ((etaV (E := X.B.I.E) v : ℤ) : ℝ) ^ D.R.k / ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ D.R.k else 1)
    (∏' 𝔭 : {𝔭 : Ideal (𝓞 D.host.F) // 𝔭.IsMaximal},
      (if (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ 𝔭.1 then
        1 - Formalism.HermitianLattices.Ext.L3.etaF D.host.E D.host.F 𝔭.1 ^ D.R.k * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(D.R.k : ℤ)) else 1)) ∧
  Formalism.HermitianLatticesTheory.vInv D.host.E = |(NumberField.discr D.host.F : ℝ)| ^ ((1 : ℝ) / Module.finrank ℚ D.host.F) / 2 ∧
  Formalism.HermitianLatticesTheory.fDeg D.host.E = Module.finrank ℚ D.host.F ∧
  X.B.I.n = D.R.r ∧
  (∀ p : TypX X, absV p.1 (dV p.1) = 1) ∧
  (∀ p : TypX X, aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u') = aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u)) ∧
  ∏ p : TypX X, (gAt X p.1 : ℝ) = ((Lat.gS D : ℕ) : ℝ) ^ Module.finrank ℚ D.host.F

def NcArith : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (hK : X.LevelSubgroupCharacter) (FdN FdN' : Set X.B.I.Ginf)
    (u u' : D.what₂.Word) (X0 : Fin (2 * D.R.rS + 2) → Fin X.B.I.n → X.B.I.E)
    (ψ : AddChar (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF X.B.I.F) ℂ)
    {τ Rw I H H₁ : Type} [Fintype I] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁] (T : Formalism.FourierDecayAlt.PB.Terms τ Rw I H H₁) (sd C Th : ℝ)
    {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)}
    {what₂ : Finset (Submodule (NumberField.RingOfIntegers D.host.E) (VS D).V)}
    (vR : Formalism.L2.SG.TermDef.Term D u u' F0 what₂ → ℝ) (Q : Formalism.L2.SG.PairVal.PairSys D u u' F0 what₂)
    (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep) (δ : ∀ p : PlF D, (D.s.atP p).Fp)
    (i0 i0' : ∀ _ : NumberField.InfinitePlace X.B.I.F, Fin D.R.k) (νq : X.B.I.Ginf → Measure X.B.I.Ginf) (a' : ℝ),
    0 < a' → IsRowReps D F0 what₂ →
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μK * a' =
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μH' *
        ∏' v : PlX X,
          (omAt X.B.I.cm.sig X.B.I.J ψ v
            ((gramE X.B.I.cm.sig X.B.I.J (tupH (frameOf X u'))).map (inclR (Fv X.B.I.F v)))
            {Y | ∃ k ∈ Kv X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) v,
              Y = k • ratTup (Fv X.B.I.F v) (tupH (frameOf X u'))}).toReal →
    Formalism.L2.SG.RealObj.DisintegrationConstant X u u' 1 * (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volH *
              (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN *
              (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).volN' =
      a' * 2 ^ (D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F)) *
        (Real.pi ^ D.R.k / (Nat.factorial (D.R.k - 1) : ℝ)) ^ Fintype.card (NumberField.InfinitePlace X.B.I.F) *
        ((Tw u : ℕ) : ℝ) ^ (-((D.R.k * Fintype.card (NumberField.InfinitePlace X.B.I.F) : ℕ) : ℤ)) *
        |(NumberField.discr X.B.I.F : ℝ)| ^
          (-(8 * (D.R.rS : ℝ) ^ 3 + 6 * (D.R.rS : ℝ) ^ 2 + 6 * D.R.k * (D.R.rS : ℝ) ^ 2 + D.R.rS) / 3) →
    IsCharAF X.B.I.F ψ → IsStdChar ψ → (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
    VolOrdV X u u' ψ → VolTypV X u u' ψ →
    (∀ p : TypX X,
      (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKnatp p /
          (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).μKp p =
        (gAt X p.1 : ℝ) ^ (-(((D.R.rS + 1) * (2 * D.R.k + 2 * D.R.rS + 1) : ℕ) : ℤ)) /
          aP (E := X.B.I.E) p.1 D.R.k X.B.I.n (Tw u)) →
    OmV X u' ψ → DiffProd X → Formalism.L2.SG.Pf.Cnt.RowsMass → FieldDict X u u' → ProdConv X u u' ψ →
    (bCF X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq).Pos →
    Formalism.L2.SG.Pf.NcAsm.NcValueC X hb hK FdN FdN' u u' X0 ψ T sd C Th vR Q M δ i0 i0' νq

end Formalism.L2.SG.Pf.NcVal
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FrameZZEqNegT
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting
open Matrix

noncomputable section

namespace Formalism.L2.SG.Pf.LsNc5

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {n : ℕ} (ε : Fin n → Bool)

private theorem hJ_eq_lemma (x y : Fin n → ℂ) :
    hJ ε x y = ∑ i, star (x i) * ((if ε i then 1 else -1) * y i) := by
  simp only [hJ, Formalism.REAL.Jm, dotProduct, mulVec_diagonal, Pi.star_apply]

theorem hJa (x y y' : Fin n → ℂ) : hJ ε x (y + y') = hJ ε x y + hJ ε x y' := by
  rw [hJ_eq_lemma, hJ_eq_lemma, hJ_eq_lemma, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply]
  ring

theorem hJs (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  rw [hJ_eq_lemma, hJ_eq_lemma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem hJsub (x y y' : Fin n → ℂ) : hJ ε x (y - y') = hJ ε x y - hJ ε x y' := by
  rw [hJ_eq_lemma, hJ_eq_lemma, hJ_eq_lemma, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply]
  ring

theorem hJswap (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  rw [hJ_eq_lemma, hJ_eq_lemma, star_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp only [star_mul', star_star, star_one, star_neg] <;> ring

theorem hJzr (x : Fin n → ℂ) : hJ ε x 0 = 0 := by
  rw [hJ_eq_lemma]
  simp

theorem hJzl (y : Fin n → ℂ) : hJ ε 0 y = 0 := by
  rw [hJ_eq_lemma]
  simp

theorem hJal (x x' y : Fin n → ℂ) : hJ ε (x + x') y = hJ ε x y + hJ ε x' y := by
  rw [hJ_eq_lemma, hJ_eq_lemma, hJ_eq_lemma, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.add_apply, star_add]
  ring

theorem hJsl (x y : Fin n → ℂ) (c : ℂ) : hJ ε (c • x) y = star c * hJ ε x y := by
  rw [hJ_eq_lemma, hJ_eq_lemma, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.smul_apply, smul_eq_mul, star_mul']
  ring

theorem hJsubl (x x' y : Fin n → ℂ) : hJ ε (x - x') y = hJ ε x y - hJ ε x' y := by
  rw [hJ_eq_lemma, hJ_eq_lemma, hJ_eq_lemma, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.sub_apply, star_sub]
  ring

theorem hJsumr {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε x (∑ i ∈ s, c i • y i) = ∑ i ∈ s, c i * hJ ε x (y i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hJzr]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hJa, hJs, ih]

theorem hJsuml {ι : Type*} (s : Finset ι) (x : Fin n → ℂ) (c : ι → ℂ) (y : ι → Fin n → ℂ) :
    hJ ε (∑ i ∈ s, c i • y i) x = ∑ i ∈ s, star (c i) * hJ ε (y i) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp [hJzl]
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, hJal, hJsl, ih]

theorem hJ_nondeg {d : Fin n → ℂ} (h : ∀ y, hJ ε y d = 0) : d = 0 := by
  funext i
  have h1 := h (Pi.single i 1)
  rw [hJ_eq_lemma, Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at h1
  simp only [Pi.single_eq_same, star_one, one_mul] at h1
  split_ifs at h1
  · simpa using h1
  · simpa using h1

theorem hJ_test {ι : Type*} (b : ι → Fin n → ℂ) (hs : Submodule.span ℂ (Set.range b) = ⊤)
    {x x' : Fin n → ℂ} (h : ∀ i, hJ ε (b i) x = hJ ε (b i) x') : x = x' := by
  have key : ∀ y, hJ ε y (x - x') = 0 := by
    intro y
    have hy : y ∈ Submodule.span ℂ (Set.range b) := by
      rw [hs]
      exact Submodule.mem_top
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, rfl⟩ := hz
      rw [hJsub, h i, sub_self]
    | zero => exact hJzl ε _
    | add a c _ _ ha hc => rw [hJal, ha, hc, add_zero]
    | smul c a _ ha => rw [hJsl, ha, mul_zero]
  exact sub_eq_zero.mp (hJ_nondeg ε key)

theorem span_perp {r : ℕ} (e : Fin r → Fin n → ℂ) (S : Set (Fin r)) (y : Fin n → ℂ)
    (hy : ∀ c ∈ S, hJ ε y (e c) = 0) {d : Fin n → ℂ} (hd : d ∈ Submodule.span ℂ (e '' S)) :
    hJ ε y d = 0 := by
  induction hd using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, hc, rfl⟩ := hz
    exact hy c hc
  | zero => exact hJzr ε y
  | add a c _ _ ha hc => rw [hJa, ha, hc, add_zero]
  | smul c a _ ha => rw [hJs, ha, mul_zero]

theorem span_recon {r : ℕ} (e f : Fin r → Fin n → ℂ) (S : Set (Fin r))
    (hfe : ∀ b c, hJ ε (f b) (e c) = if b = c then 1 else 0) {d : Fin n → ℂ}
    (hd : d ∈ Submodule.span ℂ (e '' S)) : d = ∑ c, hJ ε (f c) d • e c := by
  induction hd using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨c, _, rfl⟩ := hz
    simp only [hfe]
    simp [ite_smul]
  | zero => simp [hJzr]
  | add a c _ _ ha hc =>
    conv_lhs => rw [ha, hc]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hJa, add_smul]
  | smul c a _ ha =>
    conv_lhs => rw [ha]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hJs, smul_smul]

theorem mulVec_split (G : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : G *ᵥ x = x + (G - 1) *ᵥ x := by
  rw [sub_mulVec, one_mulVec]
  abel

end Gen

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F)

theorem fr_ee (a b : Fin D.R.rS) : hJ (X.B.I.ε v) (eV X v a) (eV X v b) = 0 := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_ee X a b
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [eV, eV, Formalism.L2.SG.Pf.hJ_rv_sc, h, map_zero]

theorem fr_ff (a b : Fin D.R.rS) : hJ (X.B.I.ε v) (fV X v a) (fV X v b) = 0 := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_ff X a b
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [fV, fV, Formalism.L2.SG.Pf.hJ_rv_sc, h, map_zero]

theorem fr_ef (a b : Fin D.R.rS) : hJ (X.B.I.ε v) (eV X v a) (fV X v b) = if a = b then 1 else 0 := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_ef X a b
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [eV, fV, Formalism.L2.SG.Pf.hJ_rv_sc, h]
  split_ifs <;> simp

theorem fr_fe (a b : Fin D.R.rS) : hJ (X.B.I.ε v) (fV X v a) (eV X v b) = if a = b then 1 else 0 := by
  rw [hJswap, fr_ef]
  by_cases h : a = b
  · subst h
    simp
  · simp [h, Ne.symm h]

theorem fr_ez (a : Fin D.R.rS) : hJ (X.B.I.ε v) (eV X v a) (zV X u v) = 0 := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_ez X u a
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [eV, zV, Formalism.L2.SG.Pf.hJ_rv_sc, h, map_zero]

theorem fr_fz (a : Fin D.R.rS) : hJ (X.B.I.ε v) (fV X v a) (zV X u v) = 0 := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_fz X u a
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [fV, zV, Formalism.L2.SG.Pf.hJ_rv_sc, h, map_zero]

theorem frame_z_z_eq_neg_t : hJ (X.B.I.ε v) (zV X u v) (zV X u v) = -(((D.mem u).A.T : ℕ) : ℂ) := by
  have h := Formalism.L2.SG.Pf.UnipB.hE_crd X (X.zu u) (X.zu u)
  unfold Formalism.L2.SG.Pf.UnipB.hE at h
  rw [zV, HidaSetting.zR, Formalism.L2.SG.Pf.hJ_rv_sc, h, X.zu_norm, map_neg, map_natCast, map_neg, map_natCast]

theorem fr_ew (a : Fin D.R.rS) (j : Fin D.R.k) : hJ (X.B.I.ε v) (eV X v a) (X.wfr u v j) = 0 :=
  ((X.wfr_perp u v j).1 a).1

theorem fr_fw (a : Fin D.R.rS) (j : Fin D.R.k) : hJ (X.B.I.ε v) (fV X v a) (X.wfr u v j) = 0 :=
  ((X.wfr_perp u v j).1 a).2

theorem fr_zw (j : Fin D.R.k) : hJ (X.B.I.ε v) (zV X u v) (X.wfr u v j) = 0 :=
  (X.wfr_perp u v j).2

theorem fr_ww (i j : Fin D.R.k) : hJ (X.B.I.ε v) (X.wfr u v i) (X.wfr u v j) = if i = j then 1 else 0 :=
  X.wfr_on u v i j

theorem fr_we (j : Fin D.R.k) (a : Fin D.R.rS) : hJ (X.B.I.ε v) (X.wfr u v j) (eV X v a) = 0 := by
  rw [hJswap, fr_ew, star_zero]

theorem fr_wf (j : Fin D.R.k) (a : Fin D.R.rS) : hJ (X.B.I.ε v) (X.wfr u v j) (fV X v a) = 0 := by
  rw [hJswap, fr_fw, star_zero]

theorem fr_wz (j : Fin D.R.k) : hJ (X.B.I.ε v) (X.wfr u v j) (zV X u v) = 0 := by
  rw [hJswap, fr_zw, star_zero]

theorem fr_ze (a : Fin D.R.rS) : hJ (X.B.I.ε v) (zV X u v) (eV X v a) = 0 := by
  rw [hJswap, fr_ez, star_zero]

theorem fr_zf (a : Fin D.R.rS) : hJ (X.B.I.ε v) (zV X u v) (fV X v a) = 0 := by
  rw [hJswap, fr_fz, star_zero]

def fam : Fin D.R.rS ⊕ (Fin D.R.rS ⊕ (Fin D.R.k ⊕ Unit)) → Fin X.B.I.n → ℂ :=
  Sum.elim (eV X v) (Sum.elim (fV X v) (Sum.elim (X.wfr u v) fun _ => zV X u v))

theorem T_ne : (((D.mem u).A.T : ℕ) : ℂ) ≠ 0 := by
  exact Nat.cast_ne_zero.mpr (D.mem u).A.T_prime.ne_zero

theorem fam_li : LinearIndependent ℂ (fam X u v) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have key : ∀ y, ∑ i, c i * hJ (X.B.I.ε v) y (fam X u v i) = 0 := by
    intro y
    rw [← hJsumr, hc, hJzr]
  rintro (a | a | j | ⟨⟩)
  · have h := key (fV X v a)
    simpa [Fintype.sum_sum_type, fam, fr_fe, fr_ff, fr_fw, fr_fz] using h
  · have h := key (eV X v a)
    simpa [Fintype.sum_sum_type, fam, fr_ee, fr_ef, fr_ew, fr_ez] using h
  · have h := key (X.wfr u v j)
    simpa [Fintype.sum_sum_type, fam, fr_we, fr_wf, fr_ww, fr_wz] using h
  · have h := key (zV X u v)
    simp [Fintype.sum_sum_type, fam, fr_ze, fr_zf, fr_zw, frame_z_z_eq_neg_t] at h
    rcases h with h | h
    · exact h
    · exact absurd h ((D.mem u).A.T_prime).ne_zero

theorem card_fam : Fintype.card (Fin D.R.rS ⊕ (Fin D.R.rS ⊕ (Fin D.R.k ⊕ Unit))) = X.B.I.n := by
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_unit]
  rw [X.n_eq]
  unfold Formalism.BasicNotions.Ranks.rS Formalism.BasicNotions.Ranks.r
  obtain ⟨j, hj⟩ := D.R.m_even
  have h2 := D.R.two_le_m
  omega

theorem fam_span : Submodule.span ℂ (Set.range (fam X u v)) = ⊤ := by
  exact (fam_li X u v).span_eq_top_of_card_eq_finrank (by rw [card_fam, Module.finrank_fin_fun])

end Formalism.L2.SG.Pf.LsNc5
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcSIntWittSt
noncomputable section

namespace Formalism.L2.SG.Pf.NcS.IntWittPf

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.LocVol NumberField IsDedekindDomain Filter Matrix
open scoped TensorProduct

def AlgWitt : Prop :=
  ∀ (S : Type) [CommRing S] (s : S →+* S) (O : Subring S), (∀ z, s (s z) = z) → (∀ z ∈ O, s z ∈ O) →
    ∀ (n : ℕ) (J J' : Matrix (Fin n) (Fin n) S), Formalism.UG.IsHerm s J → J' * J = 1 →
    (∀ i j, J i j ∈ O) → (∀ i j, J' i j ∈ O) →
    ∀ (a : ℕ) (β β' : Fin a → S), (∀ i, β i ∈ O) → (∀ i, β' i ∈ O) → (∀ i, β i * β' i = 1) →
    (∀ i, ∀ t ∈ O, ∃ lam ∈ O, lam * s lam = 1 ∧ ∃ c' ∈ O, (β i - s lam * t) * c' = 1) →
    ∀ (x y : Fin a → Fin n → S), (∀ i k, x i k ∈ O) → (∀ i k, y i k ∈ O) →
    (∀ i j, Formalism.UG.hform s J (x i) (x j) = if i = j then β i else 0) →
    (∀ i j, Formalism.UG.hform s J (y i) (y j) = if i = j then β i else 0) →
    ∃ g : GL (Fin n) S, g ∈ Formalism.UG.UJ s J ∧ (∀ i j, (g : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      (∀ i j, ((g⁻¹ : GL (Fin n) S) : Matrix (Fin n) (Fin n) S) i j ∈ O) ∧
      ∀ i, (g : Matrix (Fin n) (Fin n) S) *ᵥ y i = x i

def HermDiag : Prop :=
  ∀ (K : Type) [Field K] (σ : K →+* K), (∀ z, σ (σ z) = z) → (2 : K) ≠ 0 →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) K), Formalism.UG.IsHerm σ J →
    ∀ (a : ℕ) (X0 : Fin a → Fin n → K),
    (Matrix.of fun i j => Formalism.UG.hform σ J (X0 i) (X0 j)).det ≠ 0 →
    ∃ P Q : Matrix (Fin a) (Fin a) K, Q * P = 1 ∧
      (∀ i j, i ≠ j → Formalism.UG.hform σ J (∑ l, P i l • X0 l) (∑ l, P j l • X0 l) = 0) ∧
      ∀ i, Formalism.UG.hform σ J (∑ l, P i l • X0 l) (∑ l, P i l • X0 l) ≠ 0

def LamAE : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → ∀ δ : E, σ δ = δ → δ ≠ 0 →
    ∀ᶠ v : HeightOneSpectrum (𝓞 F) in cofinite, ∀ t ∈ OEv (E := E) v,
      ∃ lam ∈ OEv (E := E) v, lam * sigR (Fv F v) σ lam = 1 ∧
        ∃ c' ∈ OEv (E := E) v, (inclR (Fv F v) δ - sigR (Fv F v) σ lam * t) * c' = 1

end Formalism.L2.SG.Pf.NcS.IntWittPf
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GlueInlInl
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.GluedFormOrthogonality

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.L2.SG.Pf.GluingBases

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem form_U_orth {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {u z : V} (hu : u ∈ U)
    (hz : z ∈ orthK h U) : h u z = 0 := by
  have hz' : z ∈ ⨅ w ∈ U, LinearMap.ker (h w) := hz
  simp only [Submodule.mem_iInf, LinearMap.mem_ker] at hz'
  exact hz' u hu

theorem form_orth_U {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V} {u z : V}
    (hu : u ∈ U) (hz : z ∈ orthK h U) : h z u = 0 :=
  hs.eq_iff.1 (form_U_orth hu hz)

theorem glue_inl_inl {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {U : Submodule K V}
    {𝔭 : Ideal (𝓞 F)} {n m : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F} {π : 𝓞 F} {w : Fin m → V}
    {τ : Fin n → Fin m} (hbU : ∀ i, b i ∈ U) (hbo : ∀ i j, i ≠ j → h (b i) (b j) = 0)
    (hwW : ∀ j, w j ∈ orthK h U) (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0)
    (hτ : ∀ i k, vF 𝔭 (a i) ≠ 0 → vF 𝔭 (a k) ≠ 0 → τ i = τ k → i = k) {i i' : Fin n} (hii : i ≠ i') :
    h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (glueFam K 𝔭 b a π w τ (Sum.inl i')) = 0 := by
  simp only [glueFam, Sum.elim_inl]
  split_ifs with h1 h2 h2
  · exact hbo _ _ hii
  · simp only [map_smulₛₗ, map_smul, map_add (f := _), LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_U_orth (hbU i) (hwW _)]
  · simp only [map_smulₛₗ, map_smul, map_add (f := _), LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_orth_U hs (hbU i') (hwW _)]
  · have hτ' : τ i ≠ τ i' := fun e => hii (hτ i i' h1 h2 e)
    simp only [map_smulₛₗ, map_smul, map_add (f := _), LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, hbo _ _ hii, form_U_orth (hbU i) (hwW _),
      form_orth_U hs (hbU i') (hwW _), hwo _ _ hτ']

theorem glue_inl_w {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    {𝔭 : Ideal (𝓞 F)} {n m : ℕ} {b : Fin n → V} {a : Fin n → 𝓞 F} {π : 𝓞 F} {w : Fin m → V}
    {τ : Fin n → Fin m} (hbU : ∀ i, b i ∈ U) (hwW : ∀ j, w j ∈ orthK h U)
    (hwo : ∀ j k, j ≠ k → h (w j) (w k) = 0) {i : Fin n} {j : Fin m}
    (hj : vF 𝔭 (a i) ≠ 0 → τ i ≠ j) :
    h (glueFam K 𝔭 b a π w τ (Sum.inl i)) (w j) = 0 := by
  simp only [glueFam, Sum.elim_inl]
  split_ifs with h1
  · exact form_U_orth (hbU i) (hwW j)
  · simp only [map_smulₛₗ, map_smul, map_add (f := _), LinearMap.add_apply, LinearMap.smul_apply, smul_zero, add_zero, zero_add, smul_eq_mul, mul_zero, form_U_orth (hbU i) (hwW j), hwo _ _ (hj h1)]

end Formalism.L2.SG.Pf.GluedFormOrthogonality
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SummandLocalization
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt Formalism.HermitianLattices.Ext.L3.LocalSpans

theorem summand_localization : SummandLoc := by
  rintro K F V _ _ _ _ _ _ _ _ _ _ X 𝔭 h𝔭 Λ ⟨L, hL, rfl⟩
  let W := Submodule.span K (L : Set V)
  let i := W.subtype.restrictScalars (𝓞 K)
  let L' := L.comap i
  have hmap : L'.map i = L := by
    apply Submodule.map_comap_eq_self
    change L ≤ LinearMap.range (W.restrictScalars (𝓞 K)).subtype
    rw [Submodule.range_subtype]
    exact fun _ hx => Submodule.subset_span hx
  have hfull : Submodule.IsFullLattice K L' := by
    have hfg : L'.FG := Submodule.fg_of_fg_map_injective i Subtype.val_injective
      (hmap.symm ▸ hL.fg)
    letI : Submodule.IsLattice K L' := Submodule.IsLattice.of_fg K hfg
    refine ⟨?_⟩
    apply Submodule.map_injective_of_injective (f := W.subtype) Subtype.val_injective
    have himage : W.subtype '' (L' : Set W) = (L : Set V) := by
      rw [← hmap, Submodule.map_coe]
      rfl
    rw [Submodule.map_span, himage, Submodule.map_top, Submodule.range_subtype]
  let X' := X.comap W.subtype
  let Lloc := UpperTheory.Reformulated.B.SummandLocalization.locF 𝔭 L'
  obtain ⟨p, hpX, hpId, hpL⟩ :=
    UpperTheory.Reformulated.B.SummandLocalization.summand_localization
      K F W X' 𝔭 h𝔭 Lloc ⟨L', hfull, rfl⟩
  let N := (LinearMap.ker p).map W.subtype
  have hNX : Disjoint N X := by
    rw [Submodule.disjoint_def]
    rintro _ ⟨w, hw, rfl⟩ hx
    have hzero : p w = 0 := hw
    rw [hpId w hx] at hzero
    exact congrArg Subtype.val hzero
  obtain ⟨Y, hNY, hYX⟩ := hNX.exists_isCompl
  let π := X.projection Y hYX.symm
  have hπ (w : W) : π w = (p w : V) := by
    have hdiff : (w : V) - (p w : V) ∈ Y := hNY ⟨w - p w, by
      change p (w - p w) = 0
      rw [map_sub, hpId _ (hpX w), sub_self], rfl⟩
    have he := Submodule.projection_apply_of_mem_right hYX.symm hdiff
    change π ((w : V) - (p w : V)) = 0 at he
    have hp : (p w : V) ∈ X := hpX w
    have hproj : π (p w : V) = (p w : V) :=
      Submodule.projection_apply_of_mem_left hYX.symm hp
    rwa [map_sub, hproj, sub_eq_zero] at he
  refine ⟨π, Submodule.projection_apply_mem hYX.symm,
    fun _ hx => Submodule.projection_apply_of_mem_left hYX.symm hx, ?_⟩
  letI := h𝔭.isPrime
  intro y hy
  obtain ⟨t, ht, hty⟩ := (LocalSpans.mem_locF 𝔭 L y).1 hy
  have ht0 : t ≠ 0 := fun ht0 => ht (ht0 ▸ 𝔭.zero_mem)
  let a := algebraMap (𝓞 F) (𝓞 K) t
  have ha : algebraMap (𝓞 K) K a ≠ 0 := by
    intro h
    apply ht0
    apply RingOfIntegers.algebraMap.injective F K
    apply (RingOfIntegers.coe_injective)
    simpa [a] using h
  have hyW : y ∈ W := by
    have hs : algebraMap (𝓞 K) K a • y ∈ W := by
      rw [algebraMap_smul]
      exact Submodule.subset_span hty
    have h := W.smul_mem (algebraMap (𝓞 K) K a)⁻¹ hs
    rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at h
  let w : W := ⟨y, hyW⟩
  have hwL : w ∈ Lloc := (LocalSpans.mem_locF 𝔭 L' w).2 ⟨t, ht, hty⟩
  rw [show y = (w : V) from rfl, hπ w]
  obtain ⟨u, hu, hpu⟩ := (LocalSpans.mem_locF 𝔭 L' (p w)).1 (hpL w hwL)
  exact (LocalSpans.mem_locF 𝔭 L (p w : V)).2 ⟨u, hu, hpu⟩

end Formalism.L2.SG.Pf.G6
end
end
