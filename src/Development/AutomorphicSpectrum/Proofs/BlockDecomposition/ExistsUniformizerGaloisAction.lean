module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ValuationLtOneOfEq
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsTamagawaMeasureNormalization
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.SplitSatPre
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ColJoinColLColR
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.TwistStripLimits.BlockTypes
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.StableEigenspaces.InterpolationL2Bound
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.ProperRatH
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypOneZeroZero
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesConvergent
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeightContinuousPosStatement

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisAction
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

namespace GlobalTheory.CompanionTheory.LTHodge.UnitAct

section Ring

variable {l : ℕ} [Fact l.Prime] {K : FinExt l}
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [Algebra F (Om l)] [ValuativeExtension F (Om l)]

theorem valuation_le_one_iff (x : F) :
    valuation F x ≤ 1 ↔ ‖algebraMap F (Om l) x‖ ≤ 1 := by
  rw [← map_one (valuation F), ← (valuation F).vle_iff_le, ← ValuativeExtension.vle_iff_vle (B := Om l),
    GroundTheory.PAdicHodge.CyclNorms.vle_iff_norm_le, map_one, norm_one]

theorem exists_ringEquiv (hR : Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l))) :
    ∃ ρ : 𝒪[F] ≃+* ↥(OL K), ∀ a : 𝒪[F],
      (((ρ a : ↥(OL K)) : ↥K.1) : Om l) = algebraMap F (Om l) (a : F) := by
  have hmem : ∀ a : 𝒪[F], algebraMap F (Om l) (a : F) ∈ K.1 := fun a => by
    have h : algebraMap F (Om l) (a : F) ∈ (K.1 : Set (Om l)) := hR ▸ ⟨_, rfl⟩
    exact h
  have hO : ∀ a : 𝒪[F], (⟨_, hmem a⟩ : ↥K.1) ∈ OL K := fun a =>
    (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mpr ((valuation_le_one_iff (a : F)).mp a.2)
  let f : 𝒪[F] →+* ↥(OL K) :=
    { toFun := fun a => ⟨⟨_, hmem a⟩, hO a⟩
      map_one' := Subtype.ext (Subtype.ext (by simp))
      map_mul' := fun a b => Subtype.ext (Subtype.ext (by simp))
      map_zero' := Subtype.ext (Subtype.ext (by simp))
      map_add' := fun a b => Subtype.ext (Subtype.ext (by simp)) }
  have hinj : Function.Injective f := fun a b hab => by
    have h : algebraMap F (Om l) (a : F) = algebraMap F (Om l) (b : F) :=
      congrArg (fun c : ↥(OL K) => ((c : ↥K.1) : Om l)) hab
    exact Subtype.ext ((algebraMap F (Om l)).injective h)
  have hsurj : Function.Surjective f := fun b => by
    have hb : ((b : ↥K.1) : Om l) ∈ (K.1 : Set (Om l)) := (b : ↥K.1).2
    rw [← hR] at hb
    obtain ⟨y, hy⟩ := hb
    have hn : ‖algebraMap F (Om l) y‖ ≤ 1 := by
      rw [hy]
      exact (GlobalTheory.IntNormFinExt.mem_OL_iff_norm_le_one l K _).mp b.2
    exact ⟨⟨y, (valuation_le_one_iff y).mpr hn⟩, Subtype.ext (Subtype.ext hy)⟩
  exact ⟨RingEquiv.ofBijective f ⟨hinj, hsurj⟩, fun a => rfl⟩

theorem card_quot (ρ : 𝒪[F] ≃+* ↥(OL K)) {π : 𝒪[F]} (hπ : Irreducible π) :
    Nat.card (↥(OL K) ⧸ Ideal.span {ρ π}) = Nat.card 𝓀[F] := by
  have e1 : (𝒪[F] ⧸ Ideal.span {π}) ≃ (↥(OL K) ⧸ Ideal.span {ρ π}) :=
    (Ideal.quotientEquiv (Ideal.span {π}) (Ideal.span {ρ π}) ρ
      (by rw [Ideal.map_span, Set.image_singleton]; simp)).toEquiv
  have e2 : 𝓀[F] ≃ (𝒪[F] ⧸ Ideal.span {π}) :=
    (Ideal.quotEquivOfEq hπ.maximalIdeal_eq).toEquiv
  exact Nat.card_congr (e2.trans e1).symm

theorem map_ltPoly (ρ : 𝒪[F] ≃+* ↥(OL K)) {π : 𝒪[F]} (hπ : Irreducible π) :
    PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F]) = ltSeries (ρ π) := by
  rw [ltSeries, card_quot ρ hπ, FormalGroup.ltPoly]
  simp

end Ring

theorem main : ∀ {l : ℕ} [Fact l.Prime] {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ}, IsLTChar K χ →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [Algebra.IsAlgebraic F (Om l)],
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) →
    ∃ (π : 𝒪[F]) (hπ : Irreducible π), ∀ (g : Om l ≃ₐ[F] Om l) (g' : ↥(GK K)), (∀ y, g y = (g' : GQ l) y) →
      ∃ u : 𝒪[F]ˣ, algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∧
        ∀ n, ∀ x ∈ lubinTateTorsion (Om l) (hπ := hπ) (isLubinTateSeries_ltPoly π) n,
          lubinTateGalPointMap (hπ := hπ) (isLubinTateSeries_ltPoly π) g x = (u : 𝒪[F]) • x := by
  intro l _ K χ hχ F _ _ _ _ _ _ _ hR
  obtain ⟨πK, z, hπK, h0, h1, hs, hch⟩ := hχ
  obtain ⟨ρ, hρ⟩ := exists_ringEquiv (K := K) (F := F) hR
  have hρπ : ρ (ρ.symm πK) = πK := ρ.apply_symm_apply πK
  obtain ⟨π, hπdef⟩ : ∃ π : 𝒪[F], π = ρ.symm πK := ⟨_, rfl⟩
  rw [← hπdef] at hρπ
  have hπ : Irreducible π := hπdef ▸ (MulEquiv.irreducible_iff ρ.symm).mpr hπK
  have hf := isLubinTateSeries_ltPoly π
  have hcard : Nat.card (↥(OL K) ⧸ Ideal.span {πK}) = Nat.card 𝓀[F] := by
    have h := card_quot ρ hπ
    rwa [hρπ] at h
  have hcoe : ((πK : ↥K.1) : Om l) = algebraMap F (Om l) (π : F) := by
    rw [← hρ π, hρπ]
  have hs' : ∀ n, algebraMap F (Om l) (π : F) * z (n + 1) + z (n + 1) ^ Nat.card 𝓀[F] = z n :=
    fun n => by
      rw [← hcoe, ← hcard, add_comm]
      exact hs n
  have hv : ∀ n, valuation (Om l) (z n) < 1 := by
    intro n
    induction n with
    | zero => simp [h0]
    | succ n ih => exact CharEx.valuation_lt_one_of_eq hπ ih (hs' n)
  let Z : ℕ → IdealPoint (Om l) (lubinTateFormalGroup hπ hf) := fun n => IdealPoint.mk (z n) (hv n)
  have heval : ∀ (a : 𝒪[F]) (h : ↥(GK K)),
      (((ρ a : ↥(OL K)) : ↥K.1)) = ((χ h : (↥K.1)ˣ) : ↥K.1) →
      ∀ n, (a • Z n).val = (h : GQ l) (z n) := by
    intro a h ha n
    let Φ : PowerSeries 𝒪[F] := (lubinTateHom hπ hf hf a).toPowerSeries
    let ψ : PowerSeries ↥(OL K) := PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) Φ
    have hΦ0 : PowerSeries.constantCoeff Φ = 0 := (lubinTateHom hπ hf hf a).constantCoeff_eq_zero'
    have hψ0 : PowerSeries.constantCoeff ψ = 0 := by
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
        PowerSeries.coeff_zero_eq_constantCoeff_apply, hΦ0, map_zero]
    have hψ1 : ((PowerSeries.coeff 1 ψ : ↥(OL K)) : ↥K.1) = ((χ h : (↥K.1)ˣ) : ↥K.1) := by
      rw [PowerSeries.coeff_map, coeff_one_lubinTateHom]
      exact ha
    have hF0 : PowerSeries.constantCoeff (ltPoly π : PowerSeries 𝒪[F]) = 0 :=
      hf.constantCoeff_eq_zero
    have hsub : PowerSeries.subst ψ (ltSeries πK) = PowerSeries.subst (ltSeries πK) ψ := by
      have h2 := congrArg (MvPowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)))
        (subst_lubinTateHom hπ hf hf a)
      rw [PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hΦ0),
        PowerSeries.map_subst (PowerSeries.HasSubst.of_constantCoeff_zero hF0)] at h2
      change PowerSeries.subst ψ (PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F])) =
        PowerSeries.subst (PowerSeries.map (ρ : 𝒪[F] →+* ↥(OL K)) (ltPoly π : PowerSeries 𝒪[F])) ψ at h2
      rwa [map_ltPoly ρ hπ, hρπ] at h2
    have hsum := hch h ψ hψ0 hψ1 hsub n
    have hsum2 := CharEx.hasSum_coeff_mul_pow (K := F) Φ (hv n)
    rw [lubinTate_smul_val]
    refine hsum2.unique ?_
    convert hsum using 2 with k
    simp only [ψ, PowerSeries.coeff_map]
    rw [← hρ]
    rfl
  have hZ0 : Z 0 = 0 := IdealPoint.ext h0
  have hZ1 : Z 1 ≠ 0 := fun h => h1 (congrArg IdealPoint.val h)
  have hstep : ∀ n, π • Z (n + 1) = Z n := fun n => IdealPoint.ext (by
    rw [lubinTate_uniformizer_smul_val]
    change psEval ((ltPoly π : Polynomial 𝒪[F]) : PowerSeries 𝒪[F]) (fun _ => z (n + 1)) = z n
    rw [psEval_polynomial, aeval_ltPoly]
    exact hs' n)
  have hpow : ∀ n, π ^ n • Z (n + 1) = Z 1 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ, mul_smul, hstep, ih]
  have hunit : ∀ (a : 𝒪[F]) (h : ↥(GK K)),
      (((ρ a : ↥(OL K)) : ↥K.1)) = ((χ h : (↥K.1)ˣ) : ↥K.1) → IsUnit a := by
    intro a h ha
    by_contra hnu
    have hm := (IsLocalRing.mem_maximalIdeal a).mpr hnu
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton'] at hm
    obtain ⟨b, rfl⟩ := hm
    have h2 : (b * π) • Z 1 = 0 := by rw [mul_smul, hstep, hZ0, smul_zero]
    have h3 := heval _ h ha 1
    rw [h2] at h3
    exact h1 ((map_eq_zero_iff _ (h : GQ l).injective).mp h3.symm)
  refine ⟨π, hπ, fun g g' hg => ?_⟩
  obtain ⟨u, hu⟩ : ∃ u : 𝒪[F]ˣ,
      algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) := by
    have hy : (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∈ (K.1 : Set (Om l)) :=
      ((χ g' : (↥K.1)ˣ) : ↥K.1).2
    rw [← hR] at hy
    obtain ⟨y, hy⟩ := hy
    have hy0 : y ≠ 0 := by
      rintro rfl
      rw [map_zero] at hy
      exact (χ g').ne_zero (Subtype.ext hy.symm)
    rcases le_total (valuation F y) 1 with hle | hle
    · obtain ⟨w, hw⟩ := hunit ⟨y, hle⟩ g' (Subtype.ext (by rw [hρ]; exact hy))
      exact ⟨w, by rw [hw]; exact hy⟩
    · have hle' : valuation F y⁻¹ ≤ 1 := by
        rw [map_inv₀]
        exact inv_le_one_of_one_le₀ hle
      have hinv : (((χ (g'⁻¹) : (↥K.1)ˣ) : ↥K.1) : Om l) = algebraMap F (Om l) y⁻¹ := by
        rw [map_inv, map_inv₀, hy, Units.val_inv_eq_inv_val, IntermediateField.coe_inv]
      obtain ⟨w, hw⟩ := hunit ⟨y⁻¹, hle'⟩ g'⁻¹ (Subtype.ext (by rw [hρ, hinv]))
      refine ⟨w⁻¹, ?_⟩
      have hw2 : ((w : 𝒪[F]) : F) = y⁻¹ := by rw [hw]
      have hw3 : (((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) : F) * ((w : 𝒪[F]) : F) = 1 := by
        have h5 : ((w⁻¹ : 𝒪[F]ˣ) : 𝒪[F]) * (w : 𝒪[F]) = 1 := Units.inv_mul w
        exact congrArg Subtype.val h5
      rw [hw2] at hw3
      rw [← hy, (eq_of_mul_inv_eq_one hw3)]
  refine ⟨u, hu, fun n x hx => ?_⟩
  have hgZ : lubinTateGalPointMap (hπ := hπ) hf g (Z (n + 1)) = (u : 𝒪[F]) • Z (n + 1) :=
    IdealPoint.ext (by
      rw [lubinTateGalPointMap_val, heval (u : 𝒪[F]) g' (Subtype.ext (by rw [hρ]; exact hu))]
      exact hg _)
  have hZt : Z (n + 1) ∈ lubinTateTorsion (Om l) (hπ := hπ) hf (n + 1) :=
    CharEx.mem_torsion hπ h0 hs' (n + 1) _ rfl
  have hZn : Z (n + 1) ∉ lubinTateTorsion (Om l) (hπ := hπ) hf (n + 1 - 1) := by
    rw [Nat.add_sub_cancel, mem_lubinTateTorsion, hpow]
    exact hZ1
  obtain ⟨-, hgen⟩ := primitive_spec hπ hf hZt hZn
  obtain ⟨a, rfl⟩ := hgen x (lubinTateTorsion_mono hπ hf n.le_succ hx)
  rw [map_smul, hgZ, smul_smul, smul_smul, mul_comm]

end GlobalTheory.CompanionTheory.LTHodge.UnitAct
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniformizerGaloisActionStatement
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge
open scoped Classical
open ValuativeRel GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open scoped GroundTheory.PAdicHodge.CyclNorms

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_uniformizer_galois_action : ∀ {l : ℕ} [Fact l.Prime] {K : FinExt l} {χ : ↥(GK K) →* (↥K.1)ˣ}, IsLTChar K χ →
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    [Algebra F (Om l)] [ValuativeExtension F (Om l)] [Algebra.IsAlgebraic F (Om l)],
    Set.range (algebraMap F (Om l)) = (K.1 : Set (Om l)) →
    ∃ (π : 𝒪[F]) (hπ : Irreducible π), ∀ (g : Om l ≃ₐ[F] Om l) (g' : ↥(GK K)), (∀ y, g y = (g' : GQ l) y) →
      ∃ u : 𝒪[F]ˣ, algebraMap F (Om l) ((u : 𝒪[F]) : F) = (((χ g' : (↥K.1)ˣ) : ↥K.1) : Om l) ∧
        ∀ n, ∀ x ∈ lubinTateTorsion (Om l) (hπ := hπ) (isLubinTateSeries_ltPoly π) n,
          lubinTateGalPointMap (hπ := hπ) (isLubinTateSeries_ltPoly π) g x = (u : 𝒪[F]) • x := by
  first | exact @GlobalTheory.CompanionTheory.LTHodge.UnitAct.main | exact GlobalTheory.CompanionTheory.LTHodge.UnitAct.main | (intros; apply GlobalTheory.CompanionTheory.LTHodge.UnitAct.main <;> assumption)
end
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AuxiliaryCuspLemma
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AuxiliaryCuspLemma
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.Clozel

theorem exists_twist_isNormalised : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ π : CuspSub E a, (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) →
    ∃ s : ℂ, GlobalTheory.DiscSpec.IsNormalised (π.twist (GlobalTheory.CuspRep.Model.absC E s)) := by
  intro E _ _ _ a ha π hm
  choose m hm using hm
  have hN : (Fintype.card (E →+* ℂ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  refine ⟨-(∑ τ, (m τ).sum) / (a * Fintype.card (E →+* ℂ)), ?_⟩
  set s : ℂ := -(∑ τ, (m τ).sum) / (a * Fintype.card (E →+* ℂ)) with hs
  intro φ hφ t g
  have hsum : ∀ τ : E →+* ℂ, (∑ i : Fin a, Eop τ i i) φ = ((m τ).sum + a * s) • φ := fun τ => by
    have h1 := (hm τ).twist (GlobalTheory.CuspRep.Model.absC E s)
    rw [GlobalTheory.CuspRep.Model.expo_absC] at h1
    rw [GlobalTheory.T.trace_operator_eigenvalue_sum E a _ τ _ h1 φ hφ, Multiset.sum_map_add]
    simp [(hm τ).1]
  have hc : ∑ τ : E →+* ℂ, ((m τ).sum + a * s) = 0 := by
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hs]
    field_simp
    ring
  have hlie : lie E a (oneL E a) φ = (0 : ℂ) • φ := by
    rw [GlobalTheory.T.lie_central_element_trace E a, LinearMap.sum_apply, Finset.sum_congr rfl fun τ _ => hsum τ, ← Finset.sum_smul, hc]
  simpa using GlobalTheory.T.central_eigen_exponential E a φ 0 hlie t g

end GlobalTheory.CompanionTheory.Clozel
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AuxiliaryCuspLemmaStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.aux_statement_20 : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ π : CuspSub E a, (∀ τ : E →+* ℂ, ∃ m, π.HasInfChar τ m) → ∃ s : ℂ, GlobalTheory.DiscSpec.IsNormalised (π.twist (GlobalTheory.CuspRep.Model.absC E s)) := by
  first | exact @GlobalTheory.CompanionTheory.Clozel.exists_twist_isNormalised | exact GlobalTheory.CompanionTheory.Clozel.exists_twist_isNormalised | (intros; apply GlobalTheory.CompanionTheory.Clozel.exists_twist_isNormalised <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HasSatakeOfIsSatVecGL
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.F

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.SatComp

open GlobalTheory.LFun GlobalTheory.LGrp GlobalTheory.LFun.SatCompare

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
  {π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V}

theorem hasSatake_of_isSatVecGL (hπ : IsIrrSmooth π) {x : V} (α : Fin n → ℂˣ)
    (hx : IsSatVecGL w π x (Finset.univ.val.map α)) : GlobalTheory.SmGL.HasSatake π α := by
  obtain ⟨φ, hφ, h1, -⟩ := Final.SphericalExists E w n (fun i => (α i : ℂ)) fun i => (α i).ne_zero
  have hφ0 : φ ≠ 0 := fun e => by simp [e] at h1
  obtain ⟨ho, hc⟩ := isOpen_isCompact_KGL w n
  obtain ⟨y, hy, hy0, ht⟩ := exists_fixed_of_fun _ _ ho (Final.GLintComm E w n) hφ0 ((isSphericalGL_iff α φ).1 hφ)
  have hq : IsSubquot π (psGL (w.adicCompletion E) α) :=
    GlobalTheory.T.isSubquotient_of_same_spherical_hecke_eigenvalues _ _ _ π _ _ hc (Final.GLintComm E w n) hπ (LeviDatum.nInd_isSmooth _ _) x hx.2.1
      hx.1 y hy hy0 fun f hf => by
        obtain ⟨c, e1, e2⟩ := exists_eigenvalue_GL hx (isSatVecGL_of_isSpherical hφ hφ0) f hf
        exact ⟨c, e1, ht f hf c e2⟩
  have hs : IsSpherical π (GlobalTheory.SplitWeil.KO (w.adicCompletion E) (Fin n)) := by
    rw [GlobalTheory.SmGL.SphCompletion.KO_completion w n]
    exact (Submodule.ne_bot_iff _).2 ⟨x, hx.2.1, hx.1⟩
  exact ⟨hπ.2, hs, (GlobalTheory.LGrp.SatakeCompare.isSubquot_ps_iff _ _ π α).1 hq⟩

end GlobalTheory.CompanionTheory.SatComp


end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianForm
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianForm
noncomputable section

open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

namespace GlobalTheory.CompanionTheory.ClozelHerm

def petersson {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (μ : Measure (GA E a))
    [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a)
    (hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1) :
    π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun φ ψ => inner ℂ (toL2ₗ μ π.V hm ψ) (toL2ₗ μ π.V hm φ))
    (fun φ φ' ψ => by simp only [map_add (f := _), inner_add_right])
    (fun c φ ψ => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply])
    (fun φ ψ ψ' => by simp only [map_add (f := _), inner_add_left])
    (fun c φ ψ => by simp only [map_smul, inner_smul_left, smul_eq_mul])

theorem exists_isHerm : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ, IsHerm π B := by
  intro hB E _ _ _ a μ _ _ π hπ
  have hl := GlobalTheory.T.normalised_cusp_form_L2_bounded hB E a μ π hπ
  have hm : ∀ φ ∈ π.V, GlobalTheory.AutomorphicL2Unitary.MemL2Quotient (GlobalTheory.UnitaryBC.latticeGL E a) μ φ.1 := fun φ hφ => (hl φ hφ).1
  have hb : ∀ φ ∈ π.V, ∃ C : ℝ, ∀ g, ‖φ.1 g‖ ≤ C := fun φ hφ => (hl φ hφ).2
  refine ⟨petersson μ π hm, fun X φ ψ => GlobalTheory.T.lie_action_skew_adjoint_L2 E a μ π hm hb X φ ψ, ?_⟩
  obtain ⟨φ, hφ, hne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  have hi : Function.Injective (toL2ₗ μ π.V hm) :=
    toL2ₗ_injective hm fun ψ hψ => ContAut.continuous_of_isOpen_stab E a ψ (π.cusp ψ hψ).1.level
  have hT : toL2ₗ μ π.V hm ⟨φ, hφ⟩ ≠ 0 := fun h =>
    hne (congrArg Subtype.val (hi (h.trans (map_zero _).symm)))
  refine ⟨⟨φ, hφ⟩, ?_⟩
  show inner ℂ (toL2ₗ μ π.V hm ⟨φ, hφ⟩) (toL2ₗ μ π.V hm ⟨φ, hφ⟩) ≠ 0
  exact inner_self_ne_zero.2 hT

end GlobalTheory.CompanionTheory.ClozelHerm

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantHermitianFormStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_invariant_hermitian_form : GlobalTheory.Published.CuspFormsBoundedGL → ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ) (μ : Measure (GA E a)) [μ.IsHaarMeasure] [μ.IsMulRightInvariant] (π : CuspSub E a), GlobalTheory.DiscSpec.IsNormalised π → ∃ B : π.V →ₗ[ℂ] π.V →ₗ⋆[ℂ] ℂ, IsHerm π B := by
  first | exact @GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm | exact GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm | (intros; apply GlobalTheory.CompanionTheory.ClozelHerm.exists_isHerm <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceEopEqOfHasInfCharGL
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.CentEig

theorem trace_Eop_eq_of_hasInfCharGL {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} {τ : E →+* ℂ} {m : Multiset ℂ} (hm : HasInfCharGL V τ m) :
    ∀ φ ∈ V, (∑ i : Fin N, Eop τ i i) φ = m.sum • φ := by
  intro φ hφ
  obtain ⟨hc, hu⟩ := hm
  rcases N with _ | n
  · obtain rfl : m = 0 := Multiset.card_eq_zero.1 hc
    simp
  · obtain ⟨l, rfl⟩ := Quot.exists_rep m
    refine GlobalTheory.CompanionTheory.CapelliTrace.trace_of_qdet (Eop τ) l (by simpa using hc) φ fun v => ?_
    have := hu (v - (n : ℂ) / 2) φ hφ
    rw [cap, show v - (n : ℂ) / 2 + (((n + 1 : ℕ) : ℂ) - 1) / 2 = v by push_cast; ring] at this
    simpa using this

end GlobalTheory.CompanionTheory.CentEig

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBound
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.UnitaryBC MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.TotalTrace

theorem eq_zero_of_exp_mul_eq_one {c : ℂ} (h : ∀ t : ℝ, Complex.exp (c * t) = 1) : c = 0 := by
  have h0 : HasDerivAt (fun v : ℝ => c * (v : ℂ)) c 0 := by
    simpa using (Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).const_mul c
  have h1 := h0.cexp
  have h2 : (fun t : ℝ => Complex.exp (c * t)) = fun _ => 1 := funext h
  rw [h2] at h1
  have h3 := h1.unique (hasDerivAt_const (0 : ℝ) (1 : ℂ))
  simpa using h3

theorem total_trace_eq_zero {E : Type} [Field E] [NumberField E] [IsCMField E] {N : ℕ}
    {V : Submodule ℂ (Sm E N)} {m : (E →+* ℂ) → Multiset ℂ} (hV : IsDiscrete V)
    (hm : ∀ τ, HasInfCharGL V τ (m τ)) : ∑ τ, (m τ).sum = 0 := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hV.ne_bot
  obtain ⟨g, hg⟩ : ∃ g, φ.1 g ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hφ0 (Subtype.ext (funext hcon))
  have hlie : lie E N (oneL E N) φ = (∑ τ, (m τ).sum) • φ := by
    rw [GlobalTheory.CompanionTheory.ClozelLie.lie_oneL_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
    exact Finset.sum_congr rfl fun τ _ => GlobalTheory.CompanionTheory.CentEig.trace_Eop_eq_of_hasInfCharGL (hm τ) φ hφ
  refine eq_zero_of_exp_mul_eq_one fun t => ?_
  have h1 := GlobalTheory.CompanionTheory.Clozel.eigen_along_splitCentre E N φ _ hlie t g
  rw [(hV.sqInt φ hφ).1 t g] at h1
  have h2 : Complex.exp ((∑ τ, (m τ).sum) * t) * φ.1 g = 1 * φ.1 g := by rw [one_mul]; exact h1.symm
  exact mul_right_cancel₀ hg h2

theorem twBound : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.TwBound := by
  intro E _ _ _ N
  refine ⟨0, fun V m hV hm => ?_⟩
  rw [total_trace_eq_zero hV hm, norm_zero]

end GlobalTheory.CompanionTheory.TotalTrace

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LimitTwistBoundStatement
open scoped Classical
namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limit_twist_bound : PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5.TwBound := by
  first | exact @GlobalTheory.CompanionTheory.TotalTrace.twBound | exact GlobalTheory.CompanionTheory.TotalTrace.twBound | (intros; apply GlobalTheory.CompanionTheory.TotalTrace.twBound <;> assumption)
end PositivityTheory.Rg.BcB.SpectralAccumulation.Lim5
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsFundamentalDomainRangeProdMap
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.E1

namespace GlobalTheory.CompanionTheory.PairDom

theorem isFundamentalDomain_range_prodMap {A B X Y : Type} [Group A] [Group B] [Group X] [Group Y]
    [TopologicalSpace X] [TopologicalSpace Y] [IsTopologicalGroup X] [IsTopologicalGroup Y]
    [SecondCountableTopology X] [SecondCountableTopology Y] [MeasurableSpace X] [MeasurableSpace Y]
    [BorelSpace X] [BorelSpace Y] (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    [μ.IsMulLeftInvariant] [ν.IsMulLeftInvariant] (f : A →* X) (g : B →* Y) (F : Set X) (G : Set Y)
    (hF : IsFundamentalDomain f.range F μ) (hG : IsFundamentalDomain g.range G ν) :
    IsFundamentalDomain (f.prodMap g).range (F ×ˢ G) (μ.prod ν) := by
  have hmp : ∀ z : X × Y, MeasurePreserving (z * ·) (μ.prod ν) (μ.prod ν) := fun z =>
    measurePreserving_mul_left (μ.prod ν) z
  refine IsFundamentalDomain.mk'' (hF.nullMeasurableSet.prod hG.nullMeasurableSet) ?_ ?_
    (fun γ => (hmp γ).quasiMeasurePreserving)
  · filter_upwards [Measure.quasiMeasurePreserving_fst.ae hF.ae_covers,
      Measure.quasiMeasurePreserving_snd.ae hG.ae_covers] with z h1 h2
    obtain ⟨⟨_, a, rfl⟩, ha⟩ := h1
    obtain ⟨⟨_, b, rfl⟩, hb⟩ := h2
    exact ⟨⟨(f a, g b), (a, b), rfl⟩, ha, hb⟩
  · rintro ⟨_, ⟨a, b⟩, rfl⟩ hγ
    by_cases ha : f a = 1
    · have hb : (⟨g b, b, rfl⟩ : g.range) ≠ 1 := by
        intro h
        apply hγ
        apply Subtype.ext
        exact Prod.ext ha (congrArg Subtype.val h)
      have h3 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).preimage_null (hG.aedisjoint hb)
      refine measure_mono_null ?_ h3
      rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      exact ⟨⟨w.2, hw.2, rfl⟩, ⟨_, hz.2, one_smul _ _⟩⟩
    · have ha' : (⟨f a, a, rfl⟩ : f.range) ≠ 1 := by
        intro h
        exact ha (congrArg Subtype.val h)
      have h3 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).preimage_null (hF.aedisjoint ha')
      refine measure_mono_null ?_ h3
      rintro z ⟨⟨w, hw, rfl⟩, hz⟩
      exact ⟨⟨w.1, hw.1, rfl⟩, ⟨_, hz.1, one_smul _ _⟩⟩

theorem exists_measure_of_eq {X Y : Type} [Group X] [Group Y] [TopologicalSpace X] [TopologicalSpace Y]
    [IsTopologicalGroup X] [IsTopologicalGroup Y] [LocallyCompactSpace X] [LocallyCompactSpace Y]
    [SecondCountableTopology X] [SecondCountableTopology Y]
    [MeasurableSpace X] [MeasurableSpace Y] [BorelSpace X] [BorelSpace Y] (μ₁ : Measure X) (μ₂ : Measure Y)
    [μ₁.IsHaarMeasure] [μ₂.IsHaarMeasure] [μ₁.IsMulRightInvariant] [μ₂.IsMulRightInvariant]
    (Γ : Subgroup (X × Y)) (F : Set (X × Y)) (hF : IsFundamentalDomain Γ F (μ₁.prod μ₂))
    (m : MeasurableSpace (X × Y)) (e : Prod.instMeasurableSpace = m) :
    ∃ μ : @Measure (X × Y) m,
      (@Measure.IsMulLeftInvariant _ m _ μ ∧ @Measure.IsMulRightInvariant _ m _ μ ∧
        @Measure.IsOpenPosMeasure _ _ m μ ∧ @IsLocallyFiniteMeasure _ m _ μ) ∧
      @IsFundamentalDomain Γ (X × Y) _ _ m F μ ∧
      ∀ f : X × Y → ℂ, @integral _ _ _ _ m (@Measure.restrict _ m μ F) f =
        @integral _ _ _ _ Prod.instMeasurableSpace ((μ₁.prod μ₂).restrict F) f := by
  subst e
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  exact ⟨μ₁.prod μ₂, ⟨inferInstance, inferInstance, inferInstance, inferInstance⟩, hF, fun _ => rfl⟩

theorem isMulRightInvariant_GA (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    [m : MeasurableSpace (GA E a)] [hm : BorelSpace (GA E a)] (μ : Measure (GA E a)) [μ.IsHaarMeasure] :
    μ.IsMulRightInvariant := by
  obtain ⟨ν, h1, h2⟩ := GlobalTheory.CompanionTheory.AdelicHaar.exists_haar_rightInvariant E a
  have e : m = CuspidalL2GL.measurableSpace_GA E a := hm.measurable_eq
  subst e
  haveI := CuspidalL2GL.t2Space_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  letI := h2
  rw [Measure.isMulLeftInvariant_eq_smul μ ν]
  exact MeasureTheory.isMulRightInvariant_smul (μ := ν) _

set_option synthInstance.maxHeartbeats 200000 in
theorem prodDom : RatProper → ProdDom := by
  intro _ E _ _ _ a b _ _ _ _ μ₁ _ μ₂ _ F₁ F₂ h₁ h₂
  haveI := CuspidalL2GL.locallyCompactSpace_GA E a
  haveI := CuspidalL2GL.locallyCompactSpace_GA E b
  haveI := CuspidalL2GL.secondCountableTopology_GA E a
  haveI := CuspidalL2GL.secondCountableTopology_GA E b
  haveI := isMulRightInvariant_GA E a μ₁
  haveI := isMulRightInvariant_GA E b μ₂
  haveI : SigmaFinite μ₁ := sigmaFinite_of_locallyFinite
  haveI : SigmaFinite μ₂ := sigmaFinite_of_locallyFinite
  obtain ⟨μ, hh, hf, hi⟩ := exists_measure_of_eq μ₁ μ₂ (ratH E a b) (F₁ ×ˢ F₂)
    (isFundamentalDomain_range_prodMap μ₁ μ₂ (ratGL E a) (ratGL E b) F₁ F₂ h₁ h₂) (borelH E a b)
    Prod.borelSpace.measurable_eq
  exact ⟨⟨μ, hh, F₁ ×ˢ F₂, hf⟩, rfl, fun f => hi f⟩

end GlobalTheory.CompanionTheory.PairDom
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesContinuation
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesContinuation
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.CompanionTheory.SiegelEis

theorem rpow_le_add_rpow {A u c d : ℝ} (hA : 0 < A) (hc : c ≤ u) (hd : u ≤ d) :
    A ^ u ≤ A ^ c + A ^ d := by
  rcases le_total 1 A with h | h
  · have := Real.rpow_le_rpow_of_exponent_le h hd
    have := Real.rpow_nonneg hA.le c
    linarith
  · have := Real.rpow_le_rpow_of_exponent_ge hA h hc
    have := Real.rpow_nonneg hA.le d
    linarith

theorem differentiable_cpow_term {A : ℝ} (hA : 0 < A) (s₁ w : ℂ) :
    Differentiable ℂ (fun s : ℂ => (A : ℂ) ^ (s - s₁) * w) := by
  have hA' : (A : ℂ) ≠ 0 := by exact_mod_cast hA.ne'
  exact ((differentiable_id.sub_const s₁).const_cpow (Or.inl hA')).mul_const w

theorem eis_half_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧ ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  intro F E _ _ _ _ _ σ B n Y r s' hB hn hY b K a hb hK hH χ s₁ f hf
  have hKc := GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s' hB hn hY b K a hb hK hH
  obtain ⟨-, hpos⟩ := GlobalTheory.T.height_function_continuous_pos' F E σ B n Y r s' hB hn hY b K a hb hK hH
  obtain ⟨C₀, hC₀⟩ := GlobalTheory.T.flat_section_growth_bound K a hKc hH hpos χ s₁ f hf
  obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.T.eisenstein_series_convergent F E σ B n Y r s' hB hn hY b K a hb hK hH
  have hC : ∀ s x, ‖flat a f s₁ s x‖ ≤ max C₀ 0 * a x ^ (s.re + (n : ℝ) / 2) := fun s x =>
    (hC₀ s x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (hpos x).le _))
  have hsum : ∀ σ' : ℝ, σ₀ < σ' → ∀ x, Summable fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ' := by
    intro σ' h x
    obtain ⟨C', N, h'⟩ := hσ₀ σ' h
    exact (h' x).1
  refine ⟨fun s x => ∑' q, eisTerm (flat a f s₁ s) x q, σ₀ - (n : ℝ) / 2, ?_, ?_⟩
  · intro s hs x
    apply Summable.hasSum
    have hg := (hsum (s.re + (n : ℝ) / 2) (by linarith) x).mul_left (max C₀ 0)
    first
      | exact Summable.of_norm_bounded _ hg (fun q => hC s _)
      | exact Summable.of_norm_bounded hg (fun q => hC s _)
  · intro x s₀ hs₀
    have hs₀' : σ₀ - (n : ℝ) / 2 < s₀.re := hs₀
    set c := (σ₀ - (n : ℝ) / 2 + s₀.re) / 2 with hc
    set d := s₀.re + 1 with hd
    have hU : IsOpen {s : ℂ | c < s.re ∧ s.re < d} :=
      (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)
    have hmem : {s : ℂ | c < s.re ∧ s.re < d} ∈ 𝓝 s₀ :=
      hU.mem_nhds ⟨by linarith, by linarith⟩
    have hg : Summable fun q : Cos σ Y => max C₀ 0 * (a ((Quotient.out q).1 * x) ^ (c + (n : ℝ) / 2) +
        a ((Quotient.out q).1 * x) ^ (d + (n : ℝ) / 2)) :=
      ((hsum _ (by linarith) x).add (hsum _ (by linarith) x)).mul_left (max C₀ 0)
    have hD : DifferentiableOn ℂ (fun s => ∑' q, eisTerm (flat a f s₁ s) x q) {s : ℂ | c < s.re ∧ s.re < d} := by
      refine Complex.differentiableOn_tsum_of_summable_norm (F := fun q s => eisTerm (flat a f s₁ s) x q) hg
        (fun q => ?_) hU (fun q s hs => ?_)
      · exact (differentiable_cpow_term (hpos _) s₁ (f ((Quotient.out q).1 * x))).differentiableOn
      · refine (hC s _).trans (mul_le_mul_of_nonneg_left (rpow_le_add_rpow (hpos _) ?_ ?_) (le_max_right _ _))
        · linarith [hs.1]
        · linarith [hs.2]
    exact (hD.differentiableAt hmem).differentiableWithinAt

end GlobalTheory.CompanionTheory.SiegelEis
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSeriesContinuationStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_series_continuation : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ Ê : ℂ → G2 σ Y → ℂ, ∃ t : ℝ, (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) ∧ ∀ x, DifferentiableOn ℂ (Ê · x) {s | t < s.re} := by
  first | exact @GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane | exact GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane | (intros; apply GlobalTheory.CompanionTheory.SiegelEis.eis_half_plane <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVerticalBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVerticalBound
noncomputable section

namespace GlobalTheory.CompanionTheory.EisHalf

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem hgt_of_mem {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (ha : IsHgt K a) {k : G2 σ Y} (hk : k ∈ K) : a k = 1 := by
  have h1 : IsPar (1 : G2 σ Y) 1 := isPar_iff.2 ((Matrix.one_mul _).trans (Matrix.mul_one _).symm)
  have := ha.val 1 1 h1 k hk
  simpa using this

theorem hgt_mul {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (ha : IsHgt K a) {p : G2 σ Y} {t} (hp : IsPar p t) {k : G2 σ Y}
    (hk : k ∈ K) (u : G2 σ Y) : a (p * k * u) = a (p * k) * a (k * u) := by
  obtain ⟨q, v, hq, k', hk', e⟩ := ha.iwa (k * u)
  rw [mul_assoc, e, ← mul_assoc, ha.val _ _ (hp.mul hq) k' hk', ha.val p t hp k hk, ha.val q v hq k' hk', map_mul, map_mul,
    NNReal.coe_mul]

theorem exists_nhd_one {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ} (hK : IsCompact (K : Set (G2 σ Y))) (ac : Continuous a)
    (ha : IsHgt K a) (a0 : ∀ x, 0 < a x) :
    ∃ W : Set (G2 σ Y), IsOpen W ∧ (1 : G2 σ Y) ∈ W ∧ ∀ g, ∀ u ∈ W, a g / 2 ≤ a (g * u) ∧ a (g * u) ≤ 2 * a g := by
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  have hn : IsOpen ((fun y : G2 σ Y × G2 σ Y => a (y.1 * y.2)) ⁻¹' Set.Ioo (1 / 2) 2) :=
    isOpen_Ioo.preimage (ac.comp continuous_mul)
  have hs : (K : Set (G2 σ Y)) ×ˢ ({1} : Set (G2 σ Y)) ⊆ (fun y : G2 σ Y × G2 σ Y => a (y.1 * y.2)) ⁻¹' Set.Ioo (1 / 2) 2 := by
    rintro ⟨k, u⟩ ⟨hk, hu⟩
    have hu' : u = 1 := hu
    subst hu'
    simp only [Set.mem_preimage, mul_one]
    rw [hgt_of_mem ha hk]
    norm_num
  obtain ⟨U, V, -, hV, hKU, h1V, hUV⟩ := generalized_tube_lemma hK isCompact_singleton hn hs
  refine ⟨V, hV, h1V rfl, fun g u hu => ?_⟩
  obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa g
  have h := hUV (show (k, u) ∈ U ×ˢ V from ⟨hKU hk, hu⟩)
  obtain ⟨h1, h2⟩ : 1 / 2 < a (k * u) ∧ a (k * u) < 2 := h
  rw [hgt_mul ha hp hk]
  have := a0 (p * k)
  constructor <;> nlinarith

theorem rpow_le_add {A r c c' : ℝ} (hA : 0 < A) (h1 : c ≤ r) (h2 : r ≤ c') : A ^ r ≤ A ^ c + A ^ c' := by
  have p := Real.rpow_pos_of_pos hA c
  have p' := Real.rpow_pos_of_pos hA c'
  rcases le_total A 1 with h | h
  · linarith [Real.rpow_le_rpow_of_exponent_ge hA h h1]
  · linarith [Real.rpow_le_rpow_of_exponent_le h h2]

theorem rpow_le_of_near {A B : ℝ} (hA : 0 < A) (h1 : A / 2 ≤ B) (h2 : B ≤ 2 * A) (e : ℝ) : B ^ e ≤ 2 ^ |e| * A ^ e := by
  have hB : 0 < B := by linarith
  rcases le_total 0 e with h | h
  · rw [abs_of_nonneg h, ← Real.mul_rpow (by norm_num) hA.le]
    exact Real.rpow_le_rpow hB.le h2 h
  · have k := Real.rpow_le_rpow_of_nonpos (half_pos hA) h1 h
    refine k.trans (le_of_eq ?_)
    rw [abs_of_nonpos h, div_eq_mul_inv, Real.mul_rpow hA.le (by norm_num), Real.inv_rpow (by norm_num), Real.rpow_neg (by norm_num),
      mul_comm]

theorem eis_half_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ t₀ : ℝ, ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), t₀ ≤ t → (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → (∀ s : ℂ, t < s.re → (fun x => Ê s x) ∈ modFun σ Y) ∧ ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) ∧ ∀ c c' : ℝ, t < c → ∃ (C : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha χ s₁ f hf
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨ac, a0⟩ := GlobalTheory.T.height_function_continuous_pos' F E σ B n Y r s hB hn hY b K a hb hK ha
  have kc := GlobalTheory.T.isCompact_standard_maximal F E σ B n Y r s hB hn hY b K a hb hK ha
  obtain ⟨C, hC⟩ := GlobalTheory.T.flat_section_growth_bound K a kc ha a0 χ s₁ f hf
  obtain ⟨σ₀, hG⟩ := GlobalTheory.T.eisenstein_series_convergent F E σ B n Y r s hB hn hY b K a hb hK ha
  obtain ⟨W, hW, h1W, hWa⟩ := exists_nhd_one kc ac ha a0
  refine ⟨σ₀ - n / 2, fun t Ê ht hE => ?_⟩
  have tb : ∀ (z : ℂ) (c c' : ℝ), c ≤ z.re → z.re ≤ c' → ∀ g,
      ‖flat a f s₁ z g‖ ≤ |C| * (a g ^ (c + (n : ℝ) / 2) + a g ^ (c' + (n : ℝ) / 2)) := fun z c c' h1 h2 g =>
    (hC z g).trans ((mul_le_mul_of_nonneg_right (le_abs_self C) (Real.rpow_pos_of_pos (a0 g) _).le).trans
      (mul_le_mul_of_nonneg_left (rpow_le_add (a0 g) (by linarith) (by linarith)) (abs_nonneg C)))
  have gr : ∀ c c' : ℝ, t < c → ∃ (D : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ D * (ht2 x : ℝ) ^ N := by
    intro c c' hc
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < max c c' + (n : ℝ) / 2 := by linarith [le_max_left c c']
    obtain ⟨C₁, N₁, H₁⟩ := hG _ h1
    obtain ⟨C₂, N₂, H₂⟩ := hG _ h2
    refine ⟨|C| * (|C₁| + |C₂|), max N₁ N₂, fun z h1z h2z x => ?_⟩
    have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
    have S := (H₁ x).1.add (H₂ x).1
    have hs := (hE z (by linarith) x).norm_le_of_bounded (S.mul_left |C|).hasSum
      (fun q => tb z c (max c c') h1z (h2z.trans (le_max_right c c')) _)
    refine hs.trans ?_
    rw [tsum_mul_left, (H₁ x).1.tsum_add (H₂ x).1, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg C)
    have p1 : (ht2 x : ℝ) ^ N₁ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_left _ _)
    have p2 : (ht2 x : ℝ) ^ N₂ ≤ (ht2 x : ℝ) ^ max N₁ N₂ := pow_le_pow_right₀ hx (le_max_right _ _)
    have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₁ := pow_nonneg (by linarith) _
    have q1 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N₂ := pow_nonneg (by linarith) _
    rw [add_mul]
    exact add_le_add ((H₁ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q0).trans
        (mul_le_mul_of_nonneg_left p1 (abs_nonneg _))))
      ((H₂ x).2.trans ((mul_le_mul_of_nonneg_right (le_abs_self _) q1).trans (mul_le_mul_of_nonneg_left p2 (abs_nonneg _))))
  have ct : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) := by
    rintro ⟨z₀, x₀⟩ ⟨hz₀, -⟩
    have hz₁ : t < z₀.re := hz₀
    obtain ⟨c, hc1, hc2⟩ := exists_between hz₁
    obtain ⟨c', hc'⟩ := exists_gt z₀.re
    have h1 : σ₀ < c + (n : ℝ) / 2 := by linarith
    have h2 : σ₀ < c' + (n : ℝ) / 2 := by linarith
    obtain ⟨_, _, H₁⟩ := hG _ h1
    obtain ⟨_, _, H₂⟩ := hG _ h2
    let V : Set (G2 σ Y) := (fun x => x₀⁻¹ * x) ⁻¹' W
    have hV : IsOpen V := hW.preimage (continuous_const.mul continuous_id)
    let S : Set (ℂ × G2 σ Y) := {z : ℂ | c < z.re ∧ z.re < c'} ×ˢ V
    have hS : IsOpen S :=
      ((isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt Complex.continuous_re continuous_const)).prod hV
    have mS : (z₀, x₀) ∈ S := ⟨⟨hc2, hc'⟩, by simpa [V] using h1W⟩
    have sumU : Summable fun q : Cos σ Y => |C| *
        (2 ^ |c + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c + (n : ℝ) / 2) +
          2 ^ |c' + (n : ℝ) / 2| * a ((Quotient.out q).1 * x₀) ^ (c' + (n : ℝ) / 2)) :=
      (((H₁ x₀).1.mul_left _).add ((H₂ x₀).1.mul_left _)).mul_left _
    have cts : ContinuousOn (fun y : ℂ × G2 σ Y => ∑' q : Cos σ Y, eisTerm (flat a f s₁ y.1) y.2 q) S := by
      refine continuousOn_tsum (fun q => Continuous.continuousOn ?_) sumU ?_
      · have cg : Continuous fun y : ℂ × G2 σ Y => (Quotient.out q).1 * y.2 := continuous_const.mul continuous_snd
        exact ((Complex.continuous_ofReal.comp (ac.comp cg)).cpow (continuous_fst.sub continuous_const)
          fun y => Complex.ofReal_mem_slitPlane.2 (a0 _)).mul (hf.cont.comp cg)
      · rintro q ⟨z, x⟩ ⟨⟨hz1, hz2⟩, hx⟩
        have hu := hWa ((Quotient.out q).1 * x₀) (x₀⁻¹ * x) hx
        rw [show (Quotient.out q).1 * x₀ * (x₀⁻¹ * x) = (Quotient.out q).1 * x by group] at hu
        exact (tb z c c' hz1.le hz2.le _).trans (mul_le_mul_of_nonneg_left (add_le_add
          (rpow_le_of_near (a0 _) hu.1 hu.2 _) (rpow_le_of_near (a0 _) hu.1 hu.2 _)) (abs_nonneg C))
    have ctE : ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) S :=
      cts.congr fun y hy => (hE y.1 (hc1.trans hy.1.1) y.2).tsum_eq.symm
    exact (ctE.continuousAt (hS.mem_nhds mS)).continuousWithinAt
  refine ⟨fun z hz => ?_, ct, gr⟩
  obtain ⟨D, N, hD⟩ := gr z.re z.re hz
  have cz : Continuous fun x => Ê z x :=
    ct.comp_continuous (Continuous.prodMk_right z) fun x => ⟨hz, trivial⟩
  have M1 : (1 : ℝ) ≤ max D 1 := le_max_right _ _
  have M0 : (0 : ℝ) < max D 1 := by linarith
  have Mc : ((max D 1 : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 M0.ne'
  have e : (fun x => Ê z x) = ((max D 1 : ℝ) : ℂ) • ((((max D 1 : ℝ) : ℂ))⁻¹ • fun x => Ê z x) := by
    rw [smul_smul, mul_inv_cancel₀ Mc, one_smul]
  rw [e]
  refine Submodule.smul_mem _ _ (Submodule.subset_span ⟨cz.const_smul _, N, fun x => ?_⟩)
  have hx : (1 : ℝ) ≤ ht2 x := one_le_heightGL F x.1
  have q0 : (0 : ℝ) ≤ (ht2 x : ℝ) ^ N := pow_nonneg (by linarith) _
  rw [Pi.smul_apply, norm_smul, norm_inv, Complex.norm_real, Real.norm_of_nonneg M0.le, inv_mul_le_iff₀ M0]
  exact (hD z le_rfl le_rfl x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) q0)

end GlobalTheory.CompanionTheory.EisHalf

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinVerticalBoundStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eisenstein_vertical_bound : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∀ (χ : Chr F E) (s₁ : ℂ) (f : G2 σ Y → ℂ), IsSec K χ s₁ f → ∃ t₀ : ℝ, ∀ (t : ℝ) (Ê : ℂ → G2 σ Y → ℂ), t₀ ≤ t → (∀ s : ℂ, t < s.re → ∀ x, HasSum (eisTerm (flat a f s₁ s) x) (Ê s x)) → (∀ s : ℂ, t < s.re → (fun x => Ê s x) ∈ modFun σ Y) ∧ ContinuousOn (fun y : ℂ × G2 σ Y => Ê y.1 y.2) ({s : ℂ | t < s.re} ×ˢ Set.univ) ∧ ∀ c c' : ℝ, t < c → ∃ (C : ℝ) (N : ℕ), ∀ s : ℂ, c ≤ s.re → s.re ≤ c' → ∀ x, ‖Ê s x‖ ≤ C * (ht2 x : ℝ) ^ N := by
  first | exact @GlobalTheory.CompanionTheory.EisHalf.eis_half_plane | exact GlobalTheory.CompanionTheory.EisHalf.eis_half_plane | (intros; apply GlobalTheory.CompanionTheory.EisHalf.eis_half_plane <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSubquotientIff
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.CompanionTheory.OnePart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem hasSat_iff {π : CuspSub E n} {w : HeightOneSpectrum (𝓞 E)} {τ : SmIrr (GL (Fin n) (w.adicCompletion E))}
    (hτ : π.IsLocComp w τ) (B : Multiset ℂˣ) : (CG.mk π).HasSat w B ↔ GlobalTheory.LFun.HasSatGL w τ.ρ B := by
  refine ⟨fun h => ?_, fun h => GlobalTheory.HeightCounting.Blocks.hasSatGL_locRep hτ h⟩
  obtain ⟨α, hαB, hα⟩ := GlobalTheory.LFun.SphComp.hasSatake_of_isLocComp π h hτ
  rw [← hαB]
  exact GlobalTheory.LFun.SatBridge.hasSatGL_of_hasSatake E w n _ _ _ hα

end GlobalTheory.CompanionTheory.OnePart

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceLocalElement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceLocalElement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.NormSplit

theorem thetaGL_eq_id_map {R : Type} [CommRing R] (a : ℕ) (c : R →+* R) (g : GL (Fin a) R) :
    thetaGL a c g = thetaGL a (RingHom.id _) (GeneralLinearGroup.map c g) := by
  ext i j
  rw [GlobalTheory.ThetaPull.thetaGL_apply, GlobalTheory.ThetaPull.thetaGL_apply, ← map_inv]
  rfl

theorem ratW_mul_thetaGL : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), IsSplitAt w →
    ratW n w δ * thetaGL n (RingHom.id _) (ratW n w (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ)) = locEl n w δ := by
  intro E _ _ _ n w δ hs
  unfold locEl
  rw [if_pos hs, map_mul]
  congr 1
  unfold thE
  rw [thetaGL_eq_id_map n (IsCMField.complexConj E).toRingEquiv.toRingHom δ]
  exact (GlobalTheory.ThetaPull.map_thetaGL (algebraMap E (w.adicCompletion E)) (RingHom.id _) (RingHom.id _) (fun _ => rfl) _).symm

end GlobalTheory.CompanionTheory.NormSplit

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceLocalElementStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcB.G8.Fin GlobalTheory.CompanionTheory.LocalHypotheses
open scoped Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.split_place_local_element : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : Pl E) (δ : GL (Fin n) E), IsSplitAt w →
  ratW n w δ * thetaGL n (RingHom.id _) (ratW n w (GeneralLinearGroup.map (IsCMField.complexConj E).toRingEquiv.toRingHom δ)) = locEl n w δ := by
  first | exact @GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL | exact GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL | (intros; apply GlobalTheory.CompanionTheory.NormSplit.ratW_mul_thetaGL <;> assumption)
end
end
