module

public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicUnitaryEqMulTrivOutsidePlaceAndAtPla
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PairReadingOfJoin
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterInvariantUnderConjugation
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RestrictsExists
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousToZModComp
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSplitOfGPl

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.BlockType GlobalTheory.SplitWeil
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TypeBlockPf

theorem splitAt : ∀ (D : D7) (w : PlE D.host), IsSplitPl D.host w → ∃ s : SplitPlace D.host.E, s.w = w := by
  intro D w hw
  have hc : ∀ x : 𝓞 D.host.E, ((GlobalTheory.SumWCompare.cj D.host.E x : 𝓞 D.host.E) : D.host.E) = D.host.conj (x : D.host.E) := by
    intro x; rw [GlobalTheory.SumWCompare.cj_coe, GlobalTheory.DimPartsCompare.star_conj]
  have hcc : ∀ z : D.host.E, D.host.conj (D.host.conj z) = z := by
    intro z; rw [← GlobalTheory.DimPartsCompare.star_conj, ← GlobalTheory.DimPartsCompare.star_conj, star_star]
  obtain ⟨x, hx, hy⟩ := hw
  have hsp : IsSplitPl D.host (GlobalTheory.DimPartsCompare.cPl w) := by
    refine ⟨GlobalTheory.SumWCompare.cj D.host.E x, ?_, fun y e hy' => ?_⟩
    · rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj]; exact hx
    · rw [GlobalTheory.DimPartsCompare.mem_cPl] at hy'
      refine hy _ ?_ hy'
      rw [hc, show y = x from RingOfIntegers.ext (by rw [e, hc, hcc])]
  obtain ⟨s, -, hs, -⟩ := GlobalTheory.SplitConjPlace.splitEx_all D _ hsp
  refine ⟨s, HeightOneSpectrum.ext (Ideal.ext fun y => ?_)⟩
  have := hs (GlobalTheory.SumWCompare.cj D.host.E y) y (by rw [hc, hcc])
  rw [GlobalTheory.DimPartsCompare.mem_cPl, GlobalTheory.SumWCompare.cj_cj] at this
  exact this.symm

end GlobalTheory.TypeBlockPf
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisCompatibilityOfJumps
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.TieGalAssembly

theorem potCrysIffWD (D : D7) : PotCrysIffWD D.nd D.naut := by
  intro i a r w hw hr
  refine ⟨fun hc => ?_, fun h => (D.naut.wdOf_mono0L i r w hw hr h.1).1 h.2⟩
  suffices hd : D.naut.IsdRW i r w from ⟨hd, (D.naut.wdOf_mono0L i r w hw hr hd).2 hc⟩
  have := D.nd.lPrime i
  obtain ⟨L, hle, hL⟩ := GlobalTheory.T.compactGroup_rep_defined_over_finite_extension (D.nd.l i) _ a r hr (D.nbr i w hw).LL
  obtain ⟨ρ, hρ, rfl⟩ := GlobalTheory.CrysWD.exists_descent r hr L hL
  obtain ⟨-, h2, h1, -⟩ := (D.loc_tie i w hw).2.2 L hle a ρ hρ
  have := L.2
  obtain ⟨K', hK, hc'⟩ := h1.1 hc
  have h3 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys _ _ _ (D.locT (D.nd.l i)) _ L _ _ hc').1
  have h4 := (GlobalTheory.Per.TiedRestrict.isDR_restrict_iff hK _ (D.locT (D.nd.l i))).2 h3
  refine h2.2 ?_
  unfold IsDR at h4
  unfold LocBridge.IsdRE
  simpa using h4

end GlobalTheory.TieGalAssembly
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.GaloisRestrictionWdCompatible
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G IsPlaceOver Dec
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.AboveL

noncomputable section
open IsNilpotent

namespace GlobalTheory.AboveL.ResWD

variable {K L Ω : Type} [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω]
  [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 K)} {v' : HeightOneSpectrum (𝓞 L)}
  {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem exists_tval_resI (h' : IsPlaceOver A v') (hl' : ((l : ℕ) : 𝓞 L) ∉ v'.asIdeal)
    {t : Ine (F := K) A →* Multiplicative ℤ_[l]} {t' : Ine (F := L) A →* Multiplicative ℤ_[l]}
    (ht : IsTameChar t) (ht' : IsTameChar t') :
    ∃ c : Qbar l, c ≠ 0 ∧ ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ := by
  obtain ⟨c, hc⟩ := GlobalTheory.TameCharUnique.exists_eq_mul L Ω A v' h' l hl' (t.comp ResEx.resI) t'
    (ht.1.comp ResEx.continuous_resI) ht'.1 ht'.2
  refine ⟨algebraMap ℚ_[l] (Qbar l) (c : ℚ_[l]), ?_, fun σ => ?_⟩
  swap
  · have := hc σ
    simp only [MonoidHom.comp_apply] at this
    simp [tval, this]
  intro h0
  rw [map_eq_zero, PadicInt.coe_eq_zero] at h0
  have hc0 : ∀ σ, (t (ResEx.resI (K := K) σ)).toAdd = 0 := fun σ => by
    have := hc σ
    simpa [h0] using this
  obtain ⟨σ, hσ⟩ := ht.2 (Multiplicative.ofAdd 1)
  haveI : Module.Finite K L := Module.Finite.of_restrictScalars_finite ℚ K L
  let f : ℕ → (L →ₐ[K] Ω) := fun n => (((σ : G K Ω) ^ n : G K Ω) : Ω →ₐ[K] Ω).comp (IsScalarTower.toAlgHom K L Ω)
  have main : ∀ i j : ℕ, i < j → f i = f j → False := fun i j hij e => by
    set k := j - i with hk
    have hk0 : 0 < k := Nat.sub_pos_of_lt hij
    have hfix : ∀ x : L, ((σ : G K Ω) ^ k).toRingEquiv (algebraMap L Ω x) = algebraMap L Ω x := fun x => by
      have e1 := congrArg (fun g : L →ₐ[K] Ω => g x) e
      simp only [f, AlgHom.comp_apply, IsScalarTower.coe_toAlgHom', AlgEquiv.coe_algHom] at e1
      have e2 : (σ : G K Ω) ^ j = (σ : G K Ω) ^ i * (σ : G K Ω) ^ k := by
        rw [← pow_add, hk, Nat.add_sub_cancel' hij.le]
      rw [e2, AlgEquiv.mul_apply] at e1
      exact (((σ : G K Ω) ^ i).injective e1).symm
    let σ'' : G L Ω := AlgEquiv.ofRingEquiv (f := ((σ : G K Ω) ^ k).toRingEquiv) hfix
    have hres : AlgEquiv.restrictScalarsHom K σ'' = (σ : G K Ω) ^ k := AlgEquiv.ext fun _ => rfl
    have hmem : σ'' ∈ Ine (F := L) A := by
      show AlgEquiv.restrictScalarsHom K σ'' ∈ Ine (F := K) A
      rw [hres]
      exact pow_mem σ.2 k
    have e3 : ResEx.resI (K := K) ⟨σ'', hmem⟩ = σ ^ k := Subtype.ext (by rw [SubgroupClass.coe_pow, ← hres]; rfl)
    have := hc0 ⟨σ'', hmem⟩
    rw [e3, map_pow, hσ, ← ofAdd_nsmul, toAdd_ofAdd, nsmul_eq_mul, mul_one, Nat.cast_eq_zero] at this
    omega
  obtain ⟨i, j, hij, e⟩ := Finite.exists_ne_map_eq_of_infinite f
  rcases lt_or_gt_of_ne hij with hlt | hlt
  · exact main i j hlt e
  · exact main j i hlt e.symm

theorem isMonodromy_res {t : Ine (F := K) A →* Multiplicative ℤ_[l]}
    {t' : Ine (F := L) A →* Multiplicative ℤ_[l]} {r : G K Ω →* GL (Fin a) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {c : Qbar l} (hN : IsMonodromy t r N)
    (hc : ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ) :
    IsMonodromy t' (resTo L r) (c • N) := by
  obtain ⟨h1, U, hU, H⟩ := hN
  refine ⟨h1.smul c, U.comap ResEx.resI, hU.preimage ResEx.continuous_resI, fun σ hσ => ?_⟩
  have := H _ hσ
  rw [smul_smul, mul_comm, ← hc]
  exact this

theorem exists_conj (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (hl : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal)
    {t : Ine (F := K) A →* Multiplicative ℤ_[l]}
    {t' : Ine (F := L) A →* Multiplicative ℤ_[l]} {r : G K Ω →* GL (Fin a) (Qbar l)}
    {N : Matrix (Fin a) (Fin a) (Qbar l)} {c : Qbar l} (ht : IsTameChar t) (hN : IsMonodromy t r N)
    (hc : ∀ σ, tval t (ResEx.resI (K := K) σ) = c * tval t' σ) :
    ∃ β : Qbar l, ∀ g : Weil h', exp (β • N) * wdMat t' (deg_frob (h := h')) (resTo L r) (c • N) g =
      wdMat t (deg_frob (h := h)) r N (ResEx.resW h h' g) * exp (β • N) := by
  have hq0 : ((normV v : ℕ) : Qbar l) ≠ 0 := Nat.cast_ne_zero.mpr (ReciprocityTheory.Gal.one_lt_normV v).ne_bot
  have hf : deg (ResEx.resW h h' (frob h')) ≠ 0 := by
    intro h0
    have h1 : ((frob h' : Weil h') : G L Ω) ∈ Ine (F := L) A :=
      (deg_eq_zero_iff (σ := ResEx.resW h h' (frob h'))).1 h0
    have h2 := (deg_eq_zero_iff (σ := frob h')).2 h1
    rw [deg_frob] at h2
    exact one_ne_zero h2
  have hq1 : 1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹ ≠ 0 := by
    rw [sub_ne_zero, ne_comm, Ne, inv_eq_one]
    intro h1
    have h3 : (((normV v : ℕ) : ℚ) ^ deg (ResEx.resW h h' (frob h')) : ℚ) = 1 := by
      rw [← Rat.cast_inj (α := Qbar l)]; push_cast; exact h1
    exact hf ((zpow_eq_one_iff_right₀ (Nat.cast_nonneg _)
      (Nat.cast_ne_one.mpr (ReciprocityTheory.Gal.one_lt_normV v).ne')).mp h3)
  have key : ∀ m : ℤ,
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ m)) *
        (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹) =
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) *
        (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h') ^ m))⁻¹) := fun m => by
    have h1 := ht.tval_inePart_mul hl (deg_frob (h := h)) (ResEx.resW h h' (frob h'))
      (ResEx.resW h h' (frob h') ^ m)
    have h2 := ht.tval_inePart_mul hl (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ m)
      (ResEx.resW h h' (frob h'))
    rw [(Commute.self_zpow (ResEx.resW h h' (frob h')) m).eq] at h1
    linear_combination h2 - h1
  refine ⟨tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) /
    (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹), fun g => ?_⟩
  have hg : g = frob h' ^ deg g * ineIncl h' (inePart (deg_frob (h := h')) g) := by
    rw [ineIncl_inePart, mul_inv_cancel_left]
  have hRg : ResEx.resW h h' g =
      ResEx.resW h h' (frob h') ^ deg g * ineIncl h (ResEx.resI (inePart (deg_frob (h := h')) g)) := by
    conv_lhs => rw [hg]
    rw [map_mul, map_zpow, ResEx.resW_ineIncl]
  have hT : tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' g)) =
      tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ deg g)) +
        tval t (ResEx.resI (inePart (deg_frob (h := h')) g)) := by
    rw [hRg, ht.tval_inePart_mul hl, deg_ineIncl, zpow_zero, inv_one, one_mul, inePart_ineIncl]
  have hd : deg (ResEx.resW h h' g) = deg (ResEx.resW h h' (frob h') ^ deg g) := by
    rw [hRg, deg_mul, deg_ineIncl, add_zero]
  have hs := key (deg g)
  have hqd : ((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' g) ≠ 0 := zpow_ne_zero _ hq0
  rw [wdMat, wdMat, hT]
  have e1 : (-tval t' (inePart (deg_frob (h := h')) g)) • (c • N) =
      (-tval t (ResEx.resI (inePart (deg_frob (h := h')) g))) • N := by
    rw [smul_smul, hc]
    congr 1
    ring
  have e2 : ((resTo L r g : Matrix (Fin a) (Fin a) (Qbar l))) = r (ResEx.resW h h' g) := rfl
  rw [e1, e2]
  set β := tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h'))) /
    (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h')))⁻¹) with hβ
  have h2 := hN.mul_exp hl ht (ResEx.resW h h' g) ((((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' g))⁻¹ * β)
  rw [mul_inv_cancel_left₀ hqd] at h2
  rw [← mul_assoc, ← h2, mul_assoc, mul_assoc, ← exp_add_smul hN.1, ← exp_add_smul hN.1]
  congr 3
  have hsm : tval t (inePart (deg_frob (h := h)) (ResEx.resW h h' (frob h') ^ deg g)) =
      β * (1 - (((normV v : ℕ) : Qbar l) ^ deg (ResEx.resW h h' (frob h') ^ deg g))⁻¹) := by
    rw [hβ, div_mul_eq_mul_div, eq_div_iff hq1]
    linear_combination hs
  rw [hd]
  linear_combination hsm

end GlobalTheory.AboveL.ResWD

namespace GlobalTheory.AboveL

theorem wdOf_restricts : ∀ (K L Ω : Type) [Field Ω] [Field K] [NumberField K] [Algebra K Ω] [IsAlgClosure K Ω] [Field L] [NumberField L] [Algebra L Ω] [IsAlgClosure L Ω] [Algebra K L] [IsScalarTower K L Ω] (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 K)) (v' : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A v) (h' : IsPlaceOver A v') (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ) (r : G K Ω →* GL (Fin a) (Qbar l)) (hl : ((l : ℕ) : 𝓞 K) ∉ v.asIdeal) (hl' : ((l : ℕ) : 𝓞 L) ∉ v'.asIdeal), Continuous r → Restricts (wdOf h hl ι r) (wdOf h' hl' ι (resTo L r)) := by
  intro K L Ω _ _ _ _ _ _ _ _ _ _ _ A v v' h h' l _ ι a r hl hl' hr
  have hr' : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)) := Units.continuous_val.comp hr
  have ht := isTameChar_tameL h hl
  have ht' := isTameChar_tameL h' hl'
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hr'
  obtain ⟨c, hc0, hc⟩ := ResWD.exists_tval_resI h' hl' ht ht'
  have hN' := ResWD.isMonodromy_res hN hc
  obtain ⟨β, hβ⟩ := ResWD.exists_conj h h' hl ht hN hc
  obtain ⟨aK, haK⟩ := hN.exists_isFrobSS hl ht (deg_frob (h := h)) ι
  have ex : wdOf h hl ι r = WD.mk aK := IsWDOf.wdOf_eq hl ⟨_, ht, _, deg_frob, N, aK, hN, haK, rfl⟩
  have hb : IsFrobSS (fun g => toEndC ι (wdMat (tameL h hl) (deg_frob (h := h)) r N (ResEx.resW h h' g)))
      (toEndC ι N) (ResEx.resRep h h' aK) := ⟨haK.1, fun g => haK.2 _⟩
  obtain ⟨aL2, haL2⟩ := hN'.exists_isFrobSS hl' ht' (deg_frob (h := h')) ι
  have hcomm : ∀ g, hN'.rep hl' ht' (deg_frob (h := h')) ι g * toEndC ι N =
      ((normV v' : ℕ) : ℂ) ^ deg g • (toEndC ι N * hN'.rep hl' ht' (deg_frob (h := h')) ι g) := fun g => by
    have := hN'.rep_comm hl' ht' (deg_frob (h := h')) ι g
    rw [toEndC_smul, mul_smul_comm, smul_mul_assoc, smul_comm] at this
    exact smul_right_injective _ ((map_ne_zero ι).mpr hc0) this
  obtain ⟨aL1, haL1⟩ := WeilDeligne.exists_isFrobSS (hN'.rep hl' ht' (deg_frob (h := h')) ι) (toEndC ι N)
    (hN'.isSmooth_rep hl' ht' _ ι) (hN.1.map _) hcomm
  obtain ⟨u, hu⟩ := (isUnit_exp (hN.1.smul β)).map (toEndC ι (n := Fin a))
  have i1 : aL1.Iso (ResEx.resRep h h' aK) := haL1.iso hb (LinearMap.GeneralLinearGroup.toLinearEquiv u)
    (fun g w => by
      show ((u : Module.End ℂ (Fin a → ℂ)) * toEndC ι (wdMat (tameL h' hl') (deg_frob (h := h')) (resTo L r) (c • N) g)) w =
        (toEndC ι (wdMat (tameL h hl) (deg_frob (h := h)) r N (ResEx.resW h h' g)) * (u : Module.End ℂ (Fin a → ℂ))) w
      rw [hu, ← map_mul, hβ, map_mul])
    (fun w => by
      show ((u : Module.End ℂ (Fin a → ℂ)) * toEndC ι N) w = (toEndC ι N * (u : Module.End ℂ (Fin a → ℂ))) w
      rw [hu, ← map_mul, exp_smul_mul hN.1, map_mul])
  have i2 : aL1.Iso aL2 := haL1.iso_of_smul ((map_ne_zero ι).mpr hc0) (by
    have := haL2
    rw [toEndC_smul] at this
    exact this)
  have ex' : wdOf h' hl' ι (resTo L r) = WD.mk (ResEx.resRep h h' aK) :=
    (IsWDOf.wdOf_eq hl' ⟨_, ht', _, deg_frob, c • N, aL2, hN', haL2, rfl⟩).trans (WD.sound (i2.symm.trans i1))
  refine ⟨a, aK, ResEx.resRep h h' aK, ex.symm, ex'.symm, rfl, fun σ σ' hs => ?_⟩
  show aK.ρ (ResEx.resW h h' σ') = aK.ρ σ
  congr 1
  exact Subtype.ext (AlgEquiv.ext fun z => (hs z).symm)

end GlobalTheory.AboveL

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumJetsTranslate
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.MomT
open GlobalTheory.IndefiniteRowSideFullHecke.BadPrimesPeriodBound (recFields recPrimes recSeam HostTie AnTie badS)
open GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation (StdOver)

noncomputable section

namespace GlobalTheory.DatumJets.Transl

open GlobalTheory.LiftTypePrime GlobalTheory.MomT.PtMoments

theorem exists_denom {E W : Type} [Field E] [NumberField E] [AddCommGroup W] [Module (𝓞 E) W] {p : ℕ} (hp : p.Prime)
    {M M' : Submodule (𝓞 E) W} (hM : M.FG)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ P.asIdeal → M ≤ localization₂ P.asIdeal M') :
    ∃ s : ℕ, Nat.Coprime s p ∧ ∀ x ∈ M, (s : 𝓞 E) • x ∈ M' := by
  have key : ∀ x : W, ∃ s : ℕ, Nat.Coprime s p ∧ (x ∈ M → (s : 𝓞 E) • x ∈ M') := fun x => by
    by_cases hx : x ∈ M
    swap
    · exact ⟨1, by simp, fun h => absurd h hx⟩
    by_contra hn
    let I : Ideal (𝓞 E) := M'.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
    have : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
    have hI : I.comap (algebraMap ℤ (𝓞 E)) ≤ Ideal.span {(p : ℤ)} := fun z hz => by
      rw [Ideal.mem_span_singleton, Int.natCast_dvd]
      by_contra hz'
      refine hn ⟨z.natAbs, ((Nat.Prime.coprime_iff_not_dvd hp).2 hz').symm, fun _ => ?_⟩
      have hz1 : (z : 𝓞 E) • x ∈ M' := hz
      rcases Int.natAbs_eq z with h1 | h1
      · rw [h1, Int.cast_natCast] at hz1; exact hz1
      · rw [h1, Int.cast_neg, Int.cast_natCast, neg_smul, neg_mem_iff] at hz1; exact hz1
    obtain ⟨Q, hQ, hQp, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (Ideal.span {(p : ℤ)}) I hI
    have hpQ : (p : 𝓞 E) ∈ Q := by
      have : (p : ℤ) ∈ Q.comap (algebraMap ℤ (𝓞 E)) := by
        change (p : ℤ) ∈ Ideal.under ℤ Q
        rw [hQc]
        exact Ideal.mem_span_singleton_self _
      simpa using this
    have hQ0 : Q ≠ ⊥ := by
      rintro rfl
      exact hp.ne_zero (by simpa using hpQ)
    obtain ⟨c, hc, hcx⟩ : ∃ c : 𝓞 E, c ∉ Q ∧ c • x ∈ M' := h ⟨Q, hQp, hQ0⟩ hpQ hx
    exact hc (hQ hcx)
  choose f hf hfx using key
  obtain ⟨S, rfl⟩ := hM
  refine ⟨∏ x ∈ S, f x, Nat.Coprime.prod_left fun x _ => hf x, fun x hx => ?_⟩
  refine (Submodule.span_le (p := M'.comap (((∏ x ∈ S, f x : ℕ) : 𝓞 E) • LinearMap.id))).2 (fun y hy => ?_) hx
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem f (Finset.mem_coe.1 hy)
  change ((∏ x ∈ S, f x : ℕ) : 𝓞 E) • y ∈ M'
  rw [hc, mul_comm, Nat.cast_mul, mul_smul]
  exact M'.smul_mem _ (hfx y (Submodule.subset_span hy))

theorem stdLat_fg (E : Type) [Field E] (n : ℕ) : (Formalism.L2.Col.stdLat E n).FG :=
  Submodule.fg_pi fun _ => by rw [Submodule.one_eq_span]; exact Submodule.fg_span_singleton _

theorem stdAt_of_stdOver (D : D7) {p : ℕ} (hp : p.Prime) {n : ℕ} {N : Submodule (𝓞 D.host.E) (Sp D.host.E n)} (hN : N.FG)
    (h : StdOver p N) : StdAt D p ((recSeam D).lat N) := by
  obtain ⟨s, hs, h1⟩ := exists_denom hp hN (M' := Formalism.L2.Col.stdLat D.host.E n) fun P hP => (le_locP _ _).trans (h P hP).le
  obtain ⟨t, ht, h2⟩ := exists_denom hp (stdLat_fg D.host.E n) (M' := N) fun P hP => (le_locP _ _).trans (h P hP).ge
  have hl : ∀ x, x ∈ (recSeam D).lat N ↔ x ∈ N := fun x => GlobalTheory.SeamTransport.mem_lat (recSeam D) N x
  refine ⟨Formalism.L2.Col.stdLat D.host.E n, fun x => ?_, s * t, hs.mul_left ht, fun x hx => ?_, fun x hx => ?_⟩
  · simp only [Formalism.L2.Col.stdLat, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
    exact forall_congr' fun k => ⟨fun ⟨y, hy⟩ => hy ▸ y.isIntegral_coe, fun hy => ⟨⟨_, hy⟩, rfl⟩⟩
  · have := h1 x ((hl x).1 hx)
    rw [Nat.cast_smul_eq_nsmul] at this ⊢
    rw [mul_comm, mul_smul]
    exact nsmul_mem this _
  · have := h2 x hx
    rw [Nat.cast_smul_eq_nsmul] at this ⊢
    rw [hl, mul_smul]
    exact nsmul_mem this _

variable {D : D7} {a b : ℕ}

end GlobalTheory.DatumJets.Transl
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatUOfFixed
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertSph

theorem satU_of_fixed : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)) (hS : NG.IsIrrRep a.ρ S) (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)) (Dv : InertDatum L n v w) (α : Fin (n / 2) → ℂ), NG.OverPl w v → NG.SatAt { a with S := S, irrS := hS } Dv α → ∀ U : Subgroup (GAf L n), (∀ κ, TrivOutside {v} κ → (κ ∈ U ↔ κ ∈ Umax L n)) → ∀ f ∈ S, (∀ κ ∈ U, NG.rt L n κ f = f) → ∀ h ∈ Formalism.UG.Hecke ℂ (Formalism.UG.KU Dv.σw n), heckeFunI L n U Dv h f = Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α • f := by
  intro L _ _ _ n a S hS v w Dv α _ hsat U hU f hfS hfU h hh
  obtain ⟨f₀, hf₀S, hf₀0, U', hf₀U', hU', hH⟩ := hsat
  have hf₀S' : f₀ ∈ S := hf₀S
  have hK : ∀ κ : GAf L n, κ ∈ Umax L n → TrivOutside {v} κ → ∃ hκ : Dv.loc κ ∈ Formalism.UG.GU Dv.σw n,
      (⟨Dv.loc κ, hκ⟩ : Formalism.UG.GU Dv.σw n) ∈ Formalism.UG.KU Dv.σw n :=
    fun κ hκ _ => ⟨GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv κ, GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv κ hκ _⟩
  have hUmax : ∀ κ : GAf L n, TrivOutside {v} κ → (κ ∈ Umax L n ↔ κ ∈ Umax L n) := fun _ _ => Iff.rfl
  let ρ : GAf L n →* Module.End ℂ (GAf L n → a.W) :=
    { toFun := fun g => NG.rt L n g
      map_one' := LinearMap.ext fun φ => funext fun x => by
        show φ (x * 1) = φ x
        rw [mul_one]
      map_mul' := fun g g' => LinearMap.ext fun φ => funext fun x => by
        show φ (x * (g * g')) = φ (x * g * g')
        rw [mul_assoc] }
  have hρ : ∀ g φ, ρ g φ = NG.rt L n g φ := fun _ _ => rfl
  have hf₀K : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f₀ = f₀ :=
    fun κ hκ ht => hf₀U' κ ((hU' κ ht).2 hκ)
  have hfK : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f :=
    fun κ hκ ht => hfU κ ((hU κ ht).2 hκ)
  have hrtc : ∀ (φ : GAf L n → a.W) (x b : GAf L n), TrivOutside {v} x → TrivOutside {v}ᶜ b →
      NG.rt L n x (NG.rt L n b φ) = NG.rt L n b (NG.rt L n x φ) := by
    intro φ x b hx hb
    funext y
    show φ (y * x * b) = φ (y * b * x)
    rw [mul_assoc, mul_assoc, (GlobalTheory.InertSph.commute_of_trivOutside v x b hx hb).eq]
  have hrtm : ∀ (φ : GAf L n → a.W) (x b : GAf L n),
      NG.rt L n x (NG.rt L n b φ) = NG.rt L n (x * b) φ := by
    intro φ x b
    funext y
    show φ (y * x * b) = φ (y * (x * b))
    rw [mul_assoc]

  have hloc := fun x (hx : TrivOutside {v} x) => GlobalTheory.T.inertDoubleCosetOperator_eq_inertHeckeOperator L n v w Dv (GlobalTheory.T.inertDatum_local_mem_unitaryGroup_antidiagonal L n v w Dv) (GlobalTheory.T.inertDatum_local_stdLatticeStabilizer_mem_maxCompact L n v w Dv)
    (GlobalTheory.T.exists_trivOutside_inertDatum_local_eq L n v w Dv) (GlobalTheory.T.inertDatum_local_injective_on_trivOutside L n v w Dv) x hx
  choose! R ha hR hha hA using hloc
  have hχ : ∀ x, TrivOutside {v} x → ∑ γ ∈ R x, NG.rt L n γ f₀ =
      Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) (ha x) α • f₀ := by
    intro x hx
    rw [hA x hx a.W f₀ hf₀K, GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK (Umax L n) U' hUmax hU' a.W (ha x) (hha x hx).1 f₀ hf₀K]
    exact hH _ (hha x hx)

  let W' : Submodule ℂ (GAf L n → a.W) :=
    Submodule.span ℂ (Set.range fun b : {b : GAf L n // TrivOutside {v}ᶜ b} => NG.rt L n (b : GAf L n) f₀)
  have hgen : ∀ b : GAf L n, TrivOutside {v}ᶜ b → NG.rt L n b f₀ ∈ W' :=
    fun b hb => Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
  have hW : W' ≤ GlobalTheory.SphScalar.fixS ρ S (GlobalTheory.InertSph.Kv L n v) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨b, hb⟩, rfl⟩
    refine ⟨hS.1.stable b f₀ hf₀S', fun k hk => ?_⟩
    rw [hρ, hrtc f₀ k b hk.2 hb, hf₀K k hk.1 hk.2]
  have hf₀W : f₀ ∈ W' := by
    have := hgen 1 (GlobalTheory.InertSph.trivOutside_one _)
    have e : NG.rt L n (1 : GAf L n) f₀ = f₀ := funext fun y => by
      show f₀ (y * 1) = f₀ y
      rw [mul_one]
    rwa [e] at this
  have hW0 : W' ≠ ⊥ := by
    intro h0
    apply hf₀0
    have := hf₀W
    rw [h0] at this
    exact (Submodule.mem_bot ℂ).1 this
  have hWb : ∀ b ∈ {b : GAf L n | TrivOutside {v}ᶜ b}, ∀ x ∈ W', ρ b x ∈ W' := by
    intro b hb x hx
    have hle : W' ≤ W'.comap (ρ b) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨b', hb'⟩, rfl⟩
      show ρ b (NG.rt L n b' f₀) ∈ W'
      rw [hρ, hrtm]
      exact hgen _ (GlobalTheory.SatInd.CosetFin.trivOutside_mul hb hb')
    exact hle hx
  have hWR : ∀ x ∈ {x : GAf L n | TrivOutside {v} x}, ∀ y ∈ W', ∑ γ ∈ R x, ρ γ y ∈ W' := by
    intro x hx y hy
    have hγ : ∀ γ ∈ R x, TrivOutside {v} γ := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (hR x hx).1 γ hγ
      exact GlobalTheory.SatInd.CosetFin.trivOutside_mul (GlobalTheory.SatInd.CosetFin.trivOutside_mul hk₁.2 hx) hk₂.2
    have hle : W' ≤ W'.comap (∑ γ ∈ R x, ρ γ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨⟨b, hb⟩, rfl⟩
      show (∑ γ ∈ R x, ρ γ) (NG.rt L n b f₀) ∈ W'
      rw [LinearMap.sum_apply]
      have e : ∑ γ ∈ R x, ρ γ (NG.rt L n b f₀) = NG.rt L n b (∑ γ ∈ R x, NG.rt L n γ f₀) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum]
        exact Finset.sum_congr rfl fun γ hγ' => hrtc f₀ γ b (hγ γ hγ') hb
      rw [e, hχ x hx, map_smul]
      exact W'.smul_mem _ (hgen b hb)
    have := hle hy
    rwa [Submodule.mem_comap, LinearMap.sum_apply] at this
  have hdec : ∀ g : GAf L n, ∃ x ∈ {x : GAf L n | TrivOutside {v} x}, ∃ b ∈ {b : GAf L n | TrivOutside {v}ᶜ b},
      g = x * b := by
    intro g
    obtain ⟨x, b, hx, hb, e⟩ := GlobalTheory.T.finiteAdelicUnitary_eq_mul_trivOutside_place_and_at_place L n v g
    exact ⟨x, hx, b, hb, e⟩
  have hirr : ∀ S' : Submodule ℂ (GAf L n → a.W), S' ≤ S → (∀ g, ∀ x ∈ S', ρ g x ∈ S') → S' = ⊥ ∨ S' = S :=
    fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, fun g x hx => hst g x hx⟩ hle
  have heq := GlobalTheory.SphScalar.fixS_simple ρ S (fun g x hx => hS.1.stable g x hx) hirr (GlobalTheory.InertSph.Kv L n v)
    {x : GAf L n | TrivOutside {v} x} {b : GAf L n | TrivOutside {v}ᶜ b} hdec R (fun x hx => hR x hx)
    W' hW hW0 hWR hWb
  have hfW : f ∈ W' := by
    rw [heq]
    exact ⟨hfS, fun k hk => hfK k hk.1 hk.2⟩

  obtain ⟨C, cf, xs, hC⟩ := GlobalTheory.SatIso.heckeFunI_eq_sum Dv U h
    (GlobalTheory.SatInd.CosetFin.finite_inert_support L n v w Dv
      (GlobalTheory.SatInd.DCoset.finite_dcoset Dv.ϖ Dv.σw _ n Dv.unram)
      (GlobalTheory.InertUmax.mem_Umax_of_trivOutside_of_loc_integral L n v w Dv) U hU h hh)
  set c := Formalism.UG.SatU Dv.ϖ (Formalism.UG.qV (maximalRealSubfield L) v) h α with hc
  let T : Module.End ℂ (GAf L n → a.W) := ∑ d ∈ C, cf d • NG.rt L n (xs d)
  have hT : ∀ φ, heckeFunI L n U Dv h φ = T φ := by
    intro φ
    rw [hC a.W φ, LinearMap.sum_apply]
    rfl
  let E : Module.End ℂ (GAf L n → a.W) := T - c • (1 : Module.End ℂ (GAf L n → a.W))
  have hE : ∀ φ, E φ = T φ - c • φ := fun φ => rfl
  have hker : W' ≤ LinearMap.ker E := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨b, hb⟩, rfl⟩
    show E (NG.rt L n b f₀) = 0
    rw [hE, ← hT,
      GlobalTheory.InertSph.heckeFunI_rt U Dv h f₀ b hb,
      GlobalTheory.T.inertHeckeOperator_level_independent L n v w Dv hK U U' hU hU' a.W h hh.1 f₀ hf₀K, hH h hh, map_smul, sub_self]
  have := hker hfW
  rw [LinearMap.mem_ker, hE, sub_eq_zero] at this
  rw [hT]
  exact this

end GlobalTheory.InertSph
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicGLInductionOverPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicGLInductionOverPlaces
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open TensorProduct

namespace GlobalTheory.PlaceInd

open GlobalTheory.IdemSplit GlobalTheory.CongSplit GlobalTheory.InertUmax

variable (L : Type) [Field L] [NumberField L] [IsCMField L]

def epsOff (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) : AL L :=
  ∏ v ∈ T, (1 - idemAt L v)

theorem compAt_epsOff_of_mem {T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {w : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hw : w ∈ T) :
    compAt L w (epsOff L T) = 0 := by
  rw [epsOff, map_prod]
  exact Finset.prod_eq_zero hw (by rw [map_sub, map_one, compAt_idemAt_self, sub_self])

theorem epsOff_mem (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    epsOff L T ∈ ALint L :=
  Subring.prod_mem _ fun v _ => Subring.sub_mem _ (one_mem _) (idemAt_mem L v)

theorem epsOff_insert [DecidableEq (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))]
    {T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hv : v ∉ T) :
    epsOff L (insert v T) = (1 - idemAt L v) * epsOff L T := by
  rw [epsOff, Finset.prod_insert hv, epsOff]

theorem epsOff_mono {T T' : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} (h : T ⊆ T') :
    ∃ c ∈ ALint L, epsOff L T' = c * epsOff L T := by
  classical
  exact ⟨epsOff L (T' \ T), epsOff_mem L _, (Finset.prod_sdiff h).symm⟩

theorem exists_epsOff_mul_mem (z : AL L) :
    ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))), epsOff L T * z ∈ ALint L := by
  classical
  obtain ⟨S, Y, hY, h⟩ := GlobalTheory.FormInner.exists_int_off z
  refine ⟨S, ?_⟩
  have e : epsOff L S * z = epsOff L S * Y := by
    apply sub_eq_zero.1
    apply eq_zero_of_compAt
    intro w
    rw [map_sub, map_mul, map_mul]
    by_cases hw : w ∈ S
    · rw [compAt_epsOff_of_mem L hw]; ring
    · rw [h w hw]; ring
  rw [e]
  exact Subring.mul_mem _ (epsOff_mem L S) hY

theorem gaFold_split {n : ℕ} (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (g : GAf L n)
    (he : idemAt L v * idemAt L v = idemAt L v) (hσ : conjAL L (idemAt L v) = idemAt L v)
    (he' : (1 - idemAt L v) * (1 - idemAt L v) = 1 - idemAt L v)
    (hσ' : conjAL L (1 - idemAt L v) = 1 - idemAt L v) :
    g = gaFold he hσ g * gaFold he' hσ' g := by
  apply Subtype.ext; apply Units.ext
  show (g.1 : Matrix (Fin n) (Fin n) (AL L)) = fold (idemAt L v) _ * fold (1 - idemAt L v) _
  rw [fold_mul_fold he, ← add_smul, add_sub_cancel, one_smul]

theorem ind_epsOff (n N : ℕ) (p : GAf L n → Prop) (hC : ∀ κ, NG.Cong L n N κ → p κ)
    (hstep : ∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n),
      TrivOutside {v} x → TrivOutside {v}ᶜ y → p y → p (x * y))
    (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))) :
    ∀ g : GAf L n, (∀ i j, ∃ y ∈ ALint L, epsOff L T * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
      (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (N : AL L) * y) → p g := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    intro g hg
    have hg' : ∀ i j, ∃ y ∈ ALint L, (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j = (N : AL L) * y := by
      intro i j
      obtain ⟨y, hy, e⟩ := hg i j
      rw [epsOff, Finset.prod_empty, one_mul] at e
      exact ⟨y, hy, e⟩
    apply hC
    refine ⟨fun i j => ?_, hg'⟩
    obtain ⟨y, hy, e⟩ := hg' i j
    have h1 : (g.1 : Matrix (Fin n) (Fin n) (AL L)) i j =
        (1 : Matrix (Fin n) (Fin n) (AL L)) i j + (N : AL L) * y := by rw [← e]; ring
    rw [h1]
    exact Subring.add_mem _ (one_apply_mem L i j) (Subring.mul_mem _ (natCast_mem _ _) hy)
  | @insert v T hv ih =>
    intro g hg
    have he : idemAt L v * idemAt L v = idemAt L v := idemAt_mul_self L v
    have he' : (1 - idemAt L v) * (1 - idemAt L v) = 1 - idemAt L v := by
      rw [sub_mul, one_mul, mul_sub, mul_one, he, sub_self, sub_zero]
    have hσ : conjAL L (idemAt L v) = idemAt L v := conjAL_idemAt L v
    have hσ' : conjAL L (1 - idemAt L v) = 1 - idemAt L v := by rw [map_sub, map_one, hσ]
    have hx : TrivOutside {v} (gaFold he hσ g) := by
      intro w hw
      have hw' : w ≠ v := by simpa using hw
      ext i j
      rw [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_mul, map_sub, map_one,
        compAt_idemAt_ne L v hw', compAt_one_apply]
      simp
    have hy : TrivOutside {v}ᶜ (gaFold he' hσ' g) := by
      intro w hw
      have hw' : w = v := by simpa using hw
      rw [hw']
      ext i j
      simp only [Matrix.map_apply, gaFold_val, fold_apply, map_add (f := _), map_mul, map_sub, map_one,
        compAt_idemAt_self, compAt_one_apply]
      simp
    have hp : p (gaFold he' hσ' g) := by
      apply ih
      intro i j
      obtain ⟨y, hy, eq⟩ := hg i j
      refine ⟨y, hy, ?_⟩
      rw [epsOff_insert L hv] at eq
      rw [gaFold_val, fold_apply]
      linear_combination eq
    have := hstep v _ _ hx hy hp
    rwa [← gaFold_split L v g he hσ he' hσ'] at this

theorem induction_places : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ), 0 < N → ∀ p : GAf L n → Prop, (∀ κ, NG.Cong L n N κ → p κ) → (∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n), TrivOutside {v} x → TrivOutside {v}ᶜ y → p y → p (x * y)) → ∀ g, p g := by
  intro L _ _ _ n N hN p hC hstep g
  classical
  have hN' : (N : L) ≠ 0 := Nat.cast_ne_zero.2 hN.ne'
  obtain ⟨u, hu⟩ : ∃ u : AL L, (N : AL L) * u = 1 :=
    ⟨algebraMap L (AL L) (N : L)⁻¹, by
      rw [← map_natCast (algebraMap L (AL L)), ← map_mul, mul_inv_cancel₀ hN', map_one]⟩
  have hT : ∀ q : Fin n × Fin n, ∃ T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield L))),
      epsOff L T * (u * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) q.1 q.2 -
        (1 : Matrix (Fin n) (Fin n) (AL L)) q.1 q.2)) ∈ ALint L :=
    fun q => exists_epsOff_mul_mem L _
  choose T hT using hT
  refine ind_epsOff L n N p hC hstep (Finset.univ.biUnion T) g fun i j => ?_
  obtain ⟨c, hc, e⟩ := epsOff_mono L (Finset.subset_biUnion_of_mem T (Finset.mem_univ (i, j)))
  refine ⟨c * (epsOff L (T (i, j)) * (u * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j))), Subring.mul_mem _ hc (hT (i, j)), ?_⟩
  rw [e]
  linear_combination (-(c * epsOff L (T (i, j)) * ((g.1 : Matrix (Fin n) (Fin n) (AL L)) i j -
    (1 : Matrix (Fin n) (Fin n) (AL L)) i j))) * hu

end GlobalTheory.PlaceInd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteAdelicGLInductionOverPlacesStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteAdelicGL_induction_over_places : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (N : ℕ), 0 < N → ∀ p : GAf L n → Prop, (∀ κ, NG.Cong L n N κ → p κ) → (∀ (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (x y : GAf L n), TrivOutside {v} x → TrivOutside {v}ᶜ y → p y → p (x * y)) → ∀ g, p g := by
  first | exact @GlobalTheory.PlaceInd.induction_places | exact GlobalTheory.PlaceInd.induction_places | (intros; apply GlobalTheory.PlaceInd.induction_places <;> assumption)
end
end
