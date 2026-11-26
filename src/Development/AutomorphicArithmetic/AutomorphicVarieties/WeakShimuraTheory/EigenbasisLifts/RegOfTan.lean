module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.AwAvg
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoCaten
public import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.ExistsDeterminantPairMapOfAlgHom
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.MonomialRepresentations.RegOfDim
open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.regOfDim :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (J : Ideal R), J ≠ ⊤ →
      ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ J) → J = ⊥ := by
  intro R _ _ _ J hJ hdim
  have hR := ringKrullDim_le_spanFinrank_maximalIdeal R
  have hq := ringKrullDim_quotient_le J
  have heq : ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) = ringKrullDim R :=
    le_antisymm (hdim.trans hq) hR
  have hJeq : ringKrullDim (R ⧸ J) = ((IsLocalRing.maximalIdeal R).spanFinrank : WithBot ℕ∞) :=
    le_antisymm (hq.trans hR) hdim
  haveI : IsRegularLocalRing R := ⟨heq⟩
  haveI := PI.UnitaryGroupMassFormula.RLRS.IsRegularLocalRing.isDomain R
  by_contra hne
  obtain ⟨r, hrJ, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hnz : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hr0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hnz
  have hsub : Ideal.span {r} ≤ J := (Ideal.span_singleton_le_iff_mem J).2 hrJ
  have h2 : ringKrullDim (R ⧸ J) ≤ ringKrullDim (R ⧸ Ideal.span {r}) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hsub) (Ideal.Quotient.factor_surjective hsub)
  have h3 : ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ J) := by
    calc ringKrullDim (R ⧸ J) + 1 ≤ ringKrullDim (R ⧸ Ideal.span {r}) + 1 := by gcongr
      _ ≤ ringKrullDim R := h1
      _ = ringKrullDim (R ⧸ J) := by rw [hJeq, heq]
  rw [hJeq] at h3
  norm_cast at h3
  omega
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.TanEmb
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.CotDer
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.cotDer :
    ∀ (O R : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing R] [IsLocalRing R] [Algebra O R], Function.Injective (algebraMap O (ResidueField R)) → Algebra.IsAlgebraic O (ResidueField R) →
        ∃ d : Derivation O R (CotangentSpace R), ∀ a : maximalIdeal R, d a = (maximalIdeal R).toCotangent a := by
  intro O R _ _ _ _ _ _ hinj halg
  haveI : FaithfulSMul O (ResidueField R) := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  letI : Algebra (FractionRing O) (ResidueField R) := FractionRing.liftAlgebra O _
  haveI := FractionRing.isScalarTower_liftAlgebra O (ResidueField R)
  haveI := halg
  haveI : Algebra.IsAlgebraic (FractionRing O) (ResidueField R) :=
    Algebra.IsAlgebraic.extendScalars (IsFractionRing.injective O (FractionRing O))
  haveI : Algebra.FormallyEtale (FractionRing O) (ResidueField R) := Algebra.FormallyEtale.of_isSeparable _ _
  haveI : Algebra.FormallyEtale O (FractionRing O) := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors O)
  haveI : Algebra.FormallyEtale O (ResidueField R) := Algebra.FormallyEtale.comp O (FractionRing O) _
  have hle : maximalIdeal R ^ 2 ≤ maximalIdeal R := Ideal.pow_le_self two_ne_zero
  let g : R ⧸ maximalIdeal R ^ 2 →ₐ[O] ResidueField R := Ideal.Quotient.factorₐ O hle
  have hgmk : ∀ a : R, g (Ideal.Quotient.mk _ a) = residue R a := fun a => rfl
  have hg : Function.Surjective g := by
    intro x
    obtain ⟨a, rfl⟩ := residue_surjective x
    exact ⟨_, hgmk a⟩
  have hker : ∀ x, g x = 0 → x ∈ (maximalIdeal R).cotangentIdeal := by
    intro x hx
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [hgmk, residue_eq_zero_iff] at hx
    exact Ideal.mk_mem_cotangentIdeal.mpr hx
  have hnil : IsNilpotent (RingHom.ker (g : R ⧸ maximalIdeal R ^ 2 →+* ResidueField R)) := by
    refine ⟨2, le_bot_iff.mp ?_⟩
    refine (Ideal.pow_right_mono (fun x hx => hker x hx) 2).trans ?_
    rw [Ideal.cotangentIdeal_square]
  let s := Algebra.FormallySmooth.liftOfSurjective (AlgHom.id O (ResidueField R)) g hg hnil
  have hs : ∀ x, g (s x) = x := fun x => Algebra.FormallySmooth.liftOfSurjective_apply _ g hg hnil x
  let φ := s.comp (IsScalarTower.toAlgHom O R (ResidueField R))
  have e : (Ideal.Quotient.mkₐ O (maximalIdeal R).cotangentIdeal).comp φ
      = IsScalarTower.toAlgHom O R ((R ⧸ maximalIdeal R ^ 2) ⧸ (maximalIdeal R).cotangentIdeal) := by
    ext r
    show Ideal.Quotient.mk _ (s (algebraMap R (ResidueField R) r))
      = Ideal.Quotient.mk _ (Ideal.Quotient.mk (maximalIdeal R ^ 2) r)
    rw [Ideal.Quotient.eq]
    apply hker
    rw [map_sub, hs, hgmk, ResidueField.algebraMap_eq, sub_self]
  let D := derivationToSquareZeroOfLift (maximalIdeal R).cotangentIdeal
    (Ideal.cotangentIdeal_square _) φ e
  refine ⟨-(((maximalIdeal R).cotangentEquivIdeal.symm :
      (maximalIdeal R).cotangentIdeal →ₗ[R] (maximalIdeal R).Cotangent).compDer D), fun a => ?_⟩
  have hφ : φ a = 0 := by
    show s (algebraMap R (ResidueField R) a) = 0
    rw [ResidueField.algebraMap_eq, (residue_eq_zero_iff _).mpr a.2, map_zero]
  show -((maximalIdeal R).cotangentEquivIdeal.symm (D a)) = _
  rw [neg_eq_iff_eq_neg, ← map_neg, LinearEquiv.symm_apply_eq]
  ext
  simp only [D, derivationToSquareZeroOfLift_apply, hφ, zero_sub, Ideal.cotangentEquivIdeal_apply, map_neg,
    Submodule.coe_neg, Ideal.toCotangent_to_quotient_square]
  rfl
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem dual_der (O R K : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [Algebra O R] [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K]
    (y : R →ₐ[O] K) (hy : ∀ a ∈ maximalIdeal R, y a = 0) :
    ∃ (D : Fin (maximalIdeal R).spanFinrank → R →ₗ[O] K) (r : Fin (maximalIdeal R).spanFinrank → R),
      (∀ i, D i ∈ PtDer y K) ∧ ∀ i j, D i (r j) = if j = i then 1 else 0 := by
  classical
  let yb : ResidueField R →+* K :=
    Ideal.Quotient.lift (maximalIdeal R) y.toRingHom (fun a ha => hy a ha)
  have hyb : ∀ f : R, yb (algebraMap R (ResidueField R) f) = y f := fun f => rfl
  have h1 : ∀ c : O, yb (algebraMap O (ResidueField R) c) = algebraMap O K c := by
    intro c
    rw [← y.commutes c]
    rfl
  let ya : ResidueField R →ₐ[O] K := { yb with commutes' := h1 }
  have hyinj : Function.Injective yb := yb.injective
  have hinj : Function.Injective (algebraMap O (ResidueField R)) := by
    intro a b hab
    apply FaithfulSMul.algebraMap_injective O K
    rw [← h1, ← h1, hab]
  have halg : Algebra.IsAlgebraic O (ResidueField R) :=
    Algebra.IsAlgebraic.of_injective ya hyinj
  obtain ⟨d, hd⟩ := UpperTheory.V.Ws.Eb.cotDer O R hinj halg
  have hn : Module.finrank (ResidueField R) (CotangentSpace R) = (maximalIdeal R).spanFinrank :=
    (IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace R).symm
  let b := Module.finBasisOfFinrankEq (ResidueField R) (CotangentSpace R) hn
  have hsurj : ∀ j, ∃ a : maximalIdeal R, (maximalIdeal R).toCotangent a = b j :=
    fun j => (maximalIdeal R).toCotangent_surjective (b j)
  choose a ha using hsurj
  have hsm : ∀ (r : R) (v : CotangentSpace R) i,
      yb (b.coord i (r • v)) = y r * yb (b.coord i v) := by
    intro r v i
    rw [← algebraMap_smul (ResidueField R) r v, map_smul, smul_eq_mul, map_mul, hyb]
  let D : Fin (maximalIdeal R).spanFinrank → R →ₗ[O] K := fun i =>
    { toFun := fun f => yb (b.coord i (d f))
      map_add' := by
        intro f g
        simp only [map_add (f := _)]
      map_smul' := by
        intro c f
        rw [RingHom.id_apply, Algebra.smul_def, Derivation.leibniz, Derivation.map_algebraMap,
          smul_zero, add_zero, hsm, y.commutes, Algebra.smul_def] }
  refine ⟨D, fun j => (a j : R), ?_, ?_⟩
  · intro i
    intro f g
    show yb (b.coord i (d (f * g))) = y f • yb (b.coord i (d g)) + y g • yb (b.coord i (d f))
    rw [Derivation.leibniz, map_add (f := _), map_add (f := _), hsm, hsm, smul_eq_mul, smul_eq_mul]
  · intro i j
    show yb (b.coord i (d (a j : R))) = _
    rw [hd, ha, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp

theorem UpperTheory.V.Ws.Eb.tanEmb :
    ∀ (O B K : Type) [CommRing O] [IsDomain O] [CharZero O] [CommRing B] [IsNoetherianRing B] [Algebra O B] [Field K] [Algebra O K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (x : B →ₐ[O] K) (p : Ideal B) [p.IsPrime], p = RingHom.ker x →
        ∀ N : ℕ, Module.rank K (PtDer x K) ≤ N → (maximalIdeal (Localization.AtPrime p)).spanFinrank ≤ N := by
  intro O B K _ _ _ _ _ _ _ _ _ _ x p _ hp N hN
  classical
  let R := Localization.AtPrime p
  have hker : ∀ b : B, b ∈ p ↔ x b = 0 := by
    intro b
    rw [hp]
    exact Iff.rfl
  have hunit : ∀ s : p.primeCompl, IsUnit (x s) := by
    intro s
    apply IsUnit.mk0
    intro h0
    exact s.2 ((hker s).2 h0)
  let y : R →ₐ[O] K := IsLocalization.liftAlgHom (M := p.primeCompl) (f := x) hunit
  have hyx : ∀ b : B, y (algebraMap B R b) = x b := fun b => IsLocalization.lift_eq _ _
  have hy : ∀ a ∈ maximalIdeal R, y a = 0 := by
    intro a ha
    obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
    have hb : b ∈ p := by
      rwa [IsLocalization.AtPrime.mk'_mem_maximal_iff R p] at ha
    have h1 := congrArg y (IsLocalization.mk'_spec R b s)
    rw [map_mul, hyx, hyx, (hker b).1 hb] at h1
    exact (mul_eq_zero.mp h1).resolve_right (hunit s).ne_zero
  obtain ⟨D, r, hD, hDr⟩ := dual_der O R K y hy
  have hDl : ∀ i (u w : R), D i (u * w) = y u * D i w + y w * D i u := by
    intro i u w
    have := hD i u w
    rwa [smul_eq_mul, smul_eq_mul] at this
  let L : B →ₗ[O] R := (IsScalarTower.toAlgHom O B R).toLinearMap
  have hL : ∀ b, L b = algebraMap B R b := fun b => rfl
  have hmem : ∀ i, (D i).comp L ∈ PtDer x K := by
    intro i f g
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearMap.comp_apply, hL, hL, hL, map_mul,
      hDl, hyx, hyx, smul_eq_mul, smul_eq_mul]
  let v : Fin (maximalIdeal R).spanFinrank → PtDer x K := fun i => ⟨(D i).comp L, hmem i⟩
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    let E : R → K := fun a => ∑ i, g i * D i a
    have hE : ∀ u w : R, E (u * w) = y u * E w + y w * E u := by
      intro u w
      simp only [E, hDl, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
      congr 1 <;> refine Finset.sum_congr rfl (fun i _ => ?_) <;> ring
    have hB : ∀ b : B, E (algebraMap B R b) = 0 := by
      intro b
      have := congrArg (fun w : PtDer x K => (w : B →ₗ[O] K) b) hg
      simpa [v, E, hL] using this
    have hR : ∀ a : R, E a = 0 := by
      intro a
      obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a
      have h1 := hB b
      rw [← IsLocalization.mk'_spec R b s, hE, hB, mul_zero, zero_add, hyx] at h1
      exact (mul_eq_zero.mp h1).resolve_left (hunit s).ne_zero
    intro j
    have := hR (r j)
    simpa [E, hDr] using this
  have hc := hli.cardinal_le_rank
  rw [Cardinal.mk_fintype, Fintype.card_fin] at hc
  exact_mod_cast hc.trans hN
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DerLam
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem derLam_dense {O : Type} [CommRing O] [IsLocalRing O] {σ : Type} [Finite σ] (n : ℕ)
    (a : MvPowerSeries σ O) :
    ∃ b ∈ Algebra.adjoin O (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ O)),
      a - b ∈ maximalIdeal (MvPowerSeries σ O) ^ n := by
  have hX : ∀ i : σ, (AlgHom.id O (MvPowerSeries σ O)) (MvPowerSeries.X i) ∈ maximalIdeal (MvPowerSeries σ O) := by
    intro i
    rw [AlgHom.id_apply, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]
    simp
  have key := GlobalTheory.algHom_sub_aeval_truncTotal_mem (AlgHom.id O (MvPowerSeries σ O)) hX n a
  simp only [AlgHom.id_apply] at key
  refine ⟨_, ?_, key⟩
  rw [Algebra.adjoin_range_eq_range_aeval]
  exact ⟨_, rfl⟩

private theorem ptDer_eq_zero_of_vanish_on_X {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ)
    (x : MvPowerSeries (Fin N) c.O →ₐ[c.O] PadicAlgCl l)
    (D : MvPowerSeries (Fin N) c.O →ₗ[c.O] PadicAlgCl l) (hD : D ∈ PtDer x (PadicAlgCl l))
    (h0 : ∀ i, D (MvPowerSeries.X i) = 0) (a : MvPowerSeries (Fin N) c.O) : D a = 0 := by
  have hmul : ∀ f g, D (f * g) = x f • D g + x g • D f := hD
  have h1 : D 1 = 0 := by
    have h := hmul 1 1
    simp only [mul_one, map_one, one_smul] at h
    linear_combination (-1 : PadicAlgCl l) * h
  let y : MvPowerSeries (Fin N) c.O →ₐ[c.O] DualNumber (PadicAlgCl l) :=
    { toFun := fun f => TrivSqZeroExt.inl (x f) + TrivSqZeroExt.inr (D f)
      map_one' := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp [h1]
      map_mul' := by
        intro f g
        refine TrivSqZeroExt.ext ?_ ?_
        · simp
        · simp only [TrivSqZeroExt.snd_mul, TrivSqZeroExt.fst_add, TrivSqZeroExt.snd_add,
            TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl, TrivSqZeroExt.fst_inr, TrivSqZeroExt.snd_inr,
            add_zero, zero_add, hmul, smul_eq_mul, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
          ring
      map_zero' := by
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp
      map_add' := by
        intro f g
        refine TrivSqZeroExt.ext ?_ ?_ <;> simp <;> ring
      commutes' := by
        intro r
        refine TrivSqZeroExt.ext ?_ ?_
        · simp only [TrivSqZeroExt.fst_add, TrivSqZeroExt.fst_inl, TrivSqZeroExt.fst_inr, add_zero,
            AlgHom.commutes]
          rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r]
          rfl
        · simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
          rw [Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r, map_smul, h1,
            smul_zero]
          show (0 : PadicAlgCl l) = r • (0 : PadicAlgCl l)
          rw [smul_zero] }
  haveI := co_mvps c.O c.O (Fin N)
  have key := derZero c (MvPowerSeries (Fin N) c.O) y (Set.range MvPowerSeries.X)
    (fun n b => derLam_dense n b) (by rintro _ ⟨i, rfl⟩; simp [y, h0]) a
  simpa [y] using key

theorem UpperTheory.V.Ws.Eb.derLam :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (x : MvPowerSeries (Fin N) c.O →ₐ[c.O] PadicAlgCl l), Module.rank (PadicAlgCl l) (PtDer x (PadicAlgCl l)) ≤ N := by
  intro l _ c N x
  let Φ : PtDer x (PadicAlgCl l) →ₗ[PadicAlgCl l] (Fin N → PadicAlgCl l) :=
    { toFun := fun D i => (D : MvPowerSeries (Fin N) c.O →ₗ[c.O] PadicAlgCl l) (MvPowerSeries.X i)
      map_add' := by
        intro D D'
        rfl
      map_smul' := by
        intro k D
        rfl }
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro D hD
    apply Subtype.ext
    apply LinearMap.ext
    intro a
    exact ptDer_eq_zero_of_vanish_on_X c N x D D.2 (fun i => congrFun hD i) a
  calc Module.rank (PadicAlgCl l) (PtDer x (PadicAlgCl l))
      ≤ Module.rank (PadicAlgCl l) (Fin N → PadicAlgCl l) := LinearMap.rank_le_of_injective Φ hinj
    _ = N := by simp
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DimLow
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.DimLeOfInt
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem dim_le_of_int (R A : Type) [CommRing R] [CommRing A] [Algebra R A] [Algebra.IsIntegral R A] :
    ringKrullDim A ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R A)) fun _ _ h =>
    Ideal.IsIntegral.comap_lt_comap (R := R) h

theorem UpperTheory.V.Ws.Eb.htLow :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (T : Type) [CommRing T] [IsDomain T] [Algebra c.O T] [IsCO c.O T] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] T), Function.Injective f → (f : MvPowerSeries (Fin N) c.O →+* T).Finite → ∀ x : T →ₐ[c.O] PadicAlgCl l, (N : ℕ∞) ≤ (RingHom.ker x).height := by
  intro l _ c N T _ _ _ _ f hinj hfin x
  haveI : IsAdicComplete (maximalIdeal c.O) c.O := (UpperTheory.V.Base.dvrFacts l c.O).2.2.2.1
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l])).2 inferInstance
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ_[l]) (UpperTheory.V.Base.dvrFacts l c.O).1
  haveI : FaithfulSMul c.O (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI := UpperTheory.V.W.exists_algebraicPoint_of_groupDeterminant c.O T (PadicAlgCl l) x
  haveI : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  have h1 := UpperTheory.V.Alg.co_caten c.O T (RingHom.ker x)
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible c.O
  have h2 := (UpperTheory.V.AlgebraTools.mvPowerSeries_cotInd c.O ϖ hϖ (Fin N)).2.1
  have h3 : ringKrullDim T = ringKrullDim (MvPowerSeries (Fin N) c.O) := by
    letI : Algebra (MvPowerSeries (Fin N) c.O) T := (f : MvPowerSeries (Fin N) c.O →+* T).toAlgebra
    haveI : Module.Finite (MvPowerSeries (Fin N) c.O) T := hfin
    exact ReciprocityTheory.CA.ringKrullDim_eq_of_isIntegral_of_injective hinj
  have h4 : ringKrullDim (T ⧸ RingHom.ker x) ≤ 1 := by
    rw [ringKrullDim_eq_of_ringEquiv (Ideal.quotientKerEquivRange x).toRingEquiv,
      ← IsDiscreteValuationRing.ringKrullDim_eq_one c.O]
    exact dim_le_of_int c.O x.range
  rw [h3, h2, Fintype.card_fin] at h1
  have h5 : ((N + 1 : ℕ) : WithBot ℕ∞) ≤ ((RingHom.ker x).height : WithBot ℕ∞) + 1 := by
    rw [← h1]; exact add_le_add le_rfl h4
  have h6 : (N : ℕ∞) + 1 ≤ (RingHom.ker x).height + 1 := by exact_mod_cast h5
  exact (ENat.add_le_add_iff_right ENat.one_ne_top).1 h6
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

theorem UpperTheory.V.Ws.Eb.dimLow :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] B) (J : Ideal B), ((Ideal.Quotient.mk J).comp (f : MvPowerSeries (Fin N) c.O →+* B)).Finite → (∀ a, a ≠ 0 → ∀ b, f a * b ∈ J → b ∈ J) →
        ∀ (x : B →ₐ[c.O] PadicAlgCl l) (p : Ideal B) [p.IsPrime], p = RingHom.ker x → J ≤ p → (N : WithBot ℕ∞) ≤ ringKrullDim (Localization.AtPrime p ⧸ J.map (algebraMap B (Localization.AtPrime p))) := by
  intro l _ c N B _ _ _ f J hfin hreg x p _ hpx hJp
  obtain ⟨P, hP, hPp⟩ := Ideal.exists_minimalPrimes_le hJp
  haveI hPprime : P.IsPrime := hP.1.1
  have hJP : J ≤ P := hP.1.2
  haveI : IsCO c.O (B ⧸ P) :=
    co_quot c.O B (B ⧸ P) (Ideal.Quotient.mkₐ c.O P) Ideal.Quotient.mk_surjective
  set g : MvPowerSeries (Fin N) c.O →ₐ[c.O] B ⧸ P := (Ideal.Quotient.mkₐ c.O P).comp f with hg
  have hinj : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hne
    have hmem : f a ∈ P := by
      rw [← Ideal.Quotient.eq_zero_iff_mem]
      exact ha
    obtain ⟨y, hyJ, hy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hP hmem
    exact hyJ (hreg a hne y hy)
  have hfinP : (g : MvPowerSeries (Fin N) c.O →+* B ⧸ P).Finite := by
    have h2 := (RingHom.Finite.of_surjective _ (Ideal.Quotient.factor_surjective hJP)).comp hfin
    convert h2 using 1
    exact RingHom.ext fun a => rfl
  have hxP : ∀ a ∈ P, x a = 0 := fun a ha => by
    have h3 : a ∈ RingHom.ker x := hpx ▸ hPp ha
    exact h3
  set xb : B ⧸ P →ₐ[c.O] PadicAlgCl l := Ideal.Quotient.liftₐ P x hxP with hxb
  have hxbmk : ∀ b, xb (Ideal.Quotient.mk P b) = x b := fun b => rfl
  have hht := htLow c N (B ⧸ P) g hinj hfinP xb
  set q : Ideal (B ⧸ P) := RingHom.ker xb with hq
  haveI : q.IsPrime := RingHom.ker_isPrime _
  have hpq : p = Ideal.comap (Ideal.Quotient.mk P) q := by
    ext b
    rw [hpx, Ideal.mem_comap, hq, RingHom.mem_ker, RingHom.mem_ker, hxbmk]
  let φ := Localization.localRingHom p q (Ideal.Quotient.mk P) hpq
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl z
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective r
    obtain ⟨s', hs'⟩ := Ideal.Quotient.mk_surjective (s : B ⧸ P)
    have hs'p : s' ∈ p.primeCompl := by
      intro h
      apply s.2
      rw [hpq] at h
      rw [← hs']
      exact h
    refine ⟨IsLocalization.mk' (Localization.AtPrime p) r' ⟨s', hs'p⟩, ?_⟩
    rw [Localization.localRingHom_mk']
    congr 1
    exact Subtype.ext hs'
  have hker : ∀ a ∈ J.map (algebraMap B (Localization.AtPrime p)), φ a = 0 := by
    intro a ha
    have hle : J.map (algebraMap B (Localization.AtPrime p)) ≤ RingHom.ker φ := by
      rw [Ideal.map_le_iff_le_comap]
      intro b hb
      rw [Ideal.mem_comap, RingHom.mem_ker]
      rw [Localization.localRingHom_to_map]
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hJP hb), map_zero]
    exact hle ha
  have hψ := Ideal.Quotient.lift_surjective_of_surjective _ hker hφ
  have hdim := ringKrullDim_le_of_surjective _ hψ
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q (Localization.AtPrime q)] at hdim
  calc (N : WithBot ℕ∞) ≤ (q.height : WithBot ℕ∞) := by exact_mod_cast hht
    _ ≤ _ := hdim
end

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial Matrix UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Eb GlobalTheory.GalOfCusp

private theorem rank_le_res {O A B K : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing B] [Algebra O B]
    [Field K] [Algebra O K] (f : A →ₐ[O] B) (x : B →ₐ[O] K)
    (h : ∀ x' : B →ₐ[O] DualNumber K, (∀ b, (x' b).fst = x b) → (∀ a, (x' (f a)).snd = 0) → ∀ b, (x' b).snd = 0) :
    Module.rank K (PtDer x K) ≤ Module.rank K (PtDer (x.comp f) K) := by
  classical
  let F : PtDer x K →ₗ[K] PtDer (x.comp f) K :=
    { toFun := fun D => ⟨(D : B →ₗ[O] K).comp f.toLinearMap, by
        intro a a'
        have hD := D.2 (f a) (f a')
        simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_mul, AlgHom.comp_apply]
        simpa using hD⟩
      map_add' := fun D E => by
        ext a
        simp
      map_smul' := fun c D => by
        ext a
        simp }
  refine LinearMap.rank_le_of_injective F ?_
  have key : ∀ G : PtDer x K, F G = 0 → G = 0 := by
    intro G hG
    have hmul : ∀ b b' : B, (G : B →ₗ[O] K) (b * b') = x b • (G : B →ₗ[O] K) b' + x b' • (G : B →ₗ[O] K) b :=
      G.2
    have h1 : (G : B →ₗ[O] K) 1 = 0 := by
      have := hmul 1 1
      simp only [map_one, one_smul, mul_one] at this
      have h2 : (G : B →ₗ[O] K) 1 + (G : B →ₗ[O] K) 1 = (G : B →ₗ[O] K) 1 + 0 := by
        rw [add_zero]; exact this.symm
      exact add_left_cancel h2
    have hc : ∀ r : O, (G : B →ₗ[O] K) (algebraMap O B r) = 0 := by
      intro r
      rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]
    have halg : ∀ r : O, algebraMap O (DualNumber K) r = TrivSqZeroExt.inl (algebraMap O K r) := fun r => rfl
    let y : B →ₐ[O] DualNumber K :=
      { toFun := fun b => TrivSqZeroExt.inl (x b) + TrivSqZeroExt.inr ((G : B →ₗ[O] K) b)
        map_one' := by
          ext <;> simp [h1]
        map_mul' := fun b b' => by
          ext
          · simp
          · simp [hmul b b', smul_eq_mul, mul_comm, add_comm]
        map_zero' := by
          ext <;> simp
        map_add' := fun b b' => by
          ext <;> simp [add_comm, add_left_comm, add_assoc]
        commutes' := fun r => by
          rw [halg]
          ext
          · simp
          · simp [hc] }
    have hz := h y (fun b => by simp [y]) (fun a => by
      have := congrArg (fun H : PtDer (x.comp f) K => (H : A →ₗ[O] K) a) hG
      simpa [F, y] using this)
    ext b
    simpa [y] using hz b
  intro D E hDE
  have := key (D - E) (by rw [map_sub, hDE, sub_self])
  exact sub_eq_zero.1 this

theorem UpperTheory.V.Ws.Eb.regOfTan :
    ∀ {l : ℕ} [Fact l.Prime] (c : Coef l) (N : ℕ) (B : Type) [CommRing B] [Algebra c.O B] [IsCO c.O B] (f : MvPowerSeries (Fin N) c.O →ₐ[c.O] B) (J : Ideal B), ((Ideal.Quotient.mk J).comp (f : MvPowerSeries (Fin N) c.O →+* B)).Finite → (∀ a, a ≠ 0 → ∀ b, f a * b ∈ J → b ∈ J) →
        ∀ x : B →ₐ[c.O] PadicAlgCl l, J ≤ RingHom.ker x → (∀ x' : B →ₐ[c.O] DualNumber (PadicAlgCl l), (∀ b, (x' b).fst = x b) → (∀ a, (x' (f a)).snd = 0) → ∀ b, (x' b).snd = 0) → ∀ q : Ideal B, q.IsPrime → q ≤ RingHom.ker x → J ≤ q := by
  intro l _ c N B _ _ _ f J hfin hreg x hJ htan q hq hqx
  haveI : Algebra.IsAlgebraic ℤ_[l] (PadicAlgCl l) :=
    (IsFractionRing.comap_isAlgebraic_iff (A := ℤ_[l]) (K := ℚ_[l])).2 inferInstance
  haveI : Algebra.IsAlgebraic c.O (PadicAlgCl l) :=
    Algebra.IsAlgebraic.extendScalars (R := ℤ_[l]) (UpperTheory.V.Base.dvrFacts l c.O).1
  haveI : FaithfulSMul c.O (PadicAlgCl l) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI hp : (RingHom.ker x).IsPrime := RingHom.ker_isPrime _
  have h1 := tanEmb c.O B (PadicAlgCl l) x (RingHom.ker x) rfl N
    ((rank_le_res f x htan).trans (derLam c N (x.comp f)))
  have h2 := dimLow c N B f J hfin hreg x (RingHom.ker x) rfl hJ
  have hne : J.map (algebraMap B (Localization.AtPrime (RingHom.ker x))) ≠ ⊤ := by
    intro ht
    have := Ideal.map_mono (f := algebraMap B (Localization.AtPrime (RingHom.ker x))) hJ
    rw [ht, Localization.AtPrime.map_eq_maximalIdeal] at this
    exact (maximalIdeal.isMaximal _).ne_top (top_le_iff.1 this)
  have h3 := UpperTheory.V.AlgebraTools.regOfDim _ _ hne (le_trans (by exact_mod_cast h1) h2)
  intro a ha
  have h4 : algebraMap B (Localization.AtPrime (RingHom.ker x)) a = 0 := by
    have := Ideal.mem_map_of_mem (algebraMap B (Localization.AtPrime (RingHom.ker x))) ha
    rw [h3] at this
    exact this
  obtain ⟨s, hs⟩ := (IsLocalization.map_eq_zero_iff (RingHom.ker x).primeCompl _ a).1 h4
  have h5 : (s : B) * a ∈ q := by rw [hs]; exact q.zero_mem
  exact (hq.mem_or_mem h5).resolve_left fun h => s.2 (hqx h)
