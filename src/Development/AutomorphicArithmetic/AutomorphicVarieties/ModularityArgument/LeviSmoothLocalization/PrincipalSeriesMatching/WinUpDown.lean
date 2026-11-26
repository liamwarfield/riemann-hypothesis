module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.GammaLaurentFactors.CrossG
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.MatchBCX
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.OfSupportHolds
public import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalIdeles.UnlSph

@[expose] public section

attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing UpperTheory.V.Pr.IsCD.complete UpperTheory.V.Pr.IsCD.isLocalHom UpperTheory.V.Pr.IsCD.fin

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.WinUpDown
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.UpDownX
open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
open Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.HenQ UpperTheory.V.Z.Bc UpperTheory.V.Published
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL UpperTheory.Zero.LLC UpperTheory.V.Z.Inf
open GroundTheory.Global.SemiLocal
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

private theorem unr_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : kˣ →* ℂˣ} (ha : IsUnram a) (hb : IsUnram b) : IsUnram (a * b⁻¹) := by
  intro x hx
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, ha x hx, hb x hx, inv_one, one_mul]

private theorem unr_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    IsUnram (1 : kˣ →* ℂˣ) := by
  unfold IsUnram
  simp

private theorem loc_pow' {K : Type} [Field K] [NumberField K] (η : HChar K) (v : HeightOneSpectrum (𝓞 K)) (j : ℕ) :
    (η ^ j).loc v = η.loc v ^ j := by
  induction j with
  | zero => rw [pow_zero, pow_zero]; ext; rfl
  | succ j ih => rw [pow_succ, pow_succ, ← ih]; ext; rfl

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.upDownX :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.UpDownX := by
  intro K L _ _ _ _ _ _ _ _ hp n hn π P hBC v s s' hs hs'
  obtain ⟨η, hη, hloc⟩ := normCnt K L hp
  have hM := matchBCX K L hp n hn π P hBC η hη v s s' hs hs'
  have hK := (polFacts (v.adicCompletion K)).2.2.2
  refine ⟨fun hT w ζ hζ => ?_, fun ξ hξ => ?_⟩
  · obtain ⟨χ, hχ, hu⟩ := ((upDown K L hp n hn π P hBC v).1 hT w).2 (s' w) (hs' w) ζ hζ.1 hζ.2
    have hL := polFacts (w.1.adicCompletion L)
    have hf : 0 < fdeg w := (normVal K L v w 1).2.2.1
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq
      ((((ζ * χ.comp (nm w)) (unif (w.1.adicCompletion L)) : ℂˣ) : ℂ)⁻¹) hf
    have hbx : (((ζ * χ.comp (nm w)) (unif (w.1.adicCompletion L)) : ℂˣ) : ℂ) * x ^ fdeg w = 1 := by
      rw [hx]; exact mul_inv_cancel₀ (Units.ne_zero _)
    have h0 := congrArg (Polynomial.eval x) (hM χ hχ)
    rw [eval_prod, eval_prod] at h0
    have h1 : eval x ((pol (s' w) (χ.comp (nm w))).comp (X ^ fdeg w)) = 0 := by
      rw [eval_comp, eval_pow, eval_X]
      exact ((hL.2.2.2 (s' w) (χ.comp (nm w))).2.2.1 _).2 ⟨ζ, hζ, hu, hbx⟩
    rw [Finset.prod_eq_zero (Finset.mem_univ w) h1, Finset.prod_eq_zero_iff] at h0
    obtain ⟨j, -, hj⟩ := h0
    obtain ⟨ξ, hξ, hμ, hax⟩ := ((hK s _).2.2.1 x).1 hj
    obtain ⟨hN, hval⟩ := (normVal K L v w _).1 hμ
    have hone : ∀ y, (η ^ j).loc v (nm w y) = 1 := fun y => by
      have := DFunLike.congr_fun (hloc v w).1 y
      rw [MonoidHom.comp_apply, MonoidHom.one_apply] at this
      rw [loc_pow', MonoidHom.pow_apply, this, one_pow]
    refine ⟨ξ, hξ, hL.2.1 _ _ ?_ ?_⟩
    · have := unr_mul hu hN
      convert this using 1
      ext1 y
      simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hone, mul_one, mul_inv_rev]
      rw [mul_assoc, mul_inv_cancel_left]
    · have h2 : (((ξ * (χ * (η ^ j).loc v)) (nm w (unif (w.1.adicCompletion L))) : ℂˣ) : ℂ) * x ^ fdeg w = 1 := by
        rw [hval, Units.val_pow_eq_pow_val, ← mul_pow, hax, one_pow]
      have hx0 : x ^ fdeg w ≠ 0 := right_ne_zero_of_mul_eq_one h2
      have h3 := Units.ext (mul_right_cancel₀ hx0 (hbx.trans h2.symm))
      simp only [MonoidHom.mul_apply, MonoidHom.comp_apply, hone, mul_one] at h3
      exact mul_right_cancel h3
  · have h0 := congrArg (Polynomial.eval 1) (hM ξ⁻¹ (IsSmoothChar.inv hξ.1))
    rw [eval_prod, eval_prod] at h0
    have e : ξ * (ξ⁻¹ * (η ^ 0).loc v) = 1 := by rw [loc_pow', pow_zero, mul_one, mul_inv_cancel]
    have h1 : eval 1 (pol s (ξ⁻¹ * (η ^ 0).loc v)) = 0 :=
      ((hK s _).2.2.1 1).2 ⟨ξ, hξ, by rw [e]; exact unr_one, by rw [e]; simp⟩
    rw [Finset.prod_eq_zero (Finset.mem_range.2 hp.pos) h1, eq_comm, Finset.prod_eq_zero_iff] at h0
    obtain ⟨w, -, hw⟩ := h0
    rw [eval_comp, eval_pow, eval_X, one_pow] at hw
    have hL := polFacts (w.1.adicCompletion L)
    obtain ⟨ζ, hζ, hu, hval⟩ := ((hL.2.2.2 (s' w) _).2.2.1 1).1 hw
    refine ⟨w, ?_⟩
    have : ζ = ξ.comp (nm w) := by
      refine hL.2.1 _ _ hu ?_
      rw [mul_one, Units.val_eq_one] at hval
      exact mul_inv_eq_one.1 hval
    exact this ▸ hζ
end

open NumberField IsDedekindDomain Polynomial UpperTheory.V UpperTheory.V.Z.Gam UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem win_pow_iff (N M f : ℕ) (hf : 0 < f) (hM : M = N ^ f) (a b x y : ℝ) (hx : 0 ≤ x) (hy : y = x ^ f) :
    ((M : ℝ) ^ a < y ∧ y < (M : ℝ) ^ b) ↔ ((N : ℝ) ^ a < x ∧ x < (N : ℝ) ^ b) := by
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have key : ∀ c : ℝ, (M : ℝ) ^ c = ((N : ℝ) ^ c) ^ f := by
    intro c
    rw [hM, Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hN, ← Real.rpow_mul hN, mul_comm]
  rw [key, key, hy, pow_lt_pow_iff_left₀ (Real.rpow_nonneg hN _) hx hf.ne',
    pow_lt_pow_iff_left₀ hx (Real.rpow_nonneg hN _) hf.ne']

theorem UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.winUpDown :
    UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.WinUpDown := by
  intro K L _ _ _ _ _ _ _ _ hp n hn π P hbc t v
  have hn1 : 1 ≤ n := le_trans one_le_two hn
  have hUD := upDown K L hp n hn π P hbc v
  obtain ⟨s, hs⟩ := (suppFacts K n hn1 π v).1
  have hex : ∀ w : GroundTheory.Global.SemiLocal.PlacesOver L v, ∃ s', SuppAt P w.1 s' := fun w => (suppFacts L n hn1 P w.1).1
  choose s' hs' using hex
  have hX := upDownX K L hp n hn π P hbc v s s' hs hs'
  refine ⟨fun hW w => ?_, fun hW => ?_⟩
  · refine ⟨⟨(hUD.1 hW.1 w).1, fun s₁ hs₁ ζ hζ => ?_⟩, (hUD.1 hW.1 w).2⟩
    have e : s₁ = s' w := (suppFacts L n hn1 P w.1).2.1 _ _ hs₁ (hs' w)
    rw [e] at hζ
    obtain ⟨ξ, hξ, rfl⟩ := hX.1 hW.1 w ζ hζ
    have hv := normVal K L v w ξ
    exact (win_pow_iff _ _ _ hv.2.2.1 hv.2.2.2 _ _ _ _ (norm_nonneg _) (hv.2.1 hξ.choose)).2 (hW.2 s hs ξ hξ)
  · refine ⟨hUD.2 fun w => ⟨(hW w).1.1, (hW w).2⟩, fun s₁ hs₁ ξ hξ => ?_⟩
    have e : s₁ = s := (suppFacts K n hn1 π v).2.1 _ _ hs₁ hs
    rw [e] at hξ
    obtain ⟨w, hw⟩ := hX.2 ξ hξ
    have hv := normVal K L v w ξ
    exact (win_pow_iff _ _ _ hv.2.2.1 hv.2.2.2 _ _ _ _ (norm_nonneg _) (hv.2.1 hξ.choose)).1 ((hW w).1.2 _ (hs' w) _ hw)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LeviSmoothLocalization.PrincipalSeriesMatching.UnlFull
noncomputable section

open NumberField IsDedekindDomain ValuativeRel
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.TypeTwo GlobalTheory.ThetaGL GlobalTheory.LocGL
open GlobalTheory.TypeTwo.PowIrrProof

namespace UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem unif_valuation : valuation k (unif k : k) = uniformizer k := by
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.PrinTwo.NoFix.exists_unif k
  have hex : ∃ p : kˣ, valuation k (p : k) < 1 ∧
      ∀ x : k, valuation k x < 1 → valuation k x ≤ valuation k (p : k) := by
    refine ⟨ϖ, ?_, ?_⟩
    · rw [hϖ]
      exact uniformizer_lt_one (R := k)
    · intro x hx
      rw [hϖ]
      exact le_uniformizer_iff.mpr hx
  have hs := Classical.epsilon_spec hex
  unfold unif
  apply le_antisymm
  · exact le_uniformizer_iff.mpr hs.1
  · rw [← hϖ]
    refine hs.2 _ ?_
    rw [hϖ]
    exact uniformizer_lt_one (R := k)

private theorem absPow_neg_one_unif :
    (((absPow k (-1)) (unif k) : ℂˣ) : ℂ) = (GroundTheory.LocalField.residueCard k : ℂ) := by
  rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ord_eq_one unif_valuation]
  push_cast
  rw [Complex.cpow_neg_one, zpow_neg_one, inv_inv]
  rfl

private theorem ne_mul_absPow {n : ℕ} (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (h : Unl (GroundTheory.LocalField.residueCard k) (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)))
    (i j : Fin n) : ω j ≠ ω i * absPow k 1 := by
  intro hj
  have hi : ω i ∈ chars (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) :=
    ⟨hω i, Multiset.mem_map.mpr ⟨i, Finset.mem_univ_val i, rfl⟩⟩
  have hj' : ω j ∈ chars (Finset.univ.val.map fun i => IrrGL.ofChar (ω i) (hω i)) :=
    ⟨hω j, Multiset.mem_map.mpr ⟨j, Finset.mem_univ_val j, rfl⟩⟩
  have h0 : absPow k (-1) * absPow k 1 = 1 := by
    rw [← absPow_add]
    ext x
    simp [val_absPow]
  have hq : ω i * (ω j)⁻¹ = absPow k (-1) := by
    rw [hj, mul_inv_rev, mul_left_comm, mul_inv_cancel, mul_one]
    exact (eq_inv_of_mul_eq_one_left h0).symm
  apply h (ω i) hi (ω j) hj'
  · rw [hq]
    exact isUnram_absPow k (-1)
  · rw [hq]
    exact absPow_neg_one_unif

private theorem prinSeries_irreducible {n : ℕ} (ω : Fin n → kˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i))
    (h : ∀ i j, ω j ≠ ω i * absPow k 1) : (prinSeries ω).IsIrreducible := by
  classical
  have hd : ∑ a : Fin n, (IrrGL.ofChar (ω a) (hω a)).fst = n := by
    simp [IrrGL.ofChar]
  have hirr : (prodIrr (fun a => IrrGL.ofChar (ω a) (hω a)) hd).IsIrreducible := by
    refine GlobalTheory.RgGu.Holds.lUnlinkedIrr_holds k n n
      (fun i => Segment.single (IrrGL.ofChar (ω i) (hω i)) (IrrGL.isCusp_ofChar _ _)) _ hd ?_ ?_
    · intro i j
      apply GlobalTheory.CompanionTheory.BZPair.not_linked_single
      · unfold IrrGL.nu
        rw [IrrGL.tw_ofChar]
        intro he
        exact h i j (IrrGL.ofChar_inj.mp he)
      · unfold IrrGL.nu
        rw [IrrGL.tw_ofChar]
        intro he
        exact h j i (IrrGL.ofChar_inj.mp he)
    · intro i
      exact (single_spec (IrrGL.isCusp_ofChar (ω i) (hω i))).2.1
  let e1 := stdBlocks (fun a => (IrrGL.ofChar (ω a) (hω a)).fst) hd
  have E1 : (prodIrr (fun a => IrrGL.ofChar (ω a) (hω a)) hd).Equiv
      (multiProd e1 fun a => detRep (Fin 1) (ω a)) :=
    multiProdEquiv e1 (fun a => (equivRep (IrrRep.det (Fin 1) (ω a) (hω a))).symm)
  obtain ⟨E2⟩ := (Placing.parInd_jac_placing k (Fin n) (Fin n) (fun _ => Fin 1) e1
    (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) _).1 (piTensor fun a => detRep (Fin 1) (ω a))
  have hM : (multiProd (Equiv.sigmaUnique (Fin n) fun _ => Fin 1)
      fun a => detRep (Fin 1) (ω a)).IsIrreducible :=
    GlobalTheory.Parabolic.isIrreducible_of_equiv (E1.trans E2) hirr
  have hn {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
      [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
      (h : IsSubquotient σ ρ) (hW : Nontrivial W) : Nontrivial V := by
    letI := hW
    obtain ⟨S, f, hf⟩ := h
    have := hf.nontrivial
    exact Subtype.val_injective.nontrivial (α := S.toSubmodule)
  haveI := hn
    (GlobalTheory.PermPrin.isSubquotient_multiProd_prinSeries (Equiv.sigmaUnique (Fin n) fun _ => Fin 1) ω)
    (nontrivial_of_irreducible hM)
  have he {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
      [Module ℂ W] {σ : Representation ℂ G W} {ρ : Representation ℂ G V}
      (h : IsSubquotient σ ρ) [Nontrivial W] (hρ : ρ.IsIrreducible) :
      Nonempty (ρ.Equiv σ) := by
    obtain ⟨S, f, hf⟩ := h
    obtain ⟨y, hy⟩ := exists_ne (0 : W)
    obtain ⟨v, rfl⟩ := hf y
    haveI : IsSimpleOrder (Subrepresentation ρ) := hρ
    rcases eq_bot_or_eq_top S with rfl | rfl
    · exact absurd (by rw [show v = 0 from Subtype.ext v.2, map_zero]) hy
    let F : ρ.IntertwiningMap σ := f.comp (topEquiv ρ).symm.toIntertwiningMap
    have hs : Function.Surjective F := hf.comp (topEquiv ρ).symm.toLinearEquiv.surjective
    refine ⟨equivOfBijective F ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, hs⟩⟩
    rcases eq_bot_or_eq_top F.ker with h | h
    · have : x ∈ F.ker := hx
      rw [h] at this
      exact this
    · have : v.1 ∈ F.ker := by rw [h]; trivial
      exact absurd this hy
  obtain ⟨E3⟩ := he (GlobalTheory.PrinProd.isSubquotient_prinSeries_multiProd k n ω) hM
  exact GlobalTheory.Parabolic.isIrreducible_of_equiv E3 hM

end Loc

theorem unlFull : UnlFull := by
  intro k _ _ _ _ _ n V _ _ π ω hω hs hu
  obtain ⟨hi, hq⟩ := (UpperTheory.Gal.LocD.ofSupport_holds k n V π ω hω).1 hs
  obtain ⟨E⟩ := hq.nonempty_equiv hi (prinSeries_irreducible ω hω (ne_mul_absPow ω hω hu))
  exact ⟨E.symm⟩

end UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter
end
end
