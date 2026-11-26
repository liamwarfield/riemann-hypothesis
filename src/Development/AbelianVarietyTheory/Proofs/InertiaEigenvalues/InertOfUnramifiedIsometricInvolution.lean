module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelIteratedIntegralsSwap

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolution
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolution
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.InertOfUnramInv

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

theorem exists_int_approx (w : HeightOneSpectrum (𝓞 L)) (x : w.adicCompletion L) (hx : Valued.v x ≤ 1) :
    ∃ a : 𝓞 L, Valued.v (x - algebraMap L (w.adicCompletion L) (a : L)) < 1 := by
  have hval : ∀ k : L, Valued.v (algebraMap L (w.adicCompletion L) k) = w.valuation L k :=
    fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) k
  have hU : IsOpen {z : w.adicCompletion L | Valued.v (z - x) < 1} := by
    have h := (Valued.isOpen_ball (w.adicCompletion L) 1).preimage (continuous_sub_right x)
    simpa [Valuation.restrict_lt_one_iff] using h
  obtain ⟨y, hy⟩ :=
    (HeightOneSpectrum.denseRange_algebraMap (K := L) (v := w)).exists_mem_open hU ⟨x, by simp⟩
  have hy' : Valued.v (algebraMap L (w.adicCompletion L) y - x) < 1 := hy
  have hyv : w.valuation L y ≤ 1 := by
    rw [← hval]
    calc Valued.v (algebraMap L (w.adicCompletion L) y)
        = Valued.v ((algebraMap L (w.adicCompletion L) y - x) + x) := by rw [sub_add_cancel]
      _ ≤ max (Valued.v (algebraMap L (w.adicCompletion L) y - x)) (Valued.v x) := Valuation.map_add _ _ _
      _ ≤ 1 := max_le hy'.le hx
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer (K := L) (v := w) hyv 1
  refine ⟨a, ?_⟩
  have e : x - algebraMap L (w.adicCompletion L) (a : L) =
      -(algebraMap L (w.adicCompletion L) y - x) + -(algebraMap L (w.adicCompletion L) (a : L) -
        algebraMap L (w.adicCompletion L) y) := by ring
  rw [e]
  refine Valuation.map_add_lt _ (by rw [Valuation.map_neg]; exact hy') ?_
  rw [Valuation.map_neg, ← map_sub, hval]
  simpa using ha

theorem inert_of_isUnramInv : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal ∧ ¬ IsSplitAt w ∧ q = Formalism.UG.qV (maximalRealSubfield L) v := by
  intro L _ _ _ v w hvw s ϖ q hsc hU
  unfold Formalism.UG.IsUnramInv at hU
  obtain ⟨-, hsv, -, -, ⟨x, hxO, hx1⟩, -, hcard⟩ := hU
  have hvw' : w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) = v.asIdeal := hvw
  have hlo : w.asIdeal.LiesOver v.asIdeal := ⟨hvw'.symm⟩
  let φ : 𝓞 L →+* w.adicCompletion L := (algebraMap L (w.adicCompletion L)).comp (algebraMap (𝓞 L) L)
  have hφ : ∀ b : 𝓞 L, Valued.v (φ b) = w.valuation L (algebraMap (𝓞 L) L b) :=
    fun b => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (v := w) (algebraMap (𝓞 L) L b)
  have hval : ∀ b : 𝓞 L, Valued.v (φ b) < 1 ↔ b ∈ w.asIdeal := by
    intro b
    rw [hφ]
    exact HeightOneSpectrum.valuation_lt_one_iff_mem (K := L) w b
  have hfix : ∀ a : 𝓞 (maximalRealSubfield L),
      s (φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a)) = φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a) := by
    intro a
    show s (algebraMap L _ _) = algebraMap L _ _
    rw [hsc]
    congr 1
    exact (IsCMField.complexConj L).commutes (a : maximalRealSubfield L)
  have hxv : Valued.v x ≤ 1 := hxO

  have hf1 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≠ 1 := by
    intro hf
    have hn := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    rw [hf, pow_one, Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Submodule.cardQuot_apply] at hn
    have hle : v.asIdeal ≤ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L)) := hvw'.ge
    have hinj : Function.Injective (Ideal.quotientMap w.asIdeal _ hle) :=
      Ideal.quotientMap_injective' hvw'.le
    have hbij := (Nat.bijective_iff_injective_and_card _).mpr ⟨hinj, hn⟩
    obtain ⟨b, hb⟩ := exists_int_approx w x hxv
    obtain ⟨a, ha⟩ := hbij.2 (Ideal.Quotient.mk w.asIdeal b)
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    rw [Ideal.quotientMap_mk, Ideal.Quotient.eq] at ha
    have hsz := hfix a
    set z := φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a) with hz
    have h1 : Valued.v (x - z) < 1 := by
      have e : x - z = (x - φ b) + -(φ (algebraMap (𝓞 (maximalRealSubfield L)) (𝓞 L) a - b)) := by
        rw [map_sub]; ring
      rw [e]
      refine Valuation.map_add_lt _ hb ?_
      rw [Valuation.map_neg, hval]
      exact ha
    have h2 : s x - x = s (x - z) + -(x - z) := by
      rw [map_sub, hsz]; ring
    have h3 : Valued.v (s x - x) < 1 := by
      rw [h2]
      refine Valuation.map_add_lt _ ?_ ?_
      · rw [hsv]; exact h1
      · rw [Valuation.map_neg]; exact h1
    exact absurd hx1 (ne_of_lt h3)
  have hfpos := Ideal.inertiaDeg_pos w.asIdeal (𝓞 (maximalRealSubfield L))
  have hepos := Ideal.ramificationIdx_pos (R := 𝓞 (maximalRealSubfield L)) w.asIdeal

  have hG2 : Nat.card (L ≃ₐ[maximalRealSubfield L] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]
  have hsum := Ideal.sum_ramification_inertia_eq_card v.asIdeal (𝓞 L)
    (G := L ≃ₐ[maximalRealSubfield L] L)
  let F : v.asIdeal.primesOver (𝓞 L) → ℕ := fun P =>
    P.1.ramificationIdx (𝓞 (maximalRealSubfield L)) * P.1.inertiaDeg (𝓞 (maximalRealSubfield L))
  have hsum' : ∑ P, F P = 2 := by
    rw [← hG2, ← hsum]
  let W : v.asIdeal.primesOver (𝓞 L) := ⟨w.asIdeal, w.isPrime, hlo⟩
  have hW : F W ≤ 2 := by
    rw [← hsum']
    exact Finset.single_le_sum (f := F) (fun _ _ => Nat.zero_le _) (Finset.mem_univ W)
  have hW' : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) *
      w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) ≤ 2 := hW
  have hf2 : w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2 := by
    have : 2 ≤ w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) := by omega
    nlinarith
  have he1 : w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) = 1 := by
    rw [hf2] at hW'
    omega
  refine ⟨?_, ?_, ?_⟩
  · have : (w.asIdeal.under (𝓞 (maximalRealSubfield L))).IsMaximal := by
      rw [← hlo.over]
      exact v.isMaximal
    exact Ideal.ramificationIdx_eq_one_iff.mp he1
  · rintro ⟨u, hne, hu⟩
    have hlu : u.asIdeal.LiesOver v.asIdeal := ⟨by
      rw [hlo.over]
      exact (congrArg HeightOneSpectrum.asIdeal hu).symm⟩
    let U : v.asIdeal.primesOver (𝓞 L) := ⟨u.asIdeal, u.isPrime, hlu⟩
    have hWU : W ≠ U := fun h => hne (HeightOneSpectrum.ext (congrArg Subtype.val h).symm)
    have h2 : F W + F U ≤ 2 := by
      rw [← hsum', ← Finset.sum_pair hWU]
      exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    have hu1 := Ideal.inertiaDeg_pos u.asIdeal (𝓞 (maximalRealSubfield L))
    have hu2 := Ideal.ramificationIdx_pos (R := 𝓞 (maximalRealSubfield L)) u.asIdeal
    have hFU : 1 ≤ F U := Nat.mul_pos hu2 hu1
    have hFW : F W = 2 := by
      show w.asIdeal.ramificationIdx (𝓞 (maximalRealSubfield L)) *
        w.asIdeal.inertiaDeg (𝓞 (maximalRealSubfield L)) = 2
      rw [he1, hf2]
    omega
  ·
    let O := (Valued.v : Valuation (w.adicCompletion L) (WithZero (Multiplicative ℤ))).valuationSubring
    have hmemO : ∀ b : 𝓞 L, φ b ∈ O := by
      intro b
      show Valued.v (φ b) ≤ 1
      rw [hφ]
      exact HeightOneSpectrum.valuation_le_one (K := L) w b
    let g : 𝓞 L →+* O := φ.codRestrict O hmemO
    have hmax : ∀ y : O, y ∈ IsLocalRing.maximalIdeal O ↔ Valued.v (y : w.adicCompletion L) < 1 := by
      intro y
      have hle : Valued.v (y : w.adicCompletion L) ≤ 1 := y.2
      have hu : IsUnit y ↔ Valued.v (y : w.adicCompletion L) = 1 :=
        HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one (K := L) (v := w) (a := y)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hu]
      exact ⟨fun h => lt_of_le_of_ne hle h, fun h => ne_of_lt h⟩
    let G := (Ideal.Quotient.mk (IsLocalRing.maximalIdeal O)).comp g
    have hGs : Function.Surjective G := by
      intro Y
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective Y
      obtain ⟨b, hb⟩ := exists_int_approx w (y : w.adicCompletion L) y.2
      refine ⟨b, ?_⟩
      show Ideal.Quotient.mk _ (g b) = Ideal.Quotient.mk _ y
      rw [Ideal.Quotient.eq, hmax]
      show Valued.v (φ b - (y : w.adicCompletion L)) < 1
      rw [← Valuation.map_neg, neg_sub]
      exact hb
    have hker : RingHom.ker G = w.asIdeal := by
      ext b
      rw [RingHom.mem_ker]
      show Ideal.Quotient.mk _ (g b) = 0 ↔ _
      rw [Ideal.Quotient.eq_zero_iff_mem, hmax]
      exact hval b
    have hc := Nat.card_congr (RingHom.quotientKerEquivOfSurjective hGs).toEquiv
    rw [hker] at hc
    have hcard' : Nat.card (O ⧸ IsLocalRing.maximalIdeal O) = q ^ 2 := hcard
    have hn := Ideal.absNorm_pow_inertiaDeg v.asIdeal w.asIdeal
    rw [hf2, Ideal.absNorm_apply w.asIdeal, Submodule.cardQuot_apply, hc, hcard'] at hn
    show q = Ideal.absNorm v.asIdeal
    exact Nat.pow_left_injective (n := 2) (by norm_num) hn.symm

end GlobalTheory.InertOfUnramInv
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertOfUnramifiedIsometricInvolutionStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inert_of_unramifiedIsometricInvolution : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))) (w : HeightOneSpectrum (𝓞 L)), NG.OverPl w v → ∀ (s : w.adicCompletion L →+* w.adicCompletion L) (ϖ : w.adicCompletion L) (q : ℕ), (∀ x : L, s (algebraMap L _ x) = algebraMap L _ (IsCMField.complexConj L x)) → Formalism.UG.IsUnramInv ϖ s q → Algebra.IsUnramifiedAt (𝓞 (maximalRealSubfield L)) w.asIdeal ∧ ¬ IsSplitAt w ∧ q = Formalism.UG.qV (maximalRealSubfield L) v := by
  first | exact @GlobalTheory.InertOfUnramInv.inert_of_isUnramInv | exact GlobalTheory.InertOfUnramInv.inert_of_isUnramInv | (intros; apply GlobalTheory.InertOfUnramInv.inert_of_isUnramInv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedUnitaryAdjointAction
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedUnitaryAdjointAction
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

theorem smul_conj {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R) (B X Bi : Matrix n n R) :
    c • (B * X * Bi) = B * (c • X) * Bi := by
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem smul_one_conj {R : Type*} [CommRing R] {n : Type*} [Fintype n] [DecidableEq n] (c : R) (B Bi : Matrix n n R)
    (h : B * Bi = 1) : B * (c • (1 : Matrix n n R)) * Bi = c • (1 : Matrix n n R) := by
  rw [← smul_conj, Matrix.mul_one, h]

theorem suppAt_inv_of {D : D7} {e : AE D} {V : HSp D} {g : GA D V} (hg : SuppAt e V g) : SuppAt e V g⁻¹ := by
  intro i j
  have h := congrFun (congrFun (GlobalTheory.SplitScalar.off_smul_mt_inv hg) i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h
  rw [Matrix.sub_apply]
  linear_combination (-1 : AE D) * h

theorem chart_idem_one {D : D7} {e : AE D} {PP : Pl D.host.E} {v : HeightOneSpectrum (𝓞 D.host.F)}
    {φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v} {ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)}
    (he : Formalism.L2.NTheta.IsIdemAt e PP) (hL : LevChart e PP v φ ι) : φ (toEAf D e) = 1 := by
  have h0 : φ (toEAf D e - 1) = 0 := by
    rw [hL.2.1, mul_sub, mul_one, ← map_mul, he.1.1, sub_self]
  rwa [map_sub, map_one, sub_eq_zero] at h0


set_option maxHeartbeats 1000000 in
theorem exists_supp_rdAdj_mul : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ γ : GL (Fin T.rank) (Fv D.host.F v), ∃ g : GA D T, SuppAt e T g ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T 1 g x) = rdAdj S T βS βT φ x * γ.val := by
  intro D S T βS βT e PP v φ ι he hL γ
  have hfin : GlobalTheory.LevSplit.finSw D = toEAf D := rfl
  have h1 : φ (toEAf D e) = 1 := chart_idem_one he hL
  choose M hM using fun i j => hL.1 (γ.val i j)
  choose M' hM' using fun i j => hL.1 ((γ⁻¹).val i j)
  set A : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D) := Matrix.of M with hA
  set A' : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D) := Matrix.of M' with hA'
  have eA : A.map φ = γ.val := Matrix.ext hM
  have eA' : A'.map φ = (γ⁻¹).val := Matrix.ext hM'
  set c := toEAf D e with hc
  have hAA : c • (A * A') = c • (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) := by
    ext i j
    have hm : (A * A').map φ = (1 : Matrix (Fin T.rank) (Fin T.rank) (Fv D.host.F v)) := by
      rw [Matrix.map_mul, eA, eA', ← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hz : φ ((A * A') i j - (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) i j) = 0 := by
      rw [map_sub]
      have := congrFun (congrFun hm i) j
      rw [Matrix.map_apply] at this
      rw [this, ← Matrix.map_apply (f := φ), Matrix.map_one φ (map_zero φ) (map_one φ), sub_self]
    have := (hL.2.1 _).1 hz
    simp only [Matrix.smul_apply, smul_eq_mul]
    rw [mul_sub, sub_eq_zero] at this
    exact this
  have hb : (βT⁻¹).val * βT.val = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hb' : βT.val * (βT⁻¹).val = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hmm : GlobalTheory.LevSplit.finSw D e • ((βT.val * A * (βT⁻¹).val) * (βT.val * A' * (βT⁻¹).val)) =
      GlobalTheory.LevSplit.finSw D e • (1 : Matrix (Fin T.rank) (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) := by
    rw [hfin, ← hc]
    have : (βT.val * A * (βT⁻¹).val) * (βT.val * A' * (βT⁻¹).val) = βT.val * (A * A') * (βT⁻¹).val := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (βT⁻¹).val βT.val, hb, Matrix.one_mul]
    rw [this, smul_conj, hAA, smul_one_conj _ _ _ hb']
  obtain ⟨g₀, hs, hg₀⟩ := GlobalTheory.ParahoricLift.split_lift_fin T he.1 _ _ hmm
  rw [hfin, ← hc] at hg₀
  have hX : ((βT⁻¹).val * (Formalism.L2.Theta.mt T g₀).map (toEAf D) * βT.val).map φ = γ.val := by
    have hfe : (Formalism.L2.Theta.mt T g₀).map (toEAf D) = (finE T g₀).val := rfl
    have h2 : c • ((βT⁻¹).val * (finE T g₀).val * βT.val) = c • A := by
      rw [smul_conj, hg₀, ← smul_conj]
      congr 1
      simp only [Matrix.mul_assoc]
      rw [hb, Matrix.mul_one, ← Matrix.mul_assoc, hb, Matrix.one_mul]
    rw [hfe, ← eA]
    refine Matrix.ext fun i j => ?_
    show φ _ = φ _
    have := congrArg φ (congrFun (congrFun h2 i) j)
    simpa only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, h1, one_mul] using this
  refine ⟨g₀⁻¹, suppAt_inv_of hs, fun x => ?_⟩
  rw [rdAdj, rdAdj, GlobalTheory.TranslateAdj.frMapAdj_actO_inv, Matrix.map_mul, hX]

end GlobalTheory.DownLift.SplitCoef
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedUnitaryAdjointActionStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_supported_unitary_adjoint_action : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ γ : GL (Fin T.rank) (Fv D.host.F v), ∃ g : GA D T, SuppAt e T g ∧ ∀ x : WO S T, rdAdj S T βS βT φ (actO S T 1 g x) = rdAdj S T βS βT φ x * γ.val := by
  first | exact @GlobalTheory.DownLift.SplitCoef.exists_supp_rdAdj_mul | exact GlobalTheory.DownLift.SplitCoef.exists_supp_rdAdj_mul | (intros; apply GlobalTheory.DownLift.SplitCoef.exists_supp_rdAdj_mul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaIntegralSobolevContinuous
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaIntegralSobolevContinuous
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

noncomputable section
namespace GlobalTheory.DownLift.Sobolev₂

open GlobalTheory.Size GlobalTheory.Grow
open scoped ComplexOrder

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]


set_option maxHeartbeats 1000000 in
theorem integrableOn_extV (R : RealDat D A Ks) (hm : R.IsModels) (i : Fin D.R.m) (t : T) (y : (R.HV i t).H)
    (l : (R.cV i).W →ₗ[ℂ] ℂ) : IntegrableOn (fun h => l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := by
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  have hc := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  have hK := hc.choose_spec.1
  have hKc := hc.choose_spec.2
  have hx := (hm.HV i t).2.1.le (LinearMap.mem_range_self _ y)
  have hFc : Continuous (R.extV i t y) :=
    GlobalTheory.ThetaIntegrand.ext_continuous (R.cV i) (hm.cV i) (R.βV i) (R.datVt i t) hx
  have hFi : ∀ γ ∈ GQ (Vc D i), ∀ h, R.extV i t y (γ * h) = R.extV i t y h :=
    GlobalTheory.ThetaIntegrand.ext_invariant (R.cV i) hx
  have hlc : Continuous fun h => l (R.extV i t y h) := l.continuous_of_finiteDimensional.comp hFc
  have hH : (R.νV i t).IsHaarMeasure := (hm.νV i t).1.1
  have hfd : IsFundamentalDomain (GQ (Vc D i)) (R.fdV i t) (R.νV i t) := (hm.νV i t).2
  have : IsFiniteMeasure ((R.νV i t).restrict (R.fdV i t)) :=
    isFiniteMeasure_restrict.2 (GlobalTheory.CuspDecay.measure_lt_top GlobalTheory.Mem.VolFin.finVol (Vc D i) (R.νV i t) (R.fdV i t)
      hH hfd).ne
  have hb := hK.exists_bound_of_continuousOn hlc.continuousOn
  have hbd : ∀ h, ‖l (R.extV i t y h)‖ ≤ hb.choose := by
    intro h
    obtain ⟨γ, hγ, c, hc, e⟩ := hKc h
    rw [e, hFi γ hγ c]
    exact hb.choose_spec c hc
  exact Integrable.of_bound hlc.aestronglyMeasurable hb.choose (.of_forall hbd)


set_option maxHeartbeats 1000000 in
theorem downInt_sobolev_cont : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) (ε : ℝ), 0 < ε → ∃ (d : ℕ) (δ : ENNReal), 0 < δ ∧ ∀ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ → ‖downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g‖ < ε := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t y μ 𝓕 hμ f hf l g ε hε
  have hm := hG.core.models
  have hθ : IsInfFam R.θ := hm.inf
  have hω := hG.core.thP.ωP i t
  have hψ := hω.std
  have hpt := hG.core.thP.pt_theta i t
  have hvP : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hpt 1
    rwa [RealDat.ptP, GlobalTheory.FiniteFock.pureTensorO_one] at this
  obtain ⟨U₀, hU₀, hl₀⟩ := isTheta_iff_level.1 hvP
  obtain ⟨U₁, hU₁, hl₁⟩ := isTheta_iff_level.1 hf
  have hUo : IsOpen ((U₁ ⊓ U₀ : AddSubgroup (WO (Vc D i) (Wc D i))) : Set (WO (Vc D i) (Wc D i))) := by
    rw [AddSubgroup.coe_inf]; exact hU₁.inter hU₀
  have hptl : ∀ P, R.ptP i t P ∈ GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) U₀ := fun P =>
    ⟨hpt P, fun u hu h0 => by
      have e := ((GlobalTheory.FinTranslate.finite_translate D R.ψ R.θ _ _ hψ hθ _ hvP).2 u h0).2
      unfold RealDat.ptP
      rw [← e, hl₀.2 u hu h0]⟩
  have hfl : f ∈ GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := thetaLevel_anti inf_le_left hl₁
  have hpl : ∀ P, R.ptP i t P ∈ GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := fun P =>
    thetaLevel_anti inf_le_right (hptl P)
  have hml : ∀ P, f - R.ptP i t P ∈ GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀) := fun P => sub_mem hfl (hpl P)
  obtain ⟨Ae, d, H⟩ := GlobalTheory.KernelSeminorm.thetaGrowth D (Vc D i).rank (Wc D i).rank
  obtain ⟨C, hC0, hC⟩ := (H (Vc D i) (Wc D i) rfl rfl).real R.ψ hθ hUo
  have hp : (Vc D i).IsPosDef := hm.vpos i
  have hpd : ∀ τ, (gramAt D (Vc D i) τ).PosDef := fun τ =>
    GlobalTheory.RepsObj.gramAt_posDef hp (D.sp.V_sig ((i : ℕ) + 1)) τ
  obtain ⟨K, hK, hKc⟩ := GlobalTheory.definite_unitary_cocompact (Vc D i) hpd
  obtain ⟨HK, hHK⟩ := hK.exists_bound_of_continuousOn (continuous_height (Vc D i)).continuousOn
  have hHK0 : 0 ≤ HK := by
    obtain ⟨γ, -, c, hc, -⟩ := hKc 1
    exact (norm_nonneg _).trans (hHK c hc)
  have hg0 := height_pos (Wc D i) g
  obtain ⟨B, hB⟩ : ∃ B : ℝ, B = C * (HK * height (Wc D i) g) ^ Ae := ⟨_, rfl⟩
  have hB0 : 0 ≤ B := hB ▸ by positivity
  have hbound : ∀ φ ∈ GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀), ∀ h,
      ‖thetaKO (R.ωP i t) h g φ‖ ≤ B * (sobO R.ψ R.θ μ 𝓕 d φ).toReal := by
    intro φ hφ h
    obtain ⟨γ, hγ, c, hc, rfl⟩ := hKc h
    rw [GlobalTheory.ChainOnto.ThetaSwap.thetaKO_left_fst hω hφ.1 γ hγ c g]
    have h1 := (hC _ _ (R.ωP i t) hω μ 𝓕 hμ φ hφ).2 c g
    have hc1 : height (Vc D i) c ≤ HK := (Real.le_norm_self _).trans (hHK c hc)
    have hc0 := height_pos (Vc D i) c
    have hs : 0 ≤ (sobO R.ψ R.θ μ 𝓕 d φ).toReal := ENNReal.toReal_nonneg
    have h2 : C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (height (Vc D i) c * height (Wc D i) g) ^ Ae ≤
        C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (HK * height (Wc D i) g) ^ Ae :=
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (mul_pos hc0 hg0).le
        (mul_le_mul_of_nonneg_right hc1 hg0.le) Ae) (mul_nonneg hC0 hs)
    have h3 : C * (sobO R.ψ R.θ μ 𝓕 d φ).toReal * (HK * height (Wc D i) g) ^ Ae =
        B * (sobO R.ψ R.θ μ 𝓕 d φ).toReal := by rw [hB]; ring
    exact h1.trans (h2.trans_eq h3)
  have hl1 : IntegrableOn (fun h => l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := integrableOn_extV R hm i t y l
  have hint : ∀ φ ∈ GlobalTheory.Size.thetaLevel R.ψ (Vc D i) (Wc D i) (U₁ ⊓ U₀),
      IntegrableOn (fun h => thetaKO (R.ωP i t) h g φ * l (R.extV i t y h)) (R.fdV i t) (R.νV i t) := fun φ hφ =>
    Integrable.bdd_mul hl1 ((hω.om_cont φ hφ.1 0).comp (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (.of_forall (hbound φ hφ))
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ∫ h in R.fdV i t, ‖l (R.extV i t y h)‖ ∂(R.νV i t) := ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hMdef ▸ integral_nonneg fun _ => norm_nonneg _
  have hpos : 0 < B * M + 1 := by positivity
  refine ⟨d, ENNReal.ofReal (ε / (B * M + 1)), ENNReal.ofReal_pos.2 (by positivity), fun P hP => ?_⟩
  have hs := ENNReal.toReal_lt_of_lt_ofReal hP
  have hs0 : 0 ≤ (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal := ENNReal.toReal_nonneg
  have e : downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g =
      ∫ h in R.fdV i t, thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h) ∂(R.νV i t) := by
    have i1 := hint f hfl
    have i2 := hint (R.ptP i t P) (hpl P)
    have e1 := integral_sub i1 i2
    refine e1.symm.trans (integral_congr_ae (.of_forall fun h => ?_))
    have e2 : R.ωP i t (h, g) (f - R.ptP i t P) = R.ωP i t (h, g) f - R.ωP i t (h, g) (R.ptP i t P) :=
      LinearMap.map_sub _ _ _
    show thetaKO (R.ωP i t) h g f * l (R.extV i t y h) - thetaKO (R.ωP i t) h g (R.ptP i t P) * l (R.extV i t y h) =
      thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h)
    refine (sub_mul _ _ _).symm.trans (congrArg (· * l (R.extV i t y h)) ?_)
    exact (congrFun e2 0).symm
  rw [e]
  have hle := norm_integral_le_of_norm_le (μ := (R.νV i t).restrict (R.fdV i t))
    (f := fun h => thetaKO (R.ωP i t) h g (f - R.ptP i t P) * l (R.extV i t y h))
    (hl1.norm.const_mul (B * (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal))
    (.of_forall fun h => by
      exact (norm_mul_le _ _).trans (mul_le_mul_of_nonneg_right (hbound _ (hml P) h) (norm_nonneg _)))
  rw [integral_const_mul, ← hMdef] at hle
  calc _ ≤ _ := hle
    _ ≤ (B * M + 1) * (sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P)).toReal := by nlinarith
    _ < (B * M + 1) * (ε / (B * M + 1)) := by gcongr
    _ = ε := by field_simp

end GlobalTheory.DownLift.Sobolev₂
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaIntegralSobolevContinuousStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.downward_theta_integral_sobolev_continuous : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (y : (R.HV i t).H) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, IsThetaFunO R.ψ (Vc D i) (Wc D i) f → ∀ (l : (R.cV i).W →ₗ[ℂ] ℂ) (g : GA D (Wc D i)) (ε : ℝ), 0 < ε → ∃ (d : ℕ) (δ : ENNReal), 0 < δ ∧ ∀ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ → ‖downInt R i t y f l g - downInt R i t y (R.ptP i t P) l g‖ < ε := by
  first | exact @GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont | exact GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont | (intros; apply GlobalTheory.DownLift.Sobolev₂.downInt_sobolev_cont <;> assumption)
end
end
