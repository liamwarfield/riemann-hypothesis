module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBoundAlt
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteBasisAlgebraicForms

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.KerOpen
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.kerOpen_pf :
    UpperTheory.Gal.Gen.PowNhds → UpperTheory.Gal.Gen.KerOpen := by
  intro hP E _ _ w a J hJ A _ _ θ
  have hN : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have hV := hP E w a (Nat.card A) hN (J : Set (GL (Fin a) (w.adicCompletion E)))
    (hJ.mem_nhds J.one_mem)
  refine ⟨interior ((fun x => x ^ Nat.card A) '' (J : Set (GL (Fin a) (w.adicCompletion E)))),
    isOpen_interior, mem_interior_iff_mem_nhds.2 hV, ?_⟩
  intro x hx
  obtain ⟨y, hy, hxy⟩ := interior_subset hx
  have hx' : x = (⟨y, hy⟩ : J) ^ Nat.card A := Subtype.ext (by simpa using hxy.symm)
  rw [hx', map_pow, pow_card_eq_one']
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.RhoBound
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.rhoBound_pf :
    UpperTheory.Gal.Gen.DegLe → UpperTheory.Gal.Gen.BlockBound → UpperTheory.Gal.Gen.DetBound → UpperTheory.Gal.Gen.SizeLe → UpperTheory.Gal.Gen.RhoBound := by
  intro hdeg hblk hdet hsize E _ _ _ l _ ι a W A R hR hA x hx m
  have hx' : (x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ).totalDegree
      ≤ ∑ τ, ∑ i, (W τ).natW i := hdeg (InfinitePlace E) a W x x.2
  have hb := hblk l ι (InfinitePlace E) a (fun τ => ((A τ : Matrix (Fin a) (Fin a) ℂ)).transpose) R hR
    (fun τ i j => (hA τ j i).1) _ x hx' hx m
  have hd := hdet l ι (InfinitePlace E) a W A R hR hA
  have hs := hsize E a W
  have hcoe : (((Formalism.L2.DIV.rhoK W) A) x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ)
      = Formalism.L2.DIV.detTwK W A • Formalism.L2.DIV.trAct A (x : MvPolynomial (InfinitePlace E × Fin a × Fin a) ℂ) := rfl
  rw [hcoe, MvPolynomial.coeff_smul, smul_eq_mul, map_mul, norm_mul]
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  calc ‖ι.symm (Formalism.L2.DIV.detTwK W A)‖ * ‖ι.symm (AddMonoidAlgebra.coeff (Formalism.L2.DIV.trAct A (x : MvPolynomial _ ℂ)) m)‖
      ≤ R ^ (∑ τ, a * (W τ).detShift.natAbs) * R ^ (∑ τ, ∑ i, (W τ).natW i) :=
        mul_le_mul hd hb (norm_nonneg _) (pow_nonneg hR0 _)
    _ = R ^ (∑ τ, ∑ i, (W τ).natW i + ∑ τ, a * (W τ).detShift.natAbs) := by
        rw [← pow_add, add_comm]
    _ ≤ R ^ (a * GlobalTheory.CongW.wtSize W.at) := pow_le_pow_right₀ hR hs
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.OpOfSmul
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU

namespace UpperTheory.Gal.Gen

open GlobalTheory.CongW (IntMat wtSize HasTypeVec IsIntegralOpW)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem opOf_smul' (c : ℂ) (f : UA E a →₀ ℂ) (φ : UA E a → ℂ) : opOf (RU E a) (c • f) φ = c • opOf (RU E a) f φ := by
  have e : ∀ f : UA E a →₀ ℂ, opOf (RU E a) f φ = Finsupp.linearCombination ℂ (fun g => RU E a g φ) f := fun f =>
    (Finsupp.linearCombination_apply ℂ f).symm
  rw [e, e, map_smul]

theorem part_mono (W : Wt E a) (C : Subgroup (UA E a)) {P Q : Submodule ℂ (UA E a → ℂ) → Prop} (h : ∀ U, P U → Q U) :
    part W C P ≤ part W C Q :=
  iSup₂_le fun π hπ => le_iSup₂_of_le (f := fun (π : AutSub E a) (_ : Q π.V) => π.finPart W ⊓ fixedBy W C) π (h _ hπ) le_rfl

end UpperTheory.Gal.Gen

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TotalDegreeLeOfCol
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem totalDegree_le_of_col {r n : ℕ} {ν : Fin n → ℕ} {F : MvPolynomial (Fin r × Fin n) ℂ}
    (h : MvPolynomial.IsWeightedHomogeneous (Formalism.GradedWeylDivisibility.colW r n) F ν) : F.totalDegree ≤ ∑ i, ν i := by
  unfold MvPolynomial.totalDegree
  refine Finset.sup_le fun m hm => ?_
  have hw : Finsupp.weight (Formalism.GradedWeylDivisibility.colW r n) m = ν := h (MvPolynomial.mem_support_iff.mp hm)
  rw [← hw, Finsupp.weight_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply, Formalism.GradedWeylDivisibility.colW, smul_eq_mul]
  rw [Finset.sum_comm]
  refine le_of_eq (Finset.sum_congr rfl fun v _ => ?_)
  simp [Pi.single_apply]

theorem UpperTheory.Gal.Gen.degLe_pf :
    UpperTheory.Gal.Gen.DegLe := by
  intro T _ n lam x hx
  refine Submodule.span_induction (p := fun x _ => MvPolynomial.totalDegree x ≤ ∑ τ, ∑ i, (lam τ).natW i)
    ?_ ?_ ?_ ?_ hx
  · rintro P ⟨F, hF, rfl⟩
    refine (MvPolynomial.totalDegree_finsetProd _ _).trans (Finset.sum_le_sum fun τ _ => ?_)
    refine (MvPolynomial.totalDegree_rename_le (fun v => (τ, v)) (F τ)).trans ?_
    have hm := (Submodule.mem_inf.mp (hF τ)).1
    exact totalDegree_le_of_col ((MvPolynomial.mem_weightedHomogeneousSubmodule _ _ _ _).mp hm)
  · simp
  · intro a b _ _ ha hb
    exact (MvPolynomial.totalDegree_add a b).trans (max_le ha hb)
  · intro c a _ ha
    exact (MvPolynomial.totalDegree_smul_le c a).trans ha
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.PowNhds
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen
open Topology Filter

section
variable {𝕜 R : Type*} [NontriviallyNormedField 𝕜] [NormedRing R] [NormedAlgebra 𝕜 R]

private lemma strict_pow (N : ℕ) :
    HasStrictFDerivAt (fun x : R => x ^ N) ((N : 𝕜) • ContinuousLinearMap.id 𝕜 R) (1 : R) := by
  refine (hasStrictFDerivAt_pow' (𝕜 := 𝕜) N (x := (1 : R))).congr_fderiv ?_
  simp only [one_pow, MulOpposite.op_one, one_smul, Finset.sum_const, Finset.card_range]
  rw [Nat.cast_smul_eq_nsmul]

private lemma map_pow_nhds [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace R] {N : ℕ} (hN : N ≠ 0) :
    map (fun x : R => x ^ N) (𝓝 1) = 𝓝 1 := by
  have hN' : (N : 𝕜) ≠ 0 := Nat.cast_ne_zero.mpr hN
  let e : R ≃L[𝕜] R := ContinuousLinearEquiv.equivOfInverse ((N : 𝕜) • ContinuousLinearMap.id 𝕜 R)
    ((N : 𝕜)⁻¹ • ContinuousLinearMap.id 𝕜 R) (fun x => by simp [smul_smul, hN'])
    (fun x => by simp [smul_smul, hN'])
  have hf : HasStrictFDerivAt (fun x : R => x ^ N) (e : R →L[𝕜] R) 1 := strict_pow (𝕜 := 𝕜) N
  simpa using hf.map_nhds_eq_of_equiv

private lemma units_pow_nhds [CharZero 𝕜] [CompleteSpace 𝕜] [CompleteSpace R] {N : ℕ} (hN : N ≠ 0)
    {V : Set Rˣ} (hV : V ∈ 𝓝 (1 : Rˣ)) : (fun x => x ^ N) '' V ∈ 𝓝 (1 : Rˣ) := by
  have he := Units.isOpenEmbedding_val (R := R)
  have h1 : ((↑) : Rˣ → R) '' V ∈ 𝓝 (1 : R) := by
    simpa using he.image_mem_nhds.mpr hV
  have h2 : (fun x : R => x ^ N) '' (((↑) : Rˣ → R) '' V) ∈ 𝓝 (1 : R) := by
    rw [← map_pow_nhds (𝕜 := 𝕜) hN]
    exact image_mem_map h1
  rw [← he.image_mem_nhds]
  rw [Set.image_image, Units.val_one]
  rw [Set.image_image] at h2
  simpa using h2
end

theorem UpperTheory.Gal.Gen.powNhds_pf :
    UpperTheory.Gal.Gen.PowNhds := by
  intro E _ _ w a N hN V hV
  letI : NontriviallyNormedField (w.adicCompletion E) :=
    Valued.toNontriviallyNormedField _ (WithZero (Multiplicative ℤ))
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  letI : NormedRing (Matrix (Fin a) (Fin a) (w.adicCompletion E)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra (w.adicCompletion E) (Matrix (Fin a) (Fin a) (w.adicCompletion E)) :=
    Matrix.linftyOpNormedAlgebra
  haveI : @CompleteSpace (Matrix (Fin a) (Fin a) (w.adicCompletion E))
      (@Matrix.linftyOpNormedRing (Fin a) (w.adicCompletion E) _ _ _).toUniformSpace :=
    inferInstanceAs (CompleteSpace (Fin a → Fin a → w.adicCompletion E))
  exact units_pow_nhds (𝕜 := w.adicCompletion E) hN hV
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.TyStep
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.tyStep_pf :
    UpperTheory.Gal.Gen.LevFacts → UpperTheory.Gal.Gen.Ell → UpperTheory.Gal.Gen.KerOpen → UpperTheory.Gal.Gen.CharSum → UpperTheory.Gal.Gen.TwistPart → UpperTheory.Gal.Gen.TyStep := by
  intro hLev hEll hKer hCS hTw E _ _ _ l _ ι a w₀ hs K hK W J hJo hJc htf m θ f hf
  classical
  obtain ⟨hLvl, -, hC, -, -, -⟩ := hLev E a w₀ hs K hK J hJo hJc
  haveI : NeZero (l ^ m) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  haveI : Finite (Multiplicative (ZMod (l ^ m))) :=
    inferInstanceAs (Finite (ZMod (l ^ m)))
  let lam : (lev K w₀ J) →* Multiplicative (ZMod (l ^ m)) :=
    θ.comp (((cLoc w₀).comp (lev K w₀ J).subtype).codRestrict J fun c => hC c.1 c.2)
  have hlam : ∀ c : lev K w₀ J, lam c = θ ⟨cLoc w₀ c.1, hC c.1 c.2⟩ := fun c => rfl
  obtain ⟨N, hNo, hN1, hN⟩ := hKer E w₀ a J hJo _ θ
  obtain ⟨ℓ, hℓi, hℓC, hℓa⟩ := hEll E a (lev K w₀ J) hLvl _ lam
    ⟨cLoc w₀ ⁻¹' N, hNo.preimage (GlobalTheory.BCT.GlobLev.continuous_cLoc w₀), by simpa using hN1,
      fun c hc => hN ⟨cLoc w₀ c.1, hC c.1 c.2⟩ hc⟩
    (fun c hc => by
      obtain ⟨k, hk0, hk⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
      have h1 : (cLoc w₀ c.1) ^ k = 1 := by
        have h0 : c.1 ^ k = 1 := by simpa using congrArg Subtype.val hk
        rw [← map_pow, h0, map_one]
      have h2 := htf _ (hC c.1 c.2) k hk0 h1
      have h3 : (⟨cLoc w₀ c.1, hC c.1 c.2⟩ : J) = 1 := Subtype.ext h2
      rw [hlam, h3, map_one])
  obtain ⟨s, hs1, hs2⟩ := hCS (l ^ m)
  have hex : ∀ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ,
      ∃ F : algForms W, ∀ v g, F.1 v g = ((χ (ℓ g) : ℂˣ) : ℂ) * f.1 v g := fun χ =>
    GlobalTheory.T.exists_algebraicModularForm_mul_archInvariant E a W f (fun g => ((χ (ℓ g) : ℂˣ) : ℂ)) (hℓa fun y => ((χ y : ℂˣ) : ℂ))
      fun g x hx => by simp only [hℓi g x hx]
  choose F hF using hex
  have hpart : ∀ χ ∈ s, F χ ∈ part W K
      (fun U => ∃ χ : Multiplicative (ZMod (l ^ m)) →* ℂˣ, χ ≠ 1 ∧ GlobalTheory.CongW.HasTypeVec w₀ K J θ χ U) := by
    intro χ hχ
    have h := hTw E a w₀ K W J _ θ χ hC (fun k hk => hK.one k hk w₀ (not_apart_self w₀)) (F χ)
      (fun c hc v g => by
        rw [hF, hF, hℓC g ⟨c, hc⟩, hf c hc v g, map_mul, Units.val_mul, hlam, mul_comm (((χ (ℓ g) : ℂˣ) : ℂ))]
        ring)
    refine (?_ : part W K _ ≤ part W K _) h
    exact iSup₂_le fun π hπ => le_iSup₂_of_le π ⟨χ, hs1 χ hχ, hπ⟩ le_rfl
  refine ⟨-∑ χ ∈ s, F χ, neg_mem (sum_mem hpart), fun g => 1 + ∑ χ ∈ s, ((χ (ℓ g) : ℂˣ) : ℂ), ?_, ?_⟩
  · intro g
    rcases hs2 (ℓ g) with h | h
    · simp only [h, map_zero, norm_zero]
      positivity
    · simp only [h]
      rw [map_natCast, Nat.cast_pow, norm_pow]
  · intro v g
    have e : ((-∑ χ ∈ s, F χ : algForms W) : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v g = -∑ χ ∈ s, (F χ).1 v g := by
      simp [Finset.sum_apply, LinearMap.sum_apply]
    change f.1 v g - ((-∑ χ ∈ s, F χ : algForms W) : W.Sp →ₗ[ℂ] (UA E a → ℂ)) v g = _
    rw [e, Finset.sum_congr rfl fun χ _ => hF χ v g, ← Finset.sum_mul]
    ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.DetBound
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.NormDetLeAlt
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh59.Qbar :
    (l : ℕ) → [Fact (Nat.Prime l)] → Type :=
    fun (l : ℕ) [Fact (Nat.Prime l)] ↦ PadicAlgCl l

theorem UpperTheory.Reformulated.B.Qh59.norm_det_le :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] (ι : UpperTheory.Reformulated.B.Qh59.Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ)
      (R : ℝ),
      (1 : ℝ) ≤ R →
        (∀ (i j : Fin n), ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh59.Qbar l) (M i j)‖ ≤ R) →
          ‖(ι.symm : ℂ → UpperTheory.Reformulated.B.Qh59.Qbar l) M.det‖ ≤ R ^ n := by
  intro l inst ι n M R hR h
  have hR0 : (0 : ℝ) ≤ R := le_trans zero_le_one hR
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Matrix.det_apply', map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (pow_nonneg hR0 n) ?_
  intro σ _
  rw [map_mul, map_prod, norm_mul, norm_prod, map_intCast]
  have h1 : ‖(((Equiv.Perm.sign σ : ℤˣ) : ℤ) : UpperTheory.Reformulated.B.Qh59.Qbar l)‖ ≤ 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs <;> simp [hs]
  have h2 : ∏ i : Fin n, ‖ι.symm (M (σ i) i)‖ ≤ R ^ n := by
    calc ∏ i : Fin n, ‖ι.symm (M (σ i) i)‖ ≤ ∏ _i : Fin n, R :=
          Finset.prod_le_prod₀ (fun i _ => norm_nonneg _) (fun i _ => h _ _)
      _ = R ^ n := by simp
  calc _ ≤ 1 * R ^ n :=
        mul_le_mul h1 h2 (Finset.prod_nonneg fun i _ => norm_nonneg _) zero_le_one
    _ = R ^ n := one_mul _
end

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private lemma norm_det_le {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (R : ℝ)
    (hR : 1 ≤ R) (h : ∀ i j, ‖ι.symm (M i j)‖ ≤ R) : ‖ι.symm M.det‖ ≤ R ^ n :=
  _root_.UpperTheory.Reformulated.B.Qh59.norm_det_le ι M R hR h

theorem UpperTheory.Gal.Gen.detBound_pf :
    UpperTheory.Gal.Gen.DetBound := by
  intro l _ ι T _ n lam A R hR h
  have hR0 : (0 : ℝ) ≤ R := zero_le_one.trans hR
  rw [Formalism.L2.DIV.detTw_eq, map_prod, norm_prod, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) fun τ _ => ?_
  have h1 := norm_det_le ι ((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) R hR fun i j => (h τ i j).1
  have h2 := norm_det_le ι (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) R hR fun i j => (h τ i j).2
  have hinv : (((A τ)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det =
      (((A τ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_right ?_
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  rw [pow_mul]
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (lam τ).detShift
  · rw [hk, zpow_natCast, map_pow, norm_pow, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h1 k
  · rw [hk, zpow_neg, zpow_natCast, ← inv_pow, ← hinv, map_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
    exact pow_le_pow_left₀ (norm_nonneg _) h2 k
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.SizeLe
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound

private def sz {a : ℕ} (lam : DomWeight a) : ℕ := ∑ k, (lam.w k).natAbs

private theorem sz_dual {a : ℕ} (lam : DomWeight a) : sz lam.dual = sz lam := by
  unfold sz DomWeight.dual
  simp only [Int.natAbs_neg]
  exact Fintype.sum_equiv Fin.revPerm _ _ (fun k => by simp)

private theorem one_le {a : ℕ} (lam : DomWeight a) :
    ∑ i, lam.natW i + a * lam.detShift.natAbs ≤ a * (2 * sz lam) := by
  have key : ∀ i : Fin a, lam.natW i + lam.detShift.natAbs ≤ 2 * sz lam := by
    intro i
    have ha : 0 < a := i.pos
    have hd : lam.detShift = lam.w ⟨a - 1, by omega⟩ := by
      simp only [DomWeight.detShift, dif_pos ha]
    have hnat : lam.natW i = (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat := by
      simp only [DomWeight.natW, hd]
    have hLle : (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam := by
      unfold sz
      exact Finset.single_le_sum (f := fun k => (lam.w k).natAbs) (fun k _ => Nat.zero_le _)
        (Finset.mem_univ _)
    rw [hnat, hd]
    by_cases hi : i = ⟨a - 1, by omega⟩
    · have h0 : (lam.w i - lam.w ⟨a - 1, by omega⟩).toNat = 0 := by
        rw [hi, sub_self]; rfl
      omega
    · have hpair : (lam.w i).natAbs + (lam.w ⟨a - 1, by omega⟩).natAbs ≤ sz lam := by
        unfold sz
        have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun k => (lam.w k).natAbs)
          (Finset.subset_univ {i, ⟨a - 1, by omega⟩}) (fun _ _ _ => Nat.zero_le _)
        rwa [Finset.sum_pair hi] at h
      omega
  calc ∑ i, lam.natW i + a * lam.detShift.natAbs
      = ∑ i, (lam.natW i + lam.detShift.natAbs) := by
        simp [Finset.sum_add_distrib]
    _ ≤ ∑ _i : Fin a, 2 * sz lam := Finset.sum_le_sum fun i _ => key i
    _ = a * (2 * sz lam) := by simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

private noncomputable def emb : InfinitePlace E ⊕ InfinitePlace E → (E →+* ℂ)
  | .inl v => v.embedding
  | .inr v => ComplexEmbedding.conjugate v.embedding

private theorem mk_emb_inl (v : InfinitePlace E) : InfinitePlace.mk (emb (.inl v)) = v :=
  InfinitePlace.mk_embedding v

private theorem mk_emb_inr (v : InfinitePlace E) : InfinitePlace.mk (emb (.inr v)) = v := by
  simp [emb]

private theorem emb_injective : Function.Injective (emb (E := E)) := by
  intro x y h
  have hm : InfinitePlace.mk (emb x) = InfinitePlace.mk (emb y) := by rw [h]
  rcases x with v | v <;> rcases y with w | w <;>
    simp only [mk_emb_inl, mk_emb_inr] at hm <;> subst hm
  · rfl
  · simp only [emb] at h
    exact absurd h.symm (conjugate_ne _)
  · simp only [emb] at h
    exact absurd h (conjugate_ne _)
  · rfl

private theorem two_le (W : Wt E a) : ∑ v, 2 * sz (W v) ≤ GlobalTheory.CongW.wtSize W.at := by
  have h1 : ∑ v, 2 * sz (W v)
      = ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s)) := by
    rw [Fintype.sum_sum_type]
    simp only [emb, Wt.at_embedding, Wt.at_conjugate, sz_dual, two_mul, Finset.sum_add_distrib]
  have h2 : ∑ s : InfinitePlace E ⊕ InfinitePlace E, sz (W.at (emb s))
      = ∑ τ ∈ Finset.univ.map ⟨emb, emb_injective⟩, sz (W.at τ) := by
    rw [Finset.sum_map]; rfl
  have h3 : GlobalTheory.CongW.wtSize W.at = ∑ τ, sz (W.at τ) := rfl
  rw [h1, h2, h3]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)

end UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound

open UpperTheory.Gal.Gen.SeparatingAlgebraSizeBound in
theorem UpperTheory.Gal.Gen.sizeLe_pf :
    UpperTheory.Gal.Gen.SizeLe := by
  intro E _ _ _ a W
  calc (∑ v, ∑ i, (W v).natW i) + ∑ v, a * (W v).detShift.natAbs
      = ∑ v, (∑ i, (W v).natW i + a * (W v).detShift.natAbs) := Finset.sum_add_distrib.symm
    _ ≤ ∑ v, a * (2 * sz (W v)) := Finset.sum_le_sum fun v _ => one_le (W v)
    _ = a * ∑ v, 2 * sz (W v) := by rw [Finset.mul_sum]
    _ ≤ a * GlobalTheory.CongW.wtSize W.at := Nat.mul_le_mul_left a (two_le W)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.LatFacts
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.latFacts_pf :
    UpperTheory.Gal.Gen.LatFacts := by
  classical
  intro l _ ι σ V _
  refine ⟨fun φ => ?_, fun x => ?_⟩
  · let B := Module.finBasis ℂ V
    open MvPolynomial in
    have h : ∀ i, ∃ (s : Finset (σ →₀ ℕ)) (a : s → ℂ), ∀ v : V,
        B.repr v i = ∑ m : s, a m * AddMonoidAlgebra.coeff (v : MvPolynomial σ ℂ) m.1 := by
      intro i
      classical
      let s : Finset (σ →₀ ℕ) := Finset.univ.biUnion fun j => ((B j : V) : MvPolynomial σ ℂ).support
      let R : V →ₗ[ℂ] (s → ℂ) := LinearMap.pi fun m => (lcoeff ℂ m.1).comp V.subtype
      have hR : LinearMap.ker R = ⊥ := by
        refine LinearMap.ker_eq_bot'.2 fun v hv => ?_
        have h0 : ∀ m : s, AddMonoidAlgebra.coeff (v : MvPolynomial σ ℂ) m.1 = 0 := fun m => congrFun hv m
        refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
        by_cases hm : m ∈ s
        · simpa using h0 ⟨m, hm⟩
        · have hv' : (v : MvPolynomial σ ℂ) = ∑ j, B.repr v j • ((B j : V) : MvPolynomial σ ℂ) := by
            calc (v : MvPolynomial σ ℂ) = ((∑ j, B.repr v j • B j : V) : MvPolynomial σ ℂ) := by rw [B.sum_repr v]
              _ = _ := by rw [Submodule.coe_sum]; rfl
          rw [hv', coeff_sum]
          simp only [coeff_smul, ZeroMemClass.coe_zero, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
          refine Finset.sum_eq_zero fun j _ => ?_
          have : m ∉ ((B j : V) : MvPolynomial σ ℂ).support := fun h =>
            hm (Finset.mem_biUnion.2 ⟨j, Finset.mem_univ _, h⟩)
          rw [notMem_support_iff.1 this, smul_zero]
      obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective R hR
      refine ⟨s, fun m => B.repr (L (Pi.single m 1)) i, fun v => ?_⟩
      have e1 : B.repr v i = ((B.coord i).comp L) (R v) := by
        rw [LinearMap.comp_apply, ← LinearMap.comp_apply L R, hL, LinearMap.id_apply, Module.Basis.coord_apply]
      rw [e1, LinearMap.pi_apply_eq_sum_univ ((B.coord i).comp L) (R v)]
      refine Finset.sum_congr rfl fun m _ => ?_
      have hs : (fun j => if m = j then (1 : ℂ) else 0) = Pi.single m 1 := by
        funext j
        simp [Pi.single_apply, eq_comm]
      rw [hs, smul_eq_mul, mul_comm]
      rfl
    choose s a ha using h
    refine ⟨∑ i, ∑ m : s i, ‖ι.symm (a i m)‖ * ‖ι.symm (φ (B i))‖,
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun m _ => mul_nonneg (norm_nonneg _) (norm_nonneg _),
      fun R x hx => ?_⟩
    have e : φ x = ∑ i, B.repr x i * φ (B i) := by
      have h := congrArg φ (B.sum_repr x)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at h
      rw [← h]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    have h1 : ∀ i, ‖ι.symm (B.repr x i)‖ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R := by
      intro i
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ha i x, map_sum, Finset.sum_mul]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [map_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left (hx _) (norm_nonneg _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_mul, norm_mul, Finset.sum_mul]
    calc _ ≤ (∑ m : s i, ‖ι.symm (a i m)‖) * R * ‖ι.symm (φ (B i))‖ :=
          mul_le_mul_of_nonneg_right (h1 i) (norm_nonneg _)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]; exact Finset.sum_congr rfl fun m _ => by ring
  · have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
    have hl0 : (0 : ℝ) < (l : ℝ)⁻¹ := inv_pos.2 (by linarith)
    set T : ℝ := ∑ m ∈ x.1.support, ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ + 1 with hTdef
    have hS : 0 ≤ ∑ m ∈ x.1.support, ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ :=
      Finset.sum_nonneg fun m _ => norm_nonneg _
    have hT : 0 < T := by linarith
    obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hT) (inv_lt_one_of_one_lt₀ hl)
    have hlc : (l : ℂ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
    refine ⟨(l : ℂ) ^ k, pow_ne_zero _ hlc, fun m => ?_⟩
    have hnl : ‖((l : ℕ) : Qbar l)‖ = (l : ℝ)⁻¹ := by
      have h := PadicAlgCl.norm_extends l (l : ℚ_[l])
      rw [map_natCast, Padic.norm_p] at h
      exact h
    have hn : ‖ι.symm ((l : ℂ) ^ k)‖ = ((l : ℝ)⁻¹) ^ k := by
      rw [map_pow, map_natCast, norm_pow, hnl]
    have hc : ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖ ≤ T := by
      by_cases hm : m ∈ x.1.support
      · have := Finset.single_le_sum (f := fun m => ‖ι.symm (AddMonoidAlgebra.coeff x.1 m)‖)
          (fun m _ => norm_nonneg _) hm
        linarith
      · rw [MvPolynomial.notMem_support_iff.1 hm, map_zero, norm_zero]
        exact hT.le
    have e : AddMonoidAlgebra.coeff (((l : ℂ) ^ k • x : V) : MvPolynomial σ ℂ) m =
        (l : ℂ) ^ k * AddMonoidAlgebra.coeff x.1 m := by
      rw [Submodule.coe_smul, MvPolynomial.coeff_smul, smul_eq_mul]
    rw [e, map_mul, norm_mul, hn]
    calc _ ≤ ((l : ℝ)⁻¹) ^ k * T := mul_le_mul_of_nonneg_left hc (pow_nonneg hl0.le _)
      _ ≤ T⁻¹ * T := mul_le_mul_of_nonneg_right hk.le hT.le
      _ = 1 := inv_mul_cancel₀ hT.ne'
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.BlockBound
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

namespace UpperTheory.Gal.Gen

section CoefLeLemmas

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {σ : Type}

private lemma coefLe_sum {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) {R : ℝ} (hR : 0 ≤ R)
    (h : ∀ a ∈ s, CoefLe ι R (f a)) : CoefLe ι R (∑ a ∈ s, f a) := by
  intro m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.coeff_sum, map_sum]
  exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR (fun a ha => h a ha m)

private lemma coefLe_mul {R S : ℝ} (hR : 0 ≤ R) (hS : 0 ≤ S) {p q : MvPolynomial σ ℂ}
    (hp : CoefLe ι R p) (hq : CoefLe ι S q) : CoefLe ι (R * S) (p * q) := by
  classical
  intro m
  set_option synthInstance.maxHeartbeats 100000 in
    rw [MvPolynomial.coeff_mul, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (mul_nonneg hR hS) ?_
  intro x _
  rw [map_mul, norm_mul]
  exact mul_le_mul (hp _) (hq _) (norm_nonneg _) hR

private lemma coefLe_one : CoefLe ι 1 (1 : MvPolynomial σ ℂ) := by
  classical
  intro m
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

private lemma coefLe_pow {R : ℝ} (hR : 0 ≤ R) {p : MvPolynomial σ ℂ} (hp : CoefLe ι R p) (k : ℕ) :
    CoefLe ι (R ^ k) (p ^ k) := by
  induction k with
  | zero => simpa using coefLe_one ι
  | succ k ih =>
    rw [pow_succ, pow_succ]
    exact coefLe_mul ι (pow_nonneg hR _) hR ih hp

private lemma coefLe_prod {α : Type} (s : Finset α) (f : α → MvPolynomial σ ℂ) (r : α → ℝ)
    (hr : ∀ a, 0 ≤ r a) (h : ∀ a ∈ s, CoefLe ι (r a) (f a)) :
    CoefLe ι (∏ a ∈ s, r a) (∏ a ∈ s, f a) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using coefLe_one ι
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact coefLe_mul ι (hr a) (Finset.prod_nonneg fun b _ => hr b) (h a (Finset.mem_insert_self a s))
      (ih fun b hb => h b (Finset.mem_insert_of_mem hb))

private lemma coefLe_C_mul_X {c : ℂ} {R : ℝ} (hR : 1 ≤ R) (hc : ‖ι.symm c‖ ≤ R) (v : σ) :
    CoefLe ι R (MvPolynomial.C c * MvPolynomial.X v) := by
  classical
  intro m
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X']
  split_ifs
  · simpa using hc
  · simpa using zero_le_one.trans hR

private lemma coefLe_monomial_image {τ : Type} {y : σ → MvPolynomial τ ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hy : ∀ v, CoefLe ι R (y v)) (m : σ →₀ ℕ) :
    CoefLe ι (R ^ (m.sum fun _ e => e)) (m.prod fun v e => y v ^ e) := by
  have h := coefLe_prod ι m.support (fun v => y v ^ m v) (fun v => R ^ m v)
    (fun _ => pow_nonneg hR _) (fun v _ => coefLe_pow ι hR (hy v) (m v))
  rwa [Finset.prod_pow_eq_pow_sum] at h

end CoefLeLemmas

end UpperTheory.Gal.Gen

theorem UpperTheory.Gal.Gen.blockBound_pf :
    UpperTheory.Gal.Gen.BlockBound := by
  intro l _ ι T n A R hR hA D x hx h1
  classical
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  set y : T × Fin n × Fin n → MvPolynomial (T × Fin n × Fin n) ℂ :=
    fun v => ∑ b : Fin n, MvPolynomial.C (A v.1 v.2.1 b) * MvPolynomial.X (v.1, (b, v.2.2)) with hydef
  have hy : ∀ v, CoefLe ι R (y v) := fun v =>
    coefLe_sum ι _ _ hR0 fun b _ => coefLe_C_mul_X ι hR (hA _ _ _) _
  have e : Formalism.GradedWeylDivisibility.blockAct ℂ A x =
      ∑ m ∈ x.support, MvPolynomial.C (AddMonoidAlgebra.coeff x m) * (m.prod fun v e => y v ^ e) := by
    conv_lhs => rw [x.as_sum]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Formalism.GradedWeylDivisibility.blockAct, MvPolynomial.aeval_monomial]
    rfl
  rw [e]
  refine coefLe_sum ι _ _ (pow_nonneg hR0 _) fun m hm k => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul, norm_mul]
  have hdeg : (m.sum fun _ e => e) ≤ D := (MvPolynomial.le_totalDegree hm).trans hx
  calc _ ≤ 1 * R ^ (m.sum fun _ e => e) :=
        mul_le_mul (h1 m) (coefLe_monomial_image ι hR0 hy m k) (norm_nonneg _) zero_le_one
    _ ≤ R ^ D := by
        rw [one_mul]
        exact pow_le_pow_right₀ hR hdeg
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.NormMapIntegerLeOne
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem norm_map_integer_le_one {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime]
    (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l) (hl : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hj : Continuous j) (y : u.adicCompletion E) (hy : y ∈ u.adicCompletionIntegers E) : ‖j y‖ ≤ 1 := by
  have hvl : Valued.v ((l : ℕ) : u.adicCompletion E) < 1 := by
    have h1 : u.valuation E (((l : ℕ) : 𝓞 E) : E) < 1 :=
      (HeightOneSpectrum.valuation_lt_one_iff_mem (K := E) u _).2 hl
    have h2 : (((l : ℕ) : u.adicCompletion E)) = algebraMap E (u.adicCompletion E) (((l : ℕ) : 𝓞 E) : E) := by simp
    rw [h2]
    exact (HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _).trans_lt h1
  have hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹ := by
    have h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]
  have hlt : ∀ k : ℕ, ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k < 1 := by
    intro k
    have hyv : Valued.v y ≤ 1 := hy
    have hv : Valued.v (((l : ℕ) : u.adicCompletion E) * y ^ k) < 1 := by
      rw [map_mul, map_pow]
      exact mul_lt_one_of_lt_of_le hvl (pow_le_one' hyv k)
    have ht := Valued.tendsto_zero_pow_of_v_lt_one hv
    have ht2 : Filter.Tendsto (fun m : ℕ => (j (((l : ℕ) : u.adicCompletion E) * y ^ k)) ^ m) Filter.atTop (nhds 0) := by
      have := (hj.tendsto 0).comp ht
      simpa [Function.comp_def, map_pow] using this
    have := tendsto_pow_atTop_nhds_zero_iff_norm_lt_one.1 ht2
    simpa [map_mul, map_pow, norm_mul, norm_pow] using this
  by_contra hcon
  have hgt : 1 < ‖j y‖ := not_le.1 hcon
  have hlpos : 0 < ‖j ((l : ℕ) : u.adicCompletion E)‖ := by
    rw [hlnorm]
    exact inv_pos.2 (by exact_mod_cast (Fact.out : l.Prime).pos)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (‖j ((l : ℕ) : u.adicCompletion E)‖⁻¹) hgt
  have := hlt k
  have h3 : 1 < ‖j ((l : ℕ) : u.adicCompletion E)‖ * ‖j y‖ ^ k := by
    rw [inv_lt_iff_one_lt_mul₀ hlpos] at hk
    exact hk.trans_eq (mul_comm _ _)
  linarith

private theorem norm_map_entry_le {E : Type} [Field E] [NumberField E] (l : ℕ) [Fact l.Prime] {n : ℕ}
    (u : HeightOneSpectrum (𝓞 E)) (j : u.adicCompletion E →+* Qbar l) (hl : ((l : ℕ) : 𝓞 E) ∈ u.asIdeal)
    (hj : Continuous j) (d : ℕ) (M : Matrix (Fin n) (Fin n) (u.adicCompletion E))
    (hM : GlobalTheory.CongW.IntMat u (((l : u.adicCompletion E) ^ d) • M)) (a b : Fin n) : ‖j (M a b)‖ ≤ (l : ℝ) ^ d := by
  have h1 := norm_map_integer_le_one l u j hl hj _ (hM a b)
  have hlnorm : ‖j ((l : ℕ) : u.adicCompletion E)‖ = (l : ℝ)⁻¹ := by
    have h0 : ((l : ℕ) : Qbar l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
    rw [map_natCast, h0, PadicAlgCl.norm_extends (p := l) (l : ℚ_[l]), Padic.norm_p]
  have hl0 : (0 : ℝ) < (l : ℝ) ^ d := pow_pos (by exact_mod_cast (Fact.out : l.Prime).pos) d
  rw [Matrix.smul_apply, smul_eq_mul, map_mul, map_pow, norm_mul, norm_pow, hlnorm, inv_pow] at h1
  rwa [inv_mul_le_iff₀ hl0, mul_one] at h1

theorem UpperTheory.Gal.Gen.kappa_pf :
    UpperTheory.Gal.Gen.Kappa := by
  intro E _ _ _ l _ ι n
  have hex := fun v : InfinitePlace E =>
    GlobalTheory.LadicInf.exists_place E l (ι.symm.toRingHom.comp v.embedding)
  choose u j hl hj hjE using hex
  let f : InfinitePlace E → Af E →+* ℂ := fun v =>
    ι.toRingHom.comp ((j v).comp (pLoc E (u v)))
  let κ : UA E n →* (InfinitePlace E → GL (Fin n) ℂ) :=
    MonoidHom.pi fun v => (Matrix.GeneralLinearGroup.map ((f v).comp (pFin E))).comp (UA E n).subtype
  have hκ : ∀ (g : UA E n) (v : InfinitePlace E),
      κ g v = Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (j v)) (cLoc (u v) g) := by
    intro g v
    ext
    rfl
  refine ⟨κ, ?_, ?_, ?_⟩
  · rintro γ ⟨g₀, hg₀⟩
    funext v
    ext a b
    change (f v) (pFin E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b)) =
      coord v.embedding (pInf E ((γ.1 : Matrix (Fin n) (Fin n) (Ad E)) a b))
    have hg₁ : (γ.1 : GL (Fin n) (Ad E)) = ratGL E n g₀ := hg₀.symm
    rw [hg₁]
    change (f v) (pFin E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b))) =
      coord v.embedding (pInf E (algebraMap E (Ad E) ((g₀ : Matrix (Fin n) (Fin n) E) a b)))
    rw [coord_algebraMap]
    have h := congrArg (fun φ : E →+* Qbar l => φ ((g₀ : Matrix (Fin n) (Fin n) E) a b)) (hjE v)
    simp only [RingHom.coe_comp, Function.comp_apply] at h
    change ι (j v (algebraMap E (u v |>.adicCompletion E) _)) = _
    rw [h]
    simp
  · intro x hx
    funext v
    have hx' : Matrix.GeneralLinearGroup.map (pFin E) x.1 = 1 := hx
    have h2 : Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 =
        Matrix.GeneralLinearGroup.map (f v) (Matrix.GeneralLinearGroup.map (pFin E) x.1) := by ext; rfl
    change Matrix.GeneralLinearGroup.map ((f v).comp (pFin E)) x.1 = 1
    rw [h2, hx', map_one]
  · intro g d hd v a b
    obtain ⟨h1, h2⟩ := hd (u v) (hl v)
    constructor
    · rw [hκ g v]
      change ‖ι.symm (ι (j v (((cLoc (u v) g : GL (Fin n) ((u v).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _
      rw [RingEquiv.symm_apply_apply]
      exact norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h1 a b
    · rw [hκ g v, ← map_inv]
      change ‖ι.symm (ι (j v ((((cLoc (u v) g)⁻¹ : GL (Fin n) ((u v).adicCompletion E)) :
        Matrix (Fin n) (Fin n) ((u v).adicCompletion E)) a b)))‖ ≤ _
      rw [RingEquiv.symm_apply_apply]
      exact norm_map_entry_le l (u v) (j v) (hl v) (hj v) d _ h2 a b
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SeparatingAlgebras.FrameW
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.DefU
open UpperTheory.Gal.Gen

private theorem cAll_fin' {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {c : UA E n}
    (hc : c ∈ finU (E := E) (n := n)) : cAll c = 1 := by
  funext v
  have : cInf c = 1 := hc
  simp [cAll, cEmb, this]

theorem UpperTheory.Gal.Gen.frameW_pf :
    UpperTheory.Gal.Gen.Kappa → UpperTheory.Gal.Gen.DenomBdd → UpperTheory.Gal.Gen.RhoBound → UpperTheory.Gal.Gen.LatFacts → UpperTheory.Gal.Gen.LevelEx → UpperTheory.Gal.Gen.FrameW := by
  intro hK hD hR hL hE E _ _ _ l _ ι a W J t ht
  classical
  have hlp : l.Prime := Fact.out
  obtain ⟨κ, hκr, hκi, hκd⟩ := hK E l ι a
  let ρ := Formalism.L2.DIV.rhoK (K := ℂ) (ι := InfinitePlace E) W
  let M : UA E a → (InfinitePlace E → GL (Fin a) ℂ) := fun g => (cAll g)⁻¹ * κ g
  let b : UA E a → {x : W.Sp // CoefLe ι 1 x.1} → W.Sp := fun g x => ρ (M g) x.1
  have hl1 : (1 : ℝ) ≤ (l : ℝ) := by exact_mod_cast hlp.one_lt.le
  have hpow : ∀ d : ℕ, (1 : ℝ) ≤ (l : ℝ) ^ d := fun d => one_le_pow₀ hl1
  have hgrow : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 →
      CoefLe ι (((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at)) (ρ (κ c) x).1 := fun c d hc x hx =>
    hR E l ι a W (κ c) _ (hpow d) (fun τ i j => hκd c d hc τ i j) x hx
  have hgrowInv : ∀ (c : UA E a) (d : ℕ), DenomLe l d c → ∀ x : W.Sp, CoefLe ι 1 x.1 →
      CoefLe ι (((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at)) (ρ (κ c)⁻¹ x).1 := fun c d hc x hx =>
    hR E l ι a W (κ c)⁻¹ _ (hpow d) (fun τ i j => by
      have h := hκd c d hc τ i j
      simp only [Pi.inv_apply, inv_inv]
      exact ⟨h.2, h.1⟩) x hx
  have hval : ∀ f : algForms W, ∀ γ ∈ ratU E a, ∀ s x, x ∈ infU E a → ∀ c : finU (E := E) (n := a),
      (∀ v g, f.1 v (g * (c : UA E a)) = f.1 v g) → ∀ v,
      f.1 (ρ (M (γ * s * x * c)) v) (γ * s * x * c) = f.1 (ρ (M s) (ρ (κ (c : UA E a)) v)) s := by
    intro f γ hγ s x hx c hf v
    have hM : cAll x * M (γ * s * x * c) = M s * κ (c : UA E a) := by
      simp only [M, map_mul, hκr γ hγ, hκi x hx, cAll_fin' c.2, mul_one]
      group
    have hA : ∀ v, f.1 v (γ * s * x * c) = f.1 v (s * c * x) := by
      intro v
      rw [mul_assoc γ s, mul_assoc γ, (f.2.1 v).left γ hγ, mul_assoc s x, ← fin_mul_inf c.2 hx, ← mul_assoc]
    have hB : ∀ v, f.1 v (s * c * x) = f.1 (W.rep ⟨x, hx⟩ v) (s * c) := by
      intro v
      rw [f.2.2 ⟨x, hx⟩ v]
      rfl
    have e3 : W.rep ⟨x, hx⟩ (ρ (M (γ * s * x * c)) v) = ρ (M s) (ρ (κ (c : UA E a)) v) := by
      change ρ (cAll x) (ρ (M _) v) = _
      rw [← Module.End.mul_apply, ← map_mul, hM, map_mul, Module.End.mul_apply]
    rw [hA, hB, hf, e3]
  refine ⟨{x : W.Sp // CoefLe ι 1 x.1}, b, ?_, ?_, ?_⟩
  · intro f
    obtain ⟨C, hC, hfC⟩ := hE E a W f
    obtain ⟨d, hd⟩ := hD E l hlp a C hC.compact
    let C₃ : Subgroup (finU (E := E) (n := a)) := C.subgroupOf (finU (E := E) (n := a))
    have hC₃o : IsOpen (C₃ : Set (finU (E := E) (n := a))) := by
      obtain ⟨N, hNo, hN1, hNC⟩ := hC.isOpen
      refine Subgroup.isOpen_of_mem_nhds _ (g := 1)
        (Filter.mem_of_superset ((hNo.preimage continuous_subtype_val).mem_nhds hN1) ?_)
      intro x hx
      exact Subgroup.mem_subgroupOf.2 (hNC ⟨hx, x.2⟩)
    obtain ⟨S, hS⟩ := GlobalTheory.DefU.ClassFin.classSet_finite E a C₃ hC₃o
    let φ : UA E a → (W.Sp →ₗ[ℂ] ℂ) := fun s => (LinearMap.proj s) ∘ₗ f.1 ∘ₗ (ρ (M s))
    have hφ : ∀ s, ∃ m : ℝ, 0 ≤ m ∧ ∀ (R : ℝ) (x : W.Sp), CoefLe ι R x.1 → ‖ι.symm (φ s x)‖ ≤ m * R :=
      fun s => (hL l ι _ (Formalism.L2.DIV.VV ℂ W)).1 (φ s)
    choose m hm0 hm using hφ
    refine ⟨(∑ s ∈ S, m s) * ((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at), fun g i => ?_⟩
    obtain ⟨γ, hγ, s, hs, y, hy, c, hc, rfl⟩ := hS g
    have hcC : (c : UA E a) ∈ C := Subgroup.mem_subgroupOf.1 hc
    have e := hval f γ hγ s y hy c (fun v g => hfC _ hcC v g) i.1
    have hb : f.1 (b (γ * s * y * c) i) (γ * s * y * c) = φ s (ρ (κ (c : UA E a)) i.1) := e
    rw [hb]
    refine (hm s _ _ (hgrow _ d (hd _ hcC) i.1 i.2)).trans ?_
    exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (fun q _ => hm0 q) hs) (by positivity)
  · intro f h0
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    funext g
    obtain ⟨c, hc0, hc⟩ := (hL l ι _ (Formalism.L2.DIV.VV ℂ W)).2 (ρ (M g)⁻¹ v)
    have h1 := h0 g ⟨c • ρ (M g)⁻¹ v, hc⟩
    have h2 : b g ⟨c • ρ (M g)⁻¹ v, hc⟩ = c • v := by
      change ρ (M g) (c • ρ (M g)⁻¹ v) = c • v
      rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [h2, map_smul, Pi.smul_apply, smul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hc0
  · intro F R hF j g i
    have hR0 : 0 ≤ R := (norm_nonneg _).trans (hF g i)
    have e : opOf (RU E a) (t j) (F (b g i)) g = ∑ h ∈ (t j).support, t j h * F (b g i) (g * h) := by
      simp only [opOf, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, RU_apply, smul_eq_mul]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hR0 fun h hh => ?_
    obtain ⟨hfin, d, hd, hn⟩ := ht j h hh
    have hMh : M g = M (g * h) * (κ h)⁻¹ := by
      simp only [M, map_mul, cAll_fin' hfin, mul_one]
      group
    set y : W.Sp := ρ (κ h)⁻¹ i.1 with hy
    have hyc := hgrowInv h d hd i.1 i.2
    have hx : CoefLe ι 1 ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) := by
      intro q
      have hq := hyc q
      have e1 : AddMonoidAlgebra.coeff ((t j h • y : W.Sp) : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) q =
          t j h * AddMonoidAlgebra.coeff (y : Formalism.L2.DIV.Pol ℂ (InfinitePlace E) a) q := by
        simp [MvPolynomial.coeff_smul]
      rw [e1, map_mul, norm_mul]
      have hlpos : (0 : ℝ) < (l : ℝ) := by linarith
      calc _ ≤ ((l : ℝ)⁻¹) ^ (a * d * GlobalTheory.CongW.wtSize W.at) * ((l : ℝ) ^ d) ^ (a * GlobalTheory.CongW.wtSize W.at) :=
            mul_le_mul hn hq (norm_nonneg _) (by positivity)
        _ = 1 := by
            rw [← pow_mul, inv_pow, show d * (a * GlobalTheory.CongW.wtSize W.at) = a * d * GlobalTheory.CongW.wtSize W.at by ring]
            exact inv_mul_cancel₀ (by positivity)
    have hb : t j h * F (b g i) (g * h) = F (b (g * h) ⟨t j h • y, hx⟩) (g * h) := by
      have : b g i = ρ (M (g * h)) y := by
        change ρ (M g) i.1 = _
        rw [hMh, map_mul, Module.End.mul_apply]
      change _ = F (ρ (M (g * h)) (t j h • y)) (g * h)
      rw [this, map_smul, map_smul, Pi.smul_apply, smul_eq_mul]
    rw [hb]
    exact hF _ _
end
