module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.OpenEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.EigBoxE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.IrrOpen
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.LamDer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.UnrAlgE
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalDescent.GLDenseRanges.InertiaPartMaps.UnrAlgW
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.DerivativeDivisibility.CoefInj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.LogarithmicNormBounds.LinkedUnlEOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.PlacesOverFinite.LinkUnr
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.AbsMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.OffSelf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PlainTorsionPairs.CRealAv
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.WStmtx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.PrSeedPtOf

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.ChainRankFourGood
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.UnrE
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.KeepIrrOpenW
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.CA Formalism.MainNotions.N
namespace UpperTheory.V.J
theorem irrOpenW_alt : _root_.UpperTheory.V.J.IrrOpenAlt := by
  intro l _ L Ω _ _ _ _ _ _ s V c n r B ι J hn hE x hx
  have irr_iff_span {Γ : Type} [Group Γ] (r : Γ →* GL (Fin n) (Qbar l)) :
      IsIrr r ↔ Submodule.span (Qbar l) (Set.range (mat r)) = ⊤ := by
    have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
    rw [← UpperTheory.V.AlgebraTools.Det.irrIffSpan]
    constructor
    · intro h N hN
      obtain ⟨-, -, hIrr⟩ := h
      exact hIrr N le_top fun g v hv => hN g v hv
    · intro h
      exact ⟨top_ne_bot, fun g v _ => Submodule.mem_top, fun N _ hN => h N fun g v hv => hN g v hv⟩
  have gram_at {A G H K : Type} [CommRing A] [Group G] [Group H] [CommRing K]
      (D : GDet n A G) (f : A →+* K) (φ : H →* G) (ρ : H →* Matrix (Fin n) (Fin n) K)
      (h : (D.map f).comap φ = GDet.ofRep ρ) (g : Fin n × Fin n → H) :
      f (Matrix.det (Matrix.of fun a b => D.tr (MonoidAlgebra.single (φ (g a * g b)) 1))) =
        Matrix.det (Matrix.of fun a b => (ρ (g a) * ρ (g b)).trace) := by
    have trace_at (a : H) : f (D.tr (MonoidAlgebra.single (φ a) 1)) = (ρ a).trace := by
      have hmap : f (D.tr (MonoidAlgebra.single (φ a) 1)) =
          (D.map f).tr (MonoidAlgebra.single (φ a) 1) := by
        have hcoeff := ((d_gmap D).2.2.1 f (MonoidAlgebra.single (φ a) 1)).2 1
        simpa [GDet.tr, MonoidAlgebra.coeff_mapRingHom] using hcoeff.symm
      have hcomap : ((D.map f).comap φ).tr (MonoidAlgebra.single a 1) =
          (D.map f).tr (MonoidAlgebra.single (φ a) 1) := by
        have hchi : ((D.map f).comap φ).chi (MonoidAlgebra.single a 1) =
            (D.map f).chi (MonoidAlgebra.single (φ a) 1) := by
          show (D.map f).D (Polynomial K) (MonoidAlgebra.mapDomainRingHom (Polynomial K) φ
            (MonoidAlgebra.single 1 Polynomial.X -
              MonoidAlgebra.mapRingHom H Polynomial.C (MonoidAlgebra.single a 1))) = _
          congr 1
          rw [map_sub]
          simp [MonoidAlgebra.mapDomainRingHom_apply, MonoidAlgebra.mapDomain_single]
        simp only [GDet.tr, GDet.lam, hchi]
      rw [hmap, ← hcomap, h, ← (d_toDet _ _).2.2.1, d_toDet_ofRep.1 ρ,
        (d_ofRep _ _ _).2.2.1 hn, GDet.repAlg, MonoidAlgebra.lift_single, one_smul]
      congr 1
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    rw [trace_at, map_mul]
  obtain ⟨ρ, -, hρ, hirr⟩ := hx
  obtain ⟨m, hm, hdet⟩ := (g_gram _ _ _).1 ((irr_iff_span ρ).1 hirr)
  choose g hg using hm
  refine ⟨Matrix.det (Matrix.of fun a b => B.u.D.tr (MonoidAlgebra.single (V.pr (g a * g b)) 1)), ?_, ?_⟩
  · intro h0
    refine hdet ?_
    have h1 := gram_at B.u.D (x : B.B →+* Qbar l) V.pr (mat ρ) hρ g
    have h2 := h1.symm.trans h0
    simpa only [hg] using h2
  · intro y w hJ hy hy0
    have hA : y.Arith w := ⟨hy.1, fun v j => by
      obtain ⟨ph, hph, -⟩ := hy.2 v
      exact ⟨ph j, hph j⟩⟩
    obtain ⟨ρ', hc', -, hρ', -⟩ := _root_.UpperTheory.GalN.V.end1W' hE y w hJ hA
    refine ⟨ρ', hc', hρ', (irr_iff_span ρ').2 ((g_gram _ _ _).2 ⟨fun a => mat ρ' (g a), fun a => ⟨_, rfl⟩, fun h => hy0 ?_⟩)⟩
    have h1 := gram_at B.u.D (y : B.B →+* Qbar l) V.pr (mat ρ') hρ' g
    exact h1.trans h
end UpperTheory.V.J
end
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V UpperTheory.V.HV UpperTheory.V.W
open UpperTheory.V.Z.Desc.V0
theorem UpperTheory.V.Z.Desc.V0.unramified_at_of_dense_purity_num_e_power_series :
    UnrAlgE → ∀ (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (s : HidaSetting l L Ω) (V : s.Lev) (c : Coef l) (n : ℕ) (r : Resid V.frame c.O n) (B : UniversalOrdinaryDeterminantRing r) (Λ : LamObj r)
    (ι : Qbar l ≃+* ℂ) (J : Ideal B.B) (m : ℕ), 1 ≤ n → Nonempty (Λ.Λ ≃ₐ[c.O] MvPowerSeries (Fin m) c.O) →
    B.Dense J → B.arithmeticPointPurityDense ι J → NumE B Λ J → UpperTheory.V.J.UnrAt B J := by
  intro hU l _ L Ω _ _ _ _ _ _ s V c n r B Λ ι J m hn hiso hD hE hN
  obtain ⟨M, _, _, _, h, e₀, hId, hmu⟩ := hN
  intro x w hJ hA hI δ hδ hJδ hψ
  obtain ⟨b₀, hb₀, hopen⟩ := _root_.UpperTheory.V.J.irrOpenW_alt l L Ω s V c n r B ι J hn hE x hI
  have hlam := UpperTheory.V.J.lamDer l L Ω s V c n r B Λ x m hiso δ hδ hψ
  have hdense : ∀ a : B.B, (∀ y ∈ {y : B.Pt | J ≤ RingHom.ker y ∧ y.Good w}, y a = 0) → a ∈ J :=
    fun a ha => hD w hA.1 a fun y hy hg => ha y ⟨hy, hg⟩
  have hex : ∃ y : B.Pt, (J ≤ RingHom.ker y ∧ y.Good w) ∧ y b₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hb₀ (hJ (hdense b₀ hcon))
  obtain ⟨y₀, hy₀, hyb₀⟩ := hex
  have hone := (hmu x y₀ w hJ hy₀.1 hA hy₀.2 hI (hopen y₀ w hy₀.1 hy₀.2 hyb₀)).1
  obtain ⟨e⟩ := hiso
  haveI : IsDomain (MvPowerSeries (Fin m) c.O) := GlobalTheory.CohenStructure.isDomain_mvPowerSeries c.O m
  haveI : IsDomain Λ.Λ := e.toRingEquiv.toMulEquiv.isDomain _
  haveI : IsIntegrallyClosed (MvPowerSeries (Fin m) c.O) := GlobalTheory.CohenStructure.isIntegrallyClosed_mvPowerSeries c.O m
  haveI : IsIntegrallyClosed Λ.Λ := IsIntegrallyClosed.of_equiv e.toRingEquiv.symm
  haveI : IsNoetherianRing Λ.Λ := UpperTheory.V.Alg.IsCO.toIsNoetherian (O := c.O)
  haveI : CharZero Λ.Λ := by
    haveI : CharZero c.O :=
      (RingHom.charZero_iff (ϕ := (c.O.val : c.O →ₐ[ℤ_[l]] PadicAlgCl l).toRingHom) Subtype.val_injective).2 inferInstance
    have hC : Function.Injective (MvPowerSeries.C : c.O →+* MvPowerSeries (Fin m) c.O) := fun a b hab => by
      simpa using congrArg MvPowerSeries.constantCoeff hab
    exact (RingHom.charZero_iff (ϕ := (e.symm.toRingEquiv : MvPowerSeries (Fin m) c.O →+* Λ.Λ).comp MvPowerSeries.C)
      (e.symm.injective.comp hC)).1 inferInstance
  exact hU c.O Λ.Λ B.B _ (Λ.toPair B.u) J M h e₀ hId x {y : B.Pt | J ≤ RingHom.ker y ∧ y.Good w} b₀ hb₀ hdense hone
    (fun y hy hyb => (hmu x y w hJ hy.1 hA hy.2 hI (hopen y w hy.1 hy.2 hyb)).2)
    δ hδ hJδ hlam
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open UpperTheory.V.Z.Desc.V0
theorem UpperTheory.V.J.unramified_algebraic_weights : _root_.UpperTheory.V.J.UnramifiedEndsStatement := _root_.UpperTheory.V.Z.Desc.V0.unramified_at_of_dense_purity_num_e_power_series (unrAlgE unrAlgW muRange)
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.COpenEx
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af
namespace UpperTheory.V.J
open UpperTheory.V.Pr
theorem mod_l_open_existence
    {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {c : Coef l}
    [CharP (ResidueField c.O) l] {N : ℕ} [NeZero N] {e : ℕ} {ψ : DirichletCharacter c.O N}
    {η : G ℚ Ω →* ℤˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ} (H : LinkHyp c N e η σ B M)
    {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
    {k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ} (v : Φ.V)
    {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O} {n : ℕ}
    {ka : G L Ω →* (Qbar l)ˣ} (R : CReal k c₁ f n ka) (Λ : W.LamObj R.r)
    (hΛ : Nonempty (Λ.Λ ≃ₐ[c₁.O] MvPowerSeries (Fin (n * Module.finrank ℚ (W.Lp L))) c₁.O))
    (J : Ideal R.B₀.B) (hJ : R.B₀.ModularAlt ι J Λ) (hs : R.T.IdealSpecializationPoint J) : R.T.ModIn J := by
  obtain ⟨hd, -⟩ := degEq Ω l ι c N e ψ η σ g₁ B M H L Φ k v
  refine ⟨⟨Λ, hJ.ring.fin⟩, ?_, fun g hg => (hJ.ring.unr0 R.v0 g hg).1,
    n4Of Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f n ka R, hJ.p1, hJ.p3, hs⟩
  intro Z hZ
  haveI : IsDiscreteValuationRing c₁.O := c₁.dvr
  have := dimOf c₁.O Λ.Λ R.B₀.B (Λ.toPair R.B₀.u : Λ.Λ →+* R.B₀.B) J _ hΛ hJ.ring.fin hJ.ring.tf Z hZ
  rw [← hd] at this
  exact this
end UpperTheory.V.J
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.EndPtOf
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.BFixOf
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J
section Fx
open Matrix Ws.Eb
private def sn {K : Type} [CommRing K] {n : ℕ} (X : Matrix (Fin n) (Fin n) (DualNumber K)) :
    Matrix (Fin n) (Fin n) K := Matrix.of fun i j => (X i j).snd
private theorem sn_mul {K : Type} [CommRing K] {n : ℕ} (X Y : Matrix (Fin n) (Fin n) (DualNumber K)) :
    sn (X * Y) = X.map (dF K) * sn Y + sn X * Y.map (dF K) := by
  ext a b
  simp only [sn, Matrix.mul_apply, Matrix.of_apply, Matrix.add_apply, Matrix.map_apply, TrivSqZeroExt.snd_sum,
    DualNumber.snd_mul, Finset.sum_add_distrib]
  rfl
private theorem sn_one {K : Type} [CommRing K] {n : ℕ} : sn (1 : Matrix (Fin n) (Fin n) (DualNumber K)) = 0 := by
  ext i j
  by_cases h : i = j <;> simp [sn, Matrix.one_apply, h]
private theorem fx_alg {M : Type} [Ring M] (A0 Ai A1 B1 R Ri y : M) (h1 : A0 * Ai = 1) (h2 : Ai * A0 = 1)
    (h3 : R * Ri = 1) (h4 : A0 * B1 + A1 * Ai = 0) :
    A0 * (y - (R * (Ai * A1) * Ri - Ai * A1)) * Ai = (A0 * (R * B1 + (y * R) * Ai) + A1 * (R * Ai)) * (A0 * Ri * Ai) := by
  have hB : B1 = -(Ai * A1 * Ai) := by
    calc B1 = Ai * (A0 * B1) := by rw [← mul_assoc, h2, one_mul]
      _ = Ai * (-(A1 * Ai)) := by rw [eq_neg_of_add_eq_zero_left h4]
      _ = _ := by noncomm_ring
  subst hB
  have h1' : ∀ x, A0 * (Ai * x) = x := fun x => by rw [← mul_assoc, h1, one_mul]
  have h2' : ∀ x, Ai * (A0 * x) = x := fun x => by rw [← mul_assoc, h2, one_mul]
  have h3' : ∀ x, R * (Ri * x) = x := fun x => by rw [← mul_assoc, h3, one_mul]
  simp only [mul_add, add_mul, mul_sub, sub_mul, mul_neg, neg_mul, mul_assoc, h1', h2', h3', h1, h2, h3, mul_one]
  abel
private theorem tri_mul {K : Type} [CommRing K] {n : ℕ} (M N : Matrix (Fin n) (Fin n) K)
    (hM : ∀ i j, j < i → M i j = 0) (hN : ∀ i j, j < i → N i j = 0) :
    (∀ i j, j < i → (M * N) i j = 0) ∧ ∀ i, (M * N) i i = M i i * N i i := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hM i k h, zero_mul]
    · rw [hN k j (lt_of_lt_of_le hij h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hM i k h, zero_mul]
      · rw [hN k i h, mul_zero]
    · exact fun h => absurd (Finset.mem_univ i) h
private theorem fx_ord {H K : Type} [Group H] [Field K] {n : ℕ} (I : Subgroup H) (ρ : H →* GL (Fin n) K)
    (y : H → Matrix (Fin n) (Fin n) K) (ρ' : H →* GL (Fin n) (DualNumber K)) (ht : IsTan ρ y ρ')
    (ψ' : Fin n → H →* (DualNumber K)ˣ) (hfl : W.HasFlag ρ' ψ')
    (hI : ∀ g ∈ I, ∀ i, (ψ' i g : DualNumber K).snd = 0) :
    Th.OrdAt I ρ (fun i => W.pushCh (dF K) (ψ' i)) y := by
  obtain ⟨Gm, hG⟩ := hfl
  have hρ : ∀ g, ρ g = Matrix.GeneralLinearGroup.map (dF K) (ρ' g) := fun g =>
    Units.ext (Matrix.ext fun i j => (congrArg TrivSqZeroExt.fst (ht g i j)).symm)
  have hs : ∀ g, sn (ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) = y g * (ρ g : Matrix (Fin n) (Fin n) K) := fun g =>
    Matrix.ext fun i j => congrArg TrivSqZeroExt.snd (ht g i j)
  set a : GL (Fin n) K := Matrix.GeneralLinearGroup.map (dF K) Gm with ha
  have hai : ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((Gm⁻¹ : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K)).map (dF K) := by
    rw [ha, ← map_inv]; rfl
  have haa : (a : Matrix (Fin n) (Fin n) K) = (Gm : Matrix (Fin n) (Fin n) (DualNumber K)).map (dF K) := rfl
  set A1 := sn (Gm : Matrix (Fin n) (Fin n) (DualNumber K)) with hA1
  set B1 := sn ((Gm⁻¹ : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K)) with hB1
  have h4 : (a : Matrix (Fin n) (Fin n) K) * B1 + A1 * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 0 := by
    have := sn_mul (Gm : Matrix (Fin n) (Fin n) (DualNumber K)) ((Gm⁻¹ : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K))
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, sn_one] at this
    rw [hai, haa]
    exact this.symm
  let E : H → Matrix (Fin n) (Fin n) (DualNumber K) := fun g => ((Gm * ρ' g * Gm⁻¹ : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K))
  have hE0 : ∀ g, (((a * ρ g * a⁻¹ : GL (Fin n) K)) : Matrix (Fin n) (Fin n) K) = (E g).map (dF K) := fun g => by
    rw [hρ g, ha, ← map_inv, ← map_mul, ← map_mul]
    rfl
  have hEu : ∀ g i j, j < i → E g i j = 0 := fun g i j h => (hG g).1 i j h
  have hEd : ∀ g i, E g i i = (ψ' i g : DualNumber K) := fun g i => (hG g).2 i
  have hsE : ∀ g, sn (E g) = (a : Matrix (Fin n) (Fin n) K) * ((ρ g : Matrix (Fin n) (Fin n) K) * B1 + (y g * (ρ g : Matrix (Fin n) (Fin n) K)) * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) +
      A1 * ((ρ g : Matrix (Fin n) (Fin n) K) * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) := fun g => by
    have e : E g = (Gm : Matrix (Fin n) (Fin n) (DualNumber K)) * ((ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)) * ((Gm⁻¹ : GL (Fin n) (DualNumber K)) : Matrix (Fin n) (Fin n) (DualNumber K))) := by
      simp only [E, Units.val_mul, mul_assoc]
    have e2 : (ρ g : Matrix (Fin n) (Fin n) K) = (ρ' g : Matrix (Fin n) (Fin n) (DualNumber K)).map (dF K) := by
      rw [hρ g]; rfl
    rw [e, sn_mul, sn_mul, hs, Matrix.map_mul, ← e2, ← hai, ← haa]
  refine ⟨a, ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A1, fun g => ?_⟩
  have main : (a : Matrix (Fin n) (Fin n) K) * (y g - (Loc.adGL ρ g (((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A1) - ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * A1)) * ((a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      sn (E g) * ((a * ρ g⁻¹ * a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
    rw [hsE, map_inv]
    simp only [Units.val_mul]
    exact fx_alg _ _ _ _ _ _ _ (Units.mul_inv a) (Units.inv_mul a) (Units.mul_inv (ρ g)) h4
  have hN : ∀ i j, j < i → ((a * ρ g⁻¹ * a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0 := fun i j h => by
    rw [hE0, Matrix.map_apply, hEu _ i j h, map_zero]
  have hT := tri_mul (sn (E g)) _ (fun i j h => by simp [sn, hEu g i j h]) hN
  refine ⟨fun i j h => ?_, fun i => ?_, fun i j h => ?_, fun hg i => ?_⟩
  · change ((a * ρ g * a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i j = 0
    rw [hE0, Matrix.map_apply, hEu _ i j h, map_zero]
  · change ((a * ρ g * a⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) i i = _
    rw [hE0, Matrix.map_apply, hEd]
    rfl
  · rw [main]
    exact hT.1 i j h
  · rw [main, hT.2 i]
    have : sn (E g) i i = 0 := by
      simp only [sn, Matrix.of_apply, hEd]
      exact hI g hg i
    rw [this, zero_mul]
end Fx
section Tw
open Matrix Ws.Eb
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Fr.Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
include K in
private theorem fx_kk {A : Type} [CommRing A] [Algebra O A] (g : G.G₀) :
    ((K.κA A g : Aˣ) : A) * (K.κA A (G.conj g) : Aˣ) = ((G.eps O A g ^ (1 - (n : ℤ)) : Aˣ) : A) := by
  have h := congrArg (Units.map (algebraMap O A : O →* A)) (K.κ_conj g)
  rw [map_mul, map_zpow] at h
  exact congrArg Units.val h
private theorem fx_form {A : Type} [CommRing A] [Algebra O A] (ρ : Fr.NRep F n A) :
    G.IsForm O n (K.tw ρ).toHomUnits (Jgl (R := A) n) := fun g => by
  have h1 : (ρ.r (K.π g))ᵀ * Jmat A n * ρ.r (F.conj (K.π g)) = Jmat A n := by
    have e : ρ.r (F.star (K.π g)) * ρ.r (F.conj (K.π g)) = 1 := by
      rw [← map_mul, Fr.Frame.star, map_inv, inv_mul_cancel, map_one]
    rw [ρ.pol] at e
    calc _ = Jmat A n * (Jmat A n * (ρ.r (K.π g))ᵀ * Jmat A n * ρ.r (F.conj (K.π g))) := by
          simp only [← Matrix.mul_assoc, Jmat_mul_Jmat, Matrix.one_mul]
      _ = _ := by rw [e, Matrix.mul_one]
  change (((K.κA A g : Aˣ) : A) • ρ.r (K.π g))ᵀ * Jmat A n * (((K.κA A (G.conj g) : Aˣ) : A) • ρ.r (K.π (G.conj g))) = _ • Jmat A n
  rw [K.π_conj, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, h1, smul_smul,
    mul_comm ((K.κA A (G.conj g) : Aˣ) : A), fx_kk K g]
private theorem fx_ad {Q : Type} [Field Q] [Algebra O Q] (ρ : Fr.NRep F n Q) (g : G.G₀) (M : Matrix (Fin n) (Fin n) Q) :
    Loc.adGL (K.tw ρ).toHomUnits g M = ρ.r (K.π g) * M * ρ.r (K.π g)⁻¹ := by
  have e : (((K.tw ρ).toHomUnits g)⁻¹ : GL (Fin n) Q) = (K.tw ρ).toHomUnits g⁻¹ := (map_inv _ _).symm
  change ((K.tw ρ).toHomUnits g : Matrix (Fin n) (Fin n) Q) * M * (((K.tw ρ).toHomUnits g)⁻¹ : GL (Fin n) Q) = _
  rw [e]
  change (((K.κA Q g : Qˣ) : Q) • ρ.r (K.π g)) * M * (((K.κA Q g⁻¹ : Qˣ) : Q) • ρ.r (K.π g⁻¹)) = _
  rw [map_inv K.π, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_inv (K.κA Q), Units.mul_inv, one_smul]
variable {Q : Type} [Field Q] [Algebra O Q]
private noncomputable def fxY (ρD : Fr.NRep F n (DualNumber Q)) (g : G.G₀) : Matrix (Fin n) (Fin n) Q :=
  sn (ρD.r (K.π g)) * (ρD.map (dF Q)).r (K.π g)⁻¹
private theorem fx_rr (ρ : Fr.NRep F n Q) (h : F.G0) : ρ.r h⁻¹ * ρ.r h = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]
private theorem fx_rr' (ρ : Fr.NRep F n Q) (h : F.G0) : ρ.r h * ρ.r h⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]
private theorem fx_tan (ρD : Fr.NRep F n (DualNumber Q)) :
    IsTan (K.tw (ρD.map (dF Q))).toHomUnits (fxY K ρD) (K.tw ρD).toHomUnits := fun g i j => by
  have e : ((K.tw (ρD.map (dF Q))).toHomUnits g : Matrix (Fin n) (Fin n) Q) =
      ((K.κA Q g : Qˣ) : Q) • (ρD.map (dF Q)).r (K.π g) := rfl
  have e2 : fxY K ρD g * (ρD.map (dF Q)).r (K.π g) = sn (ρD.r (K.π g)) := by
    rw [fxY, Matrix.mul_assoc, fx_rr, Matrix.mul_one]
  rw [e, Matrix.mul_smul, e2]
  refine TrivSqZeroExt.ext rfl ?_
  change (((K.κA (DualNumber Q) g : (DualNumber Q)ˣ) : DualNumber Q) * ρD.r (K.π g) i j).snd = ((K.κA Q g : Qˣ) : Q) * (ρD.r (K.π g) i j).snd
  rw [DualNumber.snd_mul]
  have : (((K.κA (DualNumber Q) g : (DualNumber Q)ˣ) : DualNumber Q)).snd = 0 := rfl
  rw [this, zero_mul, add_zero]
  rfl
private theorem fx_coc (ρD : Fr.NRep F n (DualNumber Q)) (a b : G.G₀) :
    fxY K ρD (a * b) = fxY K ρD a + Loc.adGL (K.tw (ρD.map (dF Q))).toHomUnits a (fxY K ρD b) := by
  have hm : ∀ h, (ρD.r h).map (dF Q) = (ρD.map (dF Q)).r h := fun _ => rfl
  rw [fx_ad]
  simp only [fxY]
  rw [map_mul K.π, map_mul ρD.r, sn_mul, _root_.mul_inv_rev, map_mul (ρD.map (dF Q)).r, hm, hm, add_mul, add_comm]
  congr 1
  · rw [← Matrix.mul_assoc, Matrix.mul_assoc _ ((ρD.map (dF Q)).r (K.π b)), fx_rr', Matrix.mul_one]
  · simp only [Matrix.mul_assoc]
end Tw
section Core
open Matrix Ws.Eb
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Fr.Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
  {Q : Type} [Field Q] [Algebra O Q]
private theorem fx_psi (ρD : Fr.NRep F n (DualNumber Q)) (v : G.Vl) :
    K.twψ (ρD.map (dF Q)) v = fun i => W.pushCh (dF Q) (K.twψ ρD v i) :=
  funext fun i => MonoidHom.ext fun g => Units.ext (map_mul (dF Q) (ρD.ψ (K.e v) i (K.lam v g) : DualNumber Q)
    ((K.κA (DualNumber Q) (G.φ v g) : (DualNumber Q)ˣ) : DualNumber Q)).symm
private theorem fx_snd (ρD : Fr.NRep F n (DualNumber Q)) (v : G.Vl) (i : Fin n) (g : G.Gv v)
    (h : (ρD.ψ (K.e v) i (K.lam v g) : DualNumber Q).snd = 0) : (K.twψ ρD v i g : DualNumber Q).snd = 0 := by
  change ((ρD.ψ (K.e v) i (K.lam v g) : DualNumber Q) * ((K.κA (DualNumber Q) (G.φ v g) : (DualNumber Q)ˣ) : DualNumber Q)).snd = 0
  rw [DualNumber.snd_mul, h, zero_mul, add_zero]
  exact mul_zero _
private theorem fx_twflag {A : Type} [CommRing A] [Algebra O A] (ρ : Fr.NRep F n A) (v : G.Vl)
    (h : W.HasFlag (ρ.r.comp (F.loc0 (K.e v))).toHomUnits (ρ.ψ (K.e v))) :
    W.HasFlag ((K.tw ρ).toHomUnits.comp (G.φ v)) (K.twψ ρ v) := by
  obtain ⟨a, ha⟩ := h
  refine ⟨a, fun s => ?_⟩
  have key : ∀ i j, (a * ((K.tw ρ).toHomUnits.comp (G.φ v)) s * a⁻¹ : GL (Fin n) A) i j =
      ((K.κA A (G.φ v s) : Aˣ) : A) * (a * (ρ.r.comp (F.loc0 (K.e v))).toHomUnits (K.lam v s) * a⁻¹ : GL (Fin n) A) i j := fun i j => by
    change ((a : Matrix (Fin n) (Fin n) A) * (((K.κA A (G.φ v s) : Aˣ) : A) • ρ.r (K.π (G.φ v s))) *
      ((a⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) i j =
      _ * ((a : Matrix (Fin n) (Fin n) A) * ρ.r (F.loc0 (K.e v) (K.lam v s)) * ((a⁻¹ : GL (Fin n) A) : Matrix (Fin n) (Fin n) A)) i j
    rw [K.lam_loc, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [key, (ha _).1 i j hij, mul_zero]
  · rw [key, (ha _).2 i, mul_comm]
    rfl
variable [CharZero Q] [IsAlgClosed Q] [TopologicalSpace Q] [IsTopologicalRing Q]
private theorem fx_core (ρD : Fr.NRep F n (DualNumber Q))
    (hrc : ∀ i j, Continuous fun h => (ρD.r h i j).fst) (hsc : ∀ i j, Continuous fun h => (ρD.r h i j).snd)
    (hcont : Continuous (K.tw (ρD.map (dF Q))).toHomUnits)
    (hirr : MatIrr ⊤ (W.mat (K.tw (ρD.map (dF Q))).toHomUnits))
    (hine : ∀ u, ∀ g ∈ r.Ip u, K.tw ρD g = 1)
    (hfl : ∀ v, W.HasFlag (ρD.r.comp (F.loc0 v)).toHomUnits (ρD.ψ v))
    (hI : ∀ v i, ∀ g ∈ F.Iv v, (ρD.ψ v i g : DualNumber Q).snd = 0)
    (hZ : ∀ (P : GL (Fin n) Q) (R : Representation Q G.Γ (Matrix (Fin n) (Fin n) Q)),
      G.IsForm O n (K.tw (ρD.map (dF Q))).toHomUnits P → IsAdExt G (K.tw (ρD.map (dF Q))).toHomUnits P R →
      ∀ z ∈ Z1 R, Th.OrdCoc r (K.tw (ρD.map (dF Q))).toHomUnits (K.twψ (ρD.map (dF Q))) z → ∃ X, ∀ g, z g = R g X - X) :
    ∃ X : Matrix (Fin n) (Fin n) Q, ∀ h, sn (ρD.r h) = X * (ρD.map (dF Q)).r h - (ρD.map (dF Q)).r h * X := by
  have ht := fx_tan K ρD
  have hfull : Full (K.tw (ρD.map (dF Q))).toHomUnits :=
    (AlgebraTools.Det.irrIffSpan (W.mat (K.tw (ρD.map (dF Q))).toHomUnits)).1 fun N hN => hirr N fun g _ v hv => hN g v hv
  have c1 : Continuous fun g : G.G₀ => sn (ρD.r (K.π g)) :=
    continuous_matrix fun i j => (hsc i j).comp K.π_cont
  have c2 : Continuous fun g : G.G₀ => (ρD.map (dF Q)).r (K.π g)⁻¹ :=
    continuous_matrix fun i j => (hrc i j).comp (K.π_cont.inv)
  have hy : fxY K ρD ∈ Z1 (Loc.adGL (K.tw (ρD.map (dF Q))).toHomUnits) := ⟨c1.matrix_mul c2, fx_coc K ρD⟩
  obtain ⟨hP, hrel⟩ := cocRel G O _ (fxY K ρD) (K.tw ρD).toHomUnits (Jgl (R := DualNumber Q) n) ht (fx_form K ρD)
  obtain ⟨R, hR⟩ := adExt G O _ _ hfull hP
  obtain ⟨Z, hZ'⟩ := hrel R hR
  obtain ⟨z, hz, hzy⟩ := cocExt G _ _ R hfull hcont hR _ hy Z hZ'
  have hs : ∀ g : G.G₀, sn ((K.tw ρD).toHomUnits g : Matrix (Fin n) (Fin n) (DualNumber Q)) =
      fxY K ρD g * ((K.tw (ρD.map (dF Q))).toHomUnits g).val := fun g =>
    Matrix.ext fun i j => congrArg TrivSqZeroExt.snd (ht g i j)
  have hoc : Th.OrdCoc r (K.tw (ρD.map (dF Q))).toHomUnits (K.twψ (ρD.map (dF Q))) z := by
    refine ⟨fun u g hg => ?_, fun v => ?_⟩
    · rw [hzy]
      have e := hs g
      have e1 : ((K.tw ρD).toHomUnits g : Matrix (Fin n) (Fin n) (DualNumber Q)) = 1 := hine u g hg
      rw [e1, sn_one] at e
      have e3 := congrArg (· * (((K.tw (ρD.map (dF Q))).toHomUnits g)⁻¹ : GL (Fin n) Q).val) e
      simpa only [Matrix.zero_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one] using e3.symm
    · have h := fx_ord (G.Iv v) ((K.tw (ρD.map (dF Q))).toHomUnits.comp (G.φ v)) _ _ (ht.comp (G.φ v)) (K.twψ ρD v)
        (fx_twflag K ρD v (hfl _)) fun g hg i => fx_snd K ρD v i g (hI _ i _ ((K.lam_I v g).2 hg))
      rw [← fx_psi] at h
      simpa only [hzy] using h
  obtain ⟨X, hX⟩ := hZ _ R hP hR z hz hoc
  refine ⟨-X, fun h => ?_⟩
  obtain ⟨g, rfl⟩ := K.π_surj h
  have h1 : fxY K ρD g = (ρD.map (dF Q)).r (K.π g) * X * (ρD.map (dF Q)).r (K.π g)⁻¹ - X := by
    rw [← hzy, hX, hR.ad, fx_ad]
  have e2 : sn (ρD.r (K.π g)) = fxY K ρD g * (ρD.map (dF Q)).r (K.π g) := by
    rw [fxY, Matrix.mul_assoc, fx_rr, Matrix.mul_one]
  rw [e2, h1, Matrix.sub_mul, Matrix.mul_assoc _ _ ((ρD.map (dF Q)).r (K.π g)), fx_rr, Matrix.mul_one, Matrix.neg_mul, Matrix.mul_neg]
  abel
end Core
section Sp
open Matrix Ws.Eb
private noncomputable def fxD {O A Q : Type} [CommRing O] [CommRing A] [Algebra O A] [Field Q] [Algebra O Q]
    (ξ : A →ₐ[O] Q) (D : A →ₗ[O] Q) (hD : D ∈ PtDer ξ Q) : A →ₐ[O] DualNumber Q :=
  have h1 : D 1 = 0 := by
    have h := hD 1 1
    rw [mul_one, map_one ξ, one_smul] at h
    exact left_eq_add.1 h
  { toFun := fun a => ⟨ξ a, D a⟩
    map_one' := TrivSqZeroExt.ext (map_one ξ) h1
    map_mul' := fun a b => TrivSqZeroExt.ext (map_mul ξ a b) (by
      refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
      change D (a * b) = ξ a * D b + D a * ξ b
      rw [mul_comm (D a)]
      exact hD a b)
    map_zero' := TrivSqZeroExt.ext (map_zero ξ) (map_zero D)
    map_add' := fun a b => TrivSqZeroExt.ext (map_add ξ a b) (map_add D a b)
    commutes' := fun a => TrivSqZeroExt.ext (ξ.commutes a) (by
      change D (algebraMap O A a) = 0
      rw [Algebra.algebraMap_eq_smul_one, map_smul, h1, smul_zero]) }
variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
  {F : Fr.Frame l (ResidueField O)} {n : ℕ} {G : W.GFrame l} {r : W.Resid G O n} (K : TwLink F r)
private theorem fx_ine [CharP (ResidueField O) l] {A : Type} [CommRing A] [Algebra O A] [IsCO O A] {ρ : Fr.NRep F n A}
    (h : Fr.IsLift O ρ) (u : G.St) (g : G.G₀) (hg : g ∈ r.Ip u) : K.tw ρ g = 1 := by
  obtain ⟨m, hm, h1, h2⟩ := K.tame u g hg.1
  have hχ : ∀ i, r.chib i g = 1 := fun i => (Subgroup.mem_iInf.1 hg.2) i
  have h3 : ∀ i j, res O A (K.tw ρ g i j - (1 : Matrix (Fin n) (Fin n) A) i j) = 0 := fun i j => by
    have e : K.tw ρ g i j = algebraMap O A (K.κ g) * ρ.r (K.π g) i j := rfl
    rw [map_sub, e, map_mul, AlgHom.commutes]
    by_cases hij : i = j
    · subst hij
      have e1 := congrArg Units.val ((K.chib i g).symm.trans (hχ i))
      have e2 : res O A (ρ.r (K.π g) i i) = ((F.Ψ (K.π g) ^ Fr.w n i : (ResidueField O)ˣ) : ResidueField O) :=
        h.2.1.1 (K.π g) i
      rw [e2, Matrix.one_apply_eq, map_one, mul_comm, sub_eq_zero]
      exact e1
    · have e2 : res O A (ρ.r (K.π g) i j) = 0 := h.2.2 (K.π g) i j hij
      rw [e2, Matrix.one_apply_ne hij, map_zero, mul_zero, sub_zero]
  have h4 : (K.tw ρ g).map (residue A) = 1 := by
    ext i j
    have h5 := h3 i j
    rw [res_eq_zero_iff, ← residue_eq_zero_iff, map_sub, sub_eq_zero] at h5
    refine h5.trans ?_
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  refine Pr.T.unipTorsion (A := A) (K.tw ρ g) (K.tw ρ g).charpoly n m (Matrix.charpoly_monic _)
    (Matrix.aeval_self_charpoly _) ?_ ?_ ?_
  · rw [← Matrix.charpoly_map, h4, Matrix.charpoly_one, Fintype.card_fin]
  · by_contra hn
    have h5 := (res_eq_zero_iff O A _).2 hn
    rw [map_natCast, CharP.cast_eq_zero_iff _ l] at h5
    exact hm h5
  · rw [← map_pow]
    have e : K.κA A (g ^ m) = 1 := by
      change Units.map _ (K.κ (g ^ m)) = 1
      rw [map_pow, h2, map_one]
    change ((K.κA A (g ^ m) : Aˣ) : A) • ρ.r (K.π (g ^ m)) = 1
    rw [e, map_pow K.π, h1, map_one, Units.val_one, one_smul]
private theorem fx_ineS [CharP (ResidueField O) l] {C : Type} [CommRing C] [Algebra O C] (S : Fr.Space O F n)
    (φ : S.A →ₐ[O] C) (u : G.St) (g : G.G₀) (hg : g ∈ r.Ip u) : K.tw (S.u.map (φ : S.A →+* C)) g = 1 := by
  have h := fx_ine K S.lift u g hg
  ext i j
  have h2 : ((algebraMap O S.A (K.κ g) * S.u.r (K.π g) i j : S.A) : S.R) = (1 : Matrix (Fin n) (Fin n) S.R) i j :=
    congrFun (congrFun h i) j
  have h1 : algebraMap O S.A (K.κ g) * S.u.r (K.π g) i j = (1 : Matrix (Fin n) (Fin n) S.A) i j := Subtype.ext (by
    rw [h2]
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij])
  change algebraMap O C (K.κ g) * φ (S.u.r (K.π g) i j) = _
  rw [← φ.commutes, ← map_mul, h1]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
end Sp
theorem UpperTheory.V.J.fixOf_alt :
    _root_.UpperTheory.V.Th.DenseThresholdMainCase → ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
        [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
        (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
        ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
        (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
        (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
        (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
        ∀ (ξ : R.S.A →ₐ[c₁.O] Qbar l) (x : R.B₀.Pt), IntPt R.S ξ → _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x (R.K.tw (ptRep R.S ξ)).toHomUnits →
          (∀ v, x.psi v = R.K.twψ (ptRep R.S ξ) v) → ∀ D ∈ FixTan R.S ξ,
          ∃ X : Matrix (Fin 3) (Fin 3) (Qbar l), ∀ g, (R.S.u.r g).map D = X * (ptRep R.S ξ).r g - (ptRep R.S ξ).r g * X := by
  intro hC Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f ka R hL hka ξ x hξ hN hψ D hD
  have hV : Nonempty Φ.V := by
    by_contra hV
    rw [not_nonempty_iff] at hV
    have h : _ < Φ.d := R.big.1
    simp [Fr.Frame.d] at h
  obtain ⟨v'⟩ := hV
  have hroot := (degEq Ω l ι c N e ψ η σ g₁ B M H L Φ k v').2
  obtain ⟨hrc, hsc, -⟩ := derRep l c₁ (Φ.ext f) R.C₀ 3 R.ok (Or.inr rfl) R.S ξ hξ D hD.1
  have hZ : Th.OrdZero R.r (R.K.tw (ptRep R.S ξ)).toHomUnits (R.K.twψ (ptRep R.S ξ)) := by
    have e : R.K.twψ (ptRep R.S ξ) = fun v => x.psi v := funext fun v => (hψ v).symm
    rw [e]
    exact hC l L Ω R.s R.V R.hV hroot c₁ hL 3 (by omega) (by omega) R.r R.v0 R.B₀ ι x _ hN
  exact fx_core R.K (R.S.u.map (fxD ξ D hD.1 : R.S.A →+* DualNumber (Qbar l))) hrc hsc hN.cont
    (fun U hU => hN.irr U fun g _ v hv => hU g trivial v hv) (fun u g hg => fx_ineS R.K R.S _ u g hg)
    (fun v => Fr.flag R.ok (Or.inr rfl) R.S _ _ v) (fun v i g hg => hD.2 v i g hg) hZ
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Pr UpperTheory.V.Alg UpperTheory.V.J UpperTheory.V.Th
namespace UpperTheory.Gal.projectedFormsSystemPart
private theorem la_move {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
    {A A' : ValuationSubring Ω} {w w' : W.Plc F} (h : IsPlaceOver A w) (h' : IsPlaceOver A' w') (e : A = A')
    (ψ : Fin n → Dec (F := F) A →* (Qbar l)ˣ) (ψ' : Fin n → Dec (F := F) A' →* (Qbar l)ˣ)
    (hψ : ∀ j (g : Dec (F := F) A) (g' : Dec (F := F) A'), (g : G F Ω) = (g' : G F Ω) → ψ j g = ψ' j g') (wt : Fin n → W.Emb l w → ℤ)
    (hm : ∀ τ, StrictMono fun j => wt j τ) (hl : ∀ j, W.IsLocAlg h (ψ j) (wt j)) :
    ∃ wt' : Fin n → W.Emb l w' → ℤ, (∀ τ, StrictMono fun j => wt' j τ) ∧ ∀ j, W.IsLocAlg h' (ψ' j) (wt' j) := by
  subst e
  obtain rfl : w = w' := IsDedekindDomain.HeightOneSpectrum.ext (Ideal.ext fun x => (h x).symm.trans (h' x))
  obtain rfl : ψ = ψ' := funext fun j => MonoidHom.ext fun g => hψ j g g rfl
  exact ⟨wt, hm, hl⟩
section
variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}
  {η : G ℚ Ω →* ℤˣ} {Ψ : G ℚ Ω →* c.Oˣ} {σ g₁ : G ℚ Ω} {B : ValuationSubring Ω} {M : ℕ}
  {L : Type} [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] {Φ : Fr.Frame l (ResidueField c.O)}
  {k : GalLink η Ψ σ g₁ B M L Φ} {c₁ : Coef l} [Fr.IsCoef l c₁.O] {f : ResidueField c.O →+* ResidueField c₁.O}
  {ka : G L Ω →* (Qbar l)ˣ}
def EndPtAlt (R : CReal k c₁ f 3 ka) (ι : Qbar l ≃+* ℂ) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) : Prop :=
  ∀ (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l), VPt R.S ξ → R.S.u.TI (RingHom.ker ξ) →
    ∀ x : R.B₀.Pt, x = (ξ.comp R.S.inc).comp φ → x.Arith h → _root_.UpperTheory.V.Z.Win.IsAutCsdA ι ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr)
private theorem psi_eq (R : CReal k c₁ f 3 ka) {φ : R.B₀.B →ₐ[c₁.O] R.S.B} (hφ : R.T.IsPhi φ) (ξ : R.S.A →ₐ[c₁.O] Qbar l) (v) :
    W.UniversalOrdinaryDeterminantRing.Pt.psi (B := R.B₀) ((ξ.comp R.S.inc).comp φ) v = R.K.twψ (ptRep R.S ξ) v :=
  funext fun i => (TwLink.IsPhi.maps R.K hφ ξ).2 v i
private theorem off_self (R : CReal k c₁ f 3 ka) {ι : Qbar l ≃+* ℂ} {φ : R.B₀.B →ₐ[c₁.O] R.S.B} (hφ : R.T.IsPhi φ)
    {J : Ideal R.B₀.B} (hg : AllGood R.S (J.map φ)) (hE : R.B₀.arithmeticPointClassicalityDense ι J) (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l)
    (hV : VPt R.S ξ) (hTI : R.S.u.TI (RingHom.ker ξ)) (ha : W.UniversalOrdinaryDeterminantRing.Pt.Arith (B := R.B₀) ((ξ.comp R.S.inc).comp φ) h) :
    _root_.UpperTheory.Gal.projectedFormsSystemPart.AutOffN R.s.v0 ι ((R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr) := by
  let ρ := R.K.tw (ptRep R.S ξ)
  let p : G L Ω →* R.V.frame.G₀ := R.V.pr
  have hD : W.UniversalOrdinaryDeterminantRing.Pt.D (B := R.B₀) ((ξ.comp R.S.inc).comp φ) = W.GDet.ofRep ρ :=
    (TwLink.IsPhi.maps R.K hφ ξ).1
  have hrep : W.UniversalOrdinaryDeterminantRing.Pt.IsRep (B := R.B₀) ((ξ.comp R.S.inc).comp φ) (ρ.toHomUnits.comp p) := by
    refine (congrArg (fun D : W.GDet 3 (Qbar l) R.V.frame.G₀ => D.comap p) hD).trans ?_
    change (W.GDet.ofRep ρ).comap p = W.GDet.ofRep (ρ.comp p)
    refine W.GDet.ext fun C _ _ y => ?_
    change (W.GDet.repAlg ρ C (MonoidAlgebra.mapDomainRingHom C p y)).det =
      (W.GDet.repAlg (ρ.comp p) C y).det
    congr 1
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp [W.GDet.repAlg]
  have hirr : Af.IsIrr (ρ.toHomUnits.comp p) := by
    have hMat := R.K.tw_irr _ (irrTI l c₁ _ R.C₀ 3 R.ok (Or.inr rfl) R.S ξ hV.1 hTI)
    refine ⟨top_ne_bot, fun _ _ _ => Submodule.mem_top, fun U _ hU => hMat U fun g _ v hv => ?_⟩
    obtain ⟨t, rfl⟩ := Pr.pr_surj R.V g
    exact hU t v hv
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.end2oN R.v0 hE ((ξ.comp R.S.inc).comp φ) h _
    (fun b hb => hg _ (RingHom.ker_isPrime _) hTI (Ideal.mem_map_of_mem φ hb)) ha hrep hirr
private theorem kap (R : CReal k c₁ f 3 ka) (g : G L Ω) : R.K.κA (Qbar l) (R.V.pr g) = ka g := Units.ext (R.κ_pr g)
private theorem psi_j (ρ : Fr.NRep (Φ.ext f) 3 (Qbar l)) {u u' : Φ.V} (e : u = u') (j : Fin 3) (a : Φ.Gv u) (a' : Φ.Gv u')
    (h : (k.j u a).1 = (k.j u' a').1) : ρ.ψ u j a = ρ.ψ u' j a' := by
  subst e
  rw [k.j_inj u (Subtype.ext h)]
theorem endPt_of_allGood_of_arithmeticPointClassicality (R R₀ : CReal k c₁ f 3 ka) (hp : ¬ R₀.s.p ∣ R.s.p) {ι : Qbar l ≃+* ℂ} {φ : R.B₀.B →ₐ[c₁.O] R.S.B}
    (hφ : R.T.IsPhi φ) {J : Ideal R.B₀.B} (hg : AllGood R.S (J.map φ)) (hE : R.B₀.arithmeticPointClassicalityDense ι J)
    {φ' : R₀.B₀.B →ₐ[c₁.O] R.S.B} (hφ' : (setS R₀ R.S).T.IsPhi φ') {J' : Ideal R₀.B₀.B} (hg' : AllGood R.S (J'.map φ'))
    (hE' : R₀.B₀.arithmeticPointClassicalityDense ι J') : _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ := by
  rintro h ξ hV hTI _ rfl ha
  have key : ∀ v' : W.Vl l L, ∃ wt' : Fin 3 → W.Emb l (R₀.s.w v') → ℤ, (∀ τ, StrictMono fun j => wt' j τ) ∧
      ∀ j, W.IsLocAlg (R₀.s.hw v') (W.UniversalOrdinaryDeterminantRing.Pt.psi (B := R₀.B₀) ((ξ.comp R.S.inc).comp φ') v' j) (wt' j) := fun v' => by
    obtain ⟨v, hv⟩ : ∃ v : W.Vl l L, R.K.e v = R₀.K.e v' := R.K.e.surjective (R₀.K.e v')
    refine la_move (R.s.hw v) (R₀.s.hw v') ((R.A_pl v).trans ((congrArg k.pl hv).trans (R₀.A_pl v').symm)) _ _
      (fun j g g' e => ?_) (h v) (ha.1 v) (ha.2 v)
    rw [psi_eq R hφ ξ v, psi_eq (setS R₀ R.S) hφ' ξ v']
    change (ptRep R.S ξ).ψ (R.K.e v) j (R.K.lam v g) * R.K.κA (Qbar l) (R.V.pr g) =
      (ptRep R.S ξ).ψ (R₀.K.e v') j (R₀.K.lam v' g') * R₀.K.κA (Qbar l) (R₀.V.pr g')
    rw [kap, kap, e]
    exact congrArg (· * ka g') (psi_j (k := k) (ptRep R.S ξ) hv j (R.K.lam v g) (R₀.K.lam v' g')
      ((R.lam_j v g).trans ((congrArg (galEmb ℚ L Ω) e).trans (R₀.lam_j v' g').symm)))
  choose wt' h1 h2 using key
  have a := off_self R hφ hg hE h ξ hV hTI ha
  have b := off_self (setS R₀ R.S) hφ' hg' hE' wt' ξ hV hTI ⟨h1, h2⟩
  have e : ((setS R₀ R.S).K.tw (ptRep R.S ξ)).toHomUnits.comp (setS R₀ R.S).V.pr =
      (R.K.tw (ptRep R.S ξ)).toHomUnits.comp R.V.pr := MonoidHom.ext fun g => Units.ext (by
    change ((R₀.K.κA (Qbar l) (R₀.V.pr g) : (Qbar l)ˣ) : Qbar l) • (ptRep R.S ξ).r (R₀.K.π (R₀.V.pr g)) =
      ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) • (ptRep R.S ξ).r (R.K.π (R.V.pr g))
    rw [kap, kap, R.π_pr, R₀.π_pr])
  exact _root_.UpperTheory.Gal.projectedFormsSystemPart.glueN (by norm_num) (v0_ne hp) a (e ▸ b)
end
theorem niceAt2_alt :
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∀ φ, R.T.IsPhi φ → _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ → ∀ (h : R.s.Wt 3) (ξ : R.S.A →ₐ[c₁.O] Qbar l), VPt R.S ξ →
      R.S.u.TI (RingHom.ker ξ) → ∀ x : R.B₀.Pt, x = (ξ.comp R.S.inc).comp φ → x.Good h →
      (Th.Free R.V.frame fun v => x.psi v) →
      _root_.UpperTheory.V.Th.AutomorphicPointLocallyGeneric ι x (R.K.tw (ptRep R.S ξ)).toHomUnits ∧ ∀ v, x.psi v = R.K.twψ (ptRep R.S ξ) v := by
  intro Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H L _ _ _ _ _ Φ k c₁ _ f ka R _ _ φ hφ hJ h ξ hV hTI x hx hGood hFree
  have hn : (3 : ℕ) = 2 ∨ (3 : ℕ) = 3 := Or.inr rfl
  let ρQ : Fr.NRep (Φ.ext f) 3 (Qbar l) := ptRep R.S ξ
  let ρ0 : R.V.frame.G₀ →* GL (Fin 3) (Qbar l) := (R.K.tw ρQ).toHomUnits
  have hm : R.B₀.u.Maps ((ξ.comp (R.S.inc.comp φ) : R.B₀.B →ₐ[c₁.O] Qbar l) : R.B₀.B →+* Qbar l)
      (W.GDet.ofRep (R.K.tw ρQ)) (R.K.twψ ρQ) := TwLink.IsPhi.maps R.K hφ ξ
  have hxe : x = ξ.comp (R.S.inc.comp φ) := hx
  have hψ : ∀ v, x.psi v = R.K.twψ ρQ v := fun v => funext fun i => by
    rw [hxe]
    exact hm.2 v i
  have hD : W.UniversalOrdinaryDeterminantRing.Pt.D x = W.GDet.ofRep (R.K.tw ρQ) := by
    rw [hxe]
    exact hm.1
  have hcont : Continuous ρ0 := by
    have h1 : Continuous (R.K.tw ρQ) := by
      refine continuous_matrix fun a b => ?_
      have h2 := continuous_subtype_val.comp (((X.So.adicCont l c₁).2 _ _).1 R.K.κ_cont)
      have h3 := ((derRep l c₁ _ R.C₀ 3 R.ok hn R.S ξ hV.1 0 (Submodule.zero_mem _)).1 a b).comp R.K.π_cont
      exact h2.mul h3
    exact Units.continuous_iff.2 ⟨h1, h1.comp continuous_inv⟩
  have hirr : MatIrr ⊤ (W.mat ρ0) := R.K.tw_irr ρQ (irrTI l c₁ _ R.C₀ 3 R.ok hn R.S ξ hV.1 hTI)
  have hrep : W.UniversalOrdinaryDeterminantRing.Pt.IsRep x (ρ0.comp R.V.pr) := by
    let ρ := R.K.tw ρQ
    let p : G L Ω →* R.V.frame.G₀ := R.V.pr
    refine (congrArg (fun D => D.comap p) hD).trans ?_
    change (W.GDet.ofRep ρ).comap p = W.GDet.ofRep (ρ.comp p)
    refine W.GDet.ext fun C _ _ y => ?_
    change (W.GDet.repAlg ρ C (MonoidAlgebra.mapDomainRingHom C p y)).det =
      (W.GDet.repAlg (ρ.comp p) C y).det
    congr 1
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp only [map_add (f := _), ha, hb]
    | single g r => simp [W.GDet.repAlg]
  have harith : W.UniversalOrdinaryDeterminantRing.Pt.Arith x h := ⟨hGood.1, fun v j => by
    obtain ⟨ph, hph, -⟩ := hGood.2 v
    exact ⟨ph j, hph j⟩⟩
  have hA : _root_.UpperTheory.V.Th.AutomorphicPointGalois ι x ρ0 := by
    refine ⟨hcont, hrep, ⟨h, harith⟩, hJ h ξ hV hTI x hx harith, ?_, fun v => ?_⟩
    · rintro _ ⟨g, hg, rfl⟩
      have h1 : R.K.π (R.V.pr g) = 1 := by
        rw [R.π_pr]
        let A := R.s.A R.s.v0
        have valuation_lt_of_dvd {a b : ℕ} (hab : a ∣ b)
            (ha : A.valuation (a : Ω) < 1) : A.valuation (b : Ω) < 1 := by
          obtain ⟨d, rfl⟩ := hab
          rw [Nat.cast_mul, map_mul]
          exact mul_lt_one_of_lt_of_le ha ((A.valuation_le_one_iff _).2 (natCast_mem A d))
        have hl : ¬ A.valuation (l : Ω) < 1 :=
          fun h' => R.v0M (valuation_lt_of_dvd ((dvd_mul_right l N).trans H.dvd) h')
        have hg' : galEmb ℚ L Ω g ∈ Ine (F := ℚ) A := hg
        have hc : cycZ ℚ Ω l (galEmb ℚ L Ω g) = 1 := (Base.places ℚ Ω l A).2.2.2 hl hg'
        have hd : Chr.cls ℚ Ω N (galEmb ℚ L Ω g) = 1 :=
          (Chr.clsFacts ℚ Ω N).2.2.2.2 A
            (fun h' => R.v0M (valuation_lt_of_dvd ((dvd_mul_left N l).trans H.dvd) h')) hg'
        have hψg : Chr.Psi l e (Chr.dirG ℚ Ω ψ) (galEmb ℚ L Ω g) = 1 := by
          simp [Chr.Psi, Chr.dirG, chiO, hc, hd]
        refine Subtype.ext ?_
        change toUpl Ω L (W.resP L Ω g) ∈ k.p.ker
        rw [k.p_ker]
        refine Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨A, hl, hg', ?_, ?_⟩)
        · exact (k.mem_range_resP _).1 ⟨_, rfl⟩
        · exact (congrArg (Units.map (residue c.O).toMonoidHom) hψg).trans (map_one _)
      have h2 : R.K.κ (R.V.pr g) = 1 := R.K.ramκ _ ⟨g, hg, rfl⟩
      refine Units.ext ?_
      change ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) • ρQ.r (R.K.π (R.V.pr g)) = 1
      have h3 : ((R.K.κA (Qbar l) (R.V.pr g) : (Qbar l)ˣ) : Qbar l) = 1 := by
        change algebraMap c₁.O (Qbar l) ((R.K.κ (R.V.pr g) : (↥c₁.O)ˣ) : c₁.O) = 1
        rw [h2, Units.val_one, map_one]
      rw [h1, map_one, h3, one_smul]
    · rw [hψ v]
      obtain ⟨P, hP⟩ := Fr.flag R.ok hn R.S (Qbar l) (ξ : R.S.A →+* Qbar l) (R.K.e v)
      refine ⟨P, fun s => ?_⟩
      have entry (i j : Fin 3) : (P * (ρ0.comp (R.V.frame.φ v)) s * P⁻¹ : GL (Fin 3) (Qbar l)) i j =
          (R.K.κA (Qbar l) (R.V.frame.φ v s) : Qbar l) *
            (P * (ρQ.r.comp ((Φ.ext f).loc0 (R.K.e v))).toHomUnits (R.K.lam v s) * P⁻¹ : GL (Fin 3) (Qbar l)) i j := by
        change ((P : Matrix (Fin 3) (Fin 3) (Qbar l)) *
          ((R.K.κA (Qbar l) (R.V.frame.φ v s) : Qbar l) • ρQ.r (R.K.π (R.V.frame.φ v s))) *
          ((P⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l))) i j =
          _ * ((P : Matrix (Fin 3) (Fin 3) (Qbar l)) * ρQ.r ((Φ.ext f).loc0 (R.K.e v) (R.K.lam v s)) *
            ((P⁻¹ : GL (Fin 3) (Qbar l)) : Matrix (Fin 3) (Fin 3) (Qbar l))) i j
        rw [R.K.lam_loc, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]
      refine ⟨fun i j hij => ?_, fun i => ?_⟩
      · rw [entry, (hP _).1 i j hij, mul_zero]
      · rw [entry, (hP _).2 i, mul_comm]
        rfl
  have hVne : Nonempty Φ.V := by
    by_contra hV'
    rw [not_nonempty_iff] at hV'
    have h' : _ < Φ.d := R.big.1
    simp [Fr.Frame.d] at h'
  obtain ⟨v'⟩ := hVne
  refine ⟨_root_.UpperTheory.V.Th.nice_zero_of_rank_two_or_three_irreducible_free ι x ρ0 hn hA hirr hFree ?_, hψ⟩
  obtain ⟨v, hv⟩ := R.K.e.surjective v'
  obtain ⟨s, hs⟩ := R.ok.f3 (R.K.e v)
  obtain ⟨g, rfl⟩ := (R.K.lam v).surjective s
  refine ⟨v, 0, 1, g, fun h' => ?_⟩
  rw [R.K.psib, R.K.psib, R.K.chib, R.K.chib, ← R.K.lam_loc] at h'
  have hw : (Φ.ext f).Ψ ((Φ.ext f).loc (R.K.e v) (R.K.lam v g)) ^ Fr.w 3 0 =
      (Φ.ext f).Ψ ((Φ.ext f).loc (R.K.e v) (R.K.lam v g)) ^ Fr.w 3 1 := mul_right_cancel h'
  have hζ : (Φ.ext f).Ψ ((Φ.ext f).loc (R.K.e v) (R.K.lam v g)) = 1 := by
    simpa [show Fr.w 3 0 = 1 by decide, show Fr.w 3 1 = 0 by decide] using hw
  exact hs (by rw [hζ, one_pow])
def Red2Alt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O))
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ)
    (c₁ : Coef l) [Fr.IsCoef l c₁.O] (f : ResidueField c.O →+* ResidueField c₁.O)
    (ka : G L Ω →* (Qbar l)ˣ) (R : CReal k c₁ f 3 ka), W.Large L c₁ → IsKa σ M ι 3 ka →
    ∀ φ, R.T.IsPhi φ → Function.Surjective φ → ∀ J, AllGood R.S (J.map φ) → R.T.DimT J → R.B₀.Dense J →
      _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ → ∀ ξ : R.S.A →ₐ[c₁.O] Qbar l, IntPt R.S ξ → R.S.u.TI (RingHom.ker ξ) →
      ∀ a ∈ J, ∃ s : R.S.A, ξ s ≠ 0 ∧ s * R.S.inc (φ a) = 0
theorem red2_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → _root_.UpperTheory.V.Th.DenseThresholdMainCase → _root_.UpperTheory.Gal.projectedFormsSystemPart.Red2Alt := by
  intro hG hC Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M hL L _ _ _ _ _ Φ k c₁ _ f ka R hW hK φ hPhi hSurj J hAll hDim hDense hEnd ξ hξ hTI a ha
  obtain ⟨h, hInc, hFree⟩ := wtEx hG Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK
  have hNice := _root_.UpperTheory.Gal.projectedFormsSystemPart.niceAt2_alt Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK φ hPhi hEnd h
  have hFix := _root_.UpperTheory.V.J.fixOf_alt hC Ω l ι c N e ψ η σ g₁ B M hL L Φ k c₁ f ka R hW hK
  have hN : IsNoetherianRing R.B₀.B := IsCO.toIsNoetherian (O := c₁.O)
  have hD : DenseB R.S (J.map φ) (fun y => W.UniversalOrdinaryDeterminantRing.Pt.Good (y.comp φ) h) :=
    @denseOf l _ c₁ R.B₀.B R.S.B _ hN _ _ _ φ J (1 + 3 * (Φ.ext f).d) (fun x => W.UniversalOrdinaryDeterminantRing.Pt.Good x h) hSurj hDim (hDense h hInc)
  refine redAbs l c₁ (Φ.ext f) R.C₀ 3 R.ok (Or.inr rfl) R.S (J.map φ) (fun y => W.UniversalOrdinaryDeterminantRing.Pt.Good (y.comp φ) h) hAll hD ?_ ξ hξ hTI (φ a) (Ideal.mem_map_of_mem _ ha)
  intro ζ hV hT _ hGd
  obtain ⟨h1, h2⟩ := hNice ζ hV hT _ rfl hGd (hFree _ hGd)
  exact fixLe l c₁ (Φ.ext f) R.C₀ 3 R.ok (Or.inr rfl) R.S ζ hV.1 hT (hFix ζ _ hV.1 h1 h2)
end UpperTheory.Gal.projectedFormsSystemPart
end
end

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDomain UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp IsLocalRing UpperTheory.V UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Base UpperTheory.V.Af UpperTheory.V.Alg
open UpperTheory.V.W UpperTheory.V.Pr UpperTheory.V.J
namespace UpperTheory.Gal.projectedFormsSystemPart
def OpenEx2EAlt : Prop :=
  ∀ (Ω : Type) [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (c : Coef l)
    [CharP (ResidueField c.O) l] (N : ℕ) [NeZero N] (e : ℕ) (ψ : DirichletCharacter c.O N)
    (η : G ℚ Ω →* ℤˣ) (σ g₁ : G ℚ Ω) (B : ValuationSubring Ω) (M : ℕ), LinkHyp c N e η σ B M → Even N →
    ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] [Algebra L Ω] [IsAlgClosure L Ω] (Φ : Fr.Frame l (ResidueField c.O)) (C₀ : ℕ)
    (k : GalLink η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ g₁ B M L Φ), Φ.Ok C₀ → Φ.Big C₀ → SeedClause c η (Chr.Psi l e (Chr.dirG ℚ Ω ψ)) σ L →
    ∀ (A : Subalgebra c.O (PadicAlgCl l)) [Module.Finite c.O A],
    ∃ (c₁ : Coef l) (_ : Fr.IsCoef l c₁.O) (f : ResidueField c.O →+* ResidueField c₁.O) (R : CReal k c₁ f 3 (cycBar L Ω l)⁻¹)
      (Λ : LamObj R.r) (J : Ideal R.B₀.B) (φ : R.B₀.B →ₐ[c₁.O] R.S.B) (m : ℕ),
      (∀ x ∈ A, x ∈ c₁.O) ∧ Large L c₁ ∧ IsKa σ M ι 3 (cycBar L Ω l)⁻¹ ∧ R.B₀.ModularAlt ι J Λ ∧ Num R.B₀ Λ J ∧
      Nonempty (Λ.Λ ≃ₐ[c₁.O] MvPowerSeries (Fin m) c₁.O) ∧ R.T.IsPhi φ ∧ Function.Surjective φ ∧ AllGood R.S (J.map φ) ∧
      R.T.DimT J ∧ _root_.UpperTheory.Gal.projectedFormsSystemPart.EndPtAlt R ι φ
theorem UnitaryRankTwoFlagsAlt (hO : _root_.UpperTheory.Gal.projectedFormsSystemPart.OpenEx2EAlt) (hX : XiEx) (hT : XiTI) (hA : XiArith) (hTan : TanA) (hR : _root_.UpperTheory.Gal.projectedFormsSystemPart.Red2Alt) (hU : _root_.UpperTheory.V.J.UnramifiedEndsStatement) (hE : End)
    (hι : ∀ (l : ℕ) [Fact l.Prime], Nonempty (Qbar l ≃+* ℂ)) : UpperTheory.V.Z.J.LinkedUnlE := by
  intro Ω _ _ _ l _ c _ N _ e ψ η σ g₁ B M H hev L _ _ _ _ _ Φ C₀ k hok hbig hseed A _ _ _ ρ hρ hψ r hr hirr v hpc i j
  by_contra hno
  push Not at hno
  obtain ⟨ι⟩ := hι l
  obtain ⟨c₁, _, f, R, Λ, J, φ, m, hAc, hL, hka, hmod, hnum, hΛ, hφ, hsurj, hgood, hdim, hend⟩ :=
    hO Ω l ι c N e ψ η σ g₁ B M H hev L Φ C₀ k hok hbig hseed A
  obtain ⟨ξ, h1, h2⟩ := hX Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R A hAc ρ hρ
  have hr' : ∀ s, (r s).val = (R.S.ρ.r (k.p0 s)).map fun a => (ξ a).1 := fun s => by
    rw [hr s]; ext a b; exact (h1 _ a b).symm
  have hi : IsIrr r := by
    have := hirr ⊤ (by simp)
    exact ⟨this.1, fun s w hw => Submodule.mem_top, fun U hU h => this.2.2 U hU fun s w hw => h s.1 w hw⟩
  have hψ' : ∀ v i, ∀ g ∈ Φ.Iv v, (ξ (R.S.ρ.ψ v i g).val).1 =
      (Chr.Psi l e (Chr.dirG ℚ Ω ψ) (k.j v g) ^ Fr.w 3 i).val.1 := fun v i g hg =>
    (h2 v i g).trans (by rw [hψ v i g hg]; rfl)
  obtain ⟨t1, t2, t3⟩ := hT Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R ξ r hr' hi
  obtain ⟨⟨w, hw⟩, hip⟩ := hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R hka φ hφ ξ r hr' hi hψ'
  obtain ⟨D, hD, D', hD', k1, k2, hli⟩ := hTan Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f R ξ r hr' hi hψ' v hpc i j
    fun g => (h2 v i g).trans ((hno g).trans (congrArg (· * _) (h2 v j g).symm))
  exact hE Ω l c η _ σ g₁ B M L Φ k c₁ f _ R φ hφ hsurj J ξ w
    (hU l L Ω R.s R.V c₁ 3 R.r R.B₀ Λ ι J m (by norm_num) hΛ hmod.dense hmod.end1 hnum) t1 hw hip
    (hR Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f _ R hL hka φ hφ hsurj J hgood hdim hmod.dense hend (ptA R ξ) t2 t3)
    D hD D' hD' k1 k2 hli
set_option maxHeartbeats 1600000 in
theorem openEx2E_alt :
    GlobalTheory.Published.GlobalArtinReciprocity → UpperTheory.V.W.LocCFTAll → _root_.UpperTheory.V.W.ModUAlt → _root_.UpperTheory.V.J.ModNAlt → UpperTheory.V.W.LevEx → UpperTheory.V.W.LamEx → UpperTheory.V.W.ProModularRingExists → _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense → _root_.UpperTheory.V.Sd.Seed2Alt → UpperTheory.V.Sd.Twist → UpperTheory.V.Sd.AlgCyc → UpperTheory.V.Sd.AlgRes → _root_.UpperTheory.Gal.projectedFormsSystemPart.OpenEx2EAlt := by
  intro hA hLoc hMod hN hLev hLam hB0 hS3 hS2 hTw hCyc hRes Ω _ _ _ l _ ι c _ N _ e ψ η σ g₁ B M H hev L _ _ _ _ _ Φ C₀ k hok hbig hseed A _
  obtain ⟨K, _, _, _, N', w, χ', η', θ, j, hD, hne, hord, hη, hcong, hdisc⟩ := hseed
  have hv : Nonempty Φ.V := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := hbig.1
    simp [UpperTheory.V.Fr.Frame.d] at this
  obtain ⟨v⟩ := hv
  have hker : η.ker = galOf ℚ K Ω := by
    rw [← hD.η_ker]
    ext s
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_eq_one, ← Units.val_eq_one, hη s]
    exact_mod_cast Iff.rfl
  haveI := hD.imag
  obtain ⟨κ, hκ⟩ := hTw K Ω hD.quad l hok.l_odd hdisc ι σ hD.cc
  obtain ⟨hk3, hk2⟩ := UpperTheory.V.Pr.kaOf hCyc hRes Ω l ι c N e ψ η σ g₁ B M H L Φ k
  obtain ⟨ka, hk2, hka⟩ := hk2 K hker κ hκ
  have oe_norm {x : PadicAlgCl l} (h : IsIntegral ℤ_[l] x) : ‖x‖ ≤ 1 := by
    have hq : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral x
    change spectralValue (minpoly ℚ_[l] x) ≤ 1
    rw [spectralValue_le_one_iff (minpoly.monic hq)]
    intro n
    rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] h, Polynomial.coeff_map]
    exact PadicInt.norm_le_one _
  have oe_field {R : Type} [CommRing R] [Algebra ℤ_[l] R] [Module.Finite ℤ_[l] R]
      (φ : R →ₐ[ℤ_[l]] PadicAlgCl l) :
      ∃ E : IntermediateField ℚ_[l] (PadicAlgCl l), FiniteDimensional ℚ_[l] E ∧ ∀ x, φ x ∈ E ∧ ‖φ x‖ ≤ 1 := by
    obtain ⟨t, ht⟩ := Module.Finite.fg_top (R := ℤ_[l]) (M := R)
    haveI := (t.finite_toSet.image φ).to_subtype
    refine ⟨IntermediateField.adjoin ℚ_[l] (φ '' (t : Set R)),
      IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x, fun x => ⟨?_,
        oe_norm ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) x).map φ)⟩⟩
    have hx : x ∈ Submodule.span ℤ_[l] (t : Set R) := ht ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul a b _ hb =>
      rw [map_smul, ← algebraMap_smul ℚ_[l] a]
      exact IntermediateField.smul_mem _ hb
  have ⟨c₂, hcc, hAc⟩ : ∃ c₂ : Coef l, c.O ≤ c₂.O ∧ ∀ x ∈ A, x ∈ c₂.O := by
    haveI : Module.Finite ℤ_[l] A := Module.Finite.trans c.O A
    obtain ⟨E₁, f₁, m₁⟩ := oe_field c.O.val
    obtain ⟨E₂, f₂, m₂⟩ := oe_field (A.val.restrictScalars ℤ_[l])
    obtain ⟨c₂, hc⟩ := UpperTheory.V.X.So.coefOf l (E₁ ⊔ E₂)
    exact ⟨c₂, fun x hx => (hc x).2 ⟨(le_sup_left : E₁ ≤ E₁ ⊔ E₂) (m₁ ⟨x, hx⟩).1, (m₁ ⟨x, hx⟩).2⟩,
      fun x hx => (hc x).2 ⟨(le_sup_right : E₂ ≤ E₁ ⊔ E₂) (m₂ ⟨x, hx⟩).1, (m₂ ⟨x, hx⟩).2⟩⟩
  obtain ⟨c₁, hle₁, hL, hv3, hv2, -⟩ := UpperTheory.V.Pr.coefEx l c₂ L Ω _ _ hk3.alg.1 hk2.alg.1
  have hle : c.O ≤ c₁.O := hcc.trans hle₁
  have ⟨f, hf⟩ : ∃ f : ResidueField c.O →+* ResidueField c₁.O,
      ∀ (a : c.O) (b : c₁.O), a.1 = b.1 → f (residue c.O a) = residue c₁.O b := by
    let i : c.O →+* c₁.O := (Subalgebra.inclusion hle).toRingHom
    have hi : i.IsIntegral := by
      haveI : Algebra.IsIntegral ℤ_[l] c₁.O := Algebra.IsIntegral.of_finite ℤ_[l] c₁.O
      have e : i.comp (algebraMap ℤ_[l] c.O) = algebraMap ℤ_[l] c₁.O := (Subalgebra.inclusion hle).comp_algebraMap
      refine RingHom.IsIntegral.tower_top (algebraMap ℤ_[l] c.O) i ?_
      rw [e]
      exact fun x => Algebra.IsIntegral.isIntegral x
    haveI : IsLocalHom i := hi.isLocalHom (Subalgebra.inclusion_injective hle)
    exact ⟨ResidueField.map i, fun a b h => by
      rw [ResidueField.map_residue]
      exact congrArg _ (Subtype.ext h)⟩
  haveI hco := UpperTheory.V.Pr.coefIs l c₁
  obtain ⟨R₂⟩ := UpperTheory.V.Pr.cRealEx hA hLoc hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka C₀ (Or.inl rfl)
    hok hbig hle hf hk2 hv2
  obtain ⟨R₃⟩ := UpperTheory.V.Pr.cRealEx hA hLoc hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl)
    hok hbig hle hf hk3 hv3
  obtain ⟨m₃, hm₃, -, r₃, -, s₃⟩ := hS3 K L Ω l ι σ N' w χ' η' θ j hD hne M H.3
    (by rw [mul_comm]; exact (Nat.mul_dvd_mul_left l hev.two_dvd).trans H.2)
    (UpperTheory.V.Z.Sym.Pl.linkUnr Ω l _ η _ σ g₁ B M L Φ k) (UpperTheory.V.Z.Sym.Pl.chiUnr Ω l c N e ψ χ' j hord hcong M H.2 L) 2
  obtain ⟨m₂, hm₂, -, r₂, -, -, -, s₂⟩ := hS2 K L Ω l ι σ N' w χ' η' θ j hD κ ka hκ hka 2
  obtain ⟨-, hμ⟩ := UpperTheory.V.Pr.degEq Ω l ι c N e ψ η σ g₁ B M H L Φ k v
  obtain ⟨Λ₂, hΛ₂⟩ := hLam l L Ω R₂.s R₂.V c₁ 2 R₂.r
  obtain ⟨Λ₃, hΛ₃⟩ := hLam l L Ω R₃.s R₃.V c₁ 3 R₃.r
  obtain ⟨J₂, hJ₂⟩ := hMod l L Ω R₂.s R₂.V R₂.hV hμ c₁ hL 2 (by norm_num) R₂.r R₂.B₀ Λ₂ ι
  obtain ⟨J₃, hJ₃, hnum⟩ := hN l L Ω R₃.s R₃.V R₃.hV hμ c₁ hL R₃.r R₃.v0 R₃.B₀ Λ₃ ι
  have h₂ := _root_.UpperTheory.V.J.mod_l_open_existence ι H v R₂ Λ₂ hΛ₂ J₂ hJ₂
    (_root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 2 ka R₂ hk2 χ' j hord hcong m₂ hm₂ _ (by
      convert s₂ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]) J₂ hJ₂.pt)
  have h₃ := _root_.UpperTheory.V.J.mod_l_open_existence ι H v R₃ Λ₃ hΛ₃ J₃ hJ₃
    (_root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ R₃ hk3 χ' j hord hcong m₃ hm₃ _ (by
      convert s₃ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]) J₃ hJ₃.pt)
  obtain ⟨φ, hφ, hsurj, hgood⟩ := UpperTheory.V.J.absGood l c₁.O _ R₂.T R₃.T J₂ J₃ h₂ h₃
  obtain ⟨R₀, hp⟩ := cRealAv hLev hB0 Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ C₀ (Or.inr rfl)
    hok hbig hle hf hk3 hv3 R₃.s.p R₃.s.p_prime.ne_zero
  obtain ⟨Λ₀, hΛ₀⟩ := hLam l L Ω R₀.s R₀.V c₁ 3 R₀.r
  obtain ⟨J₀, hJ₀⟩ := hMod l L Ω R₀.s R₀.V R₀.hV hμ c₁ hL 3 (by norm_num) R₀.r R₀.B₀ Λ₀ ι
  have h₀ := _root_.UpperTheory.V.J.mod_l_open_existence ι H v (setS R₀ R₃.S) Λ₀ hΛ₀ J₀ hJ₀
    (_root_.UpperTheory.V.Pr.seedPtOf_alt hA Ω l ι c N e ψ η σ g₁ B M H L Φ k c₁ f 3 _ (setS R₀ R₃.S) hk3 χ' j hord hcong m₃ hm₃ _ (by
      convert s₃ using 2 with i i i <;> fin_cases i <;> simp [UpperTheory.V.Fr.w]) J₀ hJ₀.pt)
  obtain ⟨φ₀, hφ₀, -, hgood₀⟩ := UpperTheory.V.J.absGood l c₁.O _ R₂.T (setS R₀ R₃.S).T J₂ J₀ h₂ h₀
  exact ⟨c₁, hco, f, R₃, Λ₃, J₃, φ, _, fun x hx => hle₁ (hAc x hx), hL, hk3, hJ₃, hnum, hΛ₃, hφ, hsurj, hgood, h₃.dim,
    _root_.UpperTheory.Gal.projectedFormsSystemPart.endPt_of_allGood_of_arithmeticPointClassicality R₃ R₀ hp hφ hgood hJ₃.end2 hφ₀ hgood₀ hJ₀.end2⟩
theorem linkedUnlE_alt (hG : GlobalTheory.Published.GlobalArtinReciprocity) (h1 : W.LocCFTAll) (h2 : _root_.UpperTheory.V.W.ModUAlt) (hN : _root_.UpperTheory.V.J.ModNAlt) (h3 : W.LevEx)
    (h4 : W.LamEx) (h5 : W.ProModularRingExists) (s3 : _root_.UpperTheory.V.Z.Sym.UnitaryThreeAutomorphyDense) (s2 : _root_.UpperTheory.V.Sd.Seed2Alt) (tw : Sd.Twist) (cy : Sd.AlgCyc) (re : Sd.AlgRes)
    (hT : TanA) (hC : _root_.UpperTheory.V.Th.DenseThresholdMainCase) : UpperTheory.V.Z.J.LinkedUnlE :=
  _root_.UpperTheory.Gal.projectedFormsSystemPart.UnitaryRankTwoFlagsAlt (_root_.UpperTheory.Gal.projectedFormsSystemPart.openEx2E_alt hG h1 h2 hN h3 h4 h5 s3 s2 tw cy re) xiEx xiTI (xiArith hG) hT (_root_.UpperTheory.Gal.projectedFormsSystemPart.red2_alt hG hC) _root_.UpperTheory.V.J.unramified_algebraic_weights endJ
    fun l _ => GlobalTheory.nonempty_padicAlgCl_ringEquiv_complex l
end UpperTheory.Gal.projectedFormsSystemPart
end
end
