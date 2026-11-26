module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ChebotarevFamilies.PFromAutOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.BlockForm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.TwoBlock
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FlagBasis
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.DetAsm
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CharPOfPadic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.CharPOfPadicAlt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.ArPl
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.B1abs
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArSys
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ObstructionBoundOfDuality
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.CkCastMod
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.RawMain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelmerCocyclesLimitAndDescentProperties
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.TaylorWilesSecondConditionAtLimitOfGroupConditio
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.FirstCohomologyBoundOfBoundaryBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SecondCohomologyBoundOfBoundaryBound
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.KoszulThreeOfDet
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmodEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PmDimQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.HatEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.RFSurj
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.OBLt
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.ComplOddPart
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ClosureConjugation.UrepOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.AlCSmul
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.CotangentIndependentOfResidues
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OoExKer
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FiniteOpenHomsToFiniteGroup
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.RmapsEx
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.PatchedModuleFreeFiniteOverIwasawaAlgebra
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.EventuallyExistsPatchedModuleQuotientMaps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.FreeNQuot
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.LaDimArith
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.OoPair
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AnnihilatorBaseChange.NonssT
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.Oprime
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.MemSpanMapE0kerOfPairMaps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.AutBc

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchingBaseChange.ChainTens
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa
open scoped TensorProduct

theorem UpperTheory.V.Pa.BC.chain_tens :
    ∀ (O O' B : Type) [CommRing O] [CommRing O'] [Nontrivial O'] [IsLocalRing O] [Algebra O O'] [Module.Finite O O'] [Module.Free O O'] [CommRing B] [Algebra O B] (h : ℕ) (p : Fin (h + 1) → Ideal B) (e : Fin h → Ideal B), (∀ i, (p i).IsPrime) → (∀ i, (e i).IsPrime ∧ e i ≤ p i.castSucc ∧ e i ≤ p i.succ) → (∃ (P : Fin (h + 1) → Ideal (O' ⊗[O] B)) (E : Fin h → Ideal (O' ⊗[O] B)), (∀ i, (P i).IsPrime ∧ (P i).comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = p i) ∧ ∀ i, (E i).IsPrime ∧ (E i).comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = e i ∧ E i ≤ P i.castSucc ∧ E i ≤ P i.succ) ∧ ∀ (P : Ideal (O' ⊗[O] B)) (q : Ideal B), P.IsPrime → q.IsPrime → q ≤ P.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) → ∃ Q : Ideal (O' ⊗[O] B), Q.IsPrime ∧ Q.comap (Algebra.TensorProduct.includeRight : B →ₐ[O] O' ⊗[O] B) = q ∧ Q ≤ P := by
  intro O O' B _ _ _ _ _ _ _ _ _ h p e hp he
  letI : Algebra B (O' ⊗[O] B) := Algebra.TensorProduct.rightAlgebra
  let φ : B ⊗[O] O' ≃ₐ[B] O' ⊗[O] B := Algebra.TensorProduct.commRight O B O'
  haveI : Module.Finite B (O' ⊗[O] B) := Module.Finite.equiv φ.toLinearEquiv
  haveI : Module.Free B (O' ⊗[O] B) := Module.Free.of_equiv φ.toLinearEquiv
  haveI : Module.FaithfullyFlat O O' := inferInstance
  haveI : Module.FaithfullyFlat B (O' ⊗[O] B) :=
    Module.FaithfullyFlat.of_linearEquiv B (B ⊗[O] O') φ.symm.toLinearEquiv
  haveI : FaithfulSMul B (O' ⊗[O] B) := inferInstance
  exact UpperTheory.V.Pa.BC.chain_lift B (O' ⊗[O] B) h p e hp he
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.BoundW1Arithmetic
namespace UpperTheory.V.Pa

theorem b1Ar : FirstOrderDualArithmeticBound := by
  intro hcoh l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T x0 x k al hS hloc _ hρ hN4 hE hD
  obtain ⟨d', hsum, hab⟩ := hloc
  obtain ⟨A⟩ := arSys hcoh l L Ω s V0 O n r T x0 hS
  refine b1abs l (locOf r) (globOf r V0) T n x k al _ V0.frame.D0 A d' s.odd ?_ hab
    (arPl hcoh l L Ω s V0 O n r hS).1 hρ hN4 hE hD
  rw [← hsum]
  first
    | exact (finsum_eq_sum_of_fintype _).symm
    | (convert (finsum_eq_sum_of_fintype d').symm)

end UpperTheory.V.Pa
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.Raw
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.CoreBC
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.LiftPt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.Imports
namespace UpperTheory.V.Pa

theorem s4 : S4 := selmer_cocycles_limit_and_descent_properties

end UpperTheory.V.Pa
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.GalOut
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.S6
open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

theorem s6 : S6 := by
  intro l _ L G G0 h n x O _ _ _ _ _ _ r B _ _ _ u P Bh _ _ _ rF hl hc hr hk
  letI : Algebra Bh (FractionRing x.A) := rF.toAlgebra
  have hk' : RingHom.ker (algebraMap Bh (FractionRing x.A)) = maximalIdeal Bh := hk
  obtain ⟨H⟩ := hat_ex P (Bh := Bh) hr
  have hs := rF_surj P (Bh := Bh) hr hk'
  haveI := hc.noeth
  haveI := hc.complete
  haveI := H.fin
  have h2 : IsUnit (2 : Bh) := by
    by_contra hn
    have h3 : (2 : Bh) ∈ RingHom.ker (algebraMap Bh (FractionRing x.A)) := by rw [hk']; exact hn
    rw [RingHom.mem_ker, map_ofNat] at h3
    have h4 : (2 : x.K) = 0 := by
      have h5 : (algebraMap x.A (FractionRing x.A)).comp (PowerSeries.C (R := x.K)) 2 = 0 := by rw [map_ofNat]; exact h3
      exact (map_eq_zero _).1 h5
    have h6 : IsUnit (2 : ℤ_[l]) := by
      rw [PadicInt.isUnit_iff]
      refine le_antisymm (PadicInt.norm_le_one _) (not_lt.1 fun hlt => hl ?_)
      have h7 : ‖((2 : ℤ) : ℤ_[l])‖ < 1 := by simpa using hlt
      rw [PadicInt.norm_int_lt_one_iff_dvd] at h7
      exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 (by exact_mod_cast h7)
    have h8 := h6.map (algebraMap ℤ_[l] x.K)
    rw [map_ofNat, h4] at h8
    exact not_isUnit_zero h8
  have hst := hat_st P hr H
  have hrg := hat_range P hs H
  obtain ⟨U, hx, hrk⟩ := idem x.a H.DE H.T H.r x.a_pos x.a_le h2 H.ch H.tr hk' (hat_chi P hr H) hst
    fun Z hZ => (hrg Z).1 hZ
  have hg : Nonempty (GrAlg H.T n x.a H.r U.ep) := by
    rcases x.a_le.lt_or_eq with ha | ha
    · exact gr_E x.a H.T H.r U x.a_pos ha hk' hst hx fun y => (hrg _).2 ⟨y, rfl⟩
    · have hn : 1 ≤ n := ha ▸ x.a_pos
      revert U
      rw [ha]
      intro U hx _
      exact gr_I H.T H.r U hn hst hx
  obtain ⟨g⟩ := hg
  exact urep_of H g U.coi hrk

end UpperTheory.V.Pa
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

private theorem ctx_out {l : ℕ} [Fact l.Prime] (S : Ctx l) (D0 : ℕ) (h1 : K1 S.h S.k D0) (h2 : K2 S.h S.k) (h3 : K3 S.h S.k)
    (Z Q : Ideal S.Bh) (hZ : Z.IsPrime) (hQ : Q.IsPrime) (hs : DiscSt (S.u.D.map (algebraMap S.B S.Bh)) Z)
    (hd : ((1 + D0 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (S.Bh ⧸ Z))
    (hq : DiscSt (S.u.D.map (algebraMap S.B S.Bh)) Q ∨ NonSS S.P.ker (algebraMap S.B S.Bh) Q) : Z ≤ Q := by
  obtain ⟨X, m, c, hX, hm, hc, hg, hr⟩ := pres l S D0 (k1F l _ _ _ S.h _ _ S.k D0 h1) (k2F l _ _ _ S.h _ _ S.k h2)
    (k3F l _ _ _ S.h _ _ S.k h3)
  by_cases ha : S.x.a = S.n
  · have hN := S.U.typeI ha
    have hi : ired S.U.N = ⊥ := by
      refine le_bot_iff.1 (Ideal.span_le.2 ?_)
      rintro b ⟨y, hy, z, -, e⟩
      rw [hN, Submodule.mem_bot] at hy
      rw [hy, zero_mul] at e
      exact S.U.inj (by rw [← e, map_zero])
    refine presOut0 S.OO S.Bh D0 X hX ?_ Z Q hZ hQ hd
    simpa only [Ctx.J2, hi, sup_bot_eq] using hg
  · haveI := S.U.fin
    refine presOut1 S.OO S.Bh S.U.AA S.U.N S.U.inj S.U.compl S.U.mul_mem D0 S.k.g X m c hX hm hc hg hr Z Q hZ hQ hd
      ((discImp l S Z hZ hs).resolve_left ha) ?_
    rcases hq with hq | hq
    · exact Or.inl ((discImp l S Q hQ hq).resolve_left ha)
    · exact Or.inr (S.U.thick Q hQ hq)

theorem galOut : GalOut := by
  intro l _ L G G0 h n x k O _ _ _ hO _ _ r B _ _ _ u P Bh _ _ _ D0 hl hc h1 h2 h3 Z Q hZ hQ hs hd hq
  haveI := hO.complete
  obtain ⟨rF, hf, hk⟩ := rfEx x.K O B Bh P.f hc
  obtain ⟨U⟩ := s6 l L G G0 h n x O r B u P Bh rF hl hc hf hk
  obtain ⟨OO, i1, i2, i3, i4, i5, i6, a1, a2, a3, a4⟩ := ooEx x.K O B Bh P.f P.s rF P.surj P.f_s hc hf
  exact ctx_out
    { odd := hl, L := L, G := G, G0 := G0, h := h, n := n, x := x, k := k, O := O, r := r, B := B, u := u, P := P, Bh := Bh,
      cpl := hc, rF := rF, rF_f := hf, rF_ker := hk, U := U, OO := OO, d6 := i6, oo_A := a1, oo_O := a2, ordinaryPointSection := a3, oo_surj := a4 }
    D0 h1 h2 h3 Z Q hZ hQ hs hd hq

end UpperTheory.V.Pa
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.CohLim
open UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

theorem cohLim : CohLim := by
  intro l _ L G0 T Λ n x k al D0 _ hT he h1 h2
  have hPh : TopFG Λ.Ph := by
    obtain ⟨s, hs⟩ := Λ.fg
    exact ⟨s, s.finite_toSet, (topGen_iff _).2 hs⟩
  have hG : TopFG Λ.G.Γ := (TopFG.subgroup_quot Λ.Ph hPh).2 _ Λ.πo Λ.πo_cont Λ.πo_surj
  exact ⟨firstCohomologyBound_of_boundaryBound l L _ _ Λ.h n x k D0 hG (taylorWiles_first_condition_at_limit_of_group_condition l L G0 T Λ n x k D0 h1), secondCohomologyBound_of_boundaryBound l L _ _ Λ.h n x k hG (taylorWiles_second_condition_at_limit_of_group_condition l L G0 T Λ n x k h2),
    koszulThree_of_det l L G0 T Λ n x k al hT he⟩

end UpperTheory.V.Pa
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.AnnBc
open IsLocalRing Filter UpperTheory.V.AlgebraTools UpperTheory.V.Pa.Core
open scoped TensorProduct

namespace UpperTheory.V.Pa

private theorem ann_bc {BB B MM : Type} [CommRing BB] [CommRing B] [Algebra BB B] [AddCommGroup MM] [Module BB MM]
    {a : BB} (ha : a ∈ Module.annihilator BB MM) : algebraMap BB B a ∈ Module.annihilator B (B ⊗[BB] MM) := by
  rw [Module.mem_annihilator] at ha ⊢
  intro t
  rw [algebraMap_smul]
  induction t using TensorProduct.induction_on with
  | zero => exact smul_zero _
  | tmul b m => rw [← TensorProduct.tmul_smul, ha, TensorProduct.tmul_zero]
  | add x y hx hy => rw [smul_add, hx, hy, add_zero]

private theorem s5_lemma {Λ R σ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [CommRing R]
    [IsNoetherianRing R] [Fintype σ] (s : MvPowerSeries σ Λ →+* R) (f : R) (ii : Ideal R) (X : Type)
    [AddCommGroup X] [Module R X] [Module Λ X] [Module.Free Λ X] [Module.Finite Λ X] [Module.Finite R X]
    (hC : ∀ (a : Λ) (x : X), a • x = s (MvPowerSeries.C a) • x)
    (P : PMod (fun a => s (MvPowerSeries.X a)) f ii X) [IsNoetherianRing P.BB]
    (ι : Type) (q : ι → Ideal R) (d : ℕ)
    (hq : ∀ i, (q i).IsPrime ∧ ii ≤ q i ∧ f ∉ q i ∧ ∀ (a : σ), s (MvPowerSeries.X a) ∈ q i)
    (hLa : ∀ i, ∃ (La : Type) (_ : CommRing La) (_ : IsLocalRing La) (_ : Algebra Λ La),
      IsCplAt Λ (Ideal.comap (s.comp MvPowerSeries.C) (q i)) La ∧ IsRegularLocalRing La ∧ ringKrullDim La = ↑d)
    (B : ι → Type) [∀ i, CommRing (B i)] [∀ i, IsLocalRing (B i)] [∀ i, Algebra P.BB (B i)]
    (hcpl : ∀ i, IsCplAt P.BB (Ideal.map (algebraMap R P.BB) (q i)) (B i)) :
    Nonempty (PatchedSupportCompletions s ii (Module.annihilator R X) q (d + Fintype.card σ)) := by
  haveI := P.fin
  have hyp := fun i => yPrime R σ (fun a => s (MvPowerSeries.X a)) f P.BB P.cpl (q i) (hq i).1 (hq i).2.2.1
    (hq i).2.2.2
  letI iAlgR : ∀ i, Algebra R (B i) := fun i => ((algebraMap P.BB (B i)).comp (algebraMap R P.BB)).toAlgebra
  haveI iTow : ∀ i, IsScalarTower R P.BB (B i) := fun i => IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  refine outOfNil Λ R σ s ii (Module.annihilator R X) ι q (d + Fintype.card σ) B
    (fun i => Module.annihilator (B i) (B i ⊗[P.BB] P.MM))
    (fun i => (hq i).2.1) (fun i => (hyp i).2.2.2 (B i) (hcpl i)) ?_ ?_ ?_ ?_
  · intro i x hx
    obtain ⟨k, hk⟩ := Ideal.mem_comap.mp (P.nil hx)
    refine Ideal.mem_comap.mpr ⟨k, ?_⟩
    have := ann_bc (B := B i) hk
    rw [← map_pow] at this
    rw [← map_pow]
    exact this
  · intro i Z hZ
    obtain ⟨La, _, _, _, hLcpl, hreg, hdim⟩ := hLa i
    rw [pmDim Λ R σ (s.comp MvPowerSeries.C) (fun a => s (MvPowerSeries.X a)) f ii X P (q i) d La (B i) hC
      (hq i).1 (hq i).2.2.1 (hq i).2.2.2 hLcpl hreg hdim (hcpl i) Z hZ]
  · intro i Q hQ _ hy
    have := pmFib R σ (fun a => s (MvPowerSeries.X a)) f ii X P (B i) Q hQ (fun a => hy a)
    rw [Ideal.comap_comap] at this
    exact this
  · intro i i' Z Q hZ hQ hSZ hZQ hy hQq
    have hP : Ideal.comap (algebraMap P.BB (B i)) Q ≤ Ideal.map (algebraMap R P.BB) (q i') :=
      (hyp i').2.2.1 _ (Ideal.comap_isPrime _ Q) (fun a => hy a) (by rw [Ideal.comap_comap]; exact hQq)
    obtain ⟨Z', hZ', hS', hc⟩ := pmMove P.BB P.MM (B i) (B i') _ Z (hcpl i') hZ hSZ
      (le_trans (Ideal.comap_mono hZQ) hP)
    refine ⟨Z', hZ', hS', ?_⟩
    have := congrArg (Ideal.comap (algebraMap R P.BB)) hc
    rw [Ideal.comap_comap, Ideal.comap_comap] at this
    exact this

theorem s5 : S5 := by
  intro Λ R σ _ _ _ _ _ _ _ _ _ s U f ii M _ _ X _ _ _ _ _ hU hC hX hM1 hM2 hG ι q d hq hLa
  obtain ⟨P⟩ := pmodEx Λ R σ s U f ii M X hU hC hX hM1 hM2 hG
  haveI : IsNoetherianRing P.BB := P.cpl.noeth
  haveI hfinR : Module.Finite R X := by
    letI : Algebra Λ R := (s.comp MvPowerSeries.C).toAlgebra
    haveI : IsScalarTower Λ R X := ⟨fun a r x => by
      rw [Algebra.smul_def, mul_smul, hC]
      rfl⟩
    exact Module.Finite.of_restrictScalars_finite Λ R X
  have hp := fun i => (yPrime R σ (fun a => s (MvPowerSeries.X a)) f P.BB P.cpl (q i) (hq i).1 (hq i).2.2.1
    (hq i).2.2.2).1
  exact s5_lemma s f ii X hC P ι q d hq hLa
    (fun i => @CplAt P.BB _ (Ideal.map (algebraMap R P.BB) (q i)) (hp i))
    (fun i => by
      haveI := hp i
      exact isCplAt_cplAt P.BB _)

end UpperTheory.V.Pa
end

open IsLocalRing Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa.Core
open scoped TensorProduct

namespace UpperTheory.V.Pa

section
variable {l : ℕ} [Fact l.Prime] {L : Loc} {G0 : Glob l L} {T : TWGrp G0} {n : ℕ}
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O]
    {r : Resid G0.frame O n} {B : Type} [CommRing B] [Algebra O B] [IsCO O B] {u : Pair r B} {J : Ideal B} {D : ℕ}
    (A : TWAut u J Unit D T)

private theorem lift_pt (hA : Adapted T (r := r))
    (hadj : Algebra.adjoin B (Set.range fun p : Fin T.q × Fin n => (Sp.u _ _ p.1 p.2 : Spo A)) = ⊤)
    {D0 : ℕ} (x : Pt T u D0) (P : Ideal (Spo A)) (hP : P.IsPrime)
    (h : P.comap (algebraMap B (Spo A)) = RingHom.ker x.f) :
    ∃ x' : Spo A →ₐ[O] x.x.A, (∀ b, x' (algebraMap B (Spo A) b) = x.f b) ∧ RingHom.ker x' = P := by
  obtain ⟨x', h1, h2⟩ := exists_lift_ker_eq B (Spo A) x.x.A x.f.toRingHom _ _
    (fun p : Fin T.q × Fin n => u.D.chi (MonoidAlgebra.single (T.sg p.1) 1)) hadj (fun p => by
      refine ⟨(chiRes l G0.frame n O r B u (T.sg p.1) (A.ut p.1) (A.ut_res p.1)).1, ?_, ?_⟩
      · rw [Polynomial.aeval_def, Polynomial.eval₂_eq_eval_map,
          ← (spRoots B T.q n (fun j => u.D.chi (MonoidAlgebra.single (T.sg j) 1)) _ p.1).1, Polynomial.eval_prod]
        exact Finset.prod_eq_zero (Finset.mem_univ p.2) (by simp)
      · have e1 := ((CA.d_gmap u.D).2.2.1 x.f.toRingHom (MonoidAlgebra.single (T.sg p.1) 1)).1
        rw [← e1, x.maps.1, MonoidAlgebra.mapRingHom_single, map_one]
        have e2 : (GDet.ofRep (mat x.x.ρ)).chi (MonoidAlgebra.single (T.sg p.1) 1) = (mat x.x.ρ (T.sg p.1)).charpoly := by
          show (GDet.repAlg _ _ _).det = _
          rw [Matrix.charpoly]
          congr 1
          ext i j : 2
          by_cases hij : i = j <;> simp [GDet.repAlg, Matrix.charmatrix_apply, hij, Matrix.one_apply, Matrix.diagonal_apply]
        rw [e2, (x.eig p.1).2]
        exact Polynomial.Splits.prod fun i _ => Polynomial.Splits.X_sub_C _) P hP h
  refine ⟨{ x' with commutes' := fun a => ?_ }, fun b => DFunLike.congr_fun h1 b, h2⟩
  rw [IsScalarTower.algebraMap_apply O B (Spo A)]
  exact (DFunLike.congr_fun h1 (algebraMap O B a)).trans (x.f.commutes a)

end

theorem core : Core := by
  intro l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D A hl hP hA hgen h x hx e he hq₁ q hq hqle hst
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)
  haveI : Finite (ResidueField O) := IsCoef.finite (l := l)
  have hn : 1 ≤ n := (x 0).x.a_pos.trans (x 0).x.a_le
  obtain ⟨Λ⟩ := s4 l L G0 T hP
  obtain ⟨W⟩ := rrEx l L G0 T Λ n O r B u J D A
  obtain ⟨m⟩ := rmapsEx l L G0 T Λ n O r B u J D A W hA
  obtain ⟨⟨hco, hfree, hfin, hadj⟩, -⟩ := spoCo l L G0 T Λ n O r B u J D A hA
  have hker := piKer l L G0 T Λ n O r B u J D A W m hn hA
  have hsurj := piSurj l L G0 T Λ n O r B u J D A W m hA hgen
  let πb : (W.R ⧸ ii W) →ₐ[O] Spo A := Ideal.Quotient.liftₐ (ii W) m.π fun a ha => hker ha
  have hπb : ∀ a, πb (Ideal.Quotient.mk (ii W) a) = m.π a := fun a => rfl
  haveI : Nontrivial (W.R ⧸ ii W) := πb.toRingHom.domain_nontrivial
  haveI : IsCO O (W.R ⧸ ii W) := co_quot O W.R _ (Ideal.Quotient.mkₐ O (ii W)) Ideal.Quotient.mk_surjective
  obtain ⟨o⟩ := ooPair l L G0 T Λ n O r B u J D A W hn
  haveI : FaithfulSMul B (Spo A) := inferInstance
  obtain ⟨⟨P, E, hPp, hE⟩, hdown⟩ := BC.chain_lift B (Spo A) h (fun i => RingHom.ker (x i).f) e
    (fun i => RingHom.ker_isPrime _) fun i => ⟨(he i).1, (he i).2.2⟩
  choose x' hx'1 hx'2 using fun i => lift_pt A hA hadj (x i) (P i) (hPp i).1 (hPp i).2
  have hpt := fun i => ooPt l L G0 T Λ n O r B u J D A W m o πb hπb hA _ (x i) (x' i) (hx'1 i) (hx i).1 (hx i).2
  obtain ⟨hf1, hf2, hf3, hf4⟩ := patchedModule_free_finite_over_iwasawaAlgebra l L G0 T Λ n O r B u J D A W m hA
  haveI : IsCO O (abelian₂ O Unit D) := co_mvps O O _
  haveI : Finite (ResidueField (abelian₂ O Unit D)) := Finite.of_surjective _ (resMap_bijective O (abelian₂ O Unit D)).2
  have hy0 : ∀ p, m.π (m.s (MvPowerSeries.X p)) = 0 := fun p => by rw [m.π_s]; simp
  obtain ⟨o5⟩ := s5 (abelian₂ O Unit D) W.R (Fin T.q × Fin n) m.s.toRingHom Λ.U (fo W) (ii W) (MN m) (X0 m) Λ.U_le hf3 hf4
    (freeN l L G0 T Λ n O r B u J D A W m) (eventually_exists_patchedModule_quotient_maps l L G0 T Λ n O r B u J D A W m hP hA)
    ⟨A.ex + 1, {a | Rel W a}, rfl, fun a ha => t3Of l L G0 T Λ n O r B u J D A W m a (by
      cases ha with
      | ker h k e => exact patched_trace_single_mul_sub_one_approx_annihilated l L G0 T Λ n O r B u J D A W m hn hA h k e
      | pol i g g' e => exact patched_lam_conj_twist_approx_annihilated l L G0 T Λ n O r B u J D A W m hA i g g' e
      | ord v g ga h e => exact patched_trace_local_charPoly_approx_annihilated l L G0 T Λ n O r B u J D A W m hA v g ga h e
      | ine w g ga h e e' => exact eventually_trace_inertia_congruence_of_adapted l L G0 T Λ n O r B u J D A W m hA w g ga h e e'
      | q1 j ph h e => exact t3Q1 l L G0 T Λ n O r B u J D A W m hA j ph h e
      | q2 j i ph ta h e e' => exact t3Q2 l L G0 T Λ n O r B u J D A W m hA j i ph ta h e e')⟩
    (Fin (h + 1)) (fun i => (P i).comap m.π) (1 + D)
    (fun i => by
      haveI := (hPp i).1
      refine ⟨Ideal.comap_isPrime _ _, fun a ha => ?_, fun hf => (hpt i).1 ?_, fun a => ?_⟩
      · show m.π a ∈ P i
        rw [show m.π a = 0 from hker ha]; exact zero_mem _
      · have : m.π (fo W) ∈ RingHom.ker (x' i) := by rw [hx'2]; exact hf
        exact this
      · show m.π (m.s (MvPowerSeries.X a)) ∈ P i
        rw [hy0]; exact zero_mem _)
    (fun i => by
      obtain ⟨La, j1, j2, j3, h1, h2, h3⟩ := laDim O (x i).x.K D ((x i).f.comp A.b.lam) (hx i).1 (hx i).2
      refine ⟨La, j1, j2, j3, ?_, h2, h3⟩
      convert h1 using 1
      ext a
      show m.π (m.s (MvPowerSeries.C a)) ∈ P i ↔ (x i).f (A.b.lam a) = 0
      rw [m.π_s, ← hx'2, RingHom.mem_ker, hx'1]; simp)
  have hmaps := ooMaps l L G0 T Λ n O r B u J D A W m o πb hπb
  have hSt : ∀ Q : Ideal (Spo A), DiscSt o.p.D (Q.comap πb) ↔ DiscSt u.D (Q.comap (algebraMap B (Spo A))) := fun Q => by
    have h1 := (BC.discSt_map n _ (Spo A) _ o.p.D).1 πb.toRingHom Q
    rw [hmaps.1, (BC.discSt_map n _ (Spo A) _ _).1, (BC.discSt_map n B B _ u.D).2.1 _ _ Λ.h.p₀_surj] at h1
    exact h1.symm
  have hyE : ∀ (Q : Ideal (Spo A)) a, Ideal.Quotient.mk (ii W) (m.s.toRingHom (MvPowerSeries.X a)) ∈ Q.comap πb := fun Q a => by
    show m.π (m.s (MvPowerSeries.X a)) ∈ Q
    rw [hy0]; exact zero_mem _
  obtain ⟨q₁, a1, a2, a3, a4⟩ := hq₁
  obtain ⟨Q₁, b1, b2, b3⟩ := hdown (P 0) q₁ (hPp 0).1 a1 (by rw [(hPp 0).2]; exact a4)
  obtain ⟨Q, c1, c2, c3⟩ := hdown (P (Fin.last h)) q (hPp _).1 hq (by rw [(hPp _).2]; exact hqle)
  have key := chainAbs (abelian₂ O Unit D) W.R (Fin T.q × Fin n) m.s.toRingHom (ii W) _ h _ _ o5 (DiscSt o.p.D)
    (fun i Q => NonSS (ooKer o) (algebraMap _ (o5.B i)) Q)
    (fun i => by
      haveI := (hPp i).1
      refine ⟨Ideal.comap_isPrime _ _, fun a ha => ?_⟩
      show m.π a ∈ P i
      rw [show m.π a = 0 from hker ha]; exact zero_mem _)
    (BC.discSt_map n _ B _ o.p.D).2.2
    (fun i Z Q hZ hQ h1 h2 h3 => by
      obtain ⟨Pt, e1, e2⟩ := (hpt i).2
      obtain ⟨k1, k2, k3⟩ := cohLim l L G0 T Λ n (x i).x (x i).k (x i).al _ hl hP (x i).eig (x i).b1 (x i).b2
      have hc : IsCplAt (W.R ⧸ ii W) (RingHom.ker Pt.f) (o5.B i) := by
        convert o5.cpl i using 1
        ext a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        rw [Ideal.mem_quotient_iff_mem (fun b hb => by
          show m.π b ∈ P i
          rw [show m.π b = 0 from hker hb]; exact zero_mem _), e1, ← hx'2]
        rfl
      refine galOut l L Λ.G G0 Λ.h n (x i).x (x i).k O o.r' _ o.p Pt (o5.B i) _ hl hc k1 k2 k3 Z Q hZ hQ
        (((BC.discSt_map n _ _ _ o.p.D).1 _ _).2 h1) ?_ ?_
      · convert h2 using 2
        simp [mul_comm, add_assoc]
      · rw [e2]
        exact h3.imp_left ((BC.discSt_map n _ _ _ o.p.D).1 _ _).2)
    (fun i => (E i).comap πb)
    (fun i => by
      haveI := (hE i).1
      refine ⟨Ideal.comap_isPrime _ _, hyE _, Ideal.comap_mono (f := m.π) (hE i).2.2.1, Ideal.comap_mono (f := m.π) (hE i).2.2.2,
        fun Q hQ hQE => nonssT l L G0 T Λ n O r B u J D A W m o πb hπb hP hA hn _ _ Q (E i) hQ (hE i).1 hQE ?_⟩
      rw [(hE i).2.1]; exact (he i).2.1)
    ⟨Q₁.comap πb, Ideal.comap_isPrime _ _, hyE _, Ideal.comap_mono (f := m.π) b3, (hSt _).2 (b2 ▸ a2),
      (patchedModule_annihilator_le_comap_iff_ideal_le l L G0 T Λ n O r B u J D A W m hsurj Q₁ b1).2 (b2 ▸ a3)⟩
    (Q.comap πb) (Ideal.comap_isPrime _ _) (hyE _) (Ideal.comap_mono (f := m.π) c3)
    (hst.imp (fun h1 => (hSt _).2 (c2 ▸ h1)) fun h1 Q' hQ' e =>
      nonssT l L G0 T Λ n O r B u J D A W m o πb hπb hP hA hn _ _ Q' Q hQ' c1 e (c2 ▸ h1))
  exact c2 ▸ (patchedModule_annihilator_le_comap_iff_ideal_le l L G0 T Λ n O r B u J D A W m hsurj Q c1).1 key

end UpperTheory.V.Pa
end

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W
open scoped TensorProduct

namespace UpperTheory.V.Pa

theorem coreBC : CoreBC := by
  intro l _ L G0 T n O _ _ _ _ _ r B _ _ _ u J D A0 hl hP hAd hG h x hx
  obtain ⟨O', _, _, _, _, α, P, hco, hfin, hfree, hloc, hcard, hα, hPm, hPα, hsplit⟩ :=
    BC.oprime l O (x 0).x.K
  letI : Algebra ℤ_[l] O' := ((algebraMap O O').comp (algebraMap ℤ_[l] O)).toAlgebra
  haveI : IsScalarTower ℤ_[l] O O' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsAdicComplete (maximalIdeal O) O := IsCoef.complete (l := l)
  haveI : Finite (ResidueField O) := IsCoef.finite (l := l)
  haveI : CharP (ResidueField O) l := IsCoef.char
  obtain ⟨⟨r', hr'⟩, hrr⟩ := BC.resid_bc l G0.frame O O' n r
  obtain ⟨hrIp, -, hrchi⟩ := hrr r' hr'
  obtain ⟨hTco, hιloc, hsm⟩ := BC.til_co O O' B
  obtain ⟨-, u', hu'⟩ := BC.pair_bc l G0.frame O O' n r r' hr' B (Til O O' B) (Til.ι O O' B)
    (Til.ι_algebraMap O O' B) u
  obtain ⟨A', hA'⟩ := BC.aut_bc l L G0 n O O' r r' B u u' J D T A0 hr' hu'
  have hphi := BC.phi0 l L G0 T hP
  have hAd' : Adapted (r := r') T :=
    ⟨fun g hg i => (hrchi i g).2 (hAd.1 g hg i), fun w => (hrIp w).trans (hAd.2 w)⟩
  have hG' : GenBy O' (pairVals u' ∪ {A'.b.lam (MvPowerSeries.X (Sum.inl ()))}) := by
    refine BC.gen_bc O O' B (pairVals u) _ hιloc hsm ?_ ?_ hG
    · rintro a (⟨i, g, rfl⟩ | ⟨v, i, g, rfl⟩)
      · left; left
        refine ⟨i, g, ?_⟩
        have h3 := ((CA.d_gmap u.D).2.2.1 (Til.ι O O' B) (MonoidAlgebra.single g 1)).2 i
        rw [MonoidAlgebra.mapRingHom_single, map_one, hu'.1] at h3
        exact h3.symm
      · left; right
        exact ⟨v, i, g, by rw [← hu'.2 v i]; rfl⟩
    · right; rw [hA']; rfl
  have hpr : ∀ i, (RingHom.ker (x i).f).IsPrime := fun i => RingHom.ker_isPrime _
  intro e he hq1 q hq hqle hst
  obtain ⟨⟨Pt', Et, hPt, hEt⟩, hdown⟩ := BC.chain_tens O O' B h (fun i => RingHom.ker (x i).f) e hpr
    (fun i => ⟨(he i).1, (he i).2.2⟩)
  have hl1 := fun i => BC.pt_lift l O O' α P B (x i).x.K (x i).f (Pt' i) hα hPm hPα
    (hsplit _ (hx i)) (hcard.trans (hx i).symm) (hPt i).1 (hPt i).2
  choose inst f' hsurj hfι hfs hker using hl1
  have hmaps : ∀ i, u'.Maps (f' i).toRingHom (GDet.ofRep (mat (x i).x.ρ)) (x i).x.ψ := by
    intro i
    have hc : (f' i).toRingHom.comp (Til.ι O O' B) = (x i).f.toRingHom := RingHom.ext (hfι i)
    refine ⟨?_, fun v j => ?_⟩
    · rw [← hu'.1, (CA.d_gmap u.D).2.1, hc]
      exact (x i).maps.1
    · rw [← hu'.2 v j, ← (x i).maps.2 v j, ← hc]
      rfl
  let x' : Fin (h + 1) → Pt T u' (D + n * T.q) := fun i =>
    @Pt.mk _ _ _ _ T _ _ _ _ _ r' _ _ _ _ u' _ (x i).x (inst i) (x i).k (x i).al (x i).eig (x i).b1 (x i).b2
      (f' i) (hmaps i)
  have hmain := core l L G0 T n O' r' (Til O O' B) u' _ D A' hl hP hAd' hG' h x'
    (fun i => ⟨hsurj i, by rw [hA']; exact hfs i⟩)
  have hup : ∀ Q : Ideal (O' ⊗[O] B), Q.IsPrime →
      (Ideal.map (Til.C O O' B) Q).IsPrime ∧
        Ideal.comap (Til.ι O O' B) (Ideal.map (Til.C O O' B) Q) =
          Ideal.comap Algebra.TensorProduct.includeRight Q :=
    fun Q hQ => BC.til_prime O O' B Q hQ
  have hle : ∀ (Q : Ideal (O' ⊗[O] B)) i, Q ≤ Pt' i →
      Ideal.map (Til.C O O' B) Q ≤ RingHom.ker (x' i).f := by
    intro Q i hQi
    rw [Ideal.map_le_iff_le_comap]
    exact hQi.trans (hker i).ge
  have hfinI : ∃ s : Finset G0.frame.G₀, ∀ y : MonoidAlgebra B G0.frame.G₀, ∃ c : G0.frame.G₀ → B,
      y - ∑ g ∈ s, MonoidAlgebra.single g (c g) ∈ TwoSidedIdeal.span (augmentationIdealKernel u) := by
    obtain ⟨s, hs⟩ := (BC.pair_mf l G0.frame O n r B u hphi).2.2 (pairGens u)
    exact ⟨s, fun y => (hs y).imp fun c hc => TwoSidedIdeal.subset_span hc⟩
  have hns : ∀ (E : Ideal (Til O O' B)) (e0 : Ideal B), E.IsPrime →
      Ideal.comap (Til.ι O O' B) E = e0 → NonSS (augmentationIdealKernel u) (RingHom.id B) e0 →
        NonSS (augmentationIdealKernel u') (RingHom.id _) E := by
    intro E e0 hE hEe h0
    have h1 : NonSS (augmentationIdealKernel u) (Til.ι O O' B) E :=
      BC.nonSS_field B B (Til O O' B) G0.frame.G₀ (augmentationIdealKernel u) (RingHom.id B) (Til.ι O O' B) e0 E hE
        (by rw [hEe, Ideal.comap_id]) hfinI h0
    refine BC.nonSS_mono B (Til O O' B) (Til O O' B) G0.frame.G₀ G0.frame.G₀ (MonoidHom.id _)
      (augmentationIdealKernel u) (augmentationIdealKernel u') (Til.ι O O' B) (RingHom.id _) E (fun g => ⟨g, rfl⟩) ?_ h1
    intro z hz
    rw [MonoidAlgebra.mapRingHom_id, MonoidAlgebra.mapDomainRingHom_id]
    exact BC.mem_span_map_e0ker_of_pair_maps l G0.frame O O' n r r' B (Til O O' B) u u' (Til.ι O O' B) hphi hrIp
      (fun a => Til.ι_algebraMap O O' B _) hu' z hz
  have hds : ∀ (E : Ideal (Til O O' B)), DiscSt u.D (Ideal.comap (Til.ι O O' B) E) → DiscSt u'.D E := by
    intro E hE
    rw [← hu'.1]
    exact ((BC.discSt_map n B (Til O O' B) G0.frame.G₀ u.D).1 (Til.ι O O' B) E).2 hE
  obtain ⟨q₁, hq₁, hq₁d, hJq₁, hq₁le⟩ := hq1
  obtain ⟨Q₁, hQ₁, hQ₁c, hQ₁le⟩ := hdown (Pt' 0) q₁ (hPt 0).1 hq₁ (by rw [(hPt 0).2]; exact hq₁le)
  obtain ⟨Q, hQ, hQc, hQle⟩ := hdown (Pt' (Fin.last h)) q (hPt _).1 hq (by rw [(hPt _).2]; exact hqle)
  have hEp : ∀ i, (Ideal.map (Til.C O O' B) (Et i)).IsPrime ∧
      Ideal.comap (Til.ι O O' B) (Ideal.map (Til.C O O' B) (Et i)) = e i := fun i =>
    ⟨(hup _ (hEt i).1).1, (hup _ (hEt i).1).2.trans (hEt i).2.1⟩
  have hq' := (hup Q hQ).2.trans hQc
  have hfin := hmain (fun i => Ideal.map (Til.C O O' B) (Et i))
    (fun i => ⟨(hEp i).1, hns _ _ (hEp i).1 (hEp i).2 (he i).2.1, hle _ _ (hEt i).2.2.1,
      hle _ _ (hEt i).2.2.2⟩)
    ⟨Ideal.map (Til.C O O' B) Q₁, (hup _ hQ₁).1,
      hds _ (by rw [(hup _ hQ₁).2, hQ₁c]; exact hq₁d),
      by rw [Ideal.map_le_iff_le_comap, (hup _ hQ₁).2, hQ₁c]; exact hJq₁,
      hle _ _ hQ₁le⟩
    (Ideal.map (Til.C O O' B) Q) (hup _ hQ).1 (hle _ _ hQle)
    (by
      rcases hst with hd | hn
      · exact Or.inl (hds _ (by rw [hq']; exact hd))
      · exact Or.inr (hns _ _ (hup _ hQ).1 hq' hn))
  intro b hb
  rw [← hq']
  exact hfin (Ideal.mem_map_of_mem _ hb)

end UpperTheory.V.Pa
end

namespace UpperTheory.V.Pa

theorem raw : Raw := raw_main coreBC

end UpperTheory.V.Pa
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.TaylorWilesObstructionBound
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V.W UpperTheory.V.Pa.B2

namespace UpperTheory.V.Pa

private theorem mem_of_over {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    {B : ValuationSubring Ω} {w : Plc L} {v : Plc (Lp L)} (hw : IsPlaceOver B w) (hv : IsPlaceOver B v) (l : ℕ) :
    ((l : ℕ) : 𝓞 L) ∈ w.asIdeal ↔ ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal := by
  have h := hw ((l : ℕ) : 𝓞 L)
  have h' := hv ((l : ℕ) : 𝓞 (Lp L))
  have e : algebraMap L Ω (((l : ℕ) : 𝓞 L) : L) = (l : Ω) := by simp
  have e' : algebraMap (Lp L) Ω (((l : ℕ) : 𝓞 (Lp L)) : Lp L) = (l : Ω) := by simp
  rw [e] at h
  rw [e'] at h'
  exact h.symm.trans h'

theorem B2.cohAxAr (hP : CohP) (l : ℕ) [Fact l.Prime] (L Ω : Type) [Field L] [NumberField L] [IsCMField L] [Field Ω]
    [Algebra L Ω] [IsAlgClosure L Ω] (s : HidaSetting l L Ω) (V0 V : s.Lev) (O : Type) [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [IsCoef l O] [Algebra ℤ_[l] O] (n : ℕ) (r : Resid V0.frame O n) :
    CohAx (globOf r V) (Module.finrank ℚ (Lp L)) fun v => locDeg (s.w (Subtype.val v)) := by
  have hg := arGlob hP (Lp L) Ω l V.S' s.odd V.fin fun v hv => V.sub (Or.inl hv)
  have hl := fun v => arLoc hP L Ω l (s.A v) (s.w v) (s.hw v)
  exact
    { sum := arSum l L Ω s V0 V O n r
      fin := hg.1
      finV := fun v => (hl (Subtype.val v)).1
      finU := fun u => (hl (Subtype.val u)).1
      onto := hg.2
      ge := arGE hP l L Ω s V0 V O n r
      leV := fun v => (hl (Subtype.val v)).2.2.1 ((mem_of_over (s.hw _) (s.hA _) l).2 (Subtype.property v))
      leU := fun u => (hl (Subtype.val u)).2.2.2 fun h =>
        s.St_l _ (Subtype.property u) ((mem_of_over (s.hw _) (s.hA _) l).1 h)
      ur := arUr hP l L Ω s V0 V O n r
      ck := arCk hP l L Ω s V0 V O n r }

theorem b2Ar : TaylorWilesObstructionBound := fun hP l _ L Ω _ _ _ _ _ _ s V0 O _ _ _ _ _ n r T P x k al _ _ hPL hE =>
  obstructionBound_of_duality l _ _ T n x k al (Module.finrank ℚ (Lp L)) s.odd ⟨_, B2.cohAxAr hP l L Ω s V0 V0 O n r⟩
    (fun N => ⟨_, cohAxIso l _ _ _ (P.e N) _ _ (P.e_inj N) (B2.cohAxAr hP l L Ω s V0 (P.V N) O n r)⟩) hPL hE

end UpperTheory.V.Pa
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.ConjugationDescendsToSubring
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {R S : Type} [CommRing R] [CommRing S] {n a : ℕ}

private theorem ev_mul {Y Z : Matrix (Fin n) (Fin n) R} (hY : Y ∈ Ev R R n a) (hZ : Z ∈ Ev R R n a) :
    Y * Z ∈ Ev R R n a := by
  intro i j
  refine ⟨fun _ => trivial, fun e => ?_⟩
  rw [Submodule.mem_bot, Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : ((i : ℕ) < a ↔ (k : ℕ) < a)
  · have h0 : Z k j = 0 := (hZ k j).2 fun h' => e (h.trans h')
    rw [h0, mul_zero]
  · have h0 : Y i k = 0 := (hY i k).2 h
    rw [h0, zero_mul]

private theorem ev_tr {Y : Matrix (Fin n) (Fin n) R} (hY : Y ∈ Ev R R n a) : Yᵀ ∈ Ev R R n a :=
  fun i j => ⟨fun _ => trivial, fun e => (hY j i).2 fun h => e h.symm⟩

private theorem ev_map (f : R →+* S) {Z : Matrix (Fin n) (Fin n) R} (hZ : Z ∈ Ev R R n a) : Z.map f ∈ Ev S S n a := by
  intro i j
  refine ⟨fun _ => trivial, fun e => ?_⟩
  have h0 : Z i j = 0 := (hZ i j).2 e
  rw [Submodule.mem_bot, Matrix.map_apply, h0, map_zero]

private theorem span_conj {ι : Type} (r : ι → Matrix (Fin n) (Fin n) R) (T Ti : Matrix (Fin n) (Fin n) R)
    (h1 : Ti * T = 1) (hT : T ∈ Ev R R n a) (hTi : Ti ∈ Ev R R n a)
    (h : Submodule.span R (Set.range r) = Ev R R n a) :
    Submodule.span R (Set.range fun i => Ti * r i * T) = Ev R R n a := by
  let c : Matrix (Fin n) (Fin n) R →ₗ[R] Matrix (Fin n) (Fin n) R :=
    (LinearMap.mulRight R T).comp (LinearMap.mulLeft R Ti)
  have hc : ∀ Z, c Z = Ti * Z * T := fun Z => rfl
  have e : (Set.range fun i => Ti * r i * T) = c '' Set.range r := by
    rw [← Set.range_comp]; rfl
  rw [e, ← Submodule.map_span, h]
  apply le_antisymm
  · rintro _ ⟨Z, hZ, rfl⟩
    exact ev_mul (ev_mul hTi hZ) hT
  · intro Z hZ
    refine ⟨T * Z * Ti, ev_mul (ev_mul hT hZ) hTi, ?_⟩
    rw [hc]
    calc Ti * (T * Z * Ti) * T = (Ti * T) * Z * (Ti * T) := by simp only [Matrix.mul_assoc]
      _ = Z := by rw [h1, Matrix.one_mul, Matrix.mul_one]

private theorem form_conj (A B P T Ti : Matrix (Fin n) (Fin n) R) (u : R) (h1 : T * Ti = 1) (h : Aᵀ * P * B = u • P) :
    (Ti * A * T)ᵀ * (Tᵀ * P * T) * (Ti * B * T) = u • (Tᵀ * P * T) := by
  have h2 : Tiᵀ * Tᵀ = 1 := by rw [← transpose_mul, h1, transpose_one]
  calc (Ti * A * T)ᵀ * (Tᵀ * P * T) * (Ti * B * T)
      = Tᵀ * (Aᵀ * (Tiᵀ * Tᵀ) * P * (T * Ti) * B) * T := by simp only [transpose_mul, Matrix.mul_assoc]
    _ = u • (Tᵀ * P * T) := by
      rw [h1, h2, Matrix.mul_one, Matrix.mul_one, h, Matrix.mul_smul, Matrix.smul_mul]

private theorem form_map (f : R →+* S) (A B P : Matrix (Fin n) (Fin n) R) (u : R) (h : Aᵀ * P * B = u • P) :
    (A.map f)ᵀ * P.map f * B.map f = f u • P.map f := by
  rw [← transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h]
  ext i j
  simp

private theorem clear_den [IsDomain R] (M : Matrix (Fin n) (Fin n) (FractionRing R)) :
    ∃ d : R, d ≠ 0 ∧ ∃ P : Matrix (Fin n) (Fin n) R,
      P.map (algebraMap R (FractionRing R)) = algebraMap R (FractionRing R) d • M := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun p : Fin n × Fin n => M p.1 p.2)
  choose P hP using hd
  refine ⟨d, nonZeroDivisors.coe_ne_zero d, Matrix.of fun a b => P (a, b), ?_⟩
  ext a b
  simp only [Matrix.map_apply, Matrix.of_apply, Matrix.smul_apply, hP, Algebra.smul_def]
  rfl

private theorem bdd_den [IsDomain R] (M N : Matrix (Fin n) (Fin n) (FractionRing R)) :
    ∃ d : R, d ≠ 0 ∧ ∀ (Z : Matrix (Fin n) (Fin n) R) i i', ∃ y : R,
      algebraMap R (FractionRing R) d * (M * Z.map (algebraMap R (FractionRing R)) * N) i i' =
        algebraMap R (FractionRing R) y := by
  obtain ⟨d, hd, P, hP⟩ := clear_den M
  obtain ⟨d', hd', P', hP'⟩ := clear_den N
  refine ⟨d * d', mul_ne_zero hd hd', fun Z i i' => ⟨(P * Z * P') i i', ?_⟩⟩
  have : (P * Z * P').map (algebraMap R (FractionRing R)) =
      algebraMap R (FractionRing R) (d * d') • (M * Z.map (algebraMap R (FractionRing R)) * N) := by
    rw [Matrix.map_mul, Matrix.map_mul, hP, hP', Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, map_mul]
  exact (congrFun (congrFun this i) i').symm

private theorem frac_ext [IsDomain R] [IsDomain S] (j : R →+* S) (hj : Function.Injective j) :
    ∃ f : FractionRing R →+* FractionRing S, ∀ y, f (algebraMap _ _ y) = algebraMap _ _ (j y) := by
  have hi : Function.Injective ((algebraMap S (FractionRing S)).comp j) :=
    (IsFractionRing.injective S (FractionRing S)).comp hj
  exact ⟨IsFractionRing.lift (K := FractionRing R) hi, fun y => IsFractionRing.lift_algebraMap hi y⟩

private theorem chi_ofRep {G : Type} [Group G] (ρ : G →* Matrix (Fin n) (Fin n) R) (g : G) :
    (GDet.ofRep ρ).chi (MonoidAlgebra.single g 1) = (ρ g).charpoly := by
  change (GDet.repAlg ρ (Polynomial R) _).det = _
  rw [map_sub, MonoidAlgebra.mapRingHom_single, Matrix.charpoly]
  congr 1
  ext i j : 2
  by_cases h : i = j <;> simp [GDet.repAlg, Matrix.charmatrix, h, Matrix.one_apply, Matrix.diagonal_apply]

private theorem map_ofRep {G : Type} [Group G] (ρ : G →* Matrix (Fin n) (Fin n) R)
    (f : R →+* S) : (GDet.ofRep ρ).map f = GDet.ofRep (f.mapMatrix.toMonoidHom.comp ρ) := by
  refine GDet.ext fun C _ _ x => ?_
  letI : Algebra R C := ((algebraMap S C).comp f).toAlgebra
  change (GDet.repAlg ρ C x).det = (GDet.repAlg _ C x).det
  congr 2

private theorem det_of_charpoly {G : Type} [Group G] (ρ : G →* Matrix (Fin n) (Fin n) R)
    (ρ' : G →* Matrix (Fin n) (Fin n) S) (f : R →+* S) (h : ∀ g, (ρ' g).charpoly = (ρ g).charpoly.map f) :
    GDet.ofRep ρ' = (GDet.ofRep ρ).map f := by
  rw [map_ofRep]
  refine UpperTheory.V.CA.d_gext _ _ fun g i _ _ => ?_
  rw [GDet.lam, GDet.lam, chi_ofRep, chi_ofRep, h, ← Matrix.charpoly_map]
  rfl

end SlopeTestRemainingChoices

private theorem conj_surj {l : ℕ} [Fact l.Prime] (F : GFrame l) : Function.Surjective F.conj := by
  intro g
  refine ⟨F.conj g, Subtype.ext ?_⟩
  change F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = g
  have h : F.c⁻¹ * F.c⁻¹ = 1 := by rw [← _root_.mul_inv_rev, F.c_sq, inv_one]
  calc F.c * (F.c * g * F.c⁻¹) * F.c⁻¹ = (F.c * F.c) * g * (F.c⁻¹ * F.c⁻¹) := by simp only [mul_assoc]
    _ = g := by rw [h, F.c_sq, one_mul, mul_one]

private theorem norm_core {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    {n : ℕ} {r : Resid F O n} (x : Point r) (hl : l ≠ 2) (hn : 0 < n) (hx : x.TypeI ∨ x.TypeE) :
    ∃ (K' : Type) (_ : Field K') (_ : Finite K') (j : x.A →+* PowerSeries K')
      (f : x.Fr →+* FractionRing (PowerSeries K')) (a : ℕ) (T : GL (Fin n) (FractionRing (PowerSeries K')))
      (ρ' : F.G₀ →* GL (Fin n) (PowerSeries K')),
      Function.Injective j ∧ IsLocalHom j ∧ j.Finite ∧ (∀ y, f (algebraMap _ _ y) = algebraMap _ _ (j y)) ∧
      1 ≤ a ∧ a ≤ n ∧ (x.TypeI → a = n) ∧
      (∀ g, pushRep (algebraMap _ (FractionRing (PowerSeries K'))) ρ' g = T⁻¹ * pushRep f x.ρF g * T) ∧
      (T : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K')))ᵀ *
        ((x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr)).map f * T = 1 ∧
      (∀ g, mat ρ' g ∈ Ev (PowerSeries K') (PowerSeries K') n a) ∧
      Submodule.span (FractionRing (PowerSeries K'))
        ((fun g => (mat ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K')))) '' (F.G' : Set F.G₀)) =
        Ev (FractionRing (PowerSeries K')) (FractionRing (PowerSeries K')) n a := by
  obtain ⟨a, Q, ha1, han, haI, hev, hspan, hH⟩ := Det.blockForm x hn hx
  obtain ⟨j₁, i₁, l₁, fin₁, hX⟩ := Det.sqExt (K := x.K)
  obtain ⟨K', _, _, j₂, i₂, l₂, fin₂, hsq⟩ := Det.resSq (K := x.K)
  obtain ⟨f₁, hf₁⟩ := frac_ext j₁ i₁
  obtain ⟨f₂, hf₂⟩ := frac_ext j₂ i₂
  have hch : CharP x.K l := (Det.zlUniq l).1 ((algebraMap O x.K).comp (algebraMap ℤ_[l] O))
  have h2 : (2 : x.K) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : x.K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff x.K l] at h'
    exact hl ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h')
  obtain ⟨d, hd, hden⟩ := bdd_den (R := x.A) (Q : Matrix (Fin n) (Fin n) x.Fr) ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr)
  let rQ : F.G₀ →* GL (Fin n) x.Fr := (MulAut.conj Q).toMonoidHom.comp x.ρF
  have hrQ : ∀ g, mat rQ g = (Q : Matrix (Fin n) (Fin n) x.Fr) * (mat x.ρ g).map (algebraMap x.A x.Fr) *
      ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr) := fun g => rfl
  set PF := (x.P : Matrix (Fin n) (Fin n) x.A).map (algebraMap x.A x.Fr) with hPF
  have hPd : PF.det ≠ 0 := (Matrix.isUnits_det_units (GeneralLinearGroup.map (algebraMap x.A x.Fr) x.P)).ne_zero
  have hQd : ((Q⁻¹ : GL (Fin n) x.Fr) : Matrix (Fin n) (Fin n) x.Fr).det ≠ 0 := (Matrix.isUnits_det_units Q⁻¹).ne_zero
  have hPs : PFᵀ = PF := by rw [hPF, ← transpose_map, x.symm]
  obtain ⟨Q', ρ', e1, e2, e3, e4⟩ := Det.twoBlock a j₁ f₁ j₂ f₂ rQ _ F.conj
    (fun g => ((F.eps O x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A)) d h2 hf₁ hf₂ hX hsq hd
    (fun g i i' => hden (mat x.ρ g) i i')
    (by rw [transpose_mul, transpose_mul, transpose_transpose, hPs, Matrix.mul_assoc])
    (by rw [det_mul, det_mul, det_transpose]; exact mul_ne_zero (mul_ne_zero hQd hPd) hQd)
    (conj_surj F)
    (fun g => by
      rw [hrQ, hrQ]
      exact form_conj _ _ _ _ _ _ (Units.inv_mul Q) (form_map _ _ _ _ _ (x.form g)))
    han hev hH
  have e2' : ∀ g, pushRep (algebraMap _ (FractionRing (PowerSeries K'))) ρ' g =
      Q'⁻¹ * pushRep (f₂.comp f₁) rQ g * Q' := fun g => by
    rw [mul_assoc, e2, inv_mul_cancel_left]
  refine ⟨K', inferInstance, inferInstance, j₂.comp j₁, f₂.comp f₁, a,
    GeneralLinearGroup.map (f₂.comp f₁) Q⁻¹ * Q', ρ', i₂.comp i₁, inferInstance, fin₂.comp fin₁,
    fun y => by rw [RingHom.comp_apply, hf₁, hf₂, RingHom.comp_apply], ha1, han, haI, fun g => ?_, ?_, e4, ?_⟩
  · rw [e2']
    change Q'⁻¹ * GeneralLinearGroup.map (f₂.comp f₁) (Q * x.ρF g * Q⁻¹) * Q' =
      _ * GeneralLinearGroup.map (f₂.comp f₁) (x.ρF g) * _
    simp only [map_mul, map_inv, _root_.mul_inv_rev, inv_inv, mul_assoc]
  · rw [← e1, Units.val_mul, transpose_mul, Matrix.map_mul, Matrix.map_mul, transpose_map]
    simp only [Matrix.mul_assoc]
    rfl
  · have hi : ((Q'⁻¹ : GL (Fin n) (FractionRing (PowerSeries K'))) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) ∈
        Ev (FractionRing (PowerSeries K')) (FractionRing (PowerSeries K')) n a := by
      rw [Units.inv_eq_of_mul_eq_one_left e1]
      exact ev_mul (ev_tr e3) (ev_map _ hH)
    rw [Set.image_eq_range] at hspan ⊢
    have h3 := (Det.spanDesc (f₂.comp f₁) _ fun g : (F.G' : Set F.G₀) => hev g).1 hspan
    rw [← span_conj _ _ _ (Units.inv_mul Q') e3 hi h3]
    congr 2
    funext g
    exact congrArg Units.val (e2' g)

private theorem conjugation_descends_to_subring {E E' A ι : Type} [Field E] [Field E'] [CommRing A] {n : ℕ} (f : E →+* E') (φ : A →+* E')
    (hφ : Function.Injective φ) (T : GL (Fin n) E') (e : ι → E) (r : ι → Matrix (Fin n) (Fin n) E) (e' : ι → A)
    (r' : ι → Matrix (Fin n) (Fin n) A) (he : ∀ i, f (e i) = φ (e' i))
    (hm : ∀ i, (r' i).map φ = ((T⁻¹ : GL (Fin n) E') : Matrix (Fin n) (Fin n) E') * (r i).map f * T)
    (h : ∀ X : Matrix (Fin n) (Fin n) E, (∀ i, e i • (r i * X) = X * r i) → X = 0)
    (Z : Matrix (Fin n) (Fin n) A) (hZ : ∀ i, e' i • (r' i * Z) = Z * r' i) : Z = 0 := by
  have h0 := Det.solBase f e r h ((T : Matrix (Fin n) (Fin n) E') * Z.map φ * (T⁻¹ : GL (Fin n) E')) fun g => by
    have e1 := congrArg (fun Y => Matrix.map Y φ) (hZ g)
    simp only [Matrix.map_smul' _ _ _ (map_mul φ), Matrix.map_mul, hm, ← he] at e1
    have e2 := congrArg (fun Y => (T : Matrix (Fin n) (Fin n) E') * Y * (T⁻¹ : GL (Fin n) E')) e1
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv,
      Matrix.mul_one] at e2 ⊢
    exact e2
  apply Matrix.map_injective hφ
  have e2 := congrArg (fun Y => ((T⁻¹ : GL (Fin n) E') : Matrix (Fin n) (Fin n) E') * Y *
    (T : Matrix (Fin n) (Fin n) E')) h0
  simp only [Matrix.mul_assoc, Units.inv_mul_cancel_left, Units.inv_mul, Matrix.mul_one, Matrix.mul_zero,
    Matrix.zero_mul] at e2
  exact e2.trans (Matrix.map_zero _ (map_zero _)).symm

theorem UpperTheory.V.Pa.norm :
    UpperTheory.V.Pa.Norm := by
  intro l _ F O _ _ _ n r x I hl hn hI hx
  obtain ⟨h1, hT, h3, h4⟩ : x.N1 ∧ (x.TypeI ∨ x.TypeE) ∧ x.N3 ∧ x.N4 :=
    hx.elim (fun h => ⟨h.1, .inl h.2.1, h.2.2⟩) fun h => ⟨h.1, .inr h.2.1, h.2.2⟩
  obtain ⟨K', _, _, j, f, a, T, ρ', jinj, jloc, jfin, hf, ha1, han, haI, hρ, hP, hev, hspan⟩ := norm_core x hl hn hT
  letI : Algebra ℤ_[l] K' := ((PowerSeries.constantCoeff : PowerSeries K' →+* K').comp
    (j.comp ((algebraMap O x.A).comp (algebraMap ℤ_[l] O)))).toAlgebra
  have hch : CharP K' l := (Det.zlUniq l).1 (algebraMap ℤ_[l] K')
  have hl0 : (l : PowerSeries K') = 0 := by
    rw [← map_natCast (PowerSeries.C : K' →+* PowerSeries K'), CharP.cast_eq_zero, map_zero]
  have hl1 : (l : FractionRing (PowerSeries K')) = 0 := by
    rw [← map_natCast (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))), hl0, map_zero]
  have ι := IsFractionRing.injective (PowerSeries K') (FractionRing (PowerSeries K'))
  have ιM : Function.Injective fun Z : Matrix (Fin n) (Fin n) (PowerSeries K') =>
      Z.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) := Matrix.map_injective ι
  have he : ∀ g, F.eps ℤ_[l] (PowerSeries K') g = Units.map (j : x.A →* PowerSeries K') (F.eps O x.A g) := fun g =>
    Units.ext (DFunLike.congr_fun ((Det.zlUniq l).2 ((algebraMap ℤ_[l] (PowerSeries K')).comp (algebraMap ℤ_[l] ℤ_[l]))
      (j.comp ((algebraMap O x.A).comp (algebraMap ℤ_[l] O))) hl0).1 ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]))
  have heF : ∀ g, f ((F.eps O x.Fr g : x.Frˣ) : x.Fr) = algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))
      ((F.eps ℤ_[l] (PowerSeries K') g : (PowerSeries K')ˣ) : PowerSeries K') := fun g =>
    DFunLike.congr_fun ((Det.zlUniq l).2 (f.comp ((algebraMap O x.Fr).comp (algebraMap ℤ_[l] O)))
      ((algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp
        ((algebraMap ℤ_[l] (PowerSeries K')).comp (algebraMap ℤ_[l] ℤ_[l]))) hl1).1 ((F.ε g : ℤ_[l]ˣ) : ℤ_[l])
  have hm : ∀ g, (mat ρ' g).map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) =
      ((T⁻¹ : GL (Fin n) (FractionRing (PowerSeries K'))) : Matrix (Fin n) (Fin n) (FractionRing (PowerSeries K'))) *
        (mat x.ρF g).map f * T := fun g => congrArg Units.val (hρ g)
  have hF : ∀ g, mat x.ρF g = (mat x.ρ g).map (algebraMap x.A x.Fr) := fun g => rfl
  have hfc : f.comp (algebraMap x.A x.Fr) = (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))).comp j :=
    RingHom.ext hf
  have hcp : ∀ g, (mat ρ' g).charpoly.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) =
      (mat x.ρF g).charpoly.map f := fun g => by
    rw [← Matrix.charpoly_map, ← Matrix.charpoly_map, hm, Matrix.coe_units_inv, Matrix.charpoly_units_conj']
  have hu : Function.Injective (Units.map (j : x.A →* PowerSeries K')) := Units.map_injective jinj
  have hpush : ∀ {v} (χ χ' : F.Gv v →* x.Aˣ), pushCh j χ = pushCh j χ' → χ = χ' := fun χ χ' h =>
    MonoidHom.ext fun g => hu (DFunLike.congr_fun h g)
  have hfl : ∀ v, HasFlag (pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (ρ'.comp (F.φ v)))
      fun i => pushCh (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (pushCh j (x.ψ v i)) := by
    intro v
    obtain ⟨g₀, hg₀⟩ := x.flag v
    refine ⟨GeneralLinearGroup.map f g₀ * T, fun s => ?_⟩
    have e : GeneralLinearGroup.map f g₀ * T *
        pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) (ρ'.comp (F.φ v)) s *
        (GeneralLinearGroup.map f g₀ * T)⁻¹ = GeneralLinearGroup.map f (g₀ * x.ρF (F.φ v s) * g₀⁻¹) := by
      change _ * pushRep (algebraMap (PowerSeries K') (FractionRing (PowerSeries K'))) ρ' (F.φ v s) * _ = _
      rw [hρ, map_mul, map_mul, map_inv]
      change _ * (_ * GeneralLinearGroup.map f (x.ρF (F.φ v s)) * _) * _ = _
      group
    rw [e]
    refine ⟨fun i k h => ?_, fun i => ?_⟩
    · exact (congrArg f ((hg₀ s).1 i k h)).trans (map_zero f)
    · exact (congrArg f ((hg₀ s).2 i)).trans (hf _)
  choose w ty hw htri using fun v => Det.flagBasis (a := a) (ρ'.comp (F.φ v)) (fun i => pushCh j (x.ψ v i))
    (fun g => hev _) (fun i k h => by_contra fun hik => (h1 v).1 i k hik (hpush _ _ h)) (hfl v)
  have hcont : ∀ i k, AdicCont (maximalIdeal (PowerSeries K')) fun g => mat ρ' g i k := by
    refine Det.conjCont j (fun g => mat x.ρ g) T (fun g => mat ρ' g) jloc x.cont fun g => ?_
    rw [hm, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, hF, Matrix.map_map, ← hfc]
    rfl
  have hform : F.IsForm ℤ_[l] n ρ' 1 := by
    intro g
    apply ιM
    have e := form_conj _ _ _ _ _ _ (Units.mul_inv T) (form_map f _ _ _ _ (form_map (algebraMap x.A x.Fr) _ _ _ _ (x.form g)))
    rw [hP, ← hF, ← hF, ← hm, ← hm, hf] at e
    simp only [Units.val_one, Matrix.map_mul, transpose_map, Matrix.map_one _ (map_zero _) (map_one _)]
    rw [e, he, ← map_zpow (Units.map (j : x.A →* PowerSeries K')), Matrix.map_smul' _ _ _ (map_mul _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have hine : ∀ u, ∀ g ∈ I u, ρ' g = 1 := by
    intro u g hg
    apply Units.ext
    apply ιM
    have e := hm g
    rw [hF] at e
    have e1 : mat x.ρ g = 1 := congrArg Units.val (x.ine u g (hI u hg))
    rw [e1, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Units.inv_mul] at e
    exact e.trans (Matrix.map_one _ (map_zero _) (map_one _)).symm
  have hN3 : ∀ U : Set F.G₀, IsOpen U → (U ∩ (F.G' : Set F.G₀)).Nonempty → ∃ σ ∈ U ∩ (F.G' : Set F.G₀),
      ((mat ρ' σ).charpoly.map (algebraMap (PowerSeries K') (FractionRing (PowerSeries K')))).Separable :=
    fun U hU hne => (h3 U hU hne).imp fun σ hσ => ⟨hσ.1, by rw [hcp]; exact hσ.2.map⟩
  refine ⟨{
      K := K', ρ := ρ', cont := hcont, form := hform, a := a, a_pos := ha1, a_le := han, blk := hev,
      span := Det.spanInt _ _ hspan, ine := hine, ψ := fun v i => pushCh j (x.ψ v i),
      ψ_mu := fun v i g hg => ?_, w := w, ty := ty, w_blk := hw, tri := htri,
      N1 := fun v => ⟨fun i k hik h => (h1 v).1 i k hik (hpush _ _ h), fun i k hik h => ?_⟩ },
    j, jinj, jloc, jfin, ?_, fun _ _ => rfl, ?_, ?_, haI⟩
  · change Units.map (j : x.A →* PowerSeries K') (x.ψ v i g) = 1
    rw [Det.psiMu x v i g hg, map_one]
  · refine (h1 v).2 i k hik (MonoidHom.ext fun g => hu ?_)
    have e : Units.map (j : x.A →* PowerSeries K') (x.ψ v i g) =
        Units.map (j : x.A →* PowerSeries K') (x.ψ v k g) * F.eps ℤ_[l] (PowerSeries K') (F.φ v g) :=
      DFunLike.congr_fun h g
    rw [e, he, ← map_mul]
    rfl
  · refine det_of_charpoly (mat x.ρ) (mat ρ') j fun g => Polynomial.map_injective _ ι ?_
    rw [hcp, hF, Matrix.charpoly_map, Polynomial.map_map, Polynomial.map_map, hfc]
  · exact hN3
  · intro Z hZ
    exact conjugation_descends_to_subring f _ ι T (fun g : F.D0 => ((F.eps O x.Fr g : x.Frˣ) : x.Fr)) (fun g => mat x.ρF g)
      (fun g => ((F.eps ℤ_[l] (PowerSeries K') g : (PowerSeries K')ˣ) : PowerSeries K')) (fun g => mat ρ' g)
      (fun g => heF g) (fun g => hm g) (fun X hX => h4 X fun g hg => hX ⟨g, hg⟩) Z fun g => hZ g g.2
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.Choice
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.Detection
open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

theorem UpperTheory.V.Pa.detection :
    UpperTheory.V.Pa.Detection := by
  intro l _ F n x k hl hε S _ hS z hz h0
  refine UpperTheory.V.Pa.Det.detAsm k hl hε z hz fun σ hσ => ?_
  exact closure_minimal (t := {σ : F.G₀ | ell k x.A σ z = 0}) h0 (UpperTheory.V.Pa.Det.ellClosed k z hz) (hS hσ)
end

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem detects_mono {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x)
    {S T : Set F.G₀} (hST : S ⊆ T) (h : Detects k S) : Detects k T :=
  fun z hz hT => h z hz fun σ hσ => hT σ (hST hσ)

theorem UpperTheory.V.Pa.choice :
    UpperTheory.V.Pa.Choice := by
  intro l _ F n h x hl hphi hε hN3
  classical
  set S : Set F.G₀ := {σ | σ ∈ F.G' ∧ ∀ i : Fin (h + 1),
    (Polynomial.map (algebraMap (x i).A (FractionRing (x i).A)) ((mat (x i).ρ) σ).charpoly).Separable} with hS
  have hcl : (F.G' : Set F.G₀) ⊆ closure S := Det.omDense x hN3
  have hSG : S ⊆ F.G' := fun σ hσ => hσ.1
  have k0 : ∀ i, Kap (x i) := fun i => (Det.kapEx (x i) hphi).some
  have hdet : ∀ i, Detects (k0 i) S := fun i => detection l F n (x i) (k0 i) hl hε S hSG hcl
  choose Tf hTS hTd using fun i => Det.detFin (k0 i) S hphi (hdet i)
  set U : Finset F.G₀ := Finset.univ.biUnion Tf with hU
  let sg : Fin U.card → F.G₀ := fun a => (U.equivFin.symm a : F.G₀)
  have hsgU : ∀ a, sg a ∈ U := fun a => (U.equivFin.symm a).2
  have hsgS : ∀ a, sg a ∈ S := fun a => by
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.1 (hsgU a)
    exact hTS i hi
  have hTr : ∀ i, (Tf i : Set F.G₀) ⊆ Set.range sg := fun i y hy => by
    have hyU : y ∈ U := Finset.mem_biUnion.2 ⟨i, Finset.mem_univ _, hy⟩
    exact ⟨U.equivFin ⟨y, hyU⟩, by simp [sg]⟩
  have hdr : ∀ i, Detects (k0 i) (Set.range sg) := fun i => detects_mono (k0 i) (hTr i) (hTd i)
  choose d hd0 hd using fun i => Det.onePt (k0 i) sg (fun a => (hsgS a).2 i) (hdr i)
  have hD0 : (∏ i, d i) ≠ 0 := Finset.prod_ne_zero_iff.2 (fun i _ => hd0 i)
  choose x' j k' al hext hcard hdet' hal using
    fun i => hd i (∏ i, d i) (Finset.dvd_prod_of_mem d (Finset.mem_univ i)) hD0
  exact ⟨U.card, sg, x', j, k', al, fun a => (hsgS a).1, hext, fun i => by rw [hcard, hcard],
    hdet', fun i a => hal i a⟩
end

theorem UpperTheory.V.Pa.pFromAut : UpperTheory.V.Pa.PfromAut :=
  UpperTheory.V.Pa.pFromAut_of UpperTheory.V.Pa.norm UpperTheory.V.Pa.choice UpperTheory.V.Pa.arPl UpperTheory.V.Pa.b1Ar UpperTheory.V.Pa.b2Ar UpperTheory.V.Pa.raw
