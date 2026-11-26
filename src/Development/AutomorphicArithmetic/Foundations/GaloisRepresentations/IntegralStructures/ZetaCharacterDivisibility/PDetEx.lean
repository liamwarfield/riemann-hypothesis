module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPstAtOfIsSstAt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDetEx
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem algSat_prod_eq (a q : ℕ) (B : Multiset ℂˣ) (hB : B.card = a) :
    (algSat a q B).prod = ((B.prod : ℂˣ) : ℂ) * (q : ℂ) ^ (a.choose 2) := by
  have hq : (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) ^ a : ℝ) = (q : ℝ) ^ (a.choose 2) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg q), ← Real.rpow_natCast (q : ℝ) (a.choose 2),
      Nat.cast_choose_two]
    congr 1
    ring
  have hu : ((B.prod : ℂˣ) : ℂ) = (B.map fun α : ℂˣ => (α : ℂ)).prod :=
    map_multiset_prod (Units.coeHom ℂ) B
  have hm := Multiset.prod_map_mul (m := B) (f := fun _ : ℂˣ => (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ))
    (g := fun α : ℂˣ => (α : ℂ))
  have hl : algSat a q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((a : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
    unfold algSat
    change Multiset.map _ (Multiset.bind B fun α : ℂˣ => {(α : ℂ)}) = _
    rw [Multiset.bind_singleton, Multiset.map_map]
    rfl
  rw [hl, hm, Multiset.map_const', Multiset.prod_replicate, hB, hu, mul_comm]
  congr 1
  exact_mod_cast hq

theorem UpperTheory.Gal.Int.Div.detEx_of :
    CentU → DetEx := by
  classical
  intro hC E Ω _ _ _ _ _ _ l _ ι a ha U hU
  obtain ⟨χ, n, hχ, hval⟩ := hC E a ha U hU
  obtain ⟨L, hL, -⟩ := UpperTheory.Gal.TP.Sub.charEx E Ω l ι
  obtain ⟨ν, hν⟩ : ∃ ν : HChar E, ν.IsAbsPow ((-((a.choose 2 : ℕ) : ℤ) : ℤ) : ℝ) :=
    ⟨_, GlobalTheory.Mem.Chr.CharModel.absChar_isAbsPow _⟩
  have hνa : IsAlgPos ν (fun _ => -((a.choose 2 : ℕ) : ℤ)) :=
    AlgExpo.isAlgPos_of_expo E ν _ fun τ => by
      rw [(InfType.expo_of_infType E ν).2.1 _ hν τ]
      push_cast
      rfl
  have hA := GlobalTheory.GoodCsdTwist.isAlgPos_mul hχ hνa
  refine ⟨L (χ * ν) (n + fun _ => -((a.choose 2 : ℕ) : ℤ)), (hL _ _ hA).1, fun w hw B hB => ?_⟩
  obtain ⟨hu, hv⟩ := hval w hw B hB
  have hcl := (hL _ _ hA).2 w (GlobalTheory.GoodCsdTwist.unrAt_mul hu (hν.1 w))
  have hcard : B.card = a := by
    obtain ⟨σ, -, hs⟩ := hB
    exact hs.card
  have hvalue : (((χ * ν).val w : ℂˣ) : ℂ) = (algSat a (normV w) B).prod := by
    have e : (χ * ν).val w = χ.val w * ν.val w := rfl
    have h2 : ((ν.val w : ℂˣ) : ℂ) = ((normV w : ℕ) : ℂ) ^ (a.choose 2) := by
      rw [hν.2.1 w]
      have e2 : -(((((-((a.choose 2 : ℕ) : ℤ) : ℤ) : ℝ)) : ℂ)) = ((a.choose 2 : ℕ) : ℂ) := by
        push_cast
        ring
      rw [e2, Complex.cpow_natCast]
      simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [e, Units.val_mul, hv, h2, algSat_prod_eq a _ B hcard]
  rw [hvalue] at hcl
  exact ⟨_, hcl⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLocConj
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

private theorem exists_finExt_gl {l n : ℕ} [Fact l.Prime] (A : GL (Fin n) (Qbar l)) :
    ∃ K : FinExt l, ∀ i j, (A : Matrix (Fin n) (Fin n) (Qbar l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) i j ∈ K.1 := by
  let s : Set (Qbar l) := Set.range (fun p : Fin n × Fin n => (A : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2) ∪
    Set.range (fun p : Fin n × Fin n => ((A⁻¹ : GL (Fin n) (Qbar l)) : Matrix (Fin n) (Fin n) (Qbar l)) p.1 p.2)
  have hs : s.Finite := (Set.finite_range _).union (Set.finite_range _)
  haveI : Finite s := hs.to_subtype
  refine ⟨⟨IntermediateField.adjoin ℚ_[l] s,
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩, fun i j => ⟨?_, ?_⟩⟩
  · exact IntermediateField.subset_adjoin _ _ (Or.inl ⟨(i, j), rfl⟩)
  · exact IntermediateField.subset_adjoin _ _ (Or.inr ⟨(i, j), rfl⟩)

private theorem isdRAt_conj' {l : ℕ} [Fact l.Prime] {P : LocPrime l} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {Bw : LocBridge l E Ω Gw O} {m : ℕ} {r : ↥Gw →* GL (Fin m) (Qbar l)} (A : GL (Fin m) (Qbar l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Qbar l)) : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1)
    (hr : IsdRAt P Bw r) : IsdRAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) := by
  obtain ⟨LL', r₀, hm, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := GlobalTheory.ConjCrys.exists_conj_model A K hA hm
  obtain ⟨-, hdR2, -, -⟩ := GlobalTheory.Pst.local_ext P Bw h r₀
  exact ⟨_, _, hM, (GlobalTheory.ConjCrys.local_conj P Bw _ M _).2.1 (hdR2.2 hc)⟩

private theorem isdRAt_of_isCrysAt {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P)
    (hT : Nonempty (LocTied l P AI)) {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {Bw : LocBridge l E Ω Gw O} {a : ℕ} {r : ↥Gw →* GL (Fin a) (Qbar l)}
    (h : IsCrysAt P Bw r) : IsdRAt P Bw r := by
  obtain ⟨LL', r₀, hm, hc⟩ := h
  obtain ⟨T⟩ := hT
  refine ⟨LL', r₀, hm, ?_⟩
  have h1 := (GlobalTheory.Per.CrisDR.isDR_of_isCrys l P AI T Bw.Kw LL' _ _ hc).1
  unfold Formalism.BasicNotions.LocBridge.IsdRE
  unfold Formalism.MainNotions.N.IsDR at h1
  simpa only [Module.finrank_fin_fun] using h1

theorem UpperTheory.Gal.Int.Div.locConj_of :
    LocConj := by
  intro l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r r'
  have pst : ∀ {s : ↥(Dec (F := E) A) →* GL (Fin a) (Qbar l)}, IsCrysAt P Bw s → IsPstAt P Bw s := fun {s} h =>
    GlobalTheory.GalCut.IwaTwist.isPstAt_of_isSstAt P AI hT Bw s
      (GlobalTheory.CrysSst.isSstAt_of_isCrysAt l P AI hT E Ω _ O Bw a s h)
  refine ⟨fun h => ⟨isdRAt_of_isCrysAt P AI hT h, pst h⟩, fun hiso => ?_⟩
  obtain ⟨g, hg⟩ := id hiso
  obtain ⟨K, hK⟩ := exists_finExt_gl (g⁻¹)
  have e : r' = (MulAut.conj (g⁻¹)⁻¹).toMonoidHom.comp r := by
    ext1 x
    simp [hg, MulAut.conj_apply]
  have c' : IsCrysAt P Bw r → IsCrysAt P Bw r' := fun h => by
    rw [e]
    exact GlobalTheory.ConjCrys.isCrysAt_conj _ K hK h
  refine ⟨c', fun h => ?_, fun τ J h => ?_, fun ι w hw hj h => ?_⟩
  · rw [e]
    exact isdRAt_conj' _ K hK h
  · rw [e]
    exact GlobalTheory.ConjCrys.isJumpsAt_conj _ K hK h
  · exact GlobalTheory.ConjGal.wdAt_conj P ι Bw hw hj r r' g hg (pst h) (pst (c' h))
end
