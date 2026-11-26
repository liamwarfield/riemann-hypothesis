module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivUniq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PCharOfZeta
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PPhiSeed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDetEx
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PSameNormRing
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDenseUs
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSmall
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemClosureOfJumps
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.CocharacterLieDivisors.CocharacterLieAlgebra.PCocharToLie
public import Development.EtaleCohomology.DivisorCycles.GoalHolds

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PCoverIn
namespace UpperTheory.Gal.Int.Div

open GlobalTheory.BlockSum (blockRep)

theorem coverIn_of : CoverIn := by
  intro Γ k _ _ a d r ρ ⟨m, B, hB, hg⟩
  let n := Fintype.card (Σ _ : Fin m, Fin a)
  let e : (Σ _ : Fin m, Fin a) ≃ Fin n := Fintype.equivFin _
  let σ : Fin n ≃ Fin a × Fin m := e.symm.trans ((Equiv.sigmaEquivProd _ _).trans (Equiv.prodComm _ _))
  refine ⟨m, n, e, B.submatrix σ id, ?_, fun g => ?_⟩
  · have h := Matrix.rank_submatrix B σ (Equiv.refl _)
    simpa [hB] using h
  · have key : ((blockRep (a := fun _ : Fin m => a) e fun _ => r) g : Matrix (Fin n) (Fin n) k) =
        (Matrix.kronecker (r g : Matrix (Fin a) (Fin a) k) (1 : Matrix (Fin m) (Fin m) k)).submatrix σ σ := by
      rw [GlobalTheory.BlockSum.blockRep_val]
      ext i j
      obtain ⟨⟨x, u⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨y, v⟩, rfl⟩ := e.surjective j
      simp [σ, Matrix.blockDiagonal'_apply, Matrix.one_apply, Matrix.kroneckerMap_apply]
    rw [key]
    have h1 : B.submatrix σ id = B.submatrix σ (Equiv.refl _) := rfl
    have h2 : (ρ g : Matrix (Fin d) (Fin d) k) = (ρ g : Matrix (Fin d) (Fin d) k).submatrix (Equiv.refl _) (Equiv.refl _) := by simp
    rw [h1, Matrix.submatrix_mul_equiv, hg g, h2, Matrix.submatrix_mul_equiv]
    simp

end UpperTheory.Gal.Int.Div
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivDet
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

theorem UpperTheory.Gal.Int.Div.divDet_of :
    DenseUs → DetFrob → DivDet := by
  intro hD hF E Ω _ _ _ _ _ _ l _ ι a d hd U hU ψ hψ r hr g
  obtain ⟨hrc, -, V, X, hVo, hVd, hV⟩ := hr
  have hc1 : Continuous fun g : G E Ω => (r g : Matrix (Fin a) (Fin a) (Qbar l)).det :=
    Continuous.matrix_det (Units.continuous_val.comp hrc)
  have hc2 : Continuous fun g : G E Ω => ((ψ g : (Qbar l)ˣ) : Qbar l) :=
    Units.continuous_val.comp hψ.1
  have hdense := ((hD E Ω l a d hd U hU X).inter_of_isOpen_right hVd hVo).preimage
    (Homeomorph.inv (G E Ω)).isOpenMap
  refine congrFun (Continuous.ext_on hdense hc1 hc2 ?_) g
  rintro x ⟨⟨w, hwX, hUs, hl, ⟨B, hB⟩, A, hA, hFr⟩, hxV⟩
  have hx : (x⁻¹)⁻¹ = x := inv_inv x
  have hch := (hV w hwX hUs hl B hB A hA).2 x⁻¹ hFr hxV
  rw [hx] at hch
  have hψv := (hF E Ω l ι a U ψ hψ w hUs.1 hl B hB A hA).2 x⁻¹ hFr
  rw [hx] at hψv
  apply ι.injective
  rw [hψv]
  have hcard : (algSat a (normV w) B).card = a := by
    have h1 := congrArg Polynomial.natDegree hch
    rw [Polynomial.natDegree_map, Matrix.charpoly_natDegree_eq_dim,
      Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at h1
    simpa using h1.symm
  have h0 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 0) hch
  simp only [Polynomial.coeff_map] at h0
  have hdet : (r x : Matrix (Fin a) (Fin a) (Qbar l)).det =
      (-1) ^ a * (r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0 := by
    simpa using Matrix.det_eq_sign_charpoly_coeff (r x : Matrix (Fin a) (Fin a) (Qbar l))
  have h1 : ι ((r x : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.coeff 0) =
      (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0 := h0
  have h2 : (Multiset.map (fun b => Polynomial.X - C b) (algSat a (normV w) B)).prod.coeff 0 =
      (-1) ^ a * (algSat a (normV w) B).prod := by
    rw [Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_multiset_prod, Multiset.map_map]
    have : (Multiset.map (Polynomial.eval 0 ∘ fun b : ℂ => Polynomial.X - C b) (algSat a (normV w) B)) =
        Multiset.map Neg.neg (algSat a (normV w) B) :=
      Multiset.map_congr rfl fun b _ => by simp
    rw [this, Multiset.prod_map_neg, hcard]
  show ι (r x : Matrix (Fin a) (Fin a) (Qbar l)).det = _
  rw [hdet, map_mul, h1, h2, map_pow, map_neg, map_one, ← mul_assoc, ← mul_pow]
  simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PJumpSeed
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

theorem UpperTheory.Gal.Int.Div.jumpSeed_of :
    CoverIn → SSBlock → SubLoc → LocConj → JumpCard → JumpCondition := by
  intro h1 h2 h3 h4 h5 E Ω _ _ _ _ _ _ l _ ι a dd U r ρ hss hcov w hcrys hocc P AI hT A hA O _ _ _ Bw hj
  have hc := hcrys P AI hT A hA O Bw hj
  have hdr := ((h4 l P AI hT E Ω A O Bw a (r.comp (Dec (F := E) A).subtype) (r.comp (Dec (F := E) A).subtype)).1 hc).1
  refine ⟨hc, hdr, ?_⟩
  intro τ LL' τ' hτ lam J hw hJ
  obtain ⟨Jr, hJr, hcard⟩ := h5 l P AI hT E Ω A O Bw a _ hdr τ LL' τ' hτ
  obtain ⟨J', hJ', hsub⟩ := hocc P AI hT A hA O Bw hj τ LL' τ' hτ lam J hw hJ
  obtain ⟨m, n, e, hin⟩ := h1 _ _ a dd r ρ hcov
  have hR := h2 _ _ a m n e r hss
  have hcomp : (blockRep (a := fun _ : Fin m => a) e fun _ => r).comp (Dec (F := E) A).subtype =
      blockRep (a := fun _ : Fin m => a) e fun _ => r.comp (Dec (F := E) A).subtype := by
    ext g i j
    rfl
  have hjR : IsJumpsAt P Bw ((blockRep (a := fun _ : Fin m => a) e fun _ => r).comp (Dec (F := E) A).subtype) τ
      (∑ _ : Fin m, Jr) := by
    rw [hcomp]
    exact GlobalTheory.BlockSum.isJumpsAt_blockRep P Bw e hτ fun _ => hJr
  have hle : J' ≤ ∑ _ : Fin m, Jr :=
    (h3 E Ω l dd n ρ _ hR hin ι w P AI hT A hA O Bw hj).2 τ _ _ hjR hJ'
  have hJeq : J = (wtJumps lam).val :=
    Multiset.map_injective Int.cast_injective (hJ.trans (wtJumps_val lam).symm)
  have hnd : J.Nodup := hJeq ▸ (wtJumps lam).nodup
  have hJc : J.card = a := by rw [hJeq]; exact card_wtJumps lam
  have hss' : J ⊆ Jr := fun j hjJ => by
    obtain ⟨_, -, hj'⟩ := Multiset.mem_sum.1 (Multiset.mem_of_le hle (hsub j hjJ))
    exact hj'
  have hJJ : J = Jr :=
    Multiset.eq_of_le_of_card_le ((Multiset.le_iff_subset hnd).2 hss') (by rw [hcard, hJc])
  rw [hJJ]
  exact hJr
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLocSum
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

namespace UpperTheory.Gal.Int.Div.LocalSums

section Alg

variable {Γ : Type} [Group Γ] {k k' : Type} [CommRing k] [CommRing k']

private theorem sumRep_ll {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  change Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0 (s g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm (Fin.castAdd b i)) (finSumFinEquiv.symm (Fin.castAdd b j)) = _
  simp

private theorem sumRep_rr {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) (i j : Fin b) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.natAdd a i) (Fin.natAdd a j) =
      (s g : Matrix (Fin b) (Fin b) k) i j := by
  change Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0 (s g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm (Fin.natAdd a i)) (finSumFinEquiv.symm (Fin.natAdd a j)) = _
  simp

private theorem map_sum' {a b : ℕ} (f : k →+* k') (r₁ : Γ →* GL (Fin a) k) (r₂ : Γ →* GL (Fin b) k) :
    mapRep f (sumRep r₁ r₂) = sumRep (mapRep f r₁) (mapRep f r₂) := by
  ext g i j
  change f (Matrix.fromBlocks (r₁ g : Matrix (Fin a) (Fin a) k) 0 0 (r₂ g : Matrix (Fin b) (Fin b) k)
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)) =
    Matrix.fromBlocks (mapRep f r₁ g : Matrix (Fin a) (Fin a) k') 0 0 (mapRep f r₂ g : Matrix (Fin b) (Fin b) k')
      (finSumFinEquiv.symm i) (finSumFinEquiv.symm j)
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> simp [mapRep]

private theorem descend {n : ℕ} (f : k →+* k') (hf : Function.Injective f) (r : Γ →* GL (Fin n) k')
    (A : Γ → Matrix (Fin n) (Fin n) k) (hA : ∀ g i j, f (A g i j) = (r g : Matrix (Fin n) (Fin n) k') i j) :
    ∃ r₁ : Γ →* GL (Fin n) k, mapRep f r₁ = r := by
  let M : Γ →* Matrix (Fin n) (Fin n) k :=
    { toFun := A
      map_one' := by
        ext i j
        apply hf
        rw [hA]
        simp [Matrix.one_apply, apply_ite f]
      map_mul' := fun g h => by
        ext i j
        apply hf
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hA, Matrix.mul_apply, map_sum]
        simp only [map_mul, hA, Units.val_mul, Matrix.mul_apply] }
  refine ⟨M.toHomUnits, ?_⟩
  ext g i j
  simpa [mapRep, M] using hA g i j

end Alg

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {Bw : LocBridge l E Ω Gw O} {a b : ℕ}
  {r : ↥Gw →* GL (Fin a) (Om l)} {s : ↥Gw →* GL (Fin b) (Om l)}

private theorem model_split {L : FinExt l} {ρ : ↥Gw →* GL (Fin (a + b)) ↥L.1}
    (h : IsModel Bw (sumRep r s) L ρ) :
    ∃ (r₁ : ↥Gw →* GL (Fin a) ↥L.1) (s₁ : ↥Gw →* GL (Fin b) ↥L.1),
      IsModel Bw r L r₁ ∧ IsModel Bw s L s₁ ∧ IsModel Bw (sumRep r s) L (sumRep r₁ s₁) := by
  have hf : Function.Injective (algebraMap ↥L.1 (Om l)) := (algebraMap ↥L.1 (Om l)).injective
  have e : ∀ g i j, algebraMap ↥L.1 (Om l) ((ρ g : Matrix _ _ ↥L.1) i j) =
      (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) (Om l)) i j := fun g i j => by
    rw [← h.2]
    simp [mapRep]
  obtain ⟨r₁, hr⟩ := descend (algebraMap ↥L.1 (Om l)) hf r
    (fun g i j => (ρ g : Matrix _ _ ↥L.1) (Fin.castAdd b i) (Fin.castAdd b j))
    (fun g i j => by rw [e, sumRep_ll])
  obtain ⟨s₁, hs⟩ := descend (algebraMap ↥L.1 (Om l)) hf s
    (fun g i j => (ρ g : Matrix _ _ ↥L.1) (Fin.natAdd a i) (Fin.natAdd a j))
    (fun g i j => by rw [e, sumRep_rr])
  exact ⟨r₁, s₁, ⟨h.1, hr⟩, ⟨h.1, hs⟩, ⟨h.1, by rw [map_sum', hr, hs]⟩⟩

end UpperTheory.Gal.Int.Div.LocalSums

open UpperTheory.Gal.Int.Div.LocalSums in
theorem UpperTheory.Gal.Int.Div.locSum_of :
    LocSum := by
  intro l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a b r s
  refine ⟨fun hc => ?_, fun τ J J' hJ hJ' => ?_⟩
  · obtain ⟨L, ρ, hm, -⟩ := id hc
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    obtain ⟨T⟩ := id tied
    have he : ∀ g v, GlobalTheory.DirectSumLocal.splitEquiv (↥L.1) a b (Bw.repE L (sumRep r₁ s₁) g v) =
        (Bw.repE L r₁ g (GlobalTheory.DirectSumLocal.splitEquiv (↥L.1) a b v).1,
          Bw.repE L s₁ g (GlobalTheory.DirectSumLocal.splitEquiv (↥L.1) a b v).2) := by
      intro g v
      exact GlobalTheory.DirectSumLocal.splitEquiv_sumRep r₁ s₁ _ v
    obtain ⟨-, h2, -⟩ := GlobalTheory.Per.DirectSumHT.directSum_hodgeTate l P AI T Bw.Kw L (Fin (a + b) → ↥L.1)
      (Bw.repE L (sumRep r₁ s₁)) (Fin a → ↥L.1) (Bw.repE L r₁) (Fin b → ↥L.1)
      (Bw.repE L s₁) (GlobalTheory.DirectSumLocal.splitEquiv (↥L.1) a b) he
    have hc' : Bw.IsCrysE P L (sumRep r₁ s₁) := (m.isCrysAt_iff P).1 hc
    have h3 := h2.1 hc'
    exact ⟨(m₁.isCrysAt_iff P).2 h3.1, (m₂.isCrysAt_iff P).2 h3.2⟩
  · obtain ⟨L, ρ, hm, hd, τ', t, -⟩ := id hJ
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    have S := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l P AI tied E Ω _ O Bw L a b r₁ s₁
    have hds := S.1.1 ((m.isdRAt_iff P).1 ⟨L, ρ, hm, hd⟩)
    obtain ⟨K, hK⟩ := m₂.exists_isJumpsAt P hds.2 t
    rw [Multiset.le_iff_count]
    intro n
    have c := hJ.count_eq P m t n
    have c₁ := hJ'.count_eq P m₁ t n
    have c₂ := hK.count_eq P m₂ t n
    rw [S.2] at c
    omega
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PInFacts
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

private theorem pow_intertwine {k : Type} [Field k] {a d : ℕ} {P : Matrix (Fin d) (Fin d) k}
    {R : Matrix (Fin a) (Fin a) k} {A : Matrix (Fin d) (Fin a) k} (h : P * A = A * R) (n : ℕ) :
    P ^ n * A = A * R ^ n := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, Matrix.mul_assoc, h, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, pow_succ]

private theorem aeval_intertwine {k : Type} [Field k] {a d : ℕ} {P : Matrix (Fin d) (Fin d) k}
    {R : Matrix (Fin a) (Fin a) k} {A : Matrix (Fin d) (Fin a) k} (h : P * A = A * R) (Q : k[X]) :
    aeval P Q * A = A * aeval R Q := by
  induction Q using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add (f := _), map_add (f := _), Matrix.add_mul, Matrix.mul_add, hp, hq]
  | monomial n c =>
    rw [aeval_monomial, aeval_monomial, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one]
    simp only [smul_mul_assoc, one_mul, Matrix.smul_mul, Matrix.mul_smul, pow_intertwine h n]

private theorem left_cancel {k : Type} [Field k] {a d : ℕ} {A : Matrix (Fin d) (Fin a) k} (hA : A.rank = a)
    {M N : Matrix (Fin a) (Fin a) k} (h : A * M = A * N) : M = N := by
  have hker : LinearMap.ker A.mulVecLin = ⊥ := by
    have h1 := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
    have h2 : Module.finrank k (LinearMap.range A.mulVecLin) = a := hA
    rw [h2, Module.finrank_fin_fun] at h1
    exact Submodule.finrank_eq_zero.mp (by omega)
  have hinj := LinearMap.ker_eq_bot.mp hker
  ext i j
  have hv : M.mulVec (Pi.single j 1) = N.mulVec (Pi.single j 1) := by
    apply hinj
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, h]
  simpa using congrFun hv i

theorem UpperTheory.Gal.Int.Div.inFacts_of :
    InFacts := by
  intro Γ k _ _ a d r ρ ⟨A, hA, hc⟩
  refine ⟨hA ▸ A.rank_le_height, fun g hg => ?_, fun g Q hQ => ?_⟩
  · have h := hc g
    rw [hg] at h
    apply Units.ext
    apply left_cancel hA
    simpa using h.symm
  · apply left_cancel hA
    rw [← aeval_intertwine (hc g) Q, hQ]
    simp
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSepPin
open Polynomial

namespace UpperTheory.Gal.Int.Div

theorem sepPin_of : SepPin := by
  intro k _ a M Q hQm hQd hQ hsep
  have key : M.charpoly ∣ Q := by
    rw [← Polynomial.map_dvd_map (algebraMap k (AlgebraicClosure k))
      (algebraMap k (AlgebraicClosure k)).injective M.charpoly_monic]
    rw [← M.charpoly_map]
    have hQ' : aeval (M.map (algebraMap k (AlgebraicClosure k))) Q = 0 := by
      have e : M.map (algebraMap k (AlgebraicClosure k)) =
          (Algebra.ofId k (AlgebraicClosure k)).mapMatrix M := rfl
      rw [e, Polynomial.aeval_algHom_apply, hQ, map_zero]
    have hf : aeval (Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k)))) Q = 0 := by
      have e : Matrix.toLin' (M.map (algebraMap k (AlgebraicClosure k))) =
          Matrix.toLinAlgEquiv' (M.map (algebraMap k (AlgebraicClosure k))) := rfl
      rw [e, ← Polynomial.aeval_map_algebraMap (AlgebraicClosure k), Polynomial.aeval_algHom_apply,
        Polynomial.aeval_map_algebraMap, hQ', map_zero]
    have hmon := (M.map (algebraMap k (AlgebraicClosure k))).charpoly_monic
    refine dvd_trans ?_ (prod_multiset_X_sub_C_dvd (Q.map (algebraMap k (AlgebraicClosure k))))
    rw [(IsAlgClosed.splits (M.map (algebraMap k (AlgebraicClosure k))).charpoly).eq_prod_roots_of_monic hmon]
    apply Multiset.prod_dvd_prod_of_le
    apply Multiset.map_le_map
    have hnd : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.roots.Nodup := by
      rw [M.charpoly_map]
      exact nodup_roots hsep.map
    rw [Multiset.le_iff_subset hnd]
    intro μ hμ
    have hroot : (M.map (algebraMap k (AlgebraicClosure k))).charpoly.IsRoot μ :=
      (mem_roots hmon.ne_zero).mp hμ
    rw [← Matrix.charpoly_toLin'] at hroot
    have he := (Module.End.hasEigenvalue_iff_isRoot_charpoly _ μ).mpr hroot
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hv' := Module.End.aeval_apply_of_hasEigenvector (p := Q.map (algebraMap k (AlgebraicClosure k))) hv
    rw [Polynomial.aeval_map_algebraMap, hf, LinearMap.zero_apply] at hv'
    have h0 : (Q.map (algebraMap k (AlgebraicClosure k))).eval μ = 0 :=
      (smul_eq_zero.mp hv'.symm).resolve_right hv.2
    rw [mem_roots (Polynomial.map_monic_ne_zero hQm)]
    exact h0
  exact (eq_of_monic_of_dvd_of_natDegree_le M.charpoly_monic hQm key
    (by rw [hQd, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin])).symm

end UpperTheory.Gal.Int.Div
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.HtCocharOf
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

namespace UpperTheory.Gal.Int.Div

theorem htCochar_of (hJ : JumpCard) : PositivityTheory.AutomorphicGaloisHodgeTate.Div.HTCochar := by
  intro E Ω _ _ _ _ _ l _ N n V _ ⟨P, AI, hT, w, A, _, _, O, i1, i2, i3, Bw, _, τ, J, hj, ks, k1, k2, k3⟩
  have hc : J.card = N := by
    obtain ⟨L, r', hm, hd, τ', ht, hcnt⟩ := id hj
    obtain ⟨J', h1, h2⟩ := hJ l P AI hT E Ω A O Bw N _ ⟨L, r', hm, hd⟩ τ L τ' ht
    rw [← h2]
    congr 1
    ext a
    exact_mod_cast (hcnt a).trans (h1.count_eq P hm ht a).symm
  obtain ⟨T⟩ := hT
  obtain ⟨Pm, k, hk, hf⟩ := GlobalTheory.HodgeTateCochar.mem_closure_of_jumps l P AI T Bw _ τ J hj hc
  refine ⟨ℂ_[l], inferInstance, inferInstance, inferInstance, Pm.val, k, ks, (Matrix.isUnit_iff_isUnit_det _).1 Pm.isUnit, k1, k3,
    fun i => ?_, fun f h0 t ht => ?_⟩
  · have := k2 i
    rw [← hk] at this
    obtain ⟨j, -, e⟩ := Multiset.mem_map.1 this
    exact ⟨j, e⟩
  · rw [← Matrix.coe_units_inv]
    refine hf Bw.Kw le_rfl _ (fun g _ => ?_) t ht
    have := congrArg (algebraMap (Qbar l) ℂ_[l]) (h0 g)
    rw [map_zero, MvPolynomial.eval, MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_comp_left] at this
    rw [MvPolynomial.eval_map]
    exact this

theorem senWLac_of (hJ : JumpCard) : SenWLac := PositivityTheory.AutomorphicGaloisHodgeTate.Div.cocharToLie_holds (htCochar_of hJ)

end UpperTheory.Gal.Int.Div
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivOne
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

private theorem satPol_facts {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (s : Multiset ℂ) :
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).Monic ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).natDegree = Multiset.card s ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).coeff 0 = ι.symm ((-1) ^ Multiset.card s * s.prod) ∧
    (((s.map fun b => X - C b).prod).map ι.symm.toRingHom).map ι.toRingHom = (s.map fun b => X - C b).prod := by
  refine ⟨(monic_multiset_prod_of_monic _ _ fun b _ => monic_X_sub_C b).map _, ?_, ?_, ?_⟩
  · rw [natDegree_map, natDegree_multiset_prod_X_sub_C_eq_card]
  · rw [coeff_map, coeff_zero_eq_eval_zero, eval_multiset_prod, Multiset.map_map]
    have : (s.map ((fun p : ℂ[X] => eval 0 p) ∘ fun b => X - C b)) = s.map Neg.neg := by
      refine Multiset.map_congr rfl fun b _ => ?_
      simp
    rw [this, Multiset.prod_map_neg]
    rfl
  · rw [Polynomial.map_map]
    have : ι.toRingHom.comp ι.symm.toRingHom = RingHom.id ℂ := by
      ext z
      simp
    rw [this, Polynomial.map_id]

theorem UpperTheory.Gal.Int.Div.divOne_of :
    DivSet → DenseUs → DetFrob → InFacts → SepPin → DivOne := by
  intro hDiv hDense hDet hIn hSep E Ω _ _ _ _ _ _ l _ ι a d hd U hU ψ hψ dd ρ hV
  obtain ⟨hc, hs, ⟨X, hX⟩, hr⟩ := hV
  have hcard : ∀ (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ), SatU U w B →
      Multiset.card (algSat a (normV w) B) = a := by
    rintro w B ⟨σ, -, hB⟩
    have h : Multiset.card (algSat a (normV w) B) = Multiset.card B := by
      unfold algSat
      simp
    rw [h]
    exact GlobalTheory.LFun.HasSatGL.card hB
  have hD := (hDense E Ω l a d hd U hU X).preimage (Homeomorph.inv (G E Ω)).isOpenMap
  obtain ⟨r, hrc, hrs, hin, hco, hop, hde⟩ := hDiv E Ω l a dd ρ hc hs hr ψ hψ.1 (hD.mono (by
    rintro g ⟨w, hw, hu, hl, ⟨B, hB⟩, A, hA, hf⟩
    have hf' : IsFrob A (normV w) g⁻¹ := hf
    obtain ⟨q1, q2, q3, -⟩ := satPol_facts ι (algSat a (normV w) B)
    rw [hcard w B hB] at q2 q3
    refine ⟨_, q1, q2, ?_, ?_⟩
    · have := (hX w hw hu hl B hB A hA).2 g⁻¹ hf'
      rwa [inv_inv] at this
    · have h := (hDet E Ω l ι a U ψ hψ w hu.1 hl B hB A hA).2 g⁻¹ hf'
      rw [inv_inv] at h
      rw [q3]
      apply ι.injective
      have h1 : ((-1 : ℂ) ^ a) * (-1) ^ a = 1 := by
        rw [← mul_pow]; simp
      simp only [map_mul, map_pow, map_neg, map_one, RingEquiv.apply_symm_apply]
      rw [h, ← mul_assoc, h1, one_mul]))
  refine ⟨r, ⟨hrc, hrs, (fun g : G E Ω => g⁻¹) ⁻¹' {g | (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.Separable}, X,
    hop.preimage continuous_inv, hde.preimage (Homeomorph.inv (G E Ω)).isOpenMap, ?_⟩, hin, hco⟩
  intro w hw hu hl B hB A hA
  have hE := hX w hw hu hl B hB A hA
  have hF := hIn (G E Ω) (Qbar l) a dd r ρ hin
  refine ⟨fun s hs' => hF.2.1 s (hE.1 s hs'), fun s hf hsV => ?_⟩
  obtain ⟨q1, q2, -, q4⟩ := satPol_facts ι (algSat a (normV w) B)
  rw [hcard w B hB] at q2
  rw [hSep (Qbar l) a _ _ q1 q2 (hF.2.2 s⁻¹ _ (hE.2 s hf)) hsV, q4]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PGenPin
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

private theorem aeval_matrix_map {K L : Type} [Field K] [Field L] (f : K →+* L) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) K) (Q : K[X]) :
    aeval (M.map f) (Q.map f) = (aeval M Q).map f := by
  simp only [aeval_def, eval₂_map]
  have h := hom_eval₂ Q (algebraMap K (Matrix (Fin n) (Fin n) K)) f.mapMatrix M
  rw [RingHom.mapMatrix_apply, RingHom.mapMatrix_apply] at h
  rw [h]
  congr 1
  ext a : 1
  simp [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_map]

theorem UpperTheory.Gal.Int.Div.genPin_of :
    GenPin := by
  intro l _ ι a M s hcard hgen hann hdet
  set P := (Multiset.map (fun b ↦ X - C b) s).prod with hPdef
  have hround : map ι.toRingHom (map ι.symm.toRingHom P) = P := by
    rw [Polynomial.map_map]
    convert Polynomial.map_id
    ext z
    simp
  have hann2 : aeval (M.map ι.toRingHom) (UpperTheory.Gal.crystallineComparison.rootPol s) = 0 := by
    show aeval (M.map ι.toRingHom) P = 0
    rw [← hround, aeval_matrix_map, hann]
    simp
  have hdet2 : (M.map ι.toRingHom).det = s.prod := by
    have hd := RingHom.map_det ι.toRingHom M
    rw [RingHom.mapMatrix_apply] at hd
    rw [← hd]
    exact hdet
  rw [← Matrix.charpoly_map]
  exact UpperTheory.Gal.crystallineComparison.charAnn_of ℂ a _ s hcard hgen hann2 hdet2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PJumpCard
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

theorem UpperTheory.Gal.Int.Div.jumpCard_of :
    JumpCard := by
  intro l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a r hdR τ LL' τ' hτ
  obtain ⟨T⟩ := id tied
  obtain ⟨L₀, r₀, hm, hd⟩ := hdR
  have l₁ : L₀.1 ≤ (supExt L₀ LL').1 := le_sup_left
  have l₂ : LL'.1 ≤ (supExt L₀ LL').1 := le_sup_right
  have hm' := hm.enlarge l₁
  have hd' := (local_ext P Bw l₁ r₀).2.1.2 hd
  have hτ' : IsInduced Bw τ ((IntermediateField.inclusion l₂).comp τ') := fun x => hτ x
  have hdr' : IsDR (P.PD Bw.Kw) (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀)) := by
    rw [IsDR, Module.finrank_fin_fun]
    exact hd'
  obtain ⟨hfin, -, hrk⟩ := (GlobalTheory.Per.Components.components_finrank l P AI T _ (supExt L₀ LL') _
    (Bw.repE (supExt L₀ LL') (mapRep (IntermediateField.inclusion l₁).toRingHom r₀))).1
      ((IntermediateField.inclusion l₂).comp τ')
  obtain ⟨J', h1, h2⟩ := @GlobalTheory.HtCardProof.exists_count _ _ _ _ _ T _ _
    ((mapRep (IntermediateField.inclusion l₁).toRingHom r₀).comp Bw.e.symm.toMonoidHom)
    ((IntermediateField.inclusion l₂).comp τ') hfin
  exact ⟨J', ⟨_, _, hm', hd', _, hτ', h2⟩, h1.trans ((hrk hdr').trans (Module.finrank_fin_fun _))⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PDivSet
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

theorem UpperTheory.Gal.Int.Div.divSet_of :
    DivWCoreLac → SenWLac → LacBridge → InFacts → DivSet := by
  intro hcore hsen hlac _ E Ω _ _ _ _ _ l _ a dd ρ hρ hss hHT ψ hψ hD
  classical
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : IsGalois E Ω := {}
  have : CompactSpace (G E Ω) := inferInstanceAs (CompactSpace (Ω ≃ₐ[E] Ω))
  obtain ⟨K', _, _, _, X, hX, hroots⟩ := hsen E Ω l dd a ρ hρ (hlac E Ω l a dd ρ hHT)
  let T : G E Ω → (Qbar l)[X] → Prop := fun g Q => Q.Monic ∧ Q.natDegree = a ∧
    aeval (ρ g : Matrix (Fin dd) (Fin dd) (Qbar l)) Q = 0 ∧
      ((ψ g : (Qbar l)ˣ) : Qbar l) = (-1) ^ a * Q.coeff 0
  let P : G E Ω → (Qbar l)[X] := fun g => if h : ∃ Q, T g Q then h.choose else 1
  have hP : ∀ s ∈ {g : G E Ω | ∃ Q, T g Q}, T s (P s) := by
    intro s hs
    have e : P s = (show ∃ Q, T s Q from hs).choose := dif_pos hs
    rw [e]
    exact (show ∃ Q, T s Q from hs).choose_spec
  have hss' : IsSSMat ρ := by
    intro W hW
    obtain ⟨W', h1, h2⟩ := hss W hW
    exact ⟨W', h2, h1⟩
  obtain ⟨r, hrc, hrss, hin, hco, -, -, -, hopen, hdense, -, -⟩ :=
    hcore (G E Ω) (Qbar l) K' dd a ρ (Units.continuous_val.comp hρ) hss'
      {g : G E Ω | ∃ Q, T g Q} hD P
      (fun s hs => ⟨(hP s hs).1, (hP s hs).2.1⟩) (fun s hs => (hP s hs).2.2.1)
      X hX hroots ψ (Units.continuous_val.comp hψ) (fun s hs => (hP s hs).2.2.2)
  refine ⟨r, ?_, ?_, hin, hco, hopen, hdense⟩
  · refine Units.continuous_iff.mpr ⟨hrc, ?_⟩
    simp only [← map_inv]
    exact hrc.comp continuous_inv
  · intro W hW
    obtain ⟨W', h1, h2⟩ := hrss W hW
    exact ⟨W', h2, h1⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSSBlock
open Formalism.MainNotions.N
open GlobalTheory.BlockSum (blockRep vecComp vecComp_mulVec)

namespace UpperTheory.Gal.Int.Div

section Bridge

variable {Γ k : Type} [Group Γ] [Field k] {n : ℕ}

private def colRep (ρ : Γ →* GL (Fin n) k) : Representation k Γ (Fin n → k) where
  toFun g := Matrix.mulVecLin (ρ g).val
  map_one' := by ext; simp
  map_mul' g h := by ext; simp [Matrix.mulVecLin_mul]

private theorem colRep_apply (ρ : Γ →* GL (Fin n) k) (g : Γ) (v : Fin n → k) :
    colRep ρ g v = (ρ g).val.mulVec v := rfl

private theorem isSSRep_iff (ρ : Γ →* GL (Fin n) k) : IsSSRep ρ ↔ (colRep ρ).IsSemisimpleRepresentation := by
  constructor
  · intro h
    refine ⟨fun a => ?_⟩
    obtain ⟨W', hW', hc⟩ := h a.toSubmodule fun g v hv => a.apply_mem_toSubmodule g hv
    exact ⟨⟨W', fun g v hv => hW' g v hv⟩,
      disjoint_iff.2 (Subrepresentation.toSubmodule_injective hc.inf_eq_bot),
      codisjoint_iff.2 (Subrepresentation.toSubmodule_injective hc.sup_eq_top)⟩
  · intro h W hW
    obtain ⟨b, hb⟩ := exists_isCompl (⟨W, fun g v hv => hW g v hv⟩ : Subrepresentation (colRep ρ))
    exact ⟨b.toSubmodule, fun g v hv => b.apply_mem_toSubmodule g hv,
      disjoint_iff.2 (congrArg Subrepresentation.toSubmodule hb.inf_eq_bot),
      codisjoint_iff.2 (congrArg Subrepresentation.toSubmodule hb.sup_eq_top)⟩

end Bridge

theorem sSBlock_of : SSBlock := by
  intro Γ k _ _ a m n e r hr
  rw [isSSRep_iff, Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule]
  haveI := (Representation.isSemisimpleRepresentation_iff_isSemisimpleModule_asModule _).1
    ((isSSRep_iff r).1 hr)
  set R := blockRep (a := fun _ : Fin m => a) e fun _ => r
  let L : (colRep R).asModule ≃ₗ[k] (Fin m → (colRep r).asModule) :=
    (colRep R).asModuleEquiv.trans ((vecComp e k).trans
      (LinearEquiv.piCongrRight fun _ => (colRep r).asModuleEquiv.symm))
  have hL : ∀ (g : Γ) (x : (colRep R).asModule),
      L (MonoidAlgebra.single g (1 : k) • x) = MonoidAlgebra.single g (1 : k) • L x := by
    intro g x
    funext j
    apply (colRep r).asModuleEquiv.injective
    simp only [L, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply, Pi.smul_apply,
      Representation.asModuleEquiv_map_smul, Representation.asAlgebraHom_single_one,
      LinearEquiv.apply_symm_apply, colRep_apply]
    exact vecComp_mulVec e (fun _ => r) g _ j
  exact IsSemisimpleModule.of_injective
    (MonoidAlgebra.equivariantOfLinearOfComm L.toLinearMap hL) L.injective

end UpperTheory.Gal.Int.Div
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSubLoc
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

theorem UpperTheory.Gal.Int.Div.subLoc_of :
    SubSplit → InFacts → LocConj → LocSum → JumpCard → SubLoc := by
  intro hS hI hC hL _ E Ω _ _ _ _ _ l _ a d r ρ hss hin ι w P AI hT A h O _ _ _ Bw hj
  obtain ⟨had, -, -⟩ := hI _ _ a d r ρ hin
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le had
  obtain ⟨s, g, hg⟩ := hS _ _ a b r ρ hss hin
  have e : (sumRep r s).comp (Dec (F := E) A).subtype =
      sumRep (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype) := by
    ext; rfl
  have hiso : RepIso (ρ.comp (Dec (F := E) A).subtype)
      (sumRep (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype)) := by
    refine ⟨g, fun x => ?_⟩
    rw [← e]
    exact hg x
  have hconj := (hC l P AI hT E Ω A O Bw (a + b) (ρ.comp (Dec (F := E) A).subtype) _).2 hiso
  have hsum := hL l P AI hT E Ω A O Bw a b (r.comp (Dec (F := E) A).subtype) (s.comp (Dec (F := E) A).subtype)
  refine ⟨fun hc => ?_, fun τ J J' h1 h2 => hsum.2 τ J J' (hconj.2.2.1 τ J h1) h2⟩
  have hcS := hconj.1 hc
  obtain ⟨cr, cs⟩ := hsum.1 hcS
  refine ⟨cr, fun x => ?_⟩
  have pr := ((hC l P AI hT E Ω A O Bw a _ (r.comp (Dec (F := E) A).subtype)).1 cr).2
  have ps := ((hC l P AI hT E Ω A O Bw b _ (s.comp (Dec (F := E) A).subtype)).1 cs).2
  have pT := ((hC l P AI hT E Ω A O Bw (a + b) _ (ρ.comp (Dec (F := E) A).subtype)).1 hcS).2
  have hw := GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l P AI hT ι E Ω A w O Bw h hj a b _ _ pr ps pT
  rw [← hconj.2.2.2 ι w h hj hc, hw, (UpperTheory.Gal.TP.Sub.wDFacts_holds E Ω A w h _ _).2.1 x]
  exact Dvd.intro _ rfl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PSubSplit
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

noncomputable section

namespace UpperTheory.Gal.Int.Div

section SubSplitAux

variable {Γ k : Type} [Group Γ] [Field k] {n a b : ℕ}

private lemma sumRep_val (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ) :
    ((sumRep r s g : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k) =
      (Matrix.fromBlocks (r g : Matrix (Fin a) (Fin a) k) 0 0
        (s g : Matrix (Fin b) (Fin b) k)).submatrix finSumFinEquiv.symm finSumFinEquiv.symm := rfl

private def resHom (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') : Γ →* Module.End k W' where
  toFun g := (Matrix.mulVecLin (ρ g : Matrix (Fin n) (Fin n) k)).restrict (hinv g)
  map_one' := by ext x; simp
  map_mul' g h := by
    refine LinearMap.ext fun x => Subtype.ext ?_
    change (ρ (g * h) : Matrix (Fin n) (Fin n) k).mulVec (x : Fin n → k) =
      (ρ g : Matrix (Fin n) (Fin n) k).mulVec
        ((ρ h : Matrix (Fin n) (Fin n) k).mulVec (x : Fin n → k))
    simp [Matrix.mulVec_mulVec]

private def subRep (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') : Γ →* GL (Fin b) k :=
  MonoidHom.toHomUnits
    { toFun := fun g => LinearMap.toMatrix c c (resHom ρ hinv g)
      map_one' := by simp [LinearMap.toMatrix_one]
      map_mul' := fun g h => by
        rw [map_mul, Module.End.mul_eq_comp, LinearMap.toMatrix_comp c c c] }

private lemma subRep_val (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') (g : Γ) :
    ((subRep ρ hinv c g : GL (Fin b) k) : Matrix (Fin b) (Fin b) k) =
      LinearMap.toMatrix c c (resHom ρ hinv g) := rfl

private def colM (A : Matrix (Fin n) (Fin a) k) {W' : Submodule k (Fin n → k)}
    (c : Module.Basis (Fin b) k W') : Matrix (Fin n) (Fin a ⊕ Fin b) k :=
  Matrix.of fun i => Sum.elim (fun j => A i j) (fun j => (c j : Fin n → k) i)

private lemma intertw (ρ : Γ →* GL (Fin n) k) {W' : Submodule k (Fin n → k)}
    (hinv : IsInv ρ W') (c : Module.Basis (Fin b) k W') (A : Matrix (Fin n) (Fin a) k)
    (R : Matrix (Fin a) (Fin a) k) (g : Γ)
    (hA : (ρ g : Matrix (Fin n) (Fin n) k) * A = A * R) :
    (ρ g : Matrix (Fin n) (Fin n) k) * colM A c =
      colM A c * Matrix.fromBlocks R 0 0 (subRep ρ hinv c g : Matrix (Fin b) (Fin b) k) := by
  ext i (j | j)
  · have h := congrFun (congrFun hA i) j
    simpa [colM, Matrix.mul_apply, Fintype.sum_sum_type] using h
  · have hs := congrArg (fun v : W' => (v : Fin n → k) i) (c.sum_repr (resHom ρ hinv g (c j)))
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
      smul_eq_mul] at hs
    simp only [colM, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.of_apply, Sum.elim_inl,
      Sum.elim_inr, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply,
      mul_zero, Finset.sum_const_zero, zero_add, subRep_val, LinearMap.toMatrix_apply]
    refine Eq.trans ?_ (hs.symm.trans ?_)
    · rfl
    · exact Finset.sum_congr rfl fun x _ => mul_comm _ _

private lemma col_indep (A : Matrix (Fin n) (Fin a) k) (hA : A.rank = a)
    {W' : Submodule k (Fin n → k)} (c : Module.Basis (Fin b) k W')
    (hc : IsCompl (LinearMap.range A.mulVecLin) W') :
    LinearIndependent k (Sum.elim A.col (fun j => (c j : Fin n → k))) := by
  apply LinearIndependent.sum_type
  · rw [linearIndependent_iff_card_eq_finrank_span, Fintype.card_fin]
    calc a = A.rank := hA.symm
      _ = _ := by
        rw [Matrix.rank_eq_finrank_span_cols]
        rfl
  · exact c.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  · refine hc.disjoint.mono ?_ ?_
    · rw [Matrix.range_mulVecLin]
    · rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (c j).2

end SubSplitAux

theorem subSplit_of : SubSplit := by
  intro Γ k _ _ a b r ρ hss ⟨A, hA, hAg⟩
  have hinvW : IsInv ρ (LinearMap.range A.mulVecLin) := by
    rintro g _ ⟨u, rfl⟩
    refine ⟨(r g : Matrix (Fin a) (Fin a) k).mulVec u, ?_⟩
    simp only [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, hAg g]
  obtain ⟨W', hinv, hc⟩ := hss _ hinvW
  have hdim : Module.finrank k W' = b := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hc
    have h2 : Module.finrank k (LinearMap.range A.mulVecLin) = a := hA
    rw [Module.finrank_fin_fun] at h1
    omega
  let c : Module.Basis (Fin b) k W' := Module.finBasisOfFinrankEq k W' hdim
  let e : Fin a ⊕ Fin b ≃ Fin (a + b) := finSumFinEquiv
  let P : Matrix (Fin (a + b)) (Fin (a + b)) k := (colM A c).submatrix id e.symm
  have hP : IsUnit P := by
    rw [← Matrix.linearIndependent_cols_iff_isUnit]
    have h := (col_indep A hA c hc).comp e.symm e.symm.injective
    convert h using 1
    ext j i
    rcases h' : e.symm j with j' | j' <;> simp [P, colM, Matrix.col, h'] <;> rfl
  have hinvP : ((hP.unit⁻¹ : GL (Fin (a + b)) k) : Matrix _ _ k) * P = 1 := by
    have h := hP.unit.inv_mul
    rwa [hP.unit_spec] at h
  refine ⟨subRep ρ hinv c, hP.unit⁻¹, fun x => ?_⟩
  have hx : (ρ x : Matrix _ _ k) * P = P * (Matrix.fromBlocks (r x : Matrix (Fin a) (Fin a) k) 0 0
      (subRep ρ hinv c x : Matrix (Fin b) (Fin b) k)).submatrix e.symm e.symm := by
    rw [Matrix.submatrix_mul_equiv, ← intertw ρ hinv c A (r x) x (hAg x)]
    ext i j
    simp [P, Matrix.mul_apply]
  rw [inv_inv]
  apply Units.ext
  rw [sumRep_val, Units.val_mul, Units.val_mul, hP.unit_spec, mul_assoc, hx, ← mul_assoc, hinvP,
    one_mul]

end UpperTheory.Gal.Int.Div

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PLacBridge
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

theorem UpperTheory.Gal.Int.Div.lacBridge_of :
    LacBridge := by
  intro E Ω _ _ _ _ _ l _ a dd ρ h
  obtain ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ, J₀, hc, hm, hL⟩ := h
  have hinj : Function.Injective (fun i => J₀.orderEmbOfFin hc i) := (J₀.orderEmbOfFin hc).injective
  refine ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ,
    fun i => J₀.orderEmbOfFin hc i, hinj, fun i => hm _ (Finset.orderEmbOfFin_mem J₀ hc i), ?_⟩
  intro S T hS hT' hd heq
  let f : Fin a ↪ ℤ := ⟨fun i => J₀.orderEmbOfFin hc i, hinj⟩
  have hsub : ∀ C : Finset (Fin a), C.map f ⊆ J₀ := by
    intro C x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.orderEmbOfFin_mem J₀ hc i
  refine hL (S.map f) (T.map f) (hsub S) (hsub T) ((Finset.disjoint_map f).2 hd)
    (hS.map) (hT'.map) ?_
  rw [Finset.card_map, Finset.card_map, Finset.sum_map, Finset.sum_map]
  have : ((T.card : ℤ) * ∑ i ∈ S, f i : ℚ) = (S.card : ℤ) * ∑ i ∈ T, f i := by
    simpa [f] using heq
  simpa using (by exact_mod_cast this : (T.card : ℤ) * ∑ i ∈ S, f i = (S.card : ℤ) * ∑ i ∈ T, f i)
end

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep Formalism.UG GlobalTheory.DefU

namespace UpperTheory.Gal.Int.Div

theorem subLoc_holds : SubLoc := subLoc_of subSplit_of inFacts_of locConj_of locSum_of jumpCard_of
theorem phiSeed_holds : PhiSeed := phiSeed_of subLoc_holds locConj_of rootPin_of algGen_of
theorem centU_holds : CentU := centU_of zetaEx_of zetaLoc_of schurU_of charOfZeta_of algOfFix_of satCent_of
theorem detEx_holds : DetEx := detEx_of centU_holds
theorem divDet_holds : DivDet := divDet_of denseUs_of detFrob_of
theorem senWLac_holds : PositivityTheory.AutomorphicGaloisHodgeTate.Div.SenWLac := senWLac_of jumpCard_of
theorem divSet_holds : DivSet := divSet_of LateralTheory.DivDb.goal_holds senWLac_holds lacBridge_of inFacts_of
theorem divOne_holds : DivOne := divOne_of divSet_holds denseUs_of detFrob_of inFacts_of sepPin_of
theorem divAll_holds : DivAll :=
  divAll_of detEx_holds divDet_holds phiSeed_holds divOne_holds (divUniq_of denseUs_of) isoMove_of
    (frobSeed_of inFacts_of genPin_of algGen_of detFrob_of) (jumpSeed_of coverIn_of sSBlock_of subLoc_holds locConj_of jumpCard_of)
    subLoc_holds

end UpperTheory.Gal.Int.Div
