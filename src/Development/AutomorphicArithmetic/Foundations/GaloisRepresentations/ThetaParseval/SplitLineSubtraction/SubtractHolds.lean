module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.TwoUpOKOf
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DenseSplitFrobInvAway
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPotentiallySemistable
public import Development.AutomorphicArithmetic.ThetaCorrespondence.AlgebraicCharacters.AlgebraicCharacterWD
public import Development.WeilBound.CoreStatements.PublishedTheorems.HeckeLAdicCharacters.Outright
public import Development.WeilBound.CoreStatements.StandardPublishedResults.StandardTheoremStatements.GlobalArtinReciprocity

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharInj
open NumberField Neutral.B1 GlobalTheory.HeckeGal
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charInj_holds :
    CharInj := by
  intro E Ω _ _ _ _ _ l _ ι art _ χ χ' n n' μ hχ hχ'
  have hl : Ideal.span {(l : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast (Fact.out : Nat.Prime l).ne_zero
  have hfin := Ideal.finite_factors hl
  have hquot : χ * χ'⁻¹ = 1 := by
    refine Subtype.ext (GlobalTheory.FrobDense.eq_one_of_away (χ * χ'⁻¹).1
      (χ * χ'⁻¹).2.1 (χ * χ'⁻¹).2.2 hfin.toFinset fun v hv x => ?_)
    have hl' : (l : 𝓞 E) ∉ v.asIdeal :=
      fun h => hv (hfin.mem_toFinset.mpr (Ideal.dvd_span_singleton.mpr h))
    obtain ⟨σ, hσ⟩ := toAb_surjective (E := E) (Ω := Ω) (art (localIdele E v x))
    have a := hχ.loc_away (Or.inl hl') x σ hσ.symm
    have b := hχ'.loc_away (Or.inl hl') x σ hσ.symm
    have hloc : χ.loc v x = χ'.loc v x :=
      Units.ext (ι.symm.injective (a.symm.trans b))
    change χ.loc v x * (χ'.loc v x)⁻¹ = 1
    rw [hloc, mul_inv_cancel]
  exact mul_inv_eq_one.mp hquot
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharFrob
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

theorem charFrob_holds : CharFrob := by
  intro E Ω _ _ _ _ _ l _ ι art ha χ n μ h w hw hu A hA
  have hv : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∨ n = 0 := Or.inl hw
  refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
  · have h1 : μ s = 1 := (h.unr_iff ha hv hA).mpr hu s hs
    simp [rk1, h1]
  · have h1 : ((μ σ : (Qbar l)ˣ) : Qbar l) = (ι.symm ((χ.val w : ℂˣ) : ℂ))⁻¹ := h.frob_unr ha hv hu hA hσ
    simp [rk1, Matrix.charpoly, Matrix.det_fin_one, h1, Polynomial.map_sub]

end UpperTheory.Gal.TP.Sub

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PDgFacts
noncomputable section

open Formalism.MainNotions.N Polynomial
open Formalism.MainNotions.SumRepresentations.At (sumRep)

namespace UpperTheory.Gal.TP.Sub

section

variable {Γ k : Type} [Group Γ] [Field k]

private theorem dg_val {t : ℕ} (a : Fin t → Γ →* kˣ) (g : Γ) :
    ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k) = Matrix.diagonal fun i => (a i g : k) := rfl

private theorem ss_dg_one (b : Fin 1 → Γ →* kˣ) : IsSSRep (dg b) := by
  have key : ∀ (W : Submodule k (Fin 1 → k)), IsInv (dg b) W := by
    intro W g v hv
    have : ((dg b g : GL (Fin 1) k) : Matrix (Fin 1) (Fin 1) k).mulVec v = ((b 0 g : kˣ) : k) • v := by
      ext i
      fin_cases i
      simp [dg_val, Matrix.mulVec_diagonal]
    rw [this]
    exact W.smul_mem _ hv
  intro W _
  obtain ⟨W', hW'⟩ := exists_isCompl W
  exact ⟨W', key W', hW'⟩

private theorem dg_succ {t : ℕ} (a : Fin (t + 1) → Γ →* kˣ) :
    dg a = sumRep (dg fun i : Fin t => a i.castSucc) (dg fun _ : Fin 1 => a (Fin.last t)) := by
  ext g : 1
  apply Units.ext
  rw [GlobalTheory.BCGal.sumRep_val, dg_val, dg_val, dg_val]
  ext i j
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.diagonal_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
  · rfl
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  · intro h
    have h' := congrArg Fin.val h
    simp only [Fin.val_castAdd, Fin.val_natAdd] at h'
    omega
  · obtain rfl : i = 0 := Subsingleton.elim _ _
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rfl

private theorem ss_dg {t : ℕ} (a : Fin t → Γ →* kˣ) : IsSSRep (dg a) := by
  induction t with
  | zero => exact GlobalTheory.BCGal.ss_zero _
  | succ t ih =>
    rw [dg_succ]
    exact GlobalTheory.BCGal.ss_sumRep _ _ (ih _) (ss_dg_one _)

end

theorem dgFacts_holds : DgFacts := by
  intro Γ k _ _ t a
  refine ⟨ss_dg a, fun g => ?_⟩
  show ((dg a g : GL (Fin t) k) : Matrix (Fin t) (Fin t) k).charpoly = _
  rw [dg_val, Matrix.charpoly_diagonal]

end UpperTheory.Gal.TP.Sub

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSumDR
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.TP.Sub

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

theorem sumDR_holds : SumDR := by
  intro l _ P AI tied E Ω _ _ _ _ _ A O _ _ _ Bw a b r s hd
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨L, ρ, hm, -⟩ := id hd
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    have S := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l P AI tied E Ω _ O Bw L a b r₁ s₁
    exact ⟨L, r₁, m₁, (S.1.1 ((m.isdRAt_iff P).1 hd)).1⟩
  · obtain ⟨L, ρ, hm, -⟩ := id hd
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    have S := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l P AI tied E Ω _ O Bw L a b r₁ s₁
    exact ⟨L, s₁, m₂, (S.1.1 ((m.isdRAt_iff P).1 hd)).2⟩
  · intro τ J J' hJ hJ'
    obtain ⟨L, ρ, hm, -, τ', t, -⟩ := id hJ
    obtain ⟨r₁, s₁, m₁, m₂, m⟩ := model_split hm
    have S := GlobalTheory.T.sumRep_deRham_iff_and_multiplicity_add l P AI tied E Ω _ O Bw L a b r₁ s₁
    refine ⟨L, r₁, m₁, (S.1.1 ((m.isdRAt_iff P).1 hd)).1, τ', t, fun n => ?_⟩
    have c₁ := hJ.count_eq P m t n
    have c₂ := hJ'.count_eq P m₂ t n
    rw [S.2, Multiset.count_add, Nat.cast_add, c₂] at c₁
    linarith

end UpperTheory.Gal.TP.Sub

end
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClAway
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.clAway_holds :
    ClAway := by
  intro E Ω _ _ _ _ _ l _ ι a r w hl S J
  refine ⟨fun h => h.1 hl, fun h => ⟨fun _ => h, ?_⟩⟩
  intro P AI _ A hA O _ _ _ Bw hj
  exact absurd (hj.mem_placesOver hA) hl
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PFrobSub
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

namespace UpperTheory.Gal.TP.Sub.PFrobSub

private theorem prod_scale {K : Type} [Field K] {c : K} (hc : c ≠ 0) (x : K) (S : Multiset K) :
    c ^ Multiset.card S * (S.map fun z => x / c - z).prod = (S.map fun z => x - z * c).prod := by
  induction S using Multiset.induction_on with
  | empty => simp
  | cons a S ih =>
    have e : c * (x / c - a) = x - a * c := by
      field_simp
    rw [Multiset.card_cons, Multiset.map_cons, Multiset.map_cons, Multiset.prod_cons, Multiset.prod_cons, ← ih, ← e]
    ring

private theorem charpoly_smul_eq {K : Type} [Field K] [Infinite K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K}
    (hc : c ≠ 0) (S : Multiset K) (h : M.charpoly = (S.map fun z => X - C z).prod) :
    (c • M).charpoly = (S.map fun z => X - C (z * c)).prod := by
  apply Polynomial.funext
  intro x
  have hn : Multiset.card S = n := by
    have := congrArg Polynomial.natDegree h
    rw [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_multiset_prod_X_sub_C_eq_card] at this
    simpa using this.symm
  have key : Matrix.scalar (Fin n) x - c • M = c • (Matrix.scalar (Fin n) (x / c) - M) := by
    rw [smul_sub]
    congr 1
    ext i j
    simp [Matrix.diagonal_apply]
    split_ifs <;> field_simp
  rw [Matrix.eval_charpoly, key, Matrix.det_smul, ← Matrix.eval_charpoly, h, Fintype.card_fin, ← hn,
    Polynomial.eval_multiset_prod, Polynomial.eval_multiset_prod, Multiset.map_map, Multiset.map_map]
  simp only [Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  exact prod_scale hc x S

private theorem sumRep_left {Γ k : Type} [Group Γ] [Field k] {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k)
    (g : Γ) (i j : Fin a) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) (Fin.castAdd b i) (Fin.castAdd b j) =
      (r g : Matrix (Fin a) (Fin a) k) i j := by
  simp [sumRep, Formalism.MainNotions.SumRepresentations.At.blkHom]
  rfl

private theorem characterAsRankOneRep_entry {Γ k : Type} [Group Γ] [Field k] (μ : Γ →* kˣ) (g : Γ) :
    (rk1 μ g : Matrix (Fin 1) (Fin 1) k) 0 0 = (μ g : k) := by
  unfold rk1
  simp

end UpperTheory.Gal.TP.Sub.PFrobSub

open UpperTheory.Gal.TP.Sub.PFrobSub in
theorem UpperTheory.Gal.TP.Sub.frobSub_holds :
    CpFacts → FrobSub := by
  intro h E Ω _ _ _ _ _ l _ ι a w S c μ hμ
  have hc : ∀ A, IsPlaceOver A w → ∀ σ : G E Ω, IsFrob A (normV w) σ →
      ι.toRingHom (μ σ⁻¹ : Qbar l) = c := by
    intro A hA σ hσ
    have h1 := (hμ A hA).2 σ hσ
    have h2 := (h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹
    unfold cp at h2
    rw [h2] at h1
    simpa using h1
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · intro A hA
    obtain ⟨hI, hF⟩ := hs A hA
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have e := hI σ hσ
      ext i j
      have hij := sumRep_left s (rk1 μ) σ i j
      rw [e] at hij
      rw [← hij]
      simp [Matrix.one_apply]
    · have e := hF σ hσ
      have h3 := (h (G E Ω) (Qbar l) a 1).1 s (rk1 μ) σ⁻¹
      have h4 := (h (G E Ω) (Qbar l) 1 1).2.1 μ σ⁻¹
      unfold cp at h3 h4
      rw [h3, Polynomial.map_mul, h4] at e
      simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C] at e
      rw [hc A hA σ hσ, Multiset.map_add (f := _), Multiset.prod_add, Multiset.map_singleton,
        Multiset.prod_singleton] at e
      exact mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero c) e
  · intro A hA
    obtain ⟨hI, hF⟩ := hs A hA
    obtain ⟨hIμ, -⟩ := hμ A hA
    refine ⟨fun σ hσ => ?_, fun σ hσ => ?_⟩
    · have e1 := hI σ hσ
      have e2 : (μ σ : Qbar l) = 1 := by
        rw [← characterAsRankOneRep_entry μ σ, hIμ σ hσ]
        simp
      ext i j
      rw [UpperTheory.V.Af.tw_val, e1, e2]
      simp
    · have e := hF σ hσ
      have hc' := hc A hA σ hσ
      have hc0 : c ≠ 0 := by
        rw [← hc']
        simp
      rw [UpperTheory.V.Af.tw_val, ← Matrix.charpoly_map]
      rw [← Matrix.charpoly_map] at e
      have hm : ((μ σ⁻¹ : Qbar l) • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l))).map ι.toRingHom =
          c • (s σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).map ι.toRingHom := by
        rw [← hc']
        ext i j
        simp
      rw [hm, Multiset.map_map]
      exact charpoly_smul_eq _ hc0 S e
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSSLeft
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

section
open scoped Matrix

variable {Γ k : Type} [Group Γ] [Field k]

private def inc (a b : ℕ) : (Fin a → k) →ₗ[k] (Fin (a + b) → k) where
  toFun x := Sum.elim x 0 ∘ finSumFinEquiv.symm
  map_add' x y := by
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j <;> simp
  map_smul' c x := by
    funext i
    obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
    cases j <;> simp

private theorem inc_inl {a b : ℕ} (x : Fin a → k) (i : Fin a) :
    inc a b x (finSumFinEquiv (Sum.inl i)) = x i := by
  simp [inc]

private theorem inc_inr {a b : ℕ} (x : Fin a → k) (j : Fin b) :
    inc a b x (finSumFinEquiv (Sum.inr j)) = 0 := by
  simp [inc]

private theorem inc_injective {a b : ℕ} : Function.Injective (inc (k := k) a b) := by
  intro x y h
  funext i
  rw [← inc_inl (b := b) x i, ← inc_inl (b := b) y i, h]

private theorem sum_mulVec_inc {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k) (g : Γ)
    (x : Fin a → k) :
    (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) *ᵥ inc a b x =
      inc a b ((r g : Matrix (Fin a) (Fin a) k) *ᵥ x) := by
  funext i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective i
  rcases j with j | j
  · rw [GlobalTheory.EigTwist.sumRep_mulVec_inl, inc_inl]
    congr 1
    funext i
    exact inc_inl x i
  · rw [GlobalTheory.EigTwist.sumRep_mulVec_inr, inc_inr]
    have : (inc a b x ∘ finSumFinEquiv ∘ Sum.inr : Fin b → k) = 0 := by
      funext i
      exact inc_inr x i
    rw [this, Matrix.mulVec_zero]
    rfl

private theorem ss_left {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k)
    (h : IsSSRep (sumRep r s)) : IsSSRep r := by
  intro W hW
  obtain ⟨C, hC, hc⟩ := h (W.map (inc a b)) (by
    rintro g _ ⟨x, hx, rfl⟩
    exact ⟨_, hW g x hx, (sum_mulVec_inc r s g x).symm⟩)
  refine ⟨C.comap (inc a b), fun g v hv => ?_, ?_, ?_⟩
  · show inc a b _ ∈ C
    rw [← sum_mulVec_inc r s g v]
    exact hC g _ hv
  · rw [Submodule.disjoint_def]
    intro x hx hx'
    have h0 : inc a b x ∈ W.map (inc a b) ⊓ C := ⟨⟨x, hx, rfl⟩, hx'⟩
    rw [hc.disjoint.eq_bot, Submodule.mem_bot] at h0
    exact inc_injective (h0.trans (map_zero _).symm)
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    have hx : inc a b x ∈ W.map (inc a b) ⊔ C := by
      rw [hc.codisjoint.eq_top]
      exact Submodule.mem_top
    obtain ⟨_, ⟨w, hw, rfl⟩, z, hz, hzx⟩ := Submodule.mem_sup.1 hx
    have hz' : z = inc a b (x - w) := by
      rw [map_sub, ← hzx]
      abel
    refine Submodule.mem_sup.2 ⟨w, hw, x - w, ?_, by abel⟩
    show inc a b (x - w) ∈ C
    rwa [← hz']

private theorem ss_of_iso {n : ℕ} (r r' : Γ →* GL (Fin n) k) (h : RepIso r r') (hr : IsSSRep r) :
    IsSSRep r' := by
  obtain ⟨g, hg⟩ := h
  let e : (Fin n → k) ≃ₗ[k] (Fin n → k) := Matrix.toLin'OfInv
    (M := ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) (M' := (g : Matrix (Fin n) (Fin n) k))
    (Units.inv_mul g) (Units.mul_inv g)
  have he : ∀ v, e v = (g : Matrix (Fin n) (Fin n) k) *ᵥ v := fun v => rfl
  have key : ∀ s v, e ((r s : Matrix (Fin n) (Fin n) k) *ᵥ v) = (r' s : Matrix (Fin n) (Fin n) k) *ᵥ e v := by
    intro s v
    rw [he, he, hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel_right]
  intro W hW
  obtain ⟨C, hC, hc⟩ := hr (W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))) (by
    intro s v hv
    show e _ ∈ W
    rw [key]
    exact hW s _ hv)
  refine ⟨C.map (e : (Fin n → k) →ₗ[k] (Fin n → k)), ?_, ?_⟩
  · rintro s _ ⟨u, hu, rfl⟩
    exact ⟨_, hC s u hu, key s u⟩
  · have h2 : IsCompl ((W.comap (e : (Fin n → k) →ₗ[k] (Fin n → k))).map (e : (Fin n → k) →ₗ[k] (Fin n → k)))
        (C.map (e : (Fin n → k) →ₗ[k] (Fin n → k))) := (Submodule.orderIsoMapComap e).isCompl hc
    rwa [Submodule.map_comap_eq_of_surjective e.surjective] at h2

private theorem ss_tw {n : ℕ} (r : Γ →* GL (Fin n) k) (c : Γ →* kˣ) (hr : IsSSRep r) :
    IsSSRep (tw r c) := by
  intro W hW
  have hW' : IsInv r W := by
    intro g v hv
    have h1 := W.smul_mem ((c g)⁻¹ : kˣ).val (hW g v hv)
    rw [UpperTheory.V.Af.tw_val, Matrix.smul_mulVec, smul_smul, Units.val_inv_eq_inv_val,
      inv_mul_cancel₀ (c g).ne_zero, one_smul] at h1
    exact h1
  obtain ⟨C, hC, hc⟩ := hr W hW'
  refine ⟨C, fun g v hv => ?_, hc⟩
  rw [UpperTheory.V.Af.tw_val, Matrix.smul_mulVec]
  exact C.smul_mem _ (hC g v hv)

end

theorem UpperTheory.Gal.TP.Sub.sSLeft_holds :
    SSLeft := by
  intro Γ k _ _ a b
  exact ⟨fun r s h => ss_left r s h, fun r r' h hr => ss_of_iso r r' h hr, fun r c h => ss_tw r c h⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PSatAE
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub
open GlobalTheory.PRep Formalism.UG GlobalTheory.BCT

theorem UpperTheory.Gal.TP.Sub.satAE_holds :
    SatAE := by
  intro E _ _ _ a U hU
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU (E := E) (n := a)) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hLo : IsOpen (L : Set (finU (E := E) (n := a))) := (hU.aut φ hφ).level
  filter_upwards [GlobalTheory.T.eventually_localIntegralPoints_mem_openSubgroup_definiteUnitary E a L hLo] with w hw hs
  obtain ⟨hJo, hJc⟩ := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w a
  obtain ⟨σ, hσ, v, hv0, hv⟩ := GlobalTheory.T.exists_localComponent_eigenvector_splitPlace E a U hU w hs (GlobalTheory.LFun.KGL w (n := a)) hJo hJc 1 φ hφ hφ0
    (fun x hx hxK => by
      have h : RU E a x φ = φ := hw x hx hxK hx.1
      simpa using h)
  have hsph : GlobalTheory.LGrp.IsSpherical σ.ρ (GlobalTheory.LFun.KGL w (n := a)) :=
    (Submodule.ne_bot_iff _).2 ⟨v, GlobalTheory.LGrp.mem_fixed.2 fun k hk => by simpa using hv ⟨k, hk⟩, hv0⟩
  obtain ⟨B, hB⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred hsph
  exact ⟨B, σ, hσ, hB⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.ClTwHolds
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.clTw_holds :
    FrobSub → TwLoc → TwJumps → PstOfDR → WDFacts → ContLeft → ClTw := by
  intro hF hL hJ hP hW hC E Ω _ _ _ _ _ l _ ι a s μ hs hμ w S c J m h1 h2
  refine ⟨fun hw => (hF E Ω l ι a w S c μ (h1.1 hw)).2 s (h2.1 hw), ?_⟩
  intro P AI hT A h O _ _ _ Bw hj
  obtain ⟨c1, d1, j1, p1⟩ := h1.2 P AI hT A h O Bw hj
  obtain ⟨c2, d2, j2, p2⟩ := h2.2 P AI hT A h O Bw hj
  have e1 : (rk1 μ).comp (Dec (F := E) A).subtype = rk1 (μ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw s μ).comp (Dec (F := E) A).subtype =
      tw (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  have e3 : Formalism.MainNotions.SumRepresentations.At.twGL (s.comp (Dec (F := E) A).subtype)
      (Matrix.GeneralLinearGroup.det.comp (rk1 (μ.comp (Dec (F := E) A).subtype))) =
      tw (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype) := by
    have hdet : Matrix.GeneralLinearGroup.det.comp (rk1 (μ.comp (Dec (F := E) A).subtype))
        = μ.comp (Dec (F := E) A).subtype := by
      ext g
      simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
    rw [hdet]
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, UpperTheory.V.Af.tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  rw [e1] at c1 d1 j1 p1
  rw [e2]
  have cs : Continuous (s.comp (Dec (F := E) A).subtype) := hs.comp continuous_subtype_val
  have cμ : Continuous (μ.comp (Dec (F := E) A).subtype) := hμ.comp continuous_subtype_val
  have ck := (hC _ (Qbar l) 1 1).2.2.2 _ cμ
  have ct := (hC _ (Qbar l) a 1).2.2.1 _ _ cs cμ
  obtain ⟨l1, l2⟩ := hL l P AI hT E Ω A O Bw a (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype)
  have dt := l1 d2 d1
  refine ⟨l2 c2 c1, dt, ?_, ?_⟩
  · intro τ LL' τ' hi
    exact hJ l P AI hT E Ω A O Bw a _ _ cs cμ τ (J τ) (m τ) (j2 τ LL' τ' hi) (j1 τ LL' τ' hi)
  · intro g
    have q1 := hP l P AI hT E Ω A O Bw a _ cs d2
    have q2 := hP l P AI hT E Ω A O Bw 1 _ ck d1
    have q3 := hP l P AI hT E Ω A O Bw a _ ct dt
    have hcs : Continuous fun g : ↥(Dec (F := E) A) =>
        ((s.comp (Dec (F := E) A).subtype g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l)) :=
      Units.continuous_val.comp cs
    have hck : Continuous fun g : ↥(Dec (F := E) A) =>
        ((rk1 (μ.comp (Dec (F := E) A).subtype) g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l)) :=
      Units.continuous_val.comp ck
    rw [← e3] at q3
    have key := GlobalTheory.T.fontaineParameter_twist_potentiallySemistable l P AI hT ι E Ω A w h O Bw hj a _ _ hcs hck q1 q2 q3
    rw [e3] at key
    rw [key]
    exact (hW E Ω A w h _ _).2.2.2 g S c (p2 g) (p1 g)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PPeelAll
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem univ_map_snoc {α : Type*} {t : ℕ} (f : Fin (t + 1) → α) :
    Finset.univ.val.map f =
      Finset.univ.val.map (fun i : Fin t => f i.castSucc) + {f (Fin.last t)} := by
  rw [Fin.univ_castSuccEmb]
  simp [Finset.map_val, Multiset.map_map, add_comm, Function.comp_def]

theorem UpperTheory.Gal.TP.Sub.peelAll_holds :
    PeelOne → ContLeft → ClConj → ClSub → PeelAll := by
  intro hP hC hJ hS E Ω _ _ _ _ _ l _ ι n m' t' r' a' hr' t
  induction t with
  | zero =>
    intro r a hc hss _ _ _
    refine ⟨r, hc, hss, ?_⟩
    intro w S c J m _ h
    simpa using h
  | succ t ih =>
    intro r a hc hss ha hne hid
    obtain ⟨s₁, hs₁, hiso, hid₁⟩ :=
      hP (G E Ω) (Qbar l) (n + t) m' t t' r r' a a' hss hr' hne hid
    have hC' := hC (G E Ω) (Qbar l) (n + t) 1
    have hC1 := hC (G E Ω) (Qbar l) (n + t + 1) 1
    have hcl : Continuous (sumRep s₁ (rk1 (a (Fin.last t)))) := hC1.2.1 _ _ hiso hc
    have hcs₁ : Continuous s₁ := hC'.1 _ _ hcl
    obtain ⟨s, hsc, hss', hcl'⟩ := ih s₁ (fun i => a i.castSucc) hcs₁ hs₁
      (fun i => ha _) (fun i j => hne _ _) hid₁
    refine ⟨s, hsc, hss', ?_⟩
    intro w S c J m hcl0 h
    have h2 := hJ E Ω l ι _ r _ hc hiso w _ _ h
    refine hcl' w S (fun i => c i.castSucc) J (fun i => m i.castSucc) (fun i => hcl0 _) ?_
    refine hS E Ω l ι _ s₁ (a (Fin.last t)) hcs₁ (ha _) w _ (c (Fin.last t)) _
      (m (Fin.last t)) (hcl0 _) ?_
    have e1 : S + Finset.univ.val.map c =
        S + Finset.univ.val.map (fun i : Fin t => c i.castSucc) + {c (Fin.last t)} := by
      rw [univ_map_snoc c, add_assoc]
    have e2 : (fun τ => J τ + Finset.univ.val.map fun i => m i τ) =
        fun τ => J τ + Finset.univ.val.map (fun i : Fin t => m i.castSucc τ) +
          {m (Fin.last t) τ} := by
      funext τ
      rw [univ_map_snoc (fun i => m i τ), add_assoc]
    rw [e1, e2] at h2
    exact h2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PPeelOne
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.peelOne_holds :
    DgFacts → CpFacts → EigTransfer → EigSum → SplitLine → SSLeft → PeelOne := by
  intro hDg hCp hTr hEig hSplit hSS Γ k _ _ _ _ m m' t t' r r' a a' hr hr' hne hcp
  set c := a (Fin.last t) with hc
  have hR1 : IsSSRep (sumRep r (dg a')) := GlobalTheory.BCGal.ss_sumRep _ _ hr (hDg Γ k t' a').1
  have hR2 : IsSSRep (sumRep r' (dg a)) := GlobalTheory.BCGal.ss_sumRep _ _ hr' (hDg Γ k (t + 1) a).1
  have hcpR : ∀ g, cp (sumRep r (dg a')) g = cp (sumRep r' (dg a)) g := by
    intro g
    rw [(hCp Γ k (m + 1) t').1, (hCp Γ k m' (t + 1)).1, (hDg Γ k t' a').2, (hDg Γ k (t + 1) a).2]
    exact hcp g
  have hv2 := (hEig Γ k m' (t + 1) r' a c).1 ⟨Fin.last t, rfl⟩
  have hv1 := hTr Γ k _ _ (sumRep r (dg a')) (sumRep r' (dg a)) hR1 hR2 hcpR c hv2
  have hv := (hEig Γ k (m + 1) t' r a' c).2 (fun j h => hne (Fin.last t) j h.symm) hv1
  obtain ⟨s, hs⟩ := hSplit Γ k m r hr c hv
  have hsum : IsSSRep (sumRep s (rk1 c)) := (hSS Γ k (m + 1) 0).2.1 r _ hs hr
  refine ⟨s, (hSS Γ k m 1).1 s (rk1 c) hsum, hs, ?_⟩
  intro g
  have h1 : cp r g = cp s g * (X - C ((c g : kˣ) : k)) := by
    rw [← (hCp Γ k (m + 1) 0).2.2 r _ hs g, (hCp Γ k m 1).1, (hCp Γ k m 1).2.1]
  have h2 : lin a g = lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k)) := by
    simp only [lin]
    rw [Fin.prod_univ_castSucc]
  have hX : (X - C ((c g : kˣ) : k) : k[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero _
  have key := hcp g
  rw [h1, h2] at key
  apply mul_right_cancel₀ hX
  calc cp s g * lin a' g * (X - C ((c g : kˣ) : k))
      = cp s g * (X - C ((c g : kˣ) : k)) * lin a' g := by ring
    _ = cp r' g * (lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k))) := key
    _ = cp r' g * lin (fun i => a i.castSucc) g * (X - C ((c g : kˣ) : k)) := by ring
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PCharEx
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.charEx_holds :
    GlobalTheory.Published.HeckeLAdicCharacter → CharFrob → CharAbove → CharInj → CharEx := by
  classical
  intro H hF hA hI E Ω _ _ _ _ _ l _ ι
  obtain ⟨art, hart, hex⟩ := H E Ω
  have hL : ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
      ∃ r : G E Ω →* (Qbar l)ˣ, Continuous r ∧ IsLAdicOf art ι χ n r :=
    fun χ n h => (hex l ι χ n h).exists
  let L : HChar E → ((E →+* ℂ) → ℤ) → (G E Ω →* (Qbar l)ˣ) :=
    fun χ n => if h : IsAlgPos χ n then (hL χ n h).choose else 1
  have hspec : ∀ (χ : HChar E) (n : (E →+* ℂ) → ℤ), IsAlgPos χ n →
      Continuous (L χ n) ∧ IsLAdicOf art ι χ n (L χ n) := by
    intro χ n h
    have e : L χ n = (hL χ n h).choose := dif_pos h
    rw [e]
    exact (hL χ n h).choose_spec
  refine ⟨L, fun χ n h => ⟨(hspec χ n h).1, fun w hw => ⟨fun hl => ?_, ?_⟩⟩, fun χ n χ' n' h h' e => ?_⟩
  · exact hF E Ω l ι art hart χ n (L χ n) (hspec χ n h).2 w hl hw
  · exact hA E Ω l ι art hart χ n (L χ n) h (hspec χ n h).1 (hspec χ n h).2 w hw
  · exact hI E Ω l ι art hart χ χ' n n' (L χ n) (hspec χ n h).2 (e ▸ (hspec χ' n' h').2)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PEigTransfer
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.eigTransfer_holds :
    EigTransfer := by
  intro Γ k _ _ _ _ N N' ρ ρ' hρ hρ' hcp c ⟨v, hv0, hv⟩
  have hN : N = N' := by
    have h := congrArg Polynomial.natDegree (hcp 1)
    simpa [cp, Matrix.charpoly_natDegree_eq_dim] using h
  subst hN
  obtain ⟨P, hP⟩ := Formalism.MainNotions.SumRepresentations.brauerNesbitt_matrix ρ ρ' hρ hρ' (fun g => hcp g)
  refine ⟨(P : Matrix (Fin N) (Fin N) k).mulVec v, ?_, ?_⟩
  · intro h
    apply hv0
    have := congrArg (((P⁻¹ : GL (Fin N) k) : Matrix (Fin N) (Fin N) k).mulVec) h
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec,
      Matrix.mulVec_zero] at this
    exact this
  · intro g
    have hg : ρ g * P = P * ρ' g := by
      rw [hP g]
      group
    have hm : (ρ g : Matrix (Fin N) (Fin N) k) * P = P * ρ' g := by
      rw [← Units.val_mul, hg, Units.val_mul]
    rw [Matrix.mulVec_mulVec, hm, ← Matrix.mulVec_mulVec, hv g, Matrix.mulVec_smul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PPstOfDR
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.pstOfDR_holds :
    GlobalTheory.Published.DeRhamPotSemistable → PstOfDR := by
  intro hB l _ P AI hT E Ω _ _ _ _ _ A O _ _ _ Bw a r hr hd
  obtain ⟨T⟩ := hT
  exact hB.isPstAt T Bw r (Units.continuous_val.comp hr) hd
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PClConj
open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

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

private theorem isdRAt_conj {l : ℕ} [Fact l.Prime] {P : LocPrime l} {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {Bw : LocBridge l E Ω Gw O} {m : ℕ} {r : ↥Gw →* GL (Fin m) (Qbar l)} (A : GL (Fin m) (Qbar l)) (K : FinExt l)
    (hA : ∀ i j, (A : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1 ∧
      ((A⁻¹ : GL (Fin m) (Qbar l)) : Matrix (Fin m) (Fin m) (Qbar l)) i j ∈ K.1)
    (hr : IsdRAt P Bw r) : IsdRAt P Bw ((MulAut.conj A⁻¹).toMonoidHom.comp r) := by
  obtain ⟨LL', r₀, hm, hc⟩ := hr
  obtain ⟨h, M, hM⟩ := GlobalTheory.ConjCrys.exists_conj_model A K hA hm
  obtain ⟨-, hdR2, -, -⟩ := GlobalTheory.Pst.local_ext P Bw h r₀
  exact ⟨_, _, hM, (GlobalTheory.ConjCrys.local_conj P Bw _ M _).2.1 (hdR2.2 hc)⟩

theorem UpperTheory.Gal.TP.Sub.clConj_holds :
    CpFacts → ContLeft → PstOfDR → ClConj := by
  intro hCp hCont hPst E Ω _ _ _ _ _ l _ ι a r r' hr hiso w S J hcl
  obtain ⟨g, hg⟩ := id hiso
  obtain ⟨h1, h2⟩ := hcl
  refine ⟨fun hl A hA => ?_, ?_⟩
  · obtain ⟨i1, i2⟩ := h1 hl A hA
    refine ⟨fun s hs => ?_, fun σ hσ => ?_⟩
    · rw [hg, i1 s hs]
      simp
    · have e : (r' σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly =
          (r σ⁻¹ : Matrix (Fin a) (Fin a) (Qbar l)).charpoly :=
        (hCp (G E Ω) (Qbar l) a a).2.2 r r' hiso σ⁻¹
      rw [e]
      exact i2 σ hσ
  · intro P AI hT A h O _ _ _ Bw hj
    obtain ⟨c1, c2, c3, c4⟩ := h2 P AI hT A h O Bw hj
    obtain ⟨K, hK⟩ := exists_finExt_gl (g⁻¹)
    have e : r'.comp (Dec (F := E) A).subtype =
        (MulAut.conj (g⁻¹)⁻¹).toMonoidHom.comp (r.comp (Dec (F := E) A).subtype) := by
      ext1 x
      simp [hg, MulAut.conj_apply]
    have hc' : Continuous r' := (hCont (G E Ω) (Qbar l) a a).2.1 r r' hiso hr
    have cρ : Continuous (r.comp (Dec (F := E) A).subtype) := hr.comp continuous_subtype_val
    have cρ' : Continuous (r'.comp (Dec (F := E) A).subtype) := hc'.comp continuous_subtype_val
    have d' : IsdRAt P Bw (r'.comp (Dec (F := E) A).subtype) := by
      rw [e]
      exact isdRAt_conj _ K hK c2
    refine ⟨?_, d', fun τ LL' τ' hI => ?_, fun x => ?_⟩
    · rw [e]
      exact GlobalTheory.ConjCrys.isCrysAt_conj _ K hK c1
    · rw [e]
      exact GlobalTheory.ConjCrys.isJumpsAt_conj _ K hK (c3 τ LL' τ' hI)
    · rw [GlobalTheory.ConjGal.wdAt_conj P ι Bw h hj (r.comp (Dec (F := E) A).subtype)
        (r'.comp (Dec (F := E) A).subtype) g (fun x => hg x)
        (hPst l P AI hT E Ω A O Bw a _ cρ c2) (hPst l P AI hT E Ω A O Bw a _ cρ' d')]
      exact c4 x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PDenseId
noncomputable section

open Neutral.B1 hiding G IsPlaceOver Dec
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open Formalism.MainNotions.SumRepresentations.At (sumRep)

namespace UpperTheory.Gal.TP.Sub

theorem denseId_holds : CpFacts → DgFacts → DenseId := by
  intro _ _ Γ _ _ l _ m m' t t' r r' a a' hr hr' ha ha' D hD hEq g
  apply Polynomial.funext
  intro x
  have key : ∀ {n : ℕ} (s : Γ →* GL (Fin n) (Qbar l)), Continuous s →
      Continuous fun g => (cp s g).eval x := by
    intro n s hs
    simp only [cp, Matrix.eval_charpoly]
    exact (continuous_const.sub (Units.continuous_val.comp hs)).matrix_det
  have keyl : ∀ {n : ℕ} (b : Fin n → Γ →* (Qbar l)ˣ), (∀ i, Continuous (b i)) →
      Continuous fun g => (lin b g).eval x := by
    intro n b hb
    simp only [lin, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X,
      Polynomial.eval_C]
    exact continuous_finsetProd _ fun i _ =>
      continuous_const.sub (Units.continuous_val.comp (hb i))
  have h := Continuous.ext_on hD ((key r hr).mul (keyl a' ha')) ((key r' hr').mul (keyl a ha))
    (fun g hg => by
      simp only [Pi.mul_apply]
      rw [← Polynomial.eval_mul, ← Polynomial.eval_mul, hEq g hg])
  have hg := congrFun h g
  simp only [Pi.mul_apply] at hg
  rw [Polynomial.eval_mul, Polynomial.eval_mul]
  exact hg

end UpperTheory.Gal.TP.Sub

end
end

namespace UpperTheory.Gal.TP.Sub

theorem pstOfDR : PstOfDR := pstOfDR_holds GlobalTheory.deRham_potentiallySemistable

theorem frobSub : FrobSub := frobSub_holds cpFacts_holds

theorem clConj : ClConj := clConj_holds cpFacts_holds contLeft_holds pstOfDR

theorem clSub : ClSub := clSub_holds frobSub sumDR_holds pstOfDR wDFacts_holds

theorem clTw : ClTw := clTw_holds frobSub twLoc_holds twJumps_holds pstOfDR wDFacts_holds contLeft_holds

theorem peelAll : PeelAll :=
  peelAll_holds (peelOne_holds dgFacts_holds cpFacts_holds eigTransfer_holds eigSum_holds splitLine_holds sSLeft_holds)
    contLeft_holds clConj clSub

theorem charEx : CharEx :=
  charEx_holds PositivityTheory.Stage1.PM.heckeLAdicCharacter charFrob_holds
    (charAbove_holds PositivityTheory.Stage1.PM.heckeLAdicCharacter HodgeLocalDeRhamField.HLdR.field_outright
      (UpperTheory.Lit.CharWD.algebraicCharacterWD GlobalTheory.globalArtinReciprocity_holds HodgeLocalDeRhamField.HLdR.field_outright GlobalTheory.deRham_potentiallySemistable) pstOfDR
      contLeft_holds) charInj_holds

end UpperTheory.Gal.TP.Sub
