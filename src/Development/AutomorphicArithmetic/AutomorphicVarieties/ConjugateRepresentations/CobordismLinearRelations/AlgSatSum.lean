module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.ClozelConjCOfSteps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.SumCoordRe
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.QuadraticTwists.AttTwist

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.BlockConj
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.SatConj
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.satConj :
    UpperTheory.V.Cj.SatConj := by
  intro E _ _ _ n hC π
  induction π using Quotient.inductionOn with | _ π => ?_
  intro hπ σ
  obtain ⟨π', τ, τ', h1, h2, h3, -⟩ := hC π hπ σ
  obtain ⟨hs, hs'⟩ := sep_of_conj h1 h2 h3
  exact ⟨CG.mk π', fun w B hB => (hs.comp _).exists_hasSatGL (hs'.comp _) hB⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CobordismLinearRelations.TwReg
open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

theorem UpperTheory.V.Cj.twReg :
    UpperTheory.V.Cj.TwReg := by
  intro E _ _ _ a n π μ m hμ hm hr ν hν; refine (GlobalTheory.CuspRep.CG.isRegAlg_iff _).2 fun t => ?_
  have e := ((hμ t).twist ν).infChar_eq
  rw [e, (InfType.expo_of_infType E ν).2.1 _ hν t]
  obtain ⟨-, h1, h2⟩ := hr t
  refine ⟨(Multiset.nodup_of_le (hm t) h1).map (add_left_injective _), fun z hz => ?_⟩
  obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hz
  obtain ⟨k, rfl⟩ := h2 y (Multiset.mem_of_le (hm t) hy)
  exact ⟨k, by push_cast; ring⟩
end

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem sat_twist {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ} (π : CG E a)
    {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B) {χ : HChar E} (hχ : χ.UnrAt w) :
    (π.twist χ).HasSat w (B.map (· * χ.val w)) := by
  induction π using Quotient.inductionOn
  exact GlobalTheory.SphGal.hasSatGL_twist _ _ _ χ w B hχ h

private theorem algSat_eq (n q : ℕ) (B : Multiset ℂˣ) :
    algSat n q B = B.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := by
  simp [algSat, Multiset.bind_singleton, Multiset.map_map]

private theorem algSat_shift {E : Type} [Field E] [NumberField E] (a n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    {χ : HChar E} (hχ : χ.IsAbsPow (((n : ℝ) - a) / 2)) (B : Multiset ℂˣ) :
    algSat n (Formalism.ConjugateSelfDual.normV w) (B.map (· * χ.val w)) = algSat a (Formalism.ConjugateSelfDual.normV w) B := by
  have h := hχ.2.1 w
  have hq : (0 : ℝ) < (Formalism.ConjugateSelfDual.normV w : ℕ) := by
    have he : Formalism.ConjugateSelfDual.normV w = Ideal.absNorm w.asIdeal := by
      rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
      rfl
    have hn : Ideal.absNorm w.asIdeal ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff]
      exact w.ne_bot
    rw [he]
    exact_mod_cast Nat.pos_of_ne_zero hn
  rw [algSat_eq, algSat_eq, Multiset.map_map]
  refine Multiset.map_congr rfl fun b _ => ?_
  simp only [Function.comp_apply, Units.val_mul]
  rw [h]
  have e : Ideal.absNorm w.asIdeal = Formalism.ConjugateSelfDual.normV w := by
    first | rfl | exact Ideal.absNorm_apply _ | simp [Formalism.ConjugateSelfDual.normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have e2 : ((a : ℝ) - 1) / 2 = ((n : ℝ) - 1) / 2 + -(((n : ℝ) - a) / 2) := by ring
  rw [e, e2, Real.rpow_add hq, Complex.ofReal_mul, Complex.ofReal_cpow hq.le (-_), Complex.ofReal_neg,
    Complex.ofReal_natCast]
  ring

theorem UpperTheory.V.Cj.blockConj :
    UpperTheory.V.Cj.BlockConj := by
  intro E _ _ _ a n hC π μ m h1 h2 h3 σ
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (((n : ℝ) - a) / 2)
  have hν' := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E (((a : ℝ) - n) / 2)
  obtain ⟨π', hπ'⟩ := satConj E n hC _ (twReg E a n π μ m h1 h2 h3 _ hν) σ
  refine ⟨π'.twist (GlobalTheory.HeckeGal.Model.absPow E (((a : ℝ) - n) / 2)), fun w B hB => ?_⟩
  obtain ⟨B', b1, b2⟩ := hπ' w _ (sat_twist π hB (hν.1 w))
  refine ⟨_, sat_twist π' b1 (hν'.1 w), ?_⟩
  rw [algSat_shift n a w hν', b2, algSat_shift a n w hν]
end

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Cj
open scoped TensorProduct

private theorem algSat_sum {ι : Type} [Fintype ι] (n q : ℕ) (B : ι → Multiset ℂˣ) :
    algSat n q (∑ i, B i) = ∑ i, algSat n q (B i) := by
  have e : ∀ C : Multiset ℂˣ, algSat n q C =
      C.map fun α : ℂˣ => (((q : ℝ) ^ (((n : ℝ) - 1) / 2) : ℝ) : ℂ) * (α : ℂ) := fun C => by simp [algSat]
  simp only [e]
  exact map_sum (Multiset.mapAddMonoidHom _) B Finset.univ

theorem UpperTheory.V.Cj.noEis :
    UpperTheory.V.Cj.NoEis := by
  intro hJ E _ _ _ a ha ih π σ τ τ' hτ hc m hm ι _ n P μ k1 k2 k3 k4 k5 hw
  have hle : ∀ i t, μ i t ≤ m t := fun i t => by
    rw [← k5 t]
    exact Finset.single_le_sum (f := fun i => μ i t) (fun _ _ => Multiset.zero_le _) (Finset.mem_univ i)
  choose Q hQ using fun i => blockConj E a (n i) (ih _ (k2 i) (k3 i)) (P i) (μ i) m (k4 i) (hle i) hm σ.symm
  have s1 : Sep σ.symm τ'.ρ π.finPart := hc.sep.2.trans hτ.sep.2
  have s2 : Sep σ.symm.symm π.finPart τ'.ρ := hτ.sep.1.trans hc.sep.1
  obtain ⟨s, -⟩ := hJ E Unit ι (fun _ => a) n (fun _ => CG.mk π) Q (fun _ => ha) k2 (hw.mono fun w ⟨B, h1, h2⟩ => by
    choose B' b1 b2 using fun i => hQ i w (B i) (h1 i)
    refine ⟨fun _ => ∑ i, B' i, B', fun _ => (CG.hasSat_mk ..).2 ?_, b1, by simp⟩
    refine (s1.comp _).hasSatGL (s2.comp _) h2 ?_
    rw [algSat_sum, algSat_sum, Finset.sum_congr rfl fun i _ => b2 i]
    exact (map_sum (Multiset.mapAddMonoidHom _) _ Finset.univ).symm)
  have := Fintype.card_congr s
  rw [Fintype.card_unit] at this
  omega
