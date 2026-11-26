module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDirOf
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LiMap
public import Lemmata.GeneralBFactLeftTerForm.Imports
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BePhiSmulRight
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ProdProdIte

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDimBCProved
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem restDimBC_proved : RestDimBC C0 CE1 CE2 X := by
  intro aTop _ aPlus _ b _
  set Dd := blockData X.p (X.S C0 CE1 CE2) aTop aPlus X.m b with hDd
  set V0 := Submodule.span ℚ_[X.p]
    (((gmB Dd).SSZ X.p (r := X.r) : Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :
      Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) with hV0
  set W := Submodule.span (KK X.O) ((Dd.SSZ X.O (r := X.r) : Submodule X.O (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) :
      Set (MvPolynomial (BVar (2 * X.s + 1) X.r Dd.T.t) (KK X.O))) with hW
  show Module.finrank ℚ_[X.p] V0 ≤ Module.finrank (KK X.O) W
  have : FiniteDimensional (KK X.O) W := span_SSZ_finite Dd
  by_cases hfin : FiniteDimensional ℚ_[X.p] V0
  swap
  · rw [Module.finrank_of_not_finite hfin]
    exact Nat.zero_le _

  have hmemW : ∀ x ∈ V0, MvPolynomial.map (iotaX X) x ∈ W := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact map_SSZ (ι := iotaX X) (iotaX_int X) Dd x hx
    | zero => rw [map_zero]; exact W.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact W.add_mem hx hy
    | smul a x _ hx => rw [map_smul_Q]; exact W.smul_mem _ hx
  set bs := Module.finBasis ℚ_[X.p] V0
  have hli : LinearIndependent ℚ_[X.p] (fun i => (bs i : MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gmB Dd).T.t) ℚ_[X.p])) :=
    bs.linearIndependent.map' V0.subtype (Submodule.ker_subtype V0)
  have hli2 := li_map (iotaX X) _ hli
  let w : Fin (Module.finrank ℚ_[X.p] V0) → W := fun i => ⟨MvPolynomial.map (iotaX X) (bs i).1, hmemW _ (bs i).2⟩
  have hli3 : LinearIndependent (KK X.O) w := LinearIndependent.of_comp W.subtype hli2
  have h := hli3.fintype_card_le_finrank
  rw [Fintype.card_fin] at h
  exact h

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinrankEqSpanGen
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.G.GLWeightTheory Formalism.MainNotions.G.CountingStatementReduction

section RankSpanGen

variable {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module R V] [Module K V] [IsScalarTower R K V]

theorem span_den_gen (M : Submodule R V) (y : V) (hy : y ∈ Submodule.span K (M : Set V)) :
    ∃ s : R, s ≠ 0 ∧ s • y ∈ M := by
  first | exact Bl.general_b_fact_left_ter_form.goal1 .. | (apply Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_left_ter_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_left_ter_form.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M y hy | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M y | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› M | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V ‹_› | exact @Bl.general_b_fact_left_ter_form.goal1 R K V | exact @Bl.general_b_fact_left_ter_form.goal1 R K | exact @Bl.general_b_fact_left_ter_form.goal1 R

def toSpanG (M : Submodule R V) : M →ₗ[R] (Submodule.span K (M : Set V)) where
  toFun x := ⟨x.1, Submodule.subset_span x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance toSpanG_loc (M : Submodule R V) : IsLocalizedModule (nonZeroDivisors R) (toSpanG (K := K) M) := by
  refine IsLocalizedModule.mk ?_ ?_ ?_
  · intro x
    have hx0 : (x : R) ≠ 0 := nonZeroDivisors.ne_zero x.2
    have hxK : algebraMap R K x ≠ 0 :=
      (map_ne_zero_iff (algebraMap R K) (IsFractionRing.injective R K)).2 hx0
    rw [Module.End.isUnit_iff]
    constructor
    · intro y z hyz
      simp only [Module.algebraMap_end_apply] at hyz
      rw [← algebraMap_smul K (x : R) y, ← algebraMap_smul K (x : R) z] at hyz
      exact smul_right_injective _ hxK hyz
    · intro y
      refine ⟨(algebraMap R K x)⁻¹ • y, ?_⟩
      simp only [Module.algebraMap_end_apply]
      rw [← algebraMap_smul K (x : R), smul_smul, mul_inv_cancel₀ hxK, one_smul]
  · intro y
    obtain ⟨s, hs, hsy⟩ := span_den_gen (K := K) M y.1 y.2
    exact ⟨(⟨s • y.1, hsy⟩, ⟨s, mem_nonZeroDivisors_of_ne_zero hs⟩), rfl⟩
  · intro x₁ x₂ h
    refine ⟨1, ?_⟩
    have : x₁ = x₂ := Subtype.ext (congrArg (fun z : Submodule.span K (M : Set V) => (z : V)) h)
    rw [this]

theorem finrank_eq_span_gen (M : Submodule R V) :
    Module.finrank R M = Module.finrank K (Submodule.span K (M : Set V)) := by
  unfold Module.finrank
  rw [IsLocalization.rank_eq K (nonZeroDivisors R) le_rfl]
  rw [(IsLocalizedModule.rank_eq (nonZeroDivisors R) le_rfl (toSpanG (K := K) M)).symm]

end RankSpanGen

def RestYbc : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] (p : ℕ) [Fact p.Prime] (ι : ℚ_[p] →+* KK O) (N r : ℕ) [NeZero r]
    (LL : ChainLetters N) (q : ℕ) (J : Fin q → ℕ) (M : Fin q → WithTop ℤ),
    ∀ y ∈ YjtZ O (r := r) LL J M,
      y ∈ Submodule.span (KK O) (map ι '' (Formalism.GM.M.YZ p (r := r) (gmL LL) J M : Set (MvPolynomial (Fin N × Fin r) ℚ_[p])))

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PlusAWICondition
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.ProjS

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem mono_mem_xiPolZ (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    monomial m (1 : ℚ_[p]) ∈ Formalism.GM.M.XiPolZ p N r G.T.t n := by
  classical
  obtain ⟨h1, h2, -⟩ := xiMons_spec (r := r) G n m hm
  refine Submodule.mem_inf.2 ⟨?_, ?_⟩
  · rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff]
    intro m' hm'
    have hm2 : m' = m := Finset.mem_singleton.1 (support_monomial_subset hm')
    subst hm2
    exact ⟨h1, h2⟩
  · exact ⟨monomial m 1, by simp⟩

theorem pderiv_chain_mono (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n)
    (a : Fin N) (c : Fin r) : pderiv (Sum.inl (Fin.castSucc a, c)) (monomial m (1 : ℚ_[p])) = 0 := by
  obtain ⟨h1, -, -⟩ := xiMons_spec (r := r) G n m hm
  rw [pderiv_monomial]
  have : m (Sum.inl (Fin.castSucc a, c)) = 0 := by
    by_contra hne
    obtain ⟨d, hd⟩ := h1 _ (Finsupp.mem_support_iff.2 hne)
    simp only [Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hd
    exact absurd hd.1 (Fin.castSucc_ne_last a)
  rw [this]
  simp

theorem mono_chain_zero (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n)
    (x : Fin N × Fin r) : m (Formalism.GM.M.chainEmb N r G.T.t x) = 0 := by
  obtain ⟨h1, -, -⟩ := xiMons_spec (r := r) G n m hm
  by_contra hne
  obtain ⟨d, hd⟩ := h1 _ (Finsupp.mem_support_iff.2 hne)
  simp only [Formalism.GM.M.chainEmb, Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hd
  exact absurd hd.1 (Fin.castSucc_ne_last x.1)

theorem chainEmb_inj : Function.Injective (Formalism.GM.M.chainEmb N r G.T.t) := by
  intro x y h
  simp only [Formalism.GM.M.chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
  exact Prod.ext (Fin.castSucc_injective _ h.1) h.2

theorem cf_mul (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ) (hm : m ∈ xiMons (r := r) G n) :
    (((n.factorial / (m.prod fun _ k => k.factorial) : ℕ) : ℚ_[p]) * (mfac m : ℚ_[p])) = (n.factorial : ℚ_[p]) := by
  obtain ⟨-, -, h3⟩ := xiMons_spec (r := r) G n m hm
  have hdvd : (m.prod fun _ k => k.factorial) ∣ n.factorial := by
    have := Nat.prod_factorial_dvd_factorial_sum m.support m
    rw [h3] at this
    exact this
  have e : (mfac m : ℚ_[p]) = ((m.prod fun _ k => k.factorial : ℕ) : ℚ_[p]) := by
    unfold mfac Finsupp.prod
    push_cast
    rfl
  rw [e, ← Nat.cast_mul, Nat.div_mul_cancel hdvd]

theorem plusAW_of_blockOK (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (D : ℤ) : RestPlusAW p (r := r) G j jp D := by
  classical
  unfold RestPlusAW
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p
    (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
    (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D
  have hcard : (xiMons (r := r) G (G.B - jp)).card = dXi r (G.B - jp) := card_xiMons_eq (r := r) G (G.B - jp)
  let e := Fintype.equivFin (Fin (Formalism.GM.M.goodCount p
    (fun F F' => Formalism.GM.M.fockN p (G.lettersAt j jp) (G.T.phis p (r := r) (G.lettersAt j jp) F) F')
    (Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr) D) × (xiMons (r := r) G (G.B - jp)))
  let cfn : (Formalism.GM.M.BVar N r G.T.t →₀ ℕ) → ℕ := fun m => (G.B - jp).factorial / (m.prod fun _ k => k.factorial)
  have hXm : ∀ k, rename (Formalism.GM.M.chainEmb N r G.T.t) (x (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]) ∈
      Ljj p (r := r) G j jp := fun k =>
    Submodule.subset_span ⟨x (e.symm k).1, hx _, _, mono_mem_xiPolZ p (r := r) G (G.B - jp) _ (e.symm k).2.2, rfl⟩
  have hYm : ∀ k, ((cfn (e.symm k).2.1 : ℕ) : ℚ_[p]) •
      (rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p])) ∈
      Ljj p (r := r) G j jp := by
    intro k
    have h1 : rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]) ∈
        Ljj p (r := r) G j jp :=
      Submodule.subset_span ⟨y (e.symm k).1, hy _, _, mono_mem_xiPolZ p (r := r) G (G.B - jp) _ (e.symm k).2.2, rfl⟩
    have h2 := Submodule.smul_mem (Ljj p (r := r) G j jp) ((cfn (e.symm k).2.1 : ℕ) : ℤ_[p]) h1
    rw [algebra_compatible_smul ℚ_[p] ((cfn (e.symm k).2.1 : ℕ) : ℤ_[p]), map_natCast] at h2
    exact h2
  have hpair : ∀ k k', bePhi p (r := r) G j jp
      (rename (Formalism.GM.M.chainEmb N r G.T.t) (x (e.symm k).1) * monomial (e.symm k).2.1 (1 : ℚ_[p]))
      (((cfn (e.symm k').2.1 : ℕ) : ℚ_[p]) •
        (rename (Formalism.GM.M.chainEmb N r G.T.t) (y (e.symm k').1) * monomial (e.symm k').2.1 (1 : ℚ_[p]))) =
      if k = k' then (p : ℚ_[p]) ^ D else 0 := by
    intro k k'
    obtain ⟨⟨i, m, hm⟩, hk⟩ : ∃ q, e.symm k = q := ⟨_, rfl⟩
    obtain ⟨⟨i', m', hm'⟩, hk'⟩ : ∃ q, e.symm k' = q := ⟨_, rfl⟩
    have hkk : k = k' ↔ (i = i' ∧ m = m') := by
      constructor
      · rintro rfl
        rw [hk] at hk'
        simp only [Prod.mk.injEq, Subtype.mk.injEq] at hk'
        exact hk'
      · rintro ⟨rfl, rfl⟩
        exact e.symm.injective (hk.trans hk'.symm)
    rw [hk, hk']
    dsimp only
    rw [bePhi_smul_right]
    unfold bePhi
    rw [phisB_rename_mul p (r := r) G hB j jp _ _ (fun a c => pderiv_chain_mono p (r := r) G (G.B - jp) m hm a c),
      fockK_rename_mul _ (chainEmb_inj (r := r) G) _ _ m m' 1 (mono_chain_zero (r := r) G (G.B - jp) m hm)
        (mono_chain_zero (r := r) G (G.B - jp) m' hm')]
    have hxy' : Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
        ∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p]) = if i = i' then (p : ℚ_[p]) ^ D else 0 := hxy i i'
    by_cases hmm : m = m'
    · subst hmm
      rw [if_pos rfl]
      have hcf := cf_mul p (r := r) G (G.B - jp) m hm
      have hdeg : (degFact G j jp : ℚ_[p]) =
          (∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]) := by
        unfold degFact; push_cast; rfl
      have hF : Formalism.GM.M.fockK (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') =
          Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') := rfl
      have hP : (∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) ≠ 0 :=
        Finset.prod_ne_zero_iff.2 fun a _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      have hn0 : ((G.B - jp).factorial : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
      rw [hdeg, hF]
      have key : ((cfn m : ℕ) : ℚ_[p]) *
          (1 * mfac m * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
            ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]))) =
          Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
            ∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p]) := by
        rw [show ((cfn m : ℕ) : ℚ_[p]) *
            (1 * mfac m * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
              ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p]))) =
            (((cfn m : ℕ) : ℚ_[p]) * mfac m) * Formalism.GM.M.fock p (G.T.phis p (r := r) (G.lettersAt j jp) (x i)) (y i') /
              ((∏ a, (((G.lettersAt j jp).deg a).factorial : ℚ_[p])) * ((G.B - jp).factorial : ℚ_[p])) by ring]
        rw [hcf]
        field_simp
      rw [key, hxy']
      by_cases hii : i = i'
      · rw [if_pos hii, if_pos (hkk.2 ⟨hii, rfl⟩)]
      · rw [if_neg hii, if_neg (fun h => hii (hkk.1 h).1)]
    · rw [if_neg hmm, if_neg (fun h => hmm (hkk.1 h).2)]
      simp
  have hmem := le_csSup (gcL_bdd p (r := r) G j jp D) ⟨fun k => _, fun k => _, hXm, hYm, hpair⟩
  rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, hcard] at hmem
  exact hmem

end Level

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

theorem plusAWICondition (CM : ℝ) : RestPlusAWI C0 CE1 CE2 X CM := by
  intro dl _ aTop _ x _
  exact plusAW_of_blockOK X.p (gB C0 CE1 CE2 X aTop 0 x.1) (gB_blockOK C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2 _

theorem plusACondition (CM : ℝ) : RestPlusA C0 CE1 CE2 X CM :=
  restPlusA_of C0 CE1 CE2 X CM (plusAWICondition C0 CE1 CE2 X CM)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.FinPosEqCast
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open Finset Formalism.GM Formalism.GM.M
open scoped Nat

section Block

variable (p : ℕ) [hp : Fact p.Prime] {N r : ℕ} [NeZero r] (G : M.BlockData N)

def dTot (a : Fin (N + 1)) : ℕ :=
  (∑ i, G.T.z i • (if M.finPos N (G.T.pos i) = a then 1 else 0)) +
    G.zPlus • (if Fin.castSucc G.uPos = a then 1 else 0) + chDeg G.LL a + (if Fin.last N = a then G.B else 0)

theorem chDeg_cast (LL : M.Letters N) (a0 : Fin N) : chDeg LL (Fin.castSucc a0) = LL.deg a0 := by
  unfold chDeg
  rw [Finset.sum_eq_single a0]
  · simp
  · intro b _ hb
    rw [if_neg]
    intro h
    exact hb (Fin.castSucc_injective _ h)
  · intro h
    exact absurd (Finset.mem_univ a0) h

theorem chDeg_last (LL : M.Letters N) : chDeg LL (Fin.last N) = 0 := by
  unfold chDeg
  apply Finset.sum_eq_zero
  intro b _
  rw [if_neg]
  exact Fin.castSucc_ne_last b

theorem finPos_eq_cast (k : ℕ) (hk : k < N) (a0 : Fin N) : M.finPos N k = Fin.castSucc a0 ↔ (a0 : ℕ) = k := by
  unfold M.finPos
  rw [Fin.ext_iff]
  simp only [Fin.coe_castSucc]
  rw [min_eq_left hk.le]
  exact eq_comm

theorem finPos_ne_last (k : ℕ) (hk : k < N) : M.finPos N k ≠ Fin.last N := by
  unfold M.finPos
  rw [Ne, Fin.ext_iff]
  simp only [Fin.val_last]
  rw [min_eq_left hk.le]
  exact hk.ne

theorem level_room (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp) (a0 : Fin N) :
    (∑ i, if (a0 : ℕ) = G.T.pos i ∨ (a0 : ℕ) = G.T.pos i + 1 then j i else 0) + (if a0 = G.uPos then jp else 0) ≤
      G.LL.deg a0 := by
  obtain ⟨⟨hmono, hvec, _⟩, hlt, _, _⟩ := hB
  obtain ⟨hj, hjp⟩ := hl
  have hdisj : ∀ b c : Fin G.T.t, G.T.pos b + 1 ≠ G.T.pos c := by
    intro b c h
    obtain ⟨hb1, _, hbf⟩ := hvec b
    obtain ⟨hc1, hct, _⟩ := hvec c
    have e : (⟨G.T.pos b + 1, hb1⟩ : Fin N) = ⟨G.T.pos c, by omega⟩ := Fin.ext h
    rw [e] at hbf
    rw [hbf] at hct
    exact Bool.false_ne_true hct
  by_cases hu : a0 = G.uPos
  · rw [if_pos hu, Finset.sum_eq_zero]
    · rw [hu]
      omega
    intro i _
    rw [if_neg]
    have h1 := hlt i
    have h2 : (a0 : ℕ) = G.uPos := by rw [hu]
    omega
  · rw [if_neg hu, add_zero]
    by_cases hex : ∃ i, (a0 : ℕ) = G.T.pos i ∨ (a0 : ℕ) = G.T.pos i + 1
    · obtain ⟨i0, hi0⟩ := hex
      rw [Finset.sum_eq_single i0]
      · rw [if_pos hi0]
        obtain ⟨hN0, _, _⟩ := hvec i0
        rcases hi0 with h | h
        · exact (hj i0).1.trans_eq (congrArg G.LL.deg (Fin.ext (by simp; omega)))
        · exact (hj i0).2.trans_eq (congrArg G.LL.deg (Fin.ext (by simp; omega)))
      · intro b _ hb
        rw [if_neg]
        intro hb'
        rcases hb' with h1 | h1 <;> rcases hi0 with h2 | h2
        · exact hb (hmono.injective (by omega))
        · exact hdisj i0 b (by omega)
        · exact hdisj b i0 (by omega)
        · exact hb (hmono.injective (by omega))
      · intro h'
        exact absurd (Finset.mem_univ i0) h'
    · push_neg at hex
      rw [Finset.sum_eq_zero]
      · exact Nat.zero_le _
      intro i _
      rw [if_neg]
      intro h
      rcases h with h | h
      · exact (hex i).1 h
      · exact (hex i).2 h

theorem dLvl_eq (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp) (a : Fin (N + 1)) :
    dLvl G j jp a = dTot G a := by
  have hvec := hB.1.2.1
  have hjp := hl.2
  have hposN : ∀ i, G.T.pos i + 1 < N := fun i => (hvec i).1
  induction a using Fin.lastCases with
  | last =>
    have hA : (∑ i, j i • ((if M.finPos N (G.T.pos i) = Fin.last N then 1 else 0) +
        (if M.finPos N (G.T.pos i + 1) = Fin.last N then 1 else 0))) = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [if_neg (finPos_ne_last _ (by have := hposN i; omega)), if_neg (finPos_ne_last _ (hposN i))]
      simp
    have hu : ¬ Fin.castSucc G.uPos = Fin.last N := Fin.castSucc_ne_last _
    unfold dLvl dTot
    rw [hA, chDeg_last, chDeg_last, if_neg hu, if_pos rfl, if_pos rfl, if_pos rfl]
    simp only [smul_eq_mul]
    omega
  | cast a0 =>
    have hA : (∑ i, j i • ((if M.finPos N (G.T.pos i) = Fin.castSucc a0 then 1 else 0) +
        (if M.finPos N (G.T.pos i + 1) = Fin.castSucc a0 then 1 else 0))) =
        ∑ i, if (a0 : ℕ) = G.T.pos i ∨ (a0 : ℕ) = G.T.pos i + 1 then j i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      have e1 := finPos_eq_cast (G.T.pos i) (by have := hposN i; omega) a0
      have e2 := finPos_eq_cast (G.T.pos i + 1) (hposN i) a0
      by_cases h1 : (a0 : ℕ) = G.T.pos i
      · have h2 : ¬ (a0 : ℕ) = G.T.pos i + 1 := by omega
        simp only [e1, e2, h1, h2, if_true, if_false, or_false]
        simp
      · by_cases h2 : (a0 : ℕ) = G.T.pos i + 1
        · simp only [e1, e2, h1, h2, if_true, if_false, or_true]
          simp
        · simp only [e1, e2, h1, h2, if_false, or_false]
          simp
    have hB' : jp • ((if Fin.castSucc G.uPos = Fin.castSucc a0 then 1 else 0) +
        (if Fin.last N = Fin.castSucc a0 then 1 else 0)) = if a0 = G.uPos then jp else 0 := by
      have hL : ¬ Fin.last N = Fin.castSucc a0 := fun h => Fin.castSucc_ne_last a0 h.symm
      rw [if_neg hL]
      by_cases h : a0 = G.uPos
      · rw [if_pos (by rw [h]), if_pos h]
        simp
      · rw [if_neg (fun e => h (Fin.castSucc_injective _ e).symm), if_neg h]
        simp
    have hC : chDeg (G.lettersAt j jp) (Fin.castSucc a0) =
        (G.LL.deg a0 - ∑ i, if (a0 : ℕ) = G.T.pos i ∨ (a0 : ℕ) = G.T.pos i + 1 then j i else 0) -
          (if a0 = G.uPos then jp else 0) := by
      rw [chDeg_cast]
      rfl
    have hD := level_room G hB j jp hl a0
    have hL : ¬ Fin.last N = Fin.castSucc a0 := fun h => Fin.castSucc_ne_last a0 h.symm
    unfold dLvl dTot
    rw [hA, hB', hC, chDeg_cast, if_neg hL, if_neg hL]
    omega

theorem sum_ite_inj_le {ι α : Type} [Fintype ι] [DecidableEq α] (x : ι → α) (hx : Function.Injective x) (n : ι → ℕ)
    (a : α) (Mx : ℕ) (h : ∀ i, n i ≤ Mx) : ∑ i, n i • (if x i = a then 1 else 0) ≤ Mx := by
  by_cases hex : ∃ i, x i = a
  · obtain ⟨i0, hi0⟩ := hex
    rw [Finset.sum_eq_single i0]
    · simp [hi0, h i0]
    · intro b _ hb
      rw [if_neg]
      · simp
      intro hba
      exact hb (hx (hba.trans hi0.symm))
    · intro h'
      exact absurd (Finset.mem_univ i0) h'
  · push_neg at hex
    rw [Finset.sum_eq_zero]
    · exact Nat.zero_le _
    intro i _
    simp [hex i]

theorem dTot_le (hB : G.BlockOK) (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A)
    (hz : ∀ i, G.T.z i ≤ 2 * A) (hzp : G.zPlus ≤ 2 * A) (a : Fin (N + 1)) : dTot G a ≤ 8 * A := by
  classical
  have hpN : ∀ i, G.T.pos i + 1 < N := fun i => (hB.2.1 i).trans G.uPos.2
  have hinj : Function.Injective (fun i => M.finPos N (G.T.pos i)) := by
    intro i i' h
    have h' : min (G.T.pos i) N = min (G.T.pos i') N := congrArg Fin.val h
    have h1 := hpN i
    have h2 := hpN i'
    exact hB.1.1.injective (by omega)
  have e1 := sum_ite_inj_le (fun i => M.finPos N (G.T.pos i)) hinj G.T.z a (2 * A) hz
  have e2 : G.zPlus • (if Fin.castSucc G.uPos = a then 1 else 0) ≤ 2 * A := by
    split_ifs <;> simp [hzp]
  have e3 : chDeg G.LL a ≤ 2 * A := by
    induction a using Fin.lastCases with
    | last => rw [chDeg_last]; exact Nat.zero_le _
    | cast a0 => rw [chDeg_cast]; exact hdeg a0
  have e4 : (if Fin.last N = a then G.B else 0) ≤ 2 * A := by
    split_ifs
    · exact hBa
    · exact Nat.zero_le _
  unfold dTot
  omega

theorem val_gen (hB : G.BlockOK) (A : ℕ) (hdeg : ∀ x, G.LL.deg x ≤ 2 * A) (hBa : G.B ≤ 2 * A)
    (hz : ∀ i, G.T.z i ≤ 2 * A) (hzp : G.zPlus ≤ 2 * A)
    (j : Fin G.T.t → ℕ) (jp : ℕ) (hl : G.LevelOK j jp) (j' : Fin G.T.t → ℕ) (jp' : ℕ) (hl' : G.LevelOK j' jp')
    (μ : M.BVar N r G.T.t →₀ ℕ) (hw : ∀ a, Finsupp.weight (wL (r := r) G a) μ = dLvl G j' jp' a) :
    padicValNat p (lvC (r := r) G j jp * degFact G j jp) ≤ padicValNat p (μ.prod fun _ k => k !) +
      (((N + 1) * r + (G.T.t + 1) * 2) + (G.T.t + 1)) * Nat.log p (8 * A + r) := by
  have hL : ∀ n, n ≤ 8 * A + r → Nat.log p n ≤ Nat.log p (8 * A + r) :=
    fun n hn => Nat.log_mono_right hn
  have hld : ∀ x, (G.lettersAt j jp).deg x ≤ 2 * A := by
    intro x
    have := hdeg x
    simp only [M.BlockData.lettersAt]
    omega
  have hj : ∀ i, j i ≤ 2 * A := fun i => (hl.1 i).1.trans (hdeg _)
  have h1 := val_lvC_le (r := r) p G j jp (Nat.log p (8 * A + r))
    (fun i => hL _ (by
      have := hld (G.letterAt (G.T.pos i))
      have := hld (G.letterAt (G.T.pos i + 1))
      have := hz i
      have := hj i
      omega))
    (hL _ (by
      have := hdeg G.uPos
      have := hl.2
      have := hzp
      have := hBa
      omega))
  have h2 := val_letters_le p G μ (dLvl G j' jp') hw (Nat.log p (8 * A + r))
    (fun a => hL _ (by
      rw [dLvl_eq G hB j' jp' hl' a]
      have := dTot_le G hB A hdeg hBa hz hzp a
      omega))
  have hprod : ∏ a, (dLvl G j jp a)! = ∏ a, (dLvl G j' jp' a)! := by
    apply Finset.prod_congr rfl
    intro a _
    rw [dLvl_eq G hB j jp hl a, dLvl_eq G hB j' jp' hl' a]
  rw [hprod] at h1
  rw [Nat.add_mul ((N + 1) * r + (G.T.t + 1) * 2) (G.T.t + 1)]
  omega

end Block

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end
