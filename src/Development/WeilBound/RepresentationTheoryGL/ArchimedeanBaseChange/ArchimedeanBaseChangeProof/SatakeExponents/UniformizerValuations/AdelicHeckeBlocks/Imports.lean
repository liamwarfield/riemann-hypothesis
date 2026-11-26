module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.RStabApply
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PPositions
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PFinConv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.DoubleSumFinprodFactor
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PGrowth
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IntegrableCut
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsCompactMaximalPairPlace
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocOk
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.PLocComm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.LocalOperatorSums.LocOp3
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveFinal
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.BlkGrowth

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.IsHeckeSmul
noncomputable section

open NumberField IsDedekindDomain Matrix Filter
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun PositivityTheory.Rg.BcB.F.F5 PositivityTheory.Rg.BcB.F.Eig PositivityTheory.Rg.BcB.G8 PositivityTheory.Rg.BcN.F2 PositivityTheory.Rg.BcB.F.Tail PositivityTheory.Rg.Bc.ArchbcB.B
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F

namespace PSeen

set_option linter.unusedSectionVars false

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem isHecke_smul {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (c : ℂ) {f : G → ℂ}
    (h : IsHecke K f) : IsHecke K (c • f) := by
  have := LocComm.isHecke_sum K ({()} : Finset Unit) (fun _ => c) (fun _ => f) (fun _ _ => h)
  convert this using 1
  funext y
  simp

theorem isHecke_fsum {G ι : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (s : Finset ι)
    (g : ι → G → ℂ) (h : ∀ i ∈ s, IsHecke K (g i)) : IsHecke K (∑ i ∈ s, g i) := by
  have := LocComm.isHecke_sum K s (fun _ => 1) g h
  convert this using 1
  funext y
  simp [Finset.sum_apply]

theorem mconv_hecke {a b : ℕ} {w : Pl E} (K : Subgroup (GLw a w × GLw b w)) {f g : LF a b w}
    (hf : IsHecke K f) (hg : IsHecke K g) : IsHecke K (mconv f g) := by
  have := FinConv.cv_hecke ((GlobalTheory.LFun.KGL w (n := a)).prod (GlobalTheory.LFun.KGL w (n := b))) K K f g hf hg
  rw [inf_idem] at this
  exact this

variable {n : ℕ} (d : LocData E n)

theorem notGood {w : Pl E} (hw : w ∈ d.B) : ¬ d.Good w := by
  rintro ⟨-, hT, hS, hB, -⟩
  simp only [LocData.B, Finset.mem_union] at hw
  tauto

theorem L_ok (hd : d.Ok) {a : ℕ} (ha : a ≤ n) {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) :
    IsOpen (d.L a w : Set (GLw a w × GLw (n - a) w)) ∧ d.L a w ≤ K2 a (n - a) w := by
  obtain ⟨L₁, L₂, e, h1, h2⟩ := hd.L a ha w hw
  rw [e]
  refine ⟨?_, Subgroup.prod_mono h1.2.1 h2.2.1⟩
  rw [Subgroup.coe_prod]
  exact h1.1.prod h2.1

theorem lev₂_ok (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (w : Pl E) :
    IsOpen (d.lev₂ a w : Set (GLw a w × GLw (n - a) w)) ∧ d.lev₂ a w ≤ K2 a (n - a) w := by
  unfold LocData.lev₂
  split_ifs with h
  · exact L_ok d hd ha h
  · exact ⟨LocComm.isOpen_levelSubgroup' _ _ _, le_rfl⟩

theorem notT (hd : d.Ok) {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) : w ∉ d.T := by
  intro hT
  rcases Finset.mem_union.1 hw with h | h
  · exact Finset.disjoint_left.1 hd.disj.1 hT h
  · exact Finset.disjoint_left.1 hd.disj.2.1 hT h

theorem lev_eq (hd : d.Ok) {a : ℕ} {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) : d.lev a w = d.L a w := by
  simp [LocData.lev, notT d hd hw, hw]

theorem lev₂_eq {a : ℕ} {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) : d.lev₂ a w = d.L a w := by
  simp [LocData.lev₂, hw]

theorem isLetter_t_eq_idem_lev₂ {a : ℕ} {ha : a ≤ n} {L : LM d.kap a (n - a)} (hL : d.IsLetter a ha L) {w : Pl E}
    (hw : w ∈ d.B) : L.t w = idem (d.lev₂ a w) := by
  have hG := notGood d hw
  have gt : ∀ {L' : LM d.kap a (n - a)}, d.IsGen a ha L' → L'.t w = idem (d.lev₂ a w) := by
    intro L' hL'
    rcases LocComm.generator_second_levi_position d hL' w with h | ⟨h, -⟩
    · exact h
    · exact absurd h hG
  rcases hL with hg | ⟨L', hg, rfl⟩ | rfl | rfl
  · exact gt hg
  · show lfStar (L'.t w) = _
    rw [gt hg, LocComm.lfStar_idem]
  · rfl
  · rfl

theorem prod_t (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (ls : List (LM d.kap a (n - a))) (hls : ∀ L ∈ ls, d.IsLetter a ha L)
    {w : Pl E} (hw : w ∈ d.B) : (ls.foldr LM.mul (d.eL a)).t w = idem (d.lev₂ a w) := by
  induction ls with
  | nil => rfl
  | cons L ls ih =>
    have ih' := ih fun L' h => hls L' (List.mem_cons_of_mem _ h)
    show mconv (L.t w) ((ls.foldr LM.mul (d.eL a)).t w) = _
    rw [isLetter_t_eq_idem_lev₂ d (hls L (List.mem_cons_self ..)) hw, ih']
    obtain ⟨ho, hle⟩ := lev₂_ok d hd ha w
    obtain ⟨hI, -, hf⟩ := idemAlg E a (n - a) w _ ho hle
    exact (hf _ hI).1

def Inv {a : ℕ} (w : Pl E) (L : LM d.kap a (n - a)) : Prop :=
  (w ∈ d.S₀ → ∀ x y, IsHecke (d.L a w) (L.m w x y)) ∧ (w ∈ d.Bad → IsHecke (d.L a w) (L.s w))

theorem inv_mul {a : ℕ} {w : Pl E} {L L' : LM d.kap a (n - a)} (h : Inv d w L) (h' : Inv d w L') :
    Inv d w (L.mul L') := by
  refine ⟨fun hS x y => ?_, fun hB => ?_⟩
  · show IsHecke _ (∑ z, mconv (L.m w x z) (L'.m w z y))
    exact isHecke_fsum _ _ _ fun z _ => mconv_hecke _ (h.1 hS x z) (h'.1 hS z y)
  · exact mconv_hecke _ (h.2 hB) (h'.2 hB)

theorem inv_letter (h3 : LocOpUniformizer E) (hd : d.Ok) {a : ℕ} {ha : a ≤ n} {L : LM d.kap a (n - a)}
    (hL : d.IsLetter a ha L) {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) : Inv d w L := by
  have hwB : w ∈ d.B := by
    simp only [LocData.B, Finset.mem_union] at hw ⊢
    tauto
  have hG := notGood d hwB
  have hlev := lev_eq d hd (a := a) hw
  obtain ⟨ho, hle⟩ := L_ok d hd ha hw
  obtain ⟨hI, -, -⟩ := idemAlg E a (n - a) w _ ho hle
  have eM : ∀ x y, IsHecke (d.L a w) ((d.eL a).m w x y) := by
    intro x y
    show IsHecke _ (d.diag (fun _ => idem (d.lev a w)) x y)
    unfold LocData.diag
    rw [hlev]
    split_ifs
    · exact hI
    · exact LocComm.isHecke_zero _
  have gs : ∀ {L' : LM d.kap a (n - a)}, d.IsGen a ha L' → L'.s w = idem (d.L a w) := by
    intro L' hL'
    rcases LocComm.generator_first_levi_position d hL' w with h | ⟨h, -⟩
    · rw [h, hlev]
    · exact absurd h hG
  rcases hL with hg | ⟨L', hg, rfl⟩ | rfl | rfl
  · refine ⟨fun _ x y => ?_, fun _ => ?_⟩
    · rw [LocComm.gen_m d hg]
      exact eM x y
    · rw [gs hg]
      exact hI
  · refine ⟨fun _ x y => ?_, fun _ => ?_⟩
    · rw [LocComm.adj_m d hg]
      exact eM x y
    · show IsHecke _ (lfStar (L'.s w))
      rw [gs hg, LocComm.lfStar_idem]
      exact hI
  · refine ⟨fun hS x y => ?_, fun _ => ?_⟩
    · have := LocComm.hecke_beta d h3 hd ha (Finset.mem_union_right _ hS) x y
      rwa [hlev] at this
    · show IsHecke _ (idem (d.lev a w))
      rw [hlev]
      exact hI
  · refine ⟨fun _ x y => ?_, fun hB => ?_⟩
    · show IsHecke _ (d.diag (fun _ => if w ∈ d.T then idem (d.lev a w) else d.sgn a w • idem (d.lev a w)) x y)
      unfold LocData.diag
      rw [hlev]
      split_ifs
      · exact hI
      · exact isHecke_smul _ _ hI
      · exact LocComm.isHecke_zero _
    · show IsHecke _ (if w ∈ d.Bad then d.fix a w else idem (d.lev a w))
      rw [if_pos hB]
      exact hd.fix a ha w hB

theorem inv_prod (h3 : LocOpUniformizer E) (hd : d.Ok) {a : ℕ} (ha : a ≤ n) (ls : List (LM d.kap a (n - a)))
    (hls : ∀ L ∈ ls, d.IsLetter a ha L) {w : Pl E} (hw : w ∈ d.S₀ ∪ d.Bad) :
    Inv d w (ls.foldr LM.mul (d.eL a)) := by
  induction ls with
  | nil =>
    have := inv_letter d h3 hd (ha := ha) (L := d.eL a) (Or.inl (Or.inl rfl)) hw
    exact this
  | cons L ls ih =>
    exact inv_mul d (inv_letter d h3 hd (hls L (List.mem_cons_self ..)) hw)
      (ih fun L' h => hls L' (List.mem_cons_of_mem _ h))

end PSeen

open PSeen in
theorem seenTr (h3 : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], LocOpUniformizer E) : SeenTr := by
  intro E _ _ _ n d hd a ha ls N hls w hwB
  have ht := prod_t d hd ha ls hls hwB
  refine ⟨ht, fun hc => ?_⟩
  by_cases hs : IsSplitAt w
  · have hT : w ∉ d.T := fun h => hc h hs
    have hw : w ∈ d.S₀ ∪ d.Bad := by
      simp only [LocData.B, Finset.mem_union] at hwB
      exact Finset.mem_union.2 (by tauto)
    have hinv := inv_prod d (h3 E) hd ha ls hls hw
    obtain ⟨ho, hle⟩ := L_ok d hd ha hw
    obtain ⟨-, -, hf⟩ := idemAlg E a (n - a) w _ ho hle
    have hH : IsHecke (d.L a w) ((ls.foldr LM.mul (d.eL a)).tr d.P N w) := by
      unfold LM.tr
      split_ifs with hP
      · have hS : w ∈ d.S₀ := by
          simp only [LocData.P, Finset.mem_union] at hP
          tauto
        exact isHecke_fsum _ _ _ fun x _ => isHecke_fsum _ _ _ fun y _ => isHecke_smul _ _ (hinv.1 hS x y)
      · have hB : w ∈ d.Bad := by
          simp only [LocData.P, Finset.mem_union] at hP
          rcases Finset.mem_union.1 hw with h | h
          · exact absurd (Or.inr h) hP
          · exact h
        exact hinv.2 hB
    have key := (hf _ hH).2.1
    rw [← lev₂_eq d hw] at key
    funext y
    simp only [seen, if_pos hs, ht]
    exact congrFun key y
  · funext y
    simp only [seen, if_neg hs]

end PositivityTheory.Rg.BcB.F

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.AdelicHeckeBlocks.SelfAdj
noncomputable section

open MeasureTheory Matrix Finset Filter Topology
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC
open GlobalTheory.CompanionTheory.WaveMult

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.F.SelfK

open GlobalTheory.CompanionTheory.WaveMult.KerAdj

theorem self_adj (hL : LgFacts) (hU : Unimod) (hR : RCalc) (hS : WaveSpeed) (hE : WaveEx) (hQ : KerUniq) (n : ℕ)
    [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure] (E : KMod n) (g : ℝ → ℝ) (T : ℝ)
    (k : Mat n → (E.V →L[ℂ] E.V)) (hb : IsBump g T) (hk : IsKer μ E [] g k) :
    haveI := FiniteDimensional.complete ℂ E.V
    ∀ y ∈ GLs n, ContinuousLinearMap.adjoint (k y⁻¹) = k y := by
  haveI := FiniteDimensional.complete ℂ E.V
  obtain ⟨c, hc⟩ : ∃ c : Fin 1 → ℂ, c = fun _ => 1 := ⟨_, rfl⟩
  obtain ⟨K, hKk⟩ : ∃ K : Fin 1 → Mat n → (E.V →L[ℂ] E.V), K = fun _ => k := ⟨_, rfl⟩
  have hK : ∀ i : Fin 1, IsKer μ E ((fun _ => []) i) g (K i) := fun i => by rw [hKk]; exact hk
  have hw : ∀ a b : Mat n → E.V, ContDiffOn ℝ ∞ a (GLs n) → ContDiffOn ℝ ∞ b (GLs n) → Cpt a → Cpt b →
      ∫ y : G n, ⟪zOp [] a y.val, b y.val⟫_ℂ ∂μ =
        ∑ i : Fin 1, c i * ∫ y : G n, ⟪a y.val, zOp ((fun _ => []) i) b y.val⟫_ℂ ∂μ := by
    intro a b _ _ _ _
    simp [hc, zOp]
  obtain ⟨regp, eqvp⟩ := GlobalTheory.T.kernel_adjoint_regular hL n E k ⟨hk.1.continuousOn, hk.2.1⟩ hk.2.2.1
  have regK : ∀ i, KReg (K i) := fun i => ⟨(hK i).1.continuousOn, (hK i).2.1⟩
  have rp : ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ,
      ContinuousLinearMap.adjoint (k (y * k₂.1)⁻¹) = ContinuousLinearMap.adjoint (k y⁻¹) * E.ρ k₂ := by
    intro y hy k₂
    simpa using eqvp y hy 1 k₂
  have lp : ∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ,
      ContinuousLinearMap.adjoint (k (k₁.1 * y)⁻¹) = E.ρ k₁ * ContinuousLinearMap.adjoint (k y⁻¹) := by
    intro y hy k₁
    simpa using eqvp y hy k₁ 1
  have rK : ∀ i, ∀ y ∈ GLs n, ∀ k₂ : Matrix.unitaryGroup (Fin n) ℂ, K i (y * k₂.1) = K i y * E.ρ k₂ := by
    intro i y hy k₂
    simpa using (hK i).2.2.1 y hy 1 k₂
  have lK : ∀ i, ∀ y ∈ GLs n, ∀ k₁ : Matrix.unitaryGroup (Fin n) ℂ, K i (k₁.1 * y) = E.ρ k₁ * K i y := by
    intro i y hy k₁
    simpa using (hK i).2.2.1 y hy k₁ 1
  have hD : ∀ y ∈ GLs n, ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y = 0 := by
    refine hQ n μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y) (GLs n)
      (GlobalTheory.CompanionTheory.WaveKer.isOpen_GLs n) subset_rfl
      (fun y hy k₂ => GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs hy (GlobalTheory.CompanionTheory.WaveKer.unitary_mem_GLs k₂)) ?_ ?_ ?_
    · exact regp.1.sub (continuousOn_finsetSum _ fun i _ => (regK i).1.const_smul (c i))
    · intro y hy k₂
      simp only [rp y hy k₂, rK _ y hy k₂, sub_mul, Finset.sum_mul, smul_mul_assoc]
    · intro f hf cf _
      have hfc := hf.1.continuousOn
      have ap := GlobalTheory.T.kernel_action_equivariant hL n μ E _ f regp hfc lp
      have aK := fun i => GlobalTheory.T.kernel_action_equivariant hL n μ E (K i) f (regK i) hfc (lK i)
      have hA0 := section_orth_cpt_zero hQ n μ E
        (fun x => act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f x - ∑ i, c i • act μ E (K i) f x)
        (ap.1.sub (continuousOn_finsetSum _ fun i _ => (aK i).1.const_smul (c i)))
        (by
          intro y hy k₂
          set_option synthInstance.maxHeartbeats 100000 in
            simp only [ap.2 y hy k₂, (aK _).2 y hy k₂, map_sub, map_sum, map_smul])
        (by
          intro h hh ch
          have int1 := pair_integrable μ hL ap.1 hh.1.continuousOn ch
          have int2 := fun i => (pair_integrable μ hL (aK i).1 hh.1.continuousOn ch).const_mul (conj (c i))
          have hpt : ∀ y : G n, ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f y.val - ∑ i, c i • act μ E (K i) f y.val, h y.val⟫_ℂ
              = ⟪act μ E (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) f y.val, h y.val⟫_ℂ
                - ∑ i, conj (c i) * ⟪act μ E (K i) f y.val, h y.val⟫_ℂ := by
            intro y
            simp only [inner_sub_left, sum_inner, inner_smul_left]
          simp only [hpt]
          rw [integral_sub int1 (integrable_finsetSum _ fun i _ => int2 i),
            integral_finsetSum _ fun i _ => int2 i]
          simp only [integral_const_mul]
          rw [chain μ hL hU hR hS hE hb hk hw hK hf cf hh ch, sub_self])
      have h1 := hA0 1 (GlobalTheory.CompanionTheory.WaveKer.one_mem_GLs n)
      have h2 := act_eq_sum_of_kernel hL n μ E (ι := Option (Fin 1))
        (fun o => o.elim 1 fun i => -c i)
        (fun o => o.elim (fun y => ContinuousLinearMap.adjoint (k y⁻¹)) K)
        (fun y => ContinuousLinearMap.adjoint (k y⁻¹) - ∑ i, c i • K i y) f
        (by rintro (_ | i); exacts [regp, regK i])
        (by intro y _; simp [Fintype.sum_option, sub_eq_add_neg])
        hfc 1 (GlobalTheory.CompanionTheory.WaveKer.one_mem_GLs n)
      rw [h2]
      simpa [Fintype.sum_option, sub_eq_add_neg] using h1
  intro y hy
  simpa [hc, hKk] using sub_eq_zero.1 (hD y hy)

end PositivityTheory.Rg.BcB.F.SelfK

namespace PositivityTheory.Rg.BcB.F

attribute [local instance] borelG

theorem adjKer₀ : AdjKer0 := by
  intro n μ hμ M g T k hb hk
  haveI : BorelSpace (G n) := ⟨rfl⟩
  haveI := FiniteDimensional.complete ℂ M.V
  have h := SelfK.self_adj GlobalTheory.T.length_function_facts_hold GlobalTheory.T.general_linear_group_unimodular GlobalTheory.T.right_derivative_calculus_holds wave_existence_speed_multiplicity.2.1 wave_existence_speed_multiplicity.1 GlobalTheory.T.wave_kernel_uniqueness n μ M g T k hb hk
  refine ⟨hk.1.congr h, ?_, fun y hy k₁ k₂ => ?_, fun u hu x hx => ?_⟩
  · obtain ⟨R, hR⟩ := hk.2.1
    exact ⟨R, fun y hy hl => (h y hy).trans (hR y hy hl)⟩
  · have hm := GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveKer.mul_mem_GLs (GlobalTheory.CompanionTheory.WaveKer.unitary_mem_GLs k₁) hy)
      (GlobalTheory.CompanionTheory.WaveKer.unitary_mem_GLs k₂)
    show ContinuousLinearMap.adjoint (k _⁻¹) = _ * ContinuousLinearMap.adjoint (k y⁻¹) * _
    rw [h _ hm, h y hy]
    exact hk.2.2.1 y hy k₁ k₂
  · rw [← hk.2.2.2 u hu x hx]
    simp only [act]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only
    rw [h _ (PairAdj.val_mem_GLs z)]

end PositivityTheory.Rg.BcB.F
end
end

namespace PositivityTheory.Rg.BcB.F.BlockFiniteConvolution

open PositivityTheory.RgBcC

theorem blkOp₀ : BlockOperatorsProductAdjoint := blkOp' wave_existence_speed_multiplicity.2.2.2

theorem blkComm₀ : BlockPureTensorsCommute := blkComm' wave_existence_speed_multiplicity.2.2.2

theorem blkWord₀ : BlockWordOperators := blkWord' wave_existence_speed_multiplicity.2.2.2

theorem pTTest₀ : PTTest := pTTest' wave_existence_speed_multiplicity.2.2.1

theorem locOk₀ : LocOk := locOk idemAlg PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3

theorem locComm₀ : LocComm := locComm idemAlg sphComm PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3

theorem seenTr₀ : SeenTr := seenTr PositivityTheory.Rg.BcN.F2.LocOpPf.locOp3

theorem sqOk₀ : SqOk := sqOk adjKer₀ blkOp₀ blkWord₀

end PositivityTheory.Rg.BcB.F.BlockFiniteConvolution
