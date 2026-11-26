module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAsmC
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksFg

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksAsmD
section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.LieSumDecompositions.PBlocksLag
noncomputable section

open NumberField IsDedekindDomain Polynomial
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin GlobalTheory.BlockCap PositivityTheory.Rg.Rs

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockLagrange

section Abs

variable {M ι Λ : Type} [AddCommGroup M] [Module ℂ M] [DecidableEq ι]

theorem list_prod_apply (l : List (Module.End ℂ M)) (k : Module.End ℂ M → ℂ) (φ : M) (h : ∀ f ∈ l, f φ = k f • φ) :
    l.prod φ = (l.map k).prod • φ := by
  induction l with
  | nil => simp
  | cons f l ih =>
    rw [List.prod_cons, Module.End.mul_apply, ih (fun g hg => h g (List.mem_cons_of_mem _ hg)), map_smul,
      h f List.mem_cons_self, smul_smul, List.map_cons, List.prod_cons, mul_comm]

theorem list_prod_smul (l : List (Module.End ℂ M)) (φ : M) (h : ∀ f ∈ l, ∃ c : ℂ, f φ = c • φ) :
    ∃ c : ℂ, l.prod φ = c • φ := by
  induction l with
  | nil => exact ⟨1, by simp⟩
  | cons f l ih =>
    obtain ⟨c, hc⟩ := ih (fun g hg => h g (List.mem_cons_of_mem _ hg))
    obtain ⟨d, hd⟩ := h f List.mem_cons_self
    exact ⟨c * d, by rw [List.prod_cons, Module.End.mul_apply, hc, map_smul, hd, smul_smul]⟩

variable (A : Λ → Module.End ℂ M) (χ : ι → Λ → ℂ) (lam : ι → ι → Λ)

def fac (i j : ι) : Module.End ℂ M := (χ i (lam i j) - χ j (lam i j))⁻¹ • (A (lam i j) - χ j (lam i j) • 1)

def proj (SS : Finset ι) (i : ι) : Module.End ℂ M := (((SS.erase i).toList).map (fac A χ lam i)).prod

variable {A χ lam}

omit [DecidableEq ι] in
theorem fac_apply {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ) (i j k : ι) {φ : M}
    (hφ : φ ∈ P k) :
    fac A χ lam i j φ = ((χ i (lam i j) - χ j (lam i j))⁻¹ * (χ k (lam i j) - χ j (lam i j))) • φ := by
  simp only [fac, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.one_apply, hP k φ hφ]
  rw [smul_sub, smul_smul, smul_smul, mul_sub, sub_smul]

theorem proj_self {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ)
    (hlam : ∀ i j, i ≠ j → χ i (lam i j) ≠ χ j (lam i j)) (SS : Finset ι) (i : ι) {φ : M} (hφ : φ ∈ P i) :
    proj A χ lam SS i φ = φ := by
  unfold proj
  rw [list_prod_apply _ (fun _ => 1) φ]
  · simp
  · intro f hf
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hf
    rw [one_smul, fac_apply hP i j i hφ]
    have hij : i ≠ j := fun h => by subst h; exact Finset.notMem_erase i SS (Finset.mem_toList.1 hj)
    rw [inv_mul_cancel₀ (sub_ne_zero.2 (hlam i j hij)), one_smul]

theorem proj_other {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ)
    (SS : Finset ι) (i k : ι) (hk : k ∈ SS) (hki : k ≠ i) {φ : M} (hφ : φ ∈ P k) :
    proj A χ lam SS i φ = 0 := by
  unfold proj
  have hmem : fac A χ lam i k ∈ ((SS.erase i).toList).map (fac A χ lam i) :=
    List.mem_map.2 ⟨k, Finset.mem_toList.2 (Finset.mem_erase.2 ⟨hki, hk⟩), rfl⟩
  obtain ⟨l₁, l₂, he⟩ := List.append_of_mem hmem
  have hl₂ : ∀ f ∈ l₂, ∃ c : ℂ, f φ = c • φ := by
    intro f hf
    have hf' : f ∈ ((SS.erase i).toList).map (fac A χ lam i) := by
      rw [he]; exact List.mem_append_right _ (List.mem_cons_of_mem _ hf)
    obtain ⟨j, -, rfl⟩ := List.mem_map.1 hf'
    exact ⟨_, fac_apply hP i j k hφ⟩
  obtain ⟨c, hc⟩ := list_prod_smul l₂ φ hl₂
  rw [he, List.prod_append, List.prod_cons, Module.End.mul_apply, Module.End.mul_apply, hc, map_smul,
    fac_apply hP i k k hφ, sub_self, mul_zero, zero_smul, smul_zero, map_zero]

theorem proj_decomp {P : ι → Submodule ℂ M} (hP : ∀ k, ∀ φ ∈ P k, ∀ l, A l φ = χ k l • φ)
    (hlam : ∀ i j, i ≠ j → χ i (lam i j) ≠ χ j (lam i j)) (SS : Finset ι) {φ : M} (hφ : φ ∈ ⨆ i ∈ SS, P i) :
    (∀ i, proj A χ lam SS i φ ∈ P i) ∧ ∑ i ∈ SS, proj A χ lam SS i φ = φ := by
  obtain ⟨μ, hμ⟩ := (Submodule.mem_iSup_finset_iff_exists_sum P φ).1 hφ
  have key : ∀ i, proj A χ lam SS i φ = if i ∈ SS then (μ i : M) else 0 := by
    intro i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hμ, map_sum]
    rw [Finset.sum_congr rfl (g := fun k => if k = i then (μ k : M) else 0) (fun k hk => by
      by_cases h : k = i
      · subst h; rw [if_pos rfl, proj_self hP hlam SS k (μ k).2]
      · rw [if_neg h, proj_other hP SS i k hk h (μ k).2])]
    rw [Finset.sum_ite_eq']
  refine ⟨fun i => ?_, ?_⟩
  · rw [key]
    split_ifs
    · exact (μ i).2
    · exact (P i).zero_mem
  · rw [Finset.sum_congr rfl (fun i hi => by rw [key, if_pos hi]), hμ]

theorem proj_commute (SS : Finset ι) (i : ι) (B : Module.End ℂ M) (hB : ∀ l, Commute (A l) B) :
    Commute (proj A χ lam SS i) B := by
  unfold proj
  refine Commute.list_prod_left _ _ fun f hf => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hf
  exact ((hB _).sub_left ((Commute.one_left B).smul_left _)).smul_left _

end Abs

section Sep

theorem exists_ne_prod {m m' : Multiset ℂ} (sh : ℂ) (h : m ≠ m') :
    ∃ w : ℂ, (m.map fun z => w + sh + z).prod ≠ (m'.map fun z => w + sh + z).prod := by
  by_contra hc
  push Not at hc
  have ev : ∀ (n : Multiset ℂ) (w : ℂ), (n.map fun z => w + sh + z).prod =
      ((n.map fun z => -(sh + z)).map fun a => X - C a).prod.eval w := by
    intro n w
    rw [eval_multiset_prod, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun z _ => ?_
    simp
    ring
  have hp : ((m.map fun z => -(sh + z)).map fun a => X - C a).prod =
      ((m'.map fun z => -(sh + z)).map fun a => X - C a).prod :=
    Polynomial.funext fun w => by rw [← ev, ← ev, hc w]
  have hr := congrArg Polynomial.roots hp
  rw [roots_multiset_prod_X_sub_C, roots_multiset_prod_X_sub_C] at hr
  exact h (Multiset.map_injective (fun x y hxy => by simpa using hxy) hr)

end Sep

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem proj_exists {a : ℕ} (L : Submodule ℂ (Sm E a)) (SS : Finset ((E →+* ℂ) → Multiset ℂ)) (sh : ℂ)
    (hL : L ≤ ⨆ σ ∈ SS, BlockCapelli.Eig L σ sh) :
    ∃ z : ((E →+* ℂ) → Multiset ℂ) → Module.End ℂ (Sm E a), (∀ σ (o : Op E a), Commute (z σ) (act o)) ∧
      (∀ σ, ∀ φ ∈ L, z σ φ ∈ BlockCapelli.Eig L σ sh) ∧ ∀ φ ∈ L, ∑ σ ∈ SS, z σ φ = φ := by
  classical
  let A : (E →+* ℂ) × ℂ → Module.End ℂ (Sm E a) := fun l => cap l.1 l.2
  let χ : ((E →+* ℂ) → Multiset ℂ) → (E →+* ℂ) × ℂ → ℂ := fun σ l => ((σ l.1).map fun z => l.2 + sh + z).prod
  have hsep : ∀ σ σ' : (E →+* ℂ) → Multiset ℂ, σ ≠ σ' → ∃ l, χ σ l ≠ χ σ' l := by
    intro σ σ' h
    obtain ⟨τ, hτ⟩ := Function.ne_iff.1 h
    obtain ⟨w, hw⟩ := exists_ne_prod sh hτ
    exact ⟨(τ, w), hw⟩
  let lam : ((E →+* ℂ) → Multiset ℂ) → ((E →+* ℂ) → Multiset ℂ) → (E →+* ℂ) × ℂ := fun σ σ' =>
    if h : σ ≠ σ' then Classical.choose (hsep σ σ' h) else (Classical.arbitrary _, 0)
  have hlam : ∀ σ σ', σ ≠ σ' → χ σ (lam σ σ') ≠ χ σ' (lam σ σ') := by
    intro σ σ' h
    simp only [lam, dif_pos h]
    exact Classical.choose_spec (hsep σ σ' h)
  have hP : ∀ k, ∀ φ ∈ BlockCapelli.Eig L k sh, ∀ l, A l φ = χ k l • φ := fun k φ hφ l => hφ.2 l.1 l.2
  refine ⟨proj A χ lam SS, fun σ o => proj_commute SS σ _ fun l => GlobalTheory.SpehInfChar.cap_commute_act l.1 l.2 o,
    fun σ φ hφ => (proj_decomp hP hlam SS (hL hφ)).1 σ, fun φ hφ => (proj_decomp hP hlam SS (hL hφ)).2⟩

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockLagrange

end
end

noncomputable section

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockDerivatives PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockCapelli PositivityTheory.Rg.BcB.SpectralAccumulation.Cz.BlockAssembly

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

def FgSl : Prop := ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r s : ℕ) (U : Submodule ℂ (Sm E (r + s)))
  (c : ℂ) (T : Sm E (r + s) →ₗ[ℂ] Sm E (r + s)), IsAutSt U → IsSliceMap U c T → FinGen U →
  (∃ S₁ : Finset (Sm E r), (↑S₁ : Set (Sm E r)) ⊆ LS U T ∧
    ∀ W : Submodule ℂ (Sm E r), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₁ : Set (Sm E r)) ⊆ W → LS U T ≤ W) ∧
  (∃ S₂ : Finset (Sm E s), (↑S₂ : Set (Sm E s)) ⊆ RS U T ∧
    ∀ W : Submodule ℂ (Sm E s), _root_.GlobalTheory.CuspRep.IsStable W → (↑S₂ : Set (Sm E s)) ⊆ W → RS U T ≤ W)

theorem blocks_of (hfg : FgSl) : Blocks := by
  intro E _ _ _ r s τ hr hs U hH hSI c T hT hpE
  classical
  obtain ⟨hAS, hFG, hNP, hCI, -, hRA⟩ := hH
  choose mm hmmI hmmN using hRA
  obtain ⟨hfgL, hfgR⟩ := hfg E r s U c T hAS hT hFG
  have hLle := LS_le_iSup hAS hT mm hmmN hmmI
  have hRle := RS_le_iSup hAS hT mm hmmN hmmI
  obtain ⟨z₁, hz₁c, hz₁E, hz₁s⟩ := BlockLagrange.proj_exists (LS U T) (adm mm r) ((s : ℂ) / 2) hLle
  obtain ⟨z₂, hz₂c, hz₂E, hz₂s⟩ := BlockLagrange.proj_exists (RS U T) (adm mm s) (-(r : ℂ) / 2) hRle
  have hMI := BlockSlices.memInd2 hAS hT
  have hLst := BlockSlices.LS_stable hAS hT
  have hRst := BlockSlices.RS_stable hAS hT

  have hind := fun p : ((E →+* ℂ) → Multiset ℂ) × ((E →+* ℂ) → Multiset ℂ) =>
    indMap_holds E r s U (LS U T) (RS U T) T (z₁ p.1) (z₂ p.2) hAS.1 hAS.2 hLst hRst hT.equiv hMI
      (fun o ψ _ => LinearMap.congr_fun (hz₁c p.1 o).eq ψ) (fun o ψ _ => LinearMap.congr_fun (hz₂c p.2 o).eq ψ)
  choose T' hT'e hT'u hT'l using hind

  have hvan : ∀ p, ∀ ψ ∈ U, T ψ = 0 → T' p ψ = 0 := by
    intro p ψ hψ h0
    refine eq_zero_of_levi (hT'u p ψ hψ) fun k g m => ?_
    have := hT'l p ψ hψ k g 0 Fin.elim0 Fin.elim0 (fun i => i.elim0) (fun i => i.elim0) (fun m' => by
      rw [h0]; simp) m
    simpa using this
  choose P' hP' using fun p => factor U T (T' p) (hvan p)

  set SS := adm mm r ×ˢ adm mm s with hSS
  have hsum : ∀ ψ ∈ U, ∑ p ∈ SS, T' p ψ = T ψ := by
    intro ψ hψ
    refine eq_of_levi (fun x g => ?_) (hT.unipInv ψ hψ) fun k g m => ?_
    · simp only [Submodule.coe_sum, Finset.sum_apply]
      exact Finset.sum_congr rfl fun p _ => hT'u p ψ hψ x g
    · obtain ⟨n, ψ₁, ψ₂, h₁, h₂, he⟩ := ParabolicProjection.tensor_pair_finite_sum ((hMI ψ hψ).2 k g)
      have he' : ∀ m', (T ψ).1 (lev (Ad E) r s m' * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
          ∑ i, (ψ₁ i).1 m'.1 * (ψ₂ i).1 m'.2 := fun m' => he m'
      simp only [Submodule.coe_sum, Finset.sum_apply]
      rw [Finset.sum_congr rfl fun p _ => hT'l p ψ hψ k g n ψ₁ ψ₂ h₁ h₂ he' m, he' m, hSS, Finset.sum_product]
      have e1 : ∀ i, ∑ σ ∈ adm mm r, (z₁ σ (ψ₁ i)).1 m.1 = (ψ₁ i).1 m.1 := fun i => by
        rw [← Finset.sum_apply, ← Submodule.coe_sum, hz₁s _ (h₁ i)]
      have e2 : ∀ i, ∑ ρ ∈ adm mm s, (z₂ ρ (ψ₂ i)).1 m.2 = (ψ₂ i).1 m.2 := fun i => by
        rw [← Finset.sum_apply, ← Submodule.coe_sum, hz₂s _ (h₂ i)]
      have key : ∀ i, (ψ₁ i).1 m.1 * (ψ₂ i).1 m.2 =
          ∑ σ ∈ adm mm r, ∑ ρ ∈ adm mm s, (z₁ σ (ψ₁ i)).1 m.1 * (z₂ ρ (ψ₂ i)).1 m.2 := fun i => by
        rw [← e1 i, ← e2 i, Finset.sum_mul_sum]
      rw [Finset.sum_congr rfl fun i _ => key i]
      symm
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun σ _ => Finset.sum_comm

  set N := SS.card
  let dec : ℕ → ((E →+* ℂ) → Multiset ℂ) × ((E →+* ℂ) → Multiset ℂ) := fun j =>
    if h : j < N then (SS.equivFin.symm ⟨j, h⟩).1 else (fun _ => 0, fun _ => 0)
  have hdec : ∀ j ∈ Finset.range N, dec j ∈ SS := by
    intro j hj
    have h := Finset.mem_range.1 hj
    simp only [dec, dif_pos h]
    exact (SS.equivFin.symm ⟨j, h⟩).2
  have hreidx : ∀ f : ((E →+* ℂ) → Multiset ℂ) × ((E →+* ℂ) → Multiset ℂ) → Sm E (r + s),
      ∑ j ∈ Finset.range N, f (dec j) = ∑ p ∈ SS, f p := by
    intro f
    rw [Finset.sum_range (fun j => f (dec j))]
    have e : ∀ i : Fin N, f (dec i) = f (SS.equivFin.symm i).1 := fun i => by simp only [dec, dif_pos i.2, Fin.eta]
    simp only [e]
    rw [Equiv.sum_comp SS.equivFin.symm (fun x => f x.1), Finset.sum_coe_sort SS f]
  refine ⟨Finset.range N, fun j => P' (dec j), fun j => tw ((LS U T).map (z₁ (dec j).1)) (-(s : ℂ) / 2),
    fun j => tw ((RS U T).map (z₂ (dec j).2)) ((r : ℂ) / 2), fun j hj => ?_, fun j _ o ψ hψ => ?_, fun ψ hψ => ?_,
    fun j _ ψ hψ => ?_⟩
  · have hp := Finset.mem_product.1 (hdec j hj)
    exact ⟨hyp_left hAS hNP hT hpE mm hmmN hp.1 (hz₁c _) (hz₁E _) hfgL τ,
      hyp_right hAS hNP hT hpE mm hmmN hp.2 (hz₂c _) (hz₂E _) hfgR τ⟩
  · rw [← hT.equiv o ψ hψ, hP' _ _ (hAS.1 o ψ hψ), hP' _ _ hψ, hT'e _ o ψ hψ]
  · rw [Finset.sum_congr rfl fun j _ => hP' (dec j) ψ hψ, hreidx (fun p => T' p ψ), hsum ψ hψ]
  · rw [hP' _ _ hψ]
    have e1 : tw (tw ((LS U T).map (z₁ (dec j).1)) (-(s : ℂ) / 2)) ((s : ℂ) / 2) = (LS U T).map (z₁ (dec j).1) := by
      rw [show -(s : ℂ) / 2 = -((s : ℂ) / 2) by ring]
      exact BlockTwistCharacters.tw_tw_neg _ _
    have e2 : tw (tw ((RS U T).map (z₂ (dec j).2)) ((r : ℂ) / 2)) (-(r : ℂ) / 2) = (RS U T).map (z₂ (dec j).2) := by
      have := BlockTwistCharacters.tw_tw_neg ((RS U T).map (z₂ (dec j).2)) (-(r : ℂ) / 2)
      rwa [show -(-(r : ℂ) / 2) = (r : ℂ) / 2 by ring] at this
    rw [e1, e2]
    refine ⟨hT'u _ ψ hψ, fun k g => ?_⟩
    obtain ⟨n, ψ₁, ψ₂, h₁, h₂, he⟩ := ParabolicProjection.tensor_pair_finite_sum ((hMI ψ hψ).2 k g)
    have he' : ∀ m', (T ψ).1 (lev (Ad E) r s m' * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)) =
        ∑ i, (ψ₁ i).1 m'.1 * (ψ₂ i).1 m'.2 := fun m' => he m'
    rw [show (fun m => (T' (dec j) ψ).1 (lev (Ad E) r s m * (infGL E (r + s) (Unitary.toUnits k) * finGL E (r + s) g)))
      = fun m => ∑ i, (z₁ (dec j).1 (ψ₁ i)).1 m.1 * (z₂ (dec j).2 (ψ₂ i)).1 m.2 from
      funext (hT'l _ ψ hψ k g n ψ₁ ψ₂ h₁ h₂ he')]
    exact ParabolicProjection.sum_mem_tens2 (fun i => Submodule.mem_map_of_mem (h₁ i)) (fun i => Submodule.mem_map_of_mem (h₂ i))

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

end
end

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Cz

theorem fgSl_holds : FgSl := fun _ _ _ _ _ _ _ _ _ hU hT hfg =>
  ⟨BlockFiniteGeneration.LS_fg hU hT hfg (BlockSlices.expand hU hT), BlockFiniteGeneration.RS_fg hU hT hfg (BlockSlices.expand hU hT)⟩

theorem blocks_holds : Blocks := blocks_of fgSl_holds

end PositivityTheory.Rg.BcB.SpectralAccumulation.Cz
