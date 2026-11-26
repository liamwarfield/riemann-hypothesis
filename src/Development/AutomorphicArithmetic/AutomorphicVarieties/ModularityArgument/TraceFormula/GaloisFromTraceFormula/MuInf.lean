module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.DescWeakOfRunTh
public import Development.AutomorphicArithmetic.Foundations.BaseChangeIdentities.FrameMatching.HeckeEigenvalueFiniteness.MuVal
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.MuInf
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.muInf :
    MuInf := by
  intro E _ _ _ μ e hμ
  refine ⟨fun w hw => ?_, fun N k P v => ⟨?_, ?_⟩⟩
  · simpa using UpperTheory.HeckeLevelFrameExistence.muVal E μ e hμ w hw 1
  · rw [((ParLaws.hasInfChar_infChar P v.embedding).twist (μ ^ k)).infChar_eq]
    refine Multiset.map_congr rfl fun z _ => ?_
    rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.MuProps.expo_emb hμ]
    ring
  · rw [((ParLaws.hasInfChar_infChar P (ComplexEmbedding.conjugate v.embedding)).twist (μ ^ k)).infChar_eq]
    refine Multiset.map_congr rfl fun z _ => ?_
    rw [GlobalTheory.BCT.TwistDisc.expo_pow, GlobalTheory.BCT.MuProps.expo_conj hμ]
    ring
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.TwDataT
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private theorem sum_map_eq {ι : Type} [Fintype ι] (f : ι → Multiset ℂ) (g : ℂ → ℂ) :
    ∑ i, (f i).map g = (∑ i, f i).map g :=
  (map_sum (Multiset.mapAddMonoidHom g) f Finset.univ).symm

theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.twDataT :
    CDAddG → MuInf → MWAt → DualWt → TwDataT := by
  intro hAdd hMu hMW hDW E _ _ _ n a b hab ha hb μ e hμ l₁ l₂ lam hlam D₁ D₂ h₁ h₂
  subst hab
  obtain ⟨D, hnot, hsat, hinf⟩ := hAdd E a b D₁ D₂ (μ ^ b) (μ ^ a) ha hb
  have hval : ∀ (w : Pl E) (k : ℕ), (μ ^ k).val w = μ.val w ^ k :=
    fun w k => MonoidHom.pow_apply μ.1 k _
  have hunr : ∀ {w : Pl E} (k : ℕ), μ.UnrAt w → (μ ^ k).UnrAt w := by
    intro w k h x hx
    have e1 : (μ ^ k).loc w x = μ.loc w x ^ k := MonoidHom.pow_apply μ.1 k _
    rw [e1, h x hx, one_pow]
  have hT := (hMu E μ e hμ).2
  have hemb : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) →
      ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar v.embedding =
        (infOfWeight (l v)).map (· + (k : ℂ) * (e v : ℂ) / 2) := by
    intro m C l k hC v
    have h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar v.embedding =
        ((C.P i).infChar v.embedding).map (· + (k : ℂ) * (e v : ℂ) / 2) :=
      fun i => (hT (C.N i) k (C.P i) v).1
    simp only [h1]
    rw [sum_map_eq, hC v.embedding, (hMW E m l v).1]
  have hcon : ∀ {m : ℕ} (C : CD E m) (l : InfinitePlace E → DomWeight m) (k : ℕ), C.Inf (mW l) →
      ∀ v : InfinitePlace E, ∑ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) =
        (infOfWeight (l v)).map (fun t => -(t + (k : ℂ) * (e v : ℂ) / 2)) := by
    intro m C l k hC v
    have h1 : ∀ i, ((C.P i).twist (μ ^ k)).infChar (ComplexEmbedding.conjugate v.embedding) =
        ((C.P i).infChar (ComplexEmbedding.conjugate v.embedding)).map (· - (k : ℂ) * (e v : ℂ) / 2) :=
      fun i => (hT (C.N i) k (C.P i) v).2
    simp only [h1]
    rw [sum_map_eq, hC (ComplexEmbedding.conjugate v.embedding), (hMW E m l v).2, Multiset.map_map]
    refine Multiset.map_congr rfl fun t _ => ?_
    simp only [Function.comp_apply]
    ring
  refine ⟨D, hnot, ?_, ?_⟩
  · intro τ
    rcases InfinitePlace.embedding_mk_eq τ with h | h
    · refine ⟨lam (InfinitePlace.mk τ), ?_⟩
      rw [hinf τ, ← hlam (InfinitePlace.mk τ), ← hemb D₁ l₁ b h₁, ← hemb D₂ l₂ a h₂, h]
    · obtain ⟨lam', hl⟩ := hDW (a + b) (lam (InfinitePlace.mk τ))
      have hτ : τ = ComplexEmbedding.conjugate (InfinitePlace.mk τ).embedding := by
        rw [h]
        exact (star_star τ).symm
      refine ⟨lam', ?_⟩
      rw [hinf τ, hl, ← hlam (InfinitePlace.mk τ), Multiset.map_add (f := _), Multiset.map_map, Multiset.map_map]
      have e1 := hcon D₁ l₁ b h₁ (InfinitePlace.mk τ)
      have e2 := hcon D₂ l₂ a h₂ (InfinitePlace.mk τ)
      rw [← hτ] at e1 e2
      rw [e1, e2]
      rfl
  · intro w B₁ B₂ hu s₁ s₂
    have h := hsat w B₁ B₂ (hunr b hu) (hunr a hu) s₁ s₂
    rw [hval, hval] at h
    exact h
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GaloisFromTraceFormula.Enlarge
open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open UpperTheory.V.Z.Tf.GlobalTraceComparison UpperTheory.V.Z.Tf.GlobalTraceComparison.Cusp UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm UpperTheory.V.Z.Tf.GaloisFromTraceFormula

namespace UpperTheory.V.Z.Tf.GaloisFromTraceFormula

private noncomputable def listProd {ι : Type} {a b : ℕ} (d : ι → Ex (Fin (a + 1) × Fin (b + 1))) :
    List ι → Ex (Fin (a + 1) × Fin (b + 1))
  | [] => .one
  | i :: l => .mul (d i) (listProd d l)

private theorem list_prod_unitary_test {ι : Type} {a b : ℕ} {d : ι → Ex (Fin (a + 1) × Fin (b + 1))}
    (h : ∀ i, U1 (d i)) : ∀ l : List ι, U1 (listProd d l)
  | [] => .one
  | i :: l => .mul (h i) (list_prod_unitary_test h l)

private theorem listProd_ev_zero {ι : Type} {a b : ℕ} {d : ι → Ex (Fin (a + 1) × Fin (b + 1))}
    (x : Fin (a + 1) × Fin (b + 1) → ℂ) {i : ι} (h0 : (d i).ev x = 0) :
    ∀ l : List ι, i ∈ l → (listProd d l).ev x = 0
  | [], h => by simp at h
  | j :: l, h => by
    rcases List.mem_cons.1 h with rfl | h
    · simp [listProd, Ex.ev, h0]
    · simp [listProd, Ex.ev, listProd_ev_zero x h0 l h]

end UpperTheory.V.Z.Tf.GaloisFromTraceFormula

open scoped Classical in
theorem UpperTheory.V.Z.Tf.GaloisFromTraceFormula.enlarge :
    StUnit → EvaluationAtUnitaryOne → SeparatesUnitaryOne → Places → Enlarge := by
  intro hSt hEv hSep hPl E _ _ _ hunr a b S hS Z T hZ hT hTZ e₁ e₂ I _ u C₁ C₂ hC
  obtain ⟨-, hcp, -, hsec⟩ := hPl E
  have hd : ∀ i, ∃ e, U1 e ∧ ev2 a b (u i) e (C₁ i (u i)) (C₂ i (u i)) = 0 := fun i =>
    hSep E (u i) a b _ _ (hC i).2.1 (hC i).2.2.1 (hC i).2.2.2
  choose d hdU hd0 using hd
  haveI : Fintype I := Fintype.ofFinite I
  have hnsS : ∀ w : Pl E, ¬ IsSplitAt w → w ∈ S := by
    intro w hw
    have hc : cPl w = w := by
      by_contra h
      exact hw ((hcp w).2.2 h)
    rcases (hsec S hS w).1 with h | h
    · exact h
    · rwa [hc] at h
  have hTns : ∀ w ∈ T, IsSplitAt w := fun w hw => (hT w hw).2
  have hZns : ∀ w ∈ Z, IsSplitAt w := fun w hw => (hZ w hw).2
  let L : Pl E → List I := fun w => (Finset.univ.filter fun i => u i = w).toList
  let T' : Finset (Pl E) := T ∪ Finset.univ.image u
  let f₁ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)) := fun w => if w ∈ T then e₁ w else listProd d (L w)
  let f₂ : Pl E → Ex (Fin (a + 1) × Fin (b + 1)) := fun w => if w ∈ T then e₂ w else .one
  have hfU : ∀ w, w ∉ T → U1 (f₁ w) := by
    intro w hw
    simp only [f₁, if_neg hw]
    exact list_prod_unitary_test hdU _
  have hf₂ : ∀ w, w ∉ T → f₂ w = .one := fun w hw => by simp only [f₂, if_neg hw]
  have hT'ns : ∀ w ∈ T', w ∉ T → ¬ IsSplitAt w := by
    intro w hw hwT
    rcases Finset.mem_union.1 hw with h | h
    · exact absurd h hwT
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      exact (hC i).1
  have huT : ∀ i, u i ∉ T := fun i h => (hC i).1 (hTns _ h)
  refine ⟨T', f₁, f₂, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w hw
    by_cases hwT : w ∈ T
    · exact (hT w hwT).1
    · exact hnsS w (hT'ns w hw hwT)
  · rw [Finset.disjoint_left]
    intro w hw hwZ
    by_cases hwT : w ∈ T
    · exact Finset.disjoint_left.1 hTZ hwT hwZ
    · exact hT'ns w hw hwT (hZns w hwZ)
  · intro w hw hns
    have hwT : w ∉ T := fun h => hns (hTns w h)
    exact hf₂ w hwT
  · intro i
    refine Finset.prod_eq_zero (i := u i) (Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))) ?_
    have : ev2 a b (u i) (f₁ (u i)) (C₁ i (u i)) (C₂ i (u i)) = 0 := by
      simp only [f₁, if_neg (huT i)]
      refine listProd_ev_zero _ (hd0 i) _ ?_
      simp [L]
    rw [this, zero_mul]
  · intro B₁ B₂ hB
    unfold UpperTheory.V.Z.Tf.GlobalTraceComparison.val
    symm
    have hsub : T ⊆ T' := Finset.subset_union_left
    rw [← Finset.prod_subset hsub]
    · refine Finset.prod_congr rfl fun w hw => ?_
      simp only [f₁, f₂, if_pos hw]
    · intro w hw hwT
      rcases Finset.mem_union.1 hw with h | h
      · exact absurd h hwT
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 h
      rw [hf₂ _ hwT, hEv E (u i) a b _ (hfU _ hwT) _ _ (hB i).1 (hB i).2.1 (hB i).2.2.1 (hB i).2.2.2]
      simp [ev2, Ex.ev]
  · intro l₁ l₂ φ k
    have hloc : ∀ (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Separable → Q₂.Separable →
        stTw2 a b w Q₁ Q₂ (fam Z T' φ f₁ f₂ k w) = stTw2 a b w Q₁ Q₂ (fam Z T φ e₁ e₂ k w) := by
      intro w Q₁ Q₂ h₁ h₂
      unfold fam
      by_cases hwZ : w ∈ Z
      · simp only [if_pos hwZ]
      simp only [if_neg hwZ]
      by_cases hwT : w ∈ T
      · have hw' : w ∈ T' := Finset.mem_union_left _ hwT
        simp only [if_pos hwT, if_pos hw', f₁, f₂]
      by_cases hw' : w ∈ T'
      · simp only [if_neg hwT, if_pos hw']
        rw [hf₂ w hwT]
        exact hSt E hunr w (hT'ns w hw' hwT) a b _
          (.mul ((hfU w hwT).pow k) ((U1.one).pow k)) Q₁ Q₂ h₁ h₂
      · simp only [if_neg hwT, if_neg hw']
    unfold PositivityTheory.Rg.BcB.G8.geomSt2
    refine finsum_mem_congr rfl fun p hp => ?_
    congr 1
    refine finprod_congr fun w => finprod_congr fun _ => ?_
    exact hloc w _ _ (hp.1.2.2.1.map) (hp.2.1.2.2.1.map)
end
