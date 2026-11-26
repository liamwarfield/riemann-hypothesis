module

public import Development.AutomorphicArithmetic.TwistedTraces.LeClosureSpanAllOfCommutingUnitaryReps
public import Development.AutomorphicArithmetic.TwistedTraces.IsotypicComponentProductOfSmoothReps

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.MemFixedVectorsOfProductOfCompactOpen
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_keep {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (Y : Submodule ℂ H) :
    ∀ l : List (H →L[ℂ] H), (∀ a ∈ l, ∀ v ∈ Y, a v ∈ Y) → ∀ v, (v ∈ Y ∨ ∃ a ∈ l, ∀ v, a v ∈ Y) → l.prod v ∈ Y
  | [], _, v, h => by simpa using h
  | a :: l, hl, v, h => by
    rw [List.prod_cons]
    show a (l.prod v) ∈ Y
    have ih := prod_keep Y l (fun b hb => hl b (List.mem_cons_of_mem _ hb)) v
    rcases h with h | ⟨b, hb, h⟩
    · exact hl a List.mem_cons_self _ (ih (Or.inl h))
    · rcases List.mem_cons.1 hb with rfl | hb
      · exact h _
      · exact hl a List.mem_cons_self _ (ih (Or.inr ⟨b, hb, h⟩))

theorem UpperTheory.mem_fixedVectors_of_product_of_compactOpen :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (π : ∀ i, UnitaryRep (G i) H) (Z : Submodule ℂ H) (L : ∀ i, Subgroup (G i)) (T : Fin r → H →L[ℂ] H), (∀ i v, T i v ∈ fixU (π i) (L i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → ∀ v ∈ Z, (List.ofFn T).prod v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)) := by
  intro r G _ _ _ _ _ _ H _ _ _ π Z L T h1 h2 h3 v hv
  have k1 : ∀ i j, ∀ v ∈ fixU (π j) (L j), T i v ∈ fixU (π j) (L j) := fun i j v hv u hu => by
    by_cases e : i = j
    · subst e; exact h1 i v u hu
    · rw [← h3 i j e, hv u hu]
  refine Submodule.mem_inf.2 ⟨?_, Submodule.mem_iInf _ |>.2 fun j => ?_⟩
  · exact prod_keep Z _ (fun a ha => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact h2 i) v (Or.inl hv)
  · exact prod_keep _ _ (fun a ha => by obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha; exact k1 i j) v
      (Or.inr ⟨T j, List.mem_ofFn.2 ⟨j, rfl⟩, h1 j⟩)
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ListOfFnProdEqMulUpdateOneOfPairwiseCommute
open scoped BigOperators

theorem UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute :
    ∀ (M : Type) [Monoid M] (r : ℕ) (a : Fin r → M), (∀ i j, i ≠ j → Commute (a i) (a j)) → ∀ i, (List.ofFn a).prod = a i * (List.ofFn (Function.update a i 1)).prod ∧ ∀ m : M, (∀ j, j ≠ i → Commute m (a j)) → Commute m (List.ofFn (Function.update a i 1)).prod := by
  intro M _ r a h i
  refine ⟨?_, ?_⟩
  · induction r with
    | zero => exact i.elim0
    | succ r ih =>
      refine Fin.cases ?_ (fun k => ?_) i
      · have h1 : (fun j : Fin r => Function.update a 0 1 j.succ) = fun j => a j.succ := by
          funext j
          rw [Function.update_of_ne (Fin.succ_ne_zero j)]
        rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, h1,
          Function.update_self, one_mul]
      · have h1 : (fun j : Fin r => Function.update a k.succ 1 j.succ)
            = Function.update (fun j : Fin r => a j.succ) k 1 := by
          funext j
          by_cases hj : j = k
          · subst hj
            rw [Function.update_self, Function.update_self]
          · rw [Function.update_of_ne hj,
              Function.update_of_ne (fun e => hj (Fin.succ_injective _ e))]
        have h2 := ih (fun j : Fin r => a j.succ)
          (fun i j hij => h _ _ (fun e => hij (Fin.succ_injective _ e))) k
        rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, h1,
          Function.update_of_ne (Fin.succ_ne_zero k).symm, h2, ← mul_assoc, ← mul_assoc,
          (h 0 k.succ (Fin.succ_ne_zero k).symm).eq]
  · intro m hm
    apply Commute.list_prod_right
    intro x hx
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      exact Commute.one_right m
    · rw [Function.update_of_ne hj]
      exact hm j hj
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.IsotypicIntersectionProductEq
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.IsotypicSubmoduleProductDecomposition
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.IsotypicProjectionProductCommute
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.isotypic_projection_product_commute :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (Z : Submodule ℂ H) (hsm : ∀ i, GroundTheory.Automorphic.IsSmooth (τ i)), (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → (∀ i, (π i).IsInvariant Z) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ (L K : ∀ i, Subgroup (G i)) (hL : (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i)))), (∀ i, K i ≤ L i) → (∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i) → ∀ i f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f → ∃ f', Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f' ∧ ∀ x, R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod (f x)) = f' (I i (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x : S i)) := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK i f hf
  let a : Fin r → (H →L[ℂ] H) := fun j => prj (fixU (π j) (L j))
  have hcomm : ∀ p q, p ≠ q → Commute (a p) (a q) := fun p q hpq => by
    refine ContinuousLinearMap.ext fun v => ?_
    exact ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G p) (G q) H (π p) (π q) (L p) (L q)).2.2.2 (hc p q hpq)).2 v
  have hact : ∀ j, j ≠ i → ∀ g v, a j (π i g v) = π i g (a j v) := fun j hj g v =>
    ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G i) H (π j) (π i) (L j) (L i)).2.2.2 (hc j i hj)).1 g v
  obtain ⟨hprod, hQc⟩ := UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (H →L[ℂ] H) r a hcomm i
  let b : Fin r → (H →L[ℂ] H) := Function.update a i 1
  let Q : H →L[ℂ] H := (List.ofFn b).prod
  have hQa : Commute (a i) Q := hQc (a i) fun j hj => hcomm i j hj.symm
  have hQπ : ∀ g v, Q (π i g v) = π i g (Q v) := fun g v => by
    have h : Commute (π i g : H →L[ℂ] H) Q := hQc _ fun j hj => by
      refine ContinuousLinearMap.ext fun v => ?_
      exact (hact j hj g v).symm
    exact (congrArg (fun T : H →L[ℂ] H => T v) h.eq).symm
  have hb : ∀ p q, p ≠ q → Commute (b p) (b q) := fun p q hpq => by
    by_cases hp : p = i
    · subst hp
      simp only [b, Function.update_self]
      exact Commute.one_left _
    · by_cases hq : q = i
      · subst hq
        simp only [b, Function.update_self]
        exact Commute.one_right _
      · simp only [b, Function.update_of_ne hp, Function.update_of_ne hq]
        exact hcomm p q hpq
  have hQZ : ∀ v ∈ Z, Q v ∈ Z := by
    let M : Submonoid (H →L[ℂ] H) :=
      { carrier := {T | ∀ v ∈ Z, T v ∈ Z}
        mul_mem' := fun ha hb v hv => ha _ (hb v hv)
        one_mem' := fun v hv => hv }
    have hM : Q ∈ M := by
      refine Submonoid.list_prod_mem M fun x hx => ?_
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      by_cases hj : j = i
      · subst hj
        simp only [b, Function.update_self]
        exact M.one_mem
      · simp only [b, Function.update_of_ne hj]
        exact fun v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G j) H (π j) (π j) (L j) (L j)).2.2.1 Z hZc (hZi j) v hv
    exact hM
  have hQfix : ∀ j, j ≠ i → ∀ v, Q v ∈ fixU (π j) (L j) := fun j hj v => by
    have h := (UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (H →L[ℂ] H) r b hb j).1
    have h2 : Q v = a j ((List.ofFn (Function.update b j 1)).prod v) := by
      have h3 : b j = a j := Function.update_of_ne hj _ _
      change (List.ofFn b).prod v = _
      rw [h, h3]
      rfl
    rw [h2]
    exact (UpperTheory.fixedProjection_invariant_and_commuting_reps (G j) (G j) H (π j) (π j) (L j) (L j)).1 _
  let f' : S i →ₗ[ℂ] H := (R : H →ₗ[ℂ] H) ∘ₗ (Q : H →ₗ[ℂ] H) ∘ₗ f ∘ₗ ((I i).symm : S i →ₗ[ℂ] S i)
  have hf' : ∀ y, f' y = R (Q (f ((I i).symm y))) := fun y => rfl
  have hfZ : ∀ x, f x ∈ Z := fun x => (Submodule.mem_inf.1 (hf.mem x)).1
  refine ⟨f', ⟨fun y => ?_, fun g y => ?_⟩, fun x => ?_⟩
  · rw [hf']
    have hw := hQZ _ (hfZ ((I i).symm y))
    refine Submodule.mem_inf.2 ⟨hRZ _ hw, ?_⟩
    simp only [Submodule.mem_iInf]
    intro j hj u hu
    have h := hRs j ((s j).symm u) _ hw
    rw [(s j).apply_symm_apply] at h
    rw [← h, hQfix j hj _ _ (hsK j u hu)]
  · have hIs : (I i).symm (τ i g y) = τ i ((s i).symm g) ((I i).symm y) := by
      apply (I i).injective
      rw [hI, (I i).apply_symm_apply, (I i).apply_symm_apply, (s i).apply_symm_apply]
    rw [hf', hf', hIs, hf.map, hQπ, hRs i _ _ (hQZ _ (hfZ _)), (s i).apply_symm_apply]
  · have hE : Eqv (τ i) (π i) ⊤ f := ⟨fun _ => Submodule.mem_top, hf.map⟩
    have h1 := UpperTheory.fixedProjection_apply_equivariant_eq (G i) H (S i) (τ i) (hsm i) (π i) (L i) (hL i).1 (hL i).2 f hE x
    have h2 : (List.ofFn a).prod (f x) = Q (a i (f x)) := by
      rw [hprod]
      exact congrArg (fun T : H →L[ℂ] H => T (f x)) hQa.eq
    rw [hf', (I i).symm_apply_apply]
    change R ((List.ofFn a).prod (f x)) = _
    rw [h2]
    change R (Q (prj (fixU (π i) (L i)) (f x))) = _
    rw [h1]
end

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.isotypic_submodule_product_decomposition :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (Z : Submodule ℂ H) (hsm : ∀ i, GroundTheory.Automorphic.IsSmooth (τ i)), (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → (∀ i, (π i).IsInvariant Z) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ (L K : ∀ i, Subgroup (G i)) (hL : (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i)))), (∀ i, K i ≤ L i) → (∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i) → ∀ (c : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) →ₐ[ℂ] Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) (J : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i))), (∀ i (x : fixedVectors (τ i) (K i)), ((J i x : fixedVectors (τ i) (K i)) : S i) = I i (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x : S i)) → (∀ i t f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f → ∀ (x : fixedVectors (τ i) (K i)) (y : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))), (y : H) = f x → ((c i t y : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) : H) = f (t x)) → (∀ i, (Z ⊓ ⨅ i, fixU (π i) (K i)) ≤ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) (K i)) → ∃ ρ : Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i)), (∀ v : ↥(Z ⊓ ⨅ i, fixU (π i) (K i)), ((ρ v : ↥(Z ⊓ ⨅ i, fixU (π i) (K i))) : H) = R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod v)) ∧ ∀ i a b, b * J i = J i * a → ρ * c i a = c i b * ρ := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK c J hJ hcf hsp
  let X : Submodule ℂ H := Z ⊓ ⨅ i, fixU (π i) (K i)
  let Pr : H →L[ℂ] H := (List.ofFn fun j => prj (fixU (π j) (L j))).prod
  have hPr : ∀ v ∈ Z, Pr v ∈ (Z ⊓ ⨅ j, fixU (π j) (L j)) :=
    UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L (fun j => prj (fixU (π j) (L j)))
      (fun i v => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).1 v)
      (fun i v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.2.1 Z hZc (hZi i) v hv)
      (fun i j hij h v => ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G j) H (π i) (π j) (L i) (L j)).2.2.2 (hc i j hij)).1 h v)
  have hRX : ∀ v ∈ Z, R (Pr v) ∈ X := fun v hv => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 (hPr v hv)
    refine Submodule.mem_inf.2 ⟨hRZ _ h1, (Submodule.mem_iInf _).2 fun j u hu => ?_⟩
    have h := hRs j ((s j).symm u) _ h1
    rw [(s j).apply_symm_apply] at h
    rw [← h, (Submodule.mem_iInf _).1 h2 j _ (hsK j u hu)]
  have hm : ∀ i f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) f →
      ∀ x ∈ fixedVectors (τ i) (K i), f x ∈ X := fun i f hf x hx => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 (hf.mem x)
    refine Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun j => ?_⟩
    by_cases e : j = i
    · subst e
      exact fun u hu => by rw [← hf.map, mem_fixedVectors.1 hx u hu]
    · exact (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 h2 j) e
  let ρ : Module.End ℂ X := ((R : H →ₗ[ℂ] H) ∘ₗ (Pr : H →ₗ[ℂ] H) ∘ₗ X.subtype).codRestrict X
    fun v => hRX _ (Submodule.mem_inf.1 v.2).1
  refine ⟨ρ, fun v => rfl, fun i a b hab => ?_⟩
  have key : ∀ y ∈ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (K j)) (K i),
      ∃ h : y ∈ X, ρ (c i a ⟨y, h⟩) = c i b (ρ ⟨y, h⟩) := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, x, hx, rfl⟩ := hy
      obtain ⟨f', hf', hff⟩ := UpperTheory.isotypic_projection_product_commute r G H S π τ Z hsm hc hZc hZi s I R hRZ hRs hI L K hL hKL hsK i f hf
      have hρ : ∀ (x' : fixedVectors (τ i) (K i)) (h : f x' ∈ X), ((ρ ⟨f x', h⟩ : X) : H) = f' (J i x') := by
        intro x' h
        rw [hJ]
        exact hff x'
      have hy := hm i f hf x hx
      refine ⟨hy, Subtype.ext ?_⟩
      have e1 : c i a ⟨f x, hy⟩ = ⟨f (a ⟨x, hx⟩), hm i f hf _ (a ⟨x, hx⟩).2⟩ :=
        Subtype.ext (hcf i a f hf ⟨x, hx⟩ _ rfl)
      have e2 : ((c i b (ρ ⟨f x, hy⟩) : X) : H) = f' (b (J i ⟨x, hx⟩)) :=
        hcf i b f' hf' (J i ⟨x, hx⟩) _ (hρ ⟨x, hx⟩ hy)
      have e3 : b (J i ⟨x, hx⟩) = J i (a ⟨x, hx⟩) := LinearMap.congr_fun hab ⟨x, hx⟩
      rw [e1, e2, e3]
      exact hρ _ _
    | zero => exact ⟨X.zero_mem, by
        show ρ (c i a 0) = c i b (ρ 0)
        simp only [map_zero]⟩
    | add u v _ _ h1 h2 =>
      obtain ⟨p, hp⟩ := h1
      obtain ⟨q, hq⟩ := h2
      refine ⟨X.add_mem p q, ?_⟩
      show ρ (c i a (⟨u, p⟩ + ⟨v, q⟩)) = c i b (ρ (⟨u, p⟩ + ⟨v, q⟩))
      rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), hp, hq]
    | smul k u _ h1 =>
      obtain ⟨p, hp⟩ := h1
      refine ⟨X.smul_mem k p, ?_⟩
      show ρ (c i a (k • ⟨u, p⟩)) = c i b (ρ (k • ⟨u, p⟩))
      rw [map_smul, map_smul, map_smul, map_smul, hp]
  exact LinearMap.ext fun v => (key v (hsp i v.2)).2
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.IsotypicSubspaceProductClosed
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_res {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (X : Submodule ℂ H) :
    ∀ (r : ℕ) (T : Fin r → H →L[ℂ] H) (t : Fin r → Module.End ℂ X), (∀ i (v : X), ((t i v : X) : H) = T i v) →
      ∀ v : X, (((List.ofFn t).prod v : X) : H) = (List.ofFn T).prod v := by
  intro r
  induction r with
  | zero => intro T t _ v; simp
  | succ r ih =>
    intro T t h v
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_apply, h,
      ih (fun i => T i.succ) (fun i => t i.succ) (fun i => h _) v]
    rfl

set_option maxHeartbeats 800000 in
theorem UpperTheory.isotypic_subspace_product_closed :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (Z : Submodule ℂ H) (U : ∀ i, Subgroup (G i)) (c : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i)) →ₐ[ℂ] Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) (T : Fin r → H →L[ℂ] H) (B : ∀ i, Module.End ℂ (fixedVectors (τ i) (U i))), (∀ i t f, Eqv (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)) f → ∀ (x : fixedVectors (τ i) (U i)) (y : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))), (y : H) = f x → ((c i t y : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) : H) = f (t x)) → (∀ i, (Z ⊓ ⨅ i, fixU (π i) (U i)) ≤ spanFix (τ i) (π i) (Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)) (U i)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x : fixedVectors (τ i) (U i), T i (f x) = f (B i x)) → ∀ v : ↥(Z ⊓ ⨅ i, fixU (π i) (U i)), (((List.ofFn fun i => c i (B i)).prod v : ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) : H) = (List.ofFn T).prod v := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ Z U c T B hc1 hle hB
  let X : Submodule ℂ H := Z ⊓ ⨅ i, fixU (π i) (U i)
  have hX : X = Z ⊓ ⨅ i, fixU (π i) (U i) := rfl
  let D : Fin r → Submodule ℂ H := fun i => Z ⊓ ⨅ j, ⨅ _ : j ≠ i, fixU (π j) (U j)
  have hD : ∀ i v, v ∈ D i ↔ v ∈ Z ∧ ∀ j, j ≠ i → v ∈ fixU (π j) (U j) := fun i v => by
    simp only [D, Submodule.mem_inf, Submodule.mem_iInf]
  have hXD : ∀ i, X = D i ⊓ fixU (π i) (U i) := fun i => by
    ext v
    simp only [hX, Submodule.mem_inf, Submodule.mem_iInf, hD]
    refine ⟨fun h => ⟨⟨h.1, fun j _ => h.2 j⟩, h.2 i⟩, fun h => ⟨h.1.1, fun j => ?_⟩⟩
    by_cases e : j = i
    · exact e ▸ h.2
    · exact h.1.2 j e
  have hm : ∀ i f, Eqv (τ i) (π i) (D i) f → ∀ x : fixedVectors (τ i) (U i), f x ∈ X := fun i f hf x => by
    rw [hXD i]
    exact ⟨hf.mem _, fun u hu => by rw [← hf.map, mem_fixedVectors.1 x.2 u hu]⟩
  refine prod_res X r T _ fun i v => ?_
  have key : ∀ y ∈ spanFix (τ i) (π i) (D i) (U i), ∃ h : y ∈ X, ((c i (B i) ⟨y, h⟩ : X) : H) = T i y := fun y hy => by
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨f, hf, x, hx, rfl⟩ := hy
      exact ⟨hm i f hf ⟨x, hx⟩, (hc1 i (B i) f hf ⟨x, hx⟩ _ rfl).trans (hB i f ⟨fun _ => trivial, hf.map⟩ ⟨x, hx⟩).symm⟩
    | zero => exact ⟨X.zero_mem, (congrArg Subtype.val (map_zero (c i (B i)))).trans (map_zero (T i)).symm⟩
    | add u v _ _ h1 h2 =>
      obtain ⟨a, ha⟩ := h1
      obtain ⟨b, hb⟩ := h2
      refine ⟨X.add_mem a b, (congrArg Subtype.val (map_add (c i (B i)) ⟨u, a⟩ ⟨v, b⟩)).trans ?_⟩
      rw [map_add (f := _), ← ha, ← hb]; rfl
    | smul k u _ h1 =>
      obtain ⟨a, ha⟩ := h1
      refine ⟨X.smul_mem k a, (congrArg Subtype.val (map_smul (c i (B i)) k ⟨u, a⟩)).trans ?_⟩
      rw [map_smul, ← ha]; rfl
  exact (key v (hle i v.2)).2
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.TraceRestrictEqOfHasFinTrace
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.trace_restrict_eq_of_hasFinTrace :
    ∀ (S : Type) [AddCommGroup S] [Module ℂ S] (Q Q' : Submodule ℂ S) [FiniteDimensional ℂ Q'] (g : S →ₗ[ℂ] S) (t : ℂ) (m : Module.End ℂ Q') (e : Q' →ₗ[ℂ] S), Q ≤ Q' → HasFinTrace g t → (∀ x, g x ∈ Q) → (∀ x : Q', ((m x : Q') : S) = g (e x)) → (∀ x : Q', (x : S) ∈ Q → e x = x) → LinearMap.trace ℂ Q' m = t := by
  intro S _ _ Q Q' _ g t m e hQ hg hgQ hm he
  obtain ⟨hfd, hr⟩ := hg
  haveI := hfd
  have hWQ : LinearMap.range g ≤ Q := by
    rintro _ ⟨x, rfl⟩
    exact hgQ x
  let p : Q' →ₗ[ℂ] LinearMap.range g :=
    (g ∘ₗ e).codRestrict (LinearMap.range g) fun x => LinearMap.mem_range_self g (e x)
  let q : LinearMap.range g →ₗ[ℂ] Q' := Submodule.inclusion (hWQ.trans hQ)
  have e1 : m = q ∘ₗ p := by
    ext x
    exact hm x
  have e2 : g.restrict (p := LinearMap.range g) (q := LinearMap.range g)
      (fun v _ => LinearMap.mem_range_self g v) = p ∘ₗ q := by
    ext x
    exact congrArg g (he (q x) (hWQ x.2)).symm
  rw [e1, LinearMap.trace_comp_comm', ← e2, hr]
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.ExistsScalarOfTwistedIntertwinerCommutingAlgebra
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.LinearFormEqMulTraceOfTwistedInvariant
open scoped BigOperators

theorem UpperTheory.linearForm_eq_mul_trace_of_twisted_invariant :
    ∀ (P : Type) [AddCommGroup P] [Module ℂ P] [FiniteDimensional ℂ P] (J E : Module.End ℂ P) (l : Module.End ℂ P →ₗ[ℂ] ℂ), LinearMap.trace ℂ P (E * J) = 1 → (∀ a a' b : Module.End ℂ P, a' * J = J * a → l (b * a') = l (a * b)) → ∀ b, l b = l E * LinearMap.trace ℂ P (b * J) := by
  intro P _ _ _ J E l hE h
  have tr : ∀ (η : P →ₗ[ℂ] ℂ) (u : P), LinearMap.trace ℂ P (η.smulRight u) = η u := by
    intro η u
    have h0 := LinearMap.trace_eq_contract_apply ℂ P
      (TensorProduct.tmul ℂ (show Module.Dual ℂ P from η) u)
    have h1 : dualTensorHom ℂ P P (TensorProduct.tmul ℂ (show Module.Dual ℂ P from η) u)
        = η.smulRight u := by
      apply LinearMap.ext
      intro y
      simp [dualTensorHom_apply]
    rw [h1] at h0
    rw [h0]
    simp [contractLeft_apply]
  have key : ∀ (u x : P) (η ξ : P →ₗ[ℂ] ℂ),
      ξ (J x) * l (η.smulRight u) = η (J u) * l (ξ.smulRight x) := by
    intro u x η ξ
    have hc : (η.smulRight (J x)) * J = J * ((η ∘ₗ J).smulRight x) := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply]
    have h1 := h ((η ∘ₗ J).smulRight x) (η.smulRight (J x)) (ξ.smulRight u) hc
    have e1 : ξ.smulRight u * η.smulRight (J x) = ξ (J x) • η.smulRight u := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply, smul_smul, mul_comm]
    have e2 : (η ∘ₗ J).smulRight x * ξ.smulRight u = η (J u) • ξ.smulRight x := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply, smul_smul, mul_comm]
    rw [e1, e2, map_smul, map_smul] at h1
    simpa [smul_eq_mul] using h1
  have hJ : ∃ x, J x ≠ 0 := by
    by_contra hne
    push_neg at hne
    have hJ0 : J = 0 := LinearMap.ext hne
    rw [hJ0] at hE
    simp at hE
  obtain ⟨x₀, hx₀⟩ := hJ
  have hφ : ∃ φ : Module.Dual ℂ P, φ (J x₀) ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ (J x₀)).1 hne)
  obtain ⟨φ, hφ⟩ := hφ
  obtain ⟨ξ₀, hξ₀⟩ : ∃ ξ₀ : P →ₗ[ℂ] ℂ, ξ₀ (J x₀) = 1 :=
    ⟨(φ (J x₀))⁻¹ • φ, by simp [hφ]⟩
  have rank1 : ∀ (η : P →ₗ[ℂ] ℂ) (u : P),
      l (η.smulRight u) = l (ξ₀.smulRight x₀) * LinearMap.trace ℂ P (η.smulRight u * J) := by
    intro η u
    have e : η.smulRight u * J = (η ∘ₗ J).smulRight u := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply]
    have hk := key u x₀ η ξ₀
    rw [hξ₀, one_mul] at hk
    rw [e, tr, hk]
    simp [mul_comm]
  have all : ∀ b : Module.End ℂ P,
      l b = l (ξ₀.smulRight x₀) * LinearMap.trace ℂ P (b * J) := by
    intro b
    obtain ⟨t, rfl⟩ := (dualTensorHomEquiv ℂ P P).surjective b
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul η u =>
      have h1 : dualTensorHomEquiv ℂ P P (TensorProduct.tmul ℂ η u)
          = LinearMap.smulRight (show P →ₗ[ℂ] ℂ from η) u := by
        apply LinearMap.ext
        intro y
        simp [dualTensorHomEquiv, dualTensorHom_apply]
      rw [h1]
      exact rank1 η u
    | add s t hs ht =>
      rw [map_add (f := _), map_add (f := _), add_mul, map_add (f := _), mul_add, hs, ht]
  intro b
  have hκ := all E
  rw [hE, mul_one] at hκ
  rw [hκ]
  exact all b
end

open scoped BigOperators

theorem UpperTheory.exists_scalar_of_twisted_intertwiner_commuting_algebras :
    ∀ (r : ℕ) (X : Type) [AddCommGroup X] [Module ℂ X] [FiniteDimensional ℂ X] (P : Fin r → Type) [∀ i, AddCommGroup (P i)] [∀ i, Module ℂ (P i)] [∀ i, FiniteDimensional ℂ (P i)] (c : ∀ i, Module.End ℂ (P i) →ₐ[ℂ] Module.End ℂ X) (J : ∀ i, Module.End ℂ (P i)) (ρ : Module.End ℂ X), (∀ i j, i ≠ j → ∀ s t, Commute (c i s) (c j t)) → (∀ i, J i ≠ 0) → (∀ i a b, b * J i = J i * a → ρ * c i a = c i b * ρ) → ∃ κ : ℂ, ∀ b : ∀ i, Module.End ℂ (P i), LinearMap.trace ℂ X ((List.ofFn fun i => c i (b i)).prod * ρ) = κ * ∏ i, LinearMap.trace ℂ (P i) (b i * J i) := by
  intro r X _ _ _ P _ _ _ c J ρ hc hJ hρ
  have hE : ∀ i, ∃ E : Module.End ℂ (P i), LinearMap.trace ℂ (P i) (E * J i) = 1 := by
    intro i
    have hx : ∃ x, J i x ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hJ i (LinearMap.ext hne)
    obtain ⟨x₀, hx₀⟩ := hx
    have hφ : ∃ φ : Module.Dual ℂ (P i), φ (J i x₀) ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hx₀ ((Module.forall_dual_apply_eq_zero_iff ℂ (J i x₀)).1 hne)
    obtain ⟨φ, hφ⟩ := hφ
    refine ⟨((φ (J i x₀))⁻¹ • φ).smulRight x₀, ?_⟩
    have e : (((φ (J i x₀))⁻¹ • φ).smulRight x₀) * J i
        = dualTensorHom ℂ (P i) (P i)
            (TensorProduct.tmul ℂ (((φ (J i x₀))⁻¹ • φ) ∘ₗ J i) x₀) := by
      apply LinearMap.ext
      intro y
      simp [Module.End.mul_apply, dualTensorHom_apply]
    rw [e, LinearMap.trace_eq_contract_apply ℂ (P i)]
    simp [contractLeft_apply, hφ]
  choose E hE using hE
  obtain ⟨F, hF⟩ : ∃ F : (∀ i, Module.End ℂ (P i)) → ℂ, ∀ b, F b =
      LinearMap.trace ℂ X ((List.ofFn fun i => c i (b i)).prod * ρ) := ⟨_, fun _ => rfl⟩
  have step : ∀ (b : ∀ i, Module.End ℂ (P i)) (i : Fin r) (y : Module.End ℂ (P i)),
      F (Function.update b i y)
        = F (Function.update b i (E i)) * LinearMap.trace ℂ (P i) (y * J i) := by
    intro b i y
    obtain ⟨a, ha⟩ : ∃ a : Fin r → Module.End ℂ X, a = fun j => c j (b j) := ⟨_, rfl⟩
    obtain ⟨Q, hQ⟩ : ∃ Q : Module.End ℂ X, Q = (List.ofFn (Function.update a i 1)).prod :=
      ⟨_, rfl⟩
    have fac : ∀ z, (List.ofFn fun j => c j (Function.update b i z j)).prod = c i z * Q := by
      intro z
      have h := (UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (Module.End ℂ X) r (fun j => c j (Function.update b i z j))
        (fun p q hpq => hc p q hpq _ _) i).1
      have e : Function.update (fun j => c j (Function.update b i z j)) i 1
          = Function.update a i 1 := by
        funext j
        by_cases hj : j = i
        · subst hj
          rw [Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hj, Function.update_of_ne hj, Function.update_of_ne hj, ha]
      rw [h, e, Function.update_self, hQ]
    have com : ∀ z, Commute (c i z) Q := by
      intro z
      rw [hQ]
      refine (UpperTheory.list_ofFn_prod_eq_mul_update_one_of_pairwise_commute (Module.End ℂ X) r a ?_ i).2 (c i z) ?_
      · intro p q hpq
        rw [ha]
        exact hc p q hpq _ _
      · intro j hj
        rw [ha]
        exact hc i j (Ne.symm hj) _ _
    obtain ⟨l, hl⟩ : ∃ l : Module.End ℂ (P i) →ₗ[ℂ] ℂ,
        ∀ z, l z = LinearMap.trace ℂ X (c i z * Q * ρ) :=
      ⟨(LinearMap.trace ℂ X) ∘ₗ (LinearMap.mulRight ℂ (Q * ρ)) ∘ₗ (c i).toLinearMap, by
        intro z
        simp [mul_assoc]⟩
    have hyp : ∀ a a' t : Module.End ℂ (P i), a' * J i = J i * a → l (t * a') = l (a * t) := by
      intro a a' t h
      have h1 := hρ i a a' h
      have e1 : c i (t * a') * Q * ρ = (c i t * Q * ρ) * c i a := by
        rw [map_mul, mul_assoc (c i t), (com a').eq, mul_assoc (c i t * Q) ρ, h1]
        simp only [mul_assoc]
      have e2 : c i (a * t) * Q * ρ = c i a * (c i t * Q * ρ) := by
        rw [map_mul]
        simp only [mul_assoc]
      rw [hl, hl, e1, e2, LinearMap.trace_mul_comm]
    have key := UpperTheory.linearForm_eq_mul_trace_of_twisted_invariant (P i) (J i) (E i) l (hE i) hyp y
    rw [hF, hF, fac, fac, ← hl, ← hl]
    exact key
  have ind : ∀ (S : Finset (Fin r)) (b : ∀ i, Module.End ℂ (P i)),
      F b = F (S.piecewise E b) * ∏ i ∈ S, LinearMap.trace ℂ (P i) (b i * J i) := by
    intro S b
    induction S using Finset.induction_on with
    | empty => simp
    | insert i S hi ih =>
      have hb : S.piecewise E b i = b i := Finset.piecewise_eq_of_notMem _ _ _ hi
      have h1 := step (S.piecewise E b) i (b i)
      rw [← hb, Function.update_eq_self, hb] at h1
      rw [Finset.prod_insert hi, Finset.piecewise_insert, ih, h1]
      ring
  refine ⟨F E, fun b => ?_⟩
  have h := ind Finset.univ b
  rw [Finset.piecewise_univ] at h
  rw [← hF, h]
end

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

private theorem prod_fix' {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (v : H) :
    ∀ l : List (H →L[ℂ] H), (∀ a ∈ l, a v = v) → l.prod v = v
  | [], _ => rfl
  | a :: l, hl => by
    rw [List.prod_cons]
    show a (l.prod v) = v
    rw [prod_fix' v l fun b hb => hl b (List.mem_cons_of_mem _ hb), hl a List.mem_cons_self]

theorem UpperTheory.isotypic_intersection_product_eq :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∀ L : ∀ i, Subgroup (G i), (∀ i, IsCompact (L i : Set (G i)) ∧ IsOpen (L i : Set (G i))) → (Z ⊓ ⨅ i, fixU (π i) (L i)) ≠ ⊥ → ∃ κ : ℂ, ∀ (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (t : Fin r → ℂ), (∀ i v, T i v ∈ fixU (π i) (L i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (L i)) → (∀ i, HasFinTrace (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)) → trOn (Z ⊓ ⨅ i, fixU (π i) (L i)) ((List.ofFn T).prod ∘L R) = κ * ∏ i, t i := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI L hL hne
  obtain ⟨K, hK, hKL, hsK⟩ : ∃ K : ∀ i, Subgroup (G i),
      (∀ i, IsCompact (K i : Set (G i)) ∧ IsOpen (K i : Set (G i))) ∧ (∀ i, K i ≤ L i) ∧
        ∀ i, ∀ k ∈ K i, (s i).symm k ∈ L i := by
    refine ⟨fun i => L i ⊓ (L i).map ((s i).toMulEquiv : G i →* G i), fun i => ⟨?_, ?_⟩, fun i => inf_le_left, ?_⟩
    · have h2 : IsCompact (((L i).map ((s i).toMulEquiv : G i →* G i) : Subgroup (G i)) : Set (G i)) := by
        rw [Subgroup.coe_map]
        exact (hL i).1.image (s i).continuous
      rw [Subgroup.coe_inf]
      exact (hL i).1.inter h2
    · have h2 : IsOpen (((L i).map ((s i).toMulEquiv : G i →* G i) : Subgroup (G i)) : Set (G i)) := by
        rw [Subgroup.coe_map]
        exact (s i).toHomeomorph.isOpenMap _ (hL i).2
      rw [Subgroup.coe_inf]
      exact (hL i).2.inter h2
    · rintro i k ⟨-, y, hy, rfl⟩
      show (s i).symm (s i y) ∈ L i
      rw [(s i).symm_apply_apply]
      exact hy
  have hXX : (Z ⊓ ⨅ i, fixU (π i) (L i)) ≤ (Z ⊓ ⨅ i, fixU (π i) (K i)) := fun v hv => by
    obtain ⟨h1, h2⟩ := Submodule.mem_inf.1 hv
    exact Submodule.mem_inf.2 ⟨h1, (Submodule.mem_iInf _).2 fun j u hu =>
      (Submodule.mem_iInf _).1 h2 j u (hKL j hu)⟩
  haveI hfdX : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (K i)) := hadm K hK
  haveI hfdL : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (L i)) := hadm L hL
  have hneX : (Z ⊓ ⨅ i, fixU (π i) (K i)) ≠ ⊥ := fun e => hne (le_bot_iff.1 (e ▸ hXX))
  obtain ⟨h1, c, hcc, hcf, hsp⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV K hK hfdX hneX
  obtain ⟨h1L, -⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV L hL hfdL hne
  haveI : ∀ i, FiniteDimensional ℂ (fixedVectors (τ i) (K i)) := fun i => (h1 i).1
  have hLK : ∀ i, fixedVectors (τ i) (L i) ≤ fixedVectors (τ i) (K i) := fun i x hx =>
    mem_fixedVectors.2 fun k hk => mem_fixedVectors.1 hx k (hKL i hk)
  have hIm : ∀ i, ∀ x ∈ fixedVectors (τ i) (L i), I i x ∈ fixedVectors (τ i) (K i) := fun i x hx =>
    mem_fixedVectors.2 fun k hk => by
      have h := hI i ((s i).symm k) x
      rw [(s i).apply_symm_apply, mem_fixedVectors.1 hx _ (hsK i k hk)] at h
      exact h.symm
  let e : ∀ i, fixedVectors (τ i) (K i) →ₗ[ℂ] S i := fun i =>
    (fixedVectors (τ i) (L i)).subtype ∘ₗ fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 ∘ₗ (fixedVectors (τ i) (K i)).subtype
  let J : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) := fun i =>
    (((I i : S i →ₗ[ℂ] S i)) ∘ₗ e i).codRestrict (fixedVectors (τ i) (K i)) fun x =>
      hIm i _ (fixedProj (τ i) (hsm i) (hL i).1 (hL i).2 x).2
  have he : ∀ i (x : fixedVectors (τ i) (K i)), (x : S i) ∈ fixedVectors (τ i) (L i) → e i x = x := fun i x hx =>
    fixedProj_apply_of_mem (hsm i) (hL i).1 (hL i).2 hx
  have hJ0 : ∀ i, J i ≠ 0 := fun i h0 => by
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (h1L i).2
    have h := LinearMap.congr_fun h0 ⟨x, hLK i hx⟩
    have h' : I i (e i ⟨x, hLK i hx⟩) = 0 := congrArg Subtype.val h
    rw [he i ⟨x, hLK i hx⟩ hx] at h'
    exact hx0 ((I i).map_eq_zero_iff.1 h')
  obtain ⟨ρ, hρ1, hρ2⟩ := UpperTheory.isotypic_submodule_product_decomposition r G H S π τ Z hsm hcm hZc hZi s I R hRZ hRs hI L K hL hKL hsK c J
    (fun i x => rfl) hcf hsp
  obtain ⟨κ, hκ⟩ := UpperTheory.exists_scalar_of_twisted_intertwiner_commuting_algebras r ↥(Z ⊓ ⨅ i, fixU (π i) (K i)) (fun i => fixedVectors (τ i) (K i)) c J ρ hcc hJ0 hρ2
  refine ⟨κ, fun T A t hT1 hT2 hT3 hT4 hA ht => ?_⟩
  let B : ∀ i, Module.End ℂ (fixedVectors (τ i) (K i)) := fun i =>
    (A i ∘ₗ (fixedVectors (τ i) (K i)).subtype).codRestrict (fixedVectors (τ i) (K i)) fun x => hLK i (hA i _)
  have hcomp := UpperTheory.isotypic_subspace_product_closed r G H S π τ Z K c T B hcf hsp (fun i f hf x => hT4 i f hf x)
  have hPrZ : ∀ v ∈ Z, (List.ofFn fun j => prj (fixU (π j) (L j))).prod v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)) :=
    UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L (fun j => prj (fixU (π j) (L j)))
      (fun i v => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).1 v)
      (fun i v hv => (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.2.1 Z hZc (hZi i) v hv)
      (fun i j hij h v => ((UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G j) H (π i) (π j) (L i) (L j)).2.2.2 (hcm i j hij)).1 h v)
  have hTZ := UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z L T hT1 hT2 hT3
  have hPrFix : ∀ v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)), (List.ofFn fun j => prj (fixU (π j) (L j))).prod v = v := fun v hv =>
    prod_fix' v _ fun a ha => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
      exact (UpperTheory.fixedProjection_invariant_and_commuting_reps (G i) (G i) H (π i) (π i) (L i) (L i)).2.1 v
        ((Submodule.mem_iInf _).1 (Submodule.mem_inf.1 hv).2 i)
  let W : H →L[ℂ] H := (List.ofFn T).prod ∘L R ∘L (List.ofFn fun j => prj (fixU (π j) (L j))).prod
  have e1 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (K i)) (Z ⊓ ⨅ i, fixU (π i) (K i)) W).1
    ((List.ofFn fun i => c i (B i)).prod * ρ) fun v => by
      rw [Module.End.mul_apply, hcomp, hρ1]
      rfl
  have hWX : ∀ v ∈ (Z ⊓ ⨅ i, fixU (π i) (K i)), W v ∈ (Z ⊓ ⨅ i, fixU (π i) (L i)) := fun v hv =>
    hTZ _ (hRZ _ (Submodule.mem_inf.1 (hPrZ v (Submodule.mem_inf.1 hv).1)).1)
  have e2 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (K i)) W).2 hXX hWX
  let b : Module.End ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (L i)) :=
    ((W : H →ₗ[ℂ] H) ∘ₗ (Z ⊓ ⨅ i, fixU (π i) (L i)).subtype).codRestrict _ fun v => hWX _ (hXX v.2)
  have e3 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (L i)) W).1 b fun v => rfl
  have e4 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (L i)) (Z ⊓ ⨅ i, fixU (π i) (L i))
    ((List.ofFn T).prod ∘L R)).1 b fun v => by
      show W v = _
      show (List.ofFn T).prod (R ((List.ofFn fun j => prj (fixU (π j) (L j))).prod (v : H))) = _
      rw [hPrFix _ v.2]
      rfl
  have ht' : ∀ i, LinearMap.trace ℂ (fixedVectors (τ i) (K i)) (B i * J i) = t i := fun i =>
    UpperTheory.trace_restrict_eq_of_hasFinTrace (S i) (fixedVectors (τ i) (L i)) (fixedVectors (τ i) (K i)) (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)
      (B i * J i) (e i) (hLK i) (ht i) (fun x => hA i _) (fun x => rfl) (he i)
  rw [e4, ← e3, ← e2, e1, hκ B]
  simp only [ht']
end

section -- merged from Development.AutomorphicArithmetic.TwistedTraces.TwistedIntertwinerFixedVectorsOfIrreducible
section -- merged from Development.AutomorphicArithmetic.TwistedTraces.FiniteDimensionalFixedVectorsIsotypicOfIrreducib
open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.finiteDimensional_fixedVectors_isotypic_of_irreducible :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (_ : GroundTheory.Automorphic.IsSmooth τ) (_ : τ.IsIrreducible) (π : UnitaryRep G H) (K : Subgroup G), IsCompact (K : Set G) → IsOpen (K : Set G) → FiniteDimensional ℂ (fixedVectors τ K) → fixedVectors τ K ≠ ⊥ → ∀ t : Module.End ℂ (fixedVectors τ K), ∃ (T : H →L[ℂ] H) (A : S →ₗ[ℂ] S), ((∀ v, T v ∈ fixU π K) ∧ (∀ x, A x ∈ fixedVectors τ K) ∧ (∀ D : Submodule ℂ H, IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, T v ∈ D) ∧ (∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H), (∀ g h v, π g (π' h v) = π' h (π g v)) → ∀ h v, T (π' h v) = π' h (T v)) ∧ (∀ f, Eqv τ π ⊤ f → ∀ x, T (f x) = f (A x))) ∧ ∀ x : fixedVectors τ K, A x = t x := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ hirr π K hKc hKo hfd hne t
  haveI := hfd
  haveI : Nontrivial (fixedVectors τ K) := Submodule.nontrivial_iff_ne_bot.2 hne
  obtain ⟨p1, -, p3, -⟩ := UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π K K
  let e : S →ₗ[ℂ] fixedVectors τ K := fixedProj τ hτ hKc hKo
  let b : G → Module.End ℂ (fixedVectors τ K) := fun g => e ∘ₗ τ g ∘ₗ (fixedVectors τ K).subtype
  have he : ∀ y : fixedVectors τ K, e y = y := fun y =>
    Subtype.ext (fixedProj_apply_of_mem hτ hKc hKo y.2)
  have hq : ∀ f, Eqv τ π ⊤ f → ∀ x, prj (fixU π K) (f x) = f (e x) := fun f hf x =>
    UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π K hKc hKo f hf x
  have hcomm : ∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H),
      (∀ g h v, π g (π' h v) = π' h (π g v)) →
        ∀ h v, prj (fixU π K) (π' h v) = π' h (prj (fixU π K) v) := by
    intro G' _ _ π' hc
    exact ((UpperTheory.fixedProjection_invariant_and_commuting_reps G G' H π π' K ⊥).2.2.2 hc).1
  have htop : Algebra.adjoin ℂ (Set.range b) = ⊤ := by
    obtain ⟨c, h1, h2⟩ := UpperTheory.exists_algHom_end_intertwining_mem_adjoin (fixedVectors τ K) (fixedVectors τ K) {LinearMap.id}
      (Set.range fun g => (b g, b g)) (by simp) (by
        rintro _ ⟨g, rfl⟩ _ rfl
        rfl) (by
        intro x hx
        let W : Subrepresentation τ := ⟨Submodule.span ℂ (Set.range fun g => τ g x), fun g v hv => by
          refine (Submodule.map_span_le (τ g) _ _).2 ?_ (Submodule.mem_map_of_mem hv)
          rintro _ ⟨h, rfl⟩
          exact Submodule.subset_span ⟨g * h, by simp⟩⟩
        have hW : Submodule.span ℂ (Set.range fun g => τ g x) = ⊤ := by
          rcases eq_bot_or_eq_top W with h | h
          · have h' : Submodule.span ℂ (Set.range fun g => τ g x) = ⊥ := congrArg Subrepresentation.toSubmodule h
            have : τ 1 x ∈ Submodule.span ℂ (Set.range fun g => τ g x) := Submodule.subset_span ⟨1, rfl⟩
            rw [h', map_one] at this
            exact (hx (Subtype.ext this)).elim
          · exact congrArg Subrepresentation.toSubmodule h
        rw [eq_top_iff]
        rintro y -
        rw [← he y]
        refine (Submodule.map_span_le e (Set.range fun g => τ g x) _).2 ?_ (Submodule.mem_map_of_mem (hW ▸ Submodule.mem_top))
        rintro _ ⟨g, rfl⟩
        exact Submodule.subset_span ⟨_, ⟨g, rfl⟩, rfl⟩)
    rw [eq_top_iff]
    intro s _
    have hcs : c s = s := by simpa using h1 s LinearMap.id rfl
    rw [← hcs]
    refine Algebra.adjoin_mono ?_ (h2 s)
    rintro _ ⟨_, ⟨g, rfl⟩, rfl⟩
    exact ⟨g, rfl⟩
  have ht : t ∈ Algebra.adjoin ℂ (Set.range b) := by rw [htop]; trivial
  induction ht using Algebra.adjoin_induction with
  | mem s hs =>
    obtain ⟨g, rfl⟩ := hs
    refine ⟨prj (fixU π K) ∘L π g ∘L prj (fixU π K),
      (fixedVectors τ K).subtype ∘ₗ e ∘ₗ τ g ∘ₗ (fixedVectors τ K).subtype ∘ₗ e,
      ⟨fun v => p1 _, fun x => (e _).2, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact p3 D hD hinv _ (hinv g _ (p3 D hD hinv _ hv))
    · intro G' _ _ π' hc h v
      show prj (fixU π K) (π g (prj (fixU π K) (π' h v))) = π' h (prj (fixU π K) (π g (prj (fixU π K) v)))
      rw [hcomm G' π' hc h v, hc, hcomm G' π' hc]
    · intro f hf x
      show prj (fixU π K) (π g (prj (fixU π K) (f x))) = f (e (τ g (e x)))
      rw [hq f hf x, ← hf.map, hq f hf]
    · intro x
      show ((e (τ g ((e (x : S) : fixedVectors τ K) : S)) : fixedVectors τ K) : S) = _
      rw [he x]
      rfl
  | algebraMap z =>
    refine ⟨z • prj (fixU π K), z • ((fixedVectors τ K).subtype ∘ₗ e),
      ⟨fun v => (fixU π K).smul_mem z (p1 v), fun x => (fixedVectors τ K).smul_mem z (e x).2, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact D.smul_mem z (p3 D hD hinv _ hv)
    · intro G' _ _ π' hc h v
      show z • prj (fixU π K) (π' h v) = π' h (z • prj (fixU π K) v)
      rw [hcomm G' π' hc h v, map_smul]
    · intro f hf x
      show z • prj (fixU π K) (f x) = f (z • ((e x : fixedVectors τ K) : S))
      rw [hq f hf x, map_smul]
    · intro x
      show z • ((e (x : S) : fixedVectors τ K) : S) = _
      rw [he x]
      simp [Module.algebraMap_end_apply]
  | add s u _ _ hs hu =>
    obtain ⟨T₁, A₁, ⟨a1, a2, a3, a4, a5⟩, a6⟩ := hs
    obtain ⟨T₂, A₂, ⟨b1, b2, b3, b4, b5⟩, b6⟩ := hu
    refine ⟨T₁ + T₂, A₁ + A₂, ⟨fun v => (fixU π K).add_mem (a1 v) (b1 v),
      fun x => (fixedVectors τ K).add_mem (a2 x) (b2 x), ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact D.add_mem (a3 D hD hinv v hv) (b3 D hD hinv v hv)
    · intro G' _ _ π' hc h v
      show T₁ (π' h v) + T₂ (π' h v) = π' h (T₁ v + T₂ v)
      rw [a4 G' π' hc, b4 G' π' hc, map_add (f := _)]
    · intro f hf x
      show T₁ (f x) + T₂ (f x) = f (A₁ x + A₂ x)
      rw [a5 f hf, b5 f hf, map_add (f := _)]
    · intro x
      show A₁ x + A₂ x = _
      rw [a6 x, b6 x]
      rfl
  | mul s u _ _ hs hu =>
    obtain ⟨T₁, A₁, ⟨a1, a2, a3, a4, a5⟩, a6⟩ := hs
    obtain ⟨T₂, A₂, ⟨b1, b2, b3, b4, b5⟩, b6⟩ := hu
    refine ⟨T₁ ∘L T₂, A₁ ∘ₗ A₂, ⟨fun v => a1 _, fun x => a2 _, ?_, ?_, ?_⟩, ?_⟩
    · intro D hD hinv v hv
      exact a3 D hD hinv _ (b3 D hD hinv v hv)
    · intro G' _ _ π' hc h v
      show T₁ (T₂ (π' h v)) = π' h (T₁ (T₂ v))
      rw [b4 G' π' hc, a4 G' π' hc]
    · intro f hf x
      show T₁ (T₂ (f x)) = f (A₁ (A₂ x))
      rw [b5 f hf, a5 f hf]
    · intro x
      show A₁ (A₂ x) = _
      rw [b6 x, a6 (u x)]
      rfl
end

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.twisted_intertwiner_fixedVectors_of_irreducible :
    ∀ (G H S : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [AddCommGroup S] [Module ℂ S] (τ : Representation ℂ G S) (_ : GroundTheory.Automorphic.IsSmooth τ) (_ : τ.IsIrreducible) (π : UnitaryRep G H) (s : G ≃ₜ* G) (I : S ≃ₗ[ℂ] S), (∀ g x, I (τ g x) = τ (s g) (I x)) → (∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) → FiniteDimensional ℂ (fixedVectors τ K)) → ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) → fixedVectors τ K ≠ ⊥ → ∃ (T : H →L[ℂ] H) (A : S →ₗ[ℂ] S) (t : ℂ), ((∀ v, T v ∈ fixU π K) ∧ (∀ x, A x ∈ fixedVectors τ K) ∧ (∀ D : Submodule ℂ H, IsClosed (D : Set H) → π.IsInvariant D → ∀ v ∈ D, T v ∈ D) ∧ (∀ (G' : Type) [Group G'] [TopologicalSpace G'] (π' : UnitaryRep G' H), (∀ g h v, π g (π' h v) = π' h (π g v)) → ∀ h v, T (π' h v) = π' h (T v)) ∧ (∀ f, Eqv τ π ⊤ f → ∀ x, T (f x) = f (A x))) ∧ HasFinTrace (A ∘ₗ (I : S →ₗ[ℂ] S)) t ∧ t ≠ 0 := by
  intro G H S _ _ _ _ _ _ _ _ _ _ _ τ hτ hirr π s I hI hfd K hKc hKo hne
  let sK : Subgroup G := K.map s.toMulEquiv.toMonoidHom
  have hsKc : IsCompact (sK : Set G) := by
    have : (sK : Set G) = s '' (K : Set G) := rfl
    rw [this]
    exact hKc.image s.continuous
  have hsKo : IsOpen (sK : Set G) := by
    have : (sK : Set G) = s.toHomeomorph '' (K : Set G) := rfl
    rw [this]
    exact s.toHomeomorph.isOpenMap _ hKo
  let K₁ : Subgroup G := K ⊓ sK
  have hK₁c : IsCompact (K₁ : Set G) := by
    rw [Subgroup.coe_inf]
    exact hKc.inter hsKc
  have hK₁o : IsOpen (K₁ : Set G) := by
    rw [Subgroup.coe_inf]
    exact hKo.inter hsKo
  have hPle : ∀ x ∈ fixedVectors τ K, x ∈ fixedVectors τ K₁ := fun x hx k hk => hx k hk.1
  have hsle : ∀ x ∈ fixedVectors τ sK, x ∈ fixedVectors τ K₁ := fun x hx k hk => hx k hk.2
  have hne₁ : fixedVectors τ K₁ ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have := hPle x hx
    rwa [h] at this
  have hIm : ∀ x ∈ fixedVectors τ K, I x ∈ fixedVectors τ sK := by
    rintro x hx _ ⟨k, hk, rfl⟩
    show τ (s k) (I x) = I x
    rw [← hI, hx k hk]
  have hIs : ∀ y ∈ fixedVectors τ sK, I.symm y ∈ fixedVectors τ K := by
    intro y hy k hk
    apply I.injective
    rw [hI, I.apply_symm_apply]
    exact hy _ ⟨k, hk, rfl⟩
  let ε : S →ₗ[ℂ] fixedVectors τ sK := fixedProj τ hτ hsKc hsKo
  let h : Module.End ℂ (fixedVectors τ K₁) :=
    LinearMap.codRestrict (fixedVectors τ K₁)
      ((I.symm : S →ₗ[ℂ] S) ∘ₗ (fixedVectors τ sK).subtype ∘ₗ ε ∘ₗ (fixedVectors τ K₁).subtype)
      (fun x => hPle _ (hIs _ (ε x).2))
  obtain ⟨T₀, A₀, ⟨c1, c2, c3, c4, c5⟩, c6⟩ :=
    UpperTheory.finiteDimensional_fixedVectors_isotypic_of_irreducible G H S τ hτ hirr π K₁ hK₁c hK₁o (hfd K₁ hK₁c hK₁o) hne₁ h
  obtain ⟨p1, -, p3, -⟩ := UpperTheory.fixedProjection_invariant_and_commuting_reps G G H π π K K
  let e : S →ₗ[ℂ] fixedVectors τ K := fixedProj τ hτ hKc hKo
  let A : S →ₗ[ℂ] S := (fixedVectors τ K).subtype ∘ₗ e ∘ₗ A₀
  let B : S →ₗ[ℂ] S := A ∘ₗ (I : S →ₗ[ℂ] S)
  have hB : ∀ x ∈ fixedVectors τ K, B x = x := by
    intro x hx
    have hIx := hIm x hx
    have h1 : A₀ (I x) = x := by
      have h2 := c6 ⟨I x, hsle _ hIx⟩
      have h3 : ((ε (I x) : fixedVectors τ sK) : S) = I x := fixedProj_apply_of_mem hτ hsKc hsKo hIx
      have h4 : ((h ⟨I x, hsle _ hIx⟩ : fixedVectors τ K₁) : S) = I.symm (ε (I x) : fixedVectors τ sK) := rfl
      rw [h4, h3, I.symm_apply_apply] at h2
      exact h2
    show ((e (A₀ (I x)) : fixedVectors τ K) : S) = x
    rw [h1]
    exact fixedProj_apply_of_mem hτ hKc hKo hx
  have hR : LinearMap.range B = fixedVectors τ K := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact (e _).2
    · intro x hx
      exact ⟨x, hB x hx⟩
  haveI hfdR : FiniteDimensional ℂ (LinearMap.range B) := by
    rw [hR]
    exact hfd K hKc hKo
  haveI : Nontrivial (LinearMap.range B) := by
    rw [hR]
    exact Submodule.nontrivial_iff_ne_bot.2 hne
  have hrest : (B.restrict (p := LinearMap.range B) (q := LinearMap.range B)
      fun v _ => LinearMap.mem_range_self B v) = LinearMap.id :=
    LinearMap.ext fun y => Subtype.ext (hB y (hR ▸ y.2))
  refine ⟨prj (fixU π K) ∘L T₀, A, (Module.finrank ℂ (LinearMap.range B) : ℂ),
    ⟨fun v => p1 _, fun x => (e _).2, ?_, ?_, ?_⟩, ⟨hfdR, ?_⟩, ?_⟩
  · intro D hD hinv v hv
    exact p3 D hD hinv _ (c3 D hD hinv v hv)
  · intro G' _ _ π' hc g v
    show prj (fixU π K) (T₀ (π' g v)) = π' g (prj (fixU π K) (T₀ v))
    rw [c4 G' π' hc, ((UpperTheory.fixedProjection_invariant_and_commuting_reps G G' H π π' K ⊥).2.2.2 hc).1]
  · intro f hf x
    show prj (fixU π K) (T₀ (f x)) = f (e (A₀ x))
    rw [c5 f hf]
    exact UpperTheory.fixedProjection_apply_equivariant_eq G H S τ hτ π K hKc hKo f hf _
  · show LinearMap.trace ℂ (LinearMap.range B) (B.restrict (p := LinearMap.range B) (q := LinearMap.range B)
      fun v _ => LinearMap.mem_range_self B v) = _
    rw [hrest, LinearMap.trace_id]
  · exact Nat.cast_ne_zero.2 Module.finrank_pos.ne'
end

open MeasureTheory NumberField IsDedekindDomain Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.CuspidalSpectrum GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets GlobalTheory.PRep Formalism.BasicNotions GlobalTheory.CuspRep GlobalTheory.SmGL UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.C.Sf

theorem UpperTheory.isotypic_multiplicity_tensor_product :
    ∀ (r : ℕ) (G : Fin r → Type) [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)] [∀ i, LocallyCompactSpace (G i)] [∀ i, T2Space (G i)] [∀ i, TotallyDisconnectedSpace (G i)] (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (S : Fin r → Type) [∀ i, AddCommGroup (S i)] [∀ i, Module ℂ (S i)] (π : ∀ i, UnitaryRep (G i) H) (τ : ∀ i, Representation ℂ (G i) (S i)) (V Z : Submodule ℂ H), (∀ i, GroundTheory.Automorphic.IsSmooth (τ i)) → (∀ i, (τ i).IsIrreducible) → (∀ i j, i ≠ j → ∀ g h v, π i g (π j h v) = π j h (π i g v)) → IsClosed (Z : Set H) → Z ≤ V → (∀ i, (π i).IsInvariant Z) → (∀ i, V ≤ (spanAll (τ i) (π i) V).topologicalClosure) → (∀ U : ∀ i, Subgroup (G i), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i))) → ∀ (s : ∀ i, G i ≃ₜ* G i) (I : ∀ i, S i ≃ₗ[ℂ] S i) (R : H →L[ℂ] H), (∀ v ∈ Z, R v ∈ Z) → (∀ i g, ∀ v ∈ Z, R (π i g v) = π i (s i g) (R v)) → (∀ i g x, I i (τ i g x) = τ i (s i g) (I i x)) → ∃ c : ℂ, ∀ (U : ∀ i, Subgroup (G i)) (T : Fin r → H →L[ℂ] H) (A : ∀ i, S i →ₗ[ℂ] S i) (t : Fin r → ℂ), (∀ i, IsCompact (U i : Set (G i)) ∧ IsOpen (U i : Set (G i))) → (∀ i v, T i v ∈ fixU (π i) (U i)) → (∀ i, ∀ v ∈ Z, T i v ∈ Z) → (∀ i j, i ≠ j → ∀ h v, T i (π j h v) = π j h (T i v)) → (∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T i (f x) = f (A i x)) → (∀ i x, A i x ∈ fixedVectors (τ i) (U i)) → (∀ i, HasFinTrace (A i ∘ₗ (I i : S i →ₗ[ℂ] S i)) (t i)) → trOn (Z ⊓ ⨅ i, fixU (π i) (U i)) ((List.ofFn T).prod ∘L R) = c * ∏ i, t i := by
  intro r G _ _ _ _ _ _ H _ _ _ S _ _ π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI
  by_cases hZ : Z = ⊥
  · refine ⟨0, fun U T A t hU _ _ _ _ _ _ => ?_⟩
    have hb : (Z ⊓ ⨅ i, fixU (π i) (U i)) = ⊥ := by rw [hZ, bot_inf_eq]
    haveI := hadm U hU
    rw [zero_mul, (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U i)) (Z ⊓ ⨅ i, fixU (π i) (U i))
      ((List.ofFn T).prod ∘L R)).1 0 ?_, map_zero]
    intro v
    have hv0 : (v : H) = 0 := by
      have h : ∀ w ∈ (Z ⊓ ⨅ i, fixU (π i) (U i)), w = 0 := by
        rw [hb]
        simp
      exact h _ v.2
    simp [hv0]
  have hX : ∀ (U : ∀ i, Subgroup (G i)) v, v ∈ Z ⊓ ⨅ i, fixU (π i) (U i) ↔ v ∈ Z ∧ ∀ i, v ∈ fixU (π i) (U i) := fun U v => by
    simp only [Submodule.mem_inf, Submodule.mem_iInf]
  obtain ⟨U₀, hU₀, h0⟩ := UpperTheory.exists_compactOpen_family_inf_fixed_ne_bot r G H π hcm Z hZc hZi hZ
  obtain ⟨hS, -⟩ := UpperTheory.le_closure_spanAll_of_commuting_unitaryReps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm hZ
  have hmono : ∀ L U : ∀ i, Subgroup (G i), (∀ i, L i ≤ U i) → Z ⊓ ⨅ i, fixU (π i) (U i) ≤ Z ⊓ ⨅ i, fixU (π i) (L i) :=
    fun L U h v hv => (hX L v).2 ⟨hv.1, fun i u hu => ((hX U v).1 hv).2 i u (h i hu)⟩
  have hmF : ∀ i (L U : Subgroup (G i)), L ≤ U → ∀ v ∈ fixU (π i) U, v ∈ fixU (π i) L :=
    fun i L U h v hv u hu => hv u (h hu)
  have hmS : ∀ i (L U : Subgroup (G i)), L ≤ U → fixedVectors (τ i) U ≤ fixedVectors (τ i) L :=
    fun i L U h v hv => mem_fixedVectors.2 fun u hu => mem_fixedVectors.1 hv u (h hu)
  have hSK : ∀ i (K : Subgroup (G i)), IsCompact (K : Set (G i)) → IsOpen (K : Set (G i)) →
      FiniteDimensional ℂ (fixedVectors (τ i) K) := by
    intro i K hc ho
    have h := hS (Function.update U₀ i K) (fun j => by
      by_cases e : j = i
      · subst e
        rw [Function.update_self]
        exact ⟨hc, ho⟩
      · rw [Function.update_of_ne e]
        exact hU₀ j) i
    rwa [Function.update_self] at h
  haveI hfd0 : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U₀ i)) := hadm U₀ hU₀
  obtain ⟨h1, -⟩ := UpperTheory.isotypic_component_product_of_smooth_reps r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV U₀ hU₀ hfd0 h0
  have hex := fun i => UpperTheory.twisted_intertwiner_fixedVectors_of_irreducible (G i) H (S i) (τ i) (hsm i) (hirr i) (π i) (s i) (I i) (hI i)
    (hSK i) (U₀ i) (hU₀ i).1 (hU₀ i).2 (h1 i).2
  choose T₀ A₀ t₀ hP ht₀ ht₀0 using hex
  have a1 : ∀ i v, T₀ i v ∈ fixU (π i) (U₀ i) := fun i => (hP i).1
  have a2 : ∀ i, ∀ x, A₀ i x ∈ fixedVectors (τ i) (U₀ i) := fun i => (hP i).2.1
  have a3 : ∀ i, ∀ v ∈ Z, T₀ i v ∈ Z := fun i => (hP i).2.2.1 Z hZc (hZi i)
  have a4 : ∀ i j, i ≠ j → ∀ h v, T₀ i (π j h v) = π j h (T₀ i v) := fun i j hij =>
    (hP i).2.2.2.1 (G j) (π j) (hcm i j hij)
  have a5 : ∀ i f, Eqv (τ i) (π i) ⊤ f → ∀ x, T₀ i (f x) = f (A₀ i x) := fun i => (hP i).2.2.2.2
  have hprod : (∏ i, t₀ i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ht₀0 i
  obtain ⟨κ₀, hκ₀⟩ := UpperTheory.isotypic_intersection_product_eq r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI U₀ hU₀ h0
  refine ⟨κ₀, fun U T A t hU b1 b3 b4 b5 b2 bt => ?_⟩
  have hL : ∀ i, IsCompact ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) ∧ IsOpen ((U i ⊓ U₀ i : Subgroup (G i)) : Set (G i)) :=
    fun i => ⟨(hU i).1.inter (hU₀ i).1, (hU i).2.inter (hU₀ i).2⟩
  have hle0 := hmono (fun i => U i ⊓ U₀ i) U₀ fun i => inf_le_right
  have hleU := hmono (fun i => U i ⊓ U₀ i) U fun i => inf_le_left
  have hneL : (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) ≠ ⊥ := fun e => h0 (le_bot_iff.1 (e ▸ hle0))
  haveI hfdL : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i)) := hadm _ hL
  haveI hfdU : FiniteDimensional ℂ ↥(Z ⊓ ⨅ i, fixU (π i) (U i)) := hadm U hU
  obtain ⟨κ, hκ⟩ := UpperTheory.isotypic_intersection_product_eq r G H S π τ V Z hsm hirr hcm hZc hZV hZi hV hadm s I R hRZ hRs hI
    (fun i => U i ⊓ U₀ i) hL hneL
  have e1 := hκ T₀ A₀ t₀ (fun i v => hmF i _ _ inf_le_right _ (a1 i v)) a3 a4 a5
    (fun i x => hmS i _ _ inf_le_right (a2 i x)) ht₀
  have e2 := hκ₀ T₀ A₀ t₀ a1 a3 a4 a5 a2 ht₀
  have e3 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U₀ i)) (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i))
    ((List.ofFn T₀).prod ∘L R)).2 hle0 fun v hv =>
      UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z U₀ T₀ a1 a3 a4 _ (hRZ v (Submodule.mem_inf.1 hv).1)
  have hκκ : κ = κ₀ := mul_right_cancel₀ hprod (by rw [← e1, ← e2, e3])
  have e4 := hκ T A t (fun i v => hmF i _ _ inf_le_left _ (b1 i v)) b3 b4 b5
    (fun i x => hmS i _ _ inf_le_left (b2 i x)) bt
  have e5 := (UpperTheory.trOn_restrict_and_eq_of_maps_into H (Z ⊓ ⨅ i, fixU (π i) (U i)) (Z ⊓ ⨅ i, fixU (π i) (U i ⊓ U₀ i))
    ((List.ofFn T).prod ∘L R)).2 hleU fun v hv =>
      UpperTheory.mem_fixedVectors_of_product_of_compactOpen r G H π Z U T b1 b3 b4 _ (hRZ v (Submodule.mem_inf.1 hv).1)
  rw [← e5, e4, hκκ]
