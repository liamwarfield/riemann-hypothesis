module

public import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyZeroEquivSections

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsAffineOpenBiInfOfLe
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.AbLaw

section

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
  {ν κ : Type}

theorem isAffineOpen_biInf_of_le (E : ν → Y.Opens)
    (hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V)) (u : Finset ν) {V : Y.Opens}
    (hV : IsAffineOpen V) (h : ⨅ i ∈ u, E i ≤ V) : IsAffineOpen (⨅ i ∈ u, E i) := by
  classical
  rw [← inf_eq_left.2 h]
  clear h
  induction u using Finset.induction_on with
  | empty => simpa using hV
  | insert a s _ ih =>
    rw [Finset.iInf_insert, inf_assoc]
    exact hE a _ ih

theorem acyclic_comap_secCube [LinearOrder ν] [LinearOrder κ] [Fintype κ] (hM : M.IsLB)
    (E : ν → Y.Opens) (hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V)) (e : κ ↪o ν)
    (hc : ⨆ k, E (e k) = ⊤) (s₀ : Finset ν) {V : Y.Opens} (hV : IsAffineOpen V)
    (h : ⨅ i ∈ s₀, E i ≤ V) (g : Finset κ → Finset ν) (hg : Monotone g)
    (hgs : ∀ t, g t = s₀ ∪ t.map e.toEmbedding) :
    (cubeComplex (Cube.comap g hg (secCube f M E))).Acyclic := by
  rw [Cube.comap_congr hg (Cube.monotone_union_map e s₀) hgs]
  exact acyclic_slice_secCube_of_isAffineOpen R Y f M ν κ E e s₀ hM (hc ▸ le_top) fun t =>
    isAffineOpen_biInf_of_le E hE _ hV
      ((iInf_le_iInf_of_subset E Finset.subset_union_left).trans h)


variable (M) in
def comapSecCubeIso (E : ν → Y.Opens) (D : κ → Y.Opens) (g : Finset κ → Finset ν) (hg : Monotone g)
    (h : ∀ t, ⨅ i ∈ g t, E i = ⨅ k ∈ t, D k) :
    Cube.comap g hg (secCube f M E) ≅ secCube f M D :=
  Cube.isoMk (fun t => LinearEquiv.ofBijective (SecOnR.restrict f M (h t).ge)
      (SecOnR.restrict_bijective f (h t).ge (h t).le))
    fun hst x => (SecOnR.restrict_restrict f (iInf_le_iInf_of_subset E (hg hst)) (h _).ge x).trans
      (SecOnR.restrict_restrict f (h _).ge (iInf_le_iInf_of_subset D hst) x).symm

theorem biInf_sumVertex [LinearOrder ν] [LinearOrder κ] (E : ν ⊕ₗ κ → Y.Opens) (s : Finset ν)
    (t : Finset κ) : ⨅ i ∈ Cube.sumVertex s t, E i =
      (⨅ i ∈ s, E (toLex (Sum.inl i))) ⊓ ⨅ k ∈ t, E (toLex (Sum.inr k)) := by
  apply le_antisymm
  · exact le_inf (le_iInf₂ fun i hi => iInf₂_le _ (Cube.inl_mem_sumVertex.2 hi))
      (le_iInf₂ fun i hi => iInf₂_le _ (Cube.inr_mem_sumVertex.2 hi))
  · refine le_iInf₂ fun i hi => ?_
    obtain ⟨i | i, rfl⟩ := toLex.surjective i
    · exact inf_le_left.trans (iInf₂_le _ (Cube.inl_mem_sumVertex.1 hi))
    · exact inf_le_right.trans (iInf₂_le _ (Cube.inr_mem_sumVertex.1 hi))

end

theorem cechLB_homology_equiv_trunc₂ :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (κ₁ : Type) [LinearOrder κ₁] [Fintype κ₁] (U : κ₁ → Y.Opens) (κ₂ : Type) [LinearOrder κ₂] [Fintype κ₂] (W : κ₂ → Y.Opens), M.IsLB → IsSeparated f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → ⨆ i, U i = ⊤ → ⨆ j, W j = ⊤ → (∀ i V, IsAffineOpen V → IsAffineOpen (U i ⊓ V)) → (∀ j V, IsAffineOpen V → IsAffineOpen (W j ⊓ V)) → (∀ i j, IsAffineOpen (U i ⊓ W j)) → ∀ n, Nonempty ((cechLB f M D).homology n ≃ₗ[R] (cubeComplex (Cube.trunc₂ (secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u)))).homology (n + 2)) := by
  intro R _ Y f M κ _ _ D κ₁ _ _ U κ₂ _ _ W hM hf hD cD cU cW hU hW hUW n
  have hY : Y.IsSeparated := ⟨by rw [← terminal.comp_from f]; infer_instance⟩
  let E : (κ₁ ⊕ₗ κ₂) ⊕ₗ κ → Y.Opens := fun u =>
    Sum.elim (fun v : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex v)) D (ofLex u)
  have hE : ∀ i V, IsAffineOpen V → IsAffineOpen (E i ⊓ V) := by
    rintro ((i | j) | k) V hV
    · exact hU i V hV
    · exact hW j V hV
    · exact (hD k).inf hV
  let A := secCube f M E
  let e₁ := trunc₃HomologyIsoDropLast A (fun s t ⟨i, hi⟩ ⟨j, hj⟩ =>
    acyclic_comap_secCube f hM E hE (Cube.inrEmb _ _) cD
      ((Cube.sumVertex s t).map (Cube.inlEmb _ _).toEmbedding) (hUW i j)
      (le_inf
        (iInf₂_le (toLex (Sum.inl (toLex (Sum.inl i))))
          (Finset.mem_map_of_mem _ (Cube.inl_mem_sumVertex.2 hi)))
        (iInf₂_le (toLex (Sum.inl (toLex (Sum.inr j))))
          (Finset.mem_map_of_mem _ (Cube.inr_mem_sumVertex.2 hj))))
      _ (fun _ _ h => Cube.sumVertex_mono (subset_refl _) h) fun _ => rfl) (n + 2)
  let e₂ := trunc₃HomologyIsoDropFirst A (fun t w _ ⟨k, hk⟩ =>
    acyclic_comap_secCube f hM E hE (Cube.firstEmb _ _ _) cU
      ((Cube.sumVertex t w).map (Cube.lastTwoEmb _ _ _).toEmbedding) (hD k)
      (iInf₂_le (toLex (Sum.inr k)) (Finset.mem_map_of_mem _ (Cube.inr_mem_sumVertex.2 hk)))
      (fun s => Cube.sumVertex (Cube.sumVertex s t) w)
      (fun _ _ h => Cube.sumVertex_mono (Cube.sumVertex_mono h (subset_refl _)) (subset_refl _))
      fun s => (Cube.map_lastTwoEmb_union _ _ _ s t w).symm) (n + 2)
  let e₃ := trunc₂HomologyIsoSnd (Cube.lowerFace (Cube.lastTwoEmb κ₁ κ₂ κ) A) (fun w ⟨k, hk⟩ =>
    acyclic_comap_secCube f hM E hE ((Cube.inlEmb κ₂ κ).trans (Cube.lastTwoEmb κ₁ κ₂ κ)) cW
      (w.map (Cube.inrEmb _ _).toEmbedding) (hD k)
      (iInf₂_le (toLex (Sum.inr k)) (Finset.mem_map_of_mem _ hk))
      (fun t => (Cube.sumVertex t w).map (Cube.lastTwoEmb κ₁ κ₂ κ).toEmbedding)
      (fun _ _ h => Finset.map_subset_map.2 (Cube.sumVertex_mono h (subset_refl _)))
      fun t => by
        rw [Cube.sumVertex, Finset.map_union, Finset.map_map, Finset.map_map, Finset.union_comm]
        rfl) n
  let e₄ : Cube.sliceFst A ∅ ≅ secCube f M fun u : κ₁ ⊕ₗ κ₂ => Sum.elim U W (ofLex u) :=
    comapSecCubeIso f M E _ _ (fun _ _ h => Cube.sumVertex_mono h (subset_refl _)) fun t => by
      rw [biInf_sumVertex]
      simp [E]
  let e₅ : Cube.sliceSnd A (Cube.sumVertex ∅ ∅) ≅ secCube f M D :=
    comapSecCubeIso f M E _ _ (fun _ _ h => Cube.sumVertex_mono (subset_refl _) h) fun t => by
      rw [biInf_sumVertex]
      simp [E, Cube.sumVertex]
  exact ⟨((cechHomologyMapIso
    (eqToIso (Cube.sliceSnd_lowerFace_lastTwoEmb A ∅) ≪≫ e₅) n).symm ≪≫ e₃.symm ≪≫ e₂.symm ≪≫ e₁ ≪≫
      cubeHomologyMapIso (Cube.trunc₂Iso e₄.hom fun _ _ _ _ =>
        ConcreteCategory.bijective_of_isIso (e₄.hom.app _)) (n + 2)).toLinearEquiv⟩

end GlobalTheory.AbLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCovers
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw

noncomputable section

namespace GlobalTheory.AbLaw

variable {R : Type} [CommRing R] {Y : Scheme.{0}} (f : Y ⟶ Spec (CommRingCat.of R)) {M : LB Y}
  {ν κ : Type} [LinearOrder ν] [LinearOrder κ]

def sliceEmptySecCubeIso (M : LB Y) (E : ν → Y.Opens) (e : κ ↪o ν) {s₀ : Finset ν} (h₀ : s₀ = ∅) :
    Cube.slice e s₀ (secCube f M E) ≅ secCube f M fun k => E (e k) :=
  have h (t : Finset κ) : ⨅ i ∈ s₀ ∪ t.map e.toEmbedding, E i = ⨅ k ∈ t, E (e k) := by
    subst h₀
    rw [Finset.empty_union]
    refine le_antisymm (le_iInf₂ fun k hk => biInf_le _ (Finset.mem_map_of_mem _ hk))
      (le_iInf₂ fun i hi => ?_)
    obtain ⟨k, hk, rfl⟩ := Finset.mem_map.1 hi
    exact biInf_le (fun k => E (e k)) hk
  Cube.isoMk (fun t => LinearEquiv.ofBijective (SecOnR.restrict f M (h t).ge)
      (SecOnR.restrict_bijective f (h t).ge (h t).le))
    fun {s t} _ x => (SecOnR.restrict_restrict f _ (h t).ge x).trans
      (SecOnR.restrict_restrict f (h s).ge _ x).symm

theorem acyclic_slice_secCube_of_isSeparated [Fintype κ] (hM : M.IsLB) [IsSeparated f]
    (E : ν → Y.Opens) (hE : ∀ i, IsAffineOpen (E i)) (e : κ ↪o ν) (hc : ⨆ k, E (e k) = ⊤)
    {s₀ : Finset ν} (h₀ : s₀.Nonempty) :
    (cubeComplex (Cube.slice e s₀ (secCube f M E))).Acyclic := by
  have : IsSeparated (terminal.from Y) := by
    rw [← terminal.comp_from f]
    infer_instance
  refine acyclic_slice_secCube_of_isAffineOpen R Y f M ν κ E e s₀ hM (hc ▸ le_top) fun t => ?_
  exact IsAffineOpen.biInf _ (Finset.finite_toSet _)
    (h₀.mono Finset.subset_union_left) fun i _ => hE i

theorem cechLB_homology_equiv_of_affine_covers :
    ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (κ' : Type) [LinearOrder κ'] [Fintype κ'] (D' : κ' → Y.Opens), M.IsLB → IsSeparated f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, IsAffineOpen (D' i)) → ⨆ i, D' i = ⊤ → ∀ n, Nonempty ((cechLB f M D).homology n ≃ₗ[R] (cechLB f M D').homology n) := by
  intro R _ Y f M κ _ _ D κ' _ _ D' hM hf hD hc hD' hc' n
  let E : κ ⊕ₗ κ' → Y.Opens := fun u => Sum.elim D D' (ofLex u)
  have hE (u : κ ⊕ₗ κ') : IsAffineOpen (E u) := by
    rcases u with i | i
    exacts [hD i, hD' i]
  let e₁ := trunc₂HomologyIsoFst (secCube f M E) (fun s hs =>
    acyclic_slice_secCube_of_isSeparated f hM E hE (Cube.inrEmb κ κ') hc' hs.map) n
  let e₂ := trunc₂HomologyIsoSnd (secCube f M E) (fun t ht => by
    rw [Cube.sliceFst_eq_slice]
    exact acyclic_slice_secCube_of_isSeparated f hM E hE (Cube.inlEmb κ κ') hc ht.map) n
  let i₁ : Cube.sliceFst (secCube f M E) ∅ ≅ secCube f M D :=
    eqToIso (Cube.sliceFst_eq_slice _ _) ≪≫
      sliceEmptySecCubeIso f M E (Cube.inlEmb κ κ') (Finset.map_empty _)
  let i₂ : Cube.sliceSnd (secCube f M E) ∅ ≅ secCube f M D' :=
    sliceEmptySecCubeIso f M E (Cube.inrEmb κ κ') (Finset.map_empty _)
  exact ⟨((HomologicalComplex.homologyMapIso ((cechFunctor κ R).mapIso i₁) n).symm ≪≫ e₁.symm ≪≫
    e₂ ≪≫ HomologicalComplex.homologyMapIso ((cechFunctor κ' R).mapIso i₂) n).toLinearEquiv⟩

end GlobalTheory.AbLaw
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechLBHomologyEquivOfAffineCoversStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry DirectSum TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.AbLaw
theorem _root_.GlobalTheory.T.nonempty_cechLB_homology_equiv_of_affine_covers : ∀ (R : Type) [CommRing R] (Y : Scheme.{0}) (f : Y ⟶ Spec (CommRingCat.of R)) (M : LB Y) (κ : Type) [LinearOrder κ] [Fintype κ] (D : κ → Y.Opens) (κ' : Type) [LinearOrder κ'] [Fintype κ'] (D' : κ' → Y.Opens), M.IsLB → IsSeparated f → (∀ i, IsAffineOpen (D i)) → ⨆ i, D i = ⊤ → (∀ i, IsAffineOpen (D' i)) → ⨆ i, D' i = ⊤ → ∀ n, Nonempty ((cechLB f M D).homology n ≃ₗ[R] (cechLB f M D').homology n) := by
  first | exact @GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers | exact GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers | (intros; apply GlobalTheory.AbLaw.cechLB_homology_equiv_of_affine_covers <;> assumption)
end
end
