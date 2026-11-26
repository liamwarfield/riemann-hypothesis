module

public import GroundTheory.AutomorphicForms.TensorProductTheorem.Smooth
public import GroundTheory.AutomorphicForms.TensorProductTheorem.Window

@[expose] public section

section -- merged from GroundTheory.AutomorphicForms.TensorProductTheorem.Irreducible
noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open PiTensorProduct Filter Function Module Set Topology

open scoped TensorProduct RestrictedProduct

variable {ι : Type*} {V : ι → Type*} [∀ v, AddCommGroup (V v)] [∀ v, Module ℂ (V v)]

theorem tprod_ne_zero {ξ x : ∀ v, V v} (hx : IsRestricted ξ x) (h0 : ∀ v, x v ≠ 0) :
    tprod ℂ x ≠ 0 := by
  have hex : ∀ v, ∃ f : Dual ℂ (V v), f (x v) = 1 := by
    intro v
    obtain ⟨f, hf⟩ : ∃ f : Dual ℂ (V v), f (x v) ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact h0 v ((Module.forall_dual_apply_eq_zero_iff ℂ (x v)).1 hcon)
    exact ⟨(f (x v))⁻¹ • f, by simp [hf]⟩
  choose l hl using hex
  have hl' : ∀ᶠ v in cofinite, l v (ξ v) = 1 :=
    (show ∀ᶠ v in cofinite, x v = ξ v from hx).mono fun v h => by rw [← h, hl v]
  intro h
  have := evalForm_tprod (l := l) (hl := hl') hx
  rw [h, map_zero] at this
  simp [hl] at this


omit [∀ v, Module ℂ (V v)] in
theorem nontrivial_of_isIrreducible {H : Type*} [Group H] {W : Type*} [AddCommGroup W]
    [Module ℂ W] {σ : Representation ℂ H W} (h : σ.IsIrreducible) : Nontrivial W := by
  by_contra hW
  rw [not_nontrivial_iff_subsingleton] at hW
  obtain ⟨a, b, hab⟩ := h.toNontrivial.exists_pair_ne
  apply hab
  ext x
  rw [Subsingleton.elim x 0]
  exact ⟨fun _ => b.toSubmodule.zero_mem, fun _ => a.toSubmodule.zero_mem⟩

variable {G : ι → Type*} [∀ v, Group (G v)] [∀ v, TopologicalSpace (G v)]
  [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)]
  {K : ∀ v, Subgroup (G v)} [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))]
  [hKc : ∀ v, CompactSpace (K v)]
  {π : ∀ v, Representation ℂ (G v) (V v)} {ξ : ∀ v, V v}

omit [∀ v, Module ℂ (V v)] in
theorem map_update_id_mul {κ : Type*} [DecidableEq κ] {M : κ → Type*} [∀ j, AddCommGroup (M j)]
    [∀ j, Module ℂ (M j)] (i : κ) (a b : End ℂ (M i)) :
    PiTensorProduct.map (R := ℂ) (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i (a * b)) =
      PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i a) *
        PiTensorProduct.map (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i b) := by
  rw [← PiTensorProduct.map_mul]
  congr 1
  funext j
  by_cases hj : j = i
  · subst hj
    simp only [Function.update_self]
  · simp only [Function.update_of_ne hj]
    rfl

omit [∀ v, Module ℂ (V v)] in
theorem map_update_id_one {κ : Type*} [DecidableEq κ] {M : κ → Type*} [∀ j, AddCommGroup (M j)]
    [∀ j, Module ℂ (M j)] (i : κ) :
    PiTensorProduct.map (R := ℂ) (Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i 1) =
      LinearMap.id := by
  have : Function.update (fun j => (LinearMap.id : M j →ₗ[ℂ] M j)) i 1 =
      fun j => (LinearMap.id : M j →ₗ[ℂ] M j) := by
    funext j
    by_cases hj : j = i
    · subst hj
      rw [Function.update_self]
      rfl
    · rw [Function.update_of_ne hj]
  rw [this, PiTensorProduct.map_id]

section Window

variable (hπ : ∀ v, IsSmooth (π v)) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
  {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
  [DecidableEq ι] (S : Finset ι) (hSK : ∀ v ∉ S, K' v = K v)
  (hSξ : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (K v))

include hSK hSξ in
omit [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)] hKo hKc in
theorem windowEmbed_mem (t : ⨂[ℂ] v : S, fixedVectors (π v) (K' v)) :
    ∃ h : windowEmbed ξ S t ∈ restrictedTensor ξ,
      (⟨windowEmbed ξ S t, h⟩ : restrictedTensor ξ) ∈
        fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c w =>
    have hmem : windowEmbed ξ S (c • tprod ℂ w) ∈ restrictedTensor ξ := by
      rw [map_smul, windowEmbed_tprod]
      exact Submodule.smul_mem _ _ (tprod_mem_restrictedTensor (isRestricted_extend ξ S _))
    refine ⟨hmem, fun g hg => Subtype.ext ?_⟩
    show tensorRep (K := K) π g (windowEmbed ξ S (c • tprod ℂ w)) =
      windowEmbed ξ S (c • tprod ℂ w)
    rw [map_smul, map_smul, windowEmbed_tprod, tensorRep_tprod]
    congr 2
    funext v
    unfold extend
    split_ifs with hv
    · exact (w ⟨v, hv⟩).2 _ (hg v)
    · exact hSξ v hv _ (hSK v hv ▸ hg v)
  | add a b ha hb =>
    obtain ⟨ha1, ha2⟩ := ha
    obtain ⟨hb1, hb2⟩ := hb
    refine ⟨by rw [map_add (f := _)]; exact Submodule.add_mem _ ha1 hb1, ?_⟩
    have := Submodule.add_mem _ ha2 hb2
    convert this using 1
    exact Subtype.ext (map_add _ _ _)

def windowEmbedFixed : (⨂[ℂ] v : S, fixedVectors (π v) (K' v)) →ₗ[ℂ]
    fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') :=
  LinearMap.codRestrict _ (LinearMap.codRestrict (restrictedTensor ξ) (windowEmbed ξ S)
    fun t => (windowEmbed_mem hξ S hSK hSξ t).1) fun t => (windowEmbed_mem hξ S hSK hSξ t).2

omit [∀ v, IsTopologicalGroup (G v)] [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)]
  [∀ v, TotallyDisconnectedSpace (G v)] hKo hKc in
theorem coe_windowEmbedFixed (t : ⨂[ℂ] v : S, fixedVectors (π v) (K' v)) :
    ((windowEmbedFixed hξ S hSK hSξ t : restrictedTensor ξ) : ⨂[ℂ] v, V v) =
      windowEmbed ξ S t :=
  rfl


include hπ hK'c hK'o hK'e in
theorem lift_adjoin_heckeOps (v : S) {a : End ℂ (fixedVectors (π v) (K' v))}
    (ha : a ∈ Algebra.adjoin ℂ (heckeOps (hπ v) (hK'c v) (hK'o v))) :
    ∃ A ∈ Algebra.adjoin ℂ (heckeOps (isSmooth_restrictedTensorRep hπ hξ)
        (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)),
      ∀ t, A (windowEmbedFixed hξ S hSK hSξ t) =
        windowEmbedFixed hξ S hSK hSξ
          (PiTensorProduct.map (Function.update (fun _ => LinearMap.id) v a) t) := by
  induction ha using Algebra.adjoin_induction with
  | mem a ha =>
    obtain ⟨g, rfl⟩ := ha
    refine ⟨heckeOp _ _ _ (RestrictedProduct.mulSingle K v g),
      Algebra.subset_adjoin (heckeOp_mem_heckeOps _ _ _ _), fun t => ?_⟩
    induction t using PiTensorProduct.induction_on with
    | smul_tprod c w =>
      rw [map_smul, map_smul, map_smul, map_smul]
      congr 1
      refine Subtype.ext (Subtype.ext ?_)
      rw [heckeOp_apply]
      have hx : IsRestricted ξ (extend ξ S fun u => (w u : V u)) := isRestricted_extend ξ S _
      have hx' : IsRestricted ξ (Function.update (extend ξ S fun u => (w u : V u)) v
          (π v g (w v))) := hx.update _ _
      have hρ : restrictedTensorRep π ξ hξ (RestrictedProduct.mulSingle K v g)
          (windowEmbedFixed hξ S hSK hSξ (tprod ℂ w) : restrictedTensor ξ) =
          ⟨tprod ℂ _, tprod_mem_restrictedTensor hx'⟩ := by
        refine Subtype.ext ?_
        rw [coe_restrictedTensorRep_apply, coe_windowEmbedFixed, windowEmbed_tprod,
          tensorRep_mulSingle_tprod]
        congr 2
        simp [extend]
      rw [hρ, coe_fixedProj_tprod hπ hξ hK'c hK'o hK'e hx', coe_windowEmbedFixed,
        PiTensorProduct.map_tprod, windowEmbed_tprod]
      congr 1
      funext u
      by_cases huv : u = v
      · subst huv
        simp [extend, heckeOp_apply]
      · rw [Function.update_of_ne huv]
        unfold extend
        split_ifs with hu
        · have hne : (⟨u, hu⟩ : S) ≠ v := fun h => huv (congrArg Subtype.val h)
          dsimp only
          rw [Function.update_of_ne hne]
          exact fixedProj_apply_of_mem (hπ u) (hK'c u) (hK'o u) (w ⟨u, hu⟩).2
        · exact fixedProj_apply_of_mem (hπ u) (hK'c u) (hK'o u) (hSK u hu ▸ hSξ u hu)
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
  | algebraMap c =>
    refine ⟨algebraMap ℂ _ c, Subalgebra.algebraMap_mem _ c, fun t => ?_⟩
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
      PiTensorProduct.map_update_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul,
      map_update_id_one]
    rfl
  | add a b _ _ ha hb =>
    obtain ⟨A, hA, hAt⟩ := ha
    obtain ⟨B, hB, hBt⟩ := hb
    refine ⟨A + B, Subalgebra.add_mem _ hA hB, fun t => ?_⟩
    rw [PiTensorProduct.map_update_add, LinearMap.add_apply, LinearMap.add_apply, hAt, hBt,
      map_add]
  | mul a b _ _ ha hb =>
    obtain ⟨A, hA, hAt⟩ := ha
    obtain ⟨B, hB, hBt⟩ := hb
    refine ⟨A * B, Subalgebra.mul_mem _ hA hB, fun t => ?_⟩
    rw [Module.End.mul_apply, hBt, hAt, map_update_id_mul, Module.End.mul_apply]

end Window

theorem isSimpleUnder_heckeOps_box (hπ : ∀ v, IsAdmissible (π v))
    (hirr : ∀ v, (π v).IsIrreducible) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
    (hgel : ∀ᶠ v in cofinite, ∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v)
    {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
    (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)
    (hne : fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') ≠ ⊥) :
    IsSimpleUnder (heckeOps (isSmooth_restrictedTensorRep (fun v => (hπ v).1) hξ)
      (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)) := by
  classical
  have hπs : ∀ v, IsSmooth (π v) := fun v => (hπ v).1
  set S : Finset ι := ((Filter.eventually_cofinite.1 ((hK'e.and hgel).and hξ))).toFinset
  have hS : ∀ v ∉ S, K' v = K v ∧ (∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v) ∧
      ξ v ∈ fixedVectors (π v) (K v) := fun v hv => by simpa [S] using hv
  have hSK : ∀ v ∉ S, K' v = K v := fun v hv => (hS v hv).1
  have hSξ : ∀ v ∉ S, ξ v ∈ fixedVectors (π v) (K v) := fun v hv => (hS v hv).2.2
  have hle := le_range_windowEmbed hπ hξ hK'c hK'o hK'e S hSK (fun v hv => (hS v hv).2.1) hSξ
  set J := windowEmbedFixed (π := π) (K' := K') hξ S hSK hSξ
  have hJ : Function.Surjective J := by
    intro t
    obtain ⟨s, hs⟩ := hle ⟨t, t.2, rfl⟩
    exact ⟨s, Subtype.ext (Subtype.ext hs)⟩
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hne, fun p hp => ?_⟩
  by_cases hp0 : p = ⊥
  · exact Or.inl hp0
  right
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  obtain ⟨s, rfl⟩ := hJ z
  have hs0 : s ≠ 0 := by rintro rfl; exact hz0 (map_zero _)

  have hMnt : ∀ v : S, Nontrivial (fixedVectors (π v) (K' v)) := by
    intro v
    by_contra hv
    rw [not_nontrivial_iff_subsingleton] at hv
    apply hs0
    have : ∀ t : ⨂[ℂ] u : S, fixedVectors (π u) (K' u), t = 0 := by
      intro t
      induction t using PiTensorProduct.induction_on with
      | smul_tprod c w =>
        rw [(PiTensorProduct.tprod ℂ).map_coord_zero v (Subsingleton.elim _ _), smul_zero]
      | add a b ha hb => rw [ha, hb, add_zero]
    exact this s
  have hfd : ∀ v : S, FiniteDimensional ℂ (fixedVectors (π v) (K' v)) :=
    fun v => (hπ v).2 _ (hK'c v) (hK'o v)

  let b : ∀ v : S, Basis (Basis.ofVectorSpaceIndex ℂ (fixedVectors (π v) (K' v))) ℂ
      (fixedVectors (π v) (K' v)) := fun v => Basis.ofVectorSpace ℂ _
  let B := Basis.piTensorProduct b
  obtain ⟨k, hk⟩ : ∃ k, B.repr s k ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hs0 (B.repr.injective (Finsupp.ext fun k => by simp [hcon k]))
  have hadj : ∀ v : S, Algebra.adjoin ℂ (heckeOps (hπs v) (hK'c v) (hK'o v)) = ⊤ := fun v =>
    have : (π v).IsIrreducible := hirr v
    adjoin_eq_top (isSimpleUnder_heckeOps (hπs v) (hK'c v) (hK'o v)
      (Submodule.nontrivial_iff_ne_bot.1 (hMnt v)))
  have hpadj := IsStable.adjoin hp

  have htarget : ∀ w : ∀ v : S, fixedVectors (π v) (K' v), J (tprod ℂ w) ∈ p := by
    intro w
    let r : ∀ v : S, End ℂ (fixedVectors (π v) (K' v)) := fun v => (b v).coord (k v) |>.smulRight (w v)
    have hstep : ∀ T : Finset S, J (PiTensorProduct.map (T.piecewise r fun _ => LinearMap.id) s) ∈ p := by
      intro T
      induction T using Finset.induction_on with
      | empty =>
        simp only [Finset.piecewise_empty, PiTensorProduct.map_id, LinearMap.id_apply]
        exact hz
      | insert v T hvT ih =>
        obtain ⟨A, hA, hAt⟩ := lift_adjoin_heckeOps hπs hξ hK'c hK'o hK'e S hSK hSξ v
          (a := r v) (by rw [hadj v]; trivial)
        have hmap : (PiTensorProduct.map ((insert v T).piecewise r fun _ => LinearMap.id)) =
            PiTensorProduct.map (Function.update (fun _ => LinearMap.id) v (r v)) *
              PiTensorProduct.map (T.piecewise r fun _ => LinearMap.id) := by
          rw [← PiTensorProduct.map_mul]
          congr 1
          funext u
          by_cases hu : u = v
          · subst hu
            rw [Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_insert_self _ _),
              Function.update_self, Finset.piecewise_eq_of_notMem _ _ _ hvT]
            rfl
          · rw [Function.update_of_ne hu]
            by_cases huT : u ∈ T
            · rw [Finset.piecewise_eq_of_mem _ _ _ (Finset.mem_insert_of_mem huT),
                Finset.piecewise_eq_of_mem _ _ _ huT]
              rfl
            · rw [Finset.piecewise_eq_of_notMem _ _ _ (by simp [hu, huT]),
                Finset.piecewise_eq_of_notMem _ _ _ huT]
              rfl
        rw [hmap, Module.End.mul_apply, ← hAt]
        exact hpadj A hA _ ih
    have hall := hstep Finset.univ
    rw [Finset.piecewise_univ] at hall
    have hrs : PiTensorProduct.map r s = B.repr s k • tprod ℂ w := by
      have key : PiTensorProduct.map r = (B.coord k).smulRight (tprod ℂ w) := by
        refine B.ext fun k' => ?_
        rw [Basis.piTensorProduct_apply, PiTensorProduct.map_tprod, LinearMap.smulRight_apply,
          Basis.coord_apply, ← Basis.piTensorProduct_apply, Basis.repr_self]
        simp only [r, LinearMap.smulRight_apply, Basis.coord_apply, Basis.repr_self]
        rw [MultilinearMap.map_smul_univ, Finsupp.single_apply]
        by_cases hkk : k' = k
        · subst hkk; simp
        · rw [if_neg hkk]
          obtain ⟨v, hv⟩ : ∃ v, k' v ≠ k v := by
            by_contra hcon
            push Not at hcon
            exact hkk (funext hcon)
          rw [Finset.prod_eq_zero (Finset.mem_univ v) (by simp [Finsupp.single_apply, hv]),
            zero_smul]
      rw [key, LinearMap.smulRight_apply, Basis.coord_apply]
    rw [hrs, map_smul] at hall
    have := p.smul_mem (B.repr s k)⁻¹ hall
    rwa [smul_smul, inv_mul_cancel₀ hk, one_smul] at this
  rw [eq_top_iff]
  rintro t -
  obtain ⟨u, rfl⟩ := hJ t
  have hspan : u ∈ Submodule.span ℂ (range (tprod ℂ : (∀ v : S, fixedVectors (π v) (K' v)) →
      ⨂[ℂ] v : S, fixedVectors (π v) (K' v))) := by
    rw [PiTensorProduct.span_tprod_eq_top]; trivial
  induction hspan using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨w, rfl⟩ := hu
    exact htarget w
  | zero => rw [map_zero]; exact p.zero_mem
  | add a b _ _ ha hb => rw [map_add (f := _)]; exact p.add_mem ha hb
  | smul c a _ ha => rw [map_smul]; exact p.smul_mem c ha

theorem isIrreducible_restrictedTensorRep (hπ : ∀ v, IsAdmissible (π v))
    (hirr : ∀ v, (π v).IsIrreducible) (hξ : ∀ᶠ v in cofinite, ξ v ∈ fixedVectors (π v) (K v))
    (hξ0 : ∀ᶠ v in cofinite, ξ v ≠ 0)
    (hgel : ∀ᶠ v in cofinite, ∀ u ∈ fixedVectors (π v) (K v), ∃ c : ℂ, u = c • ξ v) :
    (restrictedTensorRep π ξ hξ).IsIrreducible := by
  classical
  have hπs : ∀ v, IsSmooth (π v) := fun v => (hπ v).1
  have hnt : Nontrivial (restrictedTensor ξ) := by
    have hv : ∀ v, ∃ u : V v, u ≠ 0 := fun v =>
      have := nontrivial_of_isIrreducible (hirr v)
      exists_ne 0
    choose u hu using hv
    set x : ∀ v, V v := fun v => if ξ v ≠ 0 then ξ v else u v
    have hx : IsRestricted ξ x := hξ0.mono fun v h => by simp [x, h]
    have hx0 : ∀ v, x v ≠ 0 := fun v => by
      by_cases h : ξ v = 0
      · simp [x, h, hu v]
      · simp [x, h]
    refine ⟨⟨⟨tprod ℂ x, tprod_mem_restrictedTensor hx⟩, 0, fun h => ?_⟩⟩
    exact tprod_ne_zero hx hx0 (congrArg Subtype.val h)
  refine isIrreducible_of_forall (isSmooth_restrictedTensorRep hπs hξ) fun x y hx0 => ?_
  obtain ⟨A, hAc, hAo, hAK, hAe, hAfix⟩ := exists_boxSubgroup_fixing hπs hξ x.2
  obtain ⟨B, hBc, hBo, hBK, hBe, hBfix⟩ := exists_boxSubgroup_fixing hπs hξ y.2
  set K' : ∀ v, Subgroup (G v) := fun v => A v ⊓ B v
  have hK'c : ∀ v, IsCompact (K' v : Set (G v)) :=
    fun v => (hAc v).inter_right (Subgroup.isClosed_of_isOpen _ (hBo v))
  have hK'o : ∀ v, IsOpen (K' v : Set (G v)) := fun v => (hAo v).inter (hBo v)
  have hK'e : ∀ᶠ v in cofinite, K' v = K v := by
    filter_upwards [hAe, hBe] with v h1 h2
    simp [K', h1, h2]
  have hxK : x ∈ fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') :=
    fun g hg => Subtype.ext (hAfix g fun v => (hg v).1)
  have hyK : y ∈ fixedVectors (restrictedTensorRep π ξ hξ) (boxSubgroup K K') :=
    fun g hg => Subtype.ext (hBfix g fun v => (hg v).2)
  refine ⟨boxSubgroup K K', isCompact_boxSubgroup_of_eq hK'c hK'e, isOpen_boxSubgroup hK'o hK'e,
    hxK, hyK, isSimpleUnder_heckeOps_box hπ hirr hξ hgel hK'c hK'o hK'e ?_⟩
  intro h
  have : x ∈ (⊥ : Submodule ℂ (restrictedTensor ξ)) := h ▸ hxK
  exact hx0 ((Submodule.mem_bot ℂ).1 this)

end RestrictedTensor

end GroundTheory.Automorphic
end
end

section -- merged from GroundTheory.AutomorphicForms.TensorProductTheorem.LocalComponent
noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Module Set

variable {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
  [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {σ : Representation ℂ L V}

section General


variable (σ) in
def genSubrep (N : Submodule ℂ V) : Subrepresentation σ where
  toSubmodule := ⨆ g : L, N.map (σ g)
  apply_mem_toSubmodule g x hx := by
    have : (⨆ h : L, N.map (σ h)) ≤ (⨆ h : L, N.map (σ h)).comap (σ g) := by
      refine iSup_le fun h => ?_
      rintro _ ⟨n, hn, rfl⟩
      rw [Submodule.mem_comap, ← Module.End.mul_apply, ← map_mul]
      exact Submodule.mem_iSup_of_mem (g * h) ⟨n, hn, rfl⟩
    exact this hx

theorem mem_genSubrep_of_mem {N : Submodule ℂ V} {n : V} (hn : n ∈ N) (g : L) :
    σ g n ∈ (genSubrep σ N).toSubmodule :=
  Submodule.mem_iSup_of_mem g ⟨n, hn, rfl⟩

theorem le_genSubrep (N : Submodule ℂ V) : N ≤ (genSubrep σ N).toSubmodule := fun n hn => by
  simpa using mem_genSubrep_of_mem (σ := σ) hn 1

theorem genSubrep_le {N : Submodule ℂ V} {X : Subrepresentation σ} (h : N ≤ X.toSubmodule) :
    (genSubrep σ N).toSubmodule ≤ X.toSubmodule :=
  iSup_le fun g => by
    rintro _ ⟨n, hn, rfl⟩
    exact X.apply_mem_toSubmodule g (h hn)

end General

variable (hσ : IsSmooth σ) {K : Subgroup L} (hKc : IsCompact (K : Set L))
  (hKo : IsOpen (K : Set L)) (N : Submodule ℂ V)

def genKernel : Submodule ℂ (genSubrep σ N).toSubmodule where
  carrier := {u | ∀ g, fixedProj σ hσ hKc hKo (σ g u) = 0}
  add_mem' {a b} ha hb g := by
    simp only [mem_setOf_eq, Submodule.coe_add, map_add (f := _), ha g, hb g, add_zero]
  zero_mem' g := by simp
  smul_mem' c a ha g := by
    simp only [mem_setOf_eq, Submodule.coe_smul, map_smul, ha g, smul_zero]

theorem genKernel_le_comap (g : L) :
    genKernel hσ hKc hKo N ≤
      (genKernel hσ hKc hKo N).comap ((genSubrep σ N).toRepresentation g) := by
  intro u hu h
  show fixedProj σ hσ hKc hKo (σ h (σ g u)) = 0
  rw [← Module.End.mul_apply, ← map_mul]
  exact hu (h * g)

def genQuotRep : Representation ℂ L ((genSubrep σ N).toSubmodule ⧸ genKernel hσ hKc hKo N) :=
  (genSubrep σ N).toRepresentation.quotient _ (genKernel_le_comap hσ hKc hKo N)

def genQuotMk : N →ₗ[ℂ] (genSubrep σ N).toSubmodule ⧸ genKernel hσ hKc hKo N :=
  (genKernel hσ hKc hKo N).mkQ ∘ₗ Submodule.inclusion (le_genSubrep N)

theorem genQuotRep_mk (g : L) (u : (genSubrep σ N).toSubmodule) :
    genQuotRep hσ hKc hKo N g (Submodule.Quotient.mk u) =
      Submodule.Quotient.mk ((genSubrep σ N).toRepresentation g u) :=
  rfl

def genQuotMap : Representation.IntertwiningMap (genSubrep σ N).toRepresentation
    (genQuotRep hσ hKc hKo N) where
  toLinearMap := (genKernel hσ hKc hKo N).mkQ
  isIntertwining' g := LinearMap.ext fun _ => rfl

include hσ in
theorem isSmooth_genSubrep : IsSmooth (genSubrep σ N).toRepresentation := by
  intro u
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf σ (u : V)) (fun g hg => ?_) (hσ u)
  exact Subtype.ext hg

theorem isSmooth_genQuotRep : IsSmooth (genQuotRep hσ hKc hKo N) := by
  intro q
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  refine Subgroup.isOpen_mono (H₁ := stabilizerOf (genSubrep σ N).toRepresentation u)
    (fun g hg => ?_) (isSmooth_genSubrep hσ N u)
  show genQuotRep hσ hKc hKo N g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
  rw [genQuotRep_mk, hg]

variable {N}

section Simple

variable (hNK : N ≤ fixedVectors σ K)
  (hNst : ∀ g, ∀ n ∈ N, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N)


include hNK hNst in
theorem mem_of_mem_genSubrep_fixed {u : V} (hu : u ∈ (genSubrep σ N).toSubmodule)
    (huK : u ∈ fixedVectors σ K) : u ∈ N := by
  have h1 : (fixedProj σ hσ hKc hKo u : V) = u := fixedProj_apply_of_mem hσ hKc hKo huK
  rw [← h1]
  have : (genSubrep σ N).toSubmodule ≤ N.comap ((fixedVectors σ K).subtype ∘ₗ
      fixedProj σ hσ hKc hKo) := by
    refine iSup_le fun g => ?_
    rintro _ ⟨n, hn, rfl⟩
    exact hNst g n hn
  exact this hu

include hNK in
theorem genQuotMk_injective : Function.Injective (genQuotMk hσ hKc hKo N) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro n hn
  rw [LinearMap.mem_ker, genQuotMk, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero] at hn
  have := hn 1
  rw [map_one, Module.End.one_apply] at this
  have h2 : (fixedProj σ hσ hKc hKo (n : V) : V) = n := fixedProj_apply_of_mem hσ hKc hKo (hNK n.2)
  rw [Submodule.mem_bot]
  refine Subtype.ext ?_
  rw [← h2]
  simp only [Submodule.coe_inclusion] at this
  rw [this]
  rfl


include hNK in
theorem genQuotMk_mem_fixedVectors (n : N) :
    genQuotMk hσ hKc hKo N n ∈ fixedVectors (genQuotRep hσ hKc hKo N) K := by
  intro k hk
  show genQuotRep hσ hKc hKo N k (Submodule.Quotient.mk _) = Submodule.Quotient.mk _
  rw [genQuotRep_mk]
  congr 1
  exact Subtype.ext (hNK n.2 k hk)


include hNK hNst in
theorem isIrreducible_genQuotRep (hN0 : N ≠ ⊥)
    (hNmin : ∀ N₁ : Submodule ℂ V, N₁ ≤ N → N₁ ≠ ⊥ →
      (∀ g, ∀ n ∈ N₁, (fixedProj σ hσ hKc hKo (σ g n) : V) ∈ N₁) → N₁ = N) :
    (genQuotRep hσ hKc hKo N).IsIrreducible := by
  set U := genSubrep σ N
  set U₀ := genKernel hσ hKc hKo N
  set π := genQuotRep hσ hKc hKo N
  obtain ⟨n, hn, hn0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hN0
  have hmk0 : genQuotMk hσ hKc hKo N ⟨n, hn⟩ ≠ 0 := by
    intro h
    have := genQuotMk_injective hσ hKc hKo hNK (a₁ := ⟨n, hn⟩) (a₂ := 0) (by rw [h, map_zero])
    exact hn0 (congrArg Subtype.val this)
  have hbt : (⊥ : Subrepresentation π) ≠ ⊤ := by
    intro h0
    have : genQuotMk hσ hKc hKo N ⟨n, hn⟩ ∈ (⊤ : Subrepresentation π).toSubmodule :=
      Submodule.mem_top
    rw [← h0] at this
    exact hmk0 this
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun X => ?_ }

  let Y : Subrepresentation σ :=
    { toSubmodule := (X.toSubmodule.comap U₀.mkQ).map U.toSubmodule.subtype
      apply_mem_toSubmodule := by
        rintro g _ ⟨u, hu, rfl⟩
        refine ⟨U.toRepresentation g u, ?_, rfl⟩
        have hu' : U₀.mkQ u ∈ X.toSubmodule := hu
        have := X.apply_mem_toSubmodule g hu'
        exact this }
  have hYU : ∀ {x : V}, x ∈ Y.toSubmodule → x ∈ U.toSubmodule := by
    rintro _ ⟨u, _, rfl⟩
    exact u.2

  have hst : ∀ g, ∀ m ∈ Y.toSubmodule ⊓ N, (fixedProj σ hσ hKc hKo (σ g m) : V) ∈
      Y.toSubmodule ⊓ N := by
    rintro g m ⟨hmY, hmN⟩
    exact ⟨fixedProj_mem hσ hKc hKo Y (Y.apply_mem_toSubmodule g hmY), hNst g m hmN⟩
  by_cases hYN : Y.toSubmodule ⊓ N = ⊥
  ·
    left
    ext q
    refine ⟨fun hq => ?_, fun hq => ?_⟩
    · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
      show Submodule.Quotient.mk u = (0 : U.toSubmodule ⧸ U₀)
      rw [Submodule.Quotient.mk_eq_zero]
      intro g
      have hY : (U.toRepresentation g u : V) ∈ Y.toSubmodule :=
        ⟨U.toRepresentation g u, X.apply_mem_toSubmodule g hq, rfl⟩
      have h1 := fixedProj_mem hσ hKc hKo Y hY
      have h2 : (fixedProj σ hσ hKc hKo (σ g u) : V) ∈ N :=
        mem_of_mem_genSubrep_fixed hσ hKc hKo hNK hNst (hYU h1) (fixedProj σ hσ hKc hKo _).2
      have h3 : (fixedProj σ hσ hKc hKo (σ g u) : V) ∈ Y.toSubmodule ⊓ N := ⟨h1, h2⟩
      rw [hYN, Submodule.mem_bot] at h3
      exact Subtype.ext h3
    · have : q = 0 := hq
      rw [this]
      exact X.toSubmodule.zero_mem
  ·
    right
    have hle : Y.toSubmodule ⊓ N ≤ N := inf_le_right
    have heq := hNmin _ hle hYN hst
    have hNY : N ≤ Y.toSubmodule := heq ▸ inf_le_left
    have hUY := genSubrep_le hNY
    ext q
    refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ q
    obtain ⟨u', hu', hu'u⟩ := hUY u.2
    have : u' = u := Subtype.ext hu'u
    rw [← this]
    exact hu'

end Simple

theorem isAdmissible_genQuotRep
    (hfin : ∀ K' : Subgroup L, IsCompact (K' : Set L) → IsOpen (K' : Set L) →
      FiniteDimensional ℂ (fixedVectors (genSubrep σ N).toRepresentation K')) :
    IsAdmissible (genQuotRep hσ hKc hKo N) := by
  refine ⟨isSmooth_genQuotRep hσ hKc hKo N, fun K' hK'c hK'o => ?_⟩
  have := hfin K' hK'c hK'o
  have hsurj := fixedMap_surjective (isSmooth_genSubrep hσ N) (isSmooth_genQuotRep hσ hKc hKo N)
    hK'c hK'o (f := genQuotMap hσ hKc hKo N) (Submodule.mkQ_surjective _)
  exact Module.Finite.of_surjective _ hsurj

def genQuotForm (l : Dual ℂ (fixedVectors σ K)) :
    Dual ℂ ((genSubrep σ N).toSubmodule ⧸ genKernel hσ hKc hKo N) :=
  (genKernel hσ hKc hKo N).liftQ (l ∘ₗ fixedProj σ hσ hKc hKo ∘ₗ (genSubrep σ N).toSubmodule.subtype)
    fun u hu => by
      rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.comp_apply]
      have := hu 1
      rw [map_one, Module.End.one_apply] at this
      simp only [Submodule.subtype_apply, this, map_zero]

theorem genQuotForm_apply (l : Dual ℂ (fixedVectors σ K)) (hNK : N ≤ fixedVectors σ K) (g : L)
    (n : N) :
    genQuotForm hσ hKc hKo l (genQuotRep hσ hKc hKo N g (genQuotMk hσ hKc hKo N n)) =
      l (fixedProj σ hσ hKc hKo (σ g n)) :=
  rfl

end RestrictedTensor

end GroundTheory.Automorphic
end
end

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Filter Function Module Set

open scoped RestrictedProduct

variable {ι : Type*} {G : ι → Type*} [∀ v, Group (G v)] {K : ∀ v, Subgroup (G v)}

section Group

variable [DecidableEq ι]


variable (K) in
def singleHom (K : ∀ w, Subgroup (G w)) (v : ι) : G v →* Πʳ w, [G w, K w] where
  toFun := RestrictedProduct.mulSingle K v
  map_one' := RestrictedProduct.mulSingle_one K v
  map_mul' x y := RestrictedProduct.mulSingle_mul K v x y

theorem singleHom_apply_self (v : ι) (x : G v) : singleHom K v x v = x :=
  RestrictedProduct.mulSingle_eq_same K v x

theorem singleHom_apply_of_ne {v w : ι} (x : G v) (h : w ≠ v) : singleHom K v x w = 1 :=
  RestrictedProduct.mulSingle_eq_of_ne K x h

theorem commute_of_forall {a b : Πʳ w, [G w, K w]} (h : ∀ w, a w = 1 ∨ b w = 1) :
    a * b = b * a := by
  ext w
  simp only [RestrictedProduct.mul_apply]
  rcases h w with h | h <;> simp [h]

def eraseAt (v : ι) (g : Πʳ w, [G w, K w]) : Πʳ w, [G w, K w] :=
  (singleHom K v (g v))⁻¹ * g

theorem eraseAt_apply_self (v : ι) (g : Πʳ w, [G w, K w]) : eraseAt v g v = 1 := by
  simp [eraseAt, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply, singleHom_apply_self]

theorem eraseAt_apply_of_ne {v w : ι} (g : Πʳ w, [G w, K w]) (h : w ≠ v) :
    eraseAt v g w = g w := by
  simp [eraseAt, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
    singleHom_apply_of_ne _ h]

theorem single_mul_eraseAt (v : ι) (g : Πʳ w, [G w, K w]) :
    singleHom K v (g v) * eraseAt v g = g := by
  simp [eraseAt]

theorem eraseAt_mem_boxSubgroup {K' : ∀ v, Subgroup (G v)} (v : ι) {g : Πʳ w, [G w, K w]}
    (hg : g ∈ boxSubgroup K K') : eraseAt v g ∈ boxSubgroup K K' := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [eraseAt_apply_self]
    exact (K' w).one_mem
  · rw [eraseAt_apply_of_ne _ hw]
    exact hg w

theorem singleHom_mem_boxSubgroup {K' : ∀ v, Subgroup (G v)} {v : ι} {x : G v}
    (hx : x ∈ K' v) : singleHom K v x ∈ boxSubgroup K K' := by
  intro w
  by_cases hw : w = v
  · subst hw
    rw [singleHom_apply_self]
    exact hx
  · rw [singleHom_apply_of_ne _ hw]
    exact (K' w).one_mem

theorem commute_singleHom {v : ι} (x : G v) {b : Πʳ w, [G w, K w]} (hb : b v = 1) :
    singleHom K v x * b = b * singleHom K v x :=
  commute_of_forall fun w => by
    by_cases hw : w = v
    · subst hw; exact Or.inr hb
    · exact Or.inl (singleHom_apply_of_ne _ hw)

end Group

variable [∀ v, TopologicalSpace (G v)] [∀ v, IsTopologicalGroup (G v)]
  [∀ v, LocallyCompactSpace (G v)] [∀ v, T2Space (G v)] [∀ v, TotallyDisconnectedSpace (G v)]
  [hKo : Fact (∀ v, IsOpen (K v : Set (G v)))] [hKc : ∀ v, CompactSpace (K v)]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ (Πʳ v, [G v, K v]) V}
  (hρ : IsSmooth ρ) {K' : ∀ v, Subgroup (G v)} (hK'c : ∀ v, IsCompact (K' v : Set (G v)))
  (hK'o : ∀ v, IsOpen (K' v : Set (G v))) (hK'e : ∀ᶠ v in cofinite, K' v = K v)

section Window

variable [DecidableEq ι]


omit hK'c hK'o hK'e in
theorem apply_eq_apply_single (v : ι) {u : V}
    (hu : ∀ h ∈ boxSubgroup K K', h v = 1 → ρ h u = u) {h : Πʳ w, [G w, K w]}
    (hh : h ∈ boxSubgroup K K') : ρ h u = ρ (singleHom K v (h v)) u := by
  conv_lhs => rw [← single_mul_eraseAt v h]
  rw [map_mul, Module.End.mul_apply, hu _ (eraseAt_mem_boxSubgroup v hh) (eraseAt_apply_self v h)]


omit hK'c hK'o hK'e in
theorem apply_single_fixed (v : ι) (x : G v) {m : V} (hm : m ∈ fixedVectors ρ (boxSubgroup K K'))
    {h : Πʳ w, [G w, K w]} (hh : h ∈ boxSubgroup K K') (hv : h v = 1) :
    ρ h (ρ (singleHom K v x) m) = ρ (singleHom K v x) m := by
  rw [← Module.End.mul_apply, ← map_mul, ← commute_singleHom x hv, map_mul, Module.End.mul_apply,
    hm h hh]


include hK'c hK'o hK'e in
theorem heckeOp_single_mul (v : ι) (x : G v) {b : Πʳ w, [G w, K w]} (hb : b v = 1) :
    heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
        (singleHom K v x * b) =
      heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e)
          (singleHom K v x) *
        heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) b := by
  ext m
  rw [Module.End.mul_apply, heckeOp_mul_apply]
  intro h hh
  refine ⟨eraseAt v h, eraseAt_mem_boxSubgroup v hh, ?_, ?_⟩
  · exact (commute_singleHom x (eraseAt_apply_self v h)).symm
  · have h1 : (eraseAt v h)⁻¹ * h = singleHom K v (h v) := by
      have hc := commute_singleHom (K := K) (h v) (eraseAt_apply_self v h)
      calc (eraseAt v h)⁻¹ * h = (eraseAt v h)⁻¹ * (singleHom K v (h v) * eraseAt v h) := by
            rw [single_mul_eraseAt]
        _ = singleHom K v (h v) := by rw [hc, inv_mul_cancel_left]
    rw [h1]
    exact commute_singleHom (h v) hb

def placeOps (v : ι) : Set (End ℂ (fixedVectors ρ (boxSubgroup K K'))) :=
  range fun x : G v => heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e)
    (isOpen_boxSubgroup hK'o hK'e) (singleHom K v x)

theorem commute_placeOps {v w : ι} (hvw : v ≠ w) :
    ∀ a ∈ placeOps hρ hK'c hK'o hK'e v, ∀ b ∈ placeOps hρ hK'c hK'o hK'e w, Commute a b := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
  have h1 := heckeOp_single_mul hρ hK'c hK'o hK'e v x (b := singleHom K w y)
    (singleHom_apply_of_ne y hvw)
  have h2 := heckeOp_single_mul hρ hK'c hK'o hK'e w y (b := singleHom K v x)
    (singleHom_apply_of_ne x hvw.symm)
  show _ * _ = _ * _
  rw [← h1, ← h2, commute_singleHom x (singleHom_apply_of_ne y hvw)]

theorem heckeOp_mem_adjoin (s : Finset ι) {g : Πʳ w, [G w, K w]} (hg : ∀ v ∉ s, g v ∈ K' v) :
    heckeOp hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) g ∈
      Algebra.adjoin ℂ (⋃ v ∈ s, placeOps hρ hK'c hK'o hK'e v) := by
  induction s using Finset.induction_on generalizing g with
  | empty =>
    rw [heckeOp_of_mem _ _ _ (show g ∈ boxSubgroup K K' from fun v => hg v (Finset.notMem_empty v))]
    exact Subalgebra.one_mem _
  | insert a s has ih =>
    have herase : ∀ v ∉ s, eraseAt a g v ∈ K' v := by
      intro v hv
      by_cases hva : v = a
      · subst hva; rw [eraseAt_apply_self]; exact (K' v).one_mem
      · rw [eraseAt_apply_of_ne _ hva]
        exact hg v (by simp [hva, hv])
    have hmono : Algebra.adjoin ℂ (⋃ v ∈ s, placeOps hρ hK'c hK'o hK'e v) ≤
        Algebra.adjoin ℂ (⋃ v ∈ insert a s, placeOps hρ hK'c hK'o hK'e v) :=
      Algebra.adjoin_mono (biUnion_subset_biUnion_left (by simp))
    rw [← single_mul_eraseAt a g, heckeOp_single_mul hρ hK'c hK'o hK'e a (g a)
      (eraseAt_apply_self a g)]
    refine Subalgebra.mul_mem _ (Algebra.subset_adjoin ?_) (hmono (ih herase))
    exact mem_biUnion (Finset.mem_insert_self a s) ⟨g a, rfl⟩

theorem fixedProj_single_eq (v : ι) (hρv : IsSmooth (ρ.comp (singleHom K v))) {u : V}
    (hu : ∀ h ∈ boxSubgroup K K', h v = 1 → ρ h u = u) :
    (fixedProj (ρ.comp (singleHom K v)) hρv (hK'c v) (hK'o v) u : V) =
      fixedProj ρ hρ (isCompact_boxSubgroup_of_eq hK'c hK'e) (isOpen_boxSubgroup hK'o hK'e) u :=
  fixedProj_comp_eq (singleHom K v) hρ hρv _ _ (hK'c v) (hK'o v)
    (fun k hk => singleHom_mem_boxSubgroup hk)
    (fun h hh => ⟨h v, hh v, apply_eq_apply_single v hu hh⟩)

end Window

end RestrictedTensor

end GroundTheory.Automorphic
