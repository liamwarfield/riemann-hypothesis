module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.SymmetricIndices.IndexSym
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ZNClosed
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.LocalContinuity.LocalDescentHolds

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.LocChi
noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Loc

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def Split : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {m : ℕ} (F : Fin m → Set (Matrix (Fin n) (Fin n) k)),
    (∀ i, IsClosed (F i) ∧ ∀ g ∈ Gz Z, ∀ x ∈ F i, g.val * x * g⁻¹.val ∈ F i) → (∀ i j, i ≠ j → Disjoint (F i) (F j)) →
    ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ ((⋃ i, F i) ×ˢ Set.univ) → Inv Z ξ →
      ∃ η : Fin m → (Sp k n → ℂ) →ₗ[ℂ] ℂ, (∀ i, Supp (η i) (F i ×ˢ Set.univ) ∧ Inv Z (η i)) ∧
        ∀ f ∈ supportedIn (Set.univ : Set (Sp k n)), ξ f = ∑ i, η i f

def LocChi : Prop :=
  ∀ (n : ℕ) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (U : Set (Sp k n)), IsOpen U →
    (∀ χ : k[X], ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ ((Bz Z ∩ {x | x.charpoly = χ}) ×ˢ Set.univ) → Inv Z ξ → Kills ξ U) →
    ∀ ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ, Supp ξ (Bz Z ×ˢ Set.univ) → Inv Z ξ → Kills ξ U

end PositivityTheory.RgUd.TP.Loc
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.Psplit
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.ExistsClopenSep
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Loc.Psplit

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

section Sep

variable {X : Type*} [TopologicalSpace X] [T2Space X] [LocallyCompactSpace X] [TotallyDisconnectedSpace X]

theorem exists_clopen_in {S A B : Set X} (hSc : IsCompact S) (hSo : IsOpen S) (hA : IsClosed A) (hB : IsClosed B)
    (hAB : Disjoint A B) : ∃ W : Set X, IsClopen W ∧ W ⊆ S ∧ A ∩ S ⊆ W ∧ Disjoint W B := by
  have hK : IsCompact (A ∩ S) := hSc.inter_left hA
  have key : ∀ x ∈ A ∩ S, ∃ V : Set X, IsClopen V ∧ x ∈ V ∧ V ⊆ S \ B := by
    intro x hx
    have hxo : x ∈ S \ B := ⟨hx.2, fun hb => disjoint_left.1 hAB hx.1 hb⟩
    exact loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 ((hSo.sdiff hB).mem_nhds hxo)
  choose V hV using key
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun x : ↥(A ∩ S) => V x.1 x.2)
    (fun x => (hV x.1 x.2).1.isOpen) (fun x hx => mem_iUnion.2 ⟨⟨x, hx⟩, (hV x hx).2.1⟩)
  refine ⟨⋃ i ∈ t, V i.1 i.2, ?_, ?_, ht, ?_⟩
  · exact t.finite_toSet.isClopen_biUnion (fun i _ => (hV i.1 i.2).1)
  · exact iUnion₂_subset fun i _ => ((hV i.1 i.2).2.2).trans diff_subset
  · refine disjoint_left.2 fun y hy hyB => ?_
    obtain ⟨i, -, hyi⟩ := mem_iUnion₂.1 hy
    exact ((hV i.1 i.2).2.2 hyi).2 hyB

variable [SigmaCompactSpace X]

theorem exists_exhaust : ∃ U : ℕ → Set X, (∀ m, IsCompact (U m) ∧ IsOpen (U m)) ∧ ∀ x, ∃ m, x ∈ U m := by
  have hW : ∀ x : X, ∃ W : Set X, IsCompact W ∧ IsOpen W ∧ x ∈ W := by
    intro x
    obtain ⟨C, hC, hxC⟩ := exists_compact_mem_nhds x
    obtain ⟨V, hV, hxV, hVC⟩ :=
      loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 (interior_mem_nhds.2 hxC)
    exact ⟨V, hC.of_isClosed_subset hV.1 (hVC.trans interior_subset), hV.2, hxV⟩
  choose W hWc hWo hxW using hW
  have hU : ∀ m : ℕ, ∃ U : Set X, IsCompact U ∧ IsOpen U ∧ compactCovering X m ⊆ U := by
    intro m
    obtain ⟨t, ht⟩ := (isCompact_compactCovering X m).elim_finite_subcover W hWo
      (fun x _ => mem_iUnion.2 ⟨x, hxW x⟩)
    exact ⟨⋃ i ∈ t, W i, t.isCompact_biUnion (fun i _ => hWc i), isOpen_biUnion (fun i _ => hWo i), ht⟩
  choose U hUc hUo hKU using hU
  refine ⟨U, fun m => ⟨hUc m, hUo m⟩, fun x => ?_⟩
  obtain ⟨m, hm⟩ := exists_mem_compactCovering x
  exact ⟨m, hKU m hm⟩

theorem exists_clopen_sep {A B : Set X} (hA : IsClosed A) (hB : IsClosed B) (hAB : Disjoint A B) :
    ∃ W : Set X, IsClopen W ∧ A ⊆ W ∧ Disjoint W B := by
  obtain ⟨U, hU, hcov⟩ := exists_exhaust (X := X)
  let D : ℕ → Set X := fun m => U m \ ⋃ j ∈ Finset.range m, U j
  have hD : ∀ m, D m = U m \ ⋃ j ∈ Finset.range m, U j := fun m => rfl
  have hUcl : ∀ j, IsClosed (U j) := fun j => (hU j).1.isClosed
  have hDc : ∀ m, IsCompact (D m) := fun m => by
    rw [hD]
    exact (hU m).1.diff (isOpen_biUnion fun j _ => (hU j).2)
  have hDo : ∀ m, IsOpen (D m) := fun m => by
    rw [hD]
    exact (hU m).2.sdiff (isClosed_biUnion_finset fun j _ => hUcl j)
  choose W hW using fun m => exists_clopen_in (hDc m) (hDo m) hA hB hAB
  have hDdisj : ∀ m m', m ≠ m' → Disjoint (D m) (D m') := by
    have key : ∀ m m', m < m' → Disjoint (D m) (D m') := by
      intro m m' h
      rw [hD, hD]
      refine disjoint_left.2 fun x hx hx' => hx'.2 ?_
      exact mem_iUnion₂.2 ⟨m, Finset.mem_range.2 h, hx.1⟩
    intro m m' h
    rcases lt_or_gt_of_ne h with h | h
    · exact key m m' h
    · exact (key m' m h).symm
  have hmemD : ∀ x, ∃ m, x ∈ D m := by
    intro x
    classical
    have hex : ∃ m, x ∈ U m := hcov x
    refine ⟨Nat.find hex, ?_⟩
    rw [hD]
    refine ⟨Nat.find_spec hex, fun hx => ?_⟩
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx
    exact Nat.find_min hex (Finset.mem_range.1 hj) hxj
  have hlf : LocallyFinite W := by
    intro x
    obtain ⟨m, hm⟩ := hmemD x
    refine ⟨D m, (hDo m).mem_nhds hm, (Set.finite_singleton m).subset ?_⟩
    rintro j ⟨y, hyW, hyD⟩
    by_contra hj
    exact disjoint_left.1 (hDdisj j m hj) ((hW j).2.1 hyW) hyD
  refine ⟨⋃ m, W m, ⟨hlf.isClosed_iUnion (fun m => (hW m).1.1),
    isOpen_iUnion fun m => (hW m).1.2⟩, ?_, ?_⟩
  · intro x hx
    obtain ⟨m, hm⟩ := hmemD x
    exact mem_iUnion.2 ⟨m, (hW m).2.2.1 ⟨hx, hm⟩⟩
  · exact disjoint_iUnion_left.2 fun m => (hW m).2.2.2

end Sep

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

theorem exists_clopens {m : ℕ} (F : Fin m → Set (Matrix (Fin n) (Fin n) k)) (hF : ∀ i, IsClosed (F i))
    (hd : ∀ i j, i ≠ j → Disjoint (F i) (F j)) :
    ∃ W : Fin m → Set (Matrix (Fin n) (Fin n) k), (∀ i, IsClopen (W i) ∧ F i ⊆ W i) ∧
      (∀ i j, i ≠ j → Disjoint (W i) (W j)) ∧ ∀ i j, i ≠ j → Disjoint (W i) (F j) := by
  classical
  have hna : NonarchimedeanRing k := by
    convert! (ValuativeRel.nonarchimedeanRing k)
    exact Valuation.toTopologicalSpace_eq _
  haveI : TotallyDisconnectedSpace k := inferInstance
  haveI : TotallyDisconnectedSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin n → Fin n → k))
  haveI : SigmaCompactSpace (Matrix (Fin n) (Fin n) k) :=
    inferInstanceAs (SigmaCompactSpace (Fin n → Fin n → k))
  let B : Fin m → Set (Matrix (Fin n) (Fin n) k) := fun i => ⋃ j ∈ Finset.univ.filter (· ≠ i), F j
  have hBmem : ∀ i j, j ≠ i → ∀ x ∈ F j, x ∈ B i := fun i j h x hx =>
    mem_iUnion₂.2 ⟨j, by simp [h], hx⟩
  have hBcl : ∀ i, IsClosed (B i) := fun i => isClosed_biUnion_finset fun j _ => hF j
  have hFB : ∀ i, Disjoint (F i) (B i) := by
    intro i
    refine disjoint_left.2 fun x hx hx' => ?_
    obtain ⟨j, hj, hxj⟩ := mem_iUnion₂.1 hx'
    have hji : j ≠ i := by simpa using hj
    exact disjoint_left.1 (hd i j (Ne.symm hji)) hx hxj
  choose V hV using fun i => Psplit.exists_clopen_sep (hF i) (hBcl i) (hFB i)
  refine ⟨fun i => V i ∩ ⋂ j ∈ Finset.univ.filter (· ≠ i), (V j)ᶜ, ?_, ?_, ?_⟩
  · intro i
    refine ⟨(hV i).1.inter (isClopen_biInter_finset fun j _ => (hV j).1.compl), ?_⟩
    intro x hx
    refine ⟨(hV i).2.1 hx, mem_iInter₂.2 fun j hj => ?_⟩
    have hji : j ≠ i := by simpa using hj
    exact fun hxV => disjoint_left.1 (hV j).2.2 hxV (hBmem j i (Ne.symm hji) x hx)
  · intro i j hij
    refine disjoint_left.2 fun x hx hx' => ?_
    exact mem_iInter₂.1 hx'.2 i (by simp [hij]) hx.1
  · intro i j hij
    refine disjoint_left.2 fun x hx hx' => ?_
    exact disjoint_left.1 (hV i).2.2 hx.1 (hBmem i j (Ne.symm hij) x hx')

private theorem comp_act_mem_supportedIn_univ (g : GL (Fin n) k) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (univ : Set (Sp k n))) :
    (fun p => f (act g p)) ∈ supportedIn (univ : Set (Sp k n)) := by
  have hc : ∀ h : GL (Fin n) k, Continuous (act h : Sp k n → Sp k n) := by
    intro h
    unfold act
    exact ((continuous_const.matrix_mul continuous_fst).matrix_mul continuous_const).prodMk
      (continuous_const.matrix_mulVec continuous_snd)
  let e : Sp k n ≃ₜ Sp k n :=
    { toFun := act g
      invFun := act g⁻¹
      left_inv := fun p => by rw [← Nil.Orb.act_mul, inv_mul_cancel, Nil.Orb.act_one]
      right_inv := fun p => by rw [← Nil.Orb.act_mul, mul_inv_cancel, Nil.Orb.act_one]
      continuous_toFun := hc g
      continuous_invFun := hc g⁻¹ }
  have h := (compHomeoL e ⟨f, hf.1⟩).property
  rw [coe_compHomeoL] at h
  exact ⟨h, subset_univ _⟩

theorem split_pf : PositivityTheory.RgUd.TP.Loc.Split k := by
  intro n Z m F hF hd ξ hsupp hinv
  obtain ⟨W, hW, hWd, hWF⟩ := exists_clopens F (fun i => (hF i).1) hd
  have hWp : ∀ i, IsClopen (W i ×ˢ (univ : Set (Fin n → k))) := fun i => (hW i).1.prod isClopen_univ
  let mul : Set (Sp k n) → (Sp k n → ℂ) →ₗ[ℂ] (Sp k n → ℂ) := fun A =>
    { toFun := fun f p => A.indicator 1 p * f p
      map_add' := fun f g => by
        funext p
        simp only [Pi.add_apply, mul_add]
      map_smul' := fun c f => by
        funext p
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        ring }
  have hmul : ∀ A f p, mul A f p = A.indicator 1 p * f p := fun _ _ _ => rfl
  have hind : ∀ (A : Set (Sp k n)) p, p ∈ A → A.indicator (1 : Sp k n → ℂ) p = 1 :=
    fun A p h => by simp [h]
  have hind0 : ∀ (A : Set (Sp k n)) p, p ∉ A → A.indicator (1 : Sp k n → ℂ) p = 0 :=
    fun A p h => by simp [h]
  refine ⟨fun i => ξ ∘ₗ mul (W i ×ˢ univ), fun i => ⟨?_, ?_⟩, ?_⟩
  · intro f hf hf0
    simp only [LinearMap.comp_apply]
    apply hsupp _ (indicator_mul_mem (hWp i) hf)
    rintro ⟨x, v⟩ ⟨hx, -⟩
    obtain ⟨j, hj⟩ := mem_iUnion.1 hx
    by_cases hij : i = j
    · subst hij
      show _ * f (x, v) = 0
      rw [hf0 (x, v) ⟨hj, mem_univ _⟩, mul_zero]
    · show _ * _ = 0
      rw [hind0 (W i ×ˢ univ) (x, v) (fun h => disjoint_left.1 (hWF i j hij) h.1 hj), zero_mul]
  · intro g hg f hf
    simp only [LinearMap.comp_apply]
    have hfg := comp_act_mem_supportedIn_univ g hf
    have h1 : ξ (fun p => mul (W i ×ˢ univ) f (act g p)) = ξ (mul (W i ×ˢ univ) f) :=
      hinv g hg _ (indicator_mul_mem (hWp i) hf)
    rw [← h1, ← sub_eq_zero, ← map_sub]
    apply hsupp
    · exact sub_mem (indicator_mul_mem (hWp i) hfg) (comp_act_mem_supportedIn_univ g (indicator_mul_mem (hWp i) hf))
    · rintro ⟨x, v⟩ ⟨hx, -⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      have hgx := (hF j).2 g hg x hj
      simp only [Pi.sub_apply, hmul]
      have e : (W i ×ˢ (univ : Set (Fin n → k))).indicator (1 : Sp k n → ℂ) (x, v) =
          (W i ×ˢ (univ : Set (Fin n → k))).indicator 1 (act g (x, v)) := by
        by_cases hij : i = j
        · subst hij
          rw [hind (W i ×ˢ univ) (x, v) ⟨(hW i).2 hj, mem_univ _⟩,
            hind (W i ×ˢ univ) (act g (x, v)) ⟨(hW i).2 hgx, mem_univ _⟩]
        · rw [hind0 (W i ×ˢ univ) (x, v) (fun h => disjoint_left.1 (hWF i j hij) h.1 hj),
            hind0 (W i ×ˢ univ) (act g (x, v)) (fun h => disjoint_left.1 (hWF i j hij) h.1 hgx)]
      rw [e, sub_self]
  · intro f hf
    simp only [LinearMap.comp_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← sub_eq_zero, ← map_sum, ← map_sub]
    apply hsupp
    · exact sub_mem hf (sum_mem fun i _ => indicator_mul_mem (hWp i) hf)
    · rintro ⟨x, v⟩ ⟨hx, -⟩
      obtain ⟨j, hj⟩ := mem_iUnion.1 hx
      rw [Pi.sub_apply, Finset.sum_apply, Finset.sum_eq_single j]
      · rw [hmul, hind (W j ×ˢ univ) (x, v) ⟨(hW j).2 hj, mem_univ _⟩, one_mul, sub_self]
      · intro i _ hij
        rw [hmul, hind0 (W i ×ˢ univ) (x, v)
          (fun h => disjoint_left.1 (hWd i j hij) h.1 ((hW j).2 hj)), zero_mul]
      · intro h
        exact absurd (Finset.mem_univ j) h

end PositivityTheory.RgUd.TP.Loc.Psplit
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.ContinuousCp
noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Loc.Psplit

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def cp (x : Matrix (Fin n) (Fin n) k) : Fin (n + 1) → k := fun i => x.charpoly.coeff i

theorem continuous_cp : Continuous (cp : Matrix (Fin n) (Fin n) k → _) :=
  continuous_pi fun i => GroundTheory.Automorphic.ContragredientTranspose.continuous_charpoly_coeff_of_fintype (i : ℕ)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem cp_conj (g : GL (Fin n) k) (x : Matrix (Fin n) (Fin n) k) : cp (g.val * x * g⁻¹.val) = cp x := by
  funext i
  simp only [cp]
  rw [charpoly_mul_comm, ← mul_assoc, Units.inv_mul, one_mul]

def poly (y : Fin (n + 1) → k) : k[X] := ∑ i : Fin (n + 1), C (y i) * X ^ (i : ℕ)

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem cp_eq_iff (x : Matrix (Fin n) (Fin n) k) (y : Fin (n + 1) → k) : cp x = y ↔ x.charpoly = poly y := by
  constructor
  · rintro rfl
    have h := as_sum_range' x.charpoly (n + 1) (by rw [charpoly_natDegree_eq_dim, Fintype.card_fin]; omega)
    rw [h, poly, ← Fin.sum_univ_eq_sum_range (fun i => (monomial i) (x.charpoly.coeff i)) (n + 1)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← C_mul_X_pow_eq_monomial]
    rfl
  · intro h
    funext i
    simp only [cp, h, poly, finsetSum_coeff, coeff_C_mul, coeff_X_pow]
    rw [Finset.sum_eq_single i (fun j _ hj => by rw [if_neg (fun e => hj (Fin.ext e.symm)), mul_zero]) (by simp)]
    simp

theorem locChi_pf : PositivityTheory.RgUd.TP.Loc.LocChi k := by
  intro n Z U hU hfib ξ hS hI
  have : TotallyDisconnectedSpace k := totallyDisconnectedSpace_localField
  let p : Sp k n → _ := fun q => cp q.1
  have hp : Continuous p := continuous_cp.comp continuous_fst
  have hpact : ∀ g ∈ Gz Z, ∀ q, p (act g q) = p q := fun g _ q => cp_conj g q.1
  let C : Set (Sp k n) := Bz Z ×ˢ univ
  have hC : IsClosed C := (PositivityTheory.RgUd.T.LocStepPf.isClosed_Bz Z).prod isClosed_univ
  let W : Submodule ℂ (Sp k n → ℂ) :=
    { carrier := {w | ∀ V, IsClopen V → ξ (fun x => (p ⁻¹' V).indicator 1 x * w x) = 0}
      add_mem' := fun {a b} ha hb V hV => by
        have e : (fun x => (p ⁻¹' V).indicator 1 x * (a + b) x) =
            (fun x => (p ⁻¹' V).indicator 1 x * a x) + (fun x => (p ⁻¹' V).indicator 1 x * b x) := by
          funext x
          simp [mul_add]
        rw [e, map_add (f := _), ha V hV, hb V hV, add_zero]
      zero_mem' := fun V _ => by
        have e : (fun x => (p ⁻¹' V).indicator 1 x * (0 : Sp k n → ℂ) x) = 0 := by
          funext x
          simp
        rw [e, map_zero]
      smul_mem' := fun c a ha V hV => by
        have e : (fun x => (p ⁻¹' V).indicator 1 x * (c • a) x) =
            c • (fun x => (p ⁻¹' V).indicator 1 x * a x) := by
          funext x
          simp only [Pi.smul_apply, smul_eq_mul]
          ring
        rw [e, map_smul, ha V hV, smul_zero] }
  intro g hg
  have key : g ∈ W := by
    refine mem_of_forall_fiber (U := univ) hC hp ?_ ?_ (supportedIn_mono (subset_univ _) hg) ?_
    · rintro w ⟨hw1, hw2⟩ V hV
      refine hS _ (indicator_mul_mem (hV.preimage hp) hw1) fun q hq => ?_
      simp [(mem_vanishingOn.1 hw2) q hq]
    · intro V hV w hw V' hV'
      have := hw (V' ∩ V) (hV'.inter hV)
      convert this using 2
      funext x
      by_cases h1 : p x ∈ V' <;> by_cases h2 : p x ∈ V <;>
        simp [h1, h2]
    · intro y
      let N : Submodule ℂ (Sp k n → ℂ) := Submodule.span ℂ
        {h | ∃ γ ∈ Gz Z, ∃ f ∈ supportedIn (univ : Set (Sp k n)), h = (fun q => f (act γ q)) - f}
      have hmem : g ∈ N ⊔ (supportedIn univ ⊓ vanishingOn (C ∩ p ⁻¹' {y})) := by
        by_contra hn
        obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_notMem hn
        refine hf0 (hfib (poly y) f ?_ ?_ g hg)
        · intro u hu hu0
          refine hle (Submodule.mem_sup_right ⟨hu, fun q hq => hu0 q ⟨⟨hq.1.1, ?_⟩, trivial⟩⟩)
          exact (cp_eq_iff q.1 y).1 hq.2
        · intro γ hγ u hu
          have h1 : (fun q => u (act γ q)) - u ∈ N := Submodule.subset_span ⟨γ, hγ, u, hu, rfl⟩
          have h3 := hle (Submodule.mem_sup_left h1)
          rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h3
          exact h3
      have hNW : N ≤ W := by
        rw [Submodule.span_le]
        rintro _ ⟨γ, hγ, u, hu, rfl⟩ V hV
        have hu' := indicator_mul_mem (hV.preimage hp) hu
        have h3 := hI γ hγ _ hu'
        rw [← sub_eq_zero, ← map_sub] at h3
        convert h3 using 2
        funext q
        have e : p (act γ q) = p q := hpact γ hγ q
        by_cases h1 : p q ∈ V <;> simp [h1, e]
      exact sup_le_sup_right hNW _ hmem
  have := key univ isClopen_univ
  simpa using this

end PositivityTheory.RgUd.TP.Loc.Psplit
end
end

noncomputable section

open Matrix Polynomial GroundTheory.Automorphic.Whittaker Set

namespace PositivityTheory.RgUd.TP.Loc.Psplit

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem fib_split (hSp : PositivityTheory.RgUd.TP.Loc.Split k) {n : ℕ} (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (χ : k[X]) {m : ℕ}
    (F : Fin m → Set (Matrix (Fin n) (Fin n) k)) (hF : IsPieces Z χ F) (ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ)
    (hS : Supp ξ ((Bz Z ∩ {x | x.charpoly = χ}) ×ˢ univ)) (hI : Inv Z ξ) :
    ∃ η : Fin m → (Sp k n → ℂ) →ₗ[ℂ] ℂ, (∀ i, Supp (η i) (F i ×ˢ univ) ∧ Inv Z (η i)) ∧
      ∀ f ∈ supportedIn (univ : Set (Sp k n)), ξ f = ∑ i, η i f := by
  refine hSp n Z F (fun i => ⟨(hF.1 i).1, (hF.1 i).2.2⟩) hF.2.1 ξ ?_ hI
  intro f hf h0
  refine hS f hf fun p hp => ?_
  obtain ⟨i, hi⟩ := hF.2.2 p.1 hp.1.1 hp.1.2
  exact h0 p ⟨mem_iUnion.2 ⟨i, hi⟩, mem_univ _⟩

theorem locAll_of_pf : PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocAll k := by
  intro hSp hLC n Z _hZ hP ξ hS hI
  have hU : IsOpen {p : Sp k n | p.2 ≠ 0} := (isClosed_eq continuous_snd continuous_const).isOpen_compl
  refine hLC n Z _ hU (fun χ ξ' hS' hI' f hf => ?_) ξ hS hI
  obtain ⟨m, F, hF, hi⟩ := hP χ
  obtain ⟨η, hη, hsum⟩ := fib_split hSp Z χ F hF ξ' hS' hI'
  rw [hsum f (supportedIn_mono (subset_univ _) hf)]
  exact Finset.sum_eq_zero fun i _ => hi i (η i) (hη i).1 (hη i).2 f hf

theorem locOff_of_pf : PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocOff k := by
  intro hSp hLC n Z _hZ hP ξ hS hI U hU hUp
  refine hLC n Z U hU (fun χ ξ' hS' hI' f hf => ?_) ξ hS hI
  obtain ⟨m, F, hF, hi⟩ := hP χ
  obtain ⟨η, hη, hsum⟩ := fib_split hSp Z χ F hF ξ' hS' hI'
  rw [hsum f (supportedIn_mono (subset_univ _) hf)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases hi i with ⟨c, hc, hnil⟩ | hv
  · refine (hη i).1 f (supportedIn_mono (subset_univ _) hf) fun p hp => ?_
    by_contra h0
    exact ((hUp p (hf.2 h0)).2) ⟨⟨c, hc, hnil p.1 hp.1⟩, (hF.1 i).2.1 hp.1⟩
  · exact hv (η i) (hη i).1 (hη i).2 f (supportedIn_mono (fun p hp => (hUp p hp).1) hf)

theorem split (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.Split k := split_pf
theorem locChi (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.LocChi k := locChi_pf
theorem locOff_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocOff k := locOff_of_pf
theorem locAll_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    PositivityTheory.RgUd.TP.Loc.Split k → PositivityTheory.RgUd.TP.Loc.LocChi k → LocAll k := locAll_of_pf

end PositivityTheory.RgUd.TP.Loc.Psplit
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.Ptransl
noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.TP.Loc.Ptransl

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def trH (c : Matrix (Fin n) (Fin n) k) : Sp k n ≃ₜ Sp k n where
  toFun p := (p.1 - c, p.2)
  invFun p := (p.1 + c, p.2)
  left_inv p := by simp
  right_inv p := by simp
  continuous_toFun := (continuous_fst.sub continuous_const).prodMk continuous_snd
  continuous_invFun := (continuous_fst.add continuous_const).prodMk continuous_snd

omit [ValuativeRel k] [IsNonarchimedeanLocalField k] in
theorem comp_mem {U V : Set (Sp k n)} (e : Sp k n ≃ₜ Sp k n) (hUV : ∀ p, e p ∈ U → p ∈ V) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn U) : (fun p => f (e p)) ∈ supportedIn V := by
  obtain ⟨⟨hlc, hcs⟩, hsupp⟩ := hf
  refine ⟨⟨hlc.comp_continuous e.continuous, hcs.comp_homeomorph e⟩, ?_⟩
  intro p hp
  exact hUV p (hsupp hp)

theorem act_trH {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z)
    {g : GL (Fin n) k} (hg : g ∈ Gz Z) (p : Sp k n) : act g (trH c p) = trH c (act g p) := by
  have hcomm : c * (g : Matrix (Fin n) (Fin n) k) = g * c := hg c hc
  have hconj : (g : Matrix (Fin n) (Fin n) k) * c * (g⁻¹ : GL (Fin n) k) = c := by
    rw [← hcomm, Matrix.mul_assoc]
    simp
  simp only [act, trH, Homeomorph.homeomorph_mk_coe, Equiv.coe_fn_mk, Prod.mk.injEq, and_true]
  rw [Matrix.mul_sub, Matrix.sub_mul, hconj]

theorem transl : Transl k := by
  intro m Z hCR hNB c hc F hF hnil ξ hsupp hinv
  let ξ' : (Sp k m → ℂ) →ₗ[ℂ] ℂ := ξ.comp (LinearMap.funLeft ℂ ℂ (trH c))
  have hξ' : ∀ f, ξ' f = ξ (fun p => f (trH c p)) := fun f => rfl
  have hmem : ∀ f ∈ supportedIn (Set.univ : Set (Sp k m)),
      (fun p => f (trH c p)) ∈ supportedIn (Set.univ : Set (Sp k m)) :=
    fun f hf => comp_mem (trH c) (fun _ _ => Set.mem_univ _) hf
  have hS : Supp ξ' (NB Z ×ˢ Set.univ) := by
    intro f hf hz
    rw [hξ']
    refine hsupp _ (hmem f hf) ?_
    rintro ⟨x, v⟩ ⟨hx, -⟩
    apply hz
    refine ⟨⟨?_, ?_⟩, Set.mem_univ _⟩
    · intro a ha
      have h1 : a * x = x * a := hF hx a ha
      have h2 : a * c = c * a := hCR.1 a ha c hc
      change a * (x - c) = (x - c) * a
      rw [Matrix.mul_sub, Matrix.sub_mul, h1, h2]
    · exact hnil x hx
  have hI : T.Inv Z ξ' := by
    intro g hg f hf
    rw [hξ', hξ']
    have : (fun p => f (act g (trH c p))) = (fun p => (fun q => f (trH c q)) (act g p)) := by
      funext p
      rw [act_trH hc hg]
    rw [this]
    exact hinv g hg _ (hmem f hf)
  have hK := hNB ξ' hS hI
  intro f hf
  have hf' : (fun p => f ((trH c).symm p)) ∈ supportedIn {p : Sp k m | p.2 ≠ 0} :=
    comp_mem (trH c).symm (fun _ h => h) hf
  have := hK _ hf'
  rw [hξ'] at this
  simpa using this

end PositivityTheory.RgUd.TP.Loc.Ptransl
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceFormCore
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.LocalTraceForms.TraceCompSmulRight
noncomputable section

open Module

namespace PositivityTheory.RgUd.TP.Loc.Ptf

section Fibre

variable {R V : Type*} [CommRing R] [AddCommGroup V] [Module R V]

theorem mk_smul (I : Ideal R) (r : R) (w : V ⧸ (I • (⊤ : Submodule R V))) :
    (Ideal.Quotient.mk I r) • w = r • w := by
  induction w using Submodule.Quotient.induction_on with
  | H v => rfl

theorem le_comap (I : Ideal R) (x : V →ₗ[R] V) :
    I • (⊤ : Submodule R V) ≤ (I • (⊤ : Submodule R V)).comap x := by
  rw [← Submodule.map_le_iff_le_comap, Submodule.map_smul'']
  exact Submodule.smul_mono le_rfl le_top

def xq (I : Ideal R) (x : V →ₗ[R] V) :
    (V ⧸ (I • (⊤ : Submodule R V))) →ₗ[R ⧸ I] (V ⧸ (I • (⊤ : Submodule R V))) where
  toFun := Submodule.mapQ _ _ x (le_comap I x)
  map_add' := map_add _
  map_smul' c w := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    simp only [RingHom.id_apply, mk_smul]
    exact map_smul _ r w

theorem xq_mk (I : Ideal R) (x : V →ₗ[R] V) (v : V) :
    xq I x (Submodule.Quotient.mk v) = Submodule.Quotient.mk (x v) := rfl

theorem xq_ext (I : Ideal R) {f g : (V ⧸ (I • (⊤ : Submodule R V))) →ₗ[R ⧸ I] (V ⧸ (I • (⊤ : Submodule R V)))}
    (h : ∀ v : V, f (Submodule.Quotient.mk v) = g (Submodule.Quotient.mk v)) : f = g :=
  LinearMap.ext fun w => by
    induction w using Submodule.Quotient.induction_on with
    | H v => exact h v

theorem xq_mul (I : Ideal R) (x y : V →ₗ[R] V) : xq I (x * y) = xq I x * xq I y :=
  xq_ext I fun _ => rfl

theorem xq_one (I : Ideal R) : xq I (1 : V →ₗ[R] V) = 1 := xq_ext I fun _ => rfl

theorem xq_zero (I : Ideal R) : xq I (0 : V →ₗ[R] V) = 0 := xq_ext I fun _ => rfl

theorem xq_add (I : Ideal R) (x y : V →ₗ[R] V) : xq I (x + y) = xq I x + xq I y :=
  xq_ext I fun _ => rfl

theorem xq_pow (I : Ideal R) (x : V →ₗ[R] V) (m : ℕ) : xq I (x ^ m) = xq I x ^ m := by
  induction m with
  | zero => simp [xq_one]
  | succ m ih => rw [pow_succ, xq_mul, ih, pow_succ]

theorem xq_smul {k : Type*} [Field k] [Algebra k R] [Module k V] [IsScalarTower k R V] (I : Ideal R) (c : k)
    (x : V →ₗ[R] V) : xq I (c • x) = (algebraMap k (R ⧸ I) c) • xq I x := by
  refine xq_ext I fun v => ?_
  rw [LinearMap.smul_apply, xq_mk, xq_mk, LinearMap.smul_apply, ← algebraMap_smul R c (x v),
    ← Ideal.Quotient.mk_algebraMap, mk_smul]
  rfl

theorem trace_comp_smulRight {K W : Type*} [Field K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]
    (f : W →ₗ[K] W) (φ : Module.Dual K W) (w : W) : LinearMap.trace K W (f * φ.smulRight w) = φ (f w) := by
  have e : f * φ.smulRight w = φ.smulRight (f w) := by
    ext u
    simp
  have e2 : φ.smulRight (f w) = dualTensorHom K W W (φ ⊗ₜ f w) := by
    ext u
    simp [dualTensorHom_apply]
  rw [e, e2, LinearMap.trace_eq_contract_apply]
  simp

end Fibre

open Classical

attribute [local instance] Ideal.Quotient.field

instance isMax {R : Type*} [CommRing R] (I : MaximalSpectrum R) : I.asIdeal.IsMaximal := I.isMaximal

theorem finQ (k : Type*) {R V : Type*} [Field k] [CommRing R] [Algebra k R] [AddCommGroup V] [Module R V] [Module k V]
    [IsScalarTower k R V] [FiniteDimensional k V] (I : MaximalSpectrum R) :
    FiniteDimensional (R ⧸ I.asIdeal) (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) := by
  haveI : Module.Finite R V := Module.Finite.of_restrictScalars_finite k R V
  exact Module.Finite.of_restrictScalars_finite R _ _

theorem exists_lam (k : Type*) {R : Type*} [Field k] [CommRing R] [Algebra k R] (I : MaximalSpectrum R) :
    ∃ l : (R ⧸ I.asIdeal) →ₗ[k] k, l 1 ≠ 0 := by
  let b := Module.Free.chooseBasis k (R ⧸ I.asIdeal)
  have h1 : b.repr 1 ≠ 0 := by
    intro h
    exact one_ne_zero (b.repr.injective (h.trans (map_zero _).symm))
  obtain ⟨i, hi⟩ : ∃ i, b.repr 1 i ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact h1 (Finsupp.ext hne)
  exact ⟨b.coord i, hi⟩

variable {k R V : Type*} [Field k] [CommRing R] [IsArtinianRing R] [IsReduced R] [Algebra k R]
  [AddCommGroup V] [Module R V] [Module k V] [IsScalarTower k R V] [FiniteDimensional k V]

instance : Fintype (MaximalSpectrum R) := Fintype.ofFinite _

def lam (I : MaximalSpectrum R) : (R ⧸ I.asIdeal) →ₗ[k] k := (exists_lam k I).choose

theorem lam_one (I : MaximalSpectrum R) : lam (k := k) I 1 ≠ 0 := (exists_lam k I).choose_spec

def tI (I : MaximalSpectrum R) (x : V →ₗ[R] V) : k :=
  haveI := finQ k (V := V) I
  lam (k := k) I (LinearMap.trace (R ⧸ I.asIdeal) _ (xq I.asIdeal x))

theorem tI_add (I : MaximalSpectrum R) (x y : V →ₗ[R] V) : tI (k := k) I (x + y) = tI I x + tI I y := by
  simp only [tI, xq_add, map_add (f := _)]

theorem tI_smul (I : MaximalSpectrum R) (c : k) (x : V →ₗ[R] V) : tI (k := k) I (c • x) = c • tI I x := by
  simp only [tI, xq_smul, map_smul, smul_eq_mul]
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

def tau : (V →ₗ[R] V) →ₗ[k] k where
  toFun x := ∑ I : MaximalSpectrum R, tI (k := k) I x
  map_add' x y := by simp only [tI_add, Finset.sum_add_distrib]
  map_smul' c x := by simp only [tI_smul, RingHom.id_apply, Finset.smul_sum]

theorem tau_apply (x : V →ₗ[R] V) : tau (k := k) x = ∑ I : MaximalSpectrum R, tI (k := k) I x := rfl

theorem tau_comm (x y : V →ₗ[R] V) : tau (k := k) (x * y) = tau (k := k) (y * x) := by
  simp only [tau_apply, tI, xq_mul, LinearMap.trace_mul_comm]

theorem tau_nil (x : V →ₗ[R] V) (hx : IsNilpotent x) : tau (k := k) x = 0 := by
  rw [tau_apply]
  refine Finset.sum_eq_zero fun I _ => ?_
  haveI := finQ k (V := V) I
  obtain ⟨m, hm⟩ := hx
  have h1 : IsNilpotent (xq I.asIdeal x) := ⟨m, by rw [← xq_pow, hm, xq_zero]⟩
  have h2 := (LinearMap.isNilpotent_trace_of_isNilpotent h1).eq_zero
  simp only [tI, h2, map_zero]

def eI (I : MaximalSpectrum R) : R := (IsArtinianRing.equivPi R).symm (Pi.single I 1)

theorem equivPi_apply' (r : R) (J : MaximalSpectrum R) :
    IsArtinianRing.equivPi R r J = Ideal.Quotient.mk J.asIdeal r := rfl

theorem eI_mem {I J : MaximalSpectrum R} (h : J ≠ I) : eI I ∈ J.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← equivPi_apply', eI, AlgEquiv.apply_symm_apply, Pi.single_eq_of_ne h]

theorem eI_sub_one (I : MaximalSpectrum R) : eI I - 1 ∈ I.asIdeal := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, ← equivPi_apply', eI, AlgEquiv.apply_symm_apply, Pi.single_eq_same,
    map_one, sub_self]

theorem eI_mul (I : MaximalSpectrum R) {r : R} (hr : r ∈ I.asIdeal) : eI I * r = 0 := by
  apply (IsArtinianRing.equivPi R).injective
  rw [map_mul, map_zero, eI, AlgEquiv.apply_symm_apply]
  funext J
  by_cases h : J = I
  · subst h
    simp [equivPi_apply', Ideal.Quotient.eq_zero_iff_mem.2 hr]
  · simp [Pi.single_eq_of_ne h]

theorem sum_eI : ∑ I : MaximalSpectrum R, eI I = 1 := by
  apply (IsArtinianRing.equivPi R).injective
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_one]
  simp only [eI, AlgEquiv.apply_symm_apply]
  exact Finset.univ_sum_single 1

theorem eI_smul_eq_zero (I : MaximalSpectrum R) {w : V} (hw : w ∈ I.asIdeal • (⊤ : Submodule R V)) :
    eI I • w = 0 := by
  refine Submodule.smul_induction_on (p := fun w => eI I • w = 0) hw (fun r hr m _ => ?_) (fun a b ha hb => ?_)
  · rw [smul_smul, eI_mul I hr, zero_smul]
  · rw [smul_add, ha, hb, add_zero]

theorem eq_zero_of_xq (x : V →ₗ[R] V) (h : ∀ I : MaximalSpectrum R, xq I.asIdeal x = 0) : x = 0 := by
  ext v
  have hv : ∀ I : MaximalSpectrum R, x v ∈ I.asIdeal • (⊤ : Submodule R V) := fun I => by
    rw [← Submodule.Quotient.mk_eq_zero, ← xq_mk, h I, LinearMap.zero_apply]
  rw [LinearMap.zero_apply, ← one_smul R (x v), ← sum_eI, Finset.sum_smul]
  exact Finset.sum_eq_zero fun I _ => eI_smul_eq_zero I (hv I)

def sec (I : MaximalSpectrum R) : (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) →ₗ[R] V :=
  (I.asIdeal • (⊤ : Submodule R V)).liftQ (eI I • LinearMap.id) fun w hw => by
    simp only [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
    exact eI_smul_eq_zero I hw

theorem exists_lift (I : MaximalSpectrum R)
    (g : (V ⧸ (I.asIdeal • (⊤ : Submodule R V))) →ₗ[R ⧸ I.asIdeal] (V ⧸ (I.asIdeal • (⊤ : Submodule R V)))) :
    ∃ y : V →ₗ[R] V, xq I.asIdeal y = g ∧ ∀ J ≠ I, xq J.asIdeal y = 0 := by
  refine ⟨sec I ∘ₗ (g.restrictScalars R) ∘ₗ (I.asIdeal • (⊤ : Submodule R V)).mkQ, ?_, fun J hJ => ?_⟩
  · refine xq_ext _ fun v => ?_
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk v))
    rw [xq_mk]
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply]
    rw [← hu, sec, Submodule.liftQ_apply]
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    have e : eI I • u - u = (eI I - 1) • u := by rw [sub_smul, one_smul]
    rw [e]
    exact Submodule.smul_mem_smul (eI_sub_one I) (Submodule.mem_top : u ∈ (⊤ : Submodule R V))
  · refine xq_ext _ fun v => ?_
    obtain ⟨u, hu⟩ := Submodule.Quotient.mk_surjective _ (g (Submodule.Quotient.mk v))
    rw [xq_mk]
    simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.restrictScalars_apply]
    rw [← hu, sec, Submodule.liftQ_apply]
    simp only [LinearMap.smul_apply, LinearMap.id_apply, LinearMap.zero_apply]
    rw [Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (eI_mem hJ) (Submodule.mem_top : u ∈ (⊤ : Submodule R V))

theorem tau_nondeg (x : V →ₗ[R] V) (h : ∀ y : V →ₗ[R] V, tau (k := k) (x * y) = 0) : x = 0 := by
  by_contra hx
  obtain ⟨I, hI⟩ : ∃ I : MaximalSpectrum R, xq I.asIdeal x ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hx (eq_zero_of_xq x hne)
  haveI := finQ k (V := V) I
  obtain ⟨w, hw⟩ : ∃ w, xq I.asIdeal x w ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hI (LinearMap.ext hne)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (R ⧸ I.asIdeal) _, φ (xq I.asIdeal x w) ≠ 0 := by
    by_contra hne
    push_neg at hne
    exact hw ((Module.forall_dual_apply_eq_zero_iff _ _).1 hne)
  obtain ⟨y, hy1, hy2⟩ := exists_lift I ((φ (xq I.asIdeal x w))⁻¹ • φ.smulRight w)
  have := h y
  rw [tau_apply, Finset.sum_eq_single I] at this
  · apply lam_one (k := k) I
    simp only [tI, xq_mul, hy1] at this
    rwa [mul_smul_comm, map_smul, trace_comp_smulRight, smul_eq_mul, inv_mul_cancel₀ hφ] at this
  · intro J _ hJ
    simp only [tI, xq_mul, hy2 J hJ, mul_zero, map_zero]
  · intro hn
    exact absurd (Finset.mem_univ I) hn

theorem exists_tau : ∃ τ : (V →ₗ[R] V) →ₗ[k] k, (∀ x y, τ (x * y) = τ (y * x)) ∧
    (∀ x, (∀ y, τ (x * y) = 0) → x = 0) ∧ ∀ x, IsNilpotent x → τ x = 0 :=
  ⟨tau, tau_comm, tau_nondeg, tau_nil⟩

end PositivityTheory.RgUd.TP.Loc.Ptf
end
end

noncomputable section

open Matrix

namespace PositivityTheory.RgUd.TP.Loc.Ptf

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable {k : Type} [Field k] {n : ℕ}

def bSub (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Submodule k (Matrix (Fin n) (Fin n) k) where
  carrier := Bz Z
  add_mem' {x y} hx hy a ha := by rw [mul_add, add_mul, hx a ha, hy a ha]
  zero_mem' a _ := by simp
  smul_mem' c x hx a ha := by rw [mul_smul_comm, smul_mul_assoc, hx a ha]

theorem mul_mem_bz {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} {x y : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z)
    (hy : y ∈ Bz Z) : x * y ∈ Bz Z := by
  intro a ha
  rw [← mul_assoc, hx a ha, mul_assoc, hy a ha, ← mul_assoc]

def RZ (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Type := Z

section Inst

variable (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z)

def crZ : CommRing (RZ Z) := { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }

def valZ : @RingHom (RZ Z) (Matrix (Fin n) (Fin n) k) (crZ Z hZ).toNonAssocSemiring _ :=
  letI := crZ Z hZ
  { toFun := fun z => (show Z from z).1
    map_one' := rfl
    map_mul' := fun _ _ => rfl
    map_zero' := rfl
    map_add' := fun _ _ => rfl }

def algZ : @RingHom k (RZ Z) _ (crZ Z hZ).toNonAssocSemiring :=
  letI := crZ Z hZ
  { toFun := fun c => (show RZ Z from (⟨algebraMap k _ c, Z.algebraMap_mem c⟩ : Z))
    map_one' := Subtype.ext (map_one _)
    map_mul' := fun a b => Subtype.ext (map_mul (algebraMap k (Matrix (Fin n) (Fin n) k)) a b)
    map_zero' := Subtype.ext (map_zero _)
    map_add' := fun a b => Subtype.ext (map_add (algebraMap k (Matrix (Fin n) (Fin n) k)) a b) }

end Inst

theorem traceForm_core (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) :
    ∃ τ : Matrix (Fin n) (Fin n) k →ₗ[k] k,
      (∀ x ∈ Bz Z, ∀ y ∈ Bz Z, τ (x * y) = τ (y * x)) ∧ (∀ x ∈ Bz Z, (∀ y ∈ Bz Z, τ (x * y) = 0) → x = 0) ∧
        ∀ x ∈ NB Z, τ x = 0 := by
  letI : CommRing (RZ Z) := crZ Z hZ
  letI : Algebra k (RZ Z) := (algZ Z hZ).toAlgebra
  letI : Module (RZ Z) (Fin n → k) := Module.compHom (Fin n → k)
    ((Matrix.toLinAlgEquiv' (R := k) (n := Fin n)).toRingEquiv.toRingHom.comp (valZ Z hZ))
  have hsmul : ∀ (r : RZ Z) (v : Fin n → k), r • v = (valZ Z hZ r) *ᵥ v := fun r v => rfl
  have hval : ∀ (c : k) (r : RZ Z), valZ Z hZ (c • r) = c • valZ Z hZ r := by
    intro c r
    rw [Algebra.smul_def, map_mul]
    show algebraMap k (Matrix (Fin n) (Fin n) k) c * valZ Z hZ r = _
    rw [Algebra.smul_def]
  haveI : IsScalarTower k (RZ Z) (Fin n → k) := ⟨fun c r v => by
    rw [hsmul, hsmul, hval, Matrix.smul_mulVec]⟩
  let L : RZ Z →ₗ[k] Matrix (Fin n) (Fin n) k :=
    { toFun := valZ Z hZ
      map_add' := map_add _
      map_smul' := hval }
  have hLinj : Function.Injective L := fun a b h => Subtype.ext h
  haveI : Module.Finite k (RZ Z) := Module.Finite.of_injective L hLinj
  haveI : IsArtinianRing (RZ Z) := IsArtinianRing.of_finite k (RZ Z)
  haveI : IsReduced (RZ Z) := hZ.2
  obtain ⟨τ0, hc, hnd, hnil⟩ := exists_tau (k := k) (R := RZ Z) (V := Fin n → k)
  have hcomm : ∀ x ∈ Bz Z, ∀ r : RZ Z, x * valZ Z hZ r = valZ Z hZ r * x :=
    fun x hx r => (hx _ (show Z from r).2).symm
  let ψ : bSub Z →ₗ[k] ((Fin n → k) →ₗ[RZ Z] (Fin n → k)) :=
    { toFun := fun x =>
        { toFun := fun v => x.1 *ᵥ v
          map_add' := fun v w => Matrix.mulVec_add _ _ _
          map_smul' := fun r v => by
            show x.1 *ᵥ (valZ Z hZ r *ᵥ v) = valZ Z hZ r *ᵥ (x.1 *ᵥ v)
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hcomm x.1 x.2 r] }
      map_add' := fun x y => LinearMap.ext fun v => by
        show (x.1 + y.1) *ᵥ v = x.1 *ᵥ v + y.1 *ᵥ v
        exact Matrix.add_mulVec _ _ _
      map_smul' := fun c x => LinearMap.ext fun v => by
        show (c • x.1) *ᵥ v = c • (x.1 *ᵥ v)
        exact Matrix.smul_mulVec _ _ _ }
  have hψ : ∀ (x : bSub Z) (v : Fin n → k), ψ x v = x.1 *ᵥ v := fun x v => rfl
  have hψmul : ∀ x (hx : x ∈ Bz Z) y (hy : y ∈ Bz Z),
      ψ ⟨x * y, mul_mem_bz hx hy⟩ = ψ ⟨x, hx⟩ * ψ ⟨y, hy⟩ := by
    intro x hx y hy
    refine LinearMap.ext fun v => ?_
    rw [Module.End.mul_apply, hψ, hψ, hψ, Matrix.mulVec_mulVec]
  obtain ⟨τ, hτ⟩ := LinearMap.exists_extend (τ0.comp ψ)
  have hτx : ∀ x (hx : x ∈ Bz Z), τ x = τ0 (ψ ⟨x, hx⟩) := fun x hx =>
    LinearMap.congr_fun hτ ⟨x, hx⟩
  refine ⟨τ, ?_, ?_, ?_⟩
  · intro x hx y hy
    rw [hτx _ (mul_mem_bz hx hy), hτx _ (mul_mem_bz hy hx), hψmul x hx y hy, hψmul y hy x hx, hc]
  · intro x hx H
    have hsurj : ∀ g : (Fin n → k) →ₗ[RZ Z] (Fin n → k), ∃ y : bSub Z, ψ y = g := by
      intro g
      let y := LinearMap.toMatrix' (g.restrictScalars k)
      have hy : ∀ v, y *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec _ _
      have hyB : y ∈ Bz Z := by
        intro a ha
        apply Matrix.toLin'.injective
        refine LinearMap.ext fun v => ?_
        rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec,
          ← Matrix.mulVec_mulVec, hy, hy]
        exact (g.map_smul (show RZ Z from (⟨a, ha⟩ : Z)) v).symm
      exact ⟨⟨y, hyB⟩, LinearMap.ext fun v => hy v⟩
    have h0 : ψ ⟨x, hx⟩ = 0 := hnd _ fun g => by
      obtain ⟨y, rfl⟩ := hsurj g
      rw [← hψmul x hx y.1 y.2, ← hτx]
      exact H y.1 y.2
    apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, map_zero, LinearMap.zero_apply, ← hψ ⟨x, hx⟩, h0,
      LinearMap.zero_apply]
  · rintro x ⟨hx, m, hm⟩
    rw [hτx x hx]
    apply hnil
    refine ⟨m, LinearMap.ext fun v => ?_⟩
    have hpow : ∀ j : ℕ, (ψ ⟨x, hx⟩ ^ j) v = (x ^ j) *ᵥ v := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        rw [pow_succ', Module.End.mul_apply, ih, hψ, Matrix.mulVec_mulVec, pow_succ']
    rw [hpow, hm, LinearMap.zero_apply, Matrix.zero_mulVec]

theorem traceForm (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    TraceForm k := fun _ Z hZ => traceForm_core Z hZ

end PositivityTheory.RgUd.TP.Loc.Ptf
end
end

namespace PositivityTheory.RgUd.TP.Loc.Final

open PositivityTheory.RgUd.T PositivityTheory.RgUd.TP

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem traceForm : TraceForm k := PositivityTheory.RgUd.TP.Loc.Ptf.traceForm k
theorem unimod : TraceForm k → PositivityTheory.RgUd.T.Desc.SLF.Unimod (k := k) := PositivityTheory.RgUd.TP.Loc.Uni.unimod k
theorem locOff : LocOff k := PositivityTheory.RgUd.TP.Loc.Psplit.locOff_of k (PositivityTheory.RgUd.TP.Loc.Psplit.split k) (PositivityTheory.RgUd.TP.Loc.Psplit.locChi k)
theorem locAll : LocAll k := PositivityTheory.RgUd.TP.Loc.Psplit.locAll_of k (PositivityTheory.RgUd.TP.Loc.Psplit.split k) (PositivityTheory.RgUd.TP.Loc.Psplit.locChi k)
theorem transl : Transl k := PositivityTheory.RgUd.TP.Loc.Ptransl.transl

end PositivityTheory.RgUd.TP.Loc.Final
