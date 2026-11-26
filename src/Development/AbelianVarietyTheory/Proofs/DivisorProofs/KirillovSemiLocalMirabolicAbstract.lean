module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovArchimedeanTotallyComplexMirabolic
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCutOperatorsMirabolicFinitePlaces

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOnMirabolicOfSlicesFinitePlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDisjointUnipotentCellsCoverCompactMiraboli
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactOpenSubgroupSubsetNhdsOne
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactClopenNhdsOneGLFiniteAdeles
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactClopenNhdsOneGLFiniteAdeles
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.GLFinAdeleNhds

theorem totallyDisconnectedSpace_of_injective {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TotallyDisconnectedSpace Y] (f : X → Y) (hf : Continuous f) (hi : Function.Injective f) :
    TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs => ?_⟩
  have h := (hs.image f hf.continuousOn).subsingleton
  exact fun x hx y hy => hi (h (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))

theorem totallyDisconnectedSpace_adicCompletion {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

theorem totallyDisconnectedSpace_Af (E : Type) [Field E] [NumberField E] : TotallyDisconnectedSpace (Af E) := by
  haveI : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), TotallyDisconnectedSpace (v.adicCompletion E) :=
    fun v => totallyDisconnectedSpace_adicCompletion v
  haveI : TotallyDisconnectedSpace
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), [v.adicCompletion E, v.adicCompletionIntegers E]) :=
    totallyDisconnectedSpace_of_injective (fun x v => x v) (continuous_pi fun v => RestrictedProduct.continuous_eval v)
      fun x y h => Subtype.ext (funext fun v => congrFun h v)
  exact inferInstanceAs (TotallyDisconnectedSpace
    (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), [v.adicCompletion E, v.adicCompletionIntegers E]))

theorem exists_isCompact_isClopen (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E)))
    (hB : B ∈ nhds (1 : GL (Fin a) (Af E))) :
    ∃ U : Set (GL (Fin a) (Af E)), IsOpen U ∧ IsCompact U ∧ IsClosed U ∧ 1 ∈ U ∧ U ⊆ B := by
  haveI := totallyDisconnectedSpace_Af E
  haveI : TotallyDisconnectedSpace (Matrix (Fin a) (Fin a) (Af E)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin a → Fin a → Af E))
  haveI : TotallyDisconnectedSpace (GL (Fin a) (Af E)) :=
    totallyDisconnectedSpace_of_injective _ Units.continuous_val Units.val_injective
  haveI : LocallyCompactSpace (GL (Fin a) (Af E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  obtain ⟨K, hK, hKB, hc⟩ := local_compact_nhds hB
  obtain ⟨U, hU, h1, hUK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK
  exact ⟨U, hU.2, hc.of_isClosed_subset hU.1 hUK, hU.1, h1, hUK.trans hKB⟩

end GlobalTheory.GLFinAdeleNhds
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactClopenNhdsOneGLFiniteAdelesStatement
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_compact_clopen_nhds_one_GL_finiteAdeles : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E))), B ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ U : Set (GL (Fin a) (Af E)), IsOpen U ∧ IsCompact U ∧ IsClosed U ∧ 1 ∈ U ∧ U ⊆ B := by
  first | exact @GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen | exact GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen | (intros; apply GlobalTheory.GLFinAdeleNhds.exists_isCompact_isClopen <;> assumption)
end
end

open NumberField MeasureTheory Matrix GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.GLFin

namespace GlobalTheory.GLFinSmall

open Set Filter Pointwise Topology

theorem exists_nhds_mul_subset {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W) : ∃ T ∈ 𝓝 (1 : G), W * T ⊆ W := by
  apply hWc.induction_on (p := fun S ↦ ∃ T ∈ 𝓝 (1 : G), S * T ⊆ W)
    ⟨Set.univ, by simp only [univ_mem, Set.empty_mul, empty_subset, and_self]⟩
    (fun _ _ huv ⟨T, hT, mem⟩ ↦ ⟨T, hT, (mul_subset_mul_right huv).trans mem⟩)
    fun U V ⟨T₁, hT₁, mem1⟩ ⟨T₂, hT₂, mem2⟩ ↦ ⟨T₁ ∩ T₂, inter_mem hT₁ hT₂, by
      rw [union_mul]
      exact union_subset (mul_subset_mul_left inter_subset_left |>.trans mem1)
        (mul_subset_mul_left inter_subset_right |>.trans mem2)⟩
  intro x memW
  have : (x, 1) ∈ (fun p : G × G ↦ p.1 * p.2) ⁻¹' W := by simp [memW]
  rcases isOpen_prod_iff.mp (continuous_mul.isOpen_preimage W hWo) x 1 this with
    ⟨U, V, Uopen, Vopen, xmemU, onememV, prodsub⟩
  have h6 : U * V ⊆ W := mul_subset_iff.mpr (fun _ hx _ hy ↦ prodsub (mk_mem_prod hx hy))
  exact ⟨U ∩ W, ⟨U, Uopen.mem_nhds xmemU, W, fun _ a ↦ a, rfl⟩,
    V, IsOpen.mem_nhds Vopen onememV, fun _ a ↦ h6 ((mul_subset_mul_right inter_subset_left) a)⟩

def rightStab {G : Type} [Group G] (W : Set G) : Subgroup G where
  carrier := {g | ∀ w, w ∈ W ↔ w * g ∈ W}
  one_mem' := by intro w; simp
  mul_mem' := by
    intro g h hg hh w
    rw [hg w, hh (w * g), mul_assoc]
  inv_mem' := by
    intro g hg w
    rw [hg (w * g⁻¹), inv_mul_cancel_right]

theorem exists_compact_open_subgroup_subset {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {W : Set G} (hWc : IsCompact W) (hWo : IsOpen W) (h1 : (1 : G) ∈ W) :
    ∃ U : Subgroup G, IsOpen (U : Set G) ∧ IsCompact (U : Set G) ∧ (U : Set G) ⊆ W := by
  obtain ⟨T, hT, hTW⟩ := exists_nhds_mul_subset hWc hWo
  have hsub : T ∩ T⁻¹ ⊆ (rightStab W : Set G) := by
    intro v hv w
    constructor
    · intro hw; exact hTW (Set.mul_mem_mul hw hv.1)
    · intro hw
      have : w * v * v⁻¹ ∈ W := hTW (Set.mul_mem_mul hw (Set.mem_inv.mp hv.2))
      simpa using this
  have hnhds : (rightStab W : Set G) ∈ 𝓝 (1 : G) :=
    Filter.mem_of_superset (inter_mem hT (inv_mem_nhds_one G hT)) hsub
  have hopen : IsOpen (rightStab W : Set G) := Subgroup.isOpen_of_mem_nhds _ hnhds
  have hW : (rightStab W : Set G) ⊆ W := by
    intro g hg
    have := (hg 1).mp h1
    simpa using this
  refine ⟨rightStab W, hopen, ?_, hW⟩
  exact hWc.of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hopen) hW

end GlobalTheory.GLFinSmall

theorem GlobalTheory.GLFin.exists_compact_open_subgroup_subset_nhds_one :
    ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E))),
      B ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ U : Subgroup (GL (Fin a) (Af E)),
        IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧
          (U : Set (GL (Fin a) (Af E))) ⊆ B := by
  intro E _ _ a B hB
  obtain ⟨W, hWo, hWc, -, h1, hWB⟩ := GlobalTheory.T.exists_compact_clopen_nhds_one_GL_finiteAdeles E a B hB
  obtain ⟨U, hUo, hUc, hUW⟩ := GlobalTheory.GLFinSmall.exists_compact_open_subgroup_subset hWc hWo h1
  exact ⟨U, hUo, hUc, hUW.trans hWB⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDisjointUnipotentCellsCoverCompactMiraboli
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

noncomputable section

namespace GlobalTheory.JSW.MirPatch.Cover

open GlobalTheory.JSW GlobalTheory.JSW.MirPatch Topology

section UT

variable {R R' : Type} [CommRing R] [CommRing R'] {a : ℕ}

def IsUT (M : Matrix (Fin a) (Fin a) R) : Prop :=
  (∀ i j : Fin a, j < i → M i j = 0) ∧ ∀ i, M i i = 1

theorem isUT_one : IsUT (1 : Matrix (Fin a) (Fin a) R) :=
  ⟨fun i j h => Matrix.one_apply_ne (ne_of_gt h), fun i => Matrix.one_apply_eq i⟩

theorem IsUT.mul {M N : Matrix (Fin a) (Fin a) R} (hM : IsUT M) (hN : IsUT N) : IsUT (M * N) := by
  refine ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    rcases lt_or_ge k i with h | h
    · rw [hM.1 i k h, zero_mul]
    · rw [hN.1 k j (lt_of_lt_of_le hij h), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single i]
    · rw [hM.2, hN.2, one_mul]
    · intro k _ hk
      rcases lt_or_gt_of_ne hk with h | h
      · rw [hM.1 i k h, zero_mul]
      · rw [hN.1 k i h, mul_zero]
    · simp

theorem IsUT.map {M : Matrix (Fin a) (Fin a) R} (hM : IsUT M) (f : R →+* R') : IsUT (M.map f) :=
  ⟨fun i j h => by rw [Matrix.map_apply, hM.1 i j h, map_zero], fun i => by rw [Matrix.map_apply, hM.2 i, map_one]⟩

theorem IsUT.inv {g : GL (Fin a) R} (hg : IsUT (g : Matrix (Fin a) (Fin a) R)) :
    IsUT ((g⁻¹ : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) := by
  letI := g.invertible
  have ht : ((g⁻¹ : GL (Fin a) R) : Matrix (Fin a) (Fin a) R).BlockTriangular id := by
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular (b := id) fun i j h => hg.1 i j h
  refine ⟨fun i j h => ht h, fun i => ?_⟩
  have e : ((g⁻¹ : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) * (g : Matrix (Fin a) (Fin a) R) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e2 := congrFun (congrFun e i) i
  rw [Matrix.mul_apply, Finset.sum_eq_single i, hg.2 i, mul_one, Matrix.one_apply_eq] at e2
  · exact e2
  · intro k _ hk
    rcases lt_or_gt_of_ne hk with h | h
    · rw [ht h, zero_mul]
    · rw [hg.1 k i h, mul_zero]
  · simp

end UT

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem mem_NA_iff_isUT (u : GA E a) : u ∈ NA (E := E) (a := a) ↔ IsUT (u : Matrix (Fin a) (Fin a) (Ad E)) := Iff.rfl

theorem NA_mul {u v : GA E a} (hu : u ∈ NA (E := E) (a := a)) (hv : v ∈ NA (E := E) (a := a)) : u * v ∈ NA (E := E) (a := a) := by
  rw [mem_NA_iff_isUT, Units.val_mul]; exact IsUT.mul hu hv

theorem NA_inv {u : GA E a} (hu : u ∈ NA (E := E) (a := a)) : u⁻¹ ∈ NA (E := E) (a := a) := IsUT.inv hu

theorem last_row_mul {m : ℕ} {u : GA E (m + 1)} (hu : u ∈ NA (E := E) (a := (m + 1))) (c : GA E (m + 1)) (j : Fin (m + 1)) :
    ((u * c : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
      (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j := by
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (Fin.last m), hu.2, one_mul]
  · intro k _ hk
    rw [hu.1 _ _ (lt_of_le_of_ne (Fin.le_last k) hk), zero_mul]
  · simp

theorem mem_cell_iff (K : Subgroup (GL (Fin a) (Af E))) (q p : GA E a) :
    p ∈ cell K q ↔ ∃ u ∈ NA (E := E) (a := a), GeneralLinearGroup.map (pFin E) (q⁻¹ * u⁻¹ * p) ∈ K := by
  constructor
  · rintro ⟨u, hu, k, hk, y, rfl⟩
    refine ⟨u, hu, ?_⟩
    have : q⁻¹ * u⁻¹ * (u * q * finGL E a k * infGL E a y) = finGL E a k * infGL E a y := by group
    rw [this, map_mul, pFin_finGL, pFin_infGL, mul_one]; exact hk
  · rintro ⟨u, hu, hk⟩
    refine ⟨u, hu, _, hk, GeneralLinearGroup.map (pInf E) (q⁻¹ * u⁻¹ * p), ?_⟩
    rw [mul_assoc (u * q), ← infGL_comm, infGL_mul_finGL]
    group

theorem isOpen_cell {K : Subgroup (GL (Fin a) (Af E))} (hK : IsOpen (K : Set (GL (Fin a) (Af E)))) (q : GA E a) :
    IsOpen (cell K q) := by
  have e : cell K q = ⋃ u ∈ NA (E := E) (a := a), (fun p => GeneralLinearGroup.map (pFin E) (q⁻¹ * u⁻¹ * p)) ⁻¹' (K : Set _) := by
    ext p; rw [mem_cell_iff]; simp
  rw [e]
  refine isOpen_biUnion fun u _ => hK.preimage ?_
  exact (Continuous.units_map _ (continuous_id.matrix_map (continuous_snd : Continuous (pFin E)))).comp (continuous_const.mul continuous_id)

theorem cell_mono {K K' : Subgroup (GL (Fin a) (Af E))} (h : K ≤ K') (q : GA E a) : cell K q ⊆ cell K' q := by
  rintro p ⟨u, hu, k, hk, y, rfl⟩
  exact ⟨u, hu, k, h hk, y, rfl⟩

theorem cell_subset_of_mem {K : Subgroup (GL (Fin a) (Af E))} {q x : GA E a} (hx : x ∈ cell K q) :
    cell K x ⊆ cell K q := by
  obtain ⟨u', hu', k', hk', y', rfl⟩ := hx
  rintro p ⟨u, hu, k, hk, y, rfl⟩
  refine ⟨u * u', NA_mul hu hu', k' * k, K.mul_mem hk' hk, y' * y, ?_⟩
  rw [map_mul, map_mul]
  have e := infGL_comm (E := E) y' k
  calc u * (u' * q * finGL E a k' * infGL E a y') * finGL E a k * infGL E a y
      = u * u' * q * finGL E a k' * (infGL E a y' * finGL E a k) * infGL E a y := by group
    _ = _ := by rw [e]; group

theorem mem_cell_symm {K : Subgroup (GL (Fin a) (Af E))} {q x : GA E a} (hx : x ∈ cell K q) : q ∈ cell K x := by
  obtain ⟨u, hu, k, hk, y, rfl⟩ := hx
  refine ⟨u⁻¹, NA_inv hu, k⁻¹, K.inv_mem hk, y⁻¹, ?_⟩
  rw [map_inv, map_inv]
  have e := infGL_comm (E := E) y k⁻¹
  calc q = u⁻¹ * (u * q * finGL E a k * infGL E a y) * (infGL E a y)⁻¹ * (finGL E a k)⁻¹ := by group
    _ = u⁻¹ * (u * q * finGL E a k * infGL E a y) * ((infGL E a y)⁻¹ * (finGL E a k)⁻¹) := by group
    _ = _ := by
      rw [← map_inv, ← map_inv, infGL_comm, map_inv, map_inv]; group

theorem cell_eq_of_mem {K : Subgroup (GL (Fin a) (Af E))} {x x' p : GA E a} (h : p ∈ cell K x)
    (h' : p ∈ cell K x') : cell K x = cell K x' :=
  le_antisymm ((cell_subset_of_mem (mem_cell_symm h)).trans (cell_subset_of_mem h'))
    ((cell_subset_of_mem (mem_cell_symm h')).trans (cell_subset_of_mem h))

theorem NA_mul_mem_cell {K : Subgroup (GL (Fin a) (Af E))} {q c u : GA E a} (hu : u ∈ NA (E := E) (a := a)) (hc : c ∈ cell K q) :
    u * c ∈ cell K q := by
  obtain ⟨v, hv, k, hk, y, rfl⟩ := hc
  exact ⟨u * v, NA_mul hu hv, k, hk, y, by group⟩

end GlobalTheory.JSW.MirPatch.Cover

namespace GlobalTheory.JSW.MirPatch.Cover

open GlobalTheory.JSW GlobalTheory.JSW.MirPatch Topology

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]


variable (E) in
def Zset (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : Set (GA E (m + 1)) :=
  {c | (∀ j, (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧
    ∀ w ∉ S, IsUT ((GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) c : GL (Fin (m + 1)) (w.adicCompletion E)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E))}

theorem isClosed_Zset (S : Finset (HeightOneSpectrum (𝓞 E))) (m : ℕ) : IsClosed (Zset E S m) := by
  have hent : ∀ i j : Fin (m + 1), Continuous fun c : GA E (m + 1) => (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) i j :=
    fun i j => (Units.continuous_val (M := Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E))).matrix_elem i j
  have hloc : ∀ (w : HeightOneSpectrum (𝓞 E)) (i j : Fin (m + 1)),
      Continuous fun c : GA E (m + 1) => ((pLoc E w).comp (pFin E)) ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) i j) :=
    fun w i j => ((RestrictedProduct.continuous_eval w).comp continuous_snd).comp (hent i j)
  have e : Zset E S m = (⋂ j, {c : GA E (m + 1) | (c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
        if j = Fin.last m then 1 else 0}) ∩
      ⋂ w, ⋂ (_ : w ∉ S), ((⋂ i, ⋂ j, ⋂ (_ : j < i), {c : GA E (m + 1) |
        ((pLoc E w).comp (pFin E)) ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) i j) = 0}) ∩
        ⋂ i, {c : GA E (m + 1) | ((pLoc E w).comp (pFin E)) ((c : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) i i) = 1}) := by
    ext c
    simp only [Zset, IsUT, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    rfl
  rw [e]
  exact (isClosed_iInter fun j => isClosed_eq (hent _ _) continuous_const).inter
    (isClosed_iInter fun w => isClosed_iInter fun _ => (isClosed_iInter fun i => isClosed_iInter fun j =>
      isClosed_iInter fun _ => isClosed_eq (hloc w i j) continuous_const).inter
        (isClosed_iInter fun i => isClosed_eq (hloc w i i) continuous_const))

theorem mem_Zset_of {S : Finset (HeightOneSpectrum (𝓞 E))} {m : ℕ} {c u : GA E (m + 1)} (hu : u ∈ NA (E := E) (a := (m + 1)))
    (h : u * c ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m)) : c ∈ Zset E S m := by
  refine ⟨fun j => by rw [← last_row_mul hu c j]; exact h.2 j, fun w hw => ?_⟩
  have h1 := h.1 w hw
  rw [map_mul] at h1
  rw [eq_inv_of_mul_eq_one_right h1]
  exact IsUT.inv (g := GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) u) (IsUT.map hu _)

theorem exists_NA_of_mem_Zset {S : Finset (HeightOneSpectrum (𝓞 E))} {m : ℕ} {c : GA E (m + 1)}
    (hc : c ∈ Zset E S m) : ∃ u ∈ NA (E := E) (a := (m + 1)), u * c ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) := by
  classical
  set cf := GeneralLinearGroup.map (pFin E) c
  set L : GL (Fin (m + 1)) (Af E) :=
    (S.toList.map fun w => locGL E (m + 1) w (GeneralLinearGroup.map (pLoc E w) cf)).prod
  have hL : ∀ w, GeneralLinearGroup.map (pLoc E w) L =
      if w ∈ S then GeneralLinearGroup.map (pLoc E w) cf else 1 := by
    intro w
    have key : ∀ l : List (HeightOneSpectrum (𝓞 E)), l.Nodup → GeneralLinearGroup.map (pLoc E w)
        (l.map fun v => locGL E (m + 1) v (GeneralLinearGroup.map (pLoc E v) cf)).prod =
        if w ∈ l then GeneralLinearGroup.map (pLoc E w) cf else 1 := by
      intro l hl
      induction l with
      | nil => simp
      | cons v l ih =>
        rw [List.nodup_cons] at hl
        rw [List.map_cons, List.prod_cons, map_mul, ih hl.2]
        by_cases h : w = v
        · subst h; rw [pLoc_locGL, if_neg hl.1, if_pos List.mem_cons_self, mul_one]
        · rw [pLoc_locGL_of_ne h, one_mul]; simp [h]
    rw [key _ (Finset.nodup_toList _)]; simp
  set k := cf⁻¹ * L
  have hk : ∀ w, GeneralLinearGroup.map (pLoc E w) k =
      if w ∈ S then 1 else (GeneralLinearGroup.map (pLoc E w) cf)⁻¹ := by
    intro w; rw [map_mul, map_inv, hL]; split_ifs <;> simp
  have hkUT : ∀ w, IsUT ((GeneralLinearGroup.map (pLoc E w) k : GL (Fin (m + 1)) (w.adicCompletion E)) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) (w.adicCompletion E)) := by
    intro w; rw [hk]; split_ifs with hw
    · exact isUT_one
    · exact IsUT.inv (hc.2 w hw)
  have huNA : finGL E (m + 1) k ∈ NA (E := E) (a := (m + 1)) := by
    refine ⟨fun i j hij => ad_ext ?_ ?_, fun i => ad_ext ?_ ?_⟩
    · show (GeneralLinearGroup.map (pInf E) (finGL E (m + 1) k) : Matrix _ _ _) i j = pInf E 0
      rw [pInf_finGL, map_zero]; exact Matrix.one_apply_ne (ne_of_gt hij)
    · show (GeneralLinearGroup.map (pFin E) (finGL E (m + 1) k) : Matrix _ _ _) i j = pFin E 0
      rw [pFin_finGL, map_zero]
      exact FiniteAdeleRing.ext _ fun w => (hkUT w).1 i j hij
    · show (GeneralLinearGroup.map (pInf E) (finGL E (m + 1) k) : Matrix _ _ _) i i = pInf E 1
      rw [pInf_finGL, map_one]; exact Matrix.one_apply_eq i
    · show (GeneralLinearGroup.map (pFin E) (finGL E (m + 1) k) : Matrix _ _ _) i i = pFin E 1
      rw [pFin_finGL, map_one]
      exact FiniteAdeleRing.ext _ fun w => (hkUT w).2 i
  refine ⟨_, huNA, fun w hw => ?_, fun j => ?_⟩
  · change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (finGL E (m + 1) k * c)) = 1
    rw [map_mul, pFin_finGL, map_mul, hk, if_neg hw, inv_mul_cancel]
  · rw [last_row_mul huNA]; exact hc.1 j

theorem exists_base {S : Finset (HeightOneSpectrum (𝓞 E))} {m : ℕ} {d : GA E (m + 1)} (hd : d ∈ Zset E S m)
    (V : GA E (m + 1) → Subgroup (GL (Fin (m + 1)) (Af E))) :
    ∃ q, q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) q = 1 ∧ d ∈ cell (V q) q := by
  obtain ⟨u, hu, hm⟩ := exists_NA_of_mem_Zset hd
  set p := u * d with hp
  refine ⟨finGL E (m + 1) (GeneralLinearGroup.map (pFin E) p), ⟨fun w hw => ?_, fun j => ?_⟩, pInf_finGL _, ?_⟩
  · change GeneralLinearGroup.map (pLoc E w) (GeneralLinearGroup.map (pFin E) (finGL E (m + 1) _)) = 1
    rw [pFin_finGL]; exact hm.1 w hw
  · refine ad_ext ?_ ?_
    · show (GeneralLinearGroup.map (pInf E) (finGL E (m + 1) _) : Matrix _ _ _) (Fin.last m) j =
        pInf E (if j = Fin.last m then 1 else 0)
      rw [pInf_finGL]
      split_ifs with h
      · subst h; simp
      · rw [map_zero]; exact Matrix.one_apply_ne (Ne.symm h)
    · show (GeneralLinearGroup.map (pFin E) (finGL E (m + 1) _) : Matrix _ _ _) (Fin.last m) j =
        pFin E (if j = Fin.last m then 1 else 0)
      rw [pFin_finGL]
      show pFin E ((p : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j) = _
      rw [hm.2 j]
  · refine ⟨u⁻¹, NA_inv hu, 1, (V _).one_mem, GeneralLinearGroup.map (pInf E) p, ?_⟩
    rw [map_one, mul_one, mul_assoc, ← infGL_comm, infGL_mul_finGL, hp, inv_mul_cancel_left]

end GlobalTheory.JSW.MirPatch.Cover

namespace GlobalTheory.JSW.MirPatch.Cover

open GlobalTheory.JSW GlobalTheory.JSW.MirPatch Topology

theorem exists_cover : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (C : Set (GA E (m + 1))), IsCompact C → ∀ V : GA E (m + 1) → Subgroup (GL (Fin (m + 1)) (Af E)), (∀ q, IsOpen (V q : Set (GL (Fin (m + 1)) (Af E)))) → ∃ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (R : Finset (GA E (m + 1))) (j : GA E (m + 1) → GA E (m + 1)), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) ∧ IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) ∧ (∀ x ∈ R, j x ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) (j x) = 1 ∧ K ≤ V (j x) ∧ GlobalTheory.JSW.MirPatch.cell K x ⊆ GlobalTheory.JSW.MirPatch.cell (V (j x)) (j x)) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → ∃ x ∈ R, p ∈ GlobalTheory.JSW.MirPatch.cell K x) ∧ (∀ x ∈ R, ∀ x' ∈ R, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), p ∈ GlobalTheory.JSW.MirPatch.cell K x → p ∈ GlobalTheory.JSW.MirPatch.cell K x' → x = x') := by
  intro E _ _ _ m S C hC V hV
  classical
  set D := C ∩ Zset E S m
  have hD : IsCompact D := hC.inter_right (isClosed_Zset S m)
  have hq : ∀ d ∈ D, ∃ q, q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) q = 1 ∧ d ∈ cell (V q) q :=
    fun d hd => exists_base hd.2 V
  choose! q hq using hq
  obtain ⟨t, htD, hcov⟩ := hD.elim_nhds_subcover (fun d => cell (V (q d)) (q d))
    (fun d hd => (isOpen_cell (hV _) _).mem_nhds (hq d hd).2.2)
  have hB : (⋂ d ∈ t, (V (q d) : Set (GL (Fin (m + 1)) (Af E)))) ∈ 𝓝 (1 : GL (Fin (m + 1)) (Af E)) :=
    (isOpen_biInter_finset fun d _ => hV (q d)).mem_nhds (Set.mem_iInter₂.2 fun d _ => (V (q d)).one_mem)
  obtain ⟨K, hKo, hKc, hKB⟩ := GlobalTheory.GLFin.exists_compact_open_subgroup_subset_nhds_one E (m + 1) _ hB
  have hKle : ∀ d ∈ t, K ≤ V (q d) := fun d hd k hk => Set.mem_iInter₂.1 (hKB hk) d hd
  obtain ⟨t2, ht2D, hcov2⟩ := hD.elim_nhds_subcover (fun d => cell K d)
    (fun d _ => (isOpen_cell hKo d).mem_nhds (self_mem_cell K d))
  have hj : ∀ x ∈ t2, ∃ d ∈ t, x ∈ cell (V (q d)) (q d) := fun x hx => by
    simpa using hcov (ht2D x hx)
  choose! dj hdj using hj
  let rep : Set (GA E (m + 1)) → GA E (m + 1) := fun s => if h : ∃ x ∈ t2, cell K x = s then h.choose else 1
  have hrep : ∀ x ∈ t2, rep (cell K x) ∈ t2 ∧ cell K (rep (cell K x)) = cell K x := by
    intro x hx
    have h : ∃ y ∈ t2, cell K y = cell K x := ⟨x, hx, rfl⟩
    simp only [rep, dif_pos h]
    exact h.choose_spec
  refine ⟨K, t2.image fun x => rep (cell K x), fun x => q (dj x), hKo, hKc, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨h1, -⟩ := hrep x0 hx0
    have hd := hdj _ h1
    have hqd := hq _ (htD _ hd.1)
    exact ⟨hqd.1, hqd.2.1, hKle _ hd.1, (cell_mono (hKle _ hd.1) _).trans (cell_subset_of_mem hd.2)⟩
  · rintro p hp ⟨u, hu, hc⟩
    have hcD : u⁻¹ * p ∈ D := ⟨hc, mem_Zset_of (u := u) hu (by rwa [mul_inv_cancel_left])⟩
    obtain ⟨x, hx, hmem⟩ : ∃ x ∈ t2, u⁻¹ * p ∈ cell K x := by simpa using hcov2 hcD
    refine ⟨rep (cell K x), Finset.mem_image_of_mem _ hx, ?_⟩
    rw [(hrep x hx).2]
    have := NA_mul_mem_cell hu hmem
    rwa [mul_inv_cancel_left] at this
  · intro x hx x' hx' p _ h1 h2
    obtain ⟨x0, hx0, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨x0', hx0', rfl⟩ := Finset.mem_image.1 hx'
    have e : cell K x0 = cell K x0' := by
      rw [← (hrep x0 hx0).2, ← (hrep x0' hx0').2]; exact cell_eq_of_mem h1 h2
    simp only [e]

end GlobalTheory.JSW.MirPatch.Cover
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDisjointUnipotentCellsCoverCompactMiraboliStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_disjoint_unipotentCells_cover_compact_mirabolic : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (C : Set (GA E (m + 1))), IsCompact C → ∀ V : GA E (m + 1) → Subgroup (GL (Fin (m + 1)) (Af E)), (∀ q, IsOpen (V q : Set (GL (Fin (m + 1)) (Af E)))) → ∃ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (R : Finset (GA E (m + 1))) (j : GA E (m + 1) → GA E (m + 1)), IsOpen (K : Set (GL (Fin (m + 1)) (Af E))) ∧ IsCompact (K : Set (GL (Fin (m + 1)) (Af E))) ∧ (∀ x ∈ R, j x ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) (j x) = 1 ∧ K ≤ V (j x) ∧ GlobalTheory.JSW.MirPatch.cell K x ⊆ GlobalTheory.JSW.MirPatch.cell (V (j x)) (j x)) ∧ (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), (∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → ∃ x ∈ R, p ∈ GlobalTheory.JSW.MirPatch.cell K x) ∧ (∀ x ∈ R, ∀ x' ∈ R, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), p ∈ GlobalTheory.JSW.MirPatch.cell K x → p ∈ GlobalTheory.JSW.MirPatch.cell K x' → x = x') := by
  first | exact @GlobalTheory.JSW.MirPatch.Cover.exists_cover | exact GlobalTheory.JSW.MirPatch.Cover.exists_cover | (intros; apply GlobalTheory.JSW.MirPatch.Cover.exists_cover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOnDoubleCosetOfEqOnArchimedeanSlice
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOnDoubleCosetOfEqOnArchimedeanSlice
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirPatch

theorem eq_on_cell_of_eq_on_slice : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (V : Subgroup (GL (Fin (m + 1)) (Af E))) (q : GA E (m + 1)), q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → GeneralLinearGroup.map (pInf E) q = 1 → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ V, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ u ∈ V, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), p ∈ GlobalTheory.JSW.MirPatch.cell V q → W p = b p := by
  intro E _ _ _ m S b W V q hq hqi hb hW hbV hWV hsl p hp hpc
  obtain ⟨u, hu, k, hk, y, rfl⟩ := hpc
  have key : u * q * finGL E (m + 1) k * infGL E (m + 1) y = u * ((q * infGL E (m + 1) y) * finGL E (m + 1) k) := by
    rw [mul_assoc (q) (infGL E (m + 1) y), infGL_comm, ← mul_assoc, ← mul_assoc]

  have hy : ∀ j, (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = if j = Fin.last m then 1 else 0 := by
    intro j
    have h1 := congrArg (pInf E) (hp.2 j)
    have hmap : GeneralLinearGroup.map (pInf E) (u * q * finGL E (m + 1) k * infGL E (m + 1) y)
        = GeneralLinearGroup.map (pInf E) u * y := by
      simp [map_mul, hqi]
    have h2 : (GeneralLinearGroup.map (pInf E) (u * q * finGL E (m + 1) k * infGL E (m + 1) y) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j
        = if j = Fin.last m then 1 else 0 := by
      rw [GeneralLinearGroup.map_apply] at *
      simpa [apply_ite (pInf E)] using h1
    rw [hmap] at h2
    rw [← h2]
    simp only [Units.val_mul, Matrix.mul_apply]
    rw [Finset.sum_eq_single (Fin.last m)]
    · have : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) (Fin.last m) = 1 := hu.2 _
      simp [GeneralLinearGroup.map_apply, this]
    · intro l _ hl
      have hlt : l < Fin.last m := lt_of_le_of_ne (Fin.le_last l) hl
      have : (u : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) l = 0 := hu.1 _ _ hlt
      simp [GeneralLinearGroup.map_apply, this]
    · simp
  have hslice : q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) := by
    refine ⟨?_, ?_⟩
    · intro w hw
      rw [map_mul, hq.1 w hw, one_mul]
      exact map_cornerGL_of_zero _ _ (fun _ => map_zero (pLoc E w)) y
    · intro j
      refine ad_ext ?_ ?_
      · have := congrArg (fun g : GL (Fin (m + 1)) (Cinf E) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j)
          (show GeneralLinearGroup.map (pInf E) (q * infGL E (m + 1) y) = y by simp [hqi])
        simp only [GeneralLinearGroup.map_apply] at this
        rw [this, hy j]; split_ifs <;> simp
      · have := congrArg (fun g : GL (Fin (m + 1)) (Af E) => (g : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j)
          (show GeneralLinearGroup.map (pFin E) (q * infGL E (m + 1) y) = GeneralLinearGroup.map (pFin E) q by simp)
        simp only [GeneralLinearGroup.map_apply] at this
        rw [this, hq.2 j]
  rw [key, hW u hu, hb u hu, hWV k hk, hbV k hk, hsl y hslice]

end GlobalTheory.JSW.MirPatch
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOnDoubleCosetOfEqOnArchimedeanSliceStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_on_doubleCoset_of_eq_on_archimedeanSlice : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (V : Subgroup (GL (Fin (m + 1)) (Af E))) (q : GA E (m + 1)), q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → GeneralLinearGroup.map (pInf E) q = 1 → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ V, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ u ∈ V, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), p ∈ GlobalTheory.JSW.MirPatch.cell V q → W p = b p := by
  first | exact @GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice | exact GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice | (intros; apply GlobalTheory.JSW.MirPatch.eq_on_cell_of_eq_on_slice <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOnMirabolicOfSlicesFinitePlaces
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

theorem GlobalTheory.JSW.MirPatch.exists_eq_on_mirS_of_slices : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ) (𝒲 : Submodule ℂ (GA E (m + 1) → ℂ)), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GeneralLinearGroup.map (pInf E) q = 1 → ∃ W ∈ 𝒲, ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∃ W ∈ 𝒲, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p = b p := by
  intro E _ _ _ m S b 𝒲 hb ⟨C, hC, hbC⟩ ⟨Ub, hUbo, hUb⟩ hWe hWt hWU H
  classical
  have hsel : ∀ q : GA E (m + 1), ∃ W ∈ 𝒲, (q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) q = 1 →
      ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) →
        W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) := by
    intro q
    by_cases hq : q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ∧ GeneralLinearGroup.map (pInf E) q = 1
    · obtain ⟨W, hW, h⟩ := H q hq.1 hq.2
      exact ⟨W, hW, fun _ => h⟩
    · exact ⟨0, 𝒲.zero_mem, fun h => absurd h hq⟩
  choose Wq hWq hWqb using hsel
  choose Uq hUqo hUq using fun q => hWU _ (hWq q)
  obtain ⟨K, R, j, hKo, hKc, hR, hcov, huniq⟩ :=
    GlobalTheory.T.exists_disjoint_unipotentCells_cover_compact_mirabolic E m S C hC (fun q => Ub ⊓ Uq q) (fun q => hUbo.inter (hUqo q))
  choose n hh c hhS hcutEq using GlobalTheory.T.exists_cutOperators_mirabolic_finitePlaces E m S K hKo hKc
  refine ⟨∑ x ∈ R, ∑ i, c x i • (fun g => Wq (j x) (g * hh x i)), ?_, ?_⟩
  · exact 𝒲.sum_mem fun x _ => 𝒲.sum_mem fun i _ => 𝒲.smul_mem _ (hWt _ (hWq _) _ (hhS x i))
  · intro p hp
    have e1 : (∑ x ∈ R, ∑ i, c x i • (fun g => Wq (j x) (g * hh x i))) p =
        ∑ x ∈ R, (GlobalTheory.JSW.MirPatch.cell K x).indicator (Wq (j x)) p := by
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun x hx => ?_
      refine hcutEq x (Wq (j x)) (hWe _ (hWq _)) (fun u hu g => hUq _ u ((hR x hx).2.2.1 hu).2 g) p hp
    have e2 : ∀ x ∈ R, (GlobalTheory.JSW.MirPatch.cell K x).indicator (Wq (j x)) p =
        (GlobalTheory.JSW.MirPatch.cell K x).indicator (fun _ => b p) p := by
      intro x hx
      by_cases hpx : p ∈ GlobalTheory.JSW.MirPatch.cell K x
      · rw [Set.indicator_of_mem hpx, Set.indicator_of_mem hpx]
        obtain ⟨hj1, hj2, -, hj4⟩ := hR x hx
        exact GlobalTheory.T.eq_on_doubleCoset_of_eq_on_archimedeanSlice E m S b (Wq (j x)) (Ub ⊓ Uq (j x)) (j x) hj1 hj2 hb (hWe _ (hWq _))
          (fun u hu g => hUb u hu.1 g) (fun u hu g => hUq _ u hu.2 g) (hWqb _ ⟨hj1, hj2⟩) p hp (hj4 hpx)
      · rw [Set.indicator_of_notMem hpx, Set.indicator_of_notMem hpx]
    rw [e1, Finset.sum_congr rfl e2]
    by_cases hbp : b p = 0
    · rw [hbp]; simp
    · obtain ⟨x0, hx0, hpx0⟩ := hcov p hp (hbC p hp hbp)
      rw [Finset.sum_eq_single x0 (fun x hx hne => Set.indicator_of_notMem
        (fun hpx => hne (huniq x hx x0 hx0 p hp hpx hpx0)) _) (fun h => absurd hx0 h),
        Set.indicator_of_mem hpx0]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqOnMirabolicOfSlicesFinitePlacesStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_eq_on_mirabolic_of_slices_finitePlaces : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ) (𝒲 : Submodule ℂ (GA E (m + 1) → ℂ)), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∀ q ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GeneralLinearGroup.map (pInf E) q = 1 → ∃ W ∈ 𝒲, ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y)) → ∃ W ∈ 𝒲, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p = b p := by
  first | (exact @GlobalTheory.JSW.MirPatch.exists_eq_on_mirS_of_slices) | (exact GlobalTheory.JSW.MirPatch.exists_eq_on_mirS_of_slices) | (intros; apply GlobalTheory.JSW.MirPatch.exists_eq_on_mirS_of_slices  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalKirillovArchimedeanKernelComplexPlaces
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalKirillovArchimedeanKernelComplexPlaces
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
open scoped FourierTransform ContDiff

noncomputable section

namespace GlobalTheory.JSW.KirArchTransfer

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem continuous_pInf_here : Continuous (pInf E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      ((continuous_apply w).comp continuous_fst)

theorem continuous_map_pInf_here :
    Continuous (GeneralLinearGroup.map (pInf E) : GA E a → GL (Fin a) (Cinf E)) :=
  Continuous.units_map _ (continuous_id.matrix_map continuous_pInf_here)

theorem ent {R : Type} [CommRing R] (p : Ad E →+* R) (g : GA E a) (i j : Fin a) :
    ((GeneralLinearGroup.map p g : GL (Fin a) R) : Matrix (Fin a) (Fin a) R) i j = p ((g : Matrix (Fin a) (Fin a) (Ad E)) i j) :=
  rfl

theorem pInf_sInf (x : Cinf E) : pInf E (sInf E x) = x := (infEq E).symm_apply_apply x

theorem pFin_sInf (x : Cinf E) : pFin E (sInf E x) = 0 := rfl

theorem eq_finGL {q : GA E a} (hq : GeneralLinearGroup.map (pInf E) q = 1) :
    q = finGL E a (GeneralLinearGroup.map (pFin E) q) := by
  have h := infGL_mul_finGL q
  rw [hq, map_one, one_mul] at h
  exact h.symm

theorem comm_infGL {q : GA E a} (hq : GeneralLinearGroup.map (pInf E) q = 1) (y : GL (Fin a) (Cinf E)) :
    q * infGL E a y = infGL E a y * q := by
  rw [eq_finGL hq]
  exact (infGL_comm y _).symm

theorem infGL_apply_of_ne (y : GL (Fin a) (Cinf E)) {i j : Fin a} (h : i ≠ j) :
    (infGL E a y : Matrix (Fin a) (Fin a) (Ad E)) i j = sInf E ((y : Matrix (Fin a) (Fin a) (Cinf E)) i j) := by
  refine ad_ext ?_ ?_
  · rw [← ent, pInf_infGL, pInf_sInf]
  · rw [← ent, pFin_infGL, pFin_sInf]
    simp [Matrix.one_apply, h]

theorem infGL_mem_NA {u : GL (Fin a) (Cinf E)} (hu : u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin a)) :
    infGL E a u ∈ GlobalTheory.JSW.NA (E := E) (a := a) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB (Cinf E)).1 hu
  refine ⟨fun i j hji => ?_, fun i => ?_⟩
  · refine ad_ext ?_ ?_
    · rw [map_zero, ← ent, pInf_infGL]; exact h1 i j hji
    · rw [map_zero, ← ent, pFin_infGL]; simp [Matrix.one_apply, hji.ne']
  · refine ad_ext ?_ ?_
    · rw [map_one, ← ent, pInf_infGL]; exact h2 i
    · rw [map_one, ← ent, pFin_infGL]; simp

theorem psiN_infGL (u : GL (Fin a) (Cinf E)) :
    GlobalTheory.JSW.psiN (infGL E a u) = (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) := by
  have hs : GlobalTheory.Whittaker.superDiag (infGL E a u) = sInf E (GlobalTheory.Whittaker.superDiag u) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalTheory.Whittaker.superDiag, map_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j hj => ?_
    have hij : i ≠ j := by
      intro e; subst e; simp at hj
    exact infGL_apply_of_ne u hij
  have h := GlobalTheory.ThetaPoisson.adelicChar_sInf_sum (E := E) (n := 1) (fun _ => GlobalTheory.Whittaker.superDiag u) (fun _ => 1)
  simp only [Fin.sum_univ_one, mul_one, Pi.one_apply] at h
  rw [GlobalTheory.JSW.psiN, hs, h]

theorem map_pInf_mem_unipB {u : GA E a} (hu : u ∈ GlobalTheory.JSW.NA (E := E) (a := a)) :
    GeneralLinearGroup.map (pInf E) u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin a) := by
  refine (GlobalTheory.SmGL.mem_unipB (Cinf E)).2 ⟨fun i j hji => ?_, fun i => ?_⟩
  · rw [ent, hu.1 i j hji, map_zero]
  · rw [ent, hu.2 i, map_one]

theorem ad_eq_ite_iff (x : Ad E) (c : Prop) [Decidable c] :
    x = (if c then 1 else 0) ↔ pInf E x = (if c then 1 else 0) ∧ pFin E x = (if c then 1 else 0) := by
  refine ⟨fun h => ?_, fun h => ad_ext ?_ ?_⟩
  · subst h; split_ifs <;> simp
  · rw [h.1]; split_ifs <;> simp
  · rw [h.2]; split_ifs <;> simp

theorem mem_mirS_iff {m : ℕ} (S : Finset (HeightOneSpectrum (𝓞 E))) {q : GA E (m + 1)}
    (hq : GeneralLinearGroup.map (pInf E) q = 1) (y : GL (Fin (m + 1)) (Cinf E)) :
    q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ↔
      (q ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ∧ ∀ j, ((GeneralLinearGroup.map (pFin E) q : GL (Fin (m + 1)) (Af E)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E)) (Fin.last m) j = if j = Fin.last m then 1 else 0) ∧
      y ∈ GlobalTheory.JSW.mirSet (Cinf E) m := by
  have hsup : ∀ w : HeightOneSpectrum (𝓞 E),
      GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) (infGL E (m + 1) y) = 1 :=
    fun w => map_cornerGL_of_zero _ _ (fun _ => map_zero (pLoc E w)) y
  have hI : GeneralLinearGroup.map (pInf E) (q * infGL E (m + 1) y) = y := by
    rw [map_mul, hq, one_mul, pInf_infGL]
  have hF : GeneralLinearGroup.map (pFin E) (q * infGL E (m + 1) y) = GeneralLinearGroup.map (pFin E) q := by
    rw [map_mul, pFin_infGL, mul_one]
  have hrow : ∀ j, ((q * infGL E (m + 1) y : GA E (m + 1)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Ad E)) (Fin.last m) j =
      (if j = Fin.last m then 1 else 0) ↔
      (y : Matrix (Fin (m + 1)) (Fin (m + 1)) (Cinf E)) (Fin.last m) j = (if j = Fin.last m then 1 else 0) ∧
      ((GeneralLinearGroup.map (pFin E) q : GL (Fin (m + 1)) (Af E)) : Matrix (Fin (m + 1)) (Fin (m + 1)) (Af E))
        (Fin.last m) j = (if j = Fin.last m then 1 else 0) := by
    intro j
    rw [ad_eq_ite_iff, ← ent, ← ent, hI, hF]
  have hS : q * infGL E (m + 1) y ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S ↔ q ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
    refine forall_congr' fun w => imp_congr_right fun _ => ?_
    rw [map_mul, hsup, mul_one]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨⟨hS.1 h1, fun j => ((hrow j).1 (h2 j)).2⟩, fun j => ((hrow j).1 (h2 j)).1⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨hS.2 h1, fun j => (hrow j).2 ⟨h3 j, h2 j⟩⟩

end GlobalTheory.JSW.KirArchTransfer

namespace GlobalTheory.JSW.KirArchTransfer

theorem kirillov_arch : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (q : GA E (m + 1)), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b q) (invSet E (m + 1)) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (q * infGL E (m + 1) y)) → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (q * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → GeneralLinearGroup.map (pInf E) q = 1 → W q ≠ 0 → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ ∧ ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → GlobalTheory.JSW.kerInf ν k γ W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y) := by
  intro E _ _ _ m S b W q hbe hbC hbs hWe hWc hWg hq hWq
  classical
  by_cases hne : ∃ y₀ : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y₀ ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m)
  · obtain ⟨y₀, hy₀⟩ := hne
    have hP := ((mem_mirS_iff S hq y₀).1 hy₀).1
    have hiff : ∀ y, q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) ↔ y ∈ GlobalTheory.JSW.mirSet (Cinf E) m :=
      fun y => (mem_mirS_iff S hq y).trans ⟨fun h => h.2, fun h => ⟨hP, h⟩⟩
    have heq : ∀ F : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, F (u * g) = GlobalTheory.JSW.psiN u * F g) →
        ∀ u ∈ GlobalTheory.SmGL.unipB (Cinf E) (Fin (m + 1)), ∀ y,
          F (q * infGL E (m + 1) (u * y)) =
            (𝐞 (-∑ w, 2 * (GlobalTheory.Whittaker.superDiag u w).re) : ℂ) * F (q * infGL E (m + 1) y) := by
      intro F hF u hu y
      rw [map_mul, ← mul_assoc, comm_infGL hq u, mul_assoc, hF _ (infGL_mem_NA hu), psiN_infGL]
    obtain ⟨C, hC, hCp⟩ := hbC
    obtain ⟨X, _, ν, _, k, γ, hk, hK⟩ := GlobalTheory.T.kirillov_archimedean_totallyComplex_mirabolic E m (fun y => b (q * infGL E (m + 1) y))
      (fun y => W (q * infGL E (m + 1) y)) (heq b hbe) ⟨chart b q, hbs, fun y => chart_val b q y⟩
      ⟨GeneralLinearGroup.map (pInf E) '' C, hC.image continuous_map_pInf_here, fun y hy hb0 => by
        obtain ⟨u, hu, hu'⟩ := hCp _ ((hiff y).2 hy) hb0
        refine ⟨GeneralLinearGroup.map (pInf E) u, map_pInf_mem_unipB hu, _, hu', ?_⟩
        rw [map_mul, map_inv, map_mul, hq, one_mul, pInf_infGL]⟩
      (heq W hWe) hWc hWg (by simpa using hWq)
    refine ⟨X, inferInstance, ν, inferInstance, k, γ, hk, fun y hy => ?_⟩
    rw [← hK y ((hiff y).1 hy)]
    simp only [GlobalTheory.JSW.kerInf]
    congr 1
    funext x
    rw [map_mul, mul_assoc]
  · exact ⟨Unit, inferInstance, Measure.dirac (), inferInstance, fun _ => 1, fun _ => 1, GlobalTheory.JSW.isRapidInf_dirac 1,
      fun y hy => (hne ⟨y, hy⟩).elim⟩

end GlobalTheory.JSW.KirArchTransfer
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiLocalKirillovArchimedeanKernelComplexPlacesStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semiLocal_kirillov_archimedean_kernel_complexPlaces : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b W : GA E (m + 1) → ℂ) (q : GA E (m + 1)), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b q) (invSet E (m + 1)) → (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (q * infGL E (m + 1) y)) → (∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (q * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → GeneralLinearGroup.map (pInf E) q = 1 → W q ≠ 0 → ∃ (X : Type) (_ : MeasurableSpace X) (ν : Measure X) (_ : SFinite ν) (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ ∧ ∀ y : GL (Fin (m + 1)) (Cinf E), q * infGL E (m + 1) y ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m) → GlobalTheory.JSW.kerInf ν k γ W (q * infGL E (m + 1) y) = b (q * infGL E (m + 1) y) := by
  first | exact @GlobalTheory.JSW.KirArchTransfer.kirillov_arch | exact GlobalTheory.JSW.KirArchTransfer.kirillov_arch | (intros; apply GlobalTheory.JSW.KirArchTransfer.kirillov_arch <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemiLocalMirabolicAbstract
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory

namespace GlobalTheory.JSW.MirSemi


set_option maxHeartbeats 1000000 in
theorem kirillov_semiLocal : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b g) (invSet E (m + 1))) → ∀ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∃ W ∈ 𝒲, ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p ≠ 0) → ∃ W ∈ 𝒲, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p = b p := by
  intro E _ _ _ m S b hb hC hU hsm 𝒲 h1 h2 h3 h4 h5 hne
  obtain ⟨W₀, hW₀, p₀, hp₀, hne₀⟩ := hne
  refine GlobalTheory.T.exists_eq_on_mirabolic_of_slices_finitePlaces E m S b 𝒲 hb hC hU h1 h2 h5 fun q hq hq1 => ?_
  have hh : q⁻¹ * p₀ ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S := by
    intro w hw
    rw [map_mul, map_inv, hq.1 w hw, hp₀.1 w hw, inv_one, one_mul]
  have hW' := h2 W₀ hW₀ _ hh
  have hq0 : (fun g => W₀ (g * (q⁻¹ * p₀))) q ≠ 0 := by
    simpa [← mul_assoc] using hne₀
  obtain ⟨X, _, ν, _, k, γ, hk, hK⟩ :=
    GlobalTheory.T.semiLocal_kirillov_archimedean_kernel_complexPlaces E m S b _ q hb hC (hsm q) (h1 _ hW') (h4 _ hW' q).1 (h4 _ hW' q).2 hq1 hq0
  exact ⟨_, h3 _ hW' X ν k γ hk, hK⟩

end GlobalTheory.JSW.MirSemi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemiLocalMirabolicAbstractStatement
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kirillov_semiLocal_mirabolic_abstract : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (chart b g) (invSet E (m + 1))) → ∀ 𝒲 : Submodule ℂ (GA E (m + 1) → ℂ), (∀ W ∈ 𝒲, ∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ W ∈ 𝒲, ∀ h ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, (fun g => W (g * h)) ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ (X : Type) [MeasurableSpace X] (ν : Measure X) [SFinite ν] (k : X → ℂ) (γ : X → GL (Fin (m + 1)) (Cinf E)), GlobalTheory.JSW.IsRapidInf ν k γ → GlobalTheory.JSW.kerInf ν k γ W ∈ 𝒲) → (∀ W ∈ 𝒲, ∀ g, Continuous (fun y : GL (Fin (m + 1)) (Cinf E) => W (g * infGL E (m + 1) y)) ∧ ∃ (C : ℝ) (N : ℕ), ∀ y, ‖W (g * infGL E (m + 1) y)‖ ≤ C * height y ^ N) → (∀ W ∈ 𝒲, ∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, W (g * finGL E (m + 1) u) = W g) → (∃ W ∈ 𝒲, ∃ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p ≠ 0) → ∃ W ∈ 𝒲, ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), W p = b p := by
  first | (exact @GlobalTheory.JSW.MirSemi.kirillov_semiLocal) | (exact GlobalTheory.JSW.MirSemi.kirillov_semiLocal) | (intros; apply GlobalTheory.JSW.MirSemi.kirillov_semiLocal  <;> assumption)
end
