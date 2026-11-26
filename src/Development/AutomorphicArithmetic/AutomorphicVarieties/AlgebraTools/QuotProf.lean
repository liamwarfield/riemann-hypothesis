module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDefs
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.IsQuasiRegularSeqSelfIffLocalizationMaximal

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.QuotProf
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.totallyDisconnected_quot :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] (K : Subgroup G) [K.Normal], IsClosed (K : Set G) →
      TotallyDisconnectedSpace (G ⧸ K) ∧ (∀ g : G, (∀ O : OpenNormalSubgroup G, g ∈ K ⊔ O.toSubgroup) → g ∈ K) := by
  intro G _ _ _ _ _ N _ hN
  refine ⟨?_, fun x hx => ?_⟩
  · rw [totallyDisconnectedSpace_iff_connectedComponent_one]
    refine Set.eq_singleton_iff_unique_mem.2 ⟨mem_connectedComponent, fun y hy => ?_⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    by_contra hx
    have hx' : x ∉ N := fun h => hx ((QuotientGroup.eq_one_iff x).2 h)
    have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
    let V : Subgroup (G ⧸ N) := U.toSubgroup.map (QuotientGroup.mk' N)
    have hVo : IsOpen (V : Set (G ⧸ N)) := QuotientGroup.isOpenMap_coe _ U.isOpen'
    have hV : IsClopen (V : Set (G ⧸ N)) := ⟨V.isClosed_of_isOpen hVo, hVo⟩
    obtain ⟨u, hu, hux⟩ := hV.connectedComponent_subset V.one_mem hy
    exact hU (U.toSubgroup.inv_mem hu) (QuotientGroup.eq.1 hux)
  · by_contra hx'
    have ho : IsOpen {g : G | g * x ∉ N} := hN.isOpen_compl.preimage (continuous_mul_const x)
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one ho (by simpa using hx')
    have h := hx U
    rw [sup_comm] at h
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp h
    refine hU (U.toSubgroup.inv_mem hy) ?_
    rw [← hyz]
    simpa using hz
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.SubgroupQuot
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

theorem UpperTheory.V.AlgebraTools.TopFG.subgroup_quot :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G], TopFG G →
      (∀ H : Subgroup G, IsOpen (H : Set G) → TopFG H) ∧
      (∀ (Z : Type) [Group Z] [TopologicalSpace Z] (f : G →* Z), Continuous f → Function.Surjective f → TopFG Z) := by
  intro G _ _ _ _ hG
  obtain ⟨s, hs, hden⟩ := hG
  refine ⟨?_, ?_⟩
  · intro H hH
    haveI : Finite (G ⧸ H) := H.quotient_finite_of_isOpen hH
    haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    set D := Subgroup.closure s with hD
    haveI : Finite s := hs
    haveI : Group.FG D := inferInstance
    haveI : (H.subgroupOf D).FiniteIndex := inferInstance
    have hfg : Group.FG (H.subgroupOf D) := inferInstance
    obtain ⟨t, ht, htf⟩ := Group.fg_iff.mp hfg
    let φ : H.subgroupOf D →* H :=
      (D.subtype.comp (H.subgroupOf D).subtype).codRestrict H (fun x => x.2)
    refine ⟨φ '' t, htf.image _, ?_⟩
    unfold TopGen
    rw [← MonoidHom.map_closure, ht, ← MonoidHom.range_eq_map]
    rw [dense_iff_inter_open]
    intro U hU hUne
    have hVo : IsOpen ((Subtype.val : H → G) '' U) := hH.isOpenMap_subtype_val U hU
    obtain ⟨x, ⟨y, hyU, rfl⟩, hxD⟩ := hden.inter_open_nonempty _ hVo (hUne.image _)
    refine ⟨y, hyU, ⟨⟨y.1, hxD⟩, y.2⟩, ?_⟩
    rfl
  · intro Z _ _ f hf hsurj
    refine ⟨f '' s, hs.image _, ?_⟩
    unfold TopGen at hden ⊢
    rw [← MonoidHom.map_closure, Subgroup.coe_map]
    exact hsurj.denseRange.dense_image hf hden
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UltraDefs
noncomputable section

open Filter

namespace UpperTheory.V.AlgebraTools

section ULim

variable {ι R : Type} [CommRing R] (F : Filter ι) (I : ℕ → Ideal R)
  (M : ι → Type) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]

def uNull : Submodule R (∀ i, M i) where
  carrier := {p | ∀ j, ∀ᶠ i in F, p i ∈ (I j • ⊤ : Submodule R (M i))}
  add_mem' ha hb j := ((ha j).and (hb j)).mono fun _ h => add_mem h.1 h.2
  zero_mem' _ := Eventually.of_forall fun _ => zero_mem _
  smul_mem' c _ h j := (h j).mono fun _ h => Submodule.smul_mem _ c h


abbrev ULim : Type := (∀ i, M i) ⧸ uNull F I M

def ULim.mk : (∀ i, M i) →ₗ[R] ULim F I M := (uNull F I M).mkQ

theorem ULim.mk_surjective : Function.Surjective (ULim.mk F I M) := Submodule.mkQ_surjective _

variable {F I M} in
theorem ULim.mk_eq_zero {p : ∀ i, M i} :
    ULim.mk F I M p = 0 ↔ ∀ j, ∀ᶠ i in F, p i ∈ (I j • ⊤ : Submodule R (M i)) := by
  show (uNull F I M).mkQ p = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  rfl


variable {I M} in
def ULim.map {I' : ℕ → Ideal R} {M' : ι → Type} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
    (h : ∀ j, I j ≤ I' j) (f : ∀ i, M i →ₗ[R] M' i) : ULim F I M →ₗ[R] ULim F I' M' :=
  Submodule.mapQ _ _ (LinearMap.pi fun i => f i ∘ₗ LinearMap.proj i) fun p hp j =>
    (hp j).mono fun i hi => by
      have h1 : f i (p i) ∈ Submodule.map (f i) (I j • ⊤ : Submodule R (M i)) := ⟨_, hi, rfl⟩
      rw [Submodule.map_smul''] at h1
      exact Submodule.smul_mono (h j) le_top h1

variable {I M} in
theorem ULim.map_mk {I' : ℕ → Ideal R} {M' : ι → Type} [∀ i, AddCommGroup (M' i)] [∀ i, Module R (M' i)]
    (h : ∀ j, I j ≤ I' j) (f : ∀ i, M i →ₗ[R] M' i) (p : ∀ i, M i) :
    ULim.map F h f (ULim.mk F I M p) = ULim.mk F I' M' fun i => f i (p i) := rfl

def ULim.scal (r : ι → R) : ULim F I M →ₗ[R] ULim F I M :=
  ULim.map F (fun _ => le_rfl) fun i => r i • LinearMap.id



end ULim

section QReg

variable {R : Type} [CommRing R] {σ : Type} [Finite σ]

def QRegAt (M : Type) [AddCommGroup M] [Module R M] (y : σ → R) (J : Ideal R) (a : ℕ) : Prop :=
  ∀ c : GlobalTheory.MonoDeg σ a → M,
    ∑ α, GlobalTheory.monoVal y α.1 • c α ∈ ((Ideal.span (Set.range y) ^ (a + 1) ⊔ J) • ⊤ : Submodule R M) →
      ∀ α, c α ∈ ((Ideal.span (Set.range y) ⊔ J) • ⊤ : Submodule R M)

theorem isQuasiRegularSeq_iff_qRegAt (M : Type) [AddCommGroup M] [Module R M] (y : σ → R) :
    GlobalTheory.IsQuasiRegularSeq M y ↔ ∀ a, QRegAt M y ⊥ a := by
  unfold GlobalTheory.IsQuasiRegularSeq QRegAt
  simp only [sup_bot_eq]

end QReg

end UpperTheory.V.AlgebraTools
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCplMap
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.IsCplAt.map_pow_eq :
    ∀ (R : Type) [CommRing R] (p : Ideal R) (B : Type) [CommRing B] [IsLocalRing B] [Algebra R B], IsCplAt R p B → ∀ n : ℕ, (p ^ n).map (algebraMap R B) = maximalIdeal B ^ n := by
  intro R _ p B _ _ _ h n
  have hnoeth := h.noeth
  have hle : p.map (algebraMap R B) ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, h.comap_eq]
  have heq : p.map (algebraMap R B) = maximalIdeal B := by
    refine le_antisymm hle ?_
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (IsNoetherian.noetherian _)
      (IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top).ge
    intro b hb
    obtain ⟨a, s, hs, hsa⟩ := h.dense 2 b
    have hsu : IsUnit (algebraMap R B s) := by
      by_contra hn
      apply hs
      rw [← h.comap_eq, Ideal.mem_comap]
      exact (IsLocalRing.mem_maximalIdeal _).mpr hn
    have hm2 : maximalIdeal B ^ 2 ≤ maximalIdeal B := Ideal.pow_le_self two_ne_zero
    have ha : a ∈ p := by
      rw [← h.comap_eq, Ideal.mem_comap]
      have : algebraMap R B a = algebraMap R B s * b - (algebraMap R B s * b - algebraMap R B a) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ hb) (hm2 hsa)
    obtain ⟨u, hu⟩ := hsu
    have hb' : b = (↑u⁻¹ : B) * (algebraMap R B a + (algebraMap R B s * b - algebraMap R B a)) := by
      rw [← hu]
      simp
    rw [hb', smul_eq_mul, ← pow_two]
    apply Ideal.mul_mem_left
    exact add_mem (Ideal.mem_sup_left (Ideal.mem_map_of_mem _ ha)) (Ideal.mem_sup_right hsa)
  rw [Ideal.map_pow, heq]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.EqOneOfStrictMono
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem swap_lt {n : ℕ} {a c : Fin n} (h : a.val + 1 = c.val) {x y : Fin n} (hxy : x < y)
    (hne : ¬ (x = a ∧ y = c)) : swap a c x < swap a c y := by
  have key : ∀ z : Fin n, (swap a c z).val = if z.val = a.val then c.val else if z.val = c.val then a.val else z.val := by
    intro z
    rw [swap_apply_def]
    by_cases h1 : z = a
    · subst h1
      simp
    · by_cases h2 : z = c
      · subst h2
        have h1' : z.val ≠ a.val := fun e => h1 (Fin.ext e)
        simp [h1, h1']
      · have h1' : z.val ≠ a.val := fun e => h1 (Fin.ext e)
        have h2' : z.val ≠ c.val := fun e => h2 (Fin.ext e)
        simp [h1, h2, h1', h2']
  rw [Fin.lt_def, key, key]
  rw [Fin.lt_def] at hxy
  have hne' : ¬ (x.val = a.val ∧ y.val = c.val) := fun e => hne ⟨Fin.ext e.1, Fin.ext e.2⟩
  split_ifs <;> omega

private theorem mem_invSet {n : ℕ} (w : Perm (Fin n)) (p : Fin n × Fin n) :
    p ∈ invSet w ↔ p.1 < p.2 ∧ w⁻¹ p.2 < w⁻¹ p.1 := by
  simp [invSet, pairs]

private theorem eq_one_of_strictMono {n : ℕ} (w : Perm (Fin n)) (h : StrictMono w) : w = 1 := by
  exact Equiv.ext fun x => congrFun h.eq_id x

private theorem invSet_rev (n : ℕ) : invSet (Fin.revPerm : Perm (Fin n)) = pairs n := by
  ext ⟨x, y⟩
  rw [mem_invSet]
  have hinv : ∀ z : Fin n, (Fin.revPerm : Perm (Fin n))⁻¹ z = z.rev := by
    intro z
    rw [Perm.inv_eq_iff_eq, Fin.revPerm_apply, Fin.rev_rev]
  simp only [hinv, Fin.rev_lt_rev]
  simp only [pairs, Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

theorem UpperTheory.V.AlgebraTools.hkInv :
    ∀ n : ℕ, (∀ (a c : Fin n), a.val + 1 = c.val → ∀ w : Perm (Fin n), w⁻¹ a < w⁻¹ c →
        invSet (swap a c * w) = insert (a, c) ((invSet w).image fun p => (swap a c p.1, swap a c p.2)) ∧
        (a, c) ∉ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) ∧ invN (swap a c * w) = invN w + 1) ∧
      (∀ w : Perm (Fin n), w ≠ 1 → ∃ a c : Fin n, a.val + 1 = c.val ∧ w⁻¹ c < w⁻¹ a) ∧
      invSet (1 : Perm (Fin n)) = ∅ ∧ invSet (Fin.revPerm : Perm (Fin n)) = pairs n ∧
      (∀ w : Perm (Fin n), w ≠ Fin.revPerm → invN w < invN (Fin.revPerm : Perm (Fin n))) := by
  intro n
  refine ⟨?_, ?_, ?_, invSet_rev n, ?_⟩
  · intro a c hac w hw
    have hlt : a < c := by
      rw [Fin.lt_def]
      omega
    have hff : ∀ p : Fin n × Fin n, (swap a c (swap a c p.1), swap a c (swap a c p.2)) = p := by
      intro p
      simp
    have hmemimg : ∀ q : Fin n × Fin n, q ∈ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) ↔
        (swap a c q.1, swap a c q.2) ∈ invSet w := by
      intro q
      rw [Finset.mem_image]
      constructor
      · rintro ⟨p, hp, rfl⟩
        rwa [hff]
      · intro hq
        exact ⟨_, hq, hff q⟩
    have hnot : (a, c) ∉ (invSet w).image (fun p => (swap a c p.1, swap a c p.2)) := by
      rw [hmemimg, mem_invSet]
      simp only [swap_apply_left, swap_apply_right]
      exact fun h => absurd h.1 (lt_asymm hlt)
    have heq : invSet (swap a c * w) = insert (a, c) ((invSet w).image (fun p => (swap a c p.1, swap a c p.2))) := by
      ext ⟨x, y⟩
      rw [Finset.mem_insert, hmemimg, mem_invSet, mem_invSet]
      simp only [mul_inv_rev, swap_inv, Perm.mul_apply, Prod.mk.injEq]
      by_cases hp : x = a ∧ y = c
      · obtain ⟨rfl, rfl⟩ := hp
        simp only [swap_apply_left, swap_apply_right]
        exact ⟨fun _ => Or.inl (by simp), fun _ => ⟨hlt, hw⟩⟩
      · constructor
        · rintro ⟨hxy, hA⟩
          exact Or.inr ⟨swap_lt hac hxy hp, hA⟩
        · rintro (h | ⟨hs, hA⟩)
          · exact absurd h hp
          · refine ⟨?_, hA⟩
            rcases lt_trichotomy x y with h | h | h
            · exact h
            · subst h
              exact absurd hs (lt_irrefl _)
            · by_cases hq : y = a ∧ x = c
              · obtain ⟨rfl, rfl⟩ := hq
                simp only [swap_apply_left, swap_apply_right] at hA
                exact absurd hA (lt_asymm hw)
              · exact absurd (swap_lt hac h hq) (lt_asymm hs)
    refine ⟨heq, hnot, ?_⟩
    unfold invN
    rw [heq, Finset.card_insert_of_notMem hnot, Finset.card_image_of_injective]
    intro p q hpq
    have := congrArg (fun r : Fin n × Fin n => (swap a c r.1, swap a c r.2)) hpq
    simp only [hff] at this
    exact this
  · intro w hw
    by_contra hcon
    push_neg at hcon
    apply hw
    have hadj : ∀ a c : Fin n, a.val + 1 = c.val → w⁻¹ a < w⁻¹ c := by
      intro a c h
      refine lt_of_le_of_ne (hcon a c h) ?_
      intro h'
      have := w⁻¹.injective h'
      rw [this] at h
      omega
    have key : ∀ k : ℕ, ∀ i j : Fin n, j.val = i.val + k + 1 → w⁻¹ i < w⁻¹ j := by
      intro k
      induction k with
      | zero =>
        intro i j h
        exact hadj i j (by omega)
      | succ k ih =>
        intro i j h
        have hj := j.isLt
        have hm : i.val + k + 1 < n := by omega
        exact lt_trans (ih i ⟨i.val + k + 1, hm⟩ rfl) (hadj _ _ (by show i.val + k + 1 + 1 = j.val; omega))
    have hsm : StrictMono ⇑(w⁻¹) := by
      intro i j hij
      rw [Fin.lt_def] at hij
      exact key (j.val - i.val - 1) i j (by omega)
    exact inv_eq_one.mp (eq_one_of_strictMono _ hsm)
  · apply Finset.eq_empty_of_forall_notMem
    intro p hp
    rw [mem_invSet] at hp
    simp only [inv_one, Perm.one_apply] at hp
    exact lt_asymm hp.1 hp.2
  · intro w hw
    unfold invN
    rw [invSet_rev]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_subset_ne]
    refine ⟨Finset.filter_subset _ _, ?_⟩
    intro hset
    apply hw
    have hall : ∀ i j : Fin n, i < j → w⁻¹ j < w⁻¹ i := by
      intro i j hij
      have hm : (i, j) ∈ invSet w := by
        rw [hset]
        simp [pairs, hij]
      exact ((mem_invSet w _).mp hm).2
    have hsm : StrictMono ⇑(w⁻¹ * (Fin.revPerm : Perm (Fin n))) := by
      intro i j hij
      simp only [Perm.mul_apply, Fin.revPerm_apply]
      exact hall _ _ (Fin.rev_lt_rev.mpr hij)
    have h1 := eq_one_of_strictMono _ hsm
    rw [mul_eq_one_iff_eq_inv] at h1
    exact inv_inj.mp h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeEqDet
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem de_eq_det (R : Type) [CommRing R] (n : ℕ) :
    De R n = (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).det := by
  rw [Matrix.det_vandermonde, De, pairs, Finset.prod_filter, Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.prod_filter]
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext j
  simp

private theorem nn_ne (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (q : R) : NN n q ≠ 0 := by
  rw [NN, Finset.prod_ne_zero_iff]
  intro p hp
  have hlt : p.1 < p.2 := by simpa [pairs] using hp
  intro h
  have hc := congrArg (AddMonoidAlgebra.coeff · (Finsupp.single p.2 1)) h
  rw [coeff_sub, coeff_C_mul, coeff_X, coeff_X] at hc
  simp [Finsupp.single_left_inj one_ne_zero, hlt.ne] at hc

theorem UpperTheory.V.AlgebraTools.hkDe :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ), De R n ≠ 0 ∧ (∀ w : Perm (Fin n), rename w (De R n) = Perm.sign w • De R n) ∧ ∀ q : R, NN n q ≠ 0 := by
  intro R _ _ n
  refine ⟨?_, ?_, nn_ne R n⟩
  · rw [de_eq_det, Matrix.det_vandermonde_ne_zero_iff]
    exact X_injective
  · intro w
    rw [de_eq_det, AlgHom.map_det]
    have hm : (rename w : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).mapMatrix
        (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)) =
        (Matrix.vandermonde fun i : Fin n => (X i : MvPolynomial (Fin n) R)).submatrix w id := by
      ext i j
      simp [Matrix.vandermonde_apply]
    rw [hm, Matrix.det_permute, Units.smul_def, zsmul_eq_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotExtend
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.cotInd_extend :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (κ : Type) [Fintype κ] (x : κ → R), CotInd R x →
      ∃ (s : ℕ) (y : Fin s → R), CotInd R (Sum.elim x y) ∧
        Ideal.span (Set.range (Sum.elim x y)) = maximalIdeal R ∧
        Fintype.card κ + s = (maximalIdeal R).spanFinrank := by
  intro R _ _ _ κ _ x hx
  obtain ⟨hm, hli⟩ := (cotInd_iff R x).mp hx
  set v : κ → CotangentSpace R := fun k => (maximalIdeal R).toCotangent ⟨x k, hm k⟩ with hv
  let bW := Module.Basis.span hli
  let bQ := Module.finBasis (ResidueField R) (CotangentSpace R ⧸ Submodule.span (ResidueField R) (Set.range v))
  let B := Module.Basis.sumQuot bW bQ
  choose z hz using fun i => (maximalIdeal R).toCotangent_surjective (B (Sum.inr i))
  refine ⟨_, fun i => (z i : R), ?_⟩
  have hmem : ∀ j, Sum.elim x (fun i => (z i : R)) j ∈ maximalIdeal R := by
    rintro (k | i)
    · exact hm k
    · exact (z i).2
  have hB : (fun j => (maximalIdeal R).toCotangent ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩) = ⇑B := by
    funext j
    rcases j with k | i
    · simp [B, bW, Module.Basis.span_apply, hv]
    · simpa using hz i
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  refine ⟨(cotInd_iff R _).mpr ⟨hmem, ?_⟩, ?_, ?_⟩
  · rw [hB]
    exact B.linearIndependent
  · let g : κ ⊕ Fin _ → maximalIdeal R := fun j => ⟨Sum.elim x (fun i => (z i : R)) j, hmem j⟩
    have hspan : Submodule.span R (Set.range g) = ⊤ := by
      rw [← CotangentSpace.span_image_eq_top_iff, ← Set.range_comp]
      have : (maximalIdeal R).toCotangent ∘ g = ⇑B := hB
      rw [this, B.span_eq]
    have := congrArg (Submodule.map (maximalIdeal R).subtype) hspan
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp] at this
    exact this
  · rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg, Module.finrank_eq_card_basis B,
      Fintype.card_sum, Fintype.card_fin]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.FiniteHomOfTopFG
open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem fgHom_mem_of_closed {G : Type} [Group G] [TopologicalSpace G] {s : Set G}
    (hs : TopGen s) (E : Subgroup G) (hE : IsClosed (E : Set G)) (hsE : s ⊆ E) (g : G) : g ∈ E := by
  have h1 : (Subgroup.closure s : Set G) ⊆ E := (Subgroup.closure_le E).2 hsE
  have h2 : closure (Subgroup.closure s : Set G) ⊆ E := closure_minimal h1 hE
  exact h2 (hs g)

private theorem fgHom_part1 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : TopFG G) (Z : Type) [Group Z] [Finite Z] :
    {f : G →* Z | IsOpen (f.ker : Set G)}.Finite := by
  obtain ⟨s, hsf, hs⟩ := hG
  haveI : Finite s := hsf.to_subtype
  refine Set.Finite.of_finite_image (f := fun f : G →* Z => fun x : s => f x) (Set.toFinite _) ?_
  intro f hf f' hf' h
  have hle : f.ker ⊓ f'.ker ≤ f.eqLocus f' := by
    intro x hx
    have h1 : f x = 1 := hx.1
    have h2 : f' x = 1 := hx.2
    show f x = f' x
    rw [h1, h2]
  have hop : IsOpen ((f.ker ⊓ f'.ker : Subgroup G) : Set G) := IsOpen.inter hf hf'
  have hcl : IsClosed (f.eqLocus f' : Set G) :=
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono hle hop)
  ext g
  exact fgHom_mem_of_closed hs _ hcl (fun x hx => congrFun h ⟨x, hx⟩) g

private theorem fgHom_part2 {G : Type} [Group G] [TopologicalSpace G]
    (hG : TopFG G) (M : Type) [AddCommGroup M] [Finite M] [DistribMulAction G M] :
    {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + g • c h}.Finite := by
  obtain ⟨s, hsf, hs⟩ := hG
  haveI : Finite s := hsf.to_subtype
  refine Set.Finite.of_finite_image (f := fun c : G → M => fun x : s => c x) (Set.toFinite _) ?_
  intro c hc c' hc' h
  have one : ∀ d : G → M, (∀ g h, d (g * h) = d g + g • d h) → d 1 = 0 := by
    intro d hd
    have := hd 1 1
    rw [one_mul, one_smul] at this
    exact left_eq_add.1 this
  let E : Subgroup G :=
    { carrier := {g | c g = c' g}
      mul_mem' := by
        intro a b ha hb
        have ha' : c a = c' a := ha
        have hb' : c b = c' b := hb
        show c (a * b) = c' (a * b)
        rw [hc.2, hc'.2, ha', hb']
      one_mem' := by
        show c 1 = c' 1
        rw [one c hc.2, one c' hc'.2]
      inv_mem' := by
        intro a ha
        have ha' : c a = c' a := ha
        show c a⁻¹ = c' a⁻¹
        have h1 := hc.2 a a⁻¹
        have h2 := hc'.2 a a⁻¹
        rw [mul_inv_cancel, one c hc.2] at h1
        rw [mul_inv_cancel, one c' hc'.2, ← ha'] at h2
        exact MulAction.injective a (add_left_cancel (h1.symm.trans h2)) }
  have hcl : IsClosed (E : Set G) := by
    have := (hc.1.prodMk hc'.1) {p : M × M | p.1 ≠ p.2}
    rw [← isOpen_compl_iff]
    exact this
  funext g
  exact fgHom_mem_of_closed hs E hcl (fun x hx => congrFun h ⟨x, hx⟩) g

private theorem fgHom_part3 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : TopFG G) (n : ℕ) (hn : n ≠ 0) :
    {H : Subgroup G | IsOpen (H : Set G) ∧ H.index = n}.Finite := by
  have h1 := (fgHom_part1 hG (Equiv.Perm (Fin n))).prod (Set.finite_univ (α := Fin n))
  refine (h1.image fun p => (MulAction.stabilizer (Equiv.Perm (Fin n)) p.2).comap p.1).subset ?_
  rintro H ⟨hH, hi⟩
  haveI : H.FiniteIndex := ⟨hi ▸ hn⟩
  have e : (G ⧸ H) ≃ Fin n := Finite.equivFinOfCardEq hi
  refine ⟨(e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H)), e ((1 : G) : G ⧸ H)),
    ⟨?_, trivial⟩, ?_⟩
  · have hop : IsOpen (H.normalCore : Set G) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _
        (Subgroup.normalCore_isClosed H (Subgroup.isClosed_of_isOpen H hH))
    refine Subgroup.isOpen_mono ?_ hop
    intro g hg
    rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hg, map_one]
  · ext g
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    have : (e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))) g • e ((1 : G) : G ⧸ H)
        = e ((g : G) : G ⧸ H) := by
      simp [Equiv.Perm.smul_def]
    rw [this, e.injective.eq_iff, eq_comm, QuotientGroup.eq, inv_one, one_mul]

theorem UpperTheory.V.AlgebraTools.finite_hom_of_topFG :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], TopFG G →
      (∀ (Z : Type) [Group Z] [Finite Z], {f : G →* Z | IsOpen (f.ker : Set G)}.Finite) ∧
      (∀ (M : Type) [AddCommGroup M] [Finite M] [DistribMulAction G M], (∀ m : M, IsLocallyConstant fun g : G => g • m) →
        {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + g • c h}.Finite) ∧
      (∀ n : ℕ, n ≠ 0 → {H : Subgroup G | IsOpen (H : Set G) ∧ H.index = n}.Finite) := by
  intro G _ _ _ hG
  exact ⟨fun Z _ _ => fgHom_part1 hG Z, fun M _ _ _ _ => fgHom_part2 hG M,
    fun n hn => fgHom_part3 hG n hn⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDdSpec
section -- merged from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ProdPrimesDvd
theorem UpperTheory.Reformulated.B.Qi3.finset_prod_dvd_of_prime_of_dvd_imp_eq :
    ∀ {M ι : Type} [inst : CommRing M] (f : ι → M) (y : M)
    (s : Finset ι),
    (∀ a ∈ s, Prime (f a)) → (∀ a ∈ s, ∀ b ∈ s, f a ∣ f b → a = b) → (∀ a ∈ s, f a ∣ y) → ∏ a ∈ s, f a ∣ y := by
  intro M ι inst f y s
  classical
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert a s ha ih =>
    intro hp hd hy
    have hpa : Prime (f a) := hp a (Finset.mem_insert_self a s)
    obtain ⟨c, hc⟩ := ih (fun b hb => hp b (Finset.mem_insert_of_mem hb))
      (fun b hb d hd' => hd b (Finset.mem_insert_of_mem hb) d (Finset.mem_insert_of_mem hd'))
      (fun b hb => hy b (Finset.mem_insert_of_mem hb))
    have h1 : f a ∣ (∏ b ∈ s, f b) * c := hc ▸ hy a (Finset.mem_insert_self a s)
    rcases hpa.dvd_or_dvd h1 with h2 | h2
    · obtain ⟨b, hb, hab⟩ := hpa.exists_mem_finset_dvd h2
      have h3 : a = b := hd a (Finset.mem_insert_self a s) b (Finset.mem_insert_of_mem hb) hab
      exact absurd (h3 ▸ hb) ha
    · rw [Finset.prod_insert ha, hc, mul_comm (f a)]
      exact mul_dvd_mul_left _ h2
end

open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

private theorem finset_prod_dvd_of_prime_of_dvd_imp_eq {M ι : Type} [CommRing M] (f : ι → M) (y : M) (s : Finset ι)
    (hp : ∀ a ∈ s, Prime (f a)) (hn : ∀ a ∈ s, ∀ b ∈ s, f a ∣ f b → a = b) (hd : ∀ a ∈ s, f a ∣ y) :
    ∏ a ∈ s, f a ∣ y :=
  _root_.UpperTheory.Reformulated.B.Qi3.finset_prod_dvd_of_prime_of_dvd_imp_eq f y s hp hn hd

private def sb {n : ℕ} (i j : Fin n) : Fin n → Fin n := fun k => if k = j then i else k

private theorem dvd_sub_sb {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (y : MvPolynomial (Fin n) R) :
    (X j - X i : MvPolynomial (Fin n) R) ∣ y - rename (sb i j) y := by
  induction y using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq =>
    have := dvd_add hp hq
    rw [map_add (f := _)]
    convert this using 1
    ring
  | mul_X p k hp =>
    have hk : (X j - X i : MvPolynomial (Fin n) R) ∣ X k - X (sb i j k) := by
      unfold sb
      split_ifs with h
      · rw [h]
      · simp
    have := dvd_add (hp.mul_right (X k)) (hk.mul_left (rename (sb i j) p))
    rw [map_mul, rename_X]
    convert this using 1
    ring

private theorem dvd_iff_sb {R : Type} [CommRing R] {n : ℕ} (i j : Fin n) (y : MvPolynomial (Fin n) R) :
    (X j - X i : MvPolynomial (Fin n) R) ∣ y ↔ rename (sb i j) y = 0 := by
  constructor
  · rintro ⟨c, rfl⟩
    have : sb i j j = sb i j i := by simp [sb]
    rw [map_mul, map_sub, rename_X, rename_X, this, sub_self, zero_mul]
  · intro h
    have := dvd_sub_sb i j y
    rwa [h, sub_zero] at this

private theorem prime_sb {R : Type} [CommRing R] [IsDomain R] {n : ℕ} {i j : Fin n} (h : i ≠ j) :
    Prime (X j - X i : MvPolynomial (Fin n) R) := by
  refine ⟨fun e => h.symm (X_injective (sub_eq_zero.1 e)), fun hu => ?_, fun a b hab => ?_⟩
  · have := (dvd_iff_sb i j (1 : MvPolynomial (Fin n) R)).1 hu.dvd
    simp at this
  · rw [dvd_iff_sb, map_mul, mul_eq_zero] at hab
    rwa [dvd_iff_sb, dvd_iff_sb]

private theorem alt_sb {R : Type} [CommRing R] {n : ℕ} {i j : Fin n} (h : i ≠ j) (x : MvPolynomial (Fin n) R) :
    rename (sb i j) (alt x) = 0 := by
  have hs : ∀ k, sb i j (swap i j k) = sb i j k := by
    intro k
    by_cases h1 : k = i
    · subst h1; simp [sb]
    · by_cases h2 : k = j
      · subst h2; simp [sb]
      · rw [swap_apply_of_ne_of_ne h1 h2]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [alt, map_sum]
  refine Finset.sum_involution (fun w _ => swap i j * w) (fun w _ => ?_) (fun w _ _ e => ?_)
    (fun w _ => Finset.mem_univ _) (fun w _ => ?_)
  · have e : sb i j ∘ (swap i j * w : Perm (Fin n)) = sb i j ∘ w := funext fun k => hs _
    rw [Units.smul_def, Units.smul_def, map_zsmul, map_zsmul, rename_rename, rename_rename, e, Perm.sign_mul,
      Perm.sign_swap h]
    simp
  · have := mul_eq_right.1 e
    exact h (swap_eq_one_iff.1 this)
  · simp [← mul_assoc]

theorem UpperTheory.V.AlgebraTools.hkDdSpec :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (x : MvPolynomial (Fin n) R), De R n * dd x = alt x := by
  intro R _ _ n x
  have hlt : ∀ p ∈ pairs n, p.1 < p.2 := fun p hp => by simpa [pairs] using hp
  have hd : De R n ∣ alt x := by
    refine finset_prod_dvd_of_prime_of_dvd_imp_eq _ _ _ (fun p hp => prime_sb (hlt p hp).ne) (fun p hp q hq hpq => ?_)
      (fun p hp => (dvd_iff_sb _ _ _).2 (alt_sb (hlt p hp).ne x))
    rw [dvd_iff_sb, map_sub, rename_X, rename_X, sub_eq_zero] at hpq
    have e := X_injective hpq
    have h1 := hlt p hp
    have h2 := hlt q hq
    unfold sb at e
    split_ifs at e with a b b
    · exact absurd (b.trans a.symm) h2.ne
    · exact Prod.ext e a.symm
    · rw [e, b] at h2
      exact absurd h1 h2.not_gt
    · exact absurd e h2.ne'
  obtain ⟨y, hy⟩ := hd
  have h : ∃ y, De R n * y = alt x := ⟨y, hy.symm⟩
  rw [dd, dite_eq_left h]
  exact h.choose_spec
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.CaCotOfSpan
open IsLocalRing UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.cotInd_of_span :
    ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (κ : Type) [Fintype κ] (x : κ → R),
      Ideal.span (Set.range x) = maximalIdeal R → Fintype.card κ ≤ (maximalIdeal R).spanFinrank → CotInd R x := by
  intro R _ _ _ κ _ x hx hcard
  have hm : ∀ k, x k ∈ maximalIdeal R := fun k => hx ▸ Ideal.subset_span ⟨k, rfl⟩
  refine (cotInd_iff R x).mpr ⟨hm, ?_⟩
  let g : κ → maximalIdeal R := fun k => ⟨x k, hm k⟩
  have hg : Submodule.span R (Set.range g) = ⊤ := by
    apply Submodule.map_injective_of_injective (maximalIdeal R).injective_subtype
    rw [Submodule.map_span, Submodule.map_top, Submodule.range_subtype, ← Set.range_comp]
    exact hx
  have hV : Submodule.span (ResidueField R) (Set.range ((maximalIdeal R).toCotangent ∘ g)) = ⊤ := by
    rw [Set.range_comp, CotangentSpace.span_image_eq_top_iff]
    exact hg
  have hfg : (maximalIdeal R).FG := IsNoetherian.noetherian _
  have hle := finrank_range_le_card (R := ResidueField R) ((maximalIdeal R).toCotangent ∘ g)
  rw [Set.finrank, hV, finrank_top] at hle
  rw [spanFinrank_maximalIdeal_eq_finrank_cotangentSpace_of_fg hfg] at hcard
  exact linearIndependent_of_top_le_span_of_card_eq_finrank hV.ge (le_antisymm hcard hle)
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagMap
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.lag_map :
    ∀ {R R' E E' ι : Type} [CommRing R] [CommRing R'] [Ring E] [Ring E'] [Algebra R E] [Algebra R' E'] [Fintype ι] [DecidableEq ι] (φ : R →+* R') (π : E →+* E') (a : ι → R) (P : E), (∀ c, π (algebraMap R E c) = algebraMap R' E' (φ c)) → (∀ i j, i ≠ j → IsUnit (a i - a j)) → ∀ i, π (lag a P i) = lag (fun j => φ (a j)) (π P) i := by
  intro R R' E E' ι _ _ _ _ _ _ _ _ φ π a P hc ha i
  have key : ∀ q : R[X], π (aeval P q) = aeval (π P) (q.map φ) := by
    intro q
    rw [aeval_def, aeval_def, Polynomial.hom_eval₂, Polynomial.eval₂_map]
    congr 1
    exact RingHom.ext hc
  have hsm : ∀ (c : R) (x : E), π (c • x) = φ c • π x := by
    intro c x
    rw [Algebra.smul_def, Algebra.smul_def, map_mul, hc]
  have h0 := (eq_lag_iff a P i (fun j hj => ha i j (Ne.symm hj)) (lag a P i)).1 rfl
  have h1 := congrArg π h0
  rw [hsm, key] at h1
  simp only [map_prod, Polynomial.map_prod, map_sub, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C] at h1
  rw [eq_lag_iff (fun j => φ (a j)) (π P) i (fun j hj => by
      rw [← map_sub]; exact (ha i j (Ne.symm hj)).map φ) (π (lag a P i))]
  exact h1
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HkDedekind
open MvPolynomial Equiv UpperTheory.V.AlgebraTools.Hk

theorem UpperTheory.V.AlgebraTools.hkDedekind :
    ∀ (R : Type) [CommRing R] [IsDomain R] (n : ℕ) (K : Type) [Field K] [Algebra (MvPolynomial (Fin n) R) K] [IsFractionRing (MvPolynomial (Fin n) R) K] (f : Perm (Fin n) → K),
      (∀ x : MvPolynomial (Fin n) R, ∑ u, f u * algebraMap _ K (rename u x) = 0) → f = 0 := by
  intro R _ _ n K _ _ _ f hf
  classical
  let φ : Perm (Fin n) → (MvPolynomial (Fin n) R →* K) := fun u =>
    (algebraMap (MvPolynomial (Fin n) R) K).toMonoidHom.comp (rename u : MvPolynomial (Fin n) R →ₐ[R] MvPolynomial (Fin n) R).toRingHom.toMonoidHom
  have hinj : Function.Injective φ := by
    intro u v huv
    ext i
    have h := DFunLike.congr_fun huv (X i)
    simp only [φ, MonoidHom.comp_apply, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.coe_toRingHom, rename_X] at h
    have h2 := IsFractionRing.injective (MvPolynomial (Fin n) R) K h
    exact congrArg Fin.val (X_injective h2)
  have hli := (linearIndependent_monoidHom (MvPolynomial (Fin n) R) K).comp φ hinj
  rw [Fintype.linearIndependent_iff] at hli
  funext u
  apply hli f
  funext x
  simpa [φ, Finset.sum_apply] using hf x
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.UnitsBasic
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

private theorem units_x_mul_ep_and_st_idempotent_identities {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o) (i : ι) :
    U.x i * U.ep i = U.x i ∧ U.ep (o i) * U.x i = U.x i ∧ T.st (U.x i) * U.ep (o i) = T.st (U.x i) ∧ U.ep i * T.st (U.x i) = T.st (U.x i) := by
  have hr : U.x i * U.ep i = U.x i := by
    conv_rhs => rw [← U.x_mem i]
    conv_lhs => rw [← U.x_mem i]
    rw [mul_assoc _ (U.ep i) (U.ep i), (U.coi.idem i).eq]
  have hl : U.ep (o i) * U.x i = U.x i := by
    conv_rhs => rw [← U.x_mem i]
    conv_lhs => rw [← U.x_mem i]
    simp only [← mul_assoc, (U.coi.idem (o i)).eq]
  refine ⟨hr, hl, ?_, ?_⟩
  · have h := congrArg T.st hl
    rwa [T.st_mul, U.st_ep] at h
  · have h := congrArg T.st hr
    rwa [T.st_mul, U.st_ep] at h

theorem UpperTheory.V.AlgebraTools.units_basic :
    ∀ {B E : Type} [CommRing B] [Ring E] [Algebra B E] (T : TrInv B E) {ι : Type} [Fintype ι] [DecidableEq ι] (o : ι → ι) (U : T.Units ι o), (∀ i j, i ≠ j → U.x i * T.st (U.x j) = 0) ∧ ∑ i, T.st (U.x i) * U.x i = 1 ∧ (∀ i j y, i ≠ j → T.tr (U.ep i * y * U.ep j) = 0) ∧ (∀ y, T.tr y = ∑ i, T.tr (U.x i * y * T.st (U.x i))) ∧ (∀ i j y, o i = o j → U.x i * y * T.st (U.x j) = T.tr (U.x i * y * T.st (U.x j)) • U.ep (o i)) ∧ (∀ y, y = ∑ i, ∑ j, T.st (U.x i) * (U.x i * y * T.st (U.x j)) * U.x j) ∧ ∀ i j y, U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o j) = U.x i * y * T.st (U.x j) := by
  intro B E _ _ _ T ι _ _ o U
  have key : ∀ i j y, U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o j) = U.x i * y * T.st (U.x j) := by
    intro i j y
    obtain ⟨-, hl, hs, -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U i
    obtain ⟨-, -, hs', -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U j
    simp only [← mul_assoc]
    rw [hl, mul_assoc _ (T.st (U.x j)), hs']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, key⟩
  · intro i j h
    obtain ⟨hr, -, -, -⟩ := units_x_mul_ep_and_st_idempotent_identities T o U i
    obtain ⟨-, -, -, hs⟩ := units_x_mul_ep_and_st_idempotent_identities T o U j
    rw [← hr, ← hs, mul_assoc, ← mul_assoc (U.ep i), U.coi.ortho h, zero_mul, mul_zero]
  · simp_rw [U.st_mul_x_eq]
    exact U.coi.complete
  · intro i j y h
    rw [T.tr_comm, ← mul_assoc, U.coi.ortho (Ne.symm h), zero_mul, map_zero]
  · intro y
    have h : ∀ i, T.tr (U.x i * y * T.st (U.x i)) = T.tr (U.ep i * y) := by
      intro i
      rw [T.tr_comm, ← mul_assoc, U.st_mul_x_eq]
    simp_rw [h]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← map_sum, ← Finset.sum_mul, U.coi.complete, one_mul]
  · intro i j y h
    have h7 := key i j y
    rw [← h] at h7
    calc U.x i * y * T.st (U.x j)
        = U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o i) := h7.symm
      _ = T.tr (U.ep (o i) * (U.x i * y * T.st (U.x j)) * U.ep (o i)) • U.ep (o i) := U.corner_eq _ _
      _ = T.tr (U.x i * y * T.st (U.x j)) • U.ep (o i) := by rw [h7]
  · intro y
    have h : ∀ i j, T.st (U.x i) * (U.x i * y * T.st (U.x j)) * U.x j = U.ep i * y * U.ep j := by
      intro i j
      rw [← U.st_mul_x_eq i, ← U.st_mul_x_eq j]
      simp only [mul_assoc]
    simp_rw [h, ← Finset.mul_sum, ← Finset.sum_mul, U.coi.complete, mul_one, one_mul]
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.LagCoi
open Polynomial Matrix IsLocalRing TensorProduct UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.lag_coi :
    ∀ {R E ι : Type} [CommRing R] [Ring E] [Algebra R E] [Fintype ι] [DecidableEq ι] (a : ι → R) (P : E), (∀ i j, i ≠ j → IsUnit (a i - a j)) → aeval P (∏ i, (X - C (a i))) = 0 → CompleteOrthogonalIdempotents (lag a P) ∧ (∀ i, P * lag a P i = a i • lag a P i) ∧ (∀ (q : R[X]) i, aeval P q * lag a P i = q.eval (a i) • lag a P i) ∧ ∀ y i, Commute y P → Commute y (lag a P i) := by
  intro R E ι _ _ _ _ _ a P ha hm
  have hc : ∀ i, IsUnit (∏ j ∈ Finset.univ.erase i, (a i - a j)) := fun i =>
    IsUnit.prod_iff.2 (fun j hj => ha i j (Ne.symm (Finset.ne_of_mem_erase hj)))
  let L : ι → R[X] := fun i =>
    C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j ∈ Finset.univ.erase i, (X - C (a j))
  have hL : ∀ i, lag a P i = aeval P (L i) := by
    intro i
    simp only [L, lag, map_mul, aeval_C, Algebra.smul_def]
  have hLe : ∀ i k, (L i).eval (a k) = if i = k then 1 else 0 := by
    intro i k
    simp only [L, eval_mul, eval_C, eval_prod, eval_sub, eval_X]
    split_ifs with h
    · subst h
      exact Ring.inverse_mul_cancel _ (hc i)
    · rw [Finset.prod_eq_zero (f := fun j => a k - a j)
        (Finset.mem_erase.2 ⟨Ne.symm h, Finset.mem_univ k⟩) (sub_self (a k)), mul_zero]
  have hroot : ∀ i, aeval P (X - C (a i)) * lag a P i = 0 := by
    intro i
    rw [hL, ← map_mul]
    have : (X - C (a i)) * L i =
        C (Ring.inverse (∏ j ∈ Finset.univ.erase i, (a i - a j))) * ∏ j, (X - C (a j)) := by
      simp only [L]
      rw [mul_left_comm, Finset.mul_prod_erase Finset.univ (fun j => X - C (a j)) (Finset.mem_univ i)]
    rw [this, map_mul, hm, mul_zero]
  have hq : ∀ (q : R[X]) i, aeval P q * lag a P i = q.eval (a i) • lag a P i := by
    intro q i
    obtain ⟨g, hg⟩ := (X_sub_C_dvd_sub_C_eval : X - C (a i) ∣ q - C (q.eval (a i)))
    have hq' : q = g * (X - C (a i)) + C (q.eval (a i)) := by
      rw [mul_comm, ← hg]
      ring
    conv_lhs => rw [hq']
    rw [map_add (f := _), map_mul, add_mul, mul_assoc, hroot, mul_zero, zero_add, aeval_C, Algebra.smul_def]
  have hP : ∀ i, P * lag a P i = a i • lag a P i := by
    intro i
    have := hq X i
    rwa [aeval_X, eval_X] at this
  have hcomm : ∀ y i, Commute y P → Commute y (lag a P i) := by
    intro y i hy
    rw [hL]
    generalize L i = f
    induction f using Polynomial.induction_on' with
    | add p q hp hq => rw [map_add (f := _)]; exact hp.add_right hq
    | monomial n c =>
      rw [aeval_monomial]
      exact Commute.mul_right (show Commute y (algebraMap R E c) from (Algebra.commutes c y).symm)
        (hy.pow_right n)
  have hsum : ∑ i, lag a P i = 1 := by
    have h1 : ∏ i, (X - C (a i)) ∣ 1 - ∑ i, L i := by
      apply Finset.prod_dvd_of_coprime
      · intro i _ j _ hij
        exact isCoprime_X_sub_C_of_isUnit_sub (ha i j hij)
      · intro k _
        rw [dvd_iff_isRoot, IsRoot, eval_sub, eval_one, eval_finsetSum]
        simp only [hLe, Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]
    obtain ⟨g, hg⟩ := h1
    have h2 := congrArg (aeval P) hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_mul, hm, zero_mul, map_sub, map_one, map_sum, sub_eq_zero] at h2
    simp only [hL]
    exact h2.symm
  refine ⟨⟨⟨fun i => ?_, fun i j hij => ?_⟩, hsum⟩, hP, hq, hcomm⟩
  · show lag a P i * lag a P i = lag a P i
    have := hq (L i) i
    rw [← hL, hLe, if_pos rfl, one_smul] at this
    exact this
  · have := hq (L i) j
    rw [← hL, hLe, if_neg hij, zero_smul] at this
    exact this
end
