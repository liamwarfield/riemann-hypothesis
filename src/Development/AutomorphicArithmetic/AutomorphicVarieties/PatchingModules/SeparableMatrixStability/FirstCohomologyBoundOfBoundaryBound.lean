module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.SelRed

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CoboundaryFirstSubsetSelmerFirst
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem bd_mem_iff {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}
    (Z : Matrix (Fin n) (Fin n) (DD X g)) : Z ∈ W1 n A X g a ↔ ∀ i j : Fin n,
      (Z i j).ep' = 0 ∧ (Z i j).eta = 0 ∧ ((((i : ℕ) < a) ↔ ((j : ℕ) < a)) → (Z i j).ep = 0) ∧
        (¬ (((i : ℕ) < a) ↔ ((j : ℕ) < a)) → (Z i j).a = 0) := by
  simp only [W1, blkMat, ddPart, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq]
  refine forall_congr' fun i => forall_congr' fun j => ?_
  by_cases hd : ((i : ℕ) < a ↔ (j : ℕ) < a) <;> simp [hd] <;> tauto

private theorem dd_components_finset_sum {X ι : Type} [CommRing X] {g : ℕ} (s : Finset ι) (f : ι → DD X g) :
    (∑ k ∈ s, f k).a = ∑ k ∈ s, (f k).a ∧ (∀ j, (∑ k ∈ s, f k).ep j = ∑ k ∈ s, (f k).ep j) ∧
      (∀ j, (∑ k ∈ s, f k).ep' j = ∑ k ∈ s, (f k).ep' j) ∧ (∑ k ∈ s, f k).eta = ∑ k ∈ s, (f k).eta := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [DD.zero_a, DD.zero_ep, DD.zero_ep', DD.zero_eta]
  | insert k s hk ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨?_, fun j => ?_, fun j => ?_, ?_⟩ <;>
      simp [Finset.sum_insert hk, DD.add_a, DD.add_ep, DD.add_ep', DD.add_eta, h1, h2, h3, h4]

private theorem bd_mul_mem {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ}
    {Z Z' : Matrix (Fin n) (Fin n) (DD X g)} (h : Z ∈ W1 n A X g a) (h' : Z' ∈ W1 n A X g a) :
    Z * Z' ∈ W1 n A X g a := by
  rw [bd_mem_iff] at h h' ⊢
  intro i j
  obtain ⟨ha, hep, hep', heta⟩ := dd_components_finset_sum Finset.univ (fun k => Z i k * Z' k j)
  rw [Matrix.mul_apply]
  refine ⟨?_, ?_, ?_, ?_⟩
  · funext m
    rw [hep']
    exact Finset.sum_eq_zero fun k _ => by simp [DD.mul_ep', (h i k).1, (h' k j).1]
  · rw [heta]
    exact Finset.sum_eq_zero fun k _ => by
      simp [DD.mul_eta, (h i k).1, (h' k j).1, (h i k).2.1, (h' k j).2.1]
  · intro hd
    funext m
    rw [hep]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [DD.mul_ep]
    by_cases hk : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hk' : ((k : ℕ) < a ↔ (j : ℕ) < a) := hk.symm.trans hd
      rw [congrFun ((h i k).2.2.1 hk) m, congrFun ((h' k j).2.2.1 hk') m]
      simp
    · have hk' : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun hh => hk (hd.trans hh.symm)
      rw [(h i k).2.2.2 hk, (h' k j).2.2.2 hk']
      simp
  · intro hd
    rw [ha]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [DD.mul_a]
    by_cases hk : ((i : ℕ) < a ↔ (k : ℕ) < a)
    · have hk' : ¬((k : ℕ) < a ↔ (j : ℕ) < a) := fun hh => hd (hk.trans hh)
      rw [(h' k j).2.2.2 hk', mul_zero]
    · rw [(h i k).2.2.2 hk, zero_mul]

private theorem bd_rho_mem {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (g : F.G₀) : k.ρ1 X g ∈ W1 n x.A X k.g x.a := by
  have hC : ∀ c : x.A, algebraMap x.A (DD X k.g) c = DD.C (algebraMap x.A X c) := fun _ => rfl
  have hK : ∀ m (i j : Fin n), ((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → k.κ m g i j = 0 := by
    intro m i j hd
    have hm := (k.mem m).1 g
    simp only [Od, blkMat, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq, Submodule.mem_bot] at hm
    exact (hm i j).1 hd
  have hR : ∀ i j : Fin n, ¬((i : ℕ) < x.a ↔ (j : ℕ) < x.a) → (mat x.ρ) g i j = 0 := by
    intro i j hd
    have hm := x.blk g
    simp only [Ev, blkMat, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
      Set.mem_setOf_eq, Submodule.mem_bot] at hm
    exact (hm i j).2 hd
  apply bd_mul_mem
  · rw [bd_mem_iff]
    intro i j
    by_cases hij : i = j
    · subst hij
      refine ⟨?_, ?_, fun _ => ?_, fun hd => absurd Iff.rfl hd⟩
      · funext m
        simp [DD.epM, DD.add_ep', DD.one_ep']
      · simp [DD.epM, DD.add_eta, DD.one_eta]
      · funext m
        simp [DD.epM, DD.add_ep, DD.one_ep, hK m i i Iff.rfl]
    · refine ⟨?_, ?_, fun hd => ?_, fun hd => ?_⟩
      · funext m
        simp [DD.epM, DD.add_ep', Matrix.one_apply_ne hij, DD.zero_ep']
      · simp [DD.epM, DD.add_eta, Matrix.one_apply_ne hij, DD.zero_eta]
      · funext m
        simp [DD.epM, DD.add_ep, Matrix.one_apply_ne hij, DD.zero_ep, hK m i j hd]
      · simp [DD.epM, DD.add_a, Matrix.one_apply_ne hij, DD.zero_a]
  · rw [bd_mem_iff]
    intro i j
    simp only [NP.ρX, Matrix.map_apply, hC]
    refine ⟨?_, ?_, fun _ => ?_, fun hd => ?_⟩
    · funext m
      exact DD.C_ep' _ m
    · exact DD.C_eta _
    · funext m
      exact DD.C_ep _ m
    · rw [DD.C_a, hR i j hd, map_zero]

private theorem bd_epM_mul {X : Type} [CommRing X] {g n : ℕ} (Z Z' : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * DD.epM Z' = 0 := by
  refine Matrix.ext fun i j => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun m _ => ?_
  ext <;> simp [DD.epM]

private theorem bd_polar {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) (X : Type)
    [CommRing X] [Algebra x.A X] (g : F.G₀) : (k.ρ1 X g)ᵀ * k.ρ1 X (F.conj g) =
      algebraMap x.A (DD X k.g) ((F.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) • (1 : Matrix (Fin n) (Fin n) (DD X k.g)) := by
  set E : F.G₀ → Matrix (Fin n) (Fin n) (DD X k.g) :=
    fun g => DD.epM fun j => (k.κ j g).map ⇑(algebraMap x.A X) with hE
  have hρ1 : ∀ g, k.ρ1 X g = (1 + E g) * (x.ρX (DD X k.g) g) := fun _ => rfl
  have hT : (E g)ᵀ = DD.epM fun j => ((k.κ j g).map ⇑(algebraMap x.A X))ᵀ :=
    Matrix.ext fun _ _ => rfl
  have hc : E (F.conj g) = -(E g)ᵀ := by
    refine Matrix.ext fun i i' => DD.ext ?_ ?_ ?_ ?_
    · simp [hE, DD.epM, DD.neg_a]
    · funext m
      have h4 := (k.mem m).2.2.2.1 g
      simp [hE, DD.epM, DD.neg_ep, h4]
    · funext m
      simp [hE, DD.epM, DD.neg_ep']
    · simp [hE, DD.epM, DD.neg_eta]
  have hmid : (1 + E g)ᵀ * (1 + E (F.conj g)) = 1 := by
    have hTT : (E g)ᵀ * (E g)ᵀ = 0 := by
      rw [hT]
      exact bd_epM_mul _ _
    rw [Matrix.transpose_add, Matrix.transpose_one, hc, add_mul, one_mul, mul_add, mul_one, mul_neg,
      hTT, neg_zero, add_zero, neg_add_cancel_right]
  have hsc : ∀ c : x.A, (c • (1 : Matrix (Fin n) (Fin n) x.A)).map ⇑(algebraMap x.A (DD X k.g)) =
      algebraMap x.A (DD X k.g) c • (1 : Matrix (Fin n) (Fin n) (DD X k.g)) := by
    intro c
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  rw [hρ1, hρ1, Matrix.transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc ((1 + E g)ᵀ), hmid,
    Matrix.one_mul]
  have hf := x.form g
  simp only [Units.val_one, Matrix.mul_one] at hf
  simp only [NP.ρX, ← Matrix.transpose_map, ← Matrix.map_mul, hf]
  exact hsc _

private theorem bd_cont {Γ R : Type} [TopologicalSpace Γ] [Group Γ] [IsTopologicalGroup Γ] [CommRing R] {n : ℕ} (I : Ideal R)
    (ρ : Γ → Matrix (Fin n) (Fin n) R) (hρ : ∀ i j, AdicCont I fun g => ρ g i j) (Y : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    AdicCont I fun g => (ρ g * Y * ρ g⁻¹ - Y) i j := by
  intro N
  have hl : ∀ i j, IsLocallyConstant fun g => Ideal.Quotient.mk (I ^ N) (ρ g i j) :=
    fun i j => hρ i j N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have h1 : ∀ᶠ y in nhds x, ∀ p : Fin n × Fin n,
      Ideal.Quotient.mk (I ^ N) (ρ y p.1 p.2) = Ideal.Quotient.mk (I ^ N) (ρ x p.1 p.2) := by
    rw [Filter.eventually_all]
    intro p
    exact (IsLocallyConstant.iff_eventually_eq _).mp (hl p.1 p.2) x
  have h2 : ∀ᶠ y in nhds x, ∀ p : Fin n × Fin n,
      Ideal.Quotient.mk (I ^ N) (ρ y⁻¹ p.1 p.2) = Ideal.Quotient.mk (I ^ N) (ρ x⁻¹ p.1 p.2) := by
    rw [Filter.eventually_all]
    intro p
    have hx := (IsLocallyConstant.iff_eventually_eq _).mp (hl p.1 p.2) x⁻¹
    exact (continuous_inv.tendsto x).eventually hx
  filter_upwards [h1, h2] with y hy1 hy2
  have e1 : (Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ y) = (Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ x) :=
    Matrix.ext fun i j => hy1 (i, j)
  have e2 : (Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ y⁻¹) =
      (Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ x⁻¹) :=
    Matrix.ext fun i j => hy2 (i, j)
  have key : ∀ z, Ideal.Quotient.mk (I ^ N) ((ρ z * Y * ρ z⁻¹ - Y) i j) =
      ((Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ z) * (Ideal.Quotient.mk (I ^ N)).mapMatrix Y *
        (Ideal.Quotient.mk (I ^ N)).mapMatrix (ρ z⁻¹) - (Ideal.Quotient.mk (I ^ N)).mapMatrix Y) i j := by
    intro z
    rw [← map_mul, ← map_mul, ← map_sub]
    rfl
  show Ideal.Quotient.mk (I ^ N) ((ρ y * Y * ρ y⁻¹ - Y) i j) = Ideal.Quotient.mk (I ^ N) ((ρ x * Y * ρ x⁻¹ - Y) i j)
  rw [key y, key x, e1, e2]

theorem UpperTheory.V.Pa.coboundary_first_subset_selmer_first :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (X : Type) [CommRing X] [Algebra x.A X], Bd1 h X k ⊆ Sel1 h X k := by
  intro l _ L G G0 h n x k X _ _ z hz
  obtain ⟨Y, hY, hYT, rfl⟩ := hz
  obtain ⟨hρ1, hmul, hcont⟩ := (rho_hom l G0.frame n x k X).2.1
  have hinv : ∀ g, k.ρ1 X g * k.ρ1 X g⁻¹ = 1 := fun g => by rw [← hmul, mul_inv_cancel, hρ1]
  have hz : dY G.frame (fun g => k.ρ1 X (h.p₀ g)) Y = fun g => dY G0.frame (k.ρ1 X) Y (h.p₀ g) :=
    funext fun g => h.dY_comp _ Y g
  rw [hz]
  refine (h.sel_iff x.t (k.ρ1 X) (k.w1 X) (k.wi1 X) (W1 n x.A X k.g x.a) (dY G0.frame (k.ρ1 X) Y)).mpr
    ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g
    exact Submodule.sub_mem _ (bd_mul_mem (bd_mul_mem (bd_rho_mem k X g) hY) (bd_rho_mem k X g⁻¹)) hY
  · intro i j
    exact bd_cont _ (k.ρ1 X) hcont Y i j
  · intro g g'
    show k.ρ1 X (g * g') * Y * k.ρ1 X (g * g')⁻¹ - Y =
      (k.ρ1 X g * Y * k.ρ1 X g⁻¹ - Y) + k.ρ1 X g * (k.ρ1 X g' * Y * k.ρ1 X g'⁻¹ - Y) * k.ρ1 X g⁻¹
    rw [_root_.mul_inv_rev, hmul, hmul]
    noncomm_ring
  · intro g
    have hs : ∀ g : G0.frame.G₀,
        algebraMap x.A (DD X k.g) ((G0.frame.eps ℤ_[l] x.A g⁻¹ ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) *
          algebraMap x.A (DD X k.g) ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) = 1 := by
      intro g
      rw [← map_mul, ← Units.val_mul, ← mul_zpow, ← map_mul, inv_mul_cancel, map_one, _root_.one_zpow,
        Units.val_one, map_one]
    have hA : ∀ g : G0.frame.G₀, k.ρ1 X (G0.frame.conj g) =
        algebraMap x.A (DD X k.g) ((G0.frame.eps ℤ_[l] x.A g ^ (1 - (n : ℤ)) : x.Aˣ) : x.A) •
          (k.ρ1 X g⁻¹)ᵀ := by
      intro g
      have e : (k.ρ1 X g⁻¹)ᵀ * (k.ρ1 X g)ᵀ = 1 := by
        rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
      calc k.ρ1 X (G0.frame.conj g) = ((k.ρ1 X g⁻¹)ᵀ * (k.ρ1 X g)ᵀ) * k.ρ1 X (G0.frame.conj g) := by
            rw [e, Matrix.one_mul]
        _ = _ := by rw [Matrix.mul_assoc, bd_polar k X g, Matrix.mul_smul, Matrix.mul_one]
    show k.ρ1 X (G0.frame.conj g) * Y * k.ρ1 X (G0.frame.conj g)⁻¹ - Y =
      -(k.ρ1 X g * Y * k.ρ1 X g⁻¹ - Y)ᵀ
    rw [← map_inv G0.frame.conj g, hA, hA, inv_inv, Matrix.transpose_sub, Matrix.transpose_mul,
      Matrix.transpose_mul, hYT, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul, smul_smul, hs g,
      one_smul]
    noncomm_ring
  · intro u g hg
    have hone : ∀ g ∈ G0.frame.Iu u, k.ρ1 X g = 1 := by
      intro g hg
      have h0 : ∀ j, k.κ j g = 0 := fun j => (k.mem j).2.2.2.2.1 u g hg
      have hm : (mat x.ρ) g = 1 := by simp [mat, x.ine u g hg]
      have h1 : x.ρX (DD X k.g) g = 1 := by simp [NP.ρX, hm]
      have h2 : (DD.epM fun j => (k.κ j g).map ⇑(algebraMap x.A X)) = 0 := by
        refine Matrix.ext fun i i' => DD.ext ?_ ?_ ?_ ?_
        · simp [DD.epM, DD.zero_a]
        · funext m
          simp [DD.epM, DD.zero_ep, h0]
        · funext m
          simp [DD.epM, DD.zero_ep']
        · simp [DD.epM, DD.zero_eta]
      show (1 + DD.epM fun j => (k.κ j g).map ⇑(algebraMap x.A X)) * x.ρX (DD X k.g) g = 1
      rw [h1, h2, add_zero, mul_one]
    show k.ρ1 X g * Y * k.ρ1 X g⁻¹ - Y = 0
    rw [hone g hg, hone g⁻¹ (inv_mem hg)]
    simp
  · intro v
    exact ⟨Y, hY, fun g' => ⟨fun i j _ => by simp, fun _ i => by simp⟩⟩
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SeparableMatrixStability.CoefficientsBoundedOfSelmerBoundary
open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem ar_family {A M M' S : Type} [CommRing A] [IsNoetherianRing A]
    [AddCommGroup M] [Module A M] [Module.Finite A M] [AddCommGroup M'] [Module A M']
    [Module.Finite A M'] (I : Ideal A) (f : S → M →ₗ[A] M') :
    ∃ c : ℕ, ∀ (m : ℕ) (x : M), (∀ s, f s x ∈ I ^ (m + c) • (⊤ : Submodule A M')) →
      ∀ φ : M →ₗ[A] A, (∀ y, (∀ s, f s y = 0) → φ y = 0) → φ x ∈ I ^ m := by
  classical
  have hfg : (Submodule.span A (Set.range f)).FG := IsNoetherian.noetherian _
  obtain ⟨n, v, hv⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hfg
  let Φ : M →ₗ[A] (Fin n → M') := LinearMap.pi v
  obtain ⟨c, hc⟩ := UpperTheory.V.AlgebraTools.comap_pow_le I Φ
  have key : ∀ {ι : Type} (g : ι → M →ₗ[A] M') (N : Submodule A M') (x : M), (∀ i, g i x ∈ N) →
      ∀ u ∈ Submodule.span A (Set.range g), u x ∈ N := by
    intro ι g N x hx u hu
    induction hu using Submodule.span_induction with
    | mem u hu => obtain ⟨i, rfl⟩ := hu; exact hx i
    | zero => simp
    | add a b _ _ ha hb => exact N.add_mem ha hb
    | smul r a _ ha => exact N.smul_mem r ha
  refine ⟨c, fun m x hx φ hφ => ?_⟩
  have h0 : x ∈ (I ^ (m + c) • (⊤ : Submodule A (Fin n → M'))).comap Φ := by
    have h1 : ∀ i, v i x ∈ I ^ (m + c) • (⊤ : Submodule A M') := fun i =>
      key f _ x hx _ (hv ▸ Submodule.subset_span ⟨i, rfl⟩)
    rw [Submodule.mem_comap, ← Finset.univ_sum_single (Φ x)]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h2 : LinearMap.single A (fun _ : Fin n => M') i (v i x) ∈
        (I ^ (m + c) • (⊤ : Submodule A M')).map (LinearMap.single A (fun _ : Fin n => M') i) :=
      Submodule.mem_map_of_mem (h1 i)
    rw [Submodule.map_smul''] at h2
    exact Submodule.smul_mono le_rfl le_top h2
  have hle : LinearMap.ker Φ ⊔ I ^ m • (⊤ : Submodule A M) ≤ Submodule.comap φ (I ^ m : Ideal A) := by
    refine sup_le (fun y hy => ?_) (Submodule.smul_le.2 fun a ha y _ => ?_)
    · have h1 : ∀ i, v i y ∈ (⊥ : Submodule A M') := fun i => congrFun (LinearMap.mem_ker.mp hy) i
      rw [Submodule.mem_comap, hφ y fun s => key v ⊥ y h1 (f s) (hv ▸ Submodule.subset_span ⟨s, rfl⟩)]
      exact zero_mem _
    · rw [Submodule.mem_comap, map_smul, smul_eq_mul]
      exact Ideal.mul_mem_right _ _ ha
  exact hle (hc m h0)

private theorem dd_smul {A : Type} [CommRing A] {g : ℕ} (c : A) (y : DD A g) : c • y = DD.C c * y := rfl

private theorem dd_finite (A : Type) [CommRing A] [IsNoetherianRing A] (g : ℕ) : Module.Finite A (DD A g) := by
  let f : DD A g →ₗ[A] A × (Fin g → A) × (Fin g → A) × A :=
    { toFun := DD.equiv
      map_add' := fun _ _ => rfl
      map_smul' := fun c y => by
        ext <;> simp [dd_smul, DD.equiv] }
  exact Module.Finite.of_injective f DD.equiv.injective

private theorem dd_ker {A : Type} [CommRing A] {g : ℕ} (s : A) (y : DD A g)
    (hy : DD.map g (Ideal.Quotient.mkₐ A (Ideal.span {s})) y = 0) : ∃ y' : DD A g, y = s • y' := by
  have key : ∀ a : A, Ideal.Quotient.mkₐ A (Ideal.span {s}) a = 0 → ∃ b, a = s * b := fun a ha =>
    Ideal.mem_span_singleton.1 (Ideal.Quotient.eq_zero_iff_mem.1 ha)
  obtain ⟨a, ha⟩ := key y.a (congrArg DD.a hy)
  choose b hb using fun j => key (y.ep j) (congrFun (congrArg DD.ep hy) j)
  choose b' hb' using fun j => key (y.ep' j) (congrFun (congrArg DD.ep' hy) j)
  obtain ⟨d, hd⟩ := key y.eta (congrArg DD.eta hy)
  refine ⟨⟨a, b, b', d⟩, ?_⟩
  ext <;> simp [dd_smul, ha, hb, hb', hd]

private theorem exists_antisymmetric_lift_of_section {A X : Type} [CommRing A] [CommRing X] [Algebra A X] {g n a : ℕ} (f : A →ₐ[A] X)
    (σ : X →+ A) (hσ : ∀ y, f (σ y) = y) (Y : Matrix (Fin n) (Fin n) (DD X g)) (hY : Y ∈ W1 n A X g a)
    (hT : Yᵀ = -Y) : ∃ Y' ∈ W1 n A A g a, Y'ᵀ = -Y' ∧ Y'.map (DD.map g f) = Y := by
  let S : DD X g → DD A g := fun y => ⟨σ y.a, fun j => σ (y.ep j), fun j => σ (y.ep' j), σ y.eta⟩
  have hS : ∀ (b1 b2 b3 b4 : Bool) y, y ∈ ddPart A X g b1 b2 b3 b4 → S y ∈ ddPart A A g b1 b2 b3 b4 := by
    rintro b1 b2 b3 b4 y ⟨h1, h2, h3, h4⟩
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_, fun e => ?_⟩
    · simp [S, h1 e]
    · funext j; simp [S, h2 e]
    · funext j; simp [S, h3 e]
    · simp [S, h4 e]
  refine ⟨Y.map S, fun i j => ⟨fun e => hS _ _ _ _ _ ((hY i j).1 e), fun e => hS _ _ _ _ _ ((hY i j).2 e)⟩, ?_, ?_⟩
  · refine Matrix.ext fun i j => ?_
    have e : Y j i = -Y i j := congrFun (congrFun hT i) j
    show S (Y j i) = -S (Y i j)
    rw [e]
    ext <;> simp [S]
  · refine Matrix.ext fun i j => ?_
    show DD.map g f (S (Y i j)) = Y i j
    ext <;> simp [S, hσ]

private theorem map_first_order_lift_eq {l : ℕ} [Fact l.Prime] {F : GFrame l} {n : ℕ} {x : NP F n} (k : Kap x) {X : Type} [CommRing X]
    [Algebra x.A X] (f : x.A →ₐ[x.A] X) (g : F.G₀) : (k.ρ1 x.A g).map (DD.map k.g f) = k.ρ1 X g := by
  have e1 : (x.ρX (DD x.A k.g) g).map (DD.map k.g f) = x.ρX (DD X k.g) g :=
    Matrix.ext fun i j => (DD.map k.g f).commutes _
  have e2 : (DD.epM fun j => (k.κ j g).map (algebraMap x.A x.A)).map (DD.map k.g f) =
      DD.epM fun j => (k.κ j g).map (algebraMap x.A X) := by
    refine Matrix.ext fun i j => ?_
    refine DD.ext (map_zero f) (funext fun r => f.commutes _) (funext fun r => map_zero f) (map_zero f)
  rw [Kap.ρ1, Kap.ρ1, Matrix.map_mul, e1, Matrix.map_add _ (map_add _), e2, Matrix.map_one _ (map_zero _) (map_one _)]

private theorem exists_section (K : Type) [Field K] (I : Ideal (PowerSeries K)) :
    ∃ σ : (PowerSeries K ⧸ I) →+ PowerSeries K, ∀ y, Ideal.Quotient.mkₐ (PowerSeries K) I (σ y) = y := by
  obtain ⟨σ, hσ⟩ := (Ideal.Quotient.mkₐ K I).toLinearMap.exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.2 Ideal.Quotient.mk_surjective)
  exact ⟨σ.toAddMonoidHom, fun y => LinearMap.congr_fun hσ y⟩

theorem UpperTheory.V.Pa.coefficients_bounded_of_selmer_boundary :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (e : ℕ) (z : Fin e → G.G₀ → Matrix (Fin n) (Fin n) (DD x.A k.g)), TopFG G.Γ → (∀ i, z i ∈ Sel1 h x.A k) → (∀ c : Fin e → x.A, ∑ i, c i • z i ∈ Bd1 h x.A k → c = 0) → ∃ C : ℕ, ∀ (m : ℕ) (c : Fin e → x.A), (fun g => ((∑ i, c i • z i) g).map (x.redD k.g m)) ∈ Bd1 h (x.Am m) k → ∀ i, c i ∈ Ideal.span {x.t ^ (m - C)} := by
  intro l _ L G G0 h n x k e z _ _ hind
  haveI := dd_finite x.A k.g
  let V : Submodule x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    { carrier := {Y | Y ∈ W1 n x.A x.A k.g x.a ∧ Yᵀ = -Y}
      add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, by rw [transpose_add, ha.2, hb.2, neg_add]⟩
      zero_mem' := ⟨zero_mem _, by simp⟩
      smul_mem' := fun c Y hY => ⟨Submodule.smul_mem _ c hY.1, by rw [transpose_smul, hY.2, smul_neg]⟩ }
  let f : G.G₀ → ((Fin e → x.A) × V) →ₗ[x.A] Matrix (Fin n) (Fin n) (DD x.A k.g) := fun g =>
    { toFun := fun p => (∑ i, p.1 i • z i) g - dY G.frame (fun g => k.ρ1 x.A (h.p₀ g)) p.2 g
      map_add' := fun p q => by
        simp only [dY, Prod.fst_add, Prod.snd_add, Pi.add_apply, add_smul, Finset.sum_add_distrib, Submodule.coe_add,
          Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c p => by
        simp only [dY, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum,
          Submodule.coe_smul, Matrix.mul_smul, Matrix.smul_mul, RingHom.id_apply, smul_sub] }
  haveI : Module.Finite x.A (Matrix (Fin n) (Fin n) (DD x.A k.g)) :=
    inferInstanceAs (Module.Finite x.A (Fin n → Fin n → DD x.A k.g))
  haveI : Module.Finite x.A V := Module.Finite.of_injective V.subtype V.subtype_injective
  obtain ⟨C, hC⟩ := ar_family (Ideal.span {x.t}) f
  refine ⟨C, fun m c hc i => ?_⟩
  rcases le_total m C with hm | hm
  · rw [Nat.sub_eq_zero_of_le hm, pow_zero, Ideal.span_singleton_one]
    trivial
  obtain ⟨m, rfl⟩ : ∃ r, m = r + C := ⟨m - C, by omega⟩
  obtain ⟨Y, hY, hT, hYe⟩ := hc
  obtain ⟨σ, hσ⟩ := exists_section x.K (Ideal.span {x.t ^ (m + C)})
  obtain ⟨Y', hY', hT', rfl⟩ := exists_antisymmetric_lift_of_section _ σ hσ Y hY hT
  rw [Nat.add_sub_cancel, ← Ideal.span_singleton_pow]
  refine hC m (c, ⟨Y', hY', hT'⟩) (fun g => ?_) ((LinearMap.proj i).comp (LinearMap.fst _ _ _)) fun p hp => ?_
  · have h0 : (f g (c, ⟨Y', hY', hT'⟩)).map (x.redD k.g (m + C)) = 0 := by
      show ((∑ i, c i • z i) g - dY G.frame (fun g => k.ρ1 x.A (h.p₀ g)) Y' g).map (x.redD k.g (m + C)) = 0
      rw [Matrix.map_sub _ (map_sub _), congrFun hYe g, sub_eq_zero, dY, dY, Matrix.map_sub _ (map_sub _),
        Matrix.map_mul, Matrix.map_mul, map_first_order_lift_eq, map_first_order_lift_eq]
    choose Z hZ using fun a b => dd_ker (x.t ^ (m + C)) _ (congrFun (congrFun h0 a) b)
    have h1 : f g (c, ⟨Y', hY', hT'⟩) = x.t ^ (m + C) • Matrix.of Z := Matrix.ext hZ
    rw [h1, Ideal.span_singleton_pow]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  · exact congrFun (hind p.1 ⟨p.2, p.2.2.1, p.2.2.2, funext fun g => sub_eq_zero.1 (hp g)⟩) i
end

open IsLocalRing Matrix Filter UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

private theorem card_submodule_mul_quotient_le {A M : Type} [CommRing A] [AddCommGroup M] [Module A M] (S B : Submodule A M)
    (hBS : (B : Set M) ⊆ S) (hS : (S : Set M).Finite) (I : Ideal A) (e : ℕ) (φ : (Fin e → A) → M)
    (hφ : ∀ c, φ c ∈ S) (hsub : ∀ c c', φ (c - c') = φ c - φ c') (hI : ∀ c, φ c ∈ B → ∀ i, c i ∈ I) :
    (B : Set M).ncard * Nat.card (A ⧸ I) ^ e ≤ (S : Set M).ncard := by
  haveI : Finite (S : Set M) := hS
  choose s hs using (Ideal.Quotient.mk_surjective (I := I))
  let f : ↥(B : Set M) × (Fin e → A ⧸ I) → ↥(S : Set M) := fun p =>
    ⟨φ (fun i => s (p.2 i)) + p.1, S.add_mem (hφ _) (hBS p.1.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨b, c⟩ ⟨b', c'⟩ hh
    have h1 : φ (fun i => s (c i)) + b = φ (fun i => s (c' i)) + b' := congrArg Subtype.val hh
    have h2 : φ ((fun i => s (c i)) - fun i => s (c' i)) ∈ B := by
      rw [hsub]
      have : φ (fun i => s (c i)) - φ (fun i => s (c' i)) = (b' : M) - b := by
        rw [sub_eq_sub_iff_add_eq_add, h1, add_comm]
      rw [this]
      exact B.sub_mem b'.2 b.2
    have h3 : c = c' := by
      funext i
      rw [← hs (c i), ← hs (c' i)]
      exact Ideal.Quotient.eq.2 (hI _ h2 i)
    subst h3
    exact Prod.ext (Subtype.ext (add_left_cancel h1)) rfl
  have := Nat.card_le_card_of_injective f hf
  rwa [Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin e), Fintype.card_fin,
    Nat.card_coe_set_eq, Nat.card_coe_set_eq] at this

theorem UpperTheory.V.Pa.firstCohomologyBound_of_boundaryBound :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (D0 : ℕ), TopFG G.Γ → FirstSelmerCardBoundAtAllLevels h k D0 → K1 h k D0 := by
  intro l _ L G G0 h n x k D0 hfg hB e z hz hind
  obtain ⟨C, hC⟩ := coefficients_bounded_of_selmer_boundary l L G G0 h n x k e z hfg hz hind
  obtain ⟨C', hC'⟩ := hB
  obtain ⟨⟨S0, hS0⟩, -⟩ := sel_lin l G.frame n x.A (DD x.A k.g) x.t (fun g => k.ρ1 x.A (h.p₀ g)) (k.w1 x.A)
    (k.wi1 x.A) (W1 n x.A x.A k.g x.a)
  have hS0' : (S0 : Set _) = Sel1 h x.A k := hS0
  have key : ∀ m, (m - C) * e ≤ m * D0 + C' := by
    intro m
    obtain ⟨⟨S, hS⟩, ⟨B, hB⟩⟩ := sel_lin l G.frame n x.A (DD (x.Am m) k.g) x.t (fun g => k.ρ1 (x.Am m) (h.p₀ g))
      (k.w1 (x.Am m)) (k.wi1 (x.Am m)) (W1 n x.A (x.Am m) k.g x.a)
    have hS' : (S : Set _) = Sel1 h (x.Am m) k := hS
    have hB' : (B : Set _) = Bd1 h (x.Am m) k := hB
    obtain ⟨hfin, hle⟩ := hC' m
    have hBS := coboundary_first_subset_selmer_first l L G G0 h n x k (x.Am m)
    rw [← hS'] at hfin hle hBS
    rw [← hB'] at hle hBS
    have hc := card_submodule_mul_quotient_le S B hBS hfin (Ideal.span {x.t ^ (m - C)}) e
      (fun c g => ((∑ i, c i • z i) g).map (x.redD k.g m))
      (fun c => by
        have h1 : (∑ i, c i • z i) ∈ Sel1 h x.A k := by
          rw [← hS0']
          exact S0.sum_mem fun i _ => S0.smul_mem _ (by rw [← SetLike.mem_coe, hS0']; exact hz i)
        have h2 := (sel_red l L G G0 h n x k x.A (x.Am m) (Ideal.Quotient.mkₐ x.A _)).2.1 _ h1
        rw [← hS'] at h2
        exact h2)
      (fun c c' => by
        funext g
        ext1 a b
        simp only [Pi.sub_apply, sub_smul, Finset.sum_sub_distrib, Matrix.map_apply, Matrix.sub_apply, map_sub])
      (fun c hc => hC m c (by rw [← hB']; exact hc))
    have hcard : Nat.card (x.A ⧸ Ideal.span {x.t ^ (m - C)}) = Nat.card x.K ^ (m - C) :=
      (am_fin l G0.frame n x (m - C) 0).2.1
    have hpos : 0 < Set.ncard (SetLike.coe B) := (Set.ncard_pos (hfin.subset hBS)).2 ⟨0, B.zero_mem⟩
    rw [hcard, ← pow_mul] at hc
    have h3 := Nat.le_of_mul_le_mul_left (hc.trans hle) hpos
    exact (Nat.pow_le_pow_iff_right (am_fin l G0.frame n x 0 0).2.2.2.2.2).1 h3
  by_contra hlt
  have h1 : D0 + 1 ≤ e := by omega
  have h2 := key (C + (C * D0 + C' + 1))
  rw [Nat.add_sub_cancel_left] at h2
  have h3 := (Nat.mul_le_mul_left (C * D0 + C' + 1) h1).trans h2
  nlinarith
