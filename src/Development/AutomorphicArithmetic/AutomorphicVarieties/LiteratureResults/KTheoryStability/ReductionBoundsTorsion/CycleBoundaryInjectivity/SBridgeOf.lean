module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SBridgeAlt

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.ICyclesInjective
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.Chains
noncomputable section

open TensorProduct

namespace PositivityTheory.KB.NaturalTheta

section

variable (G : Type) [Group G]

def bdZ (m : ℕ) : ((Fin (m + 1) → G) →₀ ℤ) →ₗ[ℤ] ((Fin m → G) →₀ ℤ) :=
  Finsupp.linearCombination ℤ fun g =>
    Finsupp.single (fun i => g i.succ) 1 +
      ∑ j : Fin (m + 1), ((-1 : ℤ) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) 1

theorem bdZ_single (m : ℕ) (g : Fin (m + 1) → G) (a : ℤ) :
    bdZ G m (Finsupp.single g a) = Finsupp.single (fun i => g i.succ) a +
      ∑ j : Fin (m + 1),
        Finsupp.single (Fin.contractNth j (· * ·) g) ((-1 : ℤ) ^ ((j : ℕ) + 1) * a) := by
  simp only [bdZ, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single,
    smul_eq_mul, mul_one]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]

def eC (n : ℕ) : ℝ ⊗[ℤ] ((Fin n → G) →₀ ℤ) ≃ₗ[ℝ] Chn G n :=
  letI := Classical.decEq (Fin n → G)
  TensorProduct.finsuppScalarRight ℤ ℝ ℝ (Fin n → G)

omit [Group G] in
theorem eC_single (n : ℕ) (r : ℝ) (g : Fin n → G) (a : ℤ) :
    eC G n (r ⊗ₜ Finsupp.single g a) = Finsupp.single g ((a : ℝ) * r) := by
  letI := Classical.decEq (Fin n → G)
  ext i
  rw [eC, TensorProduct.finsuppScalarRight_apply_tmul_apply, zsmul_eq_mul]
  by_cases h : g = i
  · subst h; simp
  · simp [h]

theorem bd_eC (m : ℕ) :
    bd G m ∘ₗ (eC G (m + 1)).toLinearMap = (eC G m).toLinearMap ∘ₗ (bdZ G m).baseChange ℝ := by
  refine TensorProduct.AlgebraTensorModule.ext fun r x => ?_
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, tmul_add,
      map_add] at hx hy ⊢
    rw [hx, hy]
  | single g a =>
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.baseChange_tmul, eC_single, bdZ_single, tmul_add, tmul_sum, map_add, map_sum,
      bd, Finsupp.linearCombination_single, smul_add, Finset.smul_sum, Finsupp.smul_single,
      smul_eq_mul, mul_one]
    congr 1 <;> (try funext j) <;> congr 1 <;> push_cast <;> ring

theorem cmap_eC {H : Type} [Group H] (f : G →* H) (n : ℕ) :
    cmap f n ∘ₗ (eC G n).toLinearMap =
      (eC H n).toLinearMap ∘ₗ
        (Finsupp.lmapDomain ℤ ℤ (fun (g : Fin n → G) i => f (g i))).baseChange ℝ := by
  refine TensorProduct.AlgebraTensorModule.ext fun r x => ?_
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, tmul_add,
      map_add] at hx hy ⊢
    rw [hx, hy]
  | single g a =>
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
      LinearMap.baseChange_tmul, eC_single, cmap, Finsupp.lmapDomain_apply,
      Finsupp.mapDomain_single]

end

end PositivityTheory.KB.NaturalTheta
end
end

noncomputable section

open CategoryTheory groupHomology UpperTheory.V.KL Finsupp

namespace PositivityTheory.KB.NaturalTheta

variable (G : Type) [Group G]

def Dz (n : ℕ) : ((Fin (n + 1) → G) →₀ ℤ) →ₗ[ℤ] ((Fin n → G) →₀ ℤ) :=
  (inhomogeneousChains.d (Rep.trivial ℤ G ℤ) n).hom

theorem Dz_eq_bdZ (n : ℕ) : Dz G n = bdZ G n := by
  apply Finsupp.lhom_ext
  intro g a
  unfold Dz bdZ
  rw [inhomogeneousChains.d_single, Finsupp.linearCombination_single, smul_add, Finset.smul_sum]
  congr 1
  · simp
  · refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [smul_comm, Finsupp.smul_single_one]

theorem d_hom (n : ℕ) : ((inhomogeneousChains (Rep.trivial ℤ G ℤ)).d (n + 1) n).hom = Dz G n := by
  rw [inhomogeneousChains.d_def]; rfl

theorem Dz_Dz (n : ℕ) : Dz G n ∘ₗ Dz G (n + 1) = 0 := by
  have := congrArg ModuleCat.Hom.hom (inhomogeneousChains.d_comp_d (Rep.trivial ℤ G ℤ) n)
  simp only [ModuleCat.hom_comp, ModuleCat.hom_zero] at this
  exact this

variable (k : ℕ)

theorem hnext : (ComplexShape.down ℕ).next (k + 1) = k := by simp

theorem hlift : (ModuleCat.ofHom (LinearMap.ker (Dz G k)).subtype :
      ModuleCat.of ℤ (LinearMap.ker (Dz G k)) ⟶ (inhomogeneousChains (Rep.trivial ℤ G ℤ)).X (k + 1)) ≫
      (inhomogeneousChains (Rep.trivial ℤ G ℤ)).d (k + 1) k = 0 := by
  rw [inhomogeneousChains.d_def]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact LinearMap.mem_ker.mp x.2

def cz : LinearMap.ker (Dz G k) →ₗ[ℤ] cycles (Rep.trivial ℤ G ℤ) (k + 1) :=
  ((inhomogeneousChains (Rep.trivial ℤ G ℤ)).liftCycles
    (ModuleCat.ofHom (LinearMap.ker (Dz G k)).subtype : ModuleCat.of ℤ (LinearMap.ker (Dz G k)) ⟶ _)
    k (hnext k) (hlift G k)).hom

theorem i_cz (x : LinearMap.ker (Dz G k)) :
    (iCycles (Rep.trivial ℤ G ℤ) (k + 1)).hom (cz G k x) = x.1 := by
  have h := HomologicalComplex.liftCycles_i (inhomogeneousChains (Rep.trivial ℤ G ℤ))
    (ModuleCat.ofHom (LinearMap.ker (Dz G k)).subtype :
      ModuleCat.of ℤ (LinearMap.ker (Dz G k)) ⟶ (inhomogeneousChains (Rep.trivial ℤ G ℤ)).X (k + 1))
    k (hnext k) (hlift G k)
  have h2 := congrArg (fun φ => φ.hom x) h
  exact h2

theorem iCycles_injective (n : ℕ) : Function.Injective (iCycles (Rep.trivial ℤ G ℤ) n).hom :=
  (ModuleCat.mono_iff_injective _).1 inferInstance

def pz : LinearMap.ker (Dz G k) →ₗ[ℤ] grpH G (k + 1) :=
  (π (Rep.trivial ℤ G ℤ) (k + 1)).hom ∘ₗ cz G k

set_option backward.isDefEq.respectTransparency false in
theorem pz_surjective : Function.Surjective (pz G k) := by
  intro y
  obtain ⟨c, rfl⟩ := (ModuleCat.epi_iff_surjective (π (Rep.trivial ℤ G ℤ) (k + 1))).1 inferInstance y
  have hc : (iCycles (Rep.trivial ℤ G ℤ) (k + 1)).hom c ∈ LinearMap.ker (Dz G k) := by
    rw [LinearMap.mem_ker, ← d_hom]
    have := congrArg (fun φ => φ.hom c)
      ((inhomogeneousChains (Rep.trivial ℤ G ℤ)).iCycles_d (k + 1) k)
    simpa [ModuleCat.hom_comp] using this
  refine ⟨⟨_, hc⟩, ?_⟩
  simp only [pz, LinearMap.coe_comp, Function.comp_apply]
  congr 1
  exact iCycles_injective G (k + 1) (i_cz G k _)

theorem pz_eq_zero_iff (x : LinearMap.ker (Dz G k)) :
    pz G k x = 0 ↔ x.1 ∈ LinearMap.range (Dz G (k + 1)) := by
  set K := inhomogeneousChains (Rep.trivial ℤ G ℤ) with hK
  have hex := ShortComplex.exact_of_g_is_cokernel
    (S := ShortComplex.mk (K.toCycles (k + 2) (k + 1)) (K.homologyπ (k + 1))
      (K.toCycles_comp_homologyπ (k + 2) (k + 1)))
    (K.homologyIsCokernel (k + 2) (k + 1) (by simp))
  rw [ShortComplex.moduleCat_exact_iff] at hex
  have hti : ∀ w, (iCycles (Rep.trivial ℤ G ℤ) (k + 1)).hom ((K.toCycles (k + 2) (k + 1)).hom w)
      = Dz G (k + 1) w := by
    intro w
    have h0 := congrArg (fun φ => φ.hom w) (K.toCycles_i (k + 2) (k + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h0
    rw [← d_hom]
    exact h0
  constructor
  · intro h0
    obtain ⟨w, hw⟩ := hex (cz G k x) h0
    refine ⟨w, ?_⟩
    rw [← hti, ← i_cz G k x]
    exact congrArg _ hw
  · rintro ⟨w, hw⟩
    have hc : (K.toCycles (k + 2) (k + 1)).hom w = cz G k x := by
      apply iCycles_injective
      rw [hti, i_cz, hw]
    simp only [pz, LinearMap.comp_apply, ← hc]
    have h1 := congrArg (fun φ => φ.hom w) (K.toCycles_comp_homologyπ (k + 2) (k + 1))
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    exact h1

variable {G} {H : Type} [Group H] (f : G →* H)

theorem chainsMap_hom (n : ℕ) :
    ((chainsMap f (trivHom f)).f n).hom = Finsupp.lmapDomain ℤ ℤ (fun (g : Fin n → G) i => f (g i)) := by
  rw [chainsMap_f_hom]
  apply Finsupp.lhom_ext
  intro g a
  simp [trivHom]
  rfl

theorem map_mem_ker (x : (Fin (k + 1) → G) →₀ ℤ) (hx : x ∈ LinearMap.ker (Dz G k)) :
    Finsupp.lmapDomain ℤ ℤ (fun (g : Fin (k + 1) → G) i => f (g i)) x ∈ LinearMap.ker (Dz H k) := by
  rw [LinearMap.mem_ker] at hx ⊢
  have := congrArg (fun φ => φ.hom x) ((chainsMap f (trivHom f)).comm (k + 1) k)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
  rw [d_hom, d_hom, chainsMap_hom, chainsMap_hom] at this
  rw [this, hx, map_zero]

theorem pz_natural (x : LinearMap.ker (Dz G k)) :
    pz H k ⟨_, map_mem_ker k f x.1 x.2⟩ = (grpHMap f (k + 1)).hom (pz G k x) := by
  simp only [pz, LinearMap.coe_comp, Function.comp_apply, grpHMap]
  have := congrArg (fun φ => φ.hom (cz G k x)) (π_map f (trivHom f) (k + 1))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
  rw [this]
  congr 1
  apply iCycles_injective H (k + 1)
  rw [i_cz]
  have := congrArg (fun φ => φ.hom (cz G k x))
    (HomologicalComplex.cyclesMap_i (chainsMap f (trivHom f)) (k + 1))
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at this
  rw [this, i_cz, chainsMap_hom]

end PositivityTheory.KB.NaturalTheta
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.CycleBoundaryInjectivity.ThEqZeroIff
noncomputable section

open TensorProduct

namespace PositivityTheory.KB.NaturalTheta

section

variable {C2 C1 C0 H V2 V1 V0 : Type} [AddCommGroup C2] [AddCommGroup C1] [AddCommGroup C0]
  [AddCommGroup H] [Module ℤ H]
  [AddCommGroup V2] [AddCommGroup V1] [AddCommGroup V0]
  [Module ℝ V2] [Module ℝ V1] [Module ℝ V0]
  (d1 : C2 →ₗ[ℤ] C1) (d0 : C1 →ₗ[ℤ] C0) (p : LinearMap.ker d0 →ₗ[ℤ] H)
  (e2 : ℝ ⊗[ℤ] C2 ≃ₗ[ℝ] V2) (e1 : ℝ ⊗[ℤ] C1 ≃ₗ[ℝ] V1) (e0 : ℝ ⊗[ℤ] C0 ≃ₗ[ℝ] V0)
  (D1 : V2 →ₗ[ℝ] V1) (D0 : V1 →ₗ[ℝ] V0)

def jz : ℝ ⊗[ℤ] LinearMap.ker d0 →ₗ[ℝ] V1 :=
  e1.toLinearMap ∘ₗ (LinearMap.ker d0).subtype.baseChange ℝ

theorem jz_injective : Function.Injective (jz d0 e1) := by
  unfold jz
  rw [LinearMap.coe_comp]
  refine e1.injective.comp ?_
  rw [LinearMap.baseChange_eq_ltensor]
  exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective

theorem range_jz (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ) :
    LinearMap.range (jz d0 e1) = LinearMap.ker D0 := by
  have hex := Module.Flat.lTensor_exact ℝ (LinearMap.exact_subtype_ker_map d0)
  ext x
  constructor
  · rintro ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    have h1 := congrArg (fun f => f (((LinearMap.ker d0).subtype.baseChange ℝ) w)) h0
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1
    simp only [jz, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h1, LinearMap.baseChange_eq_ltensor, LinearMap.baseChange_eq_ltensor,
      hex.apply_apply_eq_zero w, map_zero]
  · intro hx
    rw [LinearMap.mem_ker] at hx
    obtain ⟨y, rfl⟩ := e1.surjective x
    have h1 := congrArg (fun f => f y) h0
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at h1
    rw [h1] at hx
    have hy : (d0.baseChange ℝ) y = 0 := by
      rw [← map_zero e0] at hx
      exact e0.injective hx
    rw [LinearMap.baseChange_eq_ltensor] at hy
    obtain ⟨w, hw⟩ := (hex y).mp hy
    refine ⟨w, ?_⟩
    simp only [jz, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.baseChange_eq_ltensor, hw]

def th (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ) :
    LinearMap.ker D0 →ₗ[ℝ] ℝ ⊗[ℤ] H :=
  p.baseChange ℝ ∘ₗ (LinearEquiv.ofInjective _ (jz_injective d0 e1)).symm.toLinearMap ∘ₗ
    (LinearEquiv.ofEq _ _ (range_jz d0 e1 e0 D0 h0).symm).toLinearMap

theorem th_jz (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ)
    (w : ℝ ⊗[ℤ] LinearMap.ker d0) (hw : jz d0 e1 w ∈ LinearMap.ker D0) :
    th d0 p e1 e0 D0 h0 ⟨jz d0 e1 w, hw⟩ = p.baseChange ℝ w := by
  simp only [th, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  congr 1
  rw [LinearEquiv.symm_apply_eq]
  rfl

theorem exists_jz (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ)
    (z : LinearMap.ker D0) : ∃ w, jz d0 e1 w = z.1 := by
  have hz : z.1 ∈ LinearMap.range (jz d0 e1) := by
    rw [range_jz d0 e1 e0 D0 h0]
    exact z.2
  exact LinearMap.mem_range.mp hz

theorem th_surjective (hp : Function.Surjective p)
    (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ) :
    Function.Surjective (th d0 p e1 e0 D0 h0) := by
  intro y
  have hs : Function.Surjective (p.baseChange ℝ) := by
    rw [LinearMap.baseChange_eq_ltensor]
    exact LinearMap.lTensor_surjective _ hp
  obtain ⟨w, rfl⟩ := hs y
  have hw : jz d0 e1 w ∈ LinearMap.ker D0 := by
    rw [← range_jz d0 e1 e0 D0 h0]
    exact LinearMap.mem_range_self _ w
  exact ⟨⟨jz d0 e1 w, hw⟩, th_jz d0 p e1 e0 D0 h0 w hw⟩

theorem th_eq_zero_iff (hdd : d0 ∘ₗ d1 = 0) (hker : ∀ x, p x = 0 ↔ x.1 ∈ LinearMap.range d1)
    (hp : Function.Surjective p)
    (h1 : D1 ∘ₗ e2.toLinearMap = e1.toLinearMap ∘ₗ d1.baseChange ℝ)
    (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ) (z : LinearMap.ker D0) :
    th d0 p e1 e0 D0 h0 z = 0 ↔ z.1 ∈ LinearMap.range D1 := by
  obtain ⟨zv, hzv⟩ := z
  obtain ⟨w, hw⟩ := exists_jz d0 e1 e0 D0 h0 ⟨zv, hzv⟩
  simp only at hw
  subst hw
  rw [th_jz d0 p e1 e0 D0 h0 w hzv]
  have hmem : ∀ c, d1 c ∈ LinearMap.ker d0 := fun c => by
    rw [LinearMap.mem_ker]
    simpa using LinearMap.congr_fun hdd c
  obtain ⟨g, hg⟩ : ∃ g : C2 →ₗ[ℤ] LinearMap.ker d0, (LinearMap.ker d0).subtype ∘ₗ g = d1 :=
    ⟨d1.codRestrict _ hmem, LinearMap.subtype_comp_codRestrict _ _ _⟩
  have hgx : ∀ c, ((g c : LinearMap.ker d0) : C1) = d1 c := fun c => LinearMap.congr_fun hg c
  have hexZ : Function.Exact g p := by
    intro x
    rw [hker x]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨c, Subtype.ext ((hgx c).trans hc)⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, (hgx c).symm⟩
  have hexR := lTensor_exact ℝ hexZ hp
  have key : ∀ u, jz d0 e1 (g.baseChange ℝ u) = D1 (e2 u) := by
    intro u
    simp only [jz, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← LinearMap.comp_apply ((LinearMap.ker d0).subtype.baseChange ℝ),
      ← LinearMap.baseChange_comp, hg]
    have := LinearMap.congr_fun h1 u
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    exact this.symm
  rw [LinearMap.baseChange_eq_ltensor, hexR w]
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨e2 u, ?_⟩
    rw [← key u, LinearMap.baseChange_eq_ltensor]
  · rintro ⟨v, hv⟩
    obtain ⟨u, rfl⟩ := e2.surjective v
    refine ⟨u, ?_⟩
    apply jz_injective d0 e1
    rw [← LinearMap.baseChange_eq_ltensor, key u, hv]

end

section Nat

variable {C1 C0 H V1 V0 C1' C0' H' V1' V0' : Type} [AddCommGroup C1] [AddCommGroup C0]
  [AddCommGroup H] [AddCommGroup V1] [AddCommGroup V0] [Module ℝ V1] [Module ℝ V0]
  [AddCommGroup C1'] [AddCommGroup C0'] [AddCommGroup H'] [AddCommGroup V1'] [AddCommGroup V0']
  [Module ℤ H] [Module ℤ H']
  [Module ℝ V1'] [Module ℝ V0']
  (d0 : C1 →ₗ[ℤ] C0) (p : LinearMap.ker d0 →ₗ[ℤ] H)
  (e1 : ℝ ⊗[ℤ] C1 ≃ₗ[ℝ] V1) (e0 : ℝ ⊗[ℤ] C0 ≃ₗ[ℝ] V0) (D0 : V1 →ₗ[ℝ] V0)
  (d0' : C1' →ₗ[ℤ] C0') (p' : LinearMap.ker d0' →ₗ[ℤ] H')
  (e1' : ℝ ⊗[ℤ] C1' ≃ₗ[ℝ] V1') (e0' : ℝ ⊗[ℤ] C0' ≃ₗ[ℝ] V0') (D0' : V1' →ₗ[ℝ] V0')

theorem th_natural (h0 : D0 ∘ₗ e1.toLinearMap = e0.toLinearMap ∘ₗ d0.baseChange ℝ)
    (h0' : D0' ∘ₗ e1'.toLinearMap = e0'.toLinearMap ∘ₗ d0'.baseChange ℝ)
    (c1 : C1 →ₗ[ℤ] C1') (q : H →ₗ[ℤ] H') (F : V1 →ₗ[ℝ] V1')
    (hF : F ∘ₗ e1.toLinearMap = e1'.toLinearMap ∘ₗ c1.baseChange ℝ)
    (hc : ∀ x ∈ LinearMap.ker d0, c1 x ∈ LinearMap.ker d0')
    (hq : ∀ x : LinearMap.ker d0, p' ⟨c1 x, hc x x.2⟩ = q (p x))
    (z : LinearMap.ker D0) (z' : LinearMap.ker D0') (hz : z'.1 = F z.1) :
    th d0' p' e1' e0' D0' h0' z' = q.baseChange ℝ (th d0 p e1 e0 D0 h0 z) := by
  obtain ⟨zv, hzv⟩ := z
  obtain ⟨w, hw⟩ := exists_jz d0 e1 e0 D0 h0 ⟨zv, hzv⟩
  simp only at hw
  subst hw
  obtain ⟨zv', hzv'⟩ := z'
  simp only at hz
  subst hz
  rw [th_jz d0 p e1 e0 D0 h0 w hzv]
  have hcomp : c1 ∘ₗ (LinearMap.ker d0).subtype
      = (LinearMap.ker d0').subtype ∘ₗ c1.restrict hc := LinearMap.ext fun x => rfl
  have hj : F (jz d0 e1 w) = jz d0' e1' ((c1.restrict hc).baseChange ℝ w) := by
    simp only [jz, LinearMap.comp_apply, LinearEquiv.coe_coe]
    have := LinearMap.congr_fun hF ((LinearMap.ker d0).subtype.baseChange ℝ w)
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at this
    rw [this, ← LinearMap.comp_apply (c1.baseChange ℝ), ← LinearMap.baseChange_comp, hcomp,
      LinearMap.baseChange_comp, LinearMap.comp_apply]
  have hmem : jz d0' e1' ((c1.restrict hc).baseChange ℝ w) ∈ LinearMap.ker D0' := hj ▸ hzv'
  have heq : (⟨F (jz d0 e1 w), hzv'⟩ : LinearMap.ker D0')
      = ⟨jz d0' e1' ((c1.restrict hc).baseChange ℝ w), hmem⟩ := Subtype.ext hj
  rw [heq, th_jz d0' p' e1' e0' D0' h0' _ hmem, ← LinearMap.comp_apply (p'.baseChange ℝ),
    ← LinearMap.baseChange_comp, ← LinearMap.comp_apply (q.baseChange ℝ),
    ← LinearMap.baseChange_comp]
  rw [show p' ∘ₗ c1.restrict hc = q ∘ₗ p from LinearMap.ext fun x => hq x]

end Nat

end PositivityTheory.KB.NaturalTheta
end
end

noncomputable section

open UpperTheory.V.KL
open scoped TensorProduct

namespace PositivityTheory.KB

open NaturalTheta in
theorem sBridge_of : SBridge := by
  intro k
  have h0 : ∀ (G : Type) [Group G] (m : ℕ),
      bd G m ∘ₗ (eC G (m + 1)).toLinearMap = (eC G m).toLinearMap ∘ₗ (Dz G m).baseChange ℝ :=
    fun G _ m => by rw [Dz_eq_bdZ]; exact bd_eC G m
  refine ⟨fun G _ => th (Dz G k) (pz G k) (eC G (k + 1)) (eC G k) (bd G k) (h0 G k), ?_, ?_, ?_⟩
  · intro G _
    exact th_surjective _ _ _ _ _ (pz_surjective G k) _
  · intro G _ z
    exact th_eq_zero_iff (Dz G (k + 1)) (Dz G k) (pz G k) (eC G (k + 2)) (eC G (k + 1)) (eC G k)
      (bd G (k + 1)) (bd G k) (Dz_Dz G k) (pz_eq_zero_iff G k) (pz_surjective G k) (h0 G (k + 1))
      (h0 G k) z
  · intro G H _ _ f z z' hz
    exact th_natural _ _ _ _ _ _ _ _ _ _ (h0 G k) (h0 H k) _ _ _ (cmap_eC G f (k + 1))
      (map_mem_ker k f) (pz_natural k f) z z' hz

end PositivityTheory.KB
