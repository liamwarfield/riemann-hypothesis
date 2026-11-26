module

public import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
public import Formalism.HermitianLattices.DefsCS
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjLevel
public import Formalism.SuccessiveMinima.SuccessiveMinimaProofs.GjScale

@[expose] public section

section -- merged from Formalism.HermitianLattices.HermitianLatticesProofs.LocDual
noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem locDual_mem_dualAt (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (x : V) :
    x ∈ dualAt h p L ↔ ∀ y ∈ L, h y x ∈ locR (K := K) p := by
  simp only [dualAt, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]

theorem locDual_mem_locR (p : Ideal R) (k : K) :
    k ∈ locR (K := K) p ↔
      ∃ s ∈ hcompl (K := K) p, algebraMap R K s * k ∈ (1 : Submodule R K) := by
  show (∃ s ∈ hcompl (K := K) p, s • k ∈ (1 : Submodule R K)) ↔ _
  simp only [Algebra.smul_def]

theorem locDual_h_smul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (y x : V) :
    h y (r • x) = algebraMap R K r * h y x := by
  rw [← algebraMap_smul K r x, map_smul, smul_eq_mul]

theorem locDual_h_smul_left (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (y x : V) :
    h (r • y) x = star (algebraMap R K r) * h y x := by
  rw [← algebraMap_smul K r y, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    starRingEnd_apply]

theorem locDual_one_mul {a b : K} (ha : a ∈ (1 : Submodule R K)) (hb : b ∈ (1 : Submodule R K)) :
    a * b ∈ (1 : Submodule R K) := by
  simpa using Submodule.mul_mem_mul ha hb

theorem locDual_alg_mem (r : R) : algebraMap R K r ∈ (1 : Submodule R K) :=
  Submodule.algebraMap_mem r

theorem locDual_dualAt_anti (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) {L M : Submodule R V}
    (hLM : L ≤ M) : dualAt h p M ≤ dualAt h p L := by
  intro x hx
  rw [locDual_mem_dualAt] at hx ⊢
  exact fun y hy => hx y (hLM hy)

private theorem mem_dual_iff_forall_mem_one (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

theorem locDual_loc_dual_le (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) :
    loc (K := K) p (dual h L) ≤ dualAt h p L := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ : ∃ s ∈ hcompl (K := K) p, s • x ∈ dual h L := hx
  rw [mem_dual_iff_forall_mem_one] at hsx
  rw [locDual_mem_dualAt]
  intro y hy
  rw [locDual_mem_locR]
  refine ⟨s, hs, ?_⟩
  rw [← locDual_h_smul_right]
  exact hsx y hy

theorem locDual_dualAt_le (h : V →ₗ⋆[K] V →ₗ[K] K)
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (L : Submodule R V) (hL : L.FG) :
    dualAt h p L ≤ loc (K := K) p (dual h L) := by
  classical
  intro x hx
  rw [locDual_mem_dualAt] at hx
  obtain ⟨t, rfl⟩ := hL
  have hloc : ∀ y ∈ t, ∃ s ∈ hcompl (K := K) p,
      algebraMap R K s * h y x ∈ (1 : Submodule R K) :=
    fun y hy => (locDual_mem_locR p _).mp (hx y (Submodule.subset_span hy))
  choose! s hs hsy using hloc
  refine ⟨∏ y ∈ t, s y, Submonoid.prod_mem _ (fun y hy => hs y hy), ?_⟩
  rw [mem_dual_iff_forall_mem_one]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [locDual_h_smul_right, ← Finset.mul_prod_erase t s hy, map_mul,
      mul_comm (algebraMap R K (s y)), mul_assoc]
    exact locDual_one_mul (locDual_alg_mem _) (hsy y hy)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [map_add (f := _), LinearMap.add_apply]
    exact Submodule.add_mem _ hy hz
  | smul r y _ hy =>
    rw [locDual_h_smul_left]
    obtain ⟨u, hu⟩ := hstar r
    rw [← hu]
    exact locDual_one_mul (locDual_alg_mem u) hy

theorem locDual_sigma_mem (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K)) (p : Ideal R)
    (s : R) (hs : s ∈ hcompl (K := K) p) :
    locBasic_sigma hinj hstar s ∈ hcompl (K := K) p := by
  have spec : ∀ r : R, algebraMap R K (locBasic_sigma hinj hstar r) = star (algebraMap R K r) :=
    fun r => (hstar r).choose_spec
  unfold hcompl at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem s hs =>
    apply Submonoid.subset_closure
    obtain ⟨hs1, hs2⟩ := hs
    refine ⟨hs2 _ (spec s), fun t ht => ?_⟩
    rw [spec, star_star] at ht
    rw [hinj ht]
    exact hs1
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul a b _ _ ha hb => rw [map_mul]; exact Submonoid.mul_mem _ ha hb

theorem locDual_dualAt_loc (h : V →ₗ⋆[K] V →ₗ[K] K) (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (L : Submodule R V) :
    dualAt h p (loc (K := K) p L) = dualAt h p L := by
  apply le_antisymm
  · apply locDual_dualAt_anti
    intro y hy
    show ∃ s ∈ hcompl (K := K) p, s • y ∈ L
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hy⟩
  · intro x hx
    rw [locDual_mem_dualAt] at hx ⊢
    intro y hy
    obtain ⟨s, hs, hsy⟩ : ∃ s ∈ hcompl (K := K) p, s • y ∈ L := hy
    have h1 := hx _ hsy
    rw [locDual_h_smul_left, locDual_mem_locR] at h1
    obtain ⟨t, ht, hty⟩ := h1
    rw [locDual_mem_locR]
    refine ⟨t * locBasic_sigma hinj hstar s,
      Submonoid.mul_mem _ ht (locDual_sigma_mem hinj hstar p s hs), ?_⟩
    have spec : algebraMap R K (locBasic_sigma hinj hstar s) = star (algebraMap R K s) :=
      (hstar s).choose_spec
    rw [map_mul, spec, mul_assoc]
    exact hty

end SlopeTestRemainingChoices

theorem locDual : LocDual := by
  intro R K V _ _ _ _ _ _ _ _ _ _ h _ hstar L hL
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have key : ∀ p : Ideal R, loc (K := K) p (dual h L) = dualAt h p L := fun p =>
    le_antisymm (locDual_loc_dual_le h p L) (locDual_dualAt_le h hstar p L hL)
  have key2 : ∀ p : Ideal R, dualAt h p (loc (K := K) p L) = dualAt h p L :=
    fun p => locDual_dualAt_loc h hinj hstar p L
  refine ⟨fun p _ => ⟨key p, key2 p⟩, ?_⟩
  unfold IsUnimodular IsUnimodularAt
  constructor
  · intro hu p _
    rw [key2, ← key, hu]
  · intro H
    have H' : ∀ p : Ideal R, p.IsMaximal → loc (K := K) p (dual h L) = loc (K := K) p L := by
      intro p hp
      rw [key, ← key2]
      exact H p hp

    have avoid : ∀ p : Ideal R, p.IsPrime → ∀ s ∈ hcompl (K := K) p, s ∉ p := by
      intro p hp s hs
      unfold hcompl at hs
      induction hs using Submonoid.closure_induction with
      | mem s hs => exact hs.1
      | one => exact (Ideal.ne_top_iff_one p).mp hp.ne_top
      | mul a b _ _ ha hb => exact fun hab => (hp.mem_or_mem hab).elim ha hb

    have incl : ∀ M N : Submodule R V,
        (∀ p : Ideal R, p.IsMaximal → loc (K := K) p M = loc (K := K) p N) → N ≤ M := by
      intro M N hMN x hx
      by_contra hxM
      let I : Ideal R := M.comap (LinearMap.toSpanSingleton R V x)
      have hI : I ≠ ⊤ := by
        intro hI
        apply hxM
        have h1 : (1 : R) ∈ I := hI ▸ Submodule.mem_top
        simpa [I] using h1
      obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
      have hxN : x ∈ loc (K := K) m N := by
        show ∃ s ∈ hcompl (K := K) m, s • x ∈ N
        exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact hx⟩
      rw [← hMN m hm] at hxN
      obtain ⟨s, hs, hsx⟩ : ∃ s ∈ hcompl (K := K) m, s • x ∈ M := hxN
      exact avoid m hm.isPrime s hs (hIm (Submodule.mem_comap.mpr (by simpa using hsx)))
    exact le_antisymm (incl _ _ (fun p hp => (H' p hp).symm)) (incl _ _ H')

end Formalism.HermitianLatticesTheory
end
end

section -- merged from Formalism.HermitianLattices.HermitianLatticesProofs.GenusBasic
noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem genusBasic_gmap_one (L : Submodule R V) : gmap (1 : V ≃ₗ[K] V) L = L := by
  ext x
  rw [isomAct_mem_gmap]
  first
  | rfl
  | simp
  | exact Iff.rfl

theorem genusBasic_gmap_mul (g₁ g₂ : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap (g₂ * g₁) L = gmap g₂ (gmap g₁ L) := by
  ext x
  simp only [isomAct_mem_gmap]
  rfl

theorem genusBasic_gmap_inv (g : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap g⁻¹ (gmap g L) = L := by
  first
  | exact isomAct_gmap_symm g L
  | (ext x; simp only [isomAct_mem_gmap]; simp)

theorem genusBasic_mem_one_mul (x : K) (hx : x ∈ (1 : Submodule R K)) (r : R) :
    algebraMap R K r * x ∈ (1 : Submodule R K) := by
  rw [← Algebra.smul_def]
  exact Submodule.smul_mem _ r hx

theorem genusBasic_hsmul_right (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (v w : V) :
    h v (r • w) = algebraMap R K r * h v w := by
  rw [← algebraMap_smul K r w, map_smul, smul_eq_mul]

theorem genusBasic_hsmul_left (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (r : R) (v w : V) :
    h (r • v) w = algebraMap R K (locBasic_sigma hinj hstar r) * h v w := by
  rw [← algebraMap_smul K r v, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul,
    locBasic_sigma_spec, starRingEnd_apply]

theorem genusBasic_sigma_mem (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (p : Ideal R) (s : R) (hs : s ∈ hcompl (K := K) p) :
    locBasic_sigma hinj hstar s ∈ hcompl (K := K) p := by
  unfold hcompl at hs ⊢
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨hx1, hx2⟩ := hx
    refine Submonoid.subset_closure (Set.mem_setOf.2 ⟨hx2 _ (locBasic_sigma_spec hinj hstar x), fun t ht => ?_⟩)
    have e : t = x := hinj (by rw [ht, locBasic_sigma_spec, star_star])
    rw [e]
    exact hx1
  | one => rw [map_one]; exact Submonoid.one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact Submonoid.mul_mem _ hx hy

theorem genusBasic_hS (p : Ideal R) (hp : p.IsMaximal) (s : R) (hs : s ∈ hcompl (K := K) p) :
    s ∉ p := by
  haveI := hp.isPrime
  exact locBasic_hcompl_not_mem p s hs

theorem genusBasic_lg {W : Type*} [AddCommGroup W] [Module R W] (L : Submodule R W) (x : W)
    (hx : ∀ p : Ideal R, p.IsMaximal → x ∈ loc (K := K) p L) : x ∈ L := locBasic_lg (fun p => hcompl (K := K) p) (fun p hp s hs => genusBasic_hS p hp s hs) L x hx

theorem genusBasic_common (S : Submonoid R) (s : Finset V) (f : V → K)
    (hf : ∀ v ∈ s, ∃ u ∈ S, algebraMap R K u * f v ∈ (1 : Submodule R K)) :
    ∃ u ∈ S, ∀ v ∈ s, algebraMap R K u * f v ∈ (1 : Submodule R K) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, S.one_mem, fun v hv => by simp at hv⟩
  | @insert a s ha ih =>
    obtain ⟨u, hu, hus⟩ := ih (fun v hv => hf v (Finset.mem_insert_of_mem hv))
    obtain ⟨w, hw, hwa⟩ := hf a (Finset.mem_insert_self a s)
    refine ⟨u * w, S.mul_mem hu hw, fun v hv => ?_⟩
    rcases Finset.mem_insert.1 hv with rfl | hv
    · rw [map_mul, mul_assoc]
      exact genusBasic_mem_one_mul _ hwa u
    · rw [map_mul, mul_comm (algebraMap R K u), mul_assoc]
      exact genusBasic_mem_one_mul _ (hus v hv) w

theorem genusBasic_loc_dual (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (p : Ideal R) (L : Submodule R V) (hL : L.FG) (z : V)
    (hz : ∀ v ∈ L, h v z ∈ loc (K := K) p (1 : Submodule R K)) :
    z ∈ loc (K := K) p (dual h L) := by
  obtain ⟨gens, rfl⟩ := hL
  have hgen : ∀ v ∈ gens, ∃ u ∈ hcompl (K := K) p,
      algebraMap R K u * h v z ∈ (1 : Submodule R K) := by
    intro v hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 (hz v (Submodule.subset_span hv))
    exact ⟨s, hs, by rw [← Algebra.smul_def]; exact hsv⟩
  obtain ⟨u, hu, hall⟩ := genusBasic_common (hcompl (K := K) p) gens (fun v => h v z) hgen
  refine locBasic_mem_locS.2 ⟨u, hu, ?_⟩
  rw [dualBasic_mem_dual]
  intro y hy
  rw [genusBasic_hsmul_right]
  induction hy using Submodule.span_induction with
  | mem x hx => exact hall x hx
  | zero => simp
  | add x y _ _ hx hy =>
    rw [map_add (f := _), LinearMap.add_apply, mul_add]
    exact Submodule.add_mem _ hx hy
  | smul r x _ hx =>
    rw [genusBasic_hsmul_left hinj hstar, mul_left_comm]
    exact genusBasic_mem_one_mul _ hx _

theorem genusBasic_symm (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V)
    (hLM : SameGenus h L M) : SameGenus h M L := by
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  exact ⟨g⁻¹, (isom h).inv_mem hg, by rw [← hgL, genusBasic_gmap_inv]⟩

theorem genusBasic_int (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLM : SameGenus h L M)
    (hL : IsIntegralLat h L) : IsIntegralLat h M := by
  intro x hx y hy
  apply genusBasic_lg (K := K) (1 : Submodule R K) (h x y)
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  have hx' : x ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hx
  have hy' : y ∈ gmap g (loc (K := K) p L) := by
    rw [hgL]
    exact locBasic_le_locS _ _ hy
  rw [isomAct_mem_gmap] at hx' hy'
  obtain ⟨s, hs, hsx⟩ := locBasic_mem_locS.1 hx'
  obtain ⟨t, ht, hty⟩ := locBasic_mem_locS.1 hy'
  have hiso : h (g.symm x) (g.symm y) = h x y := by
    have e := hg (g.symm x) (g.symm y)
    simpa using e.symm
  refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s * t,
    Submonoid.mul_mem _ (genusBasic_sigma_mem hinj hstar p s hs) ht, ?_⟩
  have h1 := hL _ hsx _ hty
  rw [genusBasic_hsmul_left hinj hstar, genusBasic_hsmul_right, hiso] at h1
  rw [Algebra.smul_def, map_mul]
  convert h1 using 1
  ring

theorem genusBasic_dual_le (hinj : Function.Injective (algebraMap R K))
    (hstar : ∀ r : R, star (algebraMap R K r) ∈ Set.range (algebraMap R K))
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L M : Submodule R V) (hLfg : L.FG) (hLM : SameGenus h L M)
    (hL : IsUnimodular h L) : dual h M ≤ M := by
  intro z hz
  rw [dualBasic_mem_dual] at hz
  apply genusBasic_lg (K := K) M z
  intro p hp
  obtain ⟨g, hg, hgL⟩ := hLM p hp
  rw [← hgL, isomAct_mem_gmap]
  have hmem : g.symm z ∈ loc (K := K) p (dual h L) := by
    apply genusBasic_loc_dual hinj hstar h p L hLfg
    intro v hv
    have hgv : g v ∈ loc (K := K) p M := by
      rw [← hgL, isomAct_mem_gmap, LinearEquiv.symm_apply_apply]
      exact locBasic_le_locS _ _ hv
    obtain ⟨s, hs, hsv⟩ := locBasic_mem_locS.1 hgv
    have h1 := hz _ hsv
    rw [genusBasic_hsmul_left hinj hstar] at h1
    have hiso : h (g v) z = h v (g.symm z) := by
      have e := hg v (g.symm z)
      simpa using e
    refine locBasic_mem_locS.2 ⟨locBasic_sigma hinj hstar s,
      genusBasic_sigma_mem hinj hstar p s hs, ?_⟩
    rw [Algebra.smul_def, ← hiso]
    exact h1
  rwa [show dual h L = L from hL] at hmem

end SlopeTestRemainingChoices

theorem genusBasic : GenusBasic := by
  intro R K V _ _ _ _ _ _ _ _ _ _ h _ hstar
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hint_of : ∀ L : Submodule R V, IsUnimodular h L → IsIntegralLat h L := by
    intro L hL x hx y hy
    have hy' : y ∈ dual h L := by
      rw [show dual h L = L from hL]
      exact hy
    exact (dualBasic_mem_dual h L y).1 hy' x hx
  have hle_dual : ∀ L : Submodule R V, IsIntegralLat h L → L ≤ dual h L := by
    intro L hL y hy
    exact (dualBasic_mem_dual h L y).2 fun x hx => hL x hx y hy
  refine ⟨⟨fun L p hp => ⟨1, (isom h).one_mem, by rw [genusBasic_gmap_one]⟩,
    fun {L M} hLM => genusBasic_symm h L M hLM, fun {L M N} h1 h2 p hp => ?_⟩, ?_, ?_⟩
  · obtain ⟨g₁, hg₁, e₁⟩ := h1 p hp
    obtain ⟨g₂, hg₂, e₂⟩ := h2 p hp
    exact ⟨g₂ * g₁, (isom h).mul_mem hg₂ hg₁, by rw [genusBasic_gmap_mul, e₁, e₂]⟩
  · intro L g hg p hp
    refine ⟨g, hg, ?_⟩
    ext x
    simp only [loc, isomAct_mem_gmap, locBasic_mem_locS, isomAct_smul]
  · intro L M hL hM hLM
    have hML := genusBasic_symm h L M hLM
    refine ⟨⟨fun hU => ?_, fun hU => ?_⟩,
      ⟨genusBasic_int hinj hstar h L M hLM, genusBasic_int hinj hstar h M L hML⟩⟩
    · exact le_antisymm (genusBasic_dual_le hinj hstar h L M hL hLM hU)
        (hle_dual M (genusBasic_int hinj hstar h L M hLM (hint_of L hU)))
    · exact le_antisymm (genusBasic_dual_le hinj hstar h M L hM hML hU)
        (hle_dual L (genusBasic_int hinj hstar h M L hML (hint_of M hU)))

end Formalism.HermitianLatticesTheory
end
end

section -- merged from Formalism.HermitianLattices.HermitianLatticesProofs.FinIntermediate
namespace Formalism.HermitianLatticesTheory

theorem finIntermediate : FinIntermediate := by
  intro W _ P Q hPQ hfin

  let f : AddSubgroup W → AddSubgroup (Q ⧸ P.addSubgroupOf Q) := fun M =>
    (M.addSubgroupOf Q).map (QuotientAddGroup.mk' (P.addSubgroupOf Q))
  haveI : Finite (AddSubgroup (Q ⧸ P.addSubgroupOf Q)) :=
    Finite.of_injective (β := Set (Q ⧸ P.addSubgroupOf Q))
      (fun H : AddSubgroup (Q ⧸ P.addSubgroupOf Q) => (H : Set (Q ⧸ P.addSubgroupOf Q)))
      SetLike.coe_injective
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M hM N hN hMN
  have key : ∀ M : AddSubgroup W, P ≤ M → M ≤ Q →
      (f M).comap (QuotientAddGroup.mk' (P.addSubgroupOf Q)) = M.addSubgroupOf Q := by
    intro M hPM _
    simp only [f]
    rw [AddSubgroup.comap_map_eq, QuotientAddGroup.ker_mk']
    exact sup_eq_left.mpr fun x hx =>
      AddSubgroup.mem_addSubgroupOf.mpr (hPM (AddSubgroup.mem_addSubgroupOf.mp hx))
  have h1 : M.addSubgroupOf Q = N.addSubgroupOf Q := by
    rw [← key M hM.1 hM.2, ← key N hN.1 hN.2, hMN]
  have h2 : ∀ M : AddSubgroup W, M ≤ Q → (M.addSubgroupOf Q).map Q.subtype = M := by
    intro M hMQ
    rw [AddSubgroup.addSubgroupOf_map_subtype, inf_eq_left.mpr hMQ]
  rw [← h2 M hM.2, ← h2 N hN.2, h1]

end Formalism.HermitianLatticesTheory
end

section -- merged from Formalism.HermitianLattices.HermitianLatticesProofs.IsomOfTrace
open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

theorem isomOfTrace : IsomOfTrace := by
  intro K V _ _ _ _ _ h g hg
  show ∀ x y, h (g x) (g y) = h x y
  intro x y
  by_contra hne
  have hd : h (g x) (g y) - h x y ≠ 0 := sub_ne_zero.mpr hne
  have key := hg x ((h (g x) (g y) - h x y)⁻¹ • y)
  simp only [map_smul, smul_eq_mul] at key
  have h0 : Algebra.trace ℚ K ((h (g x) (g y) - h x y)⁻¹ * (h (g x) (g y) - h x y)) = 0 := by
    rw [mul_sub, map_sub, key, sub_self]
  rw [inv_mul_cancel₀ hd] at h0
  have h1 : Algebra.trace ℚ K (1 : K) = (Module.finrank ℚ K : ℚ) := by
    rw [← map_one (algebraMap ℚ K), Algebra.trace_algebraMap, nsmul_eq_mul, mul_one]
  rw [h1] at h0
  have hpos : 0 < Module.finrank ℚ K := Module.finrank_pos
  exact absurd h0 (by exact_mod_cast hpos.ne')

end Formalism.HermitianLatticesTheory
end
end

section -- merged from Formalism.HermitianLattices.HermitianLatticesProofs.DualOrthSum
noncomputable section

namespace Formalism.HermitianLatticesTheory

private theorem mem_dual_iff_hermitian_lattices {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

theorem dualOrthSum : DualOrthSum := by
  intro R K V _ _ _ _ _ _ _ _ h V₁ V₂ hc h12 h21 L₁ L₂ hL₁ hL₂
  apply le_antisymm
  · intro x hx
    rw [mem_dual_iff_hermitian_lattices] at hx
    have htop : x ∈ V₁ ⊔ V₂ := by
      rw [hc.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Submodule.mem_sup.mp htop
    refine Submodule.mem_sup.mpr ⟨x₁, Submodule.mem_inf.mpr ⟨?_, hx₁⟩,
      x₂, Submodule.mem_inf.mpr ⟨?_, hx₂⟩, rfl⟩
    · rw [mem_dual_iff_hermitian_lattices]
      intro y hy
      have e : h y x₂ = 0 := h12 y (hL₁ hy) x₂ hx₂
      have hm := hx y (Submodule.mem_sup_left hy)
      rwa [map_add, e, add_zero] at hm
    · rw [mem_dual_iff_hermitian_lattices]
      intro y hy
      have e : h y x₁ = 0 := h21 y (hL₂ hy) x₁ hx₁
      have hm := hx y (Submodule.mem_sup_right hy)
      rwa [map_add, e, zero_add] at hm
  · refine sup_le ?_ ?_
    · intro x hx
      obtain ⟨hxd, hxV⟩ := Submodule.mem_inf.mp hx
      rw [mem_dual_iff_hermitian_lattices] at hxd ⊢
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add (f := _), LinearMap.add_apply, h21 y₂ (hL₂ hy₂) x hxV, add_zero]
      exact hxd y₁ hy₁
    · intro x hx
      obtain ⟨hxd, hxV⟩ := Submodule.mem_inf.mp hx
      rw [mem_dual_iff_hermitian_lattices] at hxd ⊢
      intro y hy
      obtain ⟨y₁, hy₁, y₂, hy₂, rfl⟩ := Submodule.mem_sup.mp hy
      rw [map_add (f := _), LinearMap.add_apply, h12 y₁ (hL₁ hy₁) x hxV, zero_add]
      exact hxd y₂ hy₂

end Formalism.HermitianLatticesTheory
end
end

section -- merged from Formalism.HermitianLattices.HermitianLatticesProofs.ShortVectors
section -- merged from Formalism.SuccessiveMinima.MinkowskiIIUpper
namespace Formalism.FN

theorem minkowskiIIUpper : MinkowskiIIUpper :=
  minkowskiIIUpper_of (minkCore_of partialBoxVolumeMonotoneStep partialBoxVolumeScaling) existsSuccessiveMinimaVectors
    existsAdaptedBasis

end Formalism.FN
end

open MeasureTheory Module Metric Set
open scoped Pointwise

noncomputable section

namespace Formalism.HermitianLatticesTheory

private lemma shortVectors_norm_le {N : ℕ} {t : ℝ} (ht : 0 < t) {u : EuclideanSpace ℝ (Fin N)}
    (hu : u ∈ t • closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) : ‖u‖ ≤ t := by
  obtain ⟨v, hv, rfl⟩ := hu
  rw [mem_closedBall_zero_iff] at hv
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  exact mul_le_of_le_one_right ht.le hv

private lemma shortVectors_prod_ge {n : ℕ} {c : ℝ} (hc : 0 < c) (lam : Fin n → ℝ)
    (hlow : ∀ i, c ≤ lam i) (j : Fin n) : lam j * c ^ (n - 1) ≤ ∏ i, lam i := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ lam (Finset.mem_univ j)]
  have hcard : (Finset.univ.erase j).card = n - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
  have h1 : c ^ (n - 1) ≤ ∏ i ∈ Finset.univ.erase j, lam i := by
    rw [← hcard, ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun i _ => hc.le) (fun i _ => hlow i)
  have hj : 0 ≤ lam j := le_trans hc.le (hlow j)
  exact mul_le_mul_of_nonneg_left h1 hj

private lemma shortVectors_vol_pos (N : ℕ) :
    0 < volume.real (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := by
  show 0 < (volume (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)).toReal
  exact ENNReal.toReal_pos (measure_closedBall_pos volume _ one_pos).ne' measure_closedBall_lt_top.ne

theorem shortVectors : ShortVectors := by
  intro N c C hc
  refine ⟨2 ^ finrank ℝ (EuclideanSpace ℝ (Fin N)) * C /
      (volume.real (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) *
        c ^ (finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1)), ?_⟩
  intro Λ _ _ hmin hcov
  have hK : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := isCompact_closedBall 0 1
  have hconv : Convex ℝ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := convex_closedBall 0 1
  have hsym : ∀ x ∈ closedBall (0 : EuclideanSpace ℝ (Fin N)) 1,
      -x ∈ closedBall (0 : EuclideanSpace ℝ (Fin N)) 1 := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    rwa [norm_neg]
  have hint : (0 : EuclideanSpace ℝ (Fin N)) ∈
      interior (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) := by
    rw [interior_closedBall _ one_ne_zero]
    exact mem_ball_self one_pos
  obtain ⟨v, hli, hvL, hvK, hpos, -, -⟩ := Formalism.FN.existsSuccessiveMinimaVectors Λ _ hK hconv hsym hint
  have hM := Formalism.FN.minkowskiIIUpper (volume : Measure (EuclideanSpace ℝ (Fin N))) Λ _
    hK hconv hsym hint
  have hV := shortVectors_vol_pos N
  have hlow : ∀ i : Fin (finrank ℝ (EuclideanSpace ℝ (Fin N))), c ≤ Formalism.FN.succMin Λ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)
      ((i : ℕ) + 1) := by
    intro i
    exact le_trans (hmin _ (hvL i) (hli.ne_zero i)) (shortVectors_norm_le (hpos i) (hvK i))
  have hN : finrank ℝ (EuclideanSpace ℝ (Fin N)) = N := finrank_euclideanSpace_fin
  refine ⟨fun i => v (Fin.cast hN.symm i), fun i => hvL _,
    hli.comp _ (Fin.cast_injective _), fun i => ?_⟩
  refine le_trans (shortVectors_norm_le (hpos _) (hvK _)) ?_
  have hcp : 0 < c ^ (finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1) := pow_pos hc _
  rw [le_div_iff₀ (mul_pos hV hcp)]
  have h1 := shortVectors_prod_ge hc
    (fun i => Formalism.FN.succMin Λ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) ((i : ℕ) + 1))
    hlow (Fin.cast hN.symm i)
  have h2 : (2 : ℝ) ^ finrank ℝ (EuclideanSpace ℝ (Fin N)) * ZLattice.covolume Λ ≤
      2 ^ finrank ℝ (EuclideanSpace ℝ (Fin N)) * C :=
    mul_le_mul_of_nonneg_left hcov (by positivity)
  have h3 := mul_le_mul_of_nonneg_left h1 hV.le
  calc _ = volume.real (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1) *
        (Formalism.FN.succMin Λ (closedBall (0 : EuclideanSpace ℝ (Fin N)) 1)
          ((Fin.cast hN.symm i : ℕ) + 1) * c ^ (finrank ℝ (EuclideanSpace ℝ (Fin N)) - 1)) := by
        ring
    _ ≤ _ := h3
    _ ≤ _ := hM
    _ ≤ _ := h2

end Formalism.HermitianLatticesTheory
end
end

section -- merged from Formalism.HermitianLattices.HermitianLatticesProofs.NeighbourConstruct
noncomputable section

open nonZeroDivisors

namespace Formalism.HermitianLatticesTheory

section Gen

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem neighbourConstruct_mem_inv {P : Ideal R} {a : K} :
    a ∈ invIdeal (K := K) P ↔ ∀ p ∈ P, algebraMap R K p * a ∈ Set.range (algebraMap R K) := by
  unfold invIdeal
  simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.mulLeft_apply, Submodule.mem_one]
  rfl

theorem neighbourConstruct_mem_span {P : Ideal R} {x z : V} :
    z ∈ Submodule.span R {z | ∃ a ∈ invIdeal (K := K) P, z = a • x} ↔
      ∃ a ∈ invIdeal (K := K) P, z = a • x := by
  constructor
  · intro hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hy
    | zero => exact ⟨0, Submodule.zero_mem _, by simp⟩
    | add y y' _ _ h1 h2 =>
      obtain ⟨a, ha, rfl⟩ := h1
      obtain ⟨b, hb, rfl⟩ := h2
      exact ⟨a + b, Submodule.add_mem _ ha hb, by rw [add_smul]⟩
    | smul r y _ h1 =>
      obtain ⟨a, ha, rfl⟩ := h1
      refine ⟨r • a, Submodule.smul_mem _ r ha, ?_⟩
      rw [smul_assoc]
  · intro hz
    exact Submodule.subset_span hz

end Gen

section DedekindLFunctions

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem neighbourConstruct_one_mem (P : Ideal R) (hP0 : P ≠ ⊥) :
    (1 : K) ∈ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P := by
  have e := FractionalIdeal.coe_ideal_mul_inv (K := K) P hP0
  have e2 : ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) = 1 := by
    rw [← FractionalIdeal.coe_mul, e, FractionalIdeal.coe_one]
  have h1 : (1 : K) ∈ ((P : FractionalIdeal R⁰ K) : Submodule R K) *
      (((P : FractionalIdeal R⁰ K)⁻¹ : FractionalIdeal R⁰ K) : Submodule R K) := by
    rw [e2]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  have hne : (P : FractionalIdeal R⁰ K) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.mpr hP0
  refine (mul_le_mul' ?_ ?_ : _ ≤ Submodule.map (Algebra.linearMap R K) P * invIdeal (K := K) P) h1
  · rw [FractionalIdeal.coe_coeIdeal]; exact le_rfl
  · intro a ha
    rw [neighbourConstruct_mem_inv]
    intro p hp
    have := (FractionalIdeal.mem_inv_iff hne).mp ha (algebraMap R K p)
      (FractionalIdeal.mem_coeIdeal_of_mem _ hp)
    rw [mul_comm]
    exact (FractionalIdeal.mem_one_iff _).mp this

theorem neighbourConstruct_key (P : Ideal R) (hP0 : P ≠ ⊥) (L : Submodule R V) (x : V)
    (H : ∀ a ∈ invIdeal (K := K) P, a • x ∈ L) : x ∈ P • L := by
  have h1 := neighbourConstruct_one_mem (K := K) P hP0
  have : ((1 : K) • x) ∈ P • L := by
    refine Submodule.mul_induction_on (C := fun k => k • x ∈ P • L) h1 ?_ ?_
    · intro m hm n hn
      obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hm
      rw [Algebra.linearMap_apply, mul_smul, algebraMap_smul]
      exact Submodule.smul_mem_smul hp (H n hn)
    · intro a b ha hb
      rw [add_smul]; exact Submodule.add_mem _ ha hb
  simpa using this

end DedekindLFunctions

section Avoid

variable {R : Type*} [CommRing R]

end Avoid

section Main

variable {R K V : Type*} [CommRing R] [IsDedekindDomain R] [Field K] [StarRing K] [Algebra R K]
  [IsFractionRing R K] [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

end Main

end Formalism.HermitianLatticesTheory
end
end
