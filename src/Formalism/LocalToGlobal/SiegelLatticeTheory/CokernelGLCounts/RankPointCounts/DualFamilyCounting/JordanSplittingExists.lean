module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AlmostEverywhereSpherical
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.StepsR

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.VdEqVJof
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.CuspDecayShortRowColumn
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_over (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal) :
    ∃ P : Ideal (𝓞 K), P.IsMaximal ∧ P.comap (algebraMap (𝓞 F) (𝓞 K)) = 𝔭 := by
  haveI := h𝔭
  refine Ideal.exists_ideal_over_maximal_of_isIntegral 𝔭 ?_
  intro t ht
  rw [RingHom.mem_ker] at ht
  have h1 : algebraMap F K (t : F) = 0 := by
    have h2 := congrArg (algebraMap (𝓞 K) K) ht
    rw [map_zero] at h2
    exact h2
  have h3 : (t : F) = 0 := (algebraMap F K).injective (by rw [h1, map_zero])
  have h4 : t = 0 := by exact_mod_cast h3
  rw [h4]
  exact 𝔭.zero_mem

variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem spanS_le_of {S : Subring K} {n : ℕ} {x : Fin n → V} {X : Submodule K V} (hx : ∀ i, x i ∈ X) :
    ∀ v ∈ spanS S x, v ∈ X := fun v hv =>
  spanS_induction (p := fun v => v ∈ X) X.zero_mem (fun a b ha hb => X.add_mem ha hb)
    (fun c _ a ha => X.smul_mem c ha) hx v hv

theorem jordan_exists (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (X : Submodule K V) (L : Submodule (𝓞 K) V) (hnd : Cnt.NondegOn h X)
    (hL : Cnt.IsLatIn X L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (𝔭 : Ideal (𝓞 F))
    (h𝔭 : 𝔭.IsMaximal) : ∃ b a, Cnt.IsJordanIn h X L 𝔭 b a := by
  have inj := IsFractionRing.injective (𝓞 K) K
  have hcomp : ∀ t : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) :=
    fun t => rfl
  have hconj_conj : ∀ a : 𝓞 K, conjO K (conjO K a) = a := fun a =>
    inj (by rw [algebraMap_conjO, algebraMap_conjO, star_star])
  obtain ⟨P, hP, rfl⟩ := exists_over (K := K) 𝔭 h𝔭
  obtain ⟨π, hπ, hfin⟩ := exists_unif_fin hF hP
  have hS := isHermSemilocal_locRing hK hP
  obtain ⟨x, hxL, hli, hsp, hloc⟩ := exists_basis_in hL h𝔭
  have hdet0 : (U0.gram h x).det ≠ 0 := det_gram_ne_zero hnd hli hsp
  obtain ⟨N, hN⟩ := hfin _ hdet0
  have hint : ∀ r : 𝓞 K, algebraMap (𝓞 K) K r ∈ locRing P := by
    intro r
    change _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    exact ⟨1, one_mem _, Submodule.mem_one.mpr ⟨r, by rw [map_one, one_mul]⟩⟩
  have hxS : ∀ i j, h (x i) (x j) ∈ locRing P := by
    intro i j
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp (hLi _ (hxL i) _ (hxL j))
    rw [← hr]
    exact hint r
  obtain ⟨y, hyo, hys⟩ := exists_orth_gen hS hπ _ N h hs x hxS hN
  have hxy : ∀ i, x i ∈ spanS (locRing P) y := fun i => by rw [hys]; exact mem_spanS x i
  obtain ⟨c, -, hc⟩ := gram_det_of_le (h := h) hS hxy
  have hdety : (U0.gram h y).det ≠ 0 := fun h0 => hdet0 (by rw [hc, h0, mul_zero])
  have hdiag : U0.gram h y = Matrix.diagonal (fun i => h (y i) (y i)) := by
    ext i j
    show h (y i) (y j) = Matrix.diagonal (fun i => h (y i) (y i)) i j
    by_cases hij : i = j
    · subst hij
      rw [Matrix.diagonal_apply_eq]
    · rw [Matrix.diagonal_apply_ne _ hij]
      exact hyo i j hij
  have hyy : ∀ i, h (y i) (y i) ≠ 0 := by
    rw [hdiag, Matrix.det_diagonal] at hdety
    exact fun i => Finset.prod_ne_zero_iff.mp hdety i (Finset.mem_univ i)

  have hgen : ∀ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, ∃ w : 𝓞 K, ∃ t : 𝓞 F,
      t ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ∧ w * s = algebraMap (𝓞 F) (𝓞 K) t := by
    intro s hs
    induction hs using Submonoid.closure_induction with
    | mem s hs =>
      have hfix : conjO K (conjO K s * s) = conjO K s * s := by
        rw [map_mul, hconj_conj, mul_comm]
      obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF _).mp hfix
      refine ⟨conjO K s, t, ?_, ht.symm⟩
      show algebraMap (𝓞 F) (𝓞 K) t ∉ P
      rw [ht]
      intro h0
      rcases hP.isPrime.mem_or_mem h0 with h1 | h1
      · exact hs.2 (conjO K s) (algebraMap_conjO s) h1
      · exact hs.1 h1
    | one =>
      refine ⟨1, 1, ?_, by rw [one_mul, map_one]⟩
      show algebraMap (𝓞 F) (𝓞 K) 1 ∉ P
      rw [map_one]
      exact fun h0 => hP.ne_top ((Ideal.eq_top_iff_one _).mpr h0)
    | mul x y _ _ hx hy =>
      obtain ⟨wx, tx, htx, hx⟩ := hx
      obtain ⟨wy, ty, hty, hy⟩ := hy
      refine ⟨wx * wy, tx * ty, ?_, ?_⟩
      · show algebraMap (𝓞 F) (𝓞 K) (tx * ty) ∉ P
        rw [map_mul]
        exact fun h0 => (hP.isPrime.mem_or_mem h0).elim htx hty
      · rw [map_mul, ← hx, ← hy]
        ring
  have hclaim : ∀ c ∈ locRing P, star c = c → ∃ t : 𝓞 F, t ∉ P.comap (algebraMap (𝓞 F) (𝓞 K)) ∧
      ∃ a : 𝓞 F, algebraMap F K (a : F) = (algebraMap F K (t : F)) ^ 2 * c := by
    intro c hc hcs
    obtain ⟨s, hs, hsc⟩ := (Formalism.HermitianLatticesTheory.locDual_mem_locR (K := K) P c).mp hc
    obtain ⟨r, hr⟩ := Submodule.mem_one.mp hsc
    obtain ⟨w, t, ht, hwt⟩ := hgen s hs
    have e1 : algebraMap F K (t : F) * c = algebraMap (𝓞 K) K (w * r) := by
      rw [← hcomp, ← hwt, map_mul, map_mul, hr, mul_assoc]
    have hfixt : star (algebraMap F K (t : F)) = algebraMap F K (t : F) := (hF _).mpr ⟨_, rfl⟩
    have hfix : conjO K (w * r) = w * r :=
      inj (by rw [algebraMap_conjO, ← e1, star_mul', hfixt, hcs])
    obtain ⟨a0, ha0⟩ := (conjO_eq_iff_mem_range hF _).mp hfix
    refine ⟨t, ht, t * a0, ?_⟩
    have e2 : algebraMap F K (a0 : F) = algebraMap F K (t : F) * c := by
      rw [← hcomp, ha0, ← e1]
    show algebraMap F K ((t : F) * (a0 : F)) = _
    rw [map_mul, e2]
    ring
  have hyS : ∀ i, h (y i) (y i) ∈ locRing P := fun i =>
    int_spanS hS hxS (y i) (by rw [← hys]; exact mem_spanS y i) (y i)
      (by rw [← hys]; exact mem_spanS y i)
  have hyfix : ∀ i, star (h (y i) (y i)) = h (y i) (y i) := fun i => hs.eq (y i) (y i)
  choose t ht a ha using fun i => hclaim _ (hyS i) (hyfix i)
  have hτ0 : ∀ i, algebraMap F K (t i : F) ≠ 0 := by
    intro i h0
    apply ht i
    have h1 : (t i : F) = 0 := (algebraMap F K).injective (by rw [h0, map_zero])
    have h2 : t i = 0 := by exact_mod_cast h1
    rw [h2]
    exact Submodule.zero_mem _
  have hτfix : ∀ i, star (algebraMap F K (t i : F)) = algebraMap F K (t i : F) :=
    fun i => (hF _).mpr ⟨_, rfl⟩
  have hτS : ∀ i, algebraMap F K (t i : F) ∈ locRing P := fun i => by
    rw [← hcomp]
    exact hint _
  have hτinv : ∀ i, (algebraMap F K (t i : F))⁻¹ ∈ locRing P := by
    intro i
    change _ ∈ Formalism.HermitianLatticesTheory.locR (K := K) P
    rw [Formalism.HermitianLatticesTheory.locDual_mem_locR]
    refine ⟨algebraMap (𝓞 F) (𝓞 K) (t i), Submonoid.subset_closure ⟨ht i, fun t' ht' => ?_⟩,
      Submodule.mem_one.mpr ⟨1, ?_⟩⟩
    · have e : t' = algebraMap (𝓞 F) (𝓞 K) (t i) := inj (by rw [ht', hcomp, hτfix])
      rw [e]
      exact ht i
    · rw [map_one, hcomp, mul_inv_cancel₀ (hτ0 i)]
  obtain ⟨b, hb⟩ : ∃ b : Fin (finrank K X) → V, ∀ i, b i = algebraMap F K (t i : F) • y i :=
    ⟨_, fun _ => rfl⟩
  have hyX : ∀ i, y i ∈ X := fun i => spanS_le_of (S := locRing P) (x := x)
    (fun j => by rw [← hsp]; exact Submodule.subset_span ⟨j, rfl⟩) (y i)
    (by rw [← hys]; exact mem_spanS y i)
  have hbS : spanS (locRing P) b = spanS (locRing P) y := by
    apply le_antisymm
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [hb i]
      exact smul_mem_spanS (hτS i) (mem_spanS y i)
    · refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, rfl⟩
      rw [show y i = (algebraMap F K (t i : F))⁻¹ • b i by rw [hb i, inv_smul_smul₀ (hτ0 i)]]
      exact smul_mem_spanS (hτinv i) (mem_spanS b i)
  refine ⟨b, a, fun i => ?_, ?_, fun i j hij => ?_, fun i => ?_, fun i => ?_⟩
  · rw [hb i]
    exact X.smul_mem _ (hyX i)
  · rw [← hloc]
    ext v
    rw [mem_locF_span_iff hK hF hP b v, mem_locF_span_iff hK hF hP x v, hbS, hys]
  · rw [hb i, hb j]
    simp only [map_smulₛₗ, LinearMap.smul_apply, map_smul, hyo i j hij, smul_zero]
  · rw [hb i, ha i, map_smulₛₗ h, LinearMap.smul_apply, map_smul, smul_eq_mul, smul_eq_mul,
      starRingEnd_apply, hτfix]
    ring
  · intro h0
    have h1 := ha i
    rw [h0] at h1
    have h2 : (algebraMap F K (t i : F)) ^ 2 * h (y i) (y i) = 0 := by
      rw [← h1]
      simp
    exact mul_ne_zero (pow_ne_zero 2 (hτ0 i)) (hyy i) h2

end Formalism.L2.SG.Pf.G1
end
end

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G1

open Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.U0 Formalism.HermitianLattices.Ext.L3.WA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem vd_eq_vJof (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (h𝔭 : 𝔭.IsMaximal)
    (b : Fin (finrank K (⊤ : Submodule K V)) → V) (a : Fin (finrank K (⊤ : Submodule K V)) → 𝓞 F)
    (hJ : Cnt.IsJordanIn h ⊤ L 𝔭 b a) : vd h L 𝔭 = Cnt.vJof 𝔭 a := by
  classical
  obtain ⟨P, hP, hPc⟩ := exists_over (K := K) 𝔭 h𝔭
  haveI := h𝔭.isPrime
  have e : Fin (finrank K (⊤ : Submodule K V)) ≃ Fin (finrank K V) := finCongr (finrank_top K V)
  have hmap : ∀ x : 𝓞 F, algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) x) = algebraMap F K (x : F) := fun x => by
    rw [← IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K, IsScalarTower.algebraMap_apply (𝓞 F) F K]
  have hA0 : (∏ i, a i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => hJ.2.2.2.2 i
  have horth : ∀ i j, i ≠ j → h (b (e.symm i)) (b (e.symm j)) = 0 :=
    fun i j hij => hJ.2.2.1 _ _ fun h' => hij (e.symm.injective h')
  have hrange : Set.range (fun j => b (e.symm j)) = Set.range b := e.symm.surjective.range_comp b

  have hgb : (U0.gram h fun j => b (e.symm j)).det =
      algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) (∏ i, a i)) := by
    rw [gram_det_orth horth]
    have hp : ∏ j, h (b (e.symm j)) (b (e.symm j)) = ∏ i, h (b i) (b i) :=
      Fintype.prod_equiv e.symm _ _ fun _ => rfl
    rw [hp, map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => by rw [hJ.2.2.2.1 i, hmap]
  have key : ∀ m : ℕ, discrIdeal h L ≤ extP K 𝔭 ^ m ↔ m ≤ vF 𝔭 (∏ i, a i) := by
    intro m
    constructor
    · intro hle
      have ht : ∀ i, ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • b i ∈ L := fun i => by
        have hb : b i ∈ locF 𝔭 L := by
          rw [← hJ.2.1]
          exact LocF.le_locF 𝔭 _ (Submodule.subset_span ⟨i, rfl⟩)
        exact (LocalSpans.mem_locF 𝔭 L (b i)).1 hb
      choose t ht1 ht2 using ht
      have ht0 : ∀ i, t i ≠ 0 := fun i h0 => ht1 i (h0 ▸ 𝔭.zero_mem)
      have hT0 : (∏ i, t i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i _ => ht0 i
      have hvT : vF 𝔭 (∏ i, t i) = 0 := by
        rw [vF_prod h𝔭 Finset.univ t ht0]
        exact Finset.sum_eq_zero fun i _ => vF_of_notMem h𝔭 (ht1 i)
      have hst : ∀ u : F, star (algebraMap F K u) = algebraMap F K u := fun u => (hF _).2 ⟨u, rfl⟩
      have hx : (U0.gram h fun j => algebraMap F K (t (e.symm j) : F) • b (e.symm j)).det =
          algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) ((∏ i, t i) * (∏ i, t i) * ∏ i, a i)) := by
        rw [gram_det_smul_orth horth]
        have hp1 : ∏ j, star (algebraMap F K (t (e.symm j) : F)) * algebraMap F K (t (e.symm j) : F) =
            ∏ i, algebraMap F K (t i : F) * algebraMap F K (t i : F) :=
          Fintype.prod_equiv e.symm _ _ fun j => by rw [hst]
        have hp2 : ∏ j, h (b (e.symm j)) (b (e.symm j)) = ∏ i, h (b i) (b i) :=
          Fintype.prod_equiv e.symm _ _ fun _ => rfl
        rw [hp1, hp2, map_mul, map_mul, map_mul, map_mul, map_prod, map_prod, map_prod, map_prod,
          Finset.prod_mul_distrib]
        simp only [hmap, hJ.2.2.2.1]
      have hxL : ∀ j, algebraMap F K (t (e.symm j) : F) • b (e.symm j) ∈ L := fun j => by
        rw [← hmap, algebraMap_smul]
        exact ht2 _
      have hmem : algebraMap (𝓞 F) (𝓞 K) ((∏ i, t i) * (∏ i, t i) * ∏ i, a i) ∈ discrIdeal h L :=
        Ideal.subset_span ⟨_, hxL, hx.symm⟩
      have h2 := hle hmem
      have h3 : (∏ i, t i) * (∏ i, t i) * ∏ i, a i ∈ 𝔭 ^ m := by
        rw [← MeanB.comap_extP_pow (K := K) 𝔭 m]
        exact h2
      rw [mem_pow_iff h𝔭 (mul_ne_zero (mul_ne_zero hT0 hT0) hA0), vF_mul h𝔭 (mul_ne_zero hT0 hT0) hA0,
        vF_mul h𝔭 hT0 hT0, hvT] at h3
      simpa using h3
    · intro hv
      unfold discrIdeal
      rw [Ideal.span_le]
      rintro z ⟨x, hxL, hz⟩
      have hx' : ∀ i, x i ∈ spanS (locRing P) fun j => b (e.symm j) := fun i => by
        have hxi : x i ∈ locF 𝔭 (Submodule.span (𝓞 K) (Set.range fun j => b (e.symm j))) := by
          rw [hrange, hJ.2.1]
          exact LocF.le_locF 𝔭 L (hxL i)
        rw [← hPc] at hxi
        exact (mem_locF_span_iff hK hF hP _ (x i)).1 hxi
      obtain ⟨c, hc, hdet⟩ := gram_det_of_le (h := h) (isHermSemilocal_locRing hK hP) hx'
      obtain ⟨r, s, hs, hcr⟩ := (mem_locR_iff hP.isPrime c).1 hc
      have hsne := algebraMap_ne_zero_of_mem_hcompl hP.isPrime hs
      have hsz : s * z = r * algebraMap (𝓞 F) (𝓞 K) (∏ i, a i) := by
        apply IsFractionRing.injective (𝓞 K) K
        rw [map_mul, map_mul, hz]
        change _ * (U0.gram h x).det = _
        rw [hdet, hgb, hcr]
        field_simp
      have hAm : algebraMap (𝓞 F) (𝓞 K) (∏ i, a i) ∈ extP K 𝔭 ^ m := by
        rw [extP, ← Ideal.map_pow]
        exact Ideal.mem_map_of_mem _ ((mem_pow_iff h𝔭 hA0 m).2 hv)
      have hcop := OrthogonalBases.sup_eq_top_of_mem_hcompl hK hF hP hs
      rw [hPc] at hcop
      exact mem_pow_of_coprime hcop m (hsz ▸ Ideal.mul_mem_left _ r hAm)
  have hv : Cnt.vJof 𝔭 a = vF 𝔭 (∏ i, a i) := (vF_prod h𝔭 Finset.univ a hJ.2.2.2.2).symm
  rw [hv]
  unfold vd
  simp_rw [key]
  exact csSup_Iic

end Formalism.L2.SG.Pf.G1
end
end

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

theorem jordan_splitting_exists : JordanExists := by
  intro K F V _ _ _ _ _ _ _ _ _ _ _ hK hF h hs
  exact ⟨fun X L hnd hL hLi 𝔭 h𝔭 => G1.jordan_exists hK hF hs X L hnd hL hLi 𝔭 h𝔭,
    fun L _ 𝔭 h𝔭 b a hJ => G1.vd_eq_vJof hK hF L 𝔭 h𝔭 b a hJ⟩

end Formalism.L2.SG.Pf.Cnt
