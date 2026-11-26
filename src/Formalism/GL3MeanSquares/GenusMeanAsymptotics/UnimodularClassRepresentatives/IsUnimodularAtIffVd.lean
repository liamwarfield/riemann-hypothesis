module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsSmulMem
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtPPowLeSpanSup
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardLiftMatrix
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormDiscrIdealOfLe

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem locF_eq_loc (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) (L : Submodule (𝓞 K) V) :
    locF (P.comap (algebraMap (𝓞 F) (𝓞 K))) L = Formalism.HermitianLatticesTheory.loc (K := K) P L := by
  have hPp := hP.isPrime
  have hp : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsPrime := Ideal.comap_isPrime _ _
  ext x
  rw [LocF.mem_locF_iff hp]
  unfold Formalism.HermitianLatticesTheory.loc
  rw [Formalism.HermitianLatticesTheory.locBasic_mem_locS]
  constructor
  · rintro ⟨t, ht, hx⟩
    refine ⟨_, ?_, hx⟩
    rw [WA.mem_hcompl_iff hPp, WA.mem_conjIdeal_iff,
      (conjO_eq_iff_mem_range hF _).mpr ⟨t, rfl⟩]
    exact ⟨ht, ht⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨h1, h2⟩ := (WA.mem_hcompl_iff hPp s).mp hs
    rw [WA.mem_conjIdeal_iff] at h2
    obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF (conjO K s * s)).mp
      (by rw [map_mul, conjO_conjO, mul_comm])
    refine ⟨t, ?_, ?_⟩
    · rw [Ideal.mem_comap, ht]
      exact fun h => (hPp.mem_or_mem h).elim h2 h1
    · rw [ht, mul_smul]
      exact L.smul_mem _ hx

theorem isUnimodularAt_iff_vd (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) :
    Formalism.HermitianLatticesTheory.IsUnimodularAt h P L ↔ vd h L (P.comap (algebraMap (𝓞 F) (𝓞 K))) = 0 := by
  have hPp := hP.isPrime
  have hda := LocF.aniso_of_totPosDef hd
  have hEP : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ P := Ideal.map_comap_le
  constructor
  · intro hu
    apply LocF.vd_eq_zero_of_not_le
    have hS : WA.IsHermSemilocal (WA.locRing P) :=
      ⟨fun _ ha => WA.star_mem_locRing hPp ha, WA.frac_locRing P, WA.unram_locRing hK hP,
        WA.principal_locRing hK hP, WA.unit_or_locRing hPp⟩
    obtain ⟨x, hxM, hxo, hxu⟩ := LocF.exists_orth_unit_frame hS
      (LocF.locRing_local hPp) hs hda (WA.isSelfDualMod_loc hL hPp hu)
    choose s hs' hsx using fun i => Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp
      (show x i ∈ Formalism.HermitianLatticesTheory.locS (Formalism.HermitianLatticesTheory.hcompl (K := K) P) L from hxM i)
    obtain ⟨g, -, hdet⟩ := LocF.exists_gram hLi (fun i => s i • x i) hsx
    have hmem : g.det ∈ discrIdeal h L := Ideal.subset_span ⟨_, hsx, hdet⟩
    have hunit : WA.IsUnitIn (WA.locRing P) (algebraMap (𝓞 K) K g.det) := by
      rw [hdet]
      have hdiag : (Matrix.of fun i j => h (s i • x i) (s j • x j)) = Matrix.diagonal fun i =>
          star (algebraMap (𝓞 K) K (s i)) * algebraMap (𝓞 K) K (s i) * h (x i) (x i) := by
        ext i j
        rw [Matrix.of_apply, Formalism.HermitianLatticesTheory.locDual_h_smul_left, Formalism.HermitianLatticesTheory.locDual_h_smul_right]
        by_cases hij : i = j
        · subst hij
          rw [Matrix.diagonal_apply_eq]
          ring
        · rw [Matrix.diagonal_apply_ne _ hij, hxo i j hij]
          ring
      rw [hdiag, Matrix.det_diagonal]
      apply LocF.isUnitIn_prod
      intro i _
      refine LocF.isUnitIn_mul (LocF.isUnitIn_mul ?_ ?_) (hxu i)
      · rw [← WA.algebraMap_conjO, LocF.isUnitIn_algebraMap_iff hPp]
        exact WA.conjO_mem_hcompl (hs' i)
      · rw [LocF.isUnitIn_algebraMap_iff hPp]
        exact hs' i
    have hnP : g.det ∉ P :=
      ((WA.mem_hcompl_iff hPp _).mp ((LocF.isUnitIn_algebraMap_iff hPp _).mp hunit)).1
    exact fun hle => hnP (hEP (hle hmem))
  · intro h0
    have hn := LocF.not_le_of_vd_eq_zero (LocF.discrIdeal_ne_bot hda hL hLi)
      (ne_top_of_le_ne_top hP.ne_top hEP) h0
    unfold discrIdeal at hn
    rw [Ideal.span_le, Set.not_subset] at hn
    obtain ⟨z, ⟨x, hx, hz⟩, hzn⟩ := hn
    have hzfix : conjO K z = z := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      change star (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K z
      rw [hz, LocF.star_gram_det h hs]
    obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF z).mp hzfix
    have hzP : z ∉ P := by
      intro hmem
      apply hzn
      rw [← ht] at hmem ⊢
      exact Ideal.mem_map_of_mem _ (Ideal.mem_comap.mpr hmem)
    have hzc : z ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
      rw [WA.mem_hcompl_iff hPp, WA.mem_conjIdeal_iff, hzfix]
      exact ⟨hzP, hzP⟩
    have hz0 : (Matrix.of fun i j => h (x i) (x j)).det ≠ 0 := by
      rw [← hz]
      exact WA.algebraMap_ne_zero_of_mem_hcompl hPp hzc
    have hspan : Submodule.span K (Set.range x) = ⊤ :=
      (LocF.linearIndependent_of_gram_det_ne_zero h x hz0).span_eq_top_of_card_eq_finrank'
        (by simp)
    obtain ⟨g, hg, hdet⟩ := LocF.exists_gram hLi x hx
    have hgz : g.det = z := RingOfIntegers.ext (hdet.trans hz.symm)
    obtain ⟨hA, hB⟩ := (Formalism.HermitianLatticesTheory.locDual (𝓞 K) K V h hs (fun r => ⟨conjO K r, rfl⟩) L hL.fg).1
      P hPp
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt
    rw [hB, ← hA]
    apply le_antisymm
    · have hle : Formalism.HermitianLatticesTheory.dual h L ≤ Formalism.HermitianLatticesTheory.loc (K := K) P L := by
        intro y hy
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual] at hy
        exact Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨g.det, hgz ▸ hzc,
          LocF.det_smul_mem h x hx hspan g hg y (fun i => hy _ (hx i))⟩
      calc Formalism.HermitianLatticesTheory.loc (K := K) P (Formalism.HermitianLatticesTheory.dual h L)
          ≤ Formalism.HermitianLatticesTheory.loc (K := K) P (Formalism.HermitianLatticesTheory.loc (K := K) P L) :=
            Formalism.HermitianLatticesTheory.locBasic_locS_mono _ hle
        _ = Formalism.HermitianLatticesTheory.loc (K := K) P L := Formalism.HermitianLatticesTheory.locBasic_locS_idem _ _
    · apply Formalism.HermitianLatticesTheory.locBasic_locS_mono
      intro y hy
      rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
      exact fun w hw => hLi w hw y hy

theorem finite_vd_ne_zero (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) :
    {𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} | vd h L 𝔭.1 ≠ 0}.Finite := by
  have hD := LocF.discrIdeal_ne_bot (LocF.aniso_of_totPosDef hd) hL hLi
  have hD' : (discrIdeal h L).comap (algebraMap (𝓞 F) (𝓞 K)) ≠ ⊥ := by
    obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
    exact Ideal.comap_ne_bot_of_integral_mem hz0 hz (Algebra.IsIntegral.isIntegral z)
  refine ((Ideal.finite_factors hD').image (fun v =>
    (⟨v.asIdeal, v.isMaximal⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}))).subset ?_
  intro 𝔭 h𝔭
  have hle : discrIdeal h L ≤ extP K 𝔭.1 := by
    by_contra hn
    exact h𝔭 (LocF.vd_eq_zero_of_not_le hn)
  obtain ⟨P, hP, hP𝔭⟩ := exists_maximal_over hK hF 𝔭.2
  have h2 : extP K 𝔭.1 ≤ P := by
    rw [← hP𝔭]
    exact Ideal.map_comap_le
  have h1 : (discrIdeal h L).comap (algebraMap (𝓞 F) (𝓞 K)) ≤ 𝔭.1 := by
    rw [← hP𝔭]
    exact Ideal.comap_mono (hle.trans h2)
  have hne : 𝔭.1 ≠ ⊥ := fun e => hD' (eq_bot_iff.mpr (e ▸ h1))
  exact ⟨⟨𝔭.1, 𝔭.2.isPrime, hne⟩, Ideal.dvd_iff_le.mpr h1, rfl⟩

theorem exists_unique_patch (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {L₀ : Submodule (𝓞 K) V} (hL₀ : Submodule.IsFullLattice K L₀)
    (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) (T : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V)
    (hT : ∀ 𝔭 ∈ s, locF 𝔭.1 (T 𝔭) = T 𝔭 ∧ ∃ A : Submodule (𝓞 K) V, Submodule.IsFullLattice K A ∧
      locF 𝔭.1 A = T 𝔭) :
    ∃! Λ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ ∧ (∀ 𝔭 ∈ s, locF 𝔭.1 Λ = T 𝔭) ∧
      ∀ 𝔭 ∉ s, locF 𝔭.1 Λ = locF 𝔭.1 L₀ := by
  classical
  let B : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V := fun 𝔭 =>
    if h : 𝔭 ∈ s then (hT 𝔭 h).2.choose else L₀
  have hB1 : ∀ 𝔭 (h : 𝔭 ∈ s), Submodule.IsFullLattice K (B 𝔭) ∧ locF 𝔭.1 (B 𝔭) = T 𝔭 := by
    intro 𝔭 h
    simp only [B, dif_pos h]
    exact (hT 𝔭 h).2.choose_spec
  have hB2 : ∀ 𝔭 ∉ s, B 𝔭 = L₀ := by
    intro 𝔭 h
    simp only [B, dif_neg h]
  have hB : ∀ 𝔭, Submodule.IsFullLattice K (B 𝔭) := by
    intro 𝔭
    by_cases h : 𝔭 ∈ s
    · exact (hB1 𝔭 h).1
    · rw [hB2 𝔭 h]
      exact hL₀
  obtain ⟨hlat, hloc⟩ := LocF.patch hL₀ s B hB hB2
  refine ⟨_, ⟨hlat, fun 𝔭 h => (hloc 𝔭).trans (hB1 𝔭 h).2,
    fun 𝔭 h => (hloc 𝔭).trans (by rw [hB2 𝔭 h])⟩, ?_⟩
  rintro Λ ⟨-, h1, h2⟩
  rw [← LocF.iInf_locF (F := F) Λ]
  congr 1
  funext 𝔭
  by_cases h : 𝔭 ∈ s
  · rw [h1 𝔭 h, (hB1 𝔭 h).2]
  · rw [h2 𝔭 h, hB2 𝔭 h]

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsAddConjTransposeEq
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

theorem exists_add_conj_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (a : 𝓞 F) :
    ∃ z : 𝓞 K, z + conjO K z = algebraMap (𝓞 F) (𝓞 K) a := by
  let ι := algebraMap (𝓞 F) (𝓞 K)
  have coe_ι (b : 𝓞 F) : ((ι b : 𝓞 K) : K) = algebraMap F K (b : F) :=
    (IsScalarTower.algebraMap_apply (𝓞 F) (𝓞 K) K b).symm.trans
      (IsScalarTower.algebraMap_apply (𝓞 F) F K b)
  have ι_injective : Function.Injective ι := by
    intro b c h
    apply RingOfIntegers.ext
    have hcoe := congrArg (fun z : 𝓞 K => (z : K)) h
    exact (algebraMap F K).injective ((coe_ι b).symm.trans (hcoe.trans (coe_ι c)))
  have conj_ι (b : 𝓞 F) : conjO K (ι b) = ι b := by
    apply RingOfIntegers.ext
    change star ((ι b : 𝓞 K) : K) = ((ι b : 𝓞 K) : K)
    rw [coe_ι]
    exact (hF _).mpr ⟨b, rfl⟩
  have exists_trace (z : 𝓞 K) : ∃ b : 𝓞 F, ι b = z + conjO K z := by
    let w : 𝓞 K := z + conjO K z
    have hw : star (w : K) = (w : K) := by
      change star ((z : K) + star (z : K)) = (z : K) + star (z : K)
      rw [star_add, star_star, add_comm]
    obtain ⟨b, hb⟩ := (hF _).mp hw
    have hb_int : IsIntegral ℤ b := by
      apply (isIntegral_algHom_iff (algebraMap F K).toIntAlgHom (algebraMap F K).injective).mp
      change IsIntegral ℤ (algebraMap F K b)
      rw [hb]
      exact RingOfIntegers.isIntegral_coe w
    refine ⟨⟨b, hb_int⟩, RingOfIntegers.ext ?_⟩
    exact (coe_ι ⟨b, hb_int⟩).trans hb
  let trace (z : 𝓞 K) : 𝓞 F := Classical.choose (exists_trace z)
  have trace_spec (z : 𝓞 K) : ι (trace z) = z + conjO K z :=
    Classical.choose_spec (exists_trace z)
  let tr : 𝓞 K →ₗ[𝓞 F] 𝓞 F :=
    { toFun := trace
      map_add' := by
        intro x y
        apply ι_injective
        rw [trace_spec, map_add, map_add, trace_spec, trace_spec]
        ring
      map_smul' := by
        intro b z
        apply ι_injective
        rw [RingHom.id_apply, smul_eq_mul, map_mul, trace_spec, trace_spec, Algebra.smul_def,
          map_mul, conj_ι]
        ring }
  have htop : LinearMap.range tr = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, h𝔭, hle⟩ := Ideal.exists_le_maximal (LinearMap.range tr) hne
    obtain ⟨θ, hθ⟩ := idealPowerSpanBounds.exists_theta hK hF h𝔭
    have hmem : ∀ z : 𝓞 K, z + conjO K z ∈ extP K 𝔭 := fun z => by
      rw [← trace_spec]
      exact Ideal.mem_map_of_mem _ (hle ⟨z, rfl⟩)
    have h2 : (2 : 𝓞 K) ∈ extP K 𝔭 := by
      have := hmem 1
      rwa [map_one, one_add_one_eq_two] at this
    have hsq : (θ - conjO K θ) * (θ - conjO K θ) ∈ extP K 𝔭 := by
      have : (θ - conjO K θ) * (θ - conjO K θ) =
          (θ + conjO K θ) * (θ + conjO K θ) - 2 * (2 * (θ * conjO K θ)) := by ring
      rw [this]
      exact sub_mem (Ideal.mul_mem_left _ _ (hmem θ)) (Ideal.mul_mem_right _ _ h2)
    have hdiff : (θ - conjO K θ) ∈ extP K 𝔭 ^ 1 :=
      idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by simpa only [pow_one] using hsq)
    have hone : (1 : 𝓞 K) ∈ extP K 𝔭 ^ 1 :=
      idealPowerSpanBounds.mem_of_unit_mul_mem hθ (by simpa only [mul_one] using hdiff)
    have hcomap : Ideal.comap ι (extP K 𝔭) = 𝔭 :=
      Ideal.comap_map_eq_self_of_faithfullyFlat 𝔭
    have hone_mem : (1 : 𝓞 F) ∈ 𝔭 := by
      rw [← hcomap, Ideal.mem_comap, map_one]
      simpa only [pow_one] using hone
    exact h𝔭.ne_top ((Ideal.eq_top_iff_one _).2 hone_mem)
  obtain ⟨z, hz⟩ : a ∈ LinearMap.range tr := htop ▸ Submodule.mem_top
  exact ⟨z, (trace_spec z).symm.trans (congrArg ι hz)⟩

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsClassReps
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace StabilizerLattices

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

variable {h : V →ₗ⋆[K] V →ₗ[K] K}

omit [FiniteDimensional K V] in
theorem exists_smul_iff (N M : Submodule (𝓞 K) V) :
    (∃ g : Formalism.HermitianLatticesTheory.isom h, g • N = M) ↔ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g N = M := by
  constructor
  · rintro ⟨g, hg⟩
    exact ⟨g.1, g.2, hg⟩
  · rintro ⟨g, hg, e⟩
    exact ⟨⟨g, hg⟩, e⟩

theorem finite_rep (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V} (hM : Submodule.IsLattice K M)
    (n : K) : {x : V | x ∈ M ∧ h x x = n}.Finite := by
  have := hM
  refine (Formalism.HermitianLatticesTheory.autFinite_short h (trace_pos hd) M (Algebra.trace ℚ K n)).subset ?_
  rintro x ⟨hx, rfl⟩
  exact ⟨hx, le_rfl⟩

theorem finite_stab_lat (hs : h.IsSymm) (hd : IsTotPosDef h) {M : Submodule (𝓞 K) V}
    (hM : Submodule.IsFullLattice K M) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by
  have : Finite (Formalism.ThetaLiftIndependence.autL h M) := (Formalism.HermitianLatticesTheory.autFinite K V h hs (trace_pos hd) M hM).to_subtype
  have : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) M) := Finite.of_equiv _ (stabLatEquiv M).symm
  exact Set.toFinite _

theorem exists_classReps (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) : ∃ s, Formalism.ThetaLiftIndependence.IsClassReps h L s :=
  (Formalism.ThetaLiftIndependence.classRepsDefinite K V h hs (trace_pos hd) L hL).1

theorem exists_pairReps (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (n : K) :
    ∃ sX : Finset (Submodule (𝓞 K) V × V), (∀ t ∈ sX, t ∈ pairs h L n) ∧
      ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p := by
  obtain ⟨s, hs1, hs2⟩ := exists_classReps hs hd hL
  refine OrbSum.exists_reps_of_cover (pairs h L n) (pairs_stable hs L n)
    (⋃ M ∈ s, (fun x => (M, x)) '' {x : V | x ∈ M ∧ h x x = n}) ?_ ?_ ?_
  · exact Set.Finite.biUnion s.finite_toSet fun M hM => (finite_rep hd (hs1 M hM).1.toIsLattice n).image _
  · intro c hc
    obtain ⟨M, hM, x, hx, rfl⟩ := Set.mem_iUnion₂.mp hc
    exact ⟨hs1 M hM, hx.1, hx.2⟩
  · intro p hp
    obtain ⟨M, ⟨hM, g, hg, hgM⟩, -⟩ := hs2 p.1 hp.1
    refine ⟨(M, g.symm p.2), Set.mem_iUnion₂.mpr ⟨M, hM, g.symm p.2, ⟨?_, ?_⟩, rfl⟩, ⟨g, hg⟩, ?_⟩
    · rw [← Formalism.HermitianLatticesTheory.isomAct_mem_gmap, hgM]
      exact hp.2.1
    · rw [SplitBAux.symm_mem_isom hg]
      exact hp.2.2
    · exact Prod.ext hgM (LinearEquiv.apply_symm_apply g p.2)

theorem sum_pairs_eq_rep (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V} (n : K)
    {s : Finset (Submodule (𝓞 K) V)} (hsr : Formalism.ThetaLiftIndependence.IsClassReps h L s)
    {sX : Finset (Submodule (𝓞 K) V × V)} (hsX : ∀ t ∈ sX, t ∈ pairs h L n)
    (hX : ∀ p ∈ pairs h L n, ∃! t, t ∈ sX ∧ ∃ g : Formalism.HermitianLatticesTheory.isom h, g • t = p) :
    ∑ t ∈ sX, ((Nat.card (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) t) : ℕ) : ℝ)⁻¹ =
      ∑ M ∈ s, (repCount h M n : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h M) : ℕ) : ℝ) := by
  have key := OrbSum.sum_orbits_on (G := Formalism.HermitianLatticesTheory.isom h) (Prod.fst : Submodule (𝓞 K) V × V → _)
    (fun _ _ => rfl) (pairs h L n) (Formalism.HermitianLatticesTheory.genus h L) (pairs_stable hs L n) (fun p hp => hp.1)
    sX s hsX hsr.1 hX (fun M hM => by simp_rw [exists_smul_iff]; exact hsr.2 M hM)
    (fun M hM => finite_stab_lat hs hd hM.1)
  rw [key]
  refine Finset.sum_congr rfl fun M hM => ?_
  have e1 : Nat.card {p : Submodule (𝓞 K) V × V // p ∈ pairs h L n ∧ p.1 = M} = repCount h M n :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.2, (congrArg (fun N : Submodule (𝓞 K) V => p.1.2 ∈ N) p.2.2).mp p.2.1.2.1, p.2.1.2.2⟩
        invFun := fun x => ⟨(M, x.1), ⟨hsr.1 M hM, x.2.1, x.2.2⟩, rfl⟩
        left_inv := fun p => Subtype.ext (Prod.ext p.2.2.symm rfl)
        right_inv := fun _ => rfl }
  rw [e1, Nat.card_congr (stabLatEquiv M)]

end StabilizerLattices

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardQuotExtPPow
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

scoped instance starO : StarRing (𝓞 K) where
  star := conjO K
  star_involutive := L3.conjO_conjO
  star_mul a b := by
    show conjO K (a * b) = conjO K b * conjO K a
    rw [map_mul, mul_comm]
  star_add := map_add (conjO K)

theorem star_def (a : 𝓞 K) : star a = conjO K a := rfl

scoped instance starQ [hF : Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    StarRing (𝓞 K ⧸ extP K 𝔭 ^ k) where
  star := NormLifting.conjQ _ (conjO_mem_pow hF.out 𝔭 k)
  star_involutive a := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    show NormLifting.conjQ _ _ (NormLifting.conjQ _ _ _) = _
    rw [NormLifting.conjQ_mk, NormLifting.conjQ_mk, L3.conjO_conjO]
  star_mul a b := by
    show NormLifting.conjQ _ _ (a * b) = NormLifting.conjQ _ _ b * NormLifting.conjQ _ _ a
    rw [map_mul, mul_comm]
  star_add := map_add _

theorem star_mk [Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    star (Ideal.Quotient.mk (extP K 𝔭 ^ k) a) = Ideal.Quotient.mk (extP K 𝔭 ^ k) (star a) := NormLifting.conjQ_mk _ _ a

theorem absNorm_extP_eq_sq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) : Ideal.absNorm (extP K 𝔭) = Ideal.absNorm 𝔭 ^ 2 := by
  have h := Ideal.absNorm_algebraMap (𝓞 F) (𝓞 K) 𝔭
  rw [← IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K, MeanB.finrank_eq_two hK hF] at h
  exact h

theorem absNorm_extP_pow (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) :
    Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
  have h1 : Ideal.absNorm (extP K 𝔭 ^ k) = Ideal.absNorm 𝔭 ^ (2 * k) := by
    rw [map_pow, absNorm_extP_eq_sq hK hF h𝔭, ← pow_mul]
  rw [← h1, Ideal.absNorm_apply, Submodule.cardQuot_apply]

theorem finite_quot {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := by
  have h0 : extP K 𝔭 ^ k ≠ ⊥ := by
    rw [← Ideal.zero_eq_bot]
    exact pow_ne_zero _ (by rw [Ideal.zero_eq_bot]; exact map_ne_bot_of_isMaximal h𝔭)
  first
  | exact Ideal.finiteQuotientOfFreeOfNeBot _ h0
  | exact (Ideal.absNorm_ne_zero_iff _).mp (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact h0)

def piQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) :
    (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) →+* (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ k))

theorem piQ_mk (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    piQ K 𝔭 k (Ideal.Quotient.mk _ a) = Ideal.Quotient.mk _ a := rfl

theorem piQ_surjective (𝔭 : Ideal (𝓞 F)) (k : ℕ) : Function.Surjective (piQ K 𝔭 k) := by
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ a, rfl⟩

theorem piQ_star [Fact (IsFixF K F)] (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) :
    piQ K 𝔭 k (star a) = star (piQ K 𝔭 k a) := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [star_mk, piQ_mk, piQ_mk, star_mk]

theorem mk_mem_ker_piQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a : 𝓞 K) :
    Ideal.Quotient.mk (extP K 𝔭 ^ (k + 1)) a ∈ RingHom.ker (piQ K 𝔭 k) ↔ a ∈ extP K 𝔭 ^ k := by
  rw [RingHom.mem_ker, piQ_mk, Ideal.Quotient.eq_zero_iff_mem]

theorem card_ker_piQ (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (k : ℕ) : Nat.card (RingHom.ker (piQ K 𝔭 k)) = Ideal.absNorm 𝔭 ^ 2 := by
  haveI := finite_quot (K := K) h𝔭 (k + 1)
  have hA := absNorm_extP_pow hK hF h𝔭 (k + 1)
  have hB := absNorm_extP_pow hK hF h𝔭 k
  have hC : Nat.card ((𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) ⧸ RingHom.ker (piQ K 𝔭 k)) =
      Nat.card (𝓞 K ⧸ extP K 𝔭 ^ k) :=
    Nat.card_congr (RingHom.quotientKerEquivOfSurjective (piQ_surjective (K := K) 𝔭 k)).toEquiv
  have hmul : Nat.card (𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) = Nat.card (RingHom.ker (piQ K 𝔭 k)) *
      Nat.card ((𝓞 K ⧸ extP K 𝔭 ^ (k + 1)) ⧸ RingHom.ker (piQ K 𝔭 k)) := by
    first
    | exact Submodule.card_eq_card_quotient_mul_card _
    | (rw [mul_comm]; exact Submodule.card_eq_card_quotient_mul_card _)
    | (rw [mul_comm]; exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (RingHom.ker (piQ K 𝔭 k)).toAddSubgroup)
    | exact AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
        (RingHom.ker (piQ K 𝔭 k)).toAddSubgroup
  rw [hC, hA, hB] at hmul
  have hN : 0 < Ideal.absNorm 𝔭 ^ (2 * k) :=
    pow_pos (Nat.pos_of_ne_zero (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact ne_bot h𝔭)) _
  have e : Ideal.absNorm 𝔭 ^ (2 * (k + 1)) = Ideal.absNorm 𝔭 ^ 2 * Ideal.absNorm 𝔭 ^ (2 * k) := by
    ring
  rw [e] at hmul
  exact (Nat.eq_of_mul_eq_mul_right hN hmul).symm

def idQ (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k j : ℕ) :
    Ideal (𝓞 K ⧸ extP K 𝔭 ^ k) :=
  (extP K 𝔭 ^ j).map (Ideal.Quotient.mk _)

theorem mem_idQ {𝔭 : Ideal (𝓞 F)} {k j : ℕ} {a : 𝓞 K ⧸ extP K 𝔭 ^ k} :
    a ∈ idQ K 𝔭 k j ↔ ∃ z ∈ extP K 𝔭 ^ j, Ideal.Quotient.mk _ z = a := by
  show a ∈ (extP K 𝔭 ^ j).map (Ideal.Quotient.mk _) ↔ _
  rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]

theorem mk_mem_idQ {𝔭 : Ideal (𝓞 F)} {k j : ℕ} (hjk : j ≤ k) {z : 𝓞 K} :
    Ideal.Quotient.mk (extP K 𝔭 ^ k) z ∈ idQ K 𝔭 k j ↔ z ∈ extP K 𝔭 ^ j := by
  rw [mem_idQ]
  constructor
  · rintro ⟨z', hz', he⟩
    rw [Ideal.Quotient.eq] at he
    have h1 : z' - z ∈ extP K 𝔭 ^ j := Ideal.pow_le_pow_right hjk he
    have h2 : z = z' - (z' - z) := by ring
    rw [h2]
    exact Ideal.sub_mem _ hz' h1
  · intro hz
    exact ⟨z, hz, rfl⟩

theorem star_mem_idQ [hF : Fact (IsFixF K F)] {𝔭 : Ideal (𝓞 F)} {k j : ℕ}
    {a : 𝓞 K ⧸ extP K 𝔭 ^ k} (ha : a ∈ idQ K 𝔭 k j) : star a ∈ idQ K 𝔭 k j := by
  obtain ⟨z, hz, rfl⟩ := mem_idQ.mp ha
  rw [star_mk]
  exact mem_idQ.mpr ⟨star z, conjO_mem_pow hF.out 𝔭 j z hz, rfl⟩

theorem mul_eq_zero_idQ {𝔭 : Ideal (𝓞 F)} {k j : ℕ} (hjk : k ≤ 2 * j)
    {a b : 𝓞 K ⧸ extP K 𝔭 ^ k} (ha : a ∈ idQ K 𝔭 k j) (hb : b ∈ idQ K 𝔭 k j) : a * b = 0 := by
  obtain ⟨x, hx, rfl⟩ := mem_idQ.mp ha
  obtain ⟨y, hy, rfl⟩ := mem_idQ.mp hb
  rw [← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  have h1 : x * y ∈ extP K 𝔭 ^ (j + j) := by
    rw [pow_add]
    exact Ideal.mul_mem_mul hx hy
  exact Ideal.pow_le_pow_right (by omega) h1

theorem ker_piQ (𝔭 : Ideal (𝓞 F)) (k : ℕ) : RingHom.ker (piQ K 𝔭 k) = idQ K 𝔭 (k + 1) k := by
  ext a
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
  rw [mk_mem_ker_piQ, mk_mem_idQ (Nat.le_succ k)]

end Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.AbsNormSpanSingletonEq
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallB

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [StarRing K] in
theorem exists_det_span (b : Basis (Fin (finrank K V)) K V) {x : Fin (finrank K V) → V}
    (hx : ∀ i, x i ∈ Submodule.span (𝓞 K) (Set.range b)) :
    ∃ d : 𝓞 K, algebraMap (𝓞 K) K d = b.det x := by
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hx j)
  have hrepr : ∀ j i, b.repr (x j) i = algebraMap (𝓞 K) K (c j i) := by
    intro j i
    rw [← hc j]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [← algebraMap_smul K, map_sum, Finsupp.single_apply]
  refine ⟨(Matrix.of fun i j => c j i).det, ?_⟩
  rw [RingHom.map_det, Basis.det_apply]
  congr 1
  ext i j
  simp [Basis.toMatrix_apply, hrepr]

theorem discrIdeal_span {h : V →ₗ⋆[K] V →ₗ[K] K} (b : Basis (Fin (finrank K V)) K V) {g₀ : 𝓞 K}
    (hg : algebraMap (𝓞 K) K g₀ = gdet h b) :
    discrIdeal h (Submodule.span (𝓞 K) (Set.range b)) = Ideal.span {g₀} := by
  apply le_antisymm
  · refine discrIdeal_le b ?_
    intro x hx z hz
    obtain ⟨d, hd⟩ := exists_det_span b hx
    have hz' : z = conjO K d * g₀ * d := by
      apply IsFractionRing.injective (𝓞 K) K
      have e1 : algebraMap (𝓞 K) K (conjO K d) = star (algebraMap (𝓞 K) K d) := by
        first | rfl | simp [conjO]
      rw [hz, map_mul, map_mul, e1, hd, hg]
    rw [hz', Ideal.mem_span_singleton]
    exact ⟨conjO K d * d, by ring⟩
  · rw [Ideal.span_singleton_le_iff_mem]
    refine mem_discrIdeal b (fun i => Submodule.subset_span (Set.mem_range_self i)) ?_
    rw [Basis.det_self, hg]
    simp

omit [StarRing K] in
theorem absNorm_span_singleton_eq [_root_.NumberField.IsTotallyComplex K] (g₀ : 𝓞 K) :
    (Ideal.absNorm (Ideal.span {g₀}) : ℝ) =
      (∏ w : InfinitePlace K, w (algebraMap (𝓞 K) K g₀)) ^ 2 := by
  have hm : ∀ w : InfinitePlace K, w.mult = 2 := by
    intro w
    have hw : ¬ w.IsReal := by
      rw [InfinitePlace.not_isReal_iff_isComplex]
      exact IsTotallyComplex.isComplex w
    simp [InfinitePlace.mult, hw]
  have hp := InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 K) K g₀)
  simp only [hm] at hp
  rw [Ideal.absNorm_span_singleton, ← Finset.prod_pow, hp, Nat.cast_natAbs]
  have h3 := Algebra.coe_norm_int g₀
  rw [← h3]
  norm_cast

theorem normD_mul_relIndex (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {L : Submodule (𝓞 K) V} (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (b : Basis (Fin (finrank K V)) K V)
    (hb : ∀ i, b i ∈ L)
    (hidx : (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    normD h L * ((Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup : ℝ) =
      ∏ w : InfinitePlace K, w (gdet h b) := by
  haveI : IsTotallyComplex K := hK.1
  have hint : ∀ i j, ∃ c : 𝓞 K, algebraMap (𝓞 K) K c = h (b i) (b j) := fun i j =>
    Submodule.mem_one.1 (hLi _ (hb i) _ (hb j))
  choose c hc using hint
  have hg : algebraMap (𝓞 K) K (Matrix.of fun i j => c i j).det = gdet h b := by
    rw [RingHom.map_det]
    unfold gdet
    congr 1
    ext i j
    simp [hc]
  have hle : Submodule.span (𝓞 K) (Set.range b) ≤ L :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb i)
  obtain ⟨n, hn⟩ : ∃ n, (Submodule.span (𝓞 K) (Set.range b)).toAddSubgroup.relIndex L.toAddSubgroup = n :=
    ⟨_, rfl⟩
  rw [hn] at hidx ⊢
  have hN := absNorm_discrIdeal_of_le hK hLi b n (Submodule.span (𝓞 K) (Set.range b)) hle hn hidx
  rw [discrIdeal_span b hg] at hN
  have hS := absNorm_span_singleton_eq (Matrix.of fun i j => c i j).det
  rw [hg] at hS
  have hprod : (0 : ℝ) ≤ ∏ w : InfinitePlace K, w (gdet h b) :=
    Finset.prod_nonneg (fun w _ => w.1.nonneg _)
  have key : ((n : ℝ) * Real.sqrt (Ideal.absNorm (discrIdeal h L) : ℝ)) ^ 2 =
      (∏ w : InfinitePlace K, w (gdet h b)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _), ← hS, hN]
    push_cast
    ring
  unfold normD
  rw [← Real.sqrt_sq hprod, ← key, Real.sqrt_sq (by positivity)]
  ring

end Formalism.HermitianLattices.Ext.L3.BallB
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsASDOfTuple
noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.U0

open WA Module

variable {K V : Type*} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

variable {S : Subring K} {π : K} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem gram_det_smul_orth {n : ℕ} {y : Fin n → V} (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0)
    (d : Fin n → K) :
    (gram h fun i => d i • y i).det = (∏ i, star (d i) * d i) * ∏ i, h (y i) (y i) := by
  have hg : (gram h fun i => d i • y i) =
      Matrix.diagonal fun i => star (d i) * d i * h (y i) (y i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [gram]
      simp only [starRingEnd_apply]
      ring
    · simp [gram, Matrix.diagonal_apply_ne _ hij, horth i j hij]
  rw [hg, Matrix.det_diagonal, Finset.prod_mul_distrib]

theorem gram_det_orth {n : ℕ} {y : Fin n → V} (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0) :
    (gram h y).det = ∏ i, h (y i) (y i) := by
  have hg : gram h y = Matrix.diagonal fun i => h (y i) (y i) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [gram]
    · simp [gram, Matrix.diagonal_apply_ne _ hij, horth i j hij]
  rw [hg, Matrix.det_diagonal]

theorem expand_orth [FiniteDimensional K V] {y : Fin (finrank K V) → V}
    (horth : ∀ i j, i ≠ j → h (y i) (y j) = 0) (hne : ∀ i, h (y i) (y i) ≠ 0) (v : V) :
    v = ∑ i, (h (y i) v * (h (y i) (y i))⁻¹) • y i := by
  have hli : LinearIndependent K y := by
    rw [Fintype.linearIndependent_iff]
    intro g hg j
    have hj := congrArg (h (y j)) hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, map_zero] at hj
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero])
      (by simp)] at hj
    exact (mul_eq_zero.mp hj).resolve_right (hne j)
  by_cases h0 : finrank K V = 0
  · have : Subsingleton V := Module.finrank_zero_iff.mp h0
    exact Subsingleton.elim _ _
  have : Nonempty (Fin (finrank K V)) := ⟨⟨0, Nat.pos_of_ne_zero h0⟩⟩
  set b := basisOfLinearIndependentOfCardEqFinrank hli (Fintype.card_fin _) with hb
  have hbi : ∀ i, b i = y i := fun i => by
    rw [hb, coe_basisOfLinearIndependentOfCardEqFinrank]
  have hv : ∑ i, b.repr v i • y i = v := by
    simp_rw [← hbi]
    exact b.sum_repr v
  have hc : ∀ j, b.repr v j = h (y j) v * (h (y j) (y j))⁻¹ := by
    intro j
    rw [eq_mul_inv_iff_mul_eq₀ (hne j)]
    have hj := congrArg (h (y j)) hv
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul] at hj
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [horth j i (Ne.symm hij), mul_zero])
      (by simp)] at hj
    exact hj
  calc v = ∑ i, b.repr v i • y i := hv.symm
    _ = _ := Finset.sum_congr rfl fun i _ => by rw [hc i]

theorem exists_isASD_of_tuple [FiniteDimensional K V] (hS : IsHermSemilocal S) (hπ : IsUnif S π)
    (hs : h.IsSymm) (hd : ∀ x, h x x = 0 → x = 0) {M : AddSubgroup V} (hM : IsLatIn S h ⊤ M)
    (x : Fin (finrank K V) → V) (hx : ∀ i, x i ∈ M)
    (hdet : ¬ Dv S π ((gram h x).det * π⁻¹))
    (hall : ∀ t : Fin (finrank K V) → V, (∀ i, t i ∈ M) → (∀ i j, i ≠ j → h (t i) (t j) = 0) →
      Dv S π (gram h t).det) :
    ∃ z, IsASD S π h ⊤ M z := by
  obtain ⟨y, horth, hspan⟩ := exists_orth_tuple hS hπ hs _ x
    (fun i j => hM.int _ (hx i) _ (hx j)) hdet
  have hyM : ∀ i, y i ∈ M := by
    intro i
    have h1 : y i ∈ spanS S x := by rw [← hspan]; exact mem_spanS y i
    exact spanS_induction (p := fun v => v ∈ M) M.zero_mem (fun a b => M.add_mem)
      (fun c hc a ha => hM.smul_mem c hc a ha) hx _ h1
  have haS : ∀ i, h (y i) (y i) ∈ S := fun i => hM.int _ (hyM i) _ (hyM i)
  obtain ⟨c, hcS, hcdet⟩ := gram_det_of_le (h := h) hS
    (fun i => by rw [hspan]; exact mem_spanS x i : ∀ i, x i ∈ spanS S y)
  rw [gram_det_orth horth] at hcdet
  have hPd : Dv S π (∏ i, h (y i) (y i)) := by
    rw [← gram_det_orth horth]; exact hall y hyM horth
  have hPn : ¬ Dv S π ((∏ i, h (y i) (y i)) * π⁻¹) := by
    intro hdv
    apply hdet
    rw [hcdet, mul_assoc]
    exact hdv.mul_left hcS
  have hPf : star ((∏ i, h (y i) (y i)) * π⁻¹) = (∏ i, h (y i) (y i)) * π⁻¹ := by
    rw [star_mul', star_inv₀, hπ.fix, ← starRingEnd_apply, map_prod]
    congr 1
    exact Finset.prod_congr rfl fun i _ => hs.eq _ _
  have hPu : IsUnitIn S ((∏ i, h (y i) (y i)) * π⁻¹) := unit_of_not_dv hπ hPd hPf hPn
  obtain ⟨i₁, hi₁⟩ : ∃ i₁, ¬ IsUnitIn S (h (y i₁) (y i₁)) := by
    by_contra hcon
    push Not at hcon
    exact unit_not_dv hπ (LocF.isUnitIn_prod Finset.univ _ fun i _ => hcon i) hPd
  have hd₁ : Dv S π (h (y i₁) (y i₁)) := dv_of_not_unit hπ (haS i₁) (hs.eq _ _) hi₁
  have hQS : ∏ i ∈ Finset.univ.erase i₁, h (y i) (y i) ∈ S := S.prod_mem fun i _ => haS i
  have hsplit : (∏ i, h (y i) (y i)) * π⁻¹ =
      h (y i₁) (y i₁) * π⁻¹ * ∏ i ∈ Finset.univ.erase i₁, h (y i) (y i) := by
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₁)]
    ring
  have hQu : IsUnitIn S (∏ i ∈ Finset.univ.erase i₁, h (y i) (y i)) :=
    isUnitIn_of_mul hd₁ hQS (hsplit ▸ hPu)
  have hzu : IsUnitIn S (h (y i₁) (y i₁) * π⁻¹) :=
    isUnitIn_of_mul hQS hd₁ (by rw [mul_comm, ← hsplit]; exact hPu)
  have hau : ∀ i, i ≠ i₁ → IsUnitIn S (h (y i) (y i)) := by
    intro i hi
    have hmem : i ∈ Finset.univ.erase i₁ := Finset.mem_erase.mpr ⟨hi, Finset.mem_univ i⟩
    have e := Finset.mul_prod_erase (Finset.univ.erase i₁) (fun i => h (y i) (y i)) hmem
    refine isUnitIn_of_mul (S.prod_mem fun j _ => haS j :
      ∏ j ∈ (Finset.univ.erase i₁).erase i, h (y j) (y j) ∈ S) (haS i) ?_
    rw [mul_comm, e]
    exact hQu
  have hne : ∀ i, h (y i) (y i) ≠ 0 := by
    intro i
    by_cases hi : i = i₁
    · rw [hi]; exact left_ne_zero_of_mul hzu.1
    · exact (hau i hi).1
  have hexp := expand_orth horth hne

  have hprim : ∀ c : K, c • y i₁ ∈ M → c ∈ S := by
    have hy0 : y i₁ ≠ 0 := by
      intro h0
      apply hne i₁
      rw [h0]; simp
    obtain ⟨l, hl0, hl, hdiv⟩ := exists_primitive hS hd hM (Submodule.mem_top : y i₁ ∈ ⊤) hy0
    have hli : l⁻¹ ∈ S := by
      have := hdiv 1 (by rw [one_smul]; exact hyM i₁)
      rwa [one_mul] at this
    have hNl : star l * l ∈ S := by
      have h1 := hall (fun i => (if i = i₁ then l else 1) • y i) (by
        intro i
        by_cases hi : i = i₁
        · simp only [hi, ite_true]; exact hl
        · simp only [hi, ite_false, one_smul]; exact hyM i) (by
        intro i j hij
        simp only [map_smulₛₗ, LinearMap.smul_apply, horth i j hij, smul_zero])
      rw [gram_det_smul_orth horth] at h1
      have e : (∏ i, star (if i = i₁ then l else 1) * (if i = i₁ then l else 1)) = star l * l := by
        rw [Finset.prod_eq_single i₁]
        · simp
        · intro j _ hj; simp [hj]
        · intro hi; exact absurd (Finset.mem_univ i₁) hi
      rw [e] at h1
      unfold Dv at h1
      have h2 := S.mul_mem h1 hPu.2.2
      have h0 := hPu.1
      have e2 : star l * l * (∏ i, h (y i) (y i)) * π⁻¹ * ((∏ i, h (y i) (y i)) * π⁻¹)⁻¹ =
          star l * l := by
        rw [mul_assoc (star l * l), mul_assoc, mul_inv_cancel₀ h0, mul_one]
      rwa [e2] at h2
    have hlS : l ∈ S := by
      have hu : IsUnitIn S (star l⁻¹ * l⁻¹) := by
        refine ⟨mul_ne_zero (star_ne_zero.mpr (inv_ne_zero hl0)) (inv_ne_zero hl0),
          S.mul_mem (hS.star_mem _ hli) hli, ?_⟩
        rw [star_inv₀, mul_inv, inv_inv, inv_inv]
        exact hNl
      have := (isUnitIn_of_mul (hS.star_mem _ hli) hli hu).2.2
      rwa [inv_inv] at this
    intro c hc
    have := S.mul_mem (hdiv c hc) hlS
    rwa [mul_assoc, inv_mul_cancel₀ hl0, mul_one] at this
  refine ⟨y i₁, hM, hyM i₁, hzu, ?_, ?_⟩
  · intro m hm
    have hcS : ∀ i, i ≠ i₁ → h (y i) m * (h (y i) (y i))⁻¹ ∈ S := fun i hi =>
      S.mul_mem (hM.int _ (hyM i) _ hm) (hau i hi).2.2
    have h1 : (h (y i₁) m * (h (y i₁) (y i₁))⁻¹) • y i₁ ∈ M := by
      have e := Finset.add_sum_erase Finset.univ
        (fun i => (h (y i) m * (h (y i) (y i))⁻¹) • y i) (Finset.mem_univ i₁)
      rw [← hexp m] at e
      rw [eq_sub_of_add_eq e]
      exact M.sub_mem hm (M.sum_mem fun i hi =>
        hM.smul_mem _ (hcS i (Finset.mem_erase.mp hi).1) _ (hyM i))
    have h2 := hd₁.mul_left (hprim _ h1)
    rwa [mul_assoc, inv_mul_cancel₀ (hne i₁), mul_one] at h2
  · intro v _ hzv hv
    rw [hexp v]
    refine M.sum_mem fun i _ => ?_
    by_cases hi : i = i₁
    · rw [hi, hzv, zero_mul, zero_smul]; exact M.zero_mem
    · exact hM.smul_mem _ (S.mul_mem (hv _ (hyM i)) (hau i hi).2.2) _ (hyM i)

end Formalism.HermitianLattices.Ext.L3.U0
end
end
