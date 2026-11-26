module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.SameGenusFix
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocalJacobianOfDoubleCoset

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.JordanExists
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.Cnt

open Formalism.HermitianLattices.Ext.L3

def NondegOn {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (X : Submodule K V) : Prop :=
  ∀ x ∈ X, (∀ y ∈ X, h x y = 0) → x = 0

def JordanExists : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm →
    (∀ (X : Submodule K V) (L : Submodule (𝓞 K) V), NondegOn h X → IsLatIn X L →
      Formalism.HermitianLatticesTheory.IsIntegralLat h L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∃ b a, IsJordanIn h X L 𝔭 b a) ∧
    (∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      ∀ b a, IsJordanIn h ⊤ L 𝔭 b a → vd h L 𝔭 = vJof 𝔭 a)

def JordanInv : Prop :=
  ∀ (K F V V' : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ (h : V →ₗ⋆[K] V →ₗ[K] K) (h' : V' →ₗ⋆[K] V' →ₗ[K] K),
    h.IsSymm → h'.IsSymm → ∀ (X : Submodule K V) (X' : Submodule K V') (L : Submodule (𝓞 K) V)
    (L' : Submodule (𝓞 K) V'), IsLatIn X L → IsLatIn X' L' → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
    ∀ b a b' a', IsJordanIn h X L 𝔭 b a → IsJordanIn h' X' L' 𝔭 b' a' →
      Nonempty (DiscMod h X L 𝔭 ≃ₗ[𝓞 K] DiscMod h' X' L' 𝔭) →
      ∀ j : ℕ, ∑ i, min (vF 𝔭 (a i)) j = ∑ i, min (vF 𝔭 (a' i)) j

def JordanIsom : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ L L' : Submodule (𝓞 K) V, Submodule.IsLattice K L →
    Submodule.IsLattice K L' → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a b' a',
      IsJordanIn h ⊤ L 𝔭 b a → IsJordanIn h ⊤ L' 𝔭 b' a' → (∀ i, vF 𝔭 (a i) = vF 𝔭 (a' i)) →
      ∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 L'

def AlphaDisc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → IsTotPosDef h → ∀ L : Submodule (𝓞 K) V, Submodule.IsLattice K L →
    Formalism.HermitianLatticesTheory.IsIntegralLat h L → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → ∀ b a, IsJordanIn h ⊤ L 𝔭 b a →
      alphaL h L 𝔭 = (discAut h ⊤ L 𝔭 : ℝ) * alphaStd K 𝔭 (finrank K V - cJof 𝔭 a)

def GlueLoc : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) →
    ∀ M T : Submodule (𝓞 K) V, IsLatIn U M → IsLatIn (orthK h U) T → ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal →
      (fibP h U 𝔭 M T ≠ 0 →
        Nonempty (DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h (orthK h U) T 𝔭) ∧
        fibP h U 𝔭 M T = discAut h (orthK h U) T 𝔭) ∧
      ∀ g ∈ isomFix h U, fibP h U 𝔭 M (Formalism.HermitianLatticesTheory.gmap g T) = fibP h U 𝔭 M T

def GlueExists : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    (∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M →
    (∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → cJ h U M 𝔭 < finrank K (orthK h U)) →
      (GlueSet h U M).Nonempty

def GlueProd : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → ∀ Λ₀ ∈ GlueSet h U M,
    ∀ T : Submodule (𝓞 K) V, IsLatIn (orthK h U) T →
      ((∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → fibP h U 𝔭 M T ≠ 0) ↔
        SameGenusFix (F := F) h U (Λ₀ ⊓ (orthK h U).restrictScalars (𝓞 K)) T) ∧
      Nat.card {Λ : Submodule (𝓞 K) V // Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T} =
        ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibP h U 𝔭.1 M T

def GlueMass : Prop :=
  ∀ (K F V : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F → ∀ h : V →ₗ⋆[K] V →ₗ[K] K, h.IsSymm → Nondeg h → ∀ U : Submodule K V, IsCompl U (orthK h U) → PosDefOn h (orthK h U) →
    ∀ M : Submodule (𝓞 K) V, IsLatIn U M → Formalism.HermitianLatticesTheory.IsIntegralLat h M → (GlueSet h U M).Nonempty →
    ∀ c : ℝ, MassConst K F (finrank K (orthK h U)) c →
      ∃ s : Finset (Submodule (𝓞 K) V), (∀ Λ ∈ s, Λ ∈ GlueSet h U M) ∧
        (∀ Λ ∈ GlueSet h U M, ∃! Λ₁, Λ₁ ∈ s ∧ ∃ g ∈ isomFix h U, Formalism.HermitianLatticesTheory.gmap g Λ₁ = Λ) ∧
        (∀ Λ ∈ s, (stabFix h U Λ).Finite) ∧
        ∑ Λ ∈ s, ((Nat.card (stabFix h U Λ) : ℕ) : ℝ)⁻¹ =
          c * nM F h U M ^ finrank K (orthK h U) *
            ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaStd K 𝔭.1 (finrank K (orthK h U)) /
              alphaStd K 𝔭.1 (finrank K (orthK h U) - cJ h U M 𝔭.1)

end Formalism.L2.SG.Pf.Cnt
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocFSubspace
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G7

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem mem_dual_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule (𝓞 K) K) := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

private lemma mem_locF_lemma {W : Type} [AddCommGroup W] [Module (𝓞 K) W] (𝔭 : Ideal (𝓞 F))
    (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma star_fix_lemma_2 (hF : IsFixF K F) {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    star (algebraMap (𝓞 K) K s) = algebraMap (𝓞 K) K s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, -, rfl⟩ := hx
    exact (hF _).mpr ⟨(t : F), rfl⟩
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul, star_mul', hx, hy]

private lemma smul_smul_lemma_3 (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {𝔭 : Ideal (𝓞 F)} {s t : 𝓞 K}
    (ht : t ∈ Submonoid.closure {s : 𝓞 K | ∃ u : 𝓞 F, u ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) u = s})
    (x y : V) : h (t • y) (s • x) = (t * s) • h y x := by
  rw [← algebraMap_smul K t y, ← algebraMap_smul K s x]
  simp only [map_smulₛₗ, LinearMap.smul_apply, RingHom.id_apply, smul_eq_mul, starRingEnd_apply]
  rw [star_fix_lemma_2 hF ht, Algebra.smul_def, map_mul]
  ring

theorem locF_dual_le (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V)
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) : locF 𝔭 (Formalism.HermitianLatticesTheory.dual h L) ≤ dualF h 𝔭 (locF 𝔭 L) := by
  intro x hx
  change ∀ y ∈ locF 𝔭 L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)
  intro y hy
  obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
  obtain ⟨t, ht, hty⟩ := (mem_locF_lemma 𝔭 _ y).mp hy
  refine (mem_locF_lemma 𝔭 _ _).mpr ⟨t * s, Submonoid.mul_mem _ ht hs, ?_⟩
  rw [← smul_smul_lemma_3 hF h ht x y]
  exact (mem_dual_iff h L (s • x)).mp hsx (t • y) hty

theorem dualF_locF_le (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : L.FG)
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) : dualF h 𝔭 (locF 𝔭 L) ≤ locF 𝔭 (Formalism.HermitianLatticesTheory.dual h L) := by
  classical
  intro x hx
  have hx' : ∀ y ∈ locF 𝔭 L, h y x ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := hx
  obtain ⟨G, rfl⟩ := hL
  have hg : ∀ g ∈ G, ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s},
      s • h g x ∈ (1 : Submodule (𝓞 K) K) := fun g hg =>
    (mem_locF_lemma 𝔭 _ _).mp (hx' g ((mem_locF_lemma 𝔭 _ g).mpr
      ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span hg⟩))
  choose! sg hsg hsgx using hg
  refine (mem_locF_lemma 𝔭 _ _).mpr
    ⟨∏ g ∈ G, sg g, Submonoid.prod_mem _ fun g hg => hsg g hg, ?_⟩
  rw [mem_dual_iff]
  intro y hy
  induction hy using Submodule.span_induction with
  | mem y hy =>
    rw [← algebraMap_smul K (∏ g ∈ G, sg g) x, LinearMap.map_smul, smul_eq_mul]
    have e : algebraMap (𝓞 K) K (∏ g ∈ G, sg g) * h y x =
        (∏ g ∈ G.erase y, sg g) • (sg y • h y x) := by
      rw [← Finset.mul_prod_erase G sg hy, Algebra.smul_def, Algebra.smul_def, map_mul]
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (hsgx y hy)
  | zero => rw [map_zero, LinearMap.zero_apply]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add (f := _), LinearMap.add_apply]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy =>
    obtain ⟨r, hr⟩ := Formalism.HermitianLatticesTheory.star_algebraMap_ringOfIntegers_mem_range c
    rw [← algebraMap_smul K c y, map_smulₛₗ h (algebraMap (𝓞 K) K c) y, LinearMap.smul_apply,
      smul_eq_mul, starRingEnd_apply, ← hr, ← smul_eq_mul, algebraMap_smul]
    exact Submodule.smul_mem _ r hy

theorem locF_dual (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V} (hL : L.FG)
    {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) : locF 𝔭 (Formalism.HermitianLatticesTheory.dual h L) = dualF h 𝔭 (locF 𝔭 L) := le_antisymm (locF_dual_le hF h L hp) (dualF_locF_le h hL hp)

private lemma ne_zero_lemma_4 {𝔭 : Ideal (𝓞 F)} {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    algebraMap (𝓞 K) K s ≠ 0 := by
  induction hs using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    have ht0 : t ≠ 0 := fun h0 => ht (h0 ▸ 𝔭.zero_mem)
    have e : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) = algebraMap F K (t : F) := rfl
    rw [e]
    exact (map_ne_zero _).mpr (by simpa using ht0)
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_ne_zero hx hy

theorem locF_subspace (U : Submodule K V) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) :
    locF 𝔭 (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) := by
  ext x
  rw [mem_locF_lemma]
  constructor
  · rintro ⟨s, hs, hsx⟩
    have hs0 : algebraMap (𝓞 K) K s ≠ 0 := ne_zero_lemma_4 hs
    have e : x = (algebraMap (𝓞 K) K s)⁻¹ • (s • x) := by
      rw [← algebraMap_smul K s x, smul_smul, inv_mul_cancel₀ hs0, one_smul]
    rw [e]
    exact U.smul_mem _ hsx
  · intro hx
    exact ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩

private lemma mem_image_lemma_5 {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {s : 𝓞 K}
    (hs : s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s := by
  induction hs using Submonoid.closure_induction with
  | mem x hx => exact hx
  | one => exact ⟨1, (Ideal.ne_top_iff_one 𝔭).mp hp.ne_top, map_one _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a * b, fun hab => (hp.mem_or_mem hab).elim ha hb, map_mul _ _ _⟩

private lemma le_of_locF_lemma_6 (A B : Submodule (𝓞 K) V)
    (hAB : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → locF 𝔭 A = locF 𝔭 B) : A ≤ B := by
  intro x hx
  let J : Ideal (𝓞 F) :=
    Ideal.comap (algebraMap (𝓞 F) (𝓞 K)) (B.comap (LinearMap.toSpanSingleton (𝓞 K) V x))
  have hJ : J = ⊤ := by
    by_contra hne
    obtain ⟨𝔭, hmax, hle⟩ := Ideal.exists_le_maximal J hne
    have hxA : x ∈ locF 𝔭 A :=
      (mem_locF_lemma 𝔭 A x).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
    rw [hAB 𝔭 hmax] at hxA
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 B x).mp hxA
    obtain ⟨t, ht, rfl⟩ := mem_image_lemma_5 hmax.isPrime hs
    exact ht (hle (show t ∈ J from hsx))
  have h1 : (1 : 𝓞 F) ∈ J := by rw [hJ]; exact Submodule.mem_top
  simpa [J] using h1

theorem eq_of_locF (A B : Submodule (𝓞 K) V)
    (hAB : ∀ 𝔭 : Ideal (𝓞 F), 𝔭.IsMaximal → locF 𝔭 A = locF 𝔭 B) : A = B := le_antisymm (le_of_locF_lemma_6 A B hAB) (le_of_locF_lemma_6 B A fun 𝔭 h => (hAB 𝔭 h).symm)

end Formalism.L2.SG.Pf.G7
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DiscIsoOfProj
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def prO {X Y : Submodule K V} (hc : IsCompl X Y) : V →ₗ[𝓞 K] V :=
  (X.projection Y hc).restrictScalars (𝓞 K)

theorem prO_apply {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) :
    prO hc x = X.projection Y hc x := rfl

theorem prO_add {X Y : Submodule K V} (hc : IsCompl X Y) (x : V) :
    prO hc x + prO hc.symm x = x :=
  Submodule.projection_add_projection_eq_self hc x

def toDisc (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y) (L Λ : Submodule (𝓞 K) V)
    (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L)) :
    ↥Λ →ₗ[𝓞 K] DiscMod h X L 𝔭 :=
  Submodule.mkQ _ ∘ₗ LinearMap.codRestrict _ (prO hc ∘ₗ Λ.subtype) (fun x => hP x x.2)

theorem toDisc_surj (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y)
    (L Λ : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L))
    (hS : ∀ v ∈ locF 𝔭 (dualIn h X L), ∃ x ∈ Λ, prO hc x = v) :
    Function.Surjective (toDisc h hc L Λ 𝔭 hP) := by
  refine (Submodule.mkQ_surjective _).comp ?_
  rintro ⟨v, hv⟩
  obtain ⟨x, hx, e⟩ := hS v hv
  exact ⟨⟨x, hx⟩, Subtype.ext e⟩

theorem mem_ker_toDisc (h : V →ₗ⋆[K] V →ₗ[K] K) {X Y : Submodule K V} (hc : IsCompl X Y)
    (L Λ : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (hP : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h X L))
    (x : ↥Λ) : x ∈ LinearMap.ker (toDisc h hc L Λ 𝔭 hP) ↔ prO hc (x : V) ∈ locF 𝔭 L := by
  rw [LinearMap.mem_ker]
  change Submodule.Quotient.mk _ = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
  rfl

theorem prO_mem_iff {X Y : Submodule K V} (hc : IsCompl X Y) {L Λ : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (hX : Λ ⊓ X.restrictScalars (𝓞 K) = locF 𝔭 L) (x : V) :
    prO hc x ∈ locF 𝔭 L ↔ prO hc x ∈ Λ := by
  rw [← hX, Submodule.mem_inf]
  constructor
  · exact fun H => H.1
  · intro H
    exact ⟨H, Submodule.projection_apply_mem hc x⟩

theorem discIso_of_proj (h : V →ₗ⋆[K] V →ₗ[K] K) {U W : Submodule K V} (hc : IsCompl U W)
    {M T Λ : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)}
    (hU : Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M) (hW : Λ ⊓ W.restrictScalars (𝓞 K) = locF 𝔭 T)
    (hPU : ∀ x ∈ Λ, prO hc x ∈ locF 𝔭 (dualIn h U M))
    (hSU : ∀ v ∈ locF 𝔭 (dualIn h U M), ∃ x ∈ Λ, prO hc x = v)
    (hPW : ∀ x ∈ Λ, prO hc.symm x ∈ locF 𝔭 (dualIn h W T))
    (hSW : ∀ v ∈ locF 𝔭 (dualIn h W T), ∃ x ∈ Λ, prO hc.symm x = v) :
    Nonempty (DiscMod h U M 𝔭 ≃ₗ[𝓞 K] DiscMod h W T 𝔭) := by
  have hker : LinearMap.ker (toDisc h hc M Λ 𝔭 hPU) = LinearMap.ker (toDisc h hc.symm T Λ 𝔭 hPW) := by
    ext x
    rw [mem_ker_toDisc, mem_ker_toDisc, prO_mem_iff hc hU, prO_mem_iff hc.symm hW]
    have e := prO_add hc (x : V)
    constructor
    · intro H
      have : prO hc.symm (x : V) = (x : V) - prO hc (x : V) := eq_sub_of_add_eq' e
      rw [this]
      exact Λ.sub_mem x.2 H
    · intro H
      have : prO hc (x : V) = (x : V) - prO hc.symm (x : V) := eq_sub_of_add_eq e
      rw [this]
      exact Λ.sub_mem x.2 H
  exact ⟨((LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc M Λ 𝔭 hPU hSU)).symm.trans
    (Submodule.quotEquivOfEq _ _ hker)).trans
    (LinearMap.quotKerEquivOfSurjective _ (toDisc_surj h hc.symm T Λ 𝔭 hPW hSW))⟩

end Formalism.L2.SG.Pf.G6
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GmapEqSelfOfFix
open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G6

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem gmap_eq_iff (g : V ≃ₗ[K] V) {A B : Submodule (𝓞 K) V} :
    Formalism.HermitianLatticesTheory.gmap g A = Formalism.HermitianLatticesTheory.gmap g B ↔ A = B := by
  constructor
  · intro e
    rw [← Formalism.HermitianLatticesTheory.isomAct_gmap_symm g A, ← Formalism.HermitianLatticesTheory.isomAct_gmap_symm g B, e]
  · rintro rfl
    rfl

theorem gmap_inf (g : V ≃ₗ[K] V) (A B : Submodule (𝓞 K) V) :
    Formalism.HermitianLatticesTheory.gmap g (A ⊓ B) = Formalism.HermitianLatticesTheory.gmap g A ⊓ Formalism.HermitianLatticesTheory.gmap g B := by
  ext x
  simp only [Submodule.mem_inf, Formalism.HermitianLatticesTheory.isomAct_mem_gmap]

theorem gmap_eq_self_of_fix (g : V ≃ₗ[K] V) {A : Submodule (𝓞 K) V} (hA : ∀ x ∈ A, g x = x) :
    Formalism.HermitianLatticesTheory.gmap g A = A := by
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  constructor
  · intro hx
    have e := hA _ hx
    rw [LinearEquiv.apply_symm_apply] at e
    rw [e]
    exact hx
  · intro hx
    have e := hA _ hx
    have : g.symm x = x := by
      conv_lhs => rw [← e]
      simp
    rw [this]
    exact hx

theorem mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {v : V} :
    v ∈ orthK h U ↔ ∀ u ∈ U, h u v = 0 := by
  simp [orthK, Submodule.mem_iInf, LinearMap.mem_ker]

theorem map_mem_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) {v : V} (hv : v ∈ orthK h U) : g v ∈ orthK h U := by
  rw [mem_orthK] at hv ⊢
  intro u hu
  have e1 : h (g u) (g v) = h u v := hg.1 u v
  rw [hg.2 u hu] at e1
  rw [e1, hv u hu]

theorem gmap_orthK {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    Formalism.HermitianLatticesTheory.gmap g ((orthK h U).restrictScalars (𝓞 K)) = (orthK h U).restrictScalars (𝓞 K) := by
  have hgi : g⁻¹ ∈ isomFix h U := (isomFix h U).inv_mem hg
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap, Submodule.restrictScalars_mem, Submodule.restrictScalars_mem]
  constructor
  · intro hx
    have := map_mem_orthK hg hx
    simpa using this
  · intro hx
    exact map_mem_orthK hgi hx

theorem gmap_U {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    Formalism.HermitianLatticesTheory.gmap g (U.restrictScalars (𝓞 K)) = U.restrictScalars (𝓞 K) :=
  gmap_eq_self_of_fix g fun x hx => hg.2 x hx

theorem dualF_gmap {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (𝔭 : Ideal (𝓞 F)) (Λ : Submodule (𝓞 K) V) :
    dualF h 𝔭 (Formalism.HermitianLatticesTheory.gmap g Λ) = Formalism.HermitianLatticesTheory.gmap g (dualF h 𝔭 Λ) := by
  ext x
  rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]
  change (∀ y ∈ Formalism.HermitianLatticesTheory.gmap g Λ, h y x ∈ _) ↔ ∀ y ∈ Λ, h y (g.symm x) ∈ _
  constructor
  · intro H y hy
    have := H (g y) (by rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap]; simpa using hy)
    have e : h (g y) (g (g.symm x)) = h y (g.symm x) := hg y (g.symm x)
    rw [LinearEquiv.apply_symm_apply] at e
    rwa [e] at this
  · intro H y hy
    rw [Formalism.HermitianLatticesTheory.isomAct_mem_gmap] at hy
    have := H _ hy
    have e : h (g (g.symm y)) (g (g.symm x)) = h (g.symm y) (g.symm x) := hg _ _
    rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at e
    rwa [e]

theorem le_of_isLatIn {X : Submodule K V} {L : Submodule (𝓞 K) V} (hL : IsLatIn X L) :
    ∀ x ∈ L, x ∈ X := by
  intro x hx
  rw [← hL.2]
  exact Submodule.subset_span hx

theorem fibP_gmap [FiniteDimensional K V] {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V} {M : Submodule (𝓞 K) V}
    (hM : IsLatIn U M) (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V) {g : V ≃ₗ[K] V}
    (hg : g ∈ isomFix h U) :
    fibP h U 𝔭 M (Formalism.HermitianLatticesTheory.gmap g T) = fibP h U 𝔭 M T := by
  have hMg : Formalism.HermitianLatticesTheory.gmap g M = M := gmap_eq_self_of_fix g fun x hx => hg.2 x (le_of_isLatIn hM x hx)
  let e : Submodule (𝓞 K) V ≃ Submodule (𝓞 K) V :=
    { toFun := Formalism.HermitianLatticesTheory.gmap g
      invFun := Formalism.HermitianLatticesTheory.gmap g.symm
      left_inv := fun Λ => Formalism.HermitianLatticesTheory.isomAct_gmap_symm _ Λ
      right_inv := fun Λ => by
        have := Formalism.HermitianLatticesTheory.isomAct_gmap_symm g.symm Λ
        simpa using this }
  unfold fibP
  refine (Nat.card_congr (Equiv.subtypeEquiv e ?_)).symm
  intro Λ
  change _ ↔ ((∃ Λ₀ : Submodule (𝓞 K) V, Submodule.IsLattice K Λ₀ ∧ locF 𝔭 Λ₀ = Formalism.HermitianLatticesTheory.gmap g Λ) ∧
    dualF h 𝔭 (Formalism.HermitianLatticesTheory.gmap g Λ) = Formalism.HermitianLatticesTheory.gmap g Λ ∧
    Formalism.HermitianLatticesTheory.gmap g Λ ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M ∧
    Formalism.HermitianLatticesTheory.gmap g Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g T))
  have e1 : Formalism.HermitianLatticesTheory.gmap g Λ ⊓ U.restrictScalars (𝓞 K) =
      Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ U.restrictScalars (𝓞 K)) := by rw [gmap_inf, gmap_U hg]
  have e2 : locF 𝔭 M = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 M) := by rw [LocalizedFibreSets.gmap_locF, hMg]
  have e3 : Formalism.HermitianLatticesTheory.gmap g Λ ⊓ (orthK h U).restrictScalars (𝓞 K) =
      Formalism.HermitianLatticesTheory.gmap g (Λ ⊓ (orthK h U).restrictScalars (𝓞 K)) := by rw [gmap_inf, gmap_orthK hg]
  have e4 : locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g T) = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 T) := (LocalizedFibreSets.gmap_locF g 𝔭 T).symm
  rw [dualF_gmap hg.1, gmap_eq_iff, e1, e3, e4, gmap_eq_iff]
  conv_rhs => rw [e2, gmap_eq_iff]
  refine and_congr_left fun _ => ?_
  have lattice_gmap (a : V ≃ₗ[K] V) {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
      Submodule.IsLattice K (Formalism.HermitianLatticesTheory.gmap a L) :=
    Submodule.IsLattice.of_fg K (hL.fg.map _)
  constructor
  · rintro ⟨Λ₀, h0, e0⟩
    exact ⟨Formalism.HermitianLatticesTheory.gmap g Λ₀, lattice_gmap g h0, by rw [← LocalizedFibreSets.gmap_locF, e0]⟩
  · rintro ⟨Λ₀, h0, e0⟩
    refine ⟨Formalism.HermitianLatticesTheory.gmap g.symm Λ₀, lattice_gmap g.symm h0, ?_⟩
    rw [← LocalizedFibreSets.gmap_locF, e0, Formalism.HermitianLatticesTheory.isomAct_gmap_symm]

end Formalism.L2.SG.Pf.G6
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.NcRealXMeas
noncomputable section

open MeasureTheory Matrix
open scoped ENNReal

namespace Formalism.L2.SG.Pf.NcReal.JX

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.Pf.WFL Formalism.L2.SG.Pf Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

variable {r k : ℕ} {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ} {z0 : Fin (2 * r + k + 1) → ℂ}

theorem embQ (hF : IsFrameJ ε e f wf z0) :
    MeasurableEmbedding (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) :=
  cM_measEmb (ε := ε) (A := Qi ε e f wf z0) (B := Qm e f wf z0) (A' := Qm e f wf z0) (B' := Qi ε e f wf z0)
    (Qm_mul_Qi hF) (Qm_mul_Qi hF)

theorem Qm_e (a : Fin r) : Qm e f wf z0 *ᵥ bvec (eI k r a) = e a := by rw [Qm_mulVec_bvec, colQ_eI]

theorem Qm_f (a : Fin r) : Qm e f wf z0 *ᵥ bvec (esI k r a) = f a := by rw [Qm_mulVec_bvec, colQ_esI]

theorem conj_fix (hF : IsFrameJ ε e f wf z0) {s : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    {v : Fin (2 * r + k + 1) → ℂ} (hv : s *ᵥ v = v) :
    (Qm e f wf z0 * s * Qi ε e f wf z0) *ᵥ (Qm e f wf z0 *ᵥ v) = Qm e f wf z0 *ᵥ v := by
  rw [Matrix.mulVec_mulVec]
  have e1 : Qm e f wf z0 * s * Qi ε e f wf z0 * Qm e f wf z0 = Qm e f wf z0 * s := by
    rw [Matrix.mul_assoc (Qm e f wf z0 * s), Qi_mul_Qm hF, Matrix.mul_one]
  rw [e1, ← Matrix.mulVec_mulVec, hv]

theorem measW_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} {μH : Measure (Formalism.REAL.UJ ε)}
    (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH) :
    Formalism.MainNotions.S.IsHaarOn (UWset k r zB) (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
  have emb := embQ hF
  obtain ⟨hsf, hne, hcon, hinv⟩ := hH
  haveI := hsf
  refine ⟨emb.sigmaFinite_map, (Measure.map_ne_zero_iff emb.measurable.aemeasurable).mpr hne, ?_, ?_⟩
  · rw [emb.map_apply]
    refine measure_mono_null (fun g hg => ?_) hcon
    intro hgH
    apply hg
    exact conj_mem_UWset hF rfl (uMat_mem g) (fun a => (hgH.1 a).1) (fun a => (hgH.1 a).2) hgH.2
  · intro s hs
    have ht := conjQ_UJ hF hs.1
    set t := toUJ (Qm e f wf z0 * s * Qi ε e f wf z0) ht
    have htH : t ∈ Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB) := by
      show (∀ a, uMat t *ᵥ e a = e a ∧ uMat t *ᵥ f a = f a) ∧ uMat t *ᵥ (Qm e f wf z0 *ᵥ zB) = Qm e f wf z0 *ᵥ zB
      rw [uMat_toUJ]
      refine ⟨fun a => ⟨?_, ?_⟩, conj_fix hF hs.2.2⟩
      · rw [← Qm_e (e := e) (f := f) (wf := wf) (z0 := z0) a]; exact conj_fix hF (hs.2.1 a).1
      · rw [← Qm_f (e := e) (f := f) (wf := wf) (z0 := z0) a]; exact conj_fix hF (hs.2.1 a).2
    rw [Measure.map_map (measurable_lmulM s) emb.measurable]
    have hfun : lmulM s ∘ cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) =
        cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) ∘ (fun g : Formalism.REAL.UJ ε => t * g) := by
      funext g
      simp only [Function.comp, lmulM_cM]
      unfold cM
      rw [uMat_mul, uMat_toUJ]
      simp only [← Matrix.mul_assoc, Qi_mul_Qm hF, Matrix.one_mul]
      try rfl
    rw [hfun, ← Measure.map_map emb.measurable (measurable_const_mul t), hinv t htH]

theorem measN_of (hF : IsFrameJ ε e f wf z0) (κ : ℝ) :
    (ENNReal.ofReal κ • refN ε e f wf z0).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
      Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ) := by
  have emb := embQ hF
  rw [Measure.map_smul _ emb.measurable.aemeasurable, refN, emb.map_comap, Jac.haarLie_eq_smul (Nset k r) (ENNReal.ofReal κ)]
  congr 1
  refine Measure.restrict_eq_self_of_ae_mem ?_
  have hc : (Formalism.MainNotions.S.haarLie (Nset k r) 1) {x | Matrix.of x ∉ Nset k r} = 0 := Jac.nilradical_measure_is_haar.2.2.1
  refine ae_iff.2 (measure_mono_null (fun x hx => ?_) hc)
  simp only [Set.mem_setOf_eq] at hx ⊢
  intro hxN
  apply hx
  have hU := conjQ_UJ hF hxN.1
  refine ⟨toUJ _ hU, ?_⟩
  show Qi ε e f wf z0 * uMat (toUJ _ hU) * Qm e f wf z0 = x
  rw [uMat_toUJ, Qi_Qm_conj hF]
  rfl

theorem haarN_of (κ : ℝ) (hκ : 0 < κ) : Formalism.MainNotions.S.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) :=
  Formalism.MainNotions.BridgeCSB.haarLieN k r _ (ENNReal.ofReal_pos.2 hκ).ne' ENNReal.ofReal_ne_top

theorem psi_mul (hF : IsFrameJ ε e f wf z0) (n h : Formalism.REAL.UJ ε) :
    cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) (n * h) =
      Jac.mm (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) n) (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) h) :=
  (cM_comp_mul hF (Qm e f wf z0) n h).symm

theorem measS_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB)
    (hT : 0 < Tz k r zB) {μH : Measure (Formalism.REAL.UJ ε)} (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH)
    (κ : ℝ) (hκ : 0 < κ) :
    (muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)) =
      Formalism.MainNotions.S.muS (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0)))
        (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) := by
  have emb := embQ hF
  have hW := measW_of hF hH
  have hN := haarN_of (k := k) (r := r) κ hκ
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  set μW := μH.map Ψ with hμW
  set μN := Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ) with hμN
  set μN' := ENNReal.ofReal κ • refN ε e f wf z0 with hμN'
  haveI : SigmaFinite μH := hH.1
  haveI : SigmaFinite μW := hW.1
  haveI : SigmaFinite μN := hN.1
  have hNmap : μN'.map Ψ = μN := measN_of hF κ
  have hWB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) μN := Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ hN
  apply Measure.ext_of_lintegral
  intro g hg
  have hgm : Measurable fun p : Mt k r × Mt k r => g (Jac.mm p.1 p.2) := hg.comp Jac.measurable_mt_mul
  rw [Jac.lintegral_muS μW μN hg, lintegral_map hg emb.measurable]
  have hmul : Measurable fun p : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε => p.1 * p.2 := measurable_mul
  have hgΨ : Measurable fun a : Formalism.REAL.UJ ε => g (Ψ a) := hg.comp emb.measurable
  rw [show muSL μH μN' = (μN'.prod μH).map (fun p => p.1 * p.2) from rfl,
    lintegral_map hgΨ hmul,
    lintegral_prod (fun p : Formalism.REAL.UJ ε × Formalism.REAL.UJ ε => g (Ψ (p.1 * p.2))) (hgΨ.comp hmul).aemeasurable]
  have hpm : ∀ n h : Formalism.REAL.UJ ε, Ψ (n * h) = Jac.mm (Ψ n) (Ψ h) := psi_mul hF
  simp only [hpm]
  have step1 : ∀ n : Formalism.REAL.UJ ε, ∫⁻ h, g (Jac.mm (Ψ n) (Ψ h)) ∂μH = ∫⁻ y, g (Jac.mm (Ψ n) y) ∂μW := by
    intro n
    rw [hμW, emb.lintegral_map]
  simp_rw [step1]
  rw [← emb.lintegral_map (μ := μN') (f := fun x => ∫⁻ y, g (Jac.mm x y) ∂μW), hNmap]
  rw [lintegral_lintegral_swap (f := fun x y => g (Jac.mm x y)) hgm.aemeasurable]

  have hconc : ∀ᵐ h ∂μW, Matrix.of h ∈ UWset k r zB := by
    have h0 : μW {x | Matrix.of x ∉ UWset k r zB} = 0 := hW.2.2.1
    exact ae_iff.2 h0
  refine lintegral_congr_ae ?_
  filter_upwards [hconc] with h hh
  have hd : IsUnit (Matrix.of h).det := JL.RI.det_unit_of_UH hh.1
  have hhi : (Matrix.of h)⁻¹ ∈ UWset k r zB := JL.RI.inv_mem_UW hh
  have hc : μN.map (conjM (k := k) (r := r) (Matrix.of h)⁻¹) = μN :=
    Formalism.FourierDecayAlt.P.b2_conjInvRaw_proof k r zB μN hz hT hWB _ hhi
  conv_rhs => rw [← hc]
  have hmh : Measurable fun n : Mt k r => g (Jac.mm h n) := hgm.comp (measurable_const.prodMk measurable_id)
  rw [lintegral_map hmh (Jac.meas_conjM _)]
  refine lintegral_congr fun x => ?_
  congr 1
  show Jac.mm x h = Jac.mm h (conjM (Matrix.of h)⁻¹ x)
  funext i j
  show (Matrix.of x * Matrix.of h) i j = (Matrix.of h * ((Matrix.of h)⁻¹ * Matrix.of x * ((Matrix.of h)⁻¹)⁻¹)) i j
  rw [Matrix.nonsing_inv_nonsing_inv _ hd, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd,
    Matrix.one_mul]

theorem haarW_B (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB) (hT : 0 < Tz k r zB)
    {μH : Measure (Formalism.REAL.UJ ε)} (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH)
    (hfin : μH Set.univ ≠ ⊤) :
    Formalism.FourierDecayAlt.B.IsHaarOn (UWset k r zB) (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) := by
  have emb := embQ hF
  have hW := measW_of hF hH
  obtain ⟨μ0, h0⟩ := Formalism.FourierDecayAlt.P.weyl_haar_exists k r zB hz hT
  have hνfin : ∀ K, (μH.map (cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0))) K < ⊤ := fun K =>
    lt_of_le_of_lt (measure_mono (Set.subset_univ K)) (by rw [emb.map_apply, Set.preimage_univ]; exact hfin.lt_top)
  obtain ⟨c, hc⟩ := Formalism.FourierDecayAlt.P.haar_measure_unique_up_to_scalar k r (UWset k r zB) μ0 _ (Formalism.FourierDecayAlt.P.weyl_subgroup_closed k r zB) h0
    hW.2.2.1 hW.2.2.2 (fun K _ => hνfin K)
  exact ⟨hW.2.2.1, hW.2.2.2, fun a ha => by rw [hc, Measure.map_smul _ (JL.RI.meas_rmul a).aemeasurable, h0.right a ha], fun K _ => hνfin K, hW.2.1⟩

theorem rightX_of (hF : IsFrameJ ε e f wf z0) {zB : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r zB)
    (hT : 0 < Tz k r zB) {μH : Measure (Formalism.REAL.UJ ε)}
    (hH : IsLocHaar (Formalism.L2.SG.Pf.NcReal.HLoc ε e f (Qm e f wf z0 *ᵥ zB)) μH) (hfin : μH Set.univ ≠ ⊤)
    (κ : ℝ) (hκ : 0 < κ) (s : Formalism.REAL.UJ ε) (hs : s ∈ SLoc ε e (Qm e f wf z0 *ᵥ zB)) :
    (muSL μH (ENNReal.ofReal κ • refN ε e f wf z0)).map (fun x => x * s) =
      muSL μH (ENNReal.ofReal κ • refN ε e f wf z0) := by
  have emb := embQ hF
  set Ψ := cM (ε := ε) (Qi ε e f wf z0) (Qm e f wf z0) with hΨ
  set μS := muSL μH (ENNReal.ofReal κ • refN ε e f wf z0) with hμS
  have hN := haarN_of (k := k) (r := r) κ hκ
  have hWB := haarW_B hF hz hT hH hfin
  have hNB : Formalism.FourierDecayAlt.B.IsHaarOn (Nset k r) (Formalism.MainNotions.S.haarLie (Nset k r) (ENNReal.ofReal κ)) :=
    Formalism.MainNotions.BridgeLemma₃.lbHaarUp_proved.2 k r _ hN
  have hQinv : (Qm e f wf z0)⁻¹ = Qi ε e f wf z0 := Matrix.inv_eq_left_inv (Qi_mul_Qm hF)
  have hdet : IsUnit (Qm e f wf z0).det := Matrix.isUnit_det_of_left_inverse (Qi_mul_Qm hF)
  set sM : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ := Qi ε e f wf z0 * uMat s * Qm e f wf z0 with hsM
  have hSs : sM ∈ Sset k r zB := by
    have := (JL.setCorr_holds r k ε e (Qm e f wf z0 *ᵥ zB) zB (Qm e f wf z0) (gramQ hF) hdet
      (fun a => Qm_e (f := f) (wf := wf) (z0 := z0) a) hz rfl hT s).1 hs
    rw [hQinv] at this
    exact this
  have hmeas : Measurable fun x : Formalism.REAL.UJ ε => x * s := measurable_mul_const s
  have hfun : Ψ ∘ (fun x => x * s) = Formalism.FourierDecayAlt.B.rmulF sM ∘ Ψ := by
    funext x
    show (Qi ε e f wf z0 * uMat (x * s) * Qm e f wf z0 : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) =
      (Qi ε e f wf z0 * uMat x * Qm e f wf z0) * (Qi ε e f wf z0 * uMat s * Qm e f wf z0)
    rw [uMat_mul]
    simp only [← Matrix.mul_assoc]
    rw [Matrix.mul_assoc (Qi ε e f wf z0 * uMat x) (Qm e f wf z0) (Qi ε e f wf z0), Qm_mul_Qi hF, Matrix.mul_one]
  have key : (μS.map (fun x => x * s)).map Ψ = μS.map Ψ := by
    rw [Measure.map_map emb.measurable hmeas, hfun,
      ← Measure.map_map (JL.RI.meas_rmul (k := k) (r := r) _) emb.measurable, hμS, measS_of hF hz hT hH κ hκ]
    exact JL.RI.muS_right hz hT hWB hNB _ hSs
  rw [← emb.comap_map (μS.map (fun x => x * s)), key, emb.comap_map]

end Formalism.L2.SG.Pf.NcReal.JX
end
end
