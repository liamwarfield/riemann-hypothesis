module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MassLandSt
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtAdjoinIff
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsIsomFrame
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsHermSemilocalLocRing
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FiniteRepSetOfOrtho

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
open NumberField Module Filter Topology

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

def IsFixF (K F : Type) [Field K] [StarRing K] [Field F] [Algebra F K] : Prop :=
  ∀ a : K, star a = a ↔ a ∈ Set.range (algebraMap F K)

def extP (K : Type) {F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) :
    Ideal (𝓞 K) :=
  𝔭.map (algebraMap (𝓞 F) (𝓞 K))

def locF {K F W : Type} [Field K] [Field F] [Algebra F K] [AddCommGroup W] [Module (𝓞 K) W]
    (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) W) : Submodule (𝓞 K) W :=
  Formalism.HermitianLatticesTheory.locS (Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}) L

def CongrP {K F : Type} [Field K] [Field F] [Algebra F K] (𝔭 : Ideal (𝓞 F)) (k : ℕ) (a b : K) :
    Prop :=
  ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∃ z ∈ extP K 𝔭 ^ k,
    algebraMap (𝓞 K) K z = algebraMap F K (t : F) * (a - b)

def vF {F : Type} [Field F] (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) : ℕ := sSup {e : ℕ | n ∈ 𝔭 ^ e}

def alphaStd (K : Type) {F : Type} [Field K] [Field F] [NumberField F] [Algebra F K]
    (𝔭 : Ideal (𝓞 F)) (m : ℕ) : ℝ :=
  ∏ j ∈ Finset.Icc 1 m, (1 - etaF K F 𝔭 ^ j * (Ideal.absNorm 𝔭 : ℝ) ^ (-(j : ℤ)))

section Defs

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

def nkCount (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (n : 𝓞 F) : ℕ :=
  Nat.card {x : ↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L) //
    ∃ y : ↥L, Submodule.Quotient.mk y = x ∧
      CongrP 𝔭 k (h (y : V) (y : V)) (algebraMap F K (n : F))}

def akCount (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ) : ℕ :=
  Nat.card {X : Module.End (𝓞 K) (↥L ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) //
    ∀ x y x' y' : ↥L, Submodule.Quotient.mk x' = X (Submodule.Quotient.mk x) →
      Submodule.Quotient.mk y' = X (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))}

def alphaN (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F) : ℝ :=
  limUnder atTop fun k : ℕ =>
    (nkCount h L 𝔭 k n : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * (2 * finrank K V - 1))

def alphaL (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℝ :=
  limUnder atTop fun k : ℕ =>
    (akCount h L 𝔭 k : ℝ) / (Ideal.absNorm 𝔭 : ℝ) ^ (k * finrank K V ^ 2)

def discrIdeal (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : Ideal (𝓞 K) :=
  Ideal.span {z : 𝓞 K | ∃ x : Fin (finrank K V) → V, (∀ i, x i ∈ L) ∧
    algebraMap (𝓞 K) K z = (Matrix.of fun i j => h (x i) (x j)).det}

def vd (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℕ :=
  sSup {e : ℕ | discrIdeal h L ≤ extP K 𝔭 ^ e}

def normD (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) : ℝ :=
  Real.sqrt (Ideal.absNorm (discrIdeal h L) : ℝ)

def lamP (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℝ :=
  alphaStd K 𝔭 (finrank K V) * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h L 𝔭) / alphaL h L 𝔭

def lamG (F : Type) [Field F] [NumberField F] [Algebra F K] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) : ℝ :=
  ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, lamP h L 𝔭.1

def singS (F : Type) [Field F] [NumberField F] [Algebra F K] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) (n : 𝓞 F) : ℝ :=
  ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, alphaN h L 𝔭.1 n /
    (1 - etaF K F 𝔭.1 ^ finrank K V * (Ideal.absNorm 𝔭.1 : ℝ) ^ (-(finrank K V : ℤ)))

def fibLoc {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} (S : VecSplit h h')
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (T : Submodule (𝓞 K) V') : ℕ :=
  Nat.card {Λ : Submodule (𝓞 K) V // locF 𝔭 Λ = Λ ∧
    (∃ g ∈ Formalism.HermitianLatticesTheory.isom h, Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = Λ) ∧ S.x₀ ∈ Λ ∧ S.cut Λ = locF 𝔭 T}

def IsIntegralAt {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    (𝔭 : Ideal (𝓞 F)) (h₀ : W →ₗ⋆[K] W →ₗ[K] K) (T : Submodule (𝓞 K) W) : Prop :=
  ∀ x ∈ T, ∀ y ∈ T, h₀ x y ∈ locF 𝔭 (1 : Submodule (𝓞 K) K)

def IsLocReps {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} (S : VecSplit h h')
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (s : Finset (Submodule (𝓞 K) V')) : Prop :=
  (∀ T ∈ s, locF 𝔭 T = T ∧ IsIntegralAt 𝔭 h' T ∧ fibLoc S L 𝔭 T ≠ 0) ∧
  ∀ T : Submodule (𝓞 K) V', locF 𝔭 T = T → IsIntegralAt 𝔭 h' T → fibLoc S L 𝔭 T ≠ 0 →
    ∃! T₀, T₀ ∈ s ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g T₀ = T

def psiP {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K} (S : VecSplit h h')
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) : ℝ := by
  classical
  exact if hs : ∃ s, IsLocReps S L 𝔭 s then
    ∑ T ∈ hs.choose, (fibLoc S L 𝔭 T : ℝ) * lamP h' T 𝔭 else 0

def orbCount (h : V →ₗ⋆[K] V →ₗ[K] K) (A B : Submodule (𝓞 K) V) : ℕ :=
  Nat.card {C : Submodule (𝓞 K) V // ∃ g ∈ Formalism.HermitianLatticesTheory.isom h,
    Formalism.HermitianLatticesTheory.gmap g A = A ∧ Formalism.HermitianLatticesTheory.gmap g B = C}

def ballCount (h : V →ₗ⋆[K] V →ₗ[K] K) (Λ : Submodule (𝓞 K) V) (T : ℝ) : ℕ :=
  Nat.card {x : V // x ∈ Λ ∧ ∀ φ : K →+* ℂ, (φ (h x x)).re ≤ T}

end Defs

def boxSet (K F : Type) [Field K] [Field F] [Algebra F K] (T : ℝ) : Set (𝓞 F) :=
  {n | ∀ φ : K →+* ℂ, 0 < (φ (algebraMap F K (n : F))).re ∧ (φ (algebraMap F K (n : F))).re ≤ T}

def MassConst (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
    [Algebra F K] (m : ℕ) (c : ℝ) : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule (𝓞 K) V),
    h.IsSymm → IsTotPosDef h → finrank K V = m → Submodule.IsFullLattice K L →
    Formalism.HermitianLatticesTheory.IsIntegralLat h L → Formalism.HermitianLatticesTheory.mass h L = c * lamG F h L

def LIStat : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
    ∀ (V V' : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
      [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V'] (h : V →ₗ⋆[K] V →ₗ[K] K)
      (h' : V' →ₗ⋆[K] V' →ₗ[K] K) (S : VecSplit h h') (L : Submodule (𝓞 K) V)
      (𝔭 : Ideal (𝓞 F)) (n : 𝓞 F),
      h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → n ≠ 0 → h S.x₀ S.x₀ = algebraMap F K (n : F) →
      Submodule.IsFullLattice K L → Formalism.HermitianLatticesTheory.IsIntegralLat h L →
      psiP S L 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * (vF 𝔭 n + vd h L 𝔭)) *
        alphaStd K 𝔭 (finrank K V - 1) * alphaN h L 𝔭 n / alphaL h L 𝔭

def LocalDensityRatio : Prop :=
  ∀ (K F : Type) [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K],
    Formalism.HermitianLatticesTheory.IsCMUnram K → IsFixF K F →
    ∀ (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
      [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (A₀ B₀ : Submodule (𝓞 K) V)
      (𝔭 : Ideal (𝓞 F)),
      h.IsSymm → IsTotPosDef h → 𝔭.IsMaximal → Submodule.IsFullLattice K A₀ →
      Submodule.IsFullLattice K B₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h A₀ → Formalism.HermitianLatticesTheory.IsIntegralLat h B₀ →
      alphaL h (locF 𝔭 A₀) 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 B₀) 𝔭) *
          orbCount h (locF 𝔭 B₀) (locF 𝔭 A₀) =
        alphaL h (locF 𝔭 B₀) 𝔭 * (Ideal.absNorm 𝔭 : ℝ) ^ (finrank K V * vd h (locF 𝔭 A₀) 𝔭) *
          orbCount h (locF 𝔭 A₀) (locF 𝔭 B₀)

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.GmapLocEqOfFrame
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.WA

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem smul_mem_loc {L : Submodule (𝓞 K) V} {p : Ideal (𝓞 K)} (hp : p.IsPrime) {a : K}
    (ha : a ∈ Formalism.HermitianLatticesTheory.locR (K := K) p) {m : V} (hm : m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L) :
    a • m ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L := by
  obtain ⟨r, s, hs, rfl⟩ := (mem_locR_iff hp a).mp ha
  obtain ⟨t, ht, htm⟩ := Formalism.HermitianLatticesTheory.locBasic_mem_locS.mp hm
  refine Formalism.HermitianLatticesTheory.locBasic_mem_locS.mpr ⟨s * t, mul_mem hs ht, ?_⟩
  have hs0 := algebraMap_ne_zero_of_mem_hcompl hp hs
  have : (s * t) • ((algebraMap (𝓞 K) K r / algebraMap (𝓞 K) K s) • m) = r • (t • m) := by
    rw [← algebraMap_smul K (s * t), ← algebraMap_smul K r, ← algebraMap_smul K t, smul_smul,
      smul_smul, map_mul]
    congr 1
    field_simp
  rw [this]
  exact L.smul_mem r htm

theorem isSelfDualMod_loc {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) {p : Ideal (𝓞 K)} (hp : p.IsPrime)
    (hu : Formalism.HermitianLatticesTheory.IsUnimodularAt h p L) :
    IsSelfDualMod (locRing p) h (Formalism.HermitianLatticesTheory.loc (K := K) p L).toAddSubgroup := by
  have hu' : ∀ x, x ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L ↔
      ∀ y ∈ Formalism.HermitianLatticesTheory.loc (K := K) p L, h y x ∈ Formalism.HermitianLatticesTheory.locR (K := K) p := by
    intro x
    rw [← Formalism.HermitianLatticesTheory.locDual_mem_dualAt]
    unfold Formalism.HermitianLatticesTheory.IsUnimodularAt at hu
    rw [hu]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha m hm
    exact smul_mem_loc hp ha hm
  · intro x hx y hy
    exact (hu' y).mp hy x hx
  · intro x hx
    exact (hu' x).mpr hx
  · intro x
    obtain ⟨n, hn, hnx⟩ := Formalism.HermitianLatticesTheory.traceReal_mult L hL x
    refine ⟨(n : K), by exact_mod_cast hn, ?_⟩
    rw [Int.cast_smul_eq_zsmul]
    exact Formalism.HermitianLatticesTheory.locBasic_le_locS _ L hnx

end Formalism.HermitianLattices.Ext.L3.WA
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsRepsOfCover
open Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace OrbSum

variable {G X Y : Type*} [Group G] [MulAction G X] [MulAction G Y]

theorem exists_reps_of_cover (A : Set X) (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (C : Set X)
    (hC : C.Finite) (hCA : ∀ c ∈ C, c ∈ A) (hcov : ∀ x ∈ A, ∃ c ∈ C, ∃ g : G, g • c = x) :
    ∃ T : Finset X, (∀ t ∈ T, t ∈ A) ∧ ∀ x ∈ A, ∃! t, t ∈ T ∧ ∃ g : G, g • t = x := by
  classical
  let rep : X → X := fun x => (Quotient.mk (MulAction.orbitRel G X) x).out
  have hrep : ∀ x, ∃ g : G, g • x = rep x := fun x => by
    have h1 : Quotient.mk (MulAction.orbitRel G X) (rep x) = Quotient.mk _ x := Quotient.out_eq _
    have h2 : rep x ∈ MulAction.orbit G x := Quotient.exact h1
    exact MulAction.mem_orbit_iff.1 h2
  have hrepA : ∀ x ∈ A, rep x ∈ A := fun x hx => by
    obtain ⟨g, hg⟩ := hrep x
    rw [← hg]
    exact hA g x hx
  have hrep_eq : ∀ x y : X, ∀ g : G, g • y = x → rep y = rep x := fun x y g hg => by
    show (Quotient.mk (MulAction.orbitRel G X) y).out = (Quotient.mk (MulAction.orbitRel G X) x).out
    congr 1
    apply Quotient.sound
    show y ∈ MulAction.orbit G x
    rw [MulAction.mem_orbit_iff]
    exact ⟨g⁻¹, by rw [← hg, inv_smul_smul]⟩
  refine ⟨hC.toFinset.image rep, ?_, ?_⟩
  · intro t ht
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 ht
    exact hrepA c (hCA c (hC.mem_toFinset.1 hc))
  · intro x hx
    obtain ⟨c, hc, g, hg⟩ := hcov x hx
    obtain ⟨g', hg'⟩ := hrep c
    refine ⟨rep c, ⟨Finset.mem_image.2 ⟨c, hC.mem_toFinset.2 hc, rfl⟩, ⟨g * g'⁻¹, ?_⟩⟩, ?_⟩
    · rw [← hg', mul_smul, inv_smul_smul, hg]
    · rintro t ⟨ht, h, hh⟩
      obtain ⟨c', hc', rfl⟩ := Finset.mem_image.1 ht
      obtain ⟨g'', hg''⟩ := hrep c'
      have e1 : rep c' = rep x := (hrep_eq (rep c') c' g'' hg'').trans (hrep_eq x (rep c') h hh)
      have e2 : rep c = rep x := hrep_eq x c g hg
      rw [e1, e2]

theorem card_stab_smul (g : G) (x : X) :
    Nat.card (MulAction.stabilizer G (g • x)) = Nat.card (MulAction.stabilizer G x) := by
  rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj]
  exact Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem card_stab_sub (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (x : X) :
    Nat.card (MulAction.stabilizer (MulAction.stabilizer G (π x)) x) =
      Nat.card (MulAction.stabilizer G x) := Nat.card_congr
  { toFun := fun h => ⟨h.1.1, h.2⟩
    invFun := fun g => ⟨⟨g.1, by
      show g.1 • π x = π x
      rw [← hπ]
      exact congrArg π g.2⟩, g.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem sum_orbits_on (π : X → Y) (hπ : ∀ (g : G) x, π (g • x) = g • π x) (A : Set X) (B : Set Y)
    (hA : ∀ g : G, ∀ x ∈ A, g • x ∈ A) (hAB : ∀ x ∈ A, π x ∈ B)
    (sX : Finset X) (sY : Finset Y) (hsX : ∀ t ∈ sX, t ∈ A) (hsY : ∀ u ∈ sY, u ∈ B)
    (hX : ∀ x ∈ A, ∃! t : X, t ∈ sX ∧ ∃ g : G, g • t = x)
    (hY : ∀ y ∈ B, ∃! t : Y, t ∈ sY ∧ ∃ g : G, g • t = y)
    (hfinY : ∀ y ∈ B, (MulAction.stabilizer G y : Set G).Finite) :
    ∑ t ∈ sX, ((Nat.card (MulAction.stabilizer G t) : ℕ) : ℝ)⁻¹ =
      ∑ u ∈ sY, (Nat.card {x // x ∈ A ∧ π x = u} : ℝ) /
        (Nat.card (MulAction.stabilizer G u) : ℝ) := by
  classical
  have key : ∀ t : X, ∃ (u : Y) (g : G), t ∈ A → (u ∈ sY ∧ g • u = π t) := by
    intro t
    by_cases ht : t ∈ A
    · obtain ⟨u, ⟨hu, g, hg⟩, -⟩ := hY (π t) (hAB t ht)
      exact ⟨u, g, fun _ => ⟨hu, hg⟩⟩
    · exact ⟨π t, 1, fun h => absurd h ht⟩
  choose U γ hU using key
  have hπ' : ∀ t ∈ A, π ((γ t)⁻¹ • t) = U t := by
    intro t ht
    rw [hπ, ← (hU t ht).2, inv_smul_smul]
  rw [← Finset.sum_fiberwise_of_maps_to (s := sX) (t := sY) (g := U)
    (fun t ht => (hU t (hsX t ht)).1)]
  refine Finset.sum_congr rfl fun u hu => ?_
  set T : Finset X := (sX.filter (fun t => U t = u)).image (fun t => (γ t)⁻¹ • t) with hTdef
  have hinj : Set.InjOn (fun t => (γ t)⁻¹ • t) (sX.filter (fun t => U t = u) : Set X) := by
    intro t₁ h₁ t₂ h₂ e
    have h₁' := (Finset.mem_filter.mp h₁).1
    have h₂' := (Finset.mem_filter.mp h₂).1
    exact (hX _ (hA (γ t₁)⁻¹ t₁ (hsX t₁ h₁'))).unique ⟨h₁', _, rfl⟩ ⟨h₂', _, e.symm⟩
  have hstab : ∀ g : MulAction.stabilizer G u, ∀ x ∈ {x : X | x ∈ A ∧ π x = u},
      g • x ∈ {x : X | x ∈ A ∧ π x = u} := by
    rintro ⟨g, hg⟩ x ⟨hx1, hx2⟩
    refine ⟨hA g x hx1, ?_⟩
    change π (g • x) = u
    rw [hπ, hx2]
    exact MulAction.mem_stabilizer_iff.mp hg
  have hTA : ∀ t ∈ T, t ∈ {x : X | x ∈ A ∧ π x = u} := by
    intro t ht
    obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨h₁, rfl⟩ := Finset.mem_filter.mp h₀
    exact ⟨hA _ _ (hsX t₀ h₁), hπ' t₀ (hsX t₀ h₁)⟩
  have hT : ∀ x ∈ {x : X | x ∈ A ∧ π x = u},
      ∃! t, t ∈ T ∧ ∃ g : MulAction.stabilizer G u, g • t = x := by
    rintro x ⟨hx1, hx2⟩
    obtain ⟨t, ⟨ht, g, hg⟩, huniq⟩ := hX x hx1
    have htA := hsX t ht
    have e1 : (g * γ t) • U t = u := by
      rw [mul_smul, (hU t htA).2, ← hπ, hg, hx2]
    have hUt : U t = u :=
      (hY u (hsY u hu)).unique ⟨(hU t htA).1, _, e1⟩ ⟨hu, 1, one_smul _ _⟩
    refine ⟨(γ t)⁻¹ • t, ⟨Finset.mem_image.mpr ⟨t, Finset.mem_filter.mpr ⟨ht, hUt⟩, rfl⟩,
      ⟨g * γ t, MulAction.mem_stabilizer_iff.mpr (by rw [← hUt] at e1 ⊢; exact e1)⟩, ?_⟩, ?_⟩
    · change (g * γ t) • (γ t)⁻¹ • t = x
      rw [mul_smul, smul_inv_smul, hg]
    · rintro t' ⟨ht', ⟨g', hg'm⟩, hg'⟩
      obtain ⟨t₀, h₀, rfl⟩ := Finset.mem_image.mp ht'
      have h₀' := (Finset.mem_filter.mp h₀).1
      have : t₀ = t := huniq t₀ ⟨h₀', g' * (γ t₀)⁻¹, by rw [mul_smul]; exact hg'⟩
      rw [this]
  have hfinG : Finite (MulAction.stabilizer G u) := (hfinY u (hsY u hu)).to_subtype
  have hfinA : Finite ↥{x : X | x ∈ A ∧ π x = u} := by
    apply Set.Finite.to_subtype
    refine ((T : Set X).toFinite.biUnion
      (fun t _ => Set.finite_range (fun g : MulAction.stabilizer G u => g • t))).subset ?_
    intro x hx
    obtain ⟨t, ⟨ht, g, hg⟩, -⟩ := hT x hx
    exact Set.mem_biUnion (Finset.mem_coe.mpr ht) ⟨g, hg⟩
  have main := sum_inv_card_stab (G := MulAction.stabilizer G u) {x : X | x ∈ A ∧ π x = u}
    hstab T hTA hT
  have e0 : (Nat.card {x // x ∈ A ∧ π x = u} : ℝ) =
      (Nat.card ↥{x : X | x ∈ A ∧ π x = u} : ℝ) := rfl
  rw [e0, main, hTdef, Finset.sum_image hinj]
  refine Finset.sum_congr rfl fun t ht => ?_
  obtain ⟨ht1, rfl⟩ := Finset.mem_filter.mp ht
  have := card_stab_sub π hπ ((γ t)⁻¹ • t)
  rw [hπ' t (hsX t ht1)] at this
  rw [this, card_stab_smul]

end OrbSum

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExtOfSymmApply
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

namespace SplitBAux

variable {K V V' : Type} [Field K] [NumberField K] [StarRing K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem exists_of_orth (S : VecSplit h h') {v : V} (hv : h S.x₀ v = 0) : ∃ a, S.ι a = v := by
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [S.h_x₀_comb] at hv
  have hc : c = 0 := (mul_eq_zero.mp hv).resolve_right S.hx₀
  exact ⟨a, by rw [hc, zero_smul, zero_add]⟩

theorem h_decomp (hs : h.IsSymm) (S : VecSplit h h') (c d : K) (a b : V') :
    h (c • S.x₀ + S.ι a) (d • S.x₀ + S.ι b) = star c * d * h S.x₀ S.x₀ + h' a b := by
  simp [S.orth, S.orth' hs, S.isom, mul_assoc, starRingEnd_apply]

def liftι {W : Type} [AddCommGroup W] [Module K W] (S : VecSplit h h') (f : W →ₗ[K] V)
    (hf : ∀ w, ∃ b, S.ι b = f w) : W →ₗ[K] V' where
  toFun a := (hf a).choose
  map_add' a b := S.inj (by
    rw [map_add S.ι, (hf a).choose_spec, (hf b).choose_spec, (hf (a + b)).choose_spec, map_add f])
  map_smul' c a := S.inj (by
    simp only [RingHom.id_apply]
    rw [map_smul S.ι, (hf a).choose_spec, (hf (c • a)).choose_spec, map_smul f])

theorem liftι_spec {W : Type} [AddCommGroup W] [Module K W] (S : VecSplit h h') (f : W →ₗ[K] V)
    (hf : ∀ w, ∃ b, S.ι b = f w) (w : W) : S.ι (liftι S f hf w) = f w := (hf w).choose_spec

def projX (S : VecSplit h h') : V →ₗ[K] V :=
  ((h S.x₀ S.x₀)⁻¹ • h S.x₀).smulRight S.x₀

theorem projX_apply (S : VecSplit h h') (c : K) (a : V') :
    projX S (c • S.x₀ + S.ι a) = c • S.x₀ := by
  unfold projX
  rw [LinearMap.smulRight_apply, LinearMap.smul_apply, S.h_x₀_comb, smul_eq_mul]
  congr 1
  rw [inv_mul_eq_iff_eq_mul₀ S.hx₀]
  exact mul_comm _ _

def coordA (S : VecSplit h h') : V →ₗ[K] V' :=
  liftι S (LinearMap.id - projX S) (by
    intro v; obtain ⟨c, b, rfl⟩ := S.cover v
    exact ⟨b, by simp [projX_apply]⟩)

theorem coordA_apply (S : VecSplit h h') (c : K) (a : V') : coordA S (c • S.x₀ + S.ι a) = a := by
  apply S.inj
  unfold coordA
  rw [liftι_spec, LinearMap.sub_apply, LinearMap.id_apply, projX_apply, add_sub_cancel_left]

theorem linearMap_ext (S : VecSplit h h') {f g : V →ₗ[K] V} (h0 : f S.x₀ = g S.x₀)
    (h1 : ∀ a, f (S.ι a) = g (S.ι a)) : f = g := by
  ext v
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [map_add (f := _), map_add (f := _), map_smul, map_smul, h0, h1]

theorem isom_apply {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (x y : V) : h (g x) (g y) = h x y := hg x y

theorem symm_mem_isom {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) : g.symm ∈ Formalism.HermitianLatticesTheory.isom h := by
  exact inv_mem hg

theorem mem_gmap_iff {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (e : W ≃ₗ[K] W) (M : Submodule (𝓞 K) W) (v : W) :
    v ∈ Formalism.HermitianLatticesTheory.gmap e M ↔ e.symm v ∈ M := by
  unfold Formalism.HermitianLatticesTheory.gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro hv
    exact ⟨e.symm v, hv, by simp⟩

theorem mem_adjoin_iff (S : VecSplit h h') (L' : Submodule (𝓞 K) V') (c : K) (a : V') :
    c • S.x₀ + S.ι a ∈ S.adjoin L' ↔ (∃ r : 𝓞 K, algebraMap (𝓞 K) K r = c) ∧ a ∈ L' := by
  rw [S.comb_mem_adjoin_iff, Submodule.mem_one]

theorem maps_of_fix (S : VecSplit h h') {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) (a : V') : ∃ b, S.ι b = (g.toLinearMap ∘ₗ S.ι) a := by
  apply exists_of_orth S
  show h S.x₀ (g (S.ι a)) = 0
  rw [← hx, isom_apply hg, S.orth]

theorem symm_fix {g : V ≃ₗ[K] V} {x : V} (hx : g x = x) : g.symm x = x := by
  exact g.symm_apply_eq.mpr hx.symm

def res (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) (hx : g S.x₀ = S.x₀) :
    V' ≃ₗ[K] V' :=
  LinearEquiv.ofLinearMap (liftι S _ (maps_of_fix S hg hx))
    (liftι S _ (maps_of_fix S (symm_mem_isom hg) (symm_fix hx)))
    (by ext a; apply S.inj; simp [liftι_spec])
    (by ext a; apply S.inj; simp [liftι_spec])

theorem res_spec (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) (a : V') : S.ι (res S g hg hx a) = g (S.ι a) := by
  exact liftι_spec S _ _ a

theorem res_symm_spec (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) (a : V') : S.ι ((res S g hg hx).symm a) = g.symm (S.ι a) := by
  exact liftι_spec S _ _ a

theorem res_mem_isom (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) : res S g hg hx ∈ Formalism.HermitianLatticesTheory.isom h' := by
  show ∀ x y, h' (res S g hg hx x) (res S g hg hx y) = h' x y
  intro x y
  rw [← S.isom, res_spec, res_spec, isom_apply hg, S.isom]

theorem gmap_res (S : VecSplit h h') (g : V ≃ₗ[K] V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx : g S.x₀ = S.x₀) {L₁ L₂ : Submodule (𝓞 K) V} (hL : Formalism.HermitianLatticesTheory.gmap g L₁ = L₂) :
    Formalism.HermitianLatticesTheory.gmap (res S g hg hx) (S.cut L₁) = S.cut L₂ := by
  ext a
  rw [mem_gmap_iff, S.mem_cut_iff, S.mem_cut_iff, res_symm_spec, ← hL, mem_gmap_iff]

def extFun (S : VecSplit h h') (f : V' →ₗ[K] V') : V →ₗ[K] V :=
  projX S + S.ι ∘ₗ f ∘ₗ coordA S

theorem extFun_apply (S : VecSplit h h') (f : V' →ₗ[K] V') (c : K) (a : V') :
    extFun S f (c • S.x₀ + S.ι a) = c • S.x₀ + S.ι (f a) := by
  unfold extFun
  rw [LinearMap.add_apply, projX_apply, LinearMap.comp_apply, LinearMap.comp_apply, coordA_apply]

theorem eq_decomp_x₀ (S : VecSplit h h') : S.x₀ = (1 : K) • S.x₀ + S.ι 0 := by
  simp

theorem eq_decomp_ι (S : VecSplit h h') (a : V') : S.ι a = (0 : K) • S.x₀ + S.ι a := by
  simp

def extOf (S : VecSplit h h') (g' : V' ≃ₗ[K] V') : V ≃ₗ[K] V :=
  LinearEquiv.ofLinearMap (extFun S g'.toLinearMap) (extFun S g'.symm.toLinearMap)
    (linearMap_ext S (by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
      rw [eq_decomp_x₀ S, extFun_apply, extFun_apply]; simp)
      (fun a => by
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
        rw [eq_decomp_ι S, extFun_apply, extFun_apply]; simp))
    (linearMap_ext S (by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
      rw [eq_decomp_x₀ S, extFun_apply, extFun_apply]; simp)
      (fun a => by
        simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq]
        rw [eq_decomp_ι S, extFun_apply, extFun_apply]; simp))

theorem extOf_apply (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (c : K) (a : V') :
    extOf S g' (c • S.x₀ + S.ι a) = c • S.x₀ + S.ι (g' a) := extFun_apply S g'.toLinearMap c a

theorem extOf_symm_apply (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (c : K) (a : V') :
    (extOf S g').symm (c • S.x₀ + S.ι a) = c • S.x₀ + S.ι (g'.symm a) := extFun_apply S g'.symm.toLinearMap c a

theorem extOf_x₀ (S : VecSplit h h') (g' : V' ≃ₗ[K] V') : extOf S g' S.x₀ = S.x₀ := by
  rw [eq_decomp_x₀ S, extOf_apply]
  simp

theorem extOf_ι (S : VecSplit h h') (g' : V' ≃ₗ[K] V') (a : V') :
    extOf S g' (S.ι a) = S.ι (g' a) := by
  rw [eq_decomp_ι S a, extOf_apply]
  simp

theorem extOf_mem_isom (hs : h.IsSymm) (S : VecSplit h h') {g' : V' ≃ₗ[K] V'}
    (hg : g' ∈ Formalism.HermitianLatticesTheory.isom h') : extOf S g' ∈ Formalism.HermitianLatticesTheory.isom h := by
  have hg' : ∀ x y, h' (g' x) (g' y) = h' x y := hg
  show ∀ x y, h (extOf S g' x) (extOf S g' y) = h x y
  intro x y
  obtain ⟨c, a, rfl⟩ := S.cover x
  obtain ⟨d, b, rfl⟩ := S.cover y
  rw [extOf_apply, extOf_apply, h_decomp hs, h_decomp hs, hg']

theorem gmap_extOf (S : VecSplit h h') (g' : V' ≃ₗ[K] V') {C₁ C₂ : Submodule (𝓞 K) V'}
    (hC : Formalism.HermitianLatticesTheory.gmap g' C₁ = C₂) :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') (S.adjoin C₁) = S.adjoin C₂ := by
  ext v
  obtain ⟨c, a, rfl⟩ := S.cover v
  rw [mem_gmap_iff, extOf_symm_apply, SplitBAux.mem_adjoin_iff, SplitBAux.mem_adjoin_iff, ← hC,
    mem_gmap_iff]

end SplitBAux

end Formalism.HermitianLattices.Ext.L3
end
end
