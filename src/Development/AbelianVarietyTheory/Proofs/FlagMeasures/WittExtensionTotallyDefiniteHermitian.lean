module

public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CommonStabilizerStabilizersCommensurableVolume
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFlagDualBasis
public import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitian
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitian
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.Witt

variable {K V : Type} [Field K] [StarRing K] [AddCommGroup V] [Module K V]

theorem mem_perp (h : V →ₗ⋆[K] V →ₗ[K] K) (U : Submodule K V) (v : V) :
    v ∈ perp h U ↔ ∀ x ∈ U, h x v = 0 := by
  simp [perp, Submodule.mem_iInf, LinearMap.mem_ker]

private lemma h_sub_smul_sub_smul_eq_of_hww (h : V →ₗ⋆[K] V →ₗ[K] K) (hsym : ∀ a b, star (h a b) = h b a)
    (w : V) (α : K) (hα : α ≠ 0) (hww : h w w = α + star α) (a b : V) :
    h (a - (α⁻¹ * h w a) • w) (b - (α⁻¹ * h w b) • w) = h a b := by
  have hα' : star α ≠ 0 := star_ne_zero.mpr hα
  simp only [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul,
    starRingEnd_apply]
  rw [← hsym w a, hww, star_mul, star_inv₀]
  field_simp
  ring

theorem exists_isom_move [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) (x y : V) (hxy : h x x = h y y) :
    ∃ g ∈ isom h, g x = y ∧ ∀ v, h (x - y) v = 0 → g v = v := by
  have hsym : ∀ a b, star (h a b) = h b a := fun a b => by
    rw [← starRingEnd_apply]; exact hs.eq a b
  have hww : h (x - y) (x - y) = h (x - y) x + star (h (x - y) x) := by
    rw [hsym]
    simp only [map_sub, LinearMap.sub_apply]
    rw [hxy]; ring
  by_cases hα : h (x - y) x = 0
  · have h0 : h (x - y) (x - y) = 0 := by rw [hww, hα, star_zero, add_zero]
    have hxy' : x = y := sub_eq_zero.mp (ha _ h0)
    exact ⟨1, (isom h).one_mem, by simp [hxy'], fun v _ => rfl⟩
  · let f : V →ₗ[K] V :=
      LinearMap.id - LinearMap.smulRight ((h (x - y) x)⁻¹ • h (x - y)) (x - y)
    have hf : ∀ v, f v = v - ((h (x - y) x)⁻¹ * h (x - y) v) • (x - y) := fun v => rfl
    have key : ∀ a b, h (f a) (f b) = h a b := fun a b => by
      rw [hf, hf]; exact h_sub_smul_sub_smul_eq_of_hww h hsym (x - y) _ hα hww a b
    have hinj : Function.Injective f := by
      set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
      intro a ha0
      apply ha a
      rw [← key a a, ha0, map_zero]
    let g : V ≃ₗ[K] V := LinearEquiv.ofInjectiveEndo f hinj
    have hg : ∀ v, g v = f v := fun v => rfl
    refine ⟨g, fun a b => by rw [hg, hg, key], ?_, fun v hv => ?_⟩
    · rw [hg, hf, inv_mul_cancel₀ hα, one_smul, sub_sub_cancel]
    · rw [hg, hf, hv, mul_zero, zero_smul, sub_zero]

theorem exists_isom_finset [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) {ι : Type} (a b : ι → V)
    (hab : ∀ i j, h (b i) (b j) = h (a i) (a j)) (t : Finset ι) :
    ∃ g ∈ isom h, ∀ i ∈ t, g (a i) = b i := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨1, (isom h).one_mem, by simp⟩
  | insert j s hj ih =>
    obtain ⟨g, hg, hgs⟩ := ih
    have hg' : ∀ u v, h (g u) (g v) = h u v := hg
    have hgx : h (g (a j)) (g (a j)) = h (b j) (b j) := by rw [hg', hab]
    obtain ⟨k, hk, hkx, hkfix⟩ := exists_isom_move h hs ha (g (a j)) (b j) hgx
    refine ⟨k * g, (isom h).mul_mem hk hg, fun i hi => ?_⟩
    show k (g (a i)) = b i
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hkx
    · rw [hgs i hi]
      apply hkfix
      have e1 : h (g (a j)) (b i) = h (b j) (b i) :=
        calc h (g (a j)) (b i) = h (g (a j)) (g (a i)) := by rw [hgs i hi]
          _ = h (a j) (a i) := hg' _ _
          _ = h (b j) (b i) := (hab j i).symm
      rw [map_sub, LinearMap.sub_apply, e1, sub_self]

theorem isCompl_perp [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (ha : ∀ x, h x x = 0 → x = 0) (U : Submodule K V) : IsCompl U (perp h U) := by
  have hdis : Disjoint U (perp h U) := by
    rw [Submodule.disjoint_def]
    intro x hxU hxP
    exact ha x (((mem_perp h U x).1 hxP) x hxU)
  let bU := Module.finBasis K U
  let T : V →ₗ[K] (Fin (Module.finrank K U) → K) := LinearMap.pi fun i => h (bU i : V)
  have hker : LinearMap.ker T ≤ perp h U := by
    intro v hv
    rw [mem_perp]
    intro x hx
    have hv' : ∀ i, h (bU i : V) v = 0 := fun i => by
      have := congrFun (LinearMap.mem_ker.mp hv) i
      simpa [T] using this
    have hx' : x = ∑ i, (bU.repr ⟨x, hx⟩ i) • (bU i : V) := by
      have e := congrArg Subtype.val (bU.sum_repr ⟨x, hx⟩)
      simp only [Submodule.coe_sum, Submodule.coe_smul] at e
      exact e.symm
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hx', map_sum, LinearMap.sum_apply]
    simp [hv']
  have h1 := LinearMap.finrank_range_add_finrank_ker T
  have h2 : Module.finrank K (LinearMap.range T) ≤ Module.finrank K U := by
    simpa using Submodule.finrank_le (LinearMap.range T)
  have h3 := Submodule.finrank_mono hker
  have h4 := Submodule.finrank_sup_add_finrank_inf_eq U (perp h U)
  rw [hdis.eq_bot, finrank_bot] at h4
  refine ⟨hdis, ?_⟩
  rw [codisjoint_iff]
  apply Submodule.eq_top_of_finrank_eq
  have h5 := Submodule.finrank_le (U ⊔ perp h U)
  omega

theorem perp_perp [FiniteDimensional K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hs : h.IsSymm)
    (ha : ∀ x, h x x = 0 → x = 0) (U : Submodule K V) : perp h (perp h U) = U := by
  have hle : U ≤ perp h (perp h U) := by
    intro u hu
    rw [mem_perp]
    intro w hw
    have h0 : h u w = 0 := (mem_perp h U w).1 hw u hu
    rw [← hs.eq u w, h0, map_zero]
  have c1 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp h ha U)
  have c2 := Submodule.finrank_add_eq_of_isCompl (isCompl_perp h ha (perp h U))
  exact (Submodule.eq_of_le_of_finrank_eq hle (by omega)).symm

theorem witt_definite : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ U U' : Submodule K V, ∀ e : U ≃ₗ[K] U', (∀ x y, h (e x : V) (e y : V) = h (x : V) (y : V)) → ∃ g ∈ isom h, ∀ x : U, g (x : V) = (e x : V)) ∧ ∀ U : Submodule K V, IsCompl U (perp h U) ∧ (hRes h U).IsSymm ∧ PD (hRes h U) ∧ perp h (perp h U) = U := by
  intro K V _ _ _ _ _ _ _ _ h _ hs hpd
  have ha : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    obtain ⟨τ⟩ : Nonempty (K →+* ℂ) := inferInstance
    have := hpd τ x hne
    rw [hx, map_zero, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨?_, fun U => ⟨isCompl_perp h ha U, ?_, ?_, perp_perp h hs ha U⟩⟩
  · intro U U' e he
    let bU := Module.finBasis K U
    obtain ⟨g, hg, hgb⟩ := exists_isom_finset h hs ha (fun i => (bU i : V))
      (fun i => (e (bU i) : V)) (fun i j => he _ _) Finset.univ
    refine ⟨g, hg, fun x => ?_⟩
    have hcomp : (g : V →ₗ[K] V).comp U.subtype = U'.subtype.comp (e : U →ₗ[K] U') := by
      apply bU.ext
      intro i
      simpa using hgb i (Finset.mem_univ i)
    exact LinearMap.congr_fun hcomp x
  · exact ⟨fun x y => hs.eq x y⟩
  · intro τ x hx
    show 0 < (τ (h x x)).re
    exact hpd τ x (fun h0 => hx (Subtype.ext h0))

end GlobalTheory.Mass.Witt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionTotallyDefiniteHermitianStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_extension_totally_definite_hermitian : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → PD h → (∀ U U' : Submodule K V, ∀ e : U ≃ₗ[K] U', (∀ x y, h (e x : V) (e y : V) = h (x : V) (y : V)) → ∃ g ∈ isom h, ∀ x : U, g (x : V) = (e x : V)) ∧ ∀ U : Submodule K V, IsCompl U (perp h U) ∧ (hRes h U).IsSymm ∧ PD (hRes h U) ∧ perp h (perp h U) = U := by
  first | exact @GlobalTheory.Mass.Witt.witt_definite | exact GlobalTheory.Mass.Witt.witt_definite | (intros; apply GlobalTheory.Mass.Witt.witt_definite <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumTransportEquivariant
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumTransportEquivariant
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.OrbTransport

open MulAction in
private lemma exists_smul_eq_orbit_out {G α : Type} [Group G] [MulAction G α] (y : α) :
    ∃ g : G, g • y = (Quotient.mk (orbitRel G α) y).out := by
  obtain ⟨g, hg⟩ := Quotient.mk_out (s := orbitRel G α) y
  exact ⟨g, hg⟩

open MulAction in
private lemma card_stabilizer_smul_eq' {G α : Type} [Group G] [MulAction G α] (g : G) (a : α) :
    ENat.card (stabilizer G (g • a)) = ENat.card (stabilizer G a) :=
  (ENat.card_congr (stabilizerEquivStabilizer (g := g) rfl).toEquiv).symm

open MulAction in
theorem _root_.GlobalTheory.Mass.OrbTransport.main : ∀ (G G' α β : Type) [Group G] [Group G'] [MulAction G α] [MulAction G' β] (φ : G ≃* G') (f : α → β) (X : Set α) (Y : Set β) (N : β → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → _root_.GlobalTheory.Mass.Stable G' Y → Set.BijOn f X Y → (∀ (g : G), ∀ x ∈ X, f (g • x) = φ g • f x) → (∀ (g : G') y, N (g • y) = N y) → _root_.GlobalTheory.Mass.orbSum G X (fun x => N (f x)) = _root_.GlobalTheory.Mass.orbSum G' Y N := by
  intro G G' α β _ _ _ _ φ f X Y N hX hY hf hequiv hN
  have hcard : ∀ x ∈ X, ENat.card (stabilizer G' (f x)) = ENat.card (stabilizer G x) := by
    intro x hx
    refine (ENat.card_congr (Equiv.subtypeEquiv φ.toEquiv fun g => ?_)).symm
    simp only [mem_stabilizer_iff, MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv]
    rw [← hequiv g x hx]
    exact ⟨fun h => by rw [h], fun h => hf.injOn (hX g x hx) hx h⟩
  have hout : ∀ q : {q : orbitRel.Quotient G α // q.out ∈ X},
      (Quotient.mk (orbitRel G' β) (f q.1.out)).out ∈ Y := by
    intro q
    obtain ⟨g, hg⟩ := exists_smul_eq_orbit_out (G := G') (f q.1.out)
    rw [← hg]
    exact hY g _ (hf.mapsTo q.2)
  let F : {q : orbitRel.Quotient G α // q.out ∈ X} → {q : orbitRel.Quotient G' β // q.out ∈ Y} :=
    fun q => ⟨Quotient.mk _ (f q.1.out), hout q⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨q₁, h₁⟩ ⟨q₂, h₂⟩ h
      obtain ⟨g', hg'⟩ := Quotient.exact (congrArg Subtype.val h)
      apply Subtype.ext
      show q₁ = q₂
      rw [← Quotient.out_eq q₁, ← Quotient.out_eq q₂]
      apply Quotient.sound
      refine ⟨φ.symm g', ?_⟩
      apply hf.injOn (hX _ _ h₂) h₁
      rw [hequiv _ _ h₂, MulEquiv.apply_symm_apply]
      exact hg'
    · rintro ⟨q', hq'⟩
      obtain ⟨x, hx, hfx⟩ := hf.surjOn hq'
      obtain ⟨g, hg⟩ := exists_smul_eq_orbit_out (G := G) x
      have hmem : (Quotient.mk (orbitRel G α) x).out ∈ X := by rw [← hg]; exact hX g x hx
      refine ⟨⟨Quotient.mk _ x, hmem⟩, Subtype.ext ?_⟩
      show Quotient.mk _ (f (Quotient.mk (orbitRel G α) x).out) = q'
      rw [← Quotient.out_eq q', ← hg, hequiv g x hx, hfx]
      exact Quotient.sound ⟨φ g, rfl⟩
  unfold _root_.GlobalTheory.Mass.orbSum
  rw [← (Equiv.ofBijective F hF).tsum_eq]
  congr 1
  funext q
  obtain ⟨g', hg'⟩ := exists_smul_eq_orbit_out (G := G') (f q.1.out)
  show _ = (ENat.card (stabilizer G' (Quotient.mk (orbitRel G' β) (f q.1.out)).out) : ℝ≥0∞)⁻¹ *
    N (Quotient.mk (orbitRel G' β) (f q.1.out)).out
  rw [← hg', card_stabilizer_smul_eq', hN, hcard _ q.2]

end GlobalTheory.Mass.OrbTransport
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumTransportEquivariantStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.orbitWeightedStabilizerSum_transport_equivariant : ∀ (G G' α β : Type) [Group G] [Group G'] [MulAction G α] [MulAction G' β] (φ : G ≃* G') (f : α → β) (X : Set α) (Y : Set β) (N : β → ℝ≥0∞), Stable G X → Stable G' Y → Set.BijOn f X Y → (∀ (g : G), ∀ x ∈ X, f (g • x) = φ g • f x) → (∀ (g : G') y, N (g • y) = N y) → orbSum G X (fun x => N (f x)) = orbSum G' Y N := by
  first | exact @GlobalTheory.Mass.OrbTransport.main | exact GlobalTheory.Mass.OrbTransport.main | (intros; apply GlobalTheory.Mass.OrbTransport.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticesMoveWithIsometries
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticesMoveWithIsometries
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.PrimMove

section

variable {R K : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]

theorem discN_congr {V W : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
    [AddCommGroup W] [Module K W] [Module R W] [IsScalarTower R K W]
    (h : V →ₗ⋆[K] V →ₗ[K] K) (k : W →ₗ⋆[K] W →ₗ[K] K) (e : V ≃ₗ[K] W)
    (he : ∀ x y, k (e x) (e y) = h x y) (A : Submodule R V) (B : Submodule R W)
    (hAB : ∀ x, e x ∈ B ↔ x ∈ A) : discN k B = discN h A := by
  have hd : ∀ x, e x ∈ dual k B ↔ x ∈ dual h A := by
    intro x
    unfold dual Formalism.E.hdual
    simp only [Submodule.mem_iInf, Submodule.mem_comap, LinearMap.restrictScalars_apply]
    constructor
    · intro H y hy
      rw [← he]
      exact H _ ((hAB y).2 hy)
    · intro H y hy
      obtain ⟨z, rfl⟩ := e.surjective y
      rw [he]
      exact H _ ((hAB z).1 hy)
  have hm : ∀ (A : Submodule R V) (B : Submodule R W), (∀ x, e x ∈ B ↔ x ∈ A) →
      B.toAddSubgroup = A.toAddSubgroup.map (e : V →+ W) := by
    intro A B H
    ext y
    obtain ⟨z, rfl⟩ := e.surjective y
    constructor
    · intro hy
      exact ⟨z, (H z).1 hy, rfl⟩
    · rintro ⟨w, hw, hwz⟩
      have : e w = e z := hwz
      rw [← this]
      exact (H w).2 hw
  unfold discN idxN
  rw [hm A B hAB, hm _ _ hd]
  exact AddSubgroup.relIndex_map_map_of_injective (f := (e : V →+ W)) _ _ e.injective

variable {V : Type*} [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem smul_mem_smul_iff (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule R V) (x : V) :
    (g : V ≃ₗ[K] V) x ∈ g • L ↔ x ∈ L := by
  constructor
  · rintro ⟨w, hw, hwx⟩
    have : w = x := (g : V ≃ₗ[K] V).injective hwx
    exact this ▸ hw
  · intro hx
    exact ⟨x, hx, rfl⟩

theorem smul_mem_primSp (h : V →ₗ⋆[K] V →ₗ[K] K) (g : isom h) (L : Submodule R V)
    (U : Submodule K V) (j n : ℕ) : g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n := by
  let e : U ≃ₗ[K] (g • U : Submodule K V) := (g : V ≃ₗ[K] V).submoduleMap U
  have he : ∀ x : U, (e x : V) = (g : V ≃ₗ[K] V) x := fun _ => rfl
  have h1 : Module.finrank K (g • U : Submodule K V) = Module.finrank K U := e.finrank_eq.symm
  have h2 : discN (hRes h (g • U)) (latIn (g • U) (g • L)) = discN (hRes h U) (latIn U L) := by
    refine discN_congr _ _ e (fun x y => ?_) _ _ (fun x => ?_)
    · exact g.2 (x : V) (y : V)
    · exact smul_mem_smul_iff h g L (x : V)
  change _ ∧ _ ↔ _ ∧ _
  rw [h1, h2]

end

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (g : isom h) (L : Submodule (𝓞 K) V) (U : Submodule K V) (j n : ℕ), (g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n) ∧ (primSp h (g • L) j n).encard = (primSp h L j n).encard := by
  intro K V _ _ _ _ _ _ _ _ h _ _ _ g L U j n
  refine ⟨smul_mem_primSp h g L U j n, ?_⟩
  have hi : primSp h (g • L) j n = (fun W : Submodule K V => g • W) '' primSp h L j n := by
    ext W
    constructor
    · intro hW
      refine ⟨g⁻¹ • W, ?_, smul_inv_smul g W⟩
      rw [← smul_mem_primSp h g, smul_inv_smul]
      exact hW
    · rintro ⟨W', hW', rfl⟩
      exact (smul_mem_primSp h g L W' j n).2 hW'
  rw [hi]
  exact (MulAction.injective g).encard_image _

end GlobalTheory.Mass.PrimMove
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PrimitiveSublatticesMoveWithIsometriesStatement
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.primitive_sublattices_move_with_isometries : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K), IsCMUnram K → h.IsSymm → h.Nondegenerate → ∀ (g : isom h) (L : Submodule (𝓞 K) V) (U : Submodule K V) (j n : ℕ), (g • U ∈ primSp h (g • L) j n ↔ U ∈ primSp h L j n) ∧ (primSp h (g • L) j n).encard = (primSp h L j n).encard := by
  first | exact @GlobalTheory.Mass.PrimMove.main | exact GlobalTheory.Mass.PrimMove.main | (intros; apply GlobalTheory.Mass.PrimMove.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TsumOrbitNormaliser
open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc GlobalTheory.HL
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.InvH

theorem tsum_orbit_normaliser {G X M : Type} [Group G] [MulAction G X] [AddCommMonoid M]
    [TopologicalSpace M] (K : Subgroup G) (h : G) (h1 : ∀ s ∈ K, h * s * h⁻¹ ∈ K)
    (h2 : ∀ s ∈ K, h⁻¹ * s * h ∈ K) (φ ψ : X → M) (hφ : ∀ s ∈ K, ∀ x, φ (s • x) = φ x)
    (hψ : ∀ x, ψ (h • x) = φ x) :
    ∑' o : MulAction.orbitRel.Quotient K X, ψ o.out =
      ∑' o : MulAction.orbitRel.Quotient K X, φ o.out := by
  let e : MulAction.orbitRel.Quotient K X ≃ MulAction.orbitRel.Quotient K X :=
    Quotient.congr (MulAction.toPerm h) (by
      intro a b
      simp only [MulAction.orbitRel_apply, MulAction.mem_orbit_iff, MulAction.toPerm_apply]
      constructor
      · rintro ⟨s, hs⟩
        refine ⟨⟨_, h1 s s.2⟩, ?_⟩
        rw [← hs]
        simp [Subgroup.smul_def, mul_smul]
      · rintro ⟨s, hs⟩
        refine ⟨⟨_, h2 s s.2⟩, ?_⟩
        simp only [Subgroup.smul_def, mul_smul] at hs ⊢
        rw [hs]; simp)
  rw [← e.tsum_eq]
  refine tsum_congr fun o => ?_
  have h3 : e o = Quotient.mk _ (h • o.out) := by
    conv_lhs => rw [← Quotient.out_eq o]
    rfl
  have h4 : (MulAction.orbitRel K X) (e o).out (h • o.out) := by
    rw [h3]; exact Quotient.mk_out (s := MulAction.orbitRel K X) _
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h4
  obtain ⟨s, hs⟩ := h4
  have h5 : (e o).out = h • ((h⁻¹ * s * h) • o.out) := by
    rw [← hs]; simp [Subgroup.smul_def, mul_smul]
  rw [h5, hψ, hφ _ (h2 s s.2)]

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]

theorem conj_unipOn {n : ℕ} {A B : Submodule E (Fin n → E)} {h s : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hA : ∀ v, h v ∈ A ↔ v ∈ A) (hB : ∀ v, h v ∈ B ↔ v ∈ B) (hs : s ∈ unipOn A B) :
    h * s * h⁻¹ ∈ unipOn A B := by
  have hA' : ∀ v, h.symm v ∈ A ↔ v ∈ A := fun v => by rw [← hA]; simp
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · change h (s (h.symm v)) ∈ A ↔ _
    rw [hA, hs.1, hA']
  · have := (hB _).2 (hs.2 _ ((hA' v).2 hv))
    rw [map_sub, LinearEquiv.apply_symm_apply] at this
    exact this

theorem mem_iff_of_fix {n : ℕ} {A : Submodule E (Fin n → E)} {h : (Fin n → E) ≃ₗ[E] (Fin n → E)}
    (hA : ∀ v ∈ A, h v = v) (v : Fin n → E) : h v ∈ A ↔ v ∈ A := by
  constructor
  · intro hv
    have := h.injective (hA _ hv)
    rwa [this] at hv
  · intro hv; rwa [hA v hv]

variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

theorem spanTo_mono (g : Fin (r + 1) → S.V) {i j : ℕ} (hij : i ≤ j) : S.spanTo g i ≤ S.spanTo g j :=
  Submodule.span_mono (Set.image_mono fun _ ha => lt_of_lt_of_le ha hij)

theorem conj_Nof (g : Fin (r + 1) → S.V) {h s : S.GLV} (hi : h ∈ isomG L S.Hm)
    (hg : ∀ v ∈ S.spanTo g (r + 1), h v = v) (hs : s ∈ S.Nof g) : h * s * h⁻¹ ∈ S.Nof g := by
  have hfix : ∀ j ≤ r + 1, ∀ v, h v ∈ S.spanTo g j ↔ v ∈ S.spanTo g j := fun j hj =>
    mem_iff_of_fix fun v hv => hg v (spanTo_mono S g hj hv)
  obtain ⟨⟨s1, s2⟩, s3⟩ := hs
  refine ⟨⟨(isomG L S.Hm).mul_mem ((isomG L S.Hm).mul_mem hi s1) ((isomG L S.Hm).inv_mem hi), ?_⟩, ?_⟩
  · refine Subgroup.mem_iInf.2 fun j => ?_
    exact conj_unipOn (hfix _ (by omega)) (hfix _ (by omega)) (Subgroup.mem_iInf.1 s2 j)
  · refine conj_unipOn (fun v => ?_) (hfix _ (by omega)) s3
    refine forall₂_congr fun y hy => ?_
    have := hi v y
    rw [hg y (spanTo_mono S g (by omega) hy)] at this
    rw [this]

theorem conj_St {h s : S.GLV} (hh : h ∈ S.H0) (hs : s ∈ S.St) : h * s * h⁻¹ ∈ S.St := by
  have hfix : ∀ v ∈ S.ME, h v = v := fun v hv => sub_eq_zero.1 ((Submodule.mem_bot E).1 (hh.2.2 v hv))
  exact ⟨conj_Nof S _ hh.1 (fun v hv => hfix v (Submodule.mem_sup_left hv)) hs.1,
    conj_Nof S _ hh.1 (fun v hv => hfix v (Submodule.mem_sup_right hv)) hs.2⟩

theorem amp_mass_smul : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ h ∈ S.H0, ∀ (d : S.Datum) (Q Q' : Submodule L.O S.V → Prop), (∀ s ∈ S.St, ∀ Λ, S.IsTerm d Λ → Q Λ → Q (s • Λ)) → (∀ Λ, S.IsTerm d Λ → (Q Λ ↔ Q' (h • Λ))) → S.amp (h • d) Q' = S.amp d Q ∧ S.mass (h • d) Q' = S.mass d Q := by
  intro F _ _ _ _ _ E _ _ _ L r k S h hh d Q Q' hQ hQ'
  have c1 : ∀ s ∈ S.St, h * s * h⁻¹ ∈ S.St := fun s hs => conj_St S hh hs
  have c2 : ∀ s ∈ S.St, h⁻¹ * s * h ∈ S.St := fun s hs => by
    simpa using conj_St S (inv_mem hh) hs
  have aS := GlobalTheory.T.hermitianFrames_stabilizer_acts_on_terms L r k S d
  have aH := GlobalTheory.T.hermitianFrames_complementUnitary_acts_on_terms L r k S
  have hmu : ∀ Λ, S.IsTerm d Λ → ∀ s ∈ S.St, S.mu (s • Λ) = S.mu Λ := fun Λ hΛ =>
    ((GlobalTheory.T.commonStabilizer_stabilizers_commensurable_volume L r k S).1 Λ (GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hΛ).1.1).2.2
  have iS : ∀ s ∈ S.St, ∀ Λ, (S.IsTerm d (s • Λ) ∧ Q (s • Λ)) ↔ (S.IsTerm d Λ ∧ Q Λ) := by
    intro s hs Λ
    constructor
    · rintro ⟨a, b⟩
      have a' := (aS _ a _ (inv_mem hs)).1
      have b' := hQ _ (inv_mem hs) _ a b
      rw [inv_smul_smul] at a' b'
      exact ⟨a', b'⟩
    · rintro ⟨a, b⟩
      exact ⟨(aS _ a _ hs).1, hQ _ hs _ a b⟩
  have iH : ∀ Λ, (S.IsTerm (h • d) (h • Λ) ∧ Q' (h • Λ)) ↔ (S.IsTerm d Λ ∧ Q Λ) := by
    intro Λ
    constructor
    · rintro ⟨a, b⟩
      have a' := (aH _ _ a _ (inv_mem hh)).1
      rw [inv_smul_smul, inv_smul_smul] at a'
      exact ⟨a', (hQ' _ a').2 b⟩
    · rintro ⟨a, b⟩
      exact ⟨(aH _ _ a _ hh).1, (hQ' _ a).1 b⟩
  constructor
  · refine tsum_orbit_normaliser S.St h c1 c2
      (fun Λ => if S.IsTerm d Λ ∧ Q Λ then (S.mu Λ : ℂ) * S.om d Λ else 0)
      (fun Λ => if S.IsTerm (h • d) Λ ∧ Q' Λ then (S.mu Λ : ℂ) * S.om (h • d) Λ else 0) ?_ ?_
    · intro s hs Λ
      exact if_ctx_congr (iS s hs Λ) (fun a => by rw [hmu _ a.1 s hs, (aS _ a.1 s hs).2.1])
        fun _ => rfl
    · intro Λ
      exact if_ctx_congr (iH Λ)
        (fun a => by rw [(aH _ _ a.1 h hh).2.1, (aH _ _ a.1 h hh).2.2.1]) fun _ => rfl
  · refine tsum_orbit_normaliser S.St h c1 c2
      (fun Λ => if S.IsTerm d Λ ∧ Q Λ then ENNReal.ofReal (S.mu Λ) else 0)
      (fun Λ => if S.IsTerm (h • d) Λ ∧ Q' Λ then ENNReal.ofReal (S.mu Λ) else 0) ?_ ?_
    · intro s hs Λ
      exact if_ctx_congr (iS s hs Λ) (fun a => by rw [hmu _ a.1 s hs]) fun _ => rfl
    · intro Λ
      exact if_ctx_congr (iH Λ) (fun a => by rw [(aH _ _ a.1 h hh).2.2.1]) fun _ => rfl

end GlobalTheory.InvH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCard
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCard
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.SmallImage

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def reps (Λ : Submodule L.O S.V) : Submodule L.O S.V where
  carrier := {y | y ∈ Λ ∧ ∃ w ∈ S.W0, ∃ la ∈ S.X, ∃ la' ∈ S.X', w + la ∈ Λ ∧
    la' - la = algebraMap F E S.th • y}
  zero_mem' := ⟨Λ.zero_mem, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _, 0, Submodule.zero_mem _,
    by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, w, hw, la, hla, la', hla', h1, h2⟩ ⟨hb, v, hv, lb, hlb, lb', hlb', h3, h4⟩
    refine ⟨Λ.add_mem ha hb, w + v, add_mem hw hv, la + lb, add_mem hla hlb, la' + lb', add_mem hla' hlb',
      ?_, ?_⟩
    · rw [add_add_add_comm]; exact Λ.add_mem h1 h3
    · rw [smul_add, ← h2, ← h4]; abel
  smul_mem' := by
    rintro c a ⟨ha, w, hw, la, hla, la', hla', h1, h2⟩
    refine ⟨Λ.smul_mem c ha, (c : E) • w, Submodule.smul_mem _ _ hw, (c : E) • la,
      Submodule.smul_mem _ _ hla, (c : E) • la', Submodule.smul_mem _ _ hla', ?_, ?_⟩
    · rw [← smul_add]; exact Λ.smul_mem c h1
    · rw [← smul_sub, h2, smul_comm]; rfl

end

theorem _root_.GlobalTheory.HL.SmallImage.resQ_pos {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (ϖ : 𝒪[F]) (h : Irreducible ϖ) : 0 < _root_.GlobalTheory.HL.resQ ϖ := by
  unfold _root_.GlobalTheory.HL.resQ
  have hmax : IsLocalRing.maximalIdeal 𝒪[F] = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp h
  rw [← hmax]
  have : Finite (IsLocalRing.ResidueField 𝒪[F]) := inferInstance
  exact Nat.card_pos_iff.mpr ⟨inferInstance, this⟩

private lemma hf_sub_left_flag_measures {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L H (x - x') y = _root_.GlobalTheory.HL.hf L H x y - _root_.GlobalTheory.HL.hf L H x' y := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma hf_sub_right_flag_measures {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x y y' : Fin n → E) :
    _root_.GlobalTheory.HL.hf L H x (y - y') = _root_.GlobalTheory.HL.hf L H x y - _root_.GlobalTheory.HL.hf L H x y' := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.sub_apply, map_sub, mul_sub, Finset.sum_sub_distrib]

private lemma hf_add_left_flag_measures'' {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    _root_.GlobalTheory.HL.hf L H (x + x') y = _root_.GlobalTheory.HL.hf L H x y + _root_.GlobalTheory.HL.hf L H x' y := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma hf_algebraMap_smul_right {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E) {n : ℕ} (H : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) (c : F) :
    _root_.GlobalTheory.HL.hf L H x (algebraMap F E c • y) = algebraMap F E c * _root_.GlobalTheory.HL.hf L H x y := by
  unfold _root_.GlobalTheory.HL.hf
  simp only [Pi.smul_apply, smul_eq_mul, map_mul, AlgEquiv.commutes, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem _root_.GlobalTheory.HL.SmallImage.small_image : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∃ i : ℕ, S.cardI d Λ = S.q ^ i) ∧ S.cardI d Λ ≤ S.be d Λ ∧ (¬ S.BBzero d Λ → ¬ S.TypeBe d Λ → S.q * S.cardI d Λ ≤ S.be d Λ) := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT
  have hbasic := _root_.GlobalTheory.HL.TermBasic.term_basic L r k S d Λ hT
  have hMsat : S.M d Λ ≤ S.sat Λ := hbasic.2.2.1
  have hth : S.th ≠ 0 := by
    unfold _root_.GlobalTheory.HL.Frames.th
    split_ifs
    · exact_mod_cast S.ϖ_irr.ne_zero
    · exact one_ne_zero
  have hX : S.X ≤ S.ME := by
    unfold _root_.GlobalTheory.HL.Frames.X _root_.GlobalTheory.HL.Frames.ME
    exact (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f (Nat.le_succ r)).trans le_sup_left
  have hX' : S.X' ≤ S.ME := by
    unfold _root_.GlobalTheory.HL.Frames.X' _root_.GlobalTheory.HL.Frames.ME
    exact (_root_.GlobalTheory.HL.FrameOnto.spanTo_mono S S.f' (Nat.le_succ r)).trans le_sup_right
  have hIsat : S.Ihat d Λ ≤ S.sat Λ := by
    unfold _root_.GlobalTheory.HL.Frames.Ihat
    refine sup_le hMsat (Submodule.span_le.mpr ?_)
    rintro y ⟨w, hw, la, hla, la', hla', h1, h2, ⟨y1, hy1, hy1e⟩, h4⟩
    have hy1' : (algebraMap F E) S.th⁻¹ • (la' - la) = y1 := by
      rw [hy1e, smul_smul, ← map_mul, inv_mul_cancel₀ hth, map_one, one_smul]
    have hME : y1 ∈ S.ME := by
      rw [← hy1']
      apply Submodule.smul_mem
      exact Submodule.sub_mem _ (hX' hla') (hX hla)
    have hy1sat : y1 ∈ S.sat Λ := by
      unfold _root_.GlobalTheory.HL.Frames.sat
      exact Submodule.mem_inf.mpr ⟨hy1, (Submodule.restrictScalars_mem _ _ _).mpr hME⟩
    have hsum : y = (y - (algebraMap F E) S.th⁻¹ • (la' - la)) + y1 := by
      rw [hy1']; abel
    rw [SetLike.mem_coe, hsum]
    exact Submodule.add_mem _ (hMsat h4) hy1sat
  have hMI : S.M d Λ ≤ S.Ihat d Λ := by
    unfold _root_.GlobalTheory.HL.Frames.Ihat; exact le_sup_left
  have hq : 0 < S.q :=
    _root_.GlobalTheory.HL.SmallImage.resQ_pos S.ϖ S.ϖ_irr
  obtain ⟨j, -, hbe⟩ := (_root_.GlobalTheory.HL.Defect.exponents_and_defect L r k S d Λ hT).2.2.2.2.2.1
  have hprod := AddSubgroup.relIndex_mul_relIndex (S.M d Λ).toAddSubgroup (S.Ihat d Λ).toAddSubgroup
    (S.sat Λ).toAddSubgroup (fun x hx => hMI hx) (fun x hx => hIsat hx)
  unfold _root_.GlobalTheory.HL.Frames.cardI _root_.GlobalTheory.HL.Frames.be
    at *
  have hbe0 : (S.M d Λ).toAddSubgroup.relIndex (S.sat Λ).toAddSubgroup ≠ 0 := by
    rw [hbe]; positivity
  rw [← hprod] at hbe0 ⊢
  have hI0 := left_ne_zero_of_mul hbe0
  have hJ0 := right_ne_zero_of_mul hbe0
  refine ⟨?_, ?_, ?_⟩
  · have hfin : Finite (↥(S.Ihat d Λ) ⧸ (S.M d Λ).comap (S.Ihat d Λ).subtype) :=
      Nat.finite_of_card_ne_zero hI0
    obtain ⟨i, hi⟩ := (_root_.GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ
      S.ϖ_irr (↥(S.Ihat d Λ) ⧸ (S.M d Λ).comap (S.Ihat d Λ).subtype)).1
    exact ⟨i, hi⟩
  · exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hJ0)
  · intro hB hTB
    have hne : S.Ihat d Λ ≠ S.sat Λ := by
      intro heq
      apply hTB
      have hcancel : ∀ v : S.V,
          algebraMap F E S.th • (algebraMap F E S.th⁻¹ • v) = v := by
        intro v; rw [smul_smul, ← map_mul, mul_inv_cancel₀ hth, map_one, one_smul]
      have hcancel' : ∀ v : S.V,
          algebraMap F E S.th⁻¹ • (algebraMap F E S.th • v) = v := by
        intro v; rw [smul_smul, ← map_mul, inv_mul_cancel₀ hth, map_one, one_smul]
      refine _root_.GlobalTheory.HL.TypeRep.main L r k S d Λ hT hB
        (_root_.GlobalTheory.HL.SmallImage.reps S Λ) ?_ ?_ ?_
      · rintro y ⟨hyΛ, w, hw, la, hla, la', hla', h1, h2⟩
        refine ⟨hyΛ, ?_⟩
        rw [← hcancel' y, ← h2]
        exact Submodule.smul_mem _ _
          (Submodule.sub_mem _ (Submodule.mem_sup_right hla') (Submodule.mem_sup_left hla))
      · intro y hy
        rw [← heq] at hy
        have hle : S.Ihat d Λ ≤ S.M d Λ ⊔ _root_.GlobalTheory.HL.SmallImage.reps S Λ := by
          unfold _root_.GlobalTheory.HL.Frames.Ihat
          refine sup_le le_sup_left (Submodule.span_le.mpr ?_)
          rintro z ⟨w, hw, la, hla, la', hla', h1, h2, ⟨y1, hy1, hy1e⟩, h4⟩
          have hy1' : (algebraMap F E) S.th⁻¹ • (la' - la) = y1 := by
            rw [hy1e, hcancel']
          have hrep : y1 ∈ _root_.GlobalTheory.HL.SmallImage.reps S Λ :=
            ⟨hy1, w, hw.1, la, hla, la', hla', h1, hy1e⟩
          have hsum : z = (z - (algebraMap F E) S.th⁻¹ • (la' - la)) + y1 := by
            rw [hy1']; abel
          rw [SetLike.mem_coe, hsum]
          exact Submodule.add_mem _ (Submodule.mem_sup_left h4) (Submodule.mem_sup_right hrep)
        obtain ⟨m, hm, y₀, hy₀, hmy⟩ := Submodule.mem_sup.mp (hle hy)
        refine ⟨y₀, hy₀, ?_⟩
        rw [← hmy, add_sub_cancel_right]
        exact hm
      · intro x₁ hx₁ x₁' hx₁' x₂ hx₂ x₂' hx₂' hy₁ hy₂
        obtain ⟨hΛ1, w₁, hw₁, la₁, hla₁, la₁', hla₁', hwl₁, he₁⟩ := hy₁
        obtain ⟨hΛ2, w₂, hw₂, la₂, hla₂, la₂', hla₂', hwl₂, he₂⟩ := hy₂
        rw [hcancel] at he₁ he₂
        have isoX : ∀ a ∈ S.X, ∀ b ∈ S.X,
            _root_.GlobalTheory.HL.hf L S.Hm a b = 0 := fun a ha b hb =>
          _root_.GlobalTheory.HL.FrameOnto.spanTo_le_perp S S.f _ S.gram ha b hb
        have isoX' : ∀ a ∈ S.X', ∀ b ∈ S.X',
            _root_.GlobalTheory.HL.hf L S.Hm a b = 0 := fun a ha b hb =>
          _root_.GlobalTheory.HL.FrameOnto.spanTo_le_perp S S.f' _ S.gram' ha b hb
        have hperp : ∀ w ∈ S.W0, ∀ m ∈ S.ME,
            _root_.GlobalTheory.HL.hf L S.Hm w m = 0 := fun w hw m hm => hw m hm
        have hz₁ : x₁ + la₁ = la₁' - x₁' := by
          rw [sub_eq_iff_eq_add] at he₁; rw [he₁]; abel
        have hz₂ : x₂ + la₂ = la₂' - x₂' := by
          rw [sub_eq_iff_eq_add] at he₂; rw [he₂]; abel
        have hz₁X' : x₁ + la₁ ∈ S.X' := by
          rw [hz₁]; exact Submodule.sub_mem _ hla₁' hx₁'
        have hz₂X : x₂ + la₂ ∈ S.X := Submodule.add_mem _ hx₂ hla₂
        have hz₂X' : x₂ + la₂ ∈ S.X' := by
          rw [hz₂]; exact Submodule.sub_mem _ hla₂' hx₂'
        have e1 : x₁ = (x₁ + la₁) - la₁ := by abel
        have e2 : x₂' = la₂' - (x₂ + la₂) := by rw [hz₂]; abel
        have hmain : _root_.GlobalTheory.HL.hf L S.Hm x₁ x₂'
            = -_root_.GlobalTheory.HL.hf L S.Hm la₁ la₂' := by
          rw [e1, e2, hf_sub_left_flag_measures, hf_sub_right_flag_measures, hf_sub_right_flag_measures, isoX' _ hz₁X' _ hla₂',
            isoX' _ hz₁X' _ hz₂X', isoX _ hla₁ _ hz₂X]
          ring
        have hkey : _root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁) (la₂' - la₂)
            = _root_.GlobalTheory.HL.hf L S.Hm la₁ la₂' := by
          rw [hf_add_left_flag_measures'', hf_sub_right_flag_measures, hf_sub_right_flag_measures, hperp w₁ hw₁ la₂' (hX' hla₂'),
            hperp w₁ hw₁ la₂ (hX hla₂), isoX la₁ hla₁ la₂ hla₂]
          ring
        have hsm : _root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁) (la₂' - la₂)
            = algebraMap F E S.th * _root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁)
              (algebraMap F E S.th⁻¹ • (x₂ + x₂')) := by
          rw [← hf_algebraMap_smul_right, hcancel, he₂]
        have hdual := hbasic.1
        unfold _root_.GlobalTheory.HL.IsSD at hdual
        refine ⟨-_root_.GlobalTheory.HL.hf L S.Hm (w₁ + la₁)
          (algebraMap F E S.th⁻¹ • (x₂ + x₂')), ?_, ?_⟩
        · exact L.O.neg_mem ((hdual.2 _).mpr hΛ2 _ hwl₁)
        · show _root_.GlobalTheory.HL.hf L S.Hm x₁ x₂' = _
          rw [hmain, ← hkey, hsm]
          ring
    have hfin : Finite (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype) :=
      Nat.finite_of_card_ne_zero hJ0
    have hbot : (⊥ : Submodule L.O (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype)) ≠ ⊤ := by
      intro hbt
      apply hne
      refine le_antisymm hIsat (fun x hx => ?_)
      have hmem : Submodule.Quotient.mk (p := (S.Ihat d Λ).comap (S.sat Λ).subtype) ⟨x, hx⟩ ∈
          (⊥ : Submodule L.O (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype)) := by
        rw [hbt]; trivial
      rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero] at hmem
      exact hmem
    have hle := (_root_.GlobalTheory.FiniteModuleOrder.card_eq_pow_and_index_ge L S.ϖ
      S.ϖ_irr (↥(S.sat Λ) ⧸ (S.Ihat d Λ).comap (S.sat Λ).subtype)).2 ⊥ hbot
    rw [Nat.card_unique, mul_one] at hle
    rw [mul_comm]
    exact Nat.mul_le_mul_left _ hle

end GlobalTheory.HL.SmallImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GluingImageCardPowLeDefectGroupCardStatement
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL MeasureTheory
open scoped Pointwise ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gluingImage_card_pow_le_defectGroup_card : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : LocE F E), ∀ (r k : ℕ) (S : Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → (∃ i : ℕ, S.cardI d Λ = S.q ^ i) ∧ S.cardI d Λ ≤ S.be d Λ ∧ (¬ S.BBzero d Λ → ¬ S.TypeBe d Λ → S.q * S.cardI d Λ ≤ S.be d Λ) := by
  first | exact @GlobalTheory.HL.SmallImage.small_image | exact GlobalTheory.HL.SmallImage.small_image | (intros; apply GlobalTheory.HL.SmallImage.small_image <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrbitWeightedStabilizerSumEqSumOrbitReps
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass

theorem _root_.GlobalTheory.Mass.orbSum_eq_sum_reps : ∀ (G α : Type) [Group G] [MulAction G α]
    (X : Set α) (N : α → ℝ≥0∞), _root_.GlobalTheory.Mass.Stable G X → (∀ (g : G) x, N (g • x) = N x) →
    ∀ s : Finset α, (∀ x ∈ s, x ∈ X) → (∀ x ∈ X, ∃! y, y ∈ s ∧ ∃ g : G, g • y = x) →
    _root_.GlobalTheory.Mass.orbSum G X N =
      ∑ x ∈ s, ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ * N x := by
  intro G α _ _ X N hX hN s hs huniq
  have hX' : ∀ (g : G), ∀ x ∈ X, g • x ∈ X := hX
  unfold _root_.GlobalTheory.Mass.orbSum
  have hout : ∀ x : α, ∃ g : G, g • x = (Quotient.mk (MulAction.orbitRel G α) x).out := fun x =>
    MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp
      (Quotient.exact (Quotient.out_eq (Quotient.mk (MulAction.orbitRel G α) x))))
  have hterm : ∀ x : α,
      ((ENat.card (MulAction.stabilizer G (Quotient.mk (MulAction.orbitRel G α) x).out) : ℕ∞) :
          ℝ≥0∞)⁻¹ * N (Quotient.mk (MulAction.orbitRel G α) x).out
        = ((ENat.card (MulAction.stabilizer G x) : ℕ∞) : ℝ≥0∞)⁻¹ * N x := by
    intro x
    obtain ⟨g, hg⟩ := hout x
    rw [← hg, hN,
      ENat.card_congr (MulAction.stabilizerEquivStabilizer (rfl : g • x = g • x)).toEquiv.symm]
  let e : {x // x ∈ s} → {q : MulAction.orbitRel.Quotient G α // q.out ∈ X} := fun x =>
    ⟨Quotient.mk _ x.1, by obtain ⟨g, hg⟩ := hout x.1; rw [← hg]; exact hX' g _ (hs _ x.2)⟩
  have he_inj : Function.Injective e := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
    have hq : Quotient.mk (MulAction.orbitRel G α) x = Quotient.mk _ y := congrArg Subtype.val hxy
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp (Quotient.exact hq))
    obtain ⟨z, -, hz⟩ := huniq x (hs x hx)
    have h1 := hz x ⟨hx, 1, one_smul G x⟩
    have h2 := hz y ⟨hy, g, hg⟩
    exact Subtype.ext (h1.trans h2.symm)
  have he_surj : Function.Surjective e := by
    rintro ⟨q, hq⟩
    obtain ⟨y, ⟨hy, g, hg⟩, -⟩ := huniq q.out hq
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    show Quotient.mk _ y = q
    calc Quotient.mk (MulAction.orbitRel G α) y = Quotient.mk _ q.out :=
          Quotient.sound (MulAction.orbitRel_apply.mpr
            (MulAction.mem_orbit_iff.mpr ⟨g⁻¹, inv_smul_eq_iff.mpr hg.symm⟩))
      _ = q := Quotient.out_eq q
  rw [← (Equiv.ofBijective e ⟨he_inj, he_surj⟩).tsum_eq, tsum_fintype, ← Finset.sum_coe_sort s]
  exact Finset.sum_congr rfl fun x _ => hterm x.1

end GlobalTheory.Mass
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCompleteDense
open MeasureTheory Formalism.MainNotions.S
open scoped InnerProductSpace TensorProduct

noncomputable section

namespace GlobalTheory.HilbTensorExists

theorem exists_pre_fin (n : ℕ) : ∀ (H : Fin n → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)],
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by
  induction n with
  | zero =>
    intro H _ _
    refine ⟨ℂ, inferInstance, inferInstance, fun _ => 1, fun x y => ?_⟩
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    simp
  | succ n ih =>
    intro H _ _
    obtain ⟨K, iK, iK', t, ht⟩ := ih (fun i => H i.castSucc)
    refine ⟨K ⊗[ℂ] H (Fin.last n), inferInstance, inferInstance,
      fun x => t (fun i => x i.castSucc) ⊗ₜ[ℂ] x (Fin.last n), fun x y => ?_⟩
    rw [TensorProduct.inner_tmul, ht, Fin.prod_univ_castSucc]

theorem exists_pre {ι : Type} [Fintype ι] (H : ι → Type) [∀ v, NormedAddCommGroup (H v)]
    [∀ v, InnerProductSpace ℂ (H v)] :
    ∃ (K : Type) (_ : NormedAddCommGroup K) (_ : InnerProductSpace ℂ K) (t : (∀ v, H v) → K),
      ∀ x y, ⟪t x, t y⟫_ℂ = ∏ v, ⟪x v, y v⟫_ℂ := by
  let e := Fintype.equivFin ι
  obtain ⟨K, iK, iK', t, ht⟩ := exists_pre_fin (Fintype.card ι) (fun i => H (e.symm i))
  refine ⟨K, iK, iK', fun x => t (fun i => x (e.symm i)), fun x y => ?_⟩
  rw [ht]
  exact e.symm.prod_comp (fun v => ⟪x v, y v⟫_ℂ)

theorem exists_complete_dense {X K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] (t : X → K) :
    ∃ (L : Type) (_ : NormedAddCommGroup L) (_ : InnerProductSpace ℂ L) (_ : CompleteSpace L) (s : X → L),
      (∀ x y, ⟪s x, s y⟫_ℂ = ⟪t x, t y⟫_ℂ) ∧ Dense (Submodule.span ℂ (Set.range s) : Set L) := by
  let V := Submodule.span ℂ (Set.range t)
  let u : X → V := fun x => ⟨t x, Submodule.subset_span ⟨x, rfl⟩⟩
  have hu : Submodule.span ℂ (Set.range u) = ⊤ := by
    apply Submodule.map_injective_of_injective V.injective_subtype
    rw [Submodule.map_span, Submodule.map_subtype_top, ← Set.range_comp]
    rfl
  refine ⟨UniformSpace.Completion V, inferInstance, inferInstance, inferInstance,
    fun x => ((u x : V) : UniformSpace.Completion V), fun x y => ?_, ?_⟩
  · rw [UniformSpace.Completion.inner_coe]
    rfl
  · refine UniformSpace.Completion.denseRange_coe.mono ?_
    rintro _ ⟨v, rfl⟩
    have hv : v ∈ Submodule.span ℂ (Set.range u) := hu ▸ Submodule.mem_top
    have hm := Submodule.mem_map_of_mem
      (f := (UniformSpace.Completion.toComplₗᵢ (𝕜 := ℂ) (E := V)).toLinearMap) hv
    rw [Submodule.map_span, ← Set.range_comp] at hm
    exact hm

end GlobalTheory.HilbTensorExists
end
end
