module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.IsUnimodularAtIffVd
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.MemSmulOfMemSmulLocF

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SumOrbitsEquivariant
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']

variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

def fibG (S : VecSplit h h') (L : Submodule (𝓞 K) V) (Λ' : Submodule (𝓞 K) V') :
    Set (Submodule (𝓞 K) V) :=
  {Λ | Λ ∈ Formalism.HermitianLatticesTheory.genus h L ∧ S.x₀ ∈ Λ ∧ S.cut Λ = Λ'}

def IsFibReps (S : VecSplit h h') (L : Submodule (𝓞 K) V) (s' : Finset (Submodule (𝓞 K) V')) :
    Prop :=
  (∀ Λ' ∈ s', (fibG S L Λ').Nonempty) ∧
  ∀ Λ' : Submodule (𝓞 K) V', (fibG S L Λ').Nonempty →
    ∃! Λ₀, Λ₀ ∈ s' ∧ ∃ g ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g Λ₀ = Λ'

namespace StabilizerLattices

open SplitBAux

theorem pair_mem_of_fibG (S : VecSplit h h') {L : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'}
    {Λ : Submodule (𝓞 K) V} (hΛ : Λ ∈ fibG S L Λ') :
    (Λ, S.x₀) ∈ pairs h L (h S.x₀ S.x₀) ∧ proj h (Λ, S.x₀) = (emb S Λ', S.x₀) :=
  ⟨⟨hΛ.1, hΛ.2.1, rfl⟩, Prod.ext (by rw [← hΛ.2.2]; exact inf_perpO S Λ) rfl⟩

theorem fibG_of_pair_mem (S : VecSplit h h') {L : Submodule (𝓞 K) V} {Λ' : Submodule (𝓞 K) V'}
    {p : Submodule (𝓞 K) V × V} (hp : p ∈ pairs h L (h S.x₀ S.x₀))
    (e : proj h p = (emb S Λ', S.x₀)) : p.1 ∈ fibG S L Λ' ∧ p.2 = S.x₀ := by
  obtain ⟨Λ, x⟩ := p
  obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
  change Λ ⊓ perpO h x = emb S Λ' at e1
  change x = S.x₀ at e2
  subst e2
  rw [inf_perpO] at e1
  exact ⟨⟨hp.1, hp.2.1, emb_injective S e1⟩, rfl⟩

theorem exists_move (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') (L : Submodule (𝓞 K) V) (p : Submodule (𝓞 K) V × V) :
    ∃ g : Formalism.HermitianLatticesTheory.isom h, p ∈ pairs h L (h S.x₀ S.x₀) →
      g • p = (Formalism.HermitianLatticesTheory.gmap g.1 p.1, S.x₀) ∧
      Formalism.HermitianLatticesTheory.gmap g.1 p.1 ∈ fibG S L (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)) := by
  by_cases hp : p ∈ pairs h L (h S.x₀ S.x₀)
  · have hne : p.2 ≠ 0 := by
      intro h0
      have := hp.2.2
      rw [h0] at this
      exact S.hx₀ (by simpa using this.symm)
    obtain ⟨g, hg, hgx⟩ := exists_isom_map_of_eq hK hs hd hne hp.2.2
    refine ⟨⟨g, hg⟩, fun _ => ⟨Prod.ext rfl hgx, OrbitRepresentatives.gmap_mem_genus hs hp.1 hg, ?_, rfl⟩⟩
    rw [← hgx]
    exact apply_mem_gmap g hp.2.1
  · exact ⟨1, fun h => absurd h hp⟩

theorem fibG_smul (hs : h.IsSymm) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    {Λ' : Submodule (𝓞 K) V'} {Λ : Submodule (𝓞 K) V} (hΛ : Λ ∈ fibG S L Λ')
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h') :
    Formalism.HermitianLatticesTheory.gmap (extOf S g') Λ ∈ fibG S L (Formalism.HermitianLatticesTheory.gmap g' Λ') := by
  refine ⟨OrbitRepresentatives.gmap_mem_genus hs hΛ.1 (extOf_mem_isom hs S hg'), ?_, ?_⟩
  · have := apply_mem_gmap (extOf S g') hΛ.2.1
    rwa [extOf_x₀] at this
  · rw [cut_gmap_extOf, hΛ.2.2]

theorem finite_stab_proj (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') (L : Submodule (𝓞 K) V) {p : Submodule (𝓞 K) V × V}
    (hp : p ∈ pairs h L (h S.x₀ S.x₀)) :
    (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (proj h p) : Set (Formalism.HermitianLatticesTheory.isom h)).Finite := by
  obtain ⟨g, hg⟩ := exists_move hK hs hd S L p
  obtain ⟨hg1, hg2⟩ := hg hp
  have e : g • proj h p = (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
    rw [← proj_smul, hg1]
    exact (pair_mem_of_fibG S hg2).2
  have hlat : Submodule.IsFullLattice K (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)) := isFullLattice_cut S hg2.1.1
  have f1 : Finite (Formalism.ThetaLiftIndependence.autL h' (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1))) :=
    (Formalism.HermitianLatticesTheory.autFinite K V' h' (S.isSymm hs) (trace_pos (S.isTotPosDef hd)) _ hlat).to_subtype
  have f2 : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (g • proj h p)) := by
    rw [e]
    exact Finite.of_equiv _ (stabPairEquiv hs S _).symm
  have f3 : Finite (MulAction.stabilizer (Formalism.HermitianLatticesTheory.isom h) (proj h p)) :=
    Finite.of_equiv _ (MulAction.stabilizerEquivStabilizer (g := g) (a := proj h p) rfl).symm.toEquiv
  exact Set.toFinite _

end StabilizerLattices

open StabilizerLattices SplitBAux in
theorem exists_fibReps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) : ∃ s', IsFibReps S L s' := by
  classical
  obtain ⟨sX, hsX, hX⟩ := exists_pairReps hs hd hL (h S.x₀ S.x₀)
  choose γ hγ using exists_move hK hs hd S L
  obtain ⟨T, hT1, hT2⟩ := OrbSum.exists_reps_of_cover (G := Formalism.HermitianLatticesTheory.isom h')
    {Λ' : Submodule (𝓞 K) V' | (fibG S L Λ').Nonempty}
    (fun g' Λ' ⟨Λ, hΛ⟩ => ⟨_, fibG_smul hs S hΛ g'.2⟩)
    ((fun p => S.cut (Formalism.HermitianLatticesTheory.gmap (γ p).1 p.1)) '' (sX : Set (Submodule (𝓞 K) V × V)))
    (sX.finite_toSet.image _)
    (by
      rintro _ ⟨p, hp, rfl⟩
      exact ⟨_, (hγ p (hsX p hp)).2⟩)
    (by
      rintro Λ' ⟨Λ, hΛ⟩
      obtain ⟨t, ⟨ht, k, hk⟩, -⟩ := hX _ (pair_mem_of_fibG S hΛ).1
      refine ⟨_, ⟨t, ht, rfl⟩, ?_⟩
      have e : (k * (γ t)⁻¹) • (Formalism.HermitianLatticesTheory.gmap (γ t).1 t.1, S.x₀) = (Λ, S.x₀) := by
        rw [← (hγ t (hsX t ht)).1, mul_smul, inv_smul_smul, hk]
      obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
      have := gmap_res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2 e1
      rw [hΛ.2.2] at this
      exact ⟨⟨res S (k * (γ t)⁻¹).1 (k * (γ t)⁻¹).2 e2, res_mem_isom S _ _ _⟩, this⟩)
  refine ⟨T, hT1, fun Λ' hΛ' => ?_⟩
  have := hT2 Λ' hΛ'
  simp_rw [exists_smul_iff] at this
  exact this

open StabilizerLattices SplitBAux in
theorem repMass_eq_sum_fib (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L)
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {s' : Finset (Submodule (𝓞 K) V')}
    (hs' : IsFibReps S L s') :
    repMass h L (h S.x₀ S.x₀) =
      ∑ Λ' ∈ s', (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) := by
  classical
  obtain ⟨sX, hsX, hX⟩ := exists_pairReps hs hd hL (h S.x₀ S.x₀)
  have hex := exists_classReps hs hd hL
  unfold repMass
  rw [dite_eq_left hex, ← sum_pairs_eq_rep hs hd (h S.x₀ S.x₀) hex.choose_spec hsX hX]
  have key := OrbSum.sum_orbits_on (G := Formalism.HermitianLatticesTheory.isom h) (proj h) proj_smul
    (pairs h L (h S.x₀ S.x₀)) (proj h '' pairs h L (h S.x₀ S.x₀))
    (pairs_stable hs L _) (fun p hp => Set.mem_image_of_mem _ hp) sX
    (s'.image fun Λ' => (emb S Λ', S.x₀)) hsX
    (by
      intro u hu
      obtain ⟨Λ', hΛ', rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨Λ, hΛ⟩ := hs'.1 Λ' hΛ'
      exact ⟨_, (pair_mem_of_fibG S hΛ).1, (pair_mem_of_fibG S hΛ).2⟩)
    hX
    (by
      rintro _ ⟨p, hp, rfl⟩
      obtain ⟨g, hg⟩ := exists_move hK hs hd S L p
      obtain ⟨hg1, hg2⟩ := hg hp
      have hgy : g • proj h p = (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
        rw [← proj_smul, hg1]
        exact (pair_mem_of_fibG S hg2).2
      obtain ⟨Λ₀, ⟨h₀, g', hg', e'⟩, huniq⟩ := hs'.2 _ ⟨_, hg2⟩
      refine ⟨(emb S Λ₀, S.x₀), ⟨Finset.mem_image.mpr ⟨Λ₀, h₀, rfl⟩,
        g⁻¹ * ⟨extOf S g', extOf_mem_isom hs S hg'⟩, ?_⟩, ?_⟩
      · have e0 : (⟨extOf S g', extOf_mem_isom hs S hg'⟩ : Formalism.HermitianLatticesTheory.isom h) • (emb S Λ₀, S.x₀) =
            g • proj h p := by
          rw [hgy, ← e', ← gmap_extOf_emb]
          exact Prod.ext rfl (extOf_x₀ S g')
        rw [mul_smul, e0, inv_smul_smul]
      · rintro t ⟨ht, k, hk⟩
        obtain ⟨Λ₁, h₁, rfl⟩ := Finset.mem_image.mp ht
        have e : (g * k) • (emb S Λ₁, S.x₀) =
            (emb S (S.cut (Formalism.HermitianLatticesTheory.gmap g.1 p.1)), S.x₀) := by
          rw [mul_smul, hk, hgy]
        obtain ⟨e1, e2⟩ := Prod.ext_iff.mp e
        have := gmap_res S (g * k).1 (g * k).2 e2 e1
        rw [cut_emb, cut_emb] at this
        rw [huniq Λ₁ ⟨h₁, _, res_mem_isom S _ _ _, this⟩])
    (by
      rintro _ ⟨p, hp, rfl⟩
      exact finite_stab_proj hK hs hd S L hp)
  rw [key, Finset.sum_image (fun A _ B _ e => emb_injective S (Prod.ext_iff.mp e).1)]
  refine Finset.sum_congr rfl fun Λ' _ => ?_
  have e1 : Nat.card {p : Submodule (𝓞 K) V × V //
      p ∈ pairs h L (h S.x₀ S.x₀) ∧ proj h p = (emb S Λ', S.x₀)} = Nat.card (fibG S L Λ') :=
    Nat.card_congr
      { toFun := fun p => ⟨p.1.1, (fibG_of_pair_mem S p.2.1 p.2.2).1⟩
        invFun := fun Λ => ⟨(Λ.1, S.x₀), pair_mem_of_fibG S Λ.2⟩
        left_inv := fun p => Subtype.ext (Prod.ext rfl (fibG_of_pair_mem S p.2.1 p.2.2).2.symm)
        right_inv := fun _ => rfl }
  rw [e1, Nat.card_congr (stabPairEquiv hs S Λ')]

end Formalism.HermitianLattices.Ext.L3
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.SupEqTopOfMemHcompl
open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.OrthogonalBases

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem sup_eq_top_of_mem_hcompl (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {P : Ideal (𝓞 K)}
    (hP : P.IsMaximal) {u : 𝓞 K} (hu : u ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P) :
    Ideal.span {u} ⊔ extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) = ⊤ := by
  by_contra hne
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_le_maximal _ hne
  have hu' := (Formalism.HermitianLattices.Ext.L3.WA.mem_hcompl_iff hP.isPrime u).1 hu
  have huQ : u ∈ Q := hle (Ideal.mem_sup_left (Ideal.mem_span_singleton_self u))
  have hext : extP K (P.comap (algebraMap (𝓞 F) (𝓞 K))) ≤ Q := le_trans le_sup_right hle
  have hpQ : P.comap (algebraMap (𝓞 F) (𝓞 K)) ≤ Q.comap (algebraMap (𝓞 F) (𝓞 K)) :=
    Ideal.map_le_iff_le_comap.1 hext
  have hmax : (P.comap (algebraMap (𝓞 F) (𝓞 K))).IsMaximal :=
    Ideal.isMaximal_under_of_isIntegral_of_isMaximal P
  haveI := hQ.isPrime
  have heq : P.comap (algebraMap (𝓞 F) (𝓞 K)) = Q.comap (algebraMap (𝓞 F) (𝓞 K)) :=
    hmax.eq_of_le (inferInstance : (Q.comap (algebraMap (𝓞 F) (𝓞 K))).IsPrime).ne_top hpQ
  rcases (comap_eq_comap_iff hK hF hP hQ).1 heq with h | h
  · exact hu'.1 (h ▸ huQ)
  · exact hu'.2 (h ▸ huQ)

private theorem isUnitIn_mul' {S : Subring K} {a b : K} (ha : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S a)
    (hb : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S b) : Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn S (a * b) :=
  ⟨mul_ne_zero ha.1 hb.1, S.mul_mem ha.2.1 hb.2.1, by rw [mul_inv]; exact S.mul_mem ha.2.2 hb.2.2⟩

theorem exists_orth_basis (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 = 0) :
    ∃ (b : Basis (Fin (finrank K V)) K V) (u : Fin (finrank K V) → 𝓞 K), (∀ i, b i ∈ L) ∧
      locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L ∧
      (∀ i j, algebraMap (𝓞 K) K (diagonal u i j) = h (b i) (b j)) ∧
      (∀ i, conjO K (u i) = u i) ∧ ∀ i, Ideal.span {u i} ⊔ extP K 𝔭 = ⊤ := by
  obtain ⟨P, hP, rfl⟩ := exists_maximal_over hK hF h𝔭
  have hU : Formalism.HermitianLatticesTheory.IsUnimodularAt h P L :=
    (isUnimodularAt_iff_vd hK hF hs hd hL hLi hP).2 hv
  have hSD := Formalism.HermitianLattices.Ext.L3.WA.isSelfDualMod_loc hL hP.isPrime hU
  have hdd : ∀ x, h x x = 0 → x = 0 := by
    intro x hx
    by_contra hx0
    have := hd x hx0 (Classical.arbitrary (NumberField.InfinitePlace K)).embedding
    rw [hx, map_zero, Complex.zero_re] at this
    exact lt_irrefl 0 this
  have hS : WA.IsHermSemilocal (WA.locRing P) :=
    ⟨fun _ ha => WA.star_mem_locRing hP.isPrime ha, WA.frac_locRing P, WA.unram_locRing hK hP,
      WA.principal_locRing hK hP, WA.unit_or_locRing hP.isPrime⟩
  obtain ⟨x, hxM, hxo, hxu⟩ := Formalism.HermitianLattices.Ext.L3.LocF.exists_orth_unit_frame hS
    (Formalism.HermitianLattices.Ext.L3.LocF.locRing_local hP.isPrime) hs hdd hSD
  have hx' : ∀ i, ∃ s ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P, s • x i ∈ L := fun i => hxM i
  choose s hsP hsL using hx'
  set b0 : Fin (finrank K V) → V := fun i => algebraMap (𝓞 K) K (s i) • x i with hb0
  have hb0L : ∀ i, b0 i ∈ L := by
    intro i
    simp only [hb0, algebraMap_smul]
    exact hsL i
  have hbb : ∀ i j, h (b0 i) (b0 j) =
      star (algebraMap (𝓞 K) K (s i)) * algebraMap (𝓞 K) K (s j) * h (x i) (x j) := by
    intro i j
    simp only [hb0, LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply]
    ring
  have hunit : ∀ i, Formalism.HermitianLattices.Ext.L3.WA.IsUnitIn (Formalism.HermitianLattices.Ext.L3.WA.locRing P) (h (b0 i) (b0 i)) := by
    intro i
    have hσ := (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (s i)).2 (hsP i)
    have hσs := (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (conjO K (s i))).2
      (Formalism.HermitianLattices.Ext.L3.WA.conjO_mem_hcompl (hsP i))
    rw [hbb]
    exact isUnitIn_mul' (isUnitIn_mul' hσs hσ) (hxu i)
  have horth : ∀ i j, i ≠ j → h (b0 i) (b0 j) = 0 := by
    intro i j hij
    rw [hbb, hxo i j hij, mul_zero]
  have hint : ∀ i, h (b0 i) (b0 i) ∈ (1 : Submodule (𝓞 K) K) := fun i => hLi _ (hb0L i) _ (hb0L i)
  choose u hu using fun i => Submodule.mem_one.1 (hint i)
  have huP : ∀ i, u i ∈ Formalism.HermitianLatticesTheory.hcompl (K := K) P := by
    intro i
    refine (Formalism.HermitianLattices.Ext.L3.LocF.isUnitIn_algebraMap_iff hP.isPrime (u i)).1 ?_
    rw [hu i]
    exact hunit i
  have hli : LinearIndependent K b0 := by
    rw [linearIndependent_iff']
    intro t g hg i hi
    have := congrArg (h (b0 i)) hg
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_zero, Finset.sum_eq_single i] at this
    · rw [map_smul, smul_eq_mul] at this
      exact (mul_eq_zero.1 this).resolve_right (hunit i).1
    · intro j _ hji
      rw [map_smul, horth i j (Ne.symm hji), smul_zero]
    · intro hi'
      exact absurd hi hi'
  have htop : ⊤ ≤ Submodule.span K (Set.range b0) :=
    (Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hli, Fintype.card_fin])).ge
  let b := Basis.mk hli htop
  have hb : ⇑b = b0 := Basis.coe_mk hli htop
  refine ⟨b, u, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hb]
    exact hb0L i
  · rw [hb, locF_eq_loc hK hF hP, locF_eq_loc hK hF hP]
    apply le_antisymm
    · rintro y ⟨t, ht, hy⟩
      exact ⟨t, ht, (Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hb0L i)) hy⟩
    · rintro y ⟨t, ht, hy⟩
      have hz : t • y ∈ Formalism.HermitianLatticesTheory.loc (K := K) P (Submodule.span (𝓞 K) (Set.range b0)) := by
        rw [← b.sum_repr (t • y)]
        refine Submodule.sum_mem _ fun i _ => ?_
        refine ⟨u i, huP i, ?_⟩
        obtain ⟨a, ha⟩ := Submodule.mem_one.1 (hLi _ (hb0L i) _ hy)
        have hrep : h (b0 i) (t • y) = b.repr (t • y) i * h (b0 i) (b0 i) := by
          conv_lhs => rw [← b.sum_repr (t • y)]
          set_option synthInstance.maxHeartbeats 100000 in
            rw [map_sum, Finset.sum_eq_single i]
          · rw [map_smul, smul_eq_mul, hb]
          · intro j _ hji
            rw [map_smul, hb, horth i j (Ne.symm hji), smul_zero]
          · intro hi
            exact absurd (Finset.mem_univ i) hi
        have key : u i • (b.repr (t • y) i • b i) = a • b0 i := by
          rw [← algebraMap_smul K (u i), smul_smul, hu i, mul_comm, ← hrep, ← ha, algebraMap_smul, hb]
        rw [key]
        exact Submodule.smul_mem _ a (Submodule.subset_span ⟨i, rfl⟩)
      obtain ⟨t', ht', hy'⟩ := hz
      exact ⟨t' * t, mul_mem ht' ht, by rw [mul_smul]; exact hy'⟩
  · intro i j
    rw [hb, Matrix.diagonal_apply]
    split_ifs with hij
    · subst hij
      exact hu i
    · rw [map_zero, horth i j hij]
  · intro i
    apply IsFractionRing.injective (𝓞 K) K
    have h1 : algebraMap (𝓞 K) K (conjO K (u i)) = star (algebraMap (𝓞 K) K (u i)) := rfl
    rw [h1, hu i, ← starRingEnd_apply]
    exact hs.eq (b0 i) (b0 i)
  · intro i
    exact sup_eq_top_of_mem_hcompl hK hF hP (huP i)

end Formalism.HermitianLattices.Ext.L3.OrthogonalBases
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.FinrankRingOfIntegers
open NumberField Module IsDedekindDomain Function

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BrA

variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]

def maxEquiv (F : Type) [Field F] [NumberField F] :
    {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} ≃ HeightOneSpectrum (𝓞 F) where
  toFun 𝔭 := ⟨𝔭.1, 𝔭.2.isPrime, idealPowerSpanBounds.ne_bot 𝔭.2⟩
  invFun v := ⟨v.asIdeal, v.isMaximal⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem sSup_le_pow (v : HeightOneSpectrum (𝓞 F)) {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    sSup {e : ℕ | I ≤ v.asIdeal ^ e} = multiplicity v.asIdeal I := by
  have hfin : FiniteMultiplicity v.asIdeal I :=
    FiniteMultiplicity.of_not_isUnit v.prime.not_isUnit hI
  have : {e : ℕ | I ≤ v.asIdeal ^ e} = Set.Iic (multiplicity v.asIdeal I) := by
    ext e
    simp only [Set.mem_ofPred_eq, Set.mem_Iic]
    rw [← Ideal.dvd_iff_le, hfin.pow_dvd_iff_le_multiplicity]
  rw [this, csSup_Iic]

theorem absNorm_eq_tprod {I : Ideal (𝓞 F)} (hI : I ≠ ⊥) :
    (Ideal.absNorm I : ℝ) = ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal},
      (Ideal.absNorm 𝔭.1 : ℝ) ^ sSup {e : ℕ | I ≤ 𝔭.1 ^ e} := by
  let φ : Ideal (𝓞 F) →* ℝ :=
    ((Nat.castRingHom ℝ : ℕ →+* ℝ) : ℕ →* ℝ).comp (Ideal.absNorm : Ideal (𝓞 F) →*₀ ℕ).toMonoidHom
  have hφ : ∀ J, φ J = (Ideal.absNorm J : ℝ) := fun _ => rfl
  have h0 : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => v.maxPowDividing I :=
    Ideal.hasFiniteMulSupport hI
  have h1 : φ I = ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) := by
    conv_lhs => rw [← Ideal.finprod_heightOneSpectrum_factorization hI]
    exact map_finprod φ h0
  have h2 : HasFiniteMulSupport fun v : HeightOneSpectrum (𝓞 F) => φ (v.maxPowDividing I) :=
    h0.fun_comp (map_one φ)
  have h3 : ∏' v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) =
      ∏ᶠ v : HeightOneSpectrum (𝓞 F), φ (v.maxPowDividing I) := tprod_eq_finprod h2
  rw [← hφ, h1, ← h3, ← (maxEquiv F).tprod_eq]
  refine tprod_congr fun 𝔭 => ?_
  rw [HeightOneSpectrum.maxPowDividing_eq_pow_multiplicity hI, map_pow, hφ,
    ← sSup_le_pow _ hI]
  rfl

theorem finrank_ringOfIntegers (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) :
    finrank (𝓞 F) (𝓞 K) = 2 := by
  rw [← MeanB.finrank_eq_two hK hF]
  exact (IsFractionRing.finrank_eq (𝓞 F) F (𝓞 K) K).symm

theorem absNorm_map (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (I : Ideal (𝓞 F)) :
    Ideal.absNorm (I.map (algebraMap (𝓞 F) (𝓞 K))) = Ideal.absNorm I ^ 2 := by
  rw [Ideal.absNorm_algebraMap, finrank_ringOfIntegers hK hF]

theorem map_le_extP_pow (I 𝔭 : Ideal (𝓞 F)) (e : ℕ) :
    I.map (algebraMap (𝓞 F) (𝓞 K)) ≤ extP K 𝔭 ^ e ↔ I ≤ 𝔭 ^ e := by
  rw [Ideal.map_le_iff_le_comap, MeanB.comap_extP_pow]

variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

def discrF (F : Type) [Field F] [NumberField F] [Algebra F K] (h : V →ₗ⋆[K] V →ₗ[K] K)
    (L : Submodule (𝓞 K) V) : Ideal (𝓞 F) :=
  (discrIdeal h L).comap (algebraMap (𝓞 F) (𝓞 K))

theorem discrIdeal_eq_map (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (L : Submodule (𝓞 K) V) :
    discrIdeal h L = (discrF F h L).map (algebraMap (𝓞 F) (𝓞 K)) := by
  apply le_antisymm
  · conv_lhs => unfold discrIdeal
    rw [Ideal.span_le]
    rintro z ⟨x, hx, hz⟩
    have hzfix : conjO K z = z := by
      apply RingOfIntegers.ext
      rw [conjO_coe]
      change star (algebraMap (𝓞 K) K z) = algebraMap (𝓞 K) K z
      rw [hz, LocF.star_gram_det h hs]
    obtain ⟨t, ht⟩ := (conjO_eq_iff_mem_range hF z).mp hzfix
    rw [← ht]
    apply Ideal.mem_map_of_mem
    rw [discrF, Ideal.mem_comap, ht]
    exact Ideal.subset_span ⟨x, hx, hz⟩
  · exact Ideal.map_comap_le

theorem vd_eq (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm)
    (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) :
    vd h L 𝔭 = sSup {e : ℕ | discrF F h L ≤ 𝔭 ^ e} := by
  unfold vd
  congr 1
  ext e
  simp only [Set.mem_ofPred_eq]
  rw [discrIdeal_eq_map hF hs, map_le_extP_pow]

theorem normD_eq (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) (L : Submodule (𝓞 K) V) : normD h L = (Ideal.absNorm (discrF F h L) : ℝ) := by
  unfold normD
  rw [discrIdeal_eq_map hF hs, absNorm_map hK hF, Nat.cast_pow, Real.sqrt_sq (Nat.cast_nonneg _)]

theorem discrIdeal_gmap {h : V →ₗ⋆[K] V →ₗ[K] K} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (A : Submodule (𝓞 K) V) : discrIdeal h (Formalism.HermitianLatticesTheory.gmap g A) = discrIdeal h A := by
  unfold discrIdeal
  congr 1
  ext z
  constructor
  · rintro ⟨x, hx, e⟩
    refine ⟨fun i => g.symm (x i), fun i => ?_, ?_⟩
    · obtain ⟨y, hy, hyx⟩ := Submodule.mem_map.mp (hx i)
      have : g y = x i := hyx
      change g.symm (x i) ∈ A
      rw [← this, LinearEquiv.symm_apply_apply]
      exact hy
    · rw [e]
      congr 1
      ext i j
      have := hg (g.symm (x i)) (g.symm (x j))
      rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply] at this
      exact this
  · rintro ⟨x, hx, e⟩
    refine ⟨fun i => g (x i), fun i => Submodule.mem_map.mpr ⟨x i, hx i, rfl⟩, ?_⟩
    rw [e]
    congr 1
    ext i j
    exact (hg (x i) (x j)).symm

theorem form_mem_locF (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {L : Submodule (𝓞 K) V}
    (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) {g : V ≃ₗ[K] V}
    (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {x y : V} (hx : x ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L))
    (hy : y ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) : h x y ∈ locF 𝔭 (1 : Submodule (𝓞 K) K) := by
  obtain ⟨x', hx', ex⟩ := Submodule.mem_map.mp hx
  obtain ⟨y', hy', ey⟩ := Submodule.mem_map.mp hy
  have ex' : g x' = x := ex
  have ey' : g y' = y := ey
  obtain ⟨s, hs, hsx⟩ := (LocF.mem_locF_iff hp L x').mp hx'
  obtain ⟨t, ht, hty⟩ := (LocF.mem_locF_iff hp L y').mp hy'
  rw [← ex', ← ey', hg x' y', LocF.mem_locF_iff hp]
  refine ⟨s * t, fun hm => (hp.mem_or_mem hm).elim hs ht, ?_⟩
  have hsmul :
      h (algebraMap (𝓞 F) (𝓞 K) s • x') (algebraMap (𝓞 F) (𝓞 K) t • y') =
        algebraMap (𝓞 F) (𝓞 K) (s * t) • h x' y' := by
    rw [← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) s),
      ← algebraMap_smul K (algebraMap (𝓞 F) (𝓞 K) t),
      Algebra.smul_def (algebraMap (𝓞 F) (𝓞 K) (s * t))]
    simp only [LinearMap.map_smulₛₗ₂, map_smul, smul_eq_mul, starRingEnd_apply,
      MeanB.algebraMap_comp, MeanB.star_algebraMap hF, map_mul, mul_assoc]
    exact mul_left_comm _ _ _
  exact hsmul ▸ hLi _ hsx _ hty

end Formalism.HermitianLattices.Ext.L3.BrA
end
end
