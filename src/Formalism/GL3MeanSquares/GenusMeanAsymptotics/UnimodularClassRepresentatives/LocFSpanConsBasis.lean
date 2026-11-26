module

public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsGlobalOfFibLocNeZero
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.ExistsExactLift
public import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.RedEqOfSubMem

@[expose] public section

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocFEqLocFAdjoinCut
open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinC

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

private theorem VecSplit_adjoin_le_locF_of_le_locF (S : VecSplit h h') {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime)
    {T T' : Submodule (𝓞 K) V'} (hT : T ≤ locF 𝔭 T') :
    S.adjoin T ≤ locF 𝔭 (S.adjoin T') := by
  refine sup_le ?_ ?_
  · rw [Submodule.span_singleton_le_iff_mem]
    exact LocF.le_locF 𝔭 _ (S.x₀_mem_adjoin T')
  · rw [Submodule.map_le_iff_le_comap]
    intro a ha
    obtain ⟨t, ht, hta⟩ := (LocF.mem_locF_iff h𝔭 T' a).mp (hT ha)
    rw [Submodule.mem_comap, LocF.mem_locF_iff h𝔭]
    refine ⟨t, ht, ?_⟩
    rw [← map_smul]
    exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hta)

theorem locF_adjoin_congr (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {T T' : Submodule (𝓞 K) V'} (e : locF 𝔭 T = locF 𝔭 T') :
    locF 𝔭 (S.adjoin T) = locF 𝔭 (S.adjoin T') := by
  have key : ∀ {A B : Submodule (𝓞 K) V'}, locF 𝔭 A = locF 𝔭 B →
      locF 𝔭 (S.adjoin A) ≤ locF 𝔭 (S.adjoin B) := by
    intro A B hAB
    have hle := VecSplit_adjoin_le_locF_of_le_locF S h𝔭.isPrime ((LocF.le_locF 𝔭 A).trans hAB.le)
    calc locF 𝔭 (S.adjoin A) ≤ locF 𝔭 (locF 𝔭 (S.adjoin B)) := LocF.locF_mono 𝔭 hle
      _ = locF 𝔭 (S.adjoin B) := LocF.locF_idem 𝔭 _
  exact le_antisymm (key e) (key e.symm)

theorem vd_eq_of_basis (hF : IsFixF K F) (h : V →ₗ⋆[K] V →ₗ[K] K) {L : Submodule (𝓞 K) V}
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {m : ℕ} (hm : finrank K V = m) (b : Basis (Fin m) K V)
    (hb : locF 𝔭 (Submodule.span (𝓞 K) (Set.range b)) = locF 𝔭 L) {g₀ : 𝓞 K}
    (hg : algebraMap (𝓞 K) K g₀ = (Matrix.of fun i j => h (b i) (b j)).det) :
    vd h L 𝔭 = sSup {e : ℕ | g₀ ∈ extP K 𝔭 ^ e} := by
  subst hm
  rw [← localizedQuotients.vd_locF hF h L h𝔭, ← hb, localizedQuotients.vd_locF hF h _ h𝔭, vd, BallB.discrIdeal_span b hg]
  simp only [Ideal.span_singleton_le_iff_mem]

theorem span_range_cons (S : VecSplit h h') {n : ℕ} (x : Fin n → V') :
    Submodule.span (𝓞 K) (Set.range (Fin.cons S.x₀ (fun i => S.ι (x i)) : Fin (n + 1) → V)) =
      S.adjoin (Submodule.span (𝓞 K) (Set.range x)) := by
  rw [Fin.range_cons, Submodule.span_insert, VecSplit.adjoin, Submodule.map_span, ← Set.range_comp]
  rfl

theorem vd_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : vd h' (S.cut L) 𝔭 = vd h L 𝔭 := by
  have hcL := StabilizerLattices.isFullLattice_cut S hL
  obtain ⟨b', hb'L, hb'⟩ := LocalSpans.exists_basis_locF hcL h𝔭
  have hint : ∀ i j, h' (b' i) (b' j) ∈ (1 : Submodule (𝓞 K) K) := fun i j =>
    UnimodularLocalization.isIntegralLat_cut S hLi _ (hb'L i) _ (hb'L j)
  choose H hH using fun i j => Submodule.mem_one.mp (hint i j)
  have hg₀ : algebraMap (𝓞 K) K (Matrix.of H).det =
      (Matrix.of fun i j => h' (b' i) (b' j)).det := by
    rw [RingHom.map_det]
    congr 1
    ext i j
    simp [hH]
  let c : Fin (finrank K V' + 1) → V := Fin.cons S.x₀ (fun i => S.ι (b' i))
  have hli : LinearIndependent K c := by
    refine linearIndependent_finCons.mpr ⟨?_, ?_⟩
    · exact b'.linearIndependent.map' S.ι (LinearMap.ker_eq_bot.mpr S.inj)
    · intro hmem
      have hle : Submodule.span K (Set.range fun i => S.ι (b' i)) ≤ LinearMap.range S.ι :=
        Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact ⟨b' i, rfl⟩)
      obtain ⟨a, ha⟩ := hle hmem
      exact S.x₀_not_mem_range a ha
  have hcard : Fintype.card (Fin (finrank K V' + 1)) = finrank K V := by
    rw [Fintype.card_fin]
    exact S.finrank_add_one
  let bb := basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hbb : ⇑bb = c := coe_basisOfLinearIndependentOfCardEqFinrank hli hcard
  have hgram : (Matrix.of fun i j => h (bb i) (bb j)).det =
      (Matrix.of fun i j => h' (b' i) (b' j)).det := by
    rw [hbb, Matrix.det_succ_row_zero, Fin.sum_univ_succ]
    simp [c, S.orth, h1, Fin.succAbove_zero]
    congr 1
    ext i j
    simp [S.isom]
  have hspan : locF 𝔭 (Submodule.span (𝓞 K) (Set.range bb)) = locF 𝔭 L := by
    rw [hbb, span_range_cons S b', locF_adjoin_congr hK hF S h𝔭 hb', S.adjoin_cut h1 hLi hx]
  rw [vd_eq_of_basis hF h h𝔭 S.finrank_add_one.symm bb hspan (hg₀.trans hgram.symm),
    vd_eq_of_basis hF h' h𝔭 rfl b' hb' hg₀]

theorem locF_eq_locF_adjoin_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (S : VecSplit h h')
    (h1 : h S.x₀ S.x₀ = 1) {B : Submodule (𝓞 K) V} (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hx : S.x₀ ∈ locF 𝔭 B) :
    locF 𝔭 B = locF 𝔭 (S.adjoin (S.cut B)) := by
  obtain ⟨P, hP, rfl⟩ := LocalizedFibreSets.exists_max_over (K := K) h𝔭
  simp only [locF_eq_loc hK hF hP] at hx ⊢
  refine UnimodularLocalization.loc_eq_loc_adjoin_cut S hP.isPrime hBi hx ?_
  rw [h1, inv_one]
  exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.mem_one.mpr ⟨1, map_one _⟩⟩

theorem vd_cut_of_mem_locF (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {B : Submodule (𝓞 K) V}
    (hB : Submodule.IsFullLattice K B) (hBi : Formalism.HermitianLatticesTheory.IsIntegralLat h B)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hx : S.x₀ ∈ locF 𝔭 B) :
    vd h' (S.cut B) 𝔭 = vd h B 𝔭 := by
  have e5 := locF_eq_locF_adjoin_cut hK hF S h1 hBi h𝔭 hx
  have hcB := StabilizerLattices.isFullLattice_cut S hB
  have hBA : Submodule.IsFullLattice K (S.adjoin (S.cut B)) := by
    refine { toIsLattice := (S.isLattice_adjoin_iff _).mpr hcB.toIsLattice, span_eq_top := ?_ }
    rw [eq_top_iff]
    intro v _
    obtain ⟨c, a, rfl⟩ := S.cover v
    refine add_mem (Submodule.smul_mem _ c (Submodule.subset_span (S.x₀_mem_adjoin _))) ?_
    have ha : a ∈ Submodule.span K (S.cut B : Set V') := by
      rw [hcB.span_eq_top]
      exact Submodule.mem_top
    have hle : Submodule.map S.ι (Submodule.span K (S.cut B : Set V')) ≤
        Submodule.span K (S.adjoin (S.cut B) : Set V) := by
      rw [Submodule.map_span]
      apply Submodule.span_mono
      rintro _ ⟨b, hb, rfl⟩
      exact Submodule.mem_sup_right (Submodule.mem_map_of_mem hb)
    exact hle (Submodule.mem_map_of_mem ha)
  have hcBi := UnimodularLocalization.isIntegralLat_cut S hBi
  calc vd h' (S.cut B) 𝔭 = vd h (S.adjoin (S.cut B)) 𝔭 := by
        rw [← vd_cut hK hF hs hd S h1 hBA
          ((S.isIntegralLat_adjoin_iff hs h1 _).mpr hcBi) (S.x₀_mem_adjoin _) h𝔭, S.cut_adjoin]
    _ = vd h B 𝔭 := by rw [← localizedQuotients.vd_locF hF h _ h𝔭, ← e5, localizedQuotients.vd_locF hF h _ h𝔭]

theorem exists_isom_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    (hxg : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) :
    ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap g' (locF 𝔭 (S.cut L)) = S.cut (Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L)) ∧
      Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (locF 𝔭 L) = Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) := by
  have hML : Submodule.IsFullLattice K (Formalism.HermitianLatticesTheory.gmap g L) := by
    refine { toIsLattice := LocalizedFibreSets.isLattice_gmap g hL, span_eq_top := ?_ }
    change Submodule.span K ((g : V →ₗ[K] V) '' (L : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact g.surjective
  have hMi : Formalism.HermitianLatticesTheory.IsIntegralLat h (Formalism.HermitianLatticesTheory.gmap g L) := UnimodularLocalization.isIntegralLat_gmap hg hLi
  have hxM : S.x₀ ∈ locF 𝔭 (Formalism.HermitianLatticesTheory.gmap g L) := by rwa [← LocalizedFibreSets.gmap_locF]
  have hxL : S.x₀ ∈ locF 𝔭 L := LocF.le_locF 𝔭 L hx
  have hvA : vd h' (S.cut L) 𝔭 = vd h L 𝔭 := vd_cut hK hF hs hd S h1 hL hLi hx h𝔭
  have hvB : vd h' (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) 𝔭 = vd h L 𝔭 := by
    rw [vd_cut_of_mem_locF hK hF hs hd S h1 hML hMi h𝔭 hxM, UnimodularLocalization.vd_gmap hg]
  have hA := StabilizerLattices.isFullLattice_cut S hL
  have hB := StabilizerLattices.isFullLattice_cut S hML
  have hAi := UnimodularLocalization.isIntegralLat_cut S hLi
  have hBi := UnimodularLocalization.isIntegralLat_cut S hMi
  have hs' : h'.IsSymm := S.isSymm hs
  have hd' : IsTotPosDef h' := S.isTotPosDef hd
  obtain ⟨g', hg', hg'e⟩ : ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h',
      Formalism.HermitianLatticesTheory.gmap g' (locF 𝔭 (S.cut L)) = locF 𝔭 (S.cut (Formalism.HermitianLatticesTheory.gmap g L)) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hv with h0 | h0
    · exact exists_isom_locF_of_vd_zero hK hF hs' hd' hA hB hAi hBi h𝔭 (hvA.trans h0)
        (hvB.trans h0)
    · exact exists_isom_locF_of_vd_one hK hF hs' hd' hA hB hAi hBi h𝔭 (hvA.trans h0)
        (hvB.trans h0)
  refine ⟨g', hg', ?_, ?_⟩
  · rw [hg'e, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF]
  · rw [LocalizedFibreSets.gmap_locF g 𝔭 L, locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭 hxL, LocalizedFibreSets.gmap_locF,
      SplitBAux.gmap_extOf S g' rfl, locF_eq_locF_adjoin_cut hK hF S h1 hMi h𝔭 hxM]
    exact locF_adjoin_congr hK hF S h𝔭 (by rw [← LocalizedFibreSets.gmap_locF]; exact hg'e)

theorem fibLoc_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) : fibLoc S L 𝔭 (locF 𝔭 (S.cut L)) = 1 := by
  have hxL : S.x₀ ∈ locF 𝔭 L := LocF.le_locF 𝔭 L hx
  rw [fibLoc, Nat.card_eq_one_iff_exists]
  refine ⟨⟨locF 𝔭 L, LocF.locF_idem 𝔭 L, ⟨1, one_mem _, autSub_gmap_one _⟩, hxL,
    by rw [LocalizedFibreSets.cut_locF, LocF.locF_idem]⟩, ?_⟩
  rintro ⟨Λ, -, ⟨g, hg, rfl⟩, hΛx, hΛc⟩
  apply Subtype.ext
  show Formalism.HermitianLatticesTheory.gmap g (locF 𝔭 L) = locF 𝔭 L
  have hMi := UnimodularLocalization.isIntegralLat_gmap hg hLi
  rw [LocalizedFibreSets.gmap_locF] at hΛx hΛc ⊢
  rw [locF_eq_locF_adjoin_cut hK hF S h1 hMi h𝔭 hΛx,
    locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭 hxL]
  apply locF_adjoin_congr hK hF S h𝔭
  rw [← LocalizedFibreSets.cut_locF, hΛc, LocF.locF_idem]

theorem isLocReps_cut (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) : IsLocReps S L 𝔭 {locF 𝔭 (S.cut L)} := by
  have hcLi := UnimodularLocalization.isIntegralLat_cut S hLi
  refine ⟨?_, ?_⟩
  · intro T hT
    rw [Finset.mem_singleton] at hT
    subst hT
    refine ⟨LocF.locF_idem 𝔭 _, GoodPrimeTerms.isIntegralAt_locF h𝔭.isPrime hF hcLi, ?_⟩
    rw [fibLoc_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv]
    exact one_ne_zero
  · intro T hT _ hf
    refine ⟨locF 𝔭 (S.cut L), ⟨Finset.mem_singleton_self _, ?_⟩, ?_⟩
    · obtain ⟨g, hg, hgx, hgT⟩ := UnimodularLocalization.exists_of_fibLoc_ne_zero S hf
      rw [← LocalizedFibreSets.gmap_locF] at hgx
      obtain ⟨g', hg', he, -⟩ := exists_isom_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv hg hgx
      refine ⟨g', hg', ?_⟩
      rw [he, LocalizedFibreSets.gmap_locF, LocalizedFibreSets.cut_locF, hgT, hT]
    · rintro T₀ ⟨hT₀, -⟩
      exact Finset.mem_singleton.mp hT₀

theorem exists_aut_map (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) {y : V} (hy : y ∈ locF 𝔭 L) (hyy : h y y = 1) :
    ∃ g ∈ autSub h (locF 𝔭 L), g S.x₀ = y := by
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hyy
  obtain ⟨g₁, hg₁, hg₁y⟩ := exists_isom_map_of_eq hK hs hd hy0 (hyy.trans h1.symm)
  have hxg : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L) := by
    rw [← hg₁y]
    exact Submodule.mem_map_of_mem hy
  obtain ⟨g', hg', -, he⟩ := exists_isom_cut hK hF hs hd S h1 hL hLi hx h𝔭 hv hg₁ hxg
  refine ⟨g₁⁻¹ * SplitBAux.extOf S g', ⟨mul_mem (inv_mem hg₁) (SplitBAux.extOf_mem_isom hs S hg'), ?_⟩, ?_⟩
  · rw [autSub_gmap_mul, he, ← autSub_gmap_mul, inv_mul_cancel, autSub_gmap_one]
  · show g₁⁻¹ (SplitBAux.extOf S g' S.x₀) = y
    rw [SplitBAux.extOf_x₀, ← hg₁y]
    exact g₁.symm_apply_apply y

end Formalism.HermitianLattices.Ext.L3.PinC
end
end

section -- merged from Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.EqBlockOfFix
open Matrix

namespace Formalism.HermitianLattices.Ext.L3.PinE

variable {A : Type*} [CommRing A] [StarRing A] {κ : Type} [Fintype κ] [DecidableEq κ]

def e₀ : Unit ⊕ κ → A := Pi.single (Sum.inl ()) 1

def HH (H' : Matrix κ κ A) : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A := fromBlocks 1 0 0 H'

theorem form_block (H' X' : Matrix κ κ A) :
    (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A)ᴴ * HH H' * fromBlocks 1 0 0 X' =
      fromBlocks 1 0 0 (X'ᴴ * H' * X') := by
  simp [HH, fromBlocks_conjTranspose, fromBlocks_multiply]

theorem block_mulVec_e₀ (X' : Matrix κ κ A) :
    (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) *ᵥ e₀ = e₀ := by
  unfold e₀
  rw [mulVec_single_one]
  ext i
  rcases i with ⟨⟩ | i <;> simp

theorem eq_block_of_fix {H' : Matrix κ κ A} {Y : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A}
    (hY : Yᴴ * HH H' * Y = HH H') (h0 : Y *ᵥ e₀ = e₀) :
    Y.toBlocks₂₂ᴴ * H' * Y.toBlocks₂₂ = H' ∧ Y = fromBlocks 1 0 0 Y.toBlocks₂₂ := by
  have h11 : Y (Sum.inl ()) (Sum.inl ()) = 1 := by
    have := congrFun h0 (Sum.inl ())
    simpa [e₀, mulVec_single_one] using this
  have h21 : ∀ i, Y (Sum.inr i) (Sum.inl ()) = 0 := by
    intro i
    have := congrFun h0 (Sum.inr i)
    simpa [e₀, mulVec_single_one] using this
  have hA : Y.toBlocks₁₁ = 1 := by
    ext ⟨⟩ ⟨⟩
    simpa [toBlocks₁₁] using h11
  have hC : Y.toBlocks₂₁ = 0 := by
    ext i ⟨⟩
    simpa [toBlocks₂₁] using h21 i
  have hYb : Y = fromBlocks 1 Y.toBlocks₁₂ 0 Y.toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks Y]
    rw [hA, hC]
  rw [hYb] at hY
  have key := congrArg Matrix.toBlocks₁₂ hY
  have key2 := congrArg Matrix.toBlocks₂₂ hY
  simp [HH, fromBlocks_conjTranspose, fromBlocks_multiply] at key key2
  refine ⟨?_, ?_⟩
  · simpa [key] using key2
  · rw [key] at hYb
    exact hYb

theorem form_col {H X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A} (hX : Xᴴ * H * X = H)
    (h00 : H (Sum.inl ()) (Sum.inl ()) = 1) : star (X *ᵥ e₀) ⬝ᵥ (H *ᵥ (X *ᵥ e₀)) = 1 := by
  rw [star_mulVec, ← dotProduct_mulVec, mulVec_mulVec, mulVec_mulVec, hX]
  simp [e₀, mulVec_single_one, dotProduct, Fintype.sum_sum_type, h00]

theorem card_split [Finite A] (H' : Matrix κ κ A)
    (htr : ∀ x : Unit ⊕ κ → A, star x ⬝ᵥ (HH H' *ᵥ x) = 1 →
      ∃ G G' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A, Gᴴ * HH H' * G = HH H' ∧ G * G' = 1 ∧ G *ᵥ e₀ = x) :
    Nat.card {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} =
      Nat.card {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} *
        Nat.card {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'} := by
  classical
  choose G G' hG using htr
  have h00 : HH H' (Sum.inl ()) (Sum.inl ()) = (1 : A) := by simp [HH]
  have hinv : ∀ x hx, G' x hx * G x hx = 1 := fun x hx => by
    first
      | exact mul_eq_one_comm.mp (hG x hx).2.1
      | exact Matrix.mul_eq_one_comm_of_equiv (Equiv.refl _) (hG x hx).2.1
      | exact (Matrix.mul_eq_one_comm (M := G x hx) (N := G' x hx)).mp (hG x hx).2.1
  have hG'form : ∀ x hx, (G' x hx)ᴴ * HH H' * G' x hx = HH H' := by
    intro x hx
    calc (G' x hx)ᴴ * HH H' * G' x hx = (G' x hx)ᴴ * ((G x hx)ᴴ * HH H' * G x hx) * G' x hx := by
          rw [(hG x hx).1]
      _ = (G x hx * G' x hx)ᴴ * HH H' * (G x hx * G' x hx) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = HH H' := by rw [(hG x hx).2.1, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  have hGeq : ∀ x y (hx : star x ⬝ᵥ (HH H' *ᵥ x) = 1) (hy : star y ⬝ᵥ (HH H' *ᵥ y) = 1), x = y →
      G x hx = G y hy ∧ G' x hx = G' y hy := by
    rintro x _ hx hy rfl
    exact ⟨rfl, rfl⟩
  have fixY : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'),
      (G' (X *ᵥ e₀) (form_col hX h00) * X)ᴴ * HH H' * (G' (X *ᵥ e₀) (form_col hX h00) * X) = HH H' ∧
      (G' (X *ᵥ e₀) (form_col hX h00) * X) *ᵥ e₀ = e₀ := by
    intro X hX
    constructor
    · calc _ = Xᴴ * ((G' (X *ᵥ e₀) (form_col hX h00))ᴴ * HH H' * G' (X *ᵥ e₀) (form_col hX h00)) * X := by
            simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = HH H' := by rw [hG'form, hX]
    · have h1 : G' (X *ᵥ e₀) (form_col hX h00) *ᵥ (G (X *ᵥ e₀) (form_col hX h00) *ᵥ e₀) = e₀ := by
        rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
      rw [(hG _ _).2.2] at h1
      rw [← Matrix.mulVec_mulVec]
      exact h1
  have recon : ∀ (X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A) (hX : Xᴴ * HH H' * X = HH H'),
      X = G (X *ᵥ e₀) (form_col hX h00) *
        fromBlocks 1 0 0 (G' (X *ᵥ e₀) (form_col hX h00) * X).toBlocks₂₂ := by
    intro X hX
    rw [← (eq_block_of_fix (fixY X hX).1 (fixY X hX).2).2, ← Matrix.mul_assoc, (hG _ _).2.1,
      Matrix.one_mul]
  let f : {X : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A // Xᴴ * HH H' * X = HH H'} →
      {x : Unit ⊕ κ → A // star x ⬝ᵥ (HH H' *ᵥ x) = 1} × {X' : Matrix κ κ A // X'ᴴ * H' * X' = H'} :=
    fun X => (⟨X.1 *ᵥ e₀, form_col X.2 h00⟩,
      ⟨_, (eq_block_of_fix (fixY X.1 X.2).1 (fixY X.1 X.2).2).1⟩)
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨X1, hX1⟩ ⟨X2, hX2⟩ h
      simp only [f, Prod.mk.injEq, Subtype.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      obtain ⟨hGG, hGG'⟩ := hGeq _ _ (form_col hX1 h00) (form_col hX2 h00) h1
      apply Subtype.ext
      dsimp only
      rw [recon X1 hX1, recon X2 hX2, hGG, h2]
    · rintro ⟨⟨x, hx⟩, ⟨X', hX'⟩⟩
      have hform : (G x hx * fromBlocks 1 0 0 X')ᴴ * HH H' * (G x hx * fromBlocks 1 0 0 X') = HH H' := by
        calc _ = (fromBlocks 1 0 0 X' : Matrix (Unit ⊕ κ) (Unit ⊕ κ) A)ᴴ * ((G x hx)ᴴ * HH H' * G x hx) *
              fromBlocks 1 0 0 X' := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
          _ = HH H' := by rw [(hG x hx).1, form_block, hX']; rfl
      have hxe : (G x hx * fromBlocks 1 0 0 X') *ᵥ e₀ = x := by
        rw [← Matrix.mulVec_mulVec, block_mulVec_e₀, (hG x hx).2.2]
      refine ⟨⟨_, hform⟩, ?_⟩
      simp only [f]
      obtain ⟨_, hGG'⟩ := hGeq _ _ (form_col hform h00) hx hxe
      refine Prod.ext (Subtype.ext hxe) (Subtype.ext ?_)
      dsimp only
      rw [hGG', ← Matrix.mul_assoc, hinv, Matrix.one_mul, Matrix.toBlocks_fromBlocks₂₂]
  rw [← Nat.card_prod]
  exact Nat.card_congr (Equiv.ofBijective f hf)

end Formalism.HermitianLattices.Ext.L3.PinE
end

open NumberField Module Matrix

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.PinB

open idealPowerSpanBounds integralBasisSpans

variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}


omit [NumberField K] [FiniteDimensional K V] [FiniteDimensional K V'] in
def prodEquiv (S : VecSplit h h') : (K × V') ≃ₗ[K] V :=
  LinearEquiv.ofBijective ((LinearMap.toSpanSingleton K V S.x₀).coprod S.ι) (by
    constructor
    · rintro ⟨c, a⟩ ⟨c', a'⟩ e
      simp only [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply] at e
      obtain ⟨rfl, rfl⟩ := S.comb_eq_iff.1 e
      rfl
    · intro v
      obtain ⟨c, a, rfl⟩ := S.cover v
      exact ⟨(c, a), by simp only [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]⟩)

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem prodEquiv_apply (S : VecSplit h h') (c : K) (a : V') :
    prodEquiv S (c, a) = c • S.x₀ + S.ι a := by
  show (LinearMap.toSpanSingleton K V S.x₀).coprod S.ι (c, a) = _
  rw [LinearMap.coprod_apply, LinearMap.toSpanSingleton_apply]

def consBasis (S : VecSplit h h') {κ : Type} (b' : Basis κ K V') : Basis (Unit ⊕ κ) K V :=
  ((Basis.singleton Unit K).prod b').map (prodEquiv S)

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem consBasis_inl (S : VecSplit h h') {κ : Type} (b' : Basis κ K V') (u : Unit) :
    consBasis S b' (Sum.inl u) = S.x₀ := by
  simp [consBasis, prodEquiv_apply]

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem consBasis_inr (S : VecSplit h h') {κ : Type} (b' : Basis κ K V') (i : κ) :
    consBasis S b' (Sum.inr i) = S.ι (b' i) := by
  simp [consBasis, prodEquiv_apply]

omit [FiniteDimensional K V] [FiniteDimensional K V'] in
theorem locF_span_consBasis (S : VecSplit h h') {κ : Type} (b' : Basis κ K V')
    {T : Submodule (𝓞 K) V'} (hbT : ∀ i, b' i ∈ T) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hb' : locF 𝔭 (spanO b') = locF 𝔭 T) :
    locF 𝔭 (spanO (consBasis S b')) = locF 𝔭 (S.adjoin T) := by
  have key : ∀ {A B : Submodule (𝓞 K) V}, A ≤ locF 𝔭 B → B ≤ locF 𝔭 A →
      locF 𝔭 A = locF 𝔭 B := by
    intro A B hAB hBA
    apply le_antisymm
    · exact (Formalism.HermitianLatticesTheory.genusCovol_locS_mono _ hAB).trans (Formalism.HermitianLatticesTheory.genusCovol_locS_idem _ _)
    · exact (Formalism.HermitianLatticesTheory.genusCovol_locS_mono _ hBA).trans (Formalism.HermitianLatticesTheory.genusCovol_locS_idem _ _)
  unfold VecSplit.adjoin
  apply key
  · refine le_trans ?_ (Formalism.HermitianLatticesTheory.genusCovol_le_locS _ _)
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rcases j with u | i
    · rw [consBasis_inl]
      exact Submodule.mem_sup_left (Submodule.subset_span (Set.mem_singleton _))
    · rw [consBasis_inr]
      exact Submodule.mem_sup_right ⟨b' i, hbT i, rfl⟩
  · apply sup_le
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      apply Formalism.HermitianLatticesTheory.genusCovol_le_locS
      rw [← consBasis_inl S b' ()]
      exact Submodule.subset_span ⟨Sum.inl (), rfl⟩
    · rintro _ ⟨t, ht, rfl⟩
      have ht' : t ∈ locF 𝔭 (spanO b') := by
        rw [hb']
        exact Formalism.HermitianLatticesTheory.genusCovol_le_locS _ _ ht
      obtain ⟨s, hs, hst⟩ := (Formalism.HermitianLatticesTheory.genusCovol_mem_locS _ _ _).1 ht'
      have hmap : ∀ y ∈ spanO b', S.ι y ∈ spanO (consBasis S b') := by
        intro y hy
        refine Submodule.span_induction (p := fun y _ => S.ι y ∈ spanO (consBasis S b'))
          ?_ ?_ ?_ ?_ hy
        · rintro _ ⟨i, rfl⟩
          rw [← consBasis_inr S b' i]
          exact Submodule.subset_span ⟨Sum.inr i, rfl⟩
        · simp
        · intro x y _ _ hx hy
          rw [map_add (f := _)]
          exact Submodule.add_mem _ hx hy
        · intro a x _ hx
          have e : S.ι (a • x) = a • S.ι x := (S.ι.restrictScalars (𝓞 K)).map_smul a x
          rw [e]
          exact Submodule.smul_mem _ a hx
      refine (Formalism.HermitianLatticesTheory.genusCovol_mem_locS _ _ _).2 ⟨s, hs, ?_⟩
      have e : S.ι (s • t) = s • S.ι t := (S.ι.restrictScalars (𝓞 K)).map_smul s t
      have := hmap _ hst
      rw [e] at this
      exact this

theorem akCount_split (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') (h1 : h S.x₀ S.x₀ = 1) {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsFullLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) (hx : S.x₀ ∈ L)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (hv : vd h L 𝔭 ≤ 1) {k : ℕ} (hk : 1 ≤ k) :
    akCount h L 𝔭 k = nkCount h L 𝔭 k 1 * akCount h' (S.cut L) 𝔭 k := by
  classical
  haveI : 𝔭.IsPrime := h𝔭.isPrime
  haveI : Fact (IsFixF K F) := ⟨hF⟩

  obtain ⟨π, hπ⟩ : ∃ π : V →ₗ[K] V', ∀ v, π v = ((prodEquiv S).symm v).2 :=
    ⟨(LinearMap.snd K K V') ∘ₗ (prodEquiv S).symm.toLinearMap, fun v => rfl⟩
  have hdec : ∀ v : V, v = h S.x₀ v • S.x₀ + S.ι (π v) := by
    intro v
    obtain ⟨c, a, hv⟩ : ∃ c a, (prodEquiv S).symm v = (c, a) := ⟨_, _, rfl⟩
    have hv' : v = c • S.x₀ + S.ι a := by
      rw [← prodEquiv_apply, ← hv, LinearEquiv.apply_symm_apply]
    have hc : h S.x₀ v = c := by
      rw [hv', map_add (f := _), map_smul, h1, S.orth]
      simp
    have ha : π v = a := by rw [hπ, hv]
    rw [hc, ha]
    exact hv'
  have hπι : ∀ a, π (S.ι a) = a := by
    intro a
    have e := hdec (S.ι a)
    rw [S.orth, zero_smul, zero_add] at e
    exact (S.inj e).symm
  have hcutEq : S.cut L = L.map (π.restrictScalars (𝓞 K)) := by
    ext a
    constructor
    · intro ha
      exact ⟨S.ι a, ha, hπι a⟩
    · rintro ⟨v, hv, rfl⟩
      show S.ι (π v) ∈ L
      obtain ⟨c, hc⟩ := Submodule.mem_one.1 (hLi _ hx _ hv)
      have e : S.ι (π v) = v - h S.x₀ v • S.x₀ := by
        rw [eq_sub_iff_add_eq, add_comm]
        exact (hdec v).symm
      rw [e, ← hc, algebraMap_smul]
      exact L.sub_mem hv (L.smul_mem c hx)
  have hcutL : Submodule.IsFullLattice K (S.cut L) := by
    rw [hcutEq]
    refine { toIsLattice := Submodule.IsLattice.of_fg K (hL.fg.map _), span_eq_top := ?_ }
    rw [Submodule.map_coe]
    change Submodule.span K (π '' (L : Set V)) = ⊤
    rw [Submodule.span_image, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact fun a => ⟨S.ι a, hπι a⟩

  obtain ⟨b', hb'L, hb'⟩ := Formalism.HermitianLattices.Ext.L3.LocalSpans.exists_basis_locF hcutL h𝔭
  have hm : ∀ i, S.ι (b' i) ∈ L := hb'L
  have hH'ex : ∀ i j, ∃ z : 𝓞 K, algebraMap (𝓞 K) K z = h' (b' i) (b' j) := by
    intro i j
    have e := hLi _ (hm i) _ (hm j)
    rw [S.isom] at e
    exact Submodule.mem_one.1 e
  obtain ⟨H', hH'⟩ : ∃ H' : Matrix (Fin (finrank K V')) (Fin (finrank K V')) (𝓞 K),
      ∀ i j, algebraMap (𝓞 K) K (H' i j) = h' (b' i) (b' j) :=
    ⟨Matrix.of fun i j => (hH'ex i j).choose, fun i j => (hH'ex i j).choose_spec⟩
  set bb := consBasis S b' with hbbdef
  have hbb : locF 𝔭 (spanO bb) = locF 𝔭 L :=
    (locF_span_consBasis S b' hb'L h𝔭 hb').trans
      (Formalism.HermitianLattices.Ext.L3.PinC.locF_eq_locF_adjoin_cut hK hF S h1 hLi h𝔭
        (Formalism.HermitianLattices.Ext.L3.LocF.le_locF 𝔭 L hx)).symm
  have hbbL : ∀ p, bb p ∈ L := by
    rintro (u | i)
    · rw [hbbdef, consBasis_inl]; exact hx
    · rw [hbbdef, consBasis_inr]; exact hm i
  have hHH : ∀ p q, algebraMap (𝓞 K) K (Formalism.HermitianLattices.Ext.L3.PinE.HH H' p q) = h (bb p) (bb q) := by
    rintro (u | i) (u' | j)
    · rw [hbbdef]
      simp only [consBasis_inl]
      rw [h1]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH]
    · rw [hbbdef]
      simp only [consBasis_inl, consBasis_inr]
      rw [S.orth]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH]
    · rw [hbbdef]
      simp only [consBasis_inl, consBasis_inr]
      have e : starRingEnd K (h S.x₀ (S.ι (b' i))) = h (S.ι (b' i)) S.x₀ := by
        first
          | exact hs S.x₀ (S.ι (b' i))
          | exact hs.eq S.x₀ (S.ι (b' i))
      rw [← e, S.orth]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH]
    · rw [hbbdef]
      simp only [consBasis_inr]
      rw [S.isom]
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH, hH']
  have hmapHH : (Formalism.HermitianLattices.Ext.L3.PinE.HH H').map (Ideal.Quotient.mk (extP K 𝔭 ^ k)) =
      Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) := by
    ext p q
    rcases p with u | i <;> rcases q with u' | j <;>
      simp [Formalism.HermitianLattices.Ext.L3.PinE.HH, Matrix.one_apply]

  have htr : ∀ x : Unit ⊕ Fin (finrank K V') → 𝓞 K ⧸ extP K 𝔭 ^ k,
      star x ⬝ᵥ (Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) *ᵥ x) = 1 →
      ∃ G G' : Matrix (Unit ⊕ Fin (finrank K V')) (Unit ⊕ Fin (finrank K V')) (𝓞 K ⧸ extP K 𝔭 ^ k),
        Gᴴ * Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) * G =
          Formalism.HermitianLattices.Ext.L3.PinE.HH (H'.map (Ideal.Quotient.mk (extP K 𝔭 ^ k))) ∧
        G * G' = 1 ∧ G *ᵥ Formalism.HermitianLattices.Ext.L3.PinE.e₀ = x := by
    intro x hx1
    obtain ⟨c, hc⟩ : ∃ c : Unit ⊕ Fin (finrank K V') → 𝓞 K,
        ∀ p, Ideal.Quotient.mk (extP K 𝔭 ^ k) (c p) = x p :=
      ⟨fun p => (Ideal.Quotient.mk_surjective (x p)).choose,
        fun p => (Ideal.Quotient.mk_surjective (x p)).choose_spec⟩
    set w : ↥(locF 𝔭 (spanO bb)) := ∑ p, c p • Formalism.HermitianLattices.Ext.L3.PinG.bM bb 𝔭 p with hwdef
    have hred : Formalism.HermitianLattices.Ext.L3.PinG.red bb h𝔭 k w = x := by
      funext q
      set_option synthInstance.maxHeartbeats 100000 in
        simp [hwdef, map_sum, map_smul, Formalism.HermitianLattices.Ext.L3.PinG.red_bM, Pi.single_apply, hc,
        Algebra.smul_def, Ideal.Quotient.algebraMap_eq]
      rcases q with ⟨⟩ | i <;> simp
    have hwL : (w : V) ∈ L := by
      rw [hwdef, Submodule.coe_sum]
      exact Submodule.sum_mem _ (fun p _ => by
        rw [Submodule.coe_smul]
        exact Submodule.smul_mem _ _ (hbbL p))
    obtain ⟨z, hz⟩ := Submodule.mem_one.1 (hLi _ hwL _ hwL)
    have hform := Formalism.HermitianLattices.Ext.L3.PinG.red_form h bb hHH h𝔭 k w w hz.symm
    rw [hred, hmapHH, hx1] at hform
    have hcong : CongrP 𝔭 k (h (w : V) (w : V)) 1 := by
      have e := (Formalism.HermitianLattices.Ext.L3.integralBasisSpans.congrP_int h𝔭 k z 1).2 (by rw [map_one]; exact hform.symm)
      rwa [map_one, hz] at e
    obtain ⟨z', hz'L, hz'1, hz'd⟩ :=
      Formalism.HermitianLattices.Ext.L3.PinF.exists_exact_lift hK hF hs hd (by first | exact hL | exact hL.toIsLattice) hLi h𝔭 h1 hk hwL hcong
    obtain ⟨g, hg, hgx⟩ :=
      Formalism.HermitianLattices.Ext.L3.PinC.exists_aut_map hK hF hs hd S h1 hL hLi hx h𝔭 hv hz'L hz'1
    rw [← hbb] at hg
    obtain ⟨G, G', hGf, hGG, hGred⟩ := Formalism.HermitianLattices.Ext.L3.PinG.exists_matrix h bb hHH h𝔭 k hg
    refine ⟨G, G', by rw [← hmapHH]; exact hGf, hGG, ?_⟩
    have hz'm : z' ∈ locF 𝔭 (spanO bb) := by rw [hbb]; exact hz'L
    have e1 := hGred (Formalism.HermitianLattices.Ext.L3.PinG.bM bb 𝔭 (Sum.inl ())) ⟨z', hz'm⟩ (by
      show z' = g (bb (Sum.inl ()))
      rw [hbbdef, consBasis_inl, hgx])
    rw [Formalism.HermitianLattices.Ext.L3.PinG.red_bM] at e1
    have e2 : Formalism.HermitianLattices.Ext.L3.PinG.red bb h𝔭 k ⟨z', hz'm⟩ = Formalism.HermitianLattices.Ext.L3.PinG.red bb h𝔭 k w :=
      Formalism.HermitianLattices.Ext.L3.PinG.red_eq_of_sub_mem bb h𝔭 k _ _ (by
        have e := hz'd
        rw [← hbb] at e
        exact e)
    rw [← hred, ← e2, e1]
    rfl
  haveI : Finite (𝓞 K ⧸ extP K 𝔭 ^ k) := Formalism.HermitianLattices.Ext.L3.idealPowerSpanBounds.finite_quot (K := K) h𝔭 k
  rw [Formalism.HermitianLattices.Ext.L3.integralBasisSpans.akCount_eq h h𝔭 bb hbb hHH k, hmapHH,
    Formalism.HermitianLattices.Ext.L3.PinE.card_split _ htr,
    Formalism.HermitianLattices.Ext.L3.integralBasisSpans.nkCount_eq h h𝔭 bb hbb hHH k 1, hmapHH,
    Formalism.HermitianLattices.Ext.L3.integralBasisSpans.akCount_eq h' h𝔭 b' hb' hH' k]
  simp

end Formalism.HermitianLattices.Ext.L3.PinB
