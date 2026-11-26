module

public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HomExtensionSemiAbelianDiscreteValuationRing
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IntegralLatticeStructureUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfSurjective
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory.DivisiblePart

open RationalPoint

theorem surjective_of_rationalPoints {k : Type} [Field k] [IsAlgClosed k] {X Y : Over (Sp k)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom] (f : X ⟶ Y)
    (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ Y, ∃ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = y) :
    Surjective f.left := by
  refine ⟨fun y => ?_⟩
  by_contra hy
  have hC := (isConstructible_image_of_isClosed f isClosed_univ).compl
  obtain ⟨V, hV, h1, h2⟩ := exists_isOpen_inter_closure_subset_of_isConstructible
    continuous_id hC
  rw [Set.preimage_id] at h1 h2
  have hne : (V ∩ closure (f.left '' Set.univ)ᶜ).Nonempty := by
    rw [← closure_nonempty_iff, h2, closure_nonempty_iff]
    exact ⟨y, fun ⟨x, _, hx⟩ => hy ⟨x, hx⟩⟩
  have : JacobsonSpace Y.left := LocallyOfFiniteType.jacobsonSpace Y.hom
  obtain ⟨c, hcZ, hc⟩ := nonempty_inter_closedPoints hne
    (hV.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  obtain ⟨z, hz⟩ := exists_pt_mem (X := Y) (Z := {c}) hc ⟨c, rfl⟩
  obtain ⟨x, rfl⟩ := h z
  exact h1 hcZ ⟨pt x, trivial, hz⟩

theorem geometricallyConnected_of_surjective {X Y S : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ S)
    [Surjective f] [GeometricallyConnected (f ≫ g)] : GeometricallyConnected g := by
  refine ⟨fun K _ y W fst snd hW => ?_⟩
  have h1 := (IsPullback.of_hasPullback f fst).paste_vert hW
  have : ConnectedSpace ↥(pullback f fst) :=
    GeometricallyConnected.geometrically_connectedSpace _ _ _ h1
  exact (pullback.snd f fst).surjective.connectedSpace (pullback.snd f fst).continuous

theorem isIso_of_dim_le {k : Type} [Field k] {N G : Scheme.{0}} (ν : N ⟶ G) (s : G ⟶ Sp k)
    [IsClosedImmersion ν] [IsIntegral G] [IsReduced N] [Nonempty N] {g g' : ℕ}
    (hg : SmoothOfRelativeDimension g s) (hg' : SmoothOfRelativeDimension g' (ν ≫ s))
    (hle : g ≤ g') : IsIso ν := by
  suffices Surjective ν from isIso_of_isClosedImmersion_of_surjective ν
  refine ⟨fun y => ?_⟩
  by_contra hy
  obtain ⟨n⟩ := ‹Nonempty N›
  obtain ⟨_, ⟨U, hU, rfl⟩, hnU, -⟩ := G.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (ν n)) isOpen_univ
  replace hU : IsAffineOpen U := hU
  let W : G.Opens := ⟨(Set.range ν)ᶜ, ν.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  obtain ⟨z, hzU, hzW⟩ := nonempty_preirreducible_inter U.isOpen W.isOpen ⟨_, hnU⟩ ⟨y, hy⟩
  obtain ⟨r, hrW, hzr⟩ := hU.exists_basicOpen_le (V := W) ⟨z, hzW⟩ hzU
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hzr
  have hr1 : (ν.app U).hom r = 0 := by
    rw [← basicOpen_eq_bot_iff, ← Scheme.preimage_basicOpen, eq_bot_iff]
    intro t ht
    exact (hrW ht ⟨t, rfl⟩).elim
  have : Nonempty U := ⟨⟨_, hnU⟩⟩
  have h1 := ringKrullDim_succ_le_of_surjective (ν.app U).hom (ν.app_surjective U hU)
    (mem_nonZeroDivisors_of_ne_zero hr0) hr1
  rw [SmoothDim.ringKrullDim_affineOpen k G s g hg U hU ⟨_, hnU⟩,
    SmoothDim.ringKrullDim_affineOpen k N _ g' hg' _ (hU.preimage ν) ⟨n, hnU⟩] at h1
  have : g' + 1 ≤ g := by exact_mod_cast h1
  omega

theorem exists_divisiblePart : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : ℕ) (G : Over (Sp k)) [GrpObj G], SmConn G → ∃ (N : Over (Sp k)) (_ : GrpObj N) (ν : N ⟶ G), SmConn N ∧ IsMonHom ν ∧ IsClosedImmersion ν.left ∧ (∀ y : (𝟙_ (Over (Sp k)) ⟶ N), ∃ x : (𝟙_ (Over (Sp k)) ⟶ N), x ^ p = y) ∧ (∀ (x : (𝟙_ (Over (Sp k)) ⟶ G)) (n : ℕ), n.Coprime p → n ≠ 0 → x ^ n = 1 → ∃ y, y ≫ ν = x) ∧ (∀ F : G ⟶ G, IsMonHom F → ∃ F' : N ⟶ N, IsMonHom F' ∧ F' ≫ ν = ν ≫ F) ∧ ∀ g, SmoothOfRelativeDimension g G.hom → ∃ g', SmoothOfRelativeDimension g' N.hom ∧ (g ≤ g' → IsIso ν) := by
  intro k _ _ p G _ ⟨hc, hs, hsep, hqc, hgc⟩
  obtain ⟨a, ha⟩ := TorsionDense.exists_pow_stable G p ⊤ Set.univ isClosed_univ (by simp)
  have hpow : ∀ n : ℕ, IsMonHom (𝟙 G ^ n) := fun n => by
    induction n with
    | zero =>
      rw [pow_zero]
      exact inferInstanceAs (IsMonHom (toUnit G ≫ η[G]))
    | succ n ih =>
      rw [pow_succ]
      exact inferInstanceAs (IsMonHom (lift (𝟙 G ^ n) (𝟙 G) ≫ μ[G]))
  obtain ⟨Z, hZ, h⟩ := exists_isClosed_image_of_isClosed_subgroup k G G (𝟙 G ^ (p ^ a))
    (hpow _) inferInstance inferInstance inferInstance inferInstance ⊤ Set.univ isClosed_univ
    (by simp)
  replace h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ G, (∃ x, x ^ (p ^ a) = y) ↔ Set.range y.left ⊆ Z := by
    intro y
    rw [← h]
    simp only [MonObj.comp_pow, Category.comp_id, Subgroup.mem_top, true_and]
  let φ : (𝟙_ (Over (Sp k)) ⟶ G) →* (𝟙_ (Over (Sp k)) ⟶ G) :=
    have := hpow (p ^ a)
    MonoidHom.mk' (fun x => x ≫ 𝟙 G ^ (p ^ a)) fun x y => MonObj.mul_comp x y _
  obtain ⟨N, _, ν, hν, hνc, hNs, hr⟩ :=
    ReducedSubgroup.exists_smooth_closed_subgroup k G inferInstance φ.range Z hZ (fun x => by
      rw [← h, MonoidHom.mem_range]
      simp only [φ, MonoidHom.mk'_apply, MonObj.comp_pow, Category.comp_id])
  have : Mono ν := (Over.forget _).mono_of_mono_map (inferInstanceAs (Mono ν.left))
  have hw : N.hom = ν.left ≫ G.hom := (Over.w ν).symm
  have hNsep : IsSeparated N.hom := by rw [hw]; infer_instance
  have hNqc : QuasiCompact N.hom := by rw [hw]; infer_instance
  have hGi : IsIntegral G.left := isIntegral_of_smooth_of_geometricallyConnected G.hom
  have hNr : IsReduced N.left :=
    have := isNormalScheme_of_smooth N.hom
    IsNormalScheme.isReduced
  have hlift : ∀ {T : Over (Sp k)} [IsReduced T.left] [LocallyOfFiniteType T.hom] (g : T ⟶ G),
      (∀ x : 𝟙_ (Over (Sp k)) ⟶ T, ∃ y, y ^ (p ^ a) = x ≫ g) → ∃ l : T ⟶ N, l ≫ ν = g := by
    intro T _ _ g hg
    obtain ⟨l, hl⟩ := AbelianSubgroupFinite.exists_lift_of_range_subset g.left ν.left
      (hr ▸ ReducedSubgroup.range_subset_of_points g hZ fun x => (h _).1 (hg x))
    refine ⟨Over.homMk l ?_, Over.OverMorphism.ext hl⟩
    rw [← ν.w, ← Category.assoc, hl, g.w]
  have hmem : ∀ x : 𝟙_ (Over (Sp k)) ⟶ N, ∃ y, y ^ (p ^ a) = x ≫ ν := fun x => by
    rw [h, ← hr]
    rintro _ ⟨t, rfl⟩
    exact ⟨x.left t, rfl⟩
  obtain ⟨l, hl⟩ := hlift (𝟙 G ^ (p ^ a)) fun x => ⟨x, by rw [MonObj.comp_pow, Category.comp_id]⟩
  have hl' : ∀ x : 𝟙_ (Over (Sp k)) ⟶ G, (x ≫ l) ≫ ν = x ^ (p ^ a) := fun x => by
    rw [Category.assoc, hl, MonObj.comp_pow, Category.comp_id]
  have : Surjective l.left := surjective_of_rationalPoints l fun y => by
    obtain ⟨x, hx⟩ := hmem y
    exact ⟨x, by rw [← cancel_mono ν, hl', hx]⟩
  have hNgc : GeometricallyConnected N.hom := by
    have : GeometricallyConnected (l.left ≫ N.hom) := by rw [Over.w l]; exact hgc
    exact geometricallyConnected_of_surjective l.left N.hom
  refine ⟨N, _, ν, ⟨AbelianSubgroupFinite.isCommMonObj_of_mono ν, hNs, hNsep, hNqc, hNgc⟩, hν, hνc,
    fun y => ?_, fun x n hn hn0 hx => ?_, fun F hF => ?_, fun g hg => ?_⟩
  · obtain ⟨x, hx⟩ := hmem y
    obtain ⟨z, -, hz⟩ := ha x trivial
    refine ⟨z ≫ l, ?_⟩
    rw [← cancel_mono ν, MonObj.pow_comp, hl', ← pow_mul, ← pow_succ, hz, hx]
  · have hco : (p ^ a).Coprime (orderOf x) :=
      (Nat.Coprime.pow_left a hn.symm).coprime_dvd_right (orderOf_dvd_of_pow_eq_one hx)
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hco
    exact ⟨(x ^ m) ≫ l, by rw [hl', ← pow_mul, mul_comm, pow_mul, hm]⟩
  · obtain ⟨F', hF'⟩ := hlift (ν ≫ F) fun x => by
      obtain ⟨y, hy⟩ := hmem x
      exact ⟨y ≫ F, by rw [← MonObj.pow_comp, hy, Category.assoc]⟩
    refine ⟨F', ⟨?_, ?_⟩, hF'⟩
    · rw [← cancel_mono ν, Category.assoc, hF', IsMonHom.one_hom, IsMonHom.one_hom]
    · rw [← cancel_mono ν, Category.assoc, hF', IsMonHom.mul_hom, Category.assoc,
        IsMonHom.mul_hom, tensorHom_comp_tensorHom_assoc, hF']
  · have hNi : IsIntegral N.left := isIntegral_of_smooth_of_geometricallyConnected N.hom
    obtain ⟨g', hg'⟩ := exists_dim_of_preconnected N.hom (Classical.arbitrary _)
    refine ⟨g', hg', fun hle => ?_⟩
    have : IsIso ν.left := isIso_of_dim_le ν.left G.hom hg (hw ▸ hg') hle
    have : IsIso ((Over.forget _).map ν) := this
    exact isIso_of_reflects_iso ν (Over.forget _)

end GlobalTheory.DivisiblePart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvr
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvr
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS

namespace GlobalTheory

theorem existsUnique_hom_extension_smConn_semiAbelian_dvr :
    ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (H G : Over (Sp T)) [GrpObj H] [GrpObj G], SmConn H → IsSemiAbelian G → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj H ⟶ (Over.pullback (spMap (algebraMap T K))).obj G, IsMonHom f → ∃! F : H ⟶ G, IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f := by
  intro T K _ _ _ _ _ _ G G' _ _ hG hG' f hf
  obtain ⟨hcomm, hsm, hsep, hqc, hgc⟩ := hG
  have := hG'.comm
  have := hG'.smooth
  have := hG'.separated
  have := hG'.quasiCompact
  have hGflat : Flat G.hom := inferInstance
  obtain ⟨n, hn, hnT⟩ := exists_prime_isUnit_of_isLocalRing T
  let Φ := Over.pullback (spMap (algebraMap T K))
  let i : Φ.obj G ⟶ Φ.obj (G ⊗ G') := lift (𝟙 _) f ≫ Functor.LaxMonoidal.μ Φ G G'
  have hi : IsMonHom i := inferInstance
  have hi1 : i ≫ Φ.map (fst G G') = 𝟙 _ := by
    rw [Category.assoc, Functor.Monoidal.μ_fst, lift_fst]
  have hi2 : i ≫ Φ.map (snd G G') = f := by simp [i]
  have hs1 : IsSeparated (fst G G').left := inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom))
  have hs2 : LocallyOfFiniteType (fst G G').left :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom))
  have hs3 : QuasiCompact (fst G G').left :=
    inferInstanceAs (QuasiCompact (pullback.fst G.hom G'.hom))
  have hsP : IsSeparated (G ⊗ G').hom :=
    inferInstanceAs (IsSeparated (pullback.fst G.hom G'.hom ≫ G.hom))
  have hlP : LocallyOfFiniteType (G ⊗ G').hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.fst G.hom G'.hom ≫ G.hom))
  have hs4 : IsSeparated (Φ.map (fst G G')).left := by
    have h1 : IsSeparated (Φ.obj (G ⊗ G')).hom :=
      inferInstanceAs (IsSeparated (pullback.snd (G ⊗ G').hom _))
    rw [← Over.w (Φ.map (fst G G'))] at h1
    exact IsSeparated.of_comp _ (Φ.obj G).hom
  have hic : IsClosedImmersion i.left := by
    have h1 : IsClosedImmersion (i.left ≫ (Φ.map (fst G G')).left) := by
      rw [← Over.comp_left, hi1, Over.id_left]; infer_instance
    exact IsClosedImmersion.of_comp i.left (Φ.map (fst G G')).left
  obtain ⟨Ga, io, e, hio, hGa, he⟩ := exists_flat_closure T K (G ⊗ G') (Φ.obj G) i hic
  obtain ⟨_, hio', -, hc⟩ := flat_closure_subgroup T K (G ⊗ G') Ga io (Φ.obj G) i e hio hGa hi he
  have := hc inferInstance
  have hp : IsMonHom (io ≫ fst G G') := inferInstance
  have hpK : Φ.map (io ≫ fst G G') = e.hom := by
    rw [Functor.map_comp, ← he, Category.assoc, hi1, Category.comp_id]
  have hpKi : IsIso (Φ.map (io ≫ fst G G')) := by rw [hpK]; infer_instance
  have hGaS : IsSeparated Ga.hom := by rw [← Over.w io]; infer_instance
  have hGaL : LocallyOfFiniteType Ga.hom := by rw [← Over.w io]; infer_instance
  have hp1 : IsSeparated (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp2 : LocallyOfFiniteType (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hp3 : QuasiCompact (io ≫ fst G G').left := by rw [Over.comp_left]; infer_instance
  have hnt := KernelNoTorsion.eq_one_of_pow_eq_one_of_comp_eq_one T K Ga G (io ≫ fst G G') n hp hGaS
    (etale_mulN_torsion_dvr T Ga n hnT hGa hGaL).2
    (etale_mulN_torsion_dvr T G n hnT hGflat inferInstance).2 hpKi
  have hnS : IsUnit (n : Γ(Sp T, ⊤)) := by
    simpa using hnT.map (Scheme.ΓSpecIso (CommRingCat.of T)).inv.hom
  have hker := finite_geometric_kernel_of_pow_eq_one
    AbelianSubgroupFinite.finite_of_torsionFree (Sp T) G G' Ga io n hG' hio' hio hn hnS hnt
  have hqf := locallyQuasiFinite_of_finite_geometric_ker (Sp T) Ga G (io ≫ fst G G') hp hp2 hp3 hker
  have hiso := isIso_of_quasiFinite_of_isIso_genericFibre_dvr T K Ga G (io ≫ fst G G') hp hGa hp1 hp2
    hp3 hqf hsm hgc hpKi
  have hF : Φ.map (inv (io ≫ fst G G') ≫ io ≫ snd G G') = f := by
    rw [Functor.map_comp, Functor.map_inv, IsIso.inv_comp_eq, hpK, Functor.map_comp, ← he,
      Category.assoc, hi2]
  refine ⟨inv (io ≫ fst G G') ≫ io ≫ snd G G', ⟨?_, hF⟩, fun F hF' => ?_⟩
  · refine flat_dvr_generic_fibre.2.2 T K G G' _ hGflat hG'.separated ?_
    exact hF ▸ hf
  · exact flat_dvr_generic_fibre.1 T K G G' hGflat hG'.separated _ _ (hF'.2.trans hF.symm)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUniqueHomExtensionSmoothConnSemiAbelianDvrStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_hom_extension_smoothConn_semiAbelian_dvr : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (H G : Over (Sp T)) [GrpObj H] [GrpObj G], SmConn H → IsSemiAbelian G → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj H ⟶ (Over.pullback (spMap (algebraMap T K))).obj G, IsMonHom f → ∃! F : H ⟶ G, IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f := by
  first | exact @GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr | exact GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr | (intros; apply GlobalTheory.existsUnique_hom_extension_smConn_semiAbelian_dvr <;> assumption)
end
end
