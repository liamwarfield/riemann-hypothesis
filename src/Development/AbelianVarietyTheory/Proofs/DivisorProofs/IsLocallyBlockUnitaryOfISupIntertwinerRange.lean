module

public import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLabelAtUnfolding
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.WeilActionTranslatesThetaByUnitScalar
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.TraceDefinitePairsEqAutomorphicTrace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitarySimilitudeIntegralSubgroupCommensuratedFr

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryOfISupIntertwinerRange
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryPiFin
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryPiFin
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem locU_pi_fin : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), LocU s F → ∀ n : ℕ, LocU s (fun a b => (LinearMap.pi fun i : Fin n => F a b ∘ₗ LinearMap.proj i : Module.End ℂ (Fin n → M))) := by
  intro ι M _ _ _ _ s F hF n t
  classical
  obtain ⟨U, htU, hfd, hst, ip, hsym, hpos, hadj⟩ := hF (t.biUnion fun x => Finset.univ.image x)
  have hmem : ∀ x ∈ t, ∀ i, x i ∈ U := fun x hx i =>
    htU _ (Finset.mem_biUnion.2 ⟨x, hx, Finset.mem_image.2 ⟨i, Finset.mem_univ _, rfl⟩⟩)
  let U' : Submodule ℂ (Fin n → M) := Submodule.pi Set.univ (fun _ => U)
  let ip' : (Fin n → M) →ₗ⋆[ℂ] (Fin n → M) →ₗ[ℂ] ℂ :=
    ∑ i : Fin n, (ip ∘ₛₗ (LinearMap.proj i : (Fin n → M) →ₗ[ℂ] M)).compl₂ (LinearMap.proj i : (Fin n → M) →ₗ[ℂ] M)
  have hip' : ∀ x y, ip' x y = ∑ i, ip (x i) (y i) := by
    intro x y
    simp [ip', LinearMap.sum_apply]
  refine ⟨U', fun x hx i _ => hmem x hx i, ?_, ?_, ip', ?_, ?_, ?_⟩
  · let g : (Fin n → U) →ₗ[ℂ] (Fin n → M) := LinearMap.pi fun i => U.subtype ∘ₗ LinearMap.proj i
    have hle : U' ≤ LinearMap.range g := by
      intro x hx
      exact ⟨fun i => ⟨x i, hx i (Set.mem_univ _)⟩, by ext i; rfl⟩
    exact Submodule.finiteDimensional_of_le hle
  · intro a b hab u hu i _
    exact hst a b hab (u i) (hu i (Set.mem_univ _))
  · intro x hx y hy
    rw [hip', hip', star_sum]
    exact Finset.sum_congr rfl fun i _ => hsym _ (hx i (Set.mem_univ _)) _ (hy i (Set.mem_univ _))
  · intro x hx hx0
    rw [hip', Complex.re_sum]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx0 (funext h)
    have hnn : ∀ i ∈ (Finset.univ : Finset (Fin n)), 0 ≤ (ip (x i) (x i)).re := by
      intro i _
      by_cases h : x i = 0
      · simp [h]
      · exact (hpos _ (hx i (Set.mem_univ _)) h).le
    exact Finset.sum_pos' hnn ⟨j, Finset.mem_univ _, hpos _ (hx j (Set.mem_univ _)) hj⟩
  · intro a b hab x hx y hy
    rw [hip', hip']
    exact Finset.sum_congr rfl fun i _ => hadj a b hab _ (hx i (Set.mem_univ _)) _ (hy i (Set.mem_univ _))

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryPiFinStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyBlockUnitary_pi_fin : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), LocU s F → ∀ n : ℕ, LocU s (fun a b => (LinearMap.pi fun i : Fin n => F a b ∘ₗ LinearMap.proj i : Module.End ℂ (Fin n → M))) := by
  first | exact @GlobalTheory.HoweR.locU_pi_fin | exact GlobalTheory.HoweR.locU_pi_fin | (intros; apply GlobalTheory.HoweR.locU_pi_fin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceMapIntertwiner
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceMapIntertwiner
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem unitOn_map : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool)
    (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M')
    (f : M →ₗ[ℂ] M') (U : Submodule ℂ M), (∀ a b, s a = s b → ∀ x ∈ U, f (F a b x) = F' a b (f x)) →
    UnitOn s F U → UnitOn s F' (U.map f) := by
  intro ι M _ _ _ _ s F M' _ _ F' f U hF hU
  obtain ⟨hfd, hst, ip, hherm, hpos, hadj⟩ := hU
  let K : Submodule ℂ M := U ⊓ LinearMap.ker f
  have hKU : ∀ k ∈ K, k ∈ U := fun k hk => (Submodule.mem_inf.mp hk).1
  have hKf : ∀ k ∈ K, f k = 0 := fun k hk => LinearMap.mem_ker.mp (Submodule.mem_inf.mp hk).2
  haveI : FiniteDimensional ℂ K := Submodule.finiteDimensional_of_le (inf_le_left : K ≤ U)
  let n := Module.finrank ℂ K
  let b := Module.finBasis ℂ K
  let ψ : M →ₗ[ℂ] (Fin n → ℂ) := LinearMap.pi (fun i => ip (b i : M))
  let U1 : Submodule ℂ M := U ⊓ LinearMap.ker ψ
  have hU1U : ∀ w ∈ U1, w ∈ U := fun w hw => (Submodule.mem_inf.mp hw).1
  have hA : ∀ w ∈ U1, ∀ k ∈ K, ip k w = 0 := by
    intro w hw k hk
    have hw' : ∀ i, ip (b i : M) w = 0 := fun i => by
      have := congrFun (LinearMap.mem_ker.mp (Submodule.mem_inf.mp hw).2) i
      simpa [ψ] using this
    have h0 : ((ip.flip w).comp K.subtype) = 0 := b.ext (fun i => by simpa using hw' i)
    have := LinearMap.congr_fun h0 ⟨k, hk⟩
    simpa using this
  have hA' : ∀ w ∈ U1, ∀ k ∈ K, ip w k = 0 := by
    intro w hw k hk
    have := hherm k (hKU k hk) w (hU1U w hw)
    rw [hA w hw k hk, star_zero] at this
    exact this.symm
  have hinj : Function.Injective (ψ.comp K.subtype) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro k hk
    have hk1 : (k : M) ∈ U1 := Submodule.mem_inf.mpr ⟨hKU k k.2, LinearMap.mem_ker.mpr (by simpa using hk)⟩
    have h0 := hA _ hk1 _ k.2
    by_contra hne
    have hne' : (k : M) ≠ 0 := fun h => hne (Subtype.ext h)
    have := hpos _ (hKU k k.2) hne'
    rw [h0] at this
    simp at this
  have hsurj : Function.Surjective (ψ.comp K.subtype) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [n])).mp hinj
  have hdec : ∀ u ∈ U, ∃ k ∈ K, u - k ∈ U1 := by
    intro u hu
    obtain ⟨k, hk⟩ := hsurj (ψ u)
    refine ⟨k, k.2, Submodule.mem_inf.mpr ⟨U.sub_mem hu (hKU k k.2), LinearMap.mem_ker.mpr ?_⟩⟩
    rw [map_sub]
    exact sub_eq_zero.mpr (by simpa using hk.symm)
  have hinj1 : LinearMap.ker (f.comp U1.subtype) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro w hw
    have hwK : (w : M) ∈ K := Submodule.mem_inf.mpr ⟨hU1U w w.2, LinearMap.mem_ker.mpr (by simpa using hw)⟩
    have h0 := hA _ w.2 _ hwK
    by_contra hne
    have hne' : (w : M) ≠ 0 := fun h => hne (Subtype.ext h)
    have := hpos _ (hU1U w w.2) hne'
    rw [h0] at this
    simp at this
  obtain ⟨h, hh⟩ := LinearMap.exists_leftInverse_of_injective (f.comp U1.subtype) hinj1
  let g : M' →ₗ[ℂ] M := U1.subtype.comp h
  have hg : ∀ w ∈ U1, g (f w) = w := by
    intro w hw
    have := congrArg Subtype.val (LinearMap.congr_fun hh ⟨w, hw⟩)
    simpa [g] using this
  have hkey : ∀ u ∈ U, g (f u) ∈ U1 ∧ u - g (f u) ∈ K := by
    intro u hu
    obtain ⟨k, hk, hw⟩ := hdec u hu
    have hfu : f u = f (u - k) := by rw [map_sub, hKf k hk, sub_zero]
    rw [hfu, hg _ hw, sub_sub_cancel]
    exact ⟨hw, hk⟩
  have hgU1 : ∀ x ∈ U.map f, g x ∈ U1 := by
    rintro x ⟨u, hu, rfl⟩
    exact (hkey u hu).1
  have hfg : ∀ x ∈ U.map f, f (g x) = x := by
    rintro x ⟨u, hu, rfl⟩
    have := hKf _ (hkey u hu).2
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  haveI := hfd
  refine ⟨inferInstance, ?_, (ip.comp g).compl₂ g, ?_, ?_, ?_⟩
  · rintro a b hab _ ⟨u, hu, rfl⟩
    exact ⟨F a b u, hst a b hab u hu, hF a b hab u hu⟩
  · intro x hx y hy
    exact hherm _ (hU1U _ (hgU1 x hx)) _ (hU1U _ (hgU1 y hy))
  · intro x hx hne
    apply hpos _ (hU1U _ (hgU1 x hx))
    intro h0
    apply hne
    rw [← hfg x hx]
    change f (g x) = 0
    rw [h0, map_zero]
  · intro a b hab x hx y hy
    have hu0 := hgU1 x hx
    have hv0 := hgU1 y hy
    have e1 : F' a b x = f (F a b (g x)) := by rw [hF a b hab _ (hU1U _ hu0), hfg x hx]
    have e2 : F' b a y = f (F b a (g y)) := by rw [hF b a hab.symm _ (hU1U _ hv0), hfg y hy]
    change ip (g (F' a b x)) (g y) = ip (g x) (g (F' b a y))
    rw [e1, e2]
    have hk1 := (hkey _ (hst a b hab _ (hU1U _ hu0))).2
    have hk2 := (hkey _ (hst b a hab.symm _ (hU1U _ hv0))).2
    have l1 : ip (g (f (F a b (g x)))) (g y) = ip (F a b (g x)) (g y) := by
      have := hA (g y) hv0 _ hk1
      rw [map_sub, LinearMap.sub_apply] at this
      exact (sub_eq_zero.mp this).symm
    have l2 : ip (g x) (g (f (F b a (g y)))) = ip (g x) (F b a (g y)) := by
      have := hA' (g x) hu0 _ hk2
      rw [map_sub] at this
      exact (sub_eq_zero.mp this).symm
    rw [l1, l2]
    exact hadj a b hab _ (hU1U _ hu0) _ (hU1U _ hv0)

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockUnitaryFiniteSubspaceMapIntertwinerStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isBlockUnitaryFiniteSubspace_map_intertwiner : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (f : M →ₗ[ℂ] M') (U : Submodule ℂ M), (∀ a b, s a = s b → ∀ x ∈ U, f (F a b x) = F' a b (f x)) → UnitOn s F U → UnitOn s F' (U.map f) := by
  first | exact @GlobalTheory.HoweR.unitOn_map | exact GlobalTheory.HoweR.unitOn_map | (intros; apply GlobalTheory.HoweR.unitOn_map <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryOfISupIntertwinerRange
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

namespace GlobalTheory.HoweR

theorem locU_of_iSup_range_eq_top : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (G : Set (M →ₗ[ℂ] M')), (∀ f ∈ G, ∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) → (⨆ f ∈ G, LinearMap.range f) = ⊤ → LocU s F → LocU s F' := by
  intro ι M _ _ _ _ s F M' _ _ F' G hG hsup hloc t
  classical
  have hy : ∀ y ∈ t, ∃ S : Finset G, y ∈ ⨆ i ∈ S, LinearMap.range (i : M →ₗ[ℂ] M') := by
    intro y _
    have h1 : y ∈ ⨆ i : G, LinearMap.range (i : M →ₗ[ℂ] M') := by
      rw [iSup_subtype'' G (fun f : M →ₗ[ℂ] M' => LinearMap.range f), hsup]; trivial
    exact Submodule.mem_iSup_iff_exists_finset.1 h1
  choose S hS using hy
  let SS : Finset G := t.attach.biUnion (fun y => S y.1 y.2)
  have hmem : ∀ y ∈ t, y ∈ ⨆ i ∈ SS, LinearMap.range (i : M →ₗ[ℂ] M') := by
    intro y hy
    exact (biSup_mono (fun i hi => Finset.mem_biUnion.2 ⟨⟨y, hy⟩, Finset.mem_attach _ _, hi⟩) :
      (⨆ i ∈ S y hy, LinearMap.range (i : M →ₗ[ℂ] M')) ≤ _) (hS y hy)
  let e : SS ≃ Fin SS.card := SS.equivFin
  let f : Fin SS.card → (M →ₗ[ℂ] M') := fun k => ((e.symm k).1 : M →ₗ[ℂ] M')
  let g : (Fin SS.card → M) →ₗ[ℂ] M' := ∑ k, f k ∘ₗ LinearMap.proj k
  have hg : ∀ x, g x = ∑ k, f k (x k) := by intro x; simp [g]
  have hrange : ∀ y ∈ t, y ∈ LinearMap.range g := by
    intro y hy
    refine (iSup₂_le ?_ : (⨆ i ∈ SS, LinearMap.range (i : M →ₗ[ℂ] M')) ≤ LinearMap.range g) (hmem y hy)
    intro i hi w hw
    obtain ⟨x, rfl⟩ := LinearMap.mem_range.1 hw
    refine ⟨Pi.single (e ⟨i, hi⟩) x, ?_⟩
    rw [hg, Finset.sum_eq_single (e ⟨i, hi⟩)]
    · simp [f]
    · intro b _ hb; simp [Pi.single_apply, hb]
    · simp
  choose z hz using fun y hy => LinearMap.mem_range.1 (hrange y hy)
  obtain ⟨U, hU, hUU⟩ := GlobalTheory.T.isLocallyBlockUnitary_pi_fin ι M s F hloc SS.card (t.attach.image fun y : {x // x ∈ t} => z y.1 y.2)
  refine ⟨U.map g, ?_, GlobalTheory.T.isBlockUnitaryFiniteSubspace_map_intertwiner ι (Fin SS.card → M) s _ M' F' g U ?_ hUU⟩
  · intro y hy
    exact ⟨z y hy, hU _ (Finset.mem_image.2 ⟨⟨y, hy⟩, Finset.mem_attach _ _, rfl⟩), hz y hy⟩
  · intro a b hab x _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hg, hg, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    exact hG (f k) (e.symm k).1.2 a b hab (x k)

end GlobalTheory.HoweR
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyBlockUnitaryOfISupIntertwinerRangeStatement
open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLocallyBlockUnitary_of_iSup_intertwiner_range : ∀ (ι M : Type) [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M] (s : ι → Bool) (F : ι → ι → Module.End ℂ M), ∀ (M' : Type) [AddCommGroup M'] [Module ℂ M'] (F' : ι → ι → Module.End ℂ M') (G : Set (M →ₗ[ℂ] M')), (∀ f ∈ G, ∀ a b, s a = s b → ∀ x, f (F a b x) = F' a b (f x)) → (⨆ f ∈ G, LinearMap.range f) = ⊤ → LocU s F → LocU s F' := by
  first | exact @GlobalTheory.HoweR.locU_of_iSup_range_eq_top | exact GlobalTheory.HoweR.locU_of_iSup_range_eq_top | (intros; apply GlobalTheory.HoweR.locU_of_iSup_range_eq_top <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFormsGeneratedDlog
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private lemma smul_dlog_mem_forms {X : Scheme.{0}} [IsIntegral X] (Z : Set X) (y : X)
    (g : X.functionFieldˣ) (hg : _root_.GlobalTheory.LogDR.LogUnit Z y g) (b : X.functionField)
    (hb : b ∈ _root_.GlobalTheory.LogDR.locRing y) :
    ExteriorAlgebra.ι X.functionField (b • _root_.GlobalTheory.LogDR.dlog g) ∈
      _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
        (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1 := by
  unfold _root_.GlobalTheory.DI.forms
  refine AddSubgroup.subset_closure ⟨b, hb, fun _ => _root_.GlobalTheory.LogDR.dlog g,
    fun _ => ⟨g, hg, rfl⟩, ?_⟩
  rw [map_smul, ExteriorAlgebra.ιMulti_apply]
  simp

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private lemma logUnit_of_isUnit_stalk {X : Scheme.{0}} [IsIntegral X] (Z : Set X)
    (y : X) (g : X.functionFieldˣ) (a : X.presheaf.stalk y) (ha : IsUnit a)
    (hg : algebraMap (X.presheaf.stalk y) X.functionField a = g) :
    _root_.GlobalTheory.LogDR.LogUnit Z y g := by
  intro z hz _
  refine ⟨X.presheaf.stalkSpecializes hz a, ha.map (X.presheaf.stalkSpecializes hz).hom, ?_⟩
  rw [← hg]
  change (X.presheaf.stalkSpecializes _) ((X.presheaf.stalkSpecializes hz) a) =
    (X.presheaf.stalkSpecializes _) a
  rw [← CategoryTheory.comp_apply, TopCat.Presheaf.stalkSpecializes_comp]


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.dK_dlog_mem_forms_one : ∀ {X : Scheme.{0}} [IsIntegral X]
    (Z : Set X) (y : X), (∀ w ∈ _root_.GlobalTheory.LogDR.locRing y,
      ExteriorAlgebra.ι X.functionField (_root_.GlobalTheory.LogDR.dK w) ∈
        _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
          (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1) ∧
      ∀ g, _root_.GlobalTheory.LogDR.LogUnit Z y g → ExteriorAlgebra.ι X.functionField (_root_.GlobalTheory.LogDR.dlog g) ∈
        _root_.GlobalTheory.DI.forms (_root_.GlobalTheory.LogDR.locRing y : Set X.functionField)
          (_root_.GlobalTheory.LogDR.dlog '' {g | _root_.GlobalTheory.LogDR.LogUnit Z y g}) 1 := by
  intro X _ Z y
  refine ⟨fun w hw => ?_, fun g hg => ?_⟩
  · obtain ⟨a, rfl⟩ := _root_.GlobalTheory.LogDR.mem_locRing.mp hw
    rcases IsLocalRing.isUnit_or_isUnit_one_sub_self a with ha | ha
    · set U := (ha.map (algebraMap (X.presheaf.stalk y) X.functionField)).unit with hU
      have hUv : (U : X.functionField) = algebraMap (X.presheaf.stalk y) X.functionField a := rfl
      have key := smul_dlog_mem_forms Z y U
        (logUnit_of_isUnit_stalk Z y U a ha hUv.symm) _ hw
      convert key using 2
      unfold _root_.GlobalTheory.LogDR.dlog _root_.GlobalTheory.LogDR.dK
      rw [smul_smul, ← hUv, Units.mul_inv, one_smul]
    · set U := (ha.map (algebraMap (X.presheaf.stalk y) X.functionField)).unit with hU
      have hUv : (U : X.functionField) =
          algebraMap (X.presheaf.stalk y) X.functionField (1 - a) := rfl
      have hmem : -(U : X.functionField) ∈ _root_.GlobalTheory.LogDR.locRing y :=
        neg_mem (_root_.GlobalTheory.LogDR.mem_locRing.mpr ⟨1 - a, hUv.symm⟩)
      have key := smul_dlog_mem_forms Z y U
        (logUnit_of_isUnit_stalk Z y U (1 - a) ha hUv.symm) _ hmem
      convert key using 2
      unfold _root_.GlobalTheory.LogDR.dlog _root_.GlobalTheory.LogDR.dK
      rw [smul_smul, neg_mul, Units.mul_inv, neg_smul, one_smul, hUv, map_sub, map_one,
        map_sub, Derivation.map_one_eq_zero, zero_sub, neg_neg]
  · simpa using smul_dlog_mem_forms Z y g hg 1 (one_mem _)

end GlobalTheory.DI
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModPSquaredStalkSurjective
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI.StalkKer

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private lemma natCast_eq_zero_stalk_of_over_zmod (n : ℕ) {X : Scheme} (f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod n)) (x : X) :
    ((n : ℕ) : X.presheaf.stalk x) = 0 := by
  have := map_natCast ((X.presheaf.germ ⊤ x trivial).hom.comp
    ((f.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of (ZMod n))).inv.hom)) n
  rw [← this, ZMod.natCast_self, map_zero]

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
private lemma stalk_hom_eq_zero_of_stalkMap_eq_zero {X Y : Scheme} (π : X ⟶ Y) (y : X) {R : CommRingCat}
    [IsLocalRing R] (h : Spec R ⟶ X) (hy : h (IsLocalRing.closedPoint R) = y)
    (q : Y.presheaf.stalk (π y) ⟶ R) (hh : h ≫ π = Spec.map q ≫ Y.fromSpecStalk (π y))
    (z : Y.presheaf.stalk (π y)) (hz : (π.stalkMap y).hom z = 0) : q.hom z = 0 := by
  subst hy
  have h1 := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (h ≫ π)
  have h2 : Scheme.stalkClosedPointTo (h ≫ π) = q :=
    Spec.map_injective ((cancel_mono (Y.fromSpecStalk _)).1 (h1.trans hh))
  rw [← h2, Scheme.stalkClosedPointTo_comp]
  simp [hz]


set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry TopologicalSpace in
theorem _root_.GlobalTheory.DI.StalkKer.stalkMap_surjective_ker : ∀ (p : ℕ) [Fact p.Prime] (Y X : Scheme.{0})
    (g : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod (p ^ 2))) (f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod p)) (π : X ⟶ Y),
    IsPullback π f g (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p))) →
    ∀ y : X, Function.Surjective (π.stalkMap y).hom ∧
      ∀ z, (π.stalkMap y).hom z = 0 ↔ ∃ w, z = p * w := by
  intro p hp Y X g f π hPB y
  have hci : IsClosedImmersion π :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hPB.flip
      (IsClosedImmersion.spec_of_surjective _ (ZMod.ringHom_surjective _))
  refine ⟨π.stalkMap_surjective y, fun z => ⟨fun hz => ?_, ?_⟩⟩
  · let O := Y.presheaf.stalk (π y)
    let I : Ideal O := Ideal.span {((p : ℕ) : O)}
    have hsq : ((p : ℕ) : O) ^ 2 = 0 := by
      rw [← Nat.cast_pow]; exact natCast_eq_zero_stalk_of_over_zmod (p ^ 2) g (π y)
    have hI : I ≠ ⊤ := by
      intro hT
      have hu : IsUnit ((p : ℕ) : O) := Ideal.span_singleton_eq_top.1 hT
      have h0 : IsUnit (0 : O) := hsq ▸ hu.pow 2
      exact zero_ne_one (isUnit_zero_iff.1 h0)
    haveI : Nontrivial (O ⧸ I) := Ideal.Quotient.nontrivial_iff.2 hI
    haveI : IsLocalRing (O ⧸ I) :=
      IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    haveI hloc : IsLocalHom (Ideal.Quotient.mk I) :=
      IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
    have hpQ : ((p : ℕ) : O ⧸ I) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk I)]
      exact Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span rfl)
    haveI : CharP (O ⧸ I) p := ringChar.of_eq (CharP.ringChar_of_prime_eq_zero hp.out hpQ)
    let q : O ⟶ CommRingCat.of (O ⧸ I) := CommRingCat.ofHom (Ideal.Quotient.mk I)
    haveI : IsLocalHom q.hom := hloc
    let a : Spec (CommRingCat.of (O ⧸ I)) ⟶ Y := Spec.map q ≫ Y.fromSpecStalk (π y)
    let b : Spec (CommRingCat.of (O ⧸ I)) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (ZMod p) :=
      Spec.map (CommRingCat.ofHom (ZMod.castHom (dvd_refl p) (O ⧸ I)))
    have hcomm : a ≫ g = b ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)) := by
      obtain ⟨φ, hφ⟩ := Spec.map_surjective (a ≫ g)
      rw [← hφ]
      change Spec.map φ = Spec.map _ ≫ Spec.map _
      rw [← Spec.map_comp]
      congr 1
      apply CommRingCat.hom_ext
      exact RingHom.ext_zmod _ _
    let h := hPB.lift a b hcomm
    have hh : h ≫ π = a := hPB.lift_fst a b hcomm
    have hy : h (IsLocalRing.closedPoint (O ⧸ I)) = y := by
      apply π.isClosedEmbedding.injective
      change (h ≫ π) _ = _
      rw [hh]
      change Y.fromSpecStalk (π y) ((Spec.map q) (IsLocalRing.closedPoint (O ⧸ I))) = π y
      rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
    have hq := stalk_hom_eq_zero_of_stalkMap_eq_zero π y h hy q hh z hz
    have hmem : z ∈ I := Ideal.Quotient.eq_zero_iff_mem.1 hq
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hmem
    exact ⟨w, by rw [← hw, mul_comm]⟩
  · rintro ⟨w, rfl⟩
    rw [map_mul, map_natCast, natCast_eq_zero_stalk_of_over_zmod p f y, zero_mul]

end GlobalTheory.DI.StalkKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealCharacter
open AlgebraicGeometry CategoryTheory NumberField Matrix MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.Dict
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameEquiv.RealChar

variable {D : D7} {S T : HSp D} (C : GlobalTheory.Ker.Ctx S T)

theorem xB_mem_dom {B : C.Bas} (hB : C.IsB B) : C.xB B ∈ C.X.dom :=
  GlobalTheory.Ker.ONBasis.mem_dom C.X (GlobalTheory.Ker.ONBasis.isONFr_xB C hB)

theorem Th_ne_zero {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) : C.Th x φ ≠ 0 := by
  intro h
  obtain ⟨l1, l2, -⟩ := GlobalTheory.Ker.Ctx.th_laws D S T C x hx φ hφ
  have h3 : GlobalTheory.SW.IsSB ((0 : ℂ) • φ) := by
    rw [zero_smul]
    exact GlobalTheory.SW.isSB_zero
  refine h0 (((l1 _ h3).2 ?_).trans (zero_smul ℂ φ))
  rw [l2, h, smul_zero]

theorem Th_zero {x : Frame C.X.Ψ T.rank} (hx : x ∈ C.X.dom) : C.Th x (0 : TF S.rank C.g) = 0 := by
  have h := (GlobalTheory.Ker.Ctx.th_laws D S T C x hx 0 GlobalTheory.SW.isSB_zero).2.1 0
  rwa [zero_smul, zero_smul] at h

theorem scalar_eq {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hom : GlobalTheory.Ker.IsWeak C.ψ S T om)
    {u : GA D T} {B B' : C.Bas} (hB : C.IsB B) (hB' : C.IsB B') {φ : TF S.rank C.g} (hφ : GlobalTheory.SW.IsSB φ)
    (h0 : φ ≠ 0) {c c' : ℂ} (hc' : ‖c'‖ = 1)
    (e : om (1, u) (C.Th (C.xB B) φ) = c • C.Th (C.xB (C.mvB u B)) φ)
    (e' : om (1, u) (C.Th (C.xB B') φ) = c' • C.Th (C.xB (C.mvB u B')) φ) : c = c' := by
  obtain ⟨⟨μ, 𝓕, hμ⟩, hip⟩ := GlobalTheory.Ker.ScalarProduct.ip_basic D S T C
  have hmv : ∀ A, C.IsB A → C.IsB (C.mvB u A) := fun A hA =>
    (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 A hA).2.2.2.2.2 u).1
  have hth : ∀ A, C.IsB A → C.IsTh (C.Th (C.xB A) φ) := fun A hA =>
    (GlobalTheory.T.adelicZakTheta_exists_unique D S T C _ (xB_mem_dom C hA) φ hφ).1.1
  have hd : dbl C.X C.bas C.idx φ φ 0 ≠ 0 := by
    intro hc
    have h1 := GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C hB) (xB_mem_dom C hB) hφ hφ
    rw [hc, zero_mul] at h1
    exact Th_ne_zero C (xB_mem_dom C hB) hφ h0 ((hip μ 𝓕 hμ _ (hth B hB)).2.1 h1)
  have hk : kZero C.X C.idx (C.xB B) (C.xB B') (0 : Fin S.rank → Fin C.g → ℂ) 0 ≠ 0 := by
    rw [GlobalTheory.AdTh.Overlap.kZero_zero]
    exact Finset.prod_ne_zero_iff.2 fun τ _ => inv_ne_zero (pow_ne_zero _ (mul_ne_zero
      (DblPoint.det_aLin_ne_zero (xB_mem_dom C hB) (xB_mem_dom C hB') τ)
      (DblPoint.det_aAnti_ne_zero (xB_mem_dom C hB) (xB_mem_dom C hB') τ)))
  have h1 := ((hip μ 𝓕 hμ _ (hth B hB)).2.2.2 _ (hth B' hB')).2.2.2.2.2 om hom (1, u)
  have h2 : GlobalTheory.Ker.ipO μ 𝓕 (c • C.Th (C.xB (C.mvB u B)) φ) (c' • C.Th (C.xB (C.mvB u B')) φ) =
      c * conj c' * GlobalTheory.Ker.ipO μ 𝓕 (C.Th (C.xB (C.mvB u B)) φ) (C.Th (C.xB (C.mvB u B')) φ) := by
    rw [GlobalTheory.Ker.ipO, GlobalTheory.Ker.ipO, ← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [e, e', h2, GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C (hmv B hB)) (xB_mem_dom C (hmv B' hB')) hφ hφ,
    GlobalTheory.AdTh.Overlap.ipO_Th C hμ (xB_mem_dom C hB) (xB_mem_dom C hB') hφ hφ,
    GlobalTheory.AdTh.Overlap.kZero_mvB C hB u] at h1
  have h3 : c * conj c' = 1 := mul_right_cancel₀ (mul_ne_zero hd hk) (h1.trans (one_mul _).symm)
  have h4 : c' * conj c' = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc']
    simp
  linear_combination c' * h3 - c * h4

end GlobalTheory.FrameEquiv.RealChar


open GlobalTheory.FrameEquiv.RealChar in
set_option maxHeartbeats 1000000 in
theorem GlobalTheory.FrameEquiv.exists_real_character : ∀ (D : D7) (S T : HSp D) (C : GlobalTheory.Ker.Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), GlobalTheory.Ker.IsWeak C.ψ S T om → ∃ χ : GA D T → ℂ, (∀ u ∈ GinfC T, ‖χ u‖ = 1) ∧ (∀ u ∈ GinfC T, ∀ u' ∈ GinfC T, χ (u * u') = χ u * χ u') ∧ ∀ u ∈ GinfC T, ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, GlobalTheory.SW.IsSB φ → om (1, u) (C.Th (C.xB B) φ) = χ u • C.Th (C.xB (C.mvB u B)) φ := by
  intro D S T C om hom
  by_cases hex : ∃ φ₀ : TF S.rank C.g, GlobalTheory.SW.IsSB φ₀ ∧ φ₀ ≠ 0
  swap
  · refine ⟨fun _ => 1, fun _ _ => norm_one, fun _ _ _ _ => (mul_one _).symm, fun u _ B hB φ hφ => ?_⟩
    have h0 : φ = 0 := by
      by_contra h
      exact hex ⟨φ, hφ, h⟩
    have hmv : C.IsB (C.mvB u B) := (((GlobalTheory.Ker.onBasis_frame_period D S T C).2 B hB).2.2.2.2.2 u).1
    rw [h0, Th_zero C (xB_mem_dom C hB), Th_zero C (xB_mem_dom C hmv), map_zero, smul_zero]
  obtain ⟨φ₀, s₀, n₀⟩ := hex
  obtain ⟨⟨B₀, hB₀⟩, hJ⟩ := GlobalTheory.Ker.onBasis_frame_period D S T C
  have hr := GlobalTheory.Ker.RealScalar.om_real_Th D S T C om hom 1 (one_mem _)
  choose! χ hχ1 hχ using fun u hu => hr u hu B₀ hB₀
  have main : ∀ u ∈ GinfC T, ∀ B, C.IsB B → ∀ φ : TF S.rank C.g, GlobalTheory.SW.IsSB φ →
      om (1, u) (C.Th (C.xB B) φ) = χ u • C.Th (C.xB (C.mvB u B)) φ := fun u hu B hB φ hφ => by
    obtain ⟨c, -, hc⟩ := hr u hu B hB
    rw [← scalar_eq C hom hB hB₀ s₀ n₀ (hχ1 u hu) (hc φ₀ s₀) (hχ u hu φ₀ s₀)]
    exact hc φ hφ
  refine ⟨χ, hχ1, fun u hu u' hu' => ?_, main⟩
  have h1 := main (u * u') (mul_mem hu hu') B₀ hB₀ φ₀ s₀
  obtain ⟨hm, hmul, -⟩ := (hJ B₀ hB₀).2.2.2.2.2 u'
  have e : ((1, u * u') : GA D S × GA D T) = (1, u) * (1, u') := by simp
  rw [e, map_mul, mul_apply_eq_comp, main u' hu' B₀ hB₀ φ₀ s₀, map_smul, main u hu _ hm φ₀ s₀, hmul u,
    smul_smul] at h1
  have hne := Th_ne_zero C (xB_mem_dom C ((hJ _ hm).2.2.2.2.2 u).1) s₀ n₀
  rw [mul_comm]
  exact (smul_left_injective ℂ hne h1).symm
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrobeniusLiftStalk
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobLiftLocalization
open GlobalTheory GlobalTheory.DI

namespace GlobalTheory.DI

theorem frobLift_localization :
    ∀ (p : ℕ) [Fact p.Prime] {B Kt : Type} [CommRing B] [CommRing Kt] [Algebra B Kt]
      (S : Submonoid B) [IsLocalization S Kt] (F : B →+* B), (p : B) ^ 2 = 0 →
      (∀ z, ∃ w, F z = z ^ p + p * w) →
      ∃ F' : Kt →+* Kt, (∀ b, F' (algebraMap B Kt b) = algebraMap B Kt (F b)) ∧
        ∀ z, ∃ w, F' z = z ^ p + p * w := by
  intro p _ B Kt _ _ _ S _ F hp2 hF
  have hunit : ∀ s : S, IsUnit ((algebraMap B Kt).comp F s) := by
    intro s
    obtain ⟨w, hw⟩ := hF (s : B)
    have hu : IsUnit (algebraMap B Kt (s : B) ^ p) :=
      (IsLocalization.map_units Kt s).pow p
    have hn : IsNilpotent ((p : Kt) * algebraMap B Kt w) := by
      refine ⟨2, ?_⟩
      have : (p : Kt) ^ 2 = 0 := by
        have := congrArg (algebraMap B Kt) hp2
        simpa using this
      rw [mul_pow, this, zero_mul]
    have := hn.isUnit_add_right_of_commute hu (Commute.all _ _)
    rw [add_comm] at this
    simpa [RingHom.comp_apply, hw, map_add (f := _), map_mul, map_pow, map_natCast] using this
  refine ⟨IsLocalization.lift hunit, fun b => by simp [IsLocalization.lift_eq], ?_⟩
  intro z
  obtain ⟨⟨b, s⟩, rfl⟩ := IsLocalization.mk'_surjective S z
  set z := IsLocalization.mk' Kt b s with hz
  set F' : Kt →+* Kt := IsLocalization.lift hunit
  have hF' : ∀ c, F' (algebraMap B Kt c) = algebraMap B Kt (F c) := fun c => by
    simp [F', IsLocalization.lift_eq]
  have hspec : z * algebraMap B Kt (s : B) = algebraMap B Kt b := IsLocalization.mk'_spec Kt b s
  obtain ⟨v, hv⟩ := hF b
  obtain ⟨u, hu⟩ := hF (s : B)
  have key : F' z * (algebraMap B Kt (s : B) ^ p + p * algebraMap B Kt u) =
      algebraMap B Kt b ^ p + p * algebraMap B Kt v := by
    have := congrArg F' hspec
    rw [map_mul, hF', hF', hu, hv] at this
    simpa [map_add (f := _), map_mul, map_pow, map_natCast] using this
  obtain ⟨t, ht⟩ := (IsLocalization.map_units Kt s).pow p
  refine ⟨(algebraMap B Kt v - F' z * algebraMap B Kt u) * ↑t⁻¹, ?_⟩
  have hzs : z ^ p * algebraMap B Kt (s : B) ^ p = algebraMap B Kt b ^ p := by
    rw [← mul_pow, hspec]
  have h1 : (F' z - z ^ p) * (t : Kt) = p * (algebraMap B Kt v - F' z * algebraMap B Kt u) := by
    rw [ht]; linear_combination key - hzs
  calc F' z = z ^ p + (F' z - z ^ p) * (t : Kt) * ↑t⁻¹ := by
        rw [mul_assoc, Units.mul_inv, mul_one]; ring
    _ = _ := by rw [h1]; ring

end GlobalTheory.DI
end

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace GlobalTheory GlobalTheory.DI GlobalTheory.LogDR GlobalTheory.LogPair GlobalTheory.Cartier ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.DI

theorem frobLift_stalk (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (U : Y.Opens) (hU : IsAffineOpen U)
    (F₀ : Γ(Y, U) →+* Γ(Y, U)) (hp2 : (p : Γ(Y, U)) ^ 2 = 0) (hF₀ : ∀ z, ∃ w, F₀ z = z ^ p + p * w)
    (y : Y) (hy : y ∈ U) :
    ∃ F : Y.presheaf.stalk y →+* Y.presheaf.stalk y,
      (∀ b, F ((Y.presheaf.germ U y hy).hom b) = (Y.presheaf.germ U y hy).hom (F₀ b)) ∧
        ∀ z, ∃ w, F z = z ^ p + p * w := by
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  exact frobLift_localization p (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl F₀ hp2 hF₀

theorem stalk_ringHom_ext {Y : Scheme.{0}} (U : Y.Opens) (hU : IsAffineOpen U) (y : Y) (hy : y ∈ U)
    {C : Type} [CommRing C] (f f' : Y.presheaf.stalk y →+* C)
    (h : ∀ b, f ((Y.presheaf.germ U y hy).hom b) = f' ((Y.presheaf.germ U y hy).hom b)) : f = f' := by
  letI : Algebra Γ(Y, U) (Y.presheaf.stalk y) := Y.presheaf.algebra_section_stalk (⟨y, hy⟩ : U)
  haveI : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hy⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hy⟩
  exact IsLocalization.ringHom_ext (hU.primeIdealOf ⟨y, hy⟩).asIdeal.primeCompl (RingHom.ext h)

theorem exists_frobLift_stalk_of_etCoord :
    ∀ (p : ℕ) [Fact p.Prime] {Y : Scheme.{0}} (g : Y ⟶ Sp (ZMod (p ^ 2))) (U : Y.Opens) {n : ℕ} (t : Fin n → Γ(Y, U)), IsAffineOpen U → IsEtCoord g U t → ∀ (η : Y) (hη : η ∈ U), ∃ F : Y.presheaf.stalk η →+* Y.presheaf.stalk η, (∀ z, ∃ w, F z = z ^ p + p * w) ∧ (∀ l, F ((Y.presheaf.germ U η hη).hom (t l)) = (Y.presheaf.germ U η hη).hom (t l) ^ p) ∧ ∀ (y : Y), y ∈ U → ∀ (h : η ⤳ y), ∀ z ∈ stalkIm h, ∃ w ∈ stalkIm h, F z = z ^ p + p * w := by
  intro p _ Y g U n t hU ht η hη
  obtain ⟨F₀, hF₀, hFt⟩ := frob_lift_etale_chart p _ ht
  have hp2 : (p : Γ(Y, U)) ^ 2 = 0 := by
    have h := map_natCast (cstOn g U) (p ^ 2)
    rw [ZMod.natCast_self, map_zero] at h
    rw [← Nat.cast_pow, ← h]
  obtain ⟨F, hFg, hF⟩ := frobLift_stalk p U hU F₀ hp2 hF₀ η hη
  refine ⟨F, hF, fun l => ?_, fun y hy h z hz => ?_⟩
  · have := hFt l
    rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_X] at this
    rw [hFg, this, map_pow]
  · obtain ⟨F', hFg', hF'⟩ := frobLift_stalk p U hU F₀ hp2 hF₀ y hy
    have hs : ∀ b, (Y.presheaf.stalkSpecializes h).hom ((Y.presheaf.germ U y hy).hom b) =
        (Y.presheaf.germ U η hη).hom b := fun b =>
      congrArg (fun k => k.hom b) (Y.presheaf.germ_stalkSpecializes hy h)
    have hc : F.comp (Y.presheaf.stalkSpecializes h).hom =
        (Y.presheaf.stalkSpecializes h).hom.comp F' := by
      apply stalk_ringHom_ext U hU y hy
      intro b
      rw [RingHom.comp_apply, RingHom.comp_apply, hs, hFg, hFg', hs]
    obtain ⟨a, rfl⟩ := hz
    obtain ⟨w, hw⟩ := hF' a
    refine ⟨_, ⟨w, rfl⟩, ?_⟩
    have := congrArg (· a) hc
    simp only [RingHom.comp_apply] at this
    rw [this, hw, map_add (f := _), map_mul, map_pow, map_natCast]

end GlobalTheory.DI
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTestProductSupportFiniteLeftCosets
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTestProductSupportFiniteLeftCosets
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.CosetFin

variable {H : Type} [Group H]

theorem finite_mk_mul (A K : Subgroup H) (x : H) (h : (K.map (MulAut.conj x).toMonoidHom).relIndex A ≠ 0) :
    {q : H ⧸ K | ∃ a ∈ A, q = (QuotientGroup.mk (a * x) : H ⧸ K)}.Finite := by
  set S := (K.map (MulAut.conj x).toMonoidHom).subgroupOf A
  haveI : S.FiniteIndex := ⟨h⟩
  haveI : Finite (A ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
  refine (Set.finite_range (fun t : A ⧸ S => (QuotientGroup.mk ((t.out : H) * x) : H ⧸ K))).subset ?_
  rintro q ⟨a, ha, rfl⟩
  refine ⟨(QuotientGroup.mk (⟨a, ha⟩ : A) : A ⧸ S), ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul S (⟨a, ha⟩ : A)
  simp only
  rw [hu]
  have hu2 : ((u : A) : H) ∈ K.map (MulAut.conj x).toMonoidHom := u.2
  obtain ⟨k, hk, hke⟩ := hu2
  rw [QuotientGroup.eq]
  have : ((u : A) : H) = x * k * x⁻¹ := by rw [← hke]; rfl
  simp only [Subgroup.coe_mul, this]
  have e : (a * (x * k * x⁻¹) * x)⁻¹ * (a * x) = k⁻¹ := by group
  rw [e]; exact K.inv_mem hk

theorem finite_mk_dcoset (K₀ K : Subgroup H) (hc : K.relIndex K₀ ≠ 0)
    (hconj : ∀ y : H, (K.map (MulAut.conj y).toMonoidHom).relIndex K₀ ≠ 0) (s : H) :
    {q : H ⧸ K | ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, q = (QuotientGroup.mk (k₁ * s * k₂) : H ⧸ K)}.Finite := by
  set T := K.subgroupOf K₀
  haveI : T.FiniteIndex := ⟨hc⟩
  haveI : Finite (K₀ ⧸ T) := Subgroup.finite_quotient_of_finiteIndex
  refine (Set.finite_iUnion (fun t : K₀ ⧸ T => finite_mk_mul K₀ K (s * (t.out : H)) (hconj _))).subset ?_
  rintro q ⟨k₁, hk₁, k₂, hk₂, rfl⟩
  refine Set.mem_iUnion.2 ⟨(QuotientGroup.mk (⟨k₂, hk₂⟩ : K₀) : K₀ ⧸ T), k₁, hk₁, ?_⟩
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul T (⟨k₂, hk₂⟩ : K₀)
  rw [hu, QuotientGroup.eq]
  have hu2 : ((u : K₀) : H) ∈ K := u.2
  simp only [Subgroup.coe_mul]
  have e : (k₁ * s * k₂)⁻¹ * (k₁ * (s * (k₂ * ((u : K₀) : H)))) = ((u : K₀) : H) := by group
  rw [e]; exact hu2

theorem finite_mk_support (K₀ K : Subgroup H) (hc : K.relIndex K₀ ≠ 0)
    (hconj : ∀ y : H, (K.map (MulAut.conj y).toMonoidHom).relIndex K₀ ≠ 0) (φ : H → ℂ) (S : Finset H)
    (hS : ∀ g, φ g ≠ 0 → ∃ s ∈ S, ∃ k₁ ∈ K₀, ∃ k₂ ∈ K₀, g = k₁ * s * k₂) :
    {q : H ⧸ K | ∃ g, φ g ≠ 0 ∧ q = (QuotientGroup.mk g : H ⧸ K)}.Finite := by
  refine (S.finite_toSet.biUnion fun s _ => finite_mk_dcoset K₀ K hc hconj s).subset ?_
  rintro q ⟨g, hg, rfl⟩
  obtain ⟨s, hs, k₁, hk₁, k₂, hk₂, rfl⟩ := hS g hg
  exact Set.mem_biUnion hs ⟨k₁, hk₁, k₂, hk₂, rfl⟩

theorem relIndex_ne_zero_open_compact {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U K : Subgroup G) (hU : IsOpen (U : Set G)) (hK : IsCompact (K : Set G)) : U.relIndex K ≠ 0 := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  haveI : Finite (K ⧸ U.subgroupOf K) :=
    Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  exact Subgroup.index_ne_zero_of_finite

theorem isOpen_map_conj {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (U : Subgroup G) (hU : IsOpen (U : Set G)) (y : G) :
    IsOpen ((U.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) := by
  have e : ((U.map (MulAut.conj y).toMonoidHom : Subgroup G) : Set G) = (fun g => y⁻¹ * g * y) ⁻¹' (U : Set G) := by
    ext g
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage]
    constructor
    · rintro ⟨k, hk, rfl⟩
      have : y⁻¹ * ((MulAut.conj y).toMonoidHom k) * y = k := by
        show y⁻¹ * (y * k * y⁻¹) * y = k; group
      rw [this]; exact hk
    · intro h
      refine ⟨_, h, ?_⟩
      show y * (y⁻¹ * g * y) * y⁻¹ = g; group
  rw [e]
  exact hU.preimage ((continuous_const.mul continuous_id).mul continuous_const)

end GlobalTheory.CosetFin

namespace GlobalTheory.CosetFin

theorem commensurable_map_conj {G : Type} [Group G] {A B : Subgroup G} (h : A.Commensurable B) (y : G) :
    (A.map (MulAut.conj y).toMonoidHom).Commensurable (B.map (MulAut.conj y).toMonoidHom) := by
  exact ⟨h.1.map _, h.2.map _⟩

end GlobalTheory.CosetFin


open GlobalTheory.CosetFin in
theorem GlobalTheory.testProd_support_finite : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      (Function.support (fun q : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) =>
        f q.out.1 * f' q.out.2)).Finite := by
  intro p _ G L f hf _ K' f' hf' _
  obtain ⟨-, -, -, S, hS⟩ := hf
  obtain ⟨hc', -, -, S', hS'⟩ := hf'

  have hA : {a : G.GAf ⧸ L.K.toSubgroup | ∃ g, f g ≠ 0 ∧ a = (QuotientGroup.mk g : G.GAf ⧸ L.K.toSubgroup)}.Finite := by
    refine finite_mk_support L.K.toSubgroup L.K.toSubgroup ?_ ?_ f S hS
    · rw [Subgroup.relIndex_self]; exact one_ne_zero
    · intro y
      exact relIndex_ne_zero_open_compact _ _ (isOpen_map_conj _ L.K.isOpen y) L.compact

  have hB : {b : Gr G 1 ⧸ K' | ∃ g, f' g ≠ 0 ∧ b = (QuotientGroup.mk g : Gr G 1 ⧸ K')}.Finite := by
    refine finite_mk_support (KHT p G.m G.n 1 G.Fw) K' hc'.1.relIndex_ne_zero ?_ f' S' hS'
    intro y
    have h1 := (GlobalTheory.heckeOperator_integral p G 1 Nat.one_pos).1 y
    exact ((commensurable_map_conj hc' y).trans h1).1.relIndex_ne_zero
  let ψ : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) →
      (G.GAf ⧸ L.K.toSubgroup) × (Gr G 1 ⧸ K') :=
    fun q => ((QuotientGroup.mk q.out.1 : G.GAf ⧸ L.K.toSubgroup), (QuotientGroup.mk q.out.2 : Gr G 1 ⧸ K'))
  have hψ : Function.Injective ψ := by
    intro q r hqr
    simp only [ψ, Prod.mk.injEq, QuotientGroup.eq] at hqr
    rw [← QuotientGroup.out_eq' q, ← QuotientGroup.out_eq' r]
    apply QuotientGroup.eq.2
    exact Subgroup.mem_prod.2 ⟨by simpa using hqr.1, by simpa using hqr.2⟩
  refine ((hA.prod hB).preimage hψ.injOn).subset ?_
  intro q hq
  have h1 : f q.out.1 ≠ 0 := left_ne_zero_of_mul hq
  have h2 : f' q.out.2 ≠ 0 := right_ne_zero_of_mul hq
  exact ⟨⟨_, h1, rfl⟩, ⟨_, h2, rfl⟩⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeTestProductSupportFiniteLeftCosetsStatement
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeTestProduct_support_finite_leftCosets : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ),
    IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f →
      (∀ k ∈ L.K.toSubgroup, ∀ k' ∈ L.K.toSubgroup, ∀ g, f (k * g * k') = f g) →
    ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' →
      (∀ k ∈ K', ∀ k' ∈ K', ∀ g, f' (k * g * k') = f' g) →
      (Function.support (fun q : (G.GAf × Gr G 1) ⧸ (L.K.toSubgroup.prod K' : Subgroup (G.GAf × Gr G 1)) =>
        f q.out.1 * f' q.out.2)).Finite := by
  first | exact @GlobalTheory.testProd_support_finite | exact GlobalTheory.testProd_support_finite | (intros; apply GlobalTheory.testProd_support_finite <;> assumption)
end
end
