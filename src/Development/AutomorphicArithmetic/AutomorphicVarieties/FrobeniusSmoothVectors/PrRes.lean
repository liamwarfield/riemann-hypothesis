module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocRho
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PointLoc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.MonMemPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.LocDim

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.PrRes
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem residue_eq_map_algebraMap_comp_res_of_isCO {O' C : Type} [CommRing O'] [IsLocalRing O'] [CommRing C] [Algebra O' C]
    [IsCO O' C] [IsLocalHom (algebraMap O' C)] :
    IsLocalRing.residue C =
      (IsLocalRing.ResidueField.map (algebraMap O' C)).comp (res O' C : C →+* ResidueField O') := by
  ext z
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O') z
  have h1 : (res O' C) z = (res O' C) (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
    exact ha
  have h2 : IsLocalRing.residue C z = IsLocalRing.residue C (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact ha
  rw [RingHom.comp_apply, RingHom.coe_coe, h1, h2, AlgHom.commutes]
  exact (IsLocalRing.ResidueField.map_residue _ a).symm

private theorem nRep_isBar_of_isBar_comp_map {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {K K' : Type} [Field K] [CommRing K'] [Nontrivial K'] (f : k →+* K) (j : K →+* K')
    (σ : NRep F n K) (h : NRep.IsBar (j.comp f) (NRep.map j σ)) : NRep.IsBar f σ := by
  unfold NRep.IsBar at h ⊢
  exact ⟨fun g i => j.injective (h.1 g i), fun v i g => j.injective (h.2 v i g)⟩

theorem UpperTheory.V.Fr.pr_res :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), (∃ φ : ResidueField O →+* ResidueField L.O', (L.ρ.bar L.O').IsBar φ) ∧ ((∀ g, UpT ((L.ρ.bar L.O').r g)) ∨ ∀ g, UpT ((L.ρ.bar L.O').r g)ᵀ) := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L
  have hOloc : IsLocalHom (algebraMap O L.O') := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have hm : algebraMap O L.O' a ∈ maximalIdeal L.O' := by
      rw [← L.unr]
      exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap L.O' L.R) := IsCO.isLocalHom
  let f0 : ResidueField O →+* ResidueField L.O' := IsLocalRing.ResidueField.map (algebraMap O L.O')
  let jR : ResidueField L.O' →+* ResidueField L.R :=
    IsLocalRing.ResidueField.map (algebraMap L.O' L.R)
  have hloc := loc_rho hF hn S x L
  refine ⟨⟨f0, ?_⟩, ?_⟩
  · have hfR : IsResMap O L.R (jR.comp f0) := by
      intro a
      show jR (f0 (IsLocalRing.residue O a)) = _
      rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
        IsScalarTower.algebraMap_apply O L.O' L.R a]
    have hbR := hloc.2.1 _ hfR
    rw [residue_eq_map_algebraMap_comp_res_of_isCO (O' := L.O') (C := L.R)] at hbR
    exact nRep_isBar_of_isBar_comp_map f0 jR _ hbR
  · by_cases hP : S.u.triP ≤ x
    · left
      have hle : L.ρ.triP ≤ maximalIdeal L.R := by
        rw [(hloc.2.2.1 (maximalIdeal L.R)).1]
        show S.u.triP ≤ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R)
        rw [L.lies]
        exact hP
      intro g i j hji
      have hm : L.ρ.r g i j ∈ maximalIdeal L.R := by
        refine hle ?_
        unfold NRep.triP
        exact Ideal.subset_span ⟨g, i, j, hji, rfl⟩
      show res L.O' L.R (L.ρ.r g i j) = 0
      exact (res_eq_zero_iff _ _ _).mpr hm
    · right
      have hle := (hloc.2.2.2 hP).2
      intro g i j hji
      have hm : L.ρ.r g j i ∈ maximalIdeal L.R := by
        refine hle ?_
        unfold NRep.triM
        exact Ideal.subset_span ⟨g, j, i, hji, rfl⟩
      show res L.O' L.R (L.ρ.r g j i) = 0
      exact (res_eq_zero_iff _ _ _).mpr hm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.DefIso
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.ExtA
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.ext_A :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [IsLocalRing C] [IsNoetherianRing C] [Algebra O C] (ξ ξ' : S.A →ₐ[O] C), S.u.map (ξ : S.A →+* C) = S.u.map (ξ' : S.A →+* C) → S.x0 ≤ (maximalIdeal C).comap (ξ : S.A →+* C) → S.x0 ≤ (maximalIdeal C).comap (ξ' : S.A →+* C) → ξ = ξ' := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ _ ξ ξ' hu h1 h2
  obtain ⟨-, -, -, hc⟩ := UpperTheory.V.Fr.cont_u hF hn S
  let E : Subalgebra O S.R := (AlgHom.equalizer ξ ξ').map S.A.val
  have hE : ∀ a : S.A, (a : S.R) ∈ E ↔ ξ a = ξ' a := fun a =>
    ⟨fun ⟨b, hb, h⟩ => (Subtype.ext h : b = a) ▸ hb, fun h => ⟨a, h, rfl⟩⟩
  have hr : ∀ g i j, S.ρ.r g i j ∈ E := fun g i j =>
    (hE (S.u.r g i j)).2 (congrArg (fun ρ : NRep F n C => ρ.r g i j) hu)
  have hψ : ∀ v i g, (S.ρ.ψ v i g : S.R) ∈ E := fun v i g =>
    (hE (S.u.ψ v i g : S.A)).2 (congrArg (fun ρ : NRep F n C => (ρ.ψ v i g : C)) hu)
  have h0 : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤ E := by
    refine Algebra.adjoin_le ?_
    rintro x (⟨L, -, rfl⟩ | ⟨v, i, g, rfl⟩)
    · refine Subalgebra.list_prod_mem E fun y hy => ?_
      obtain ⟨s, -, rfl⟩ := List.mem_map.1 hy
      exact hr _ _ _
    · exact hψ v i g
  have hpow : ∀ (f : S.A →ₐ[O] C), S.x0 ≤ (maximalIdeal C).comap (f : S.A →+* C) → ∀ (N : ℕ) (a : S.A),
      a ∈ S.mB ^ N • S.gr 0 → f a ∈ maximalIdeal C ^ N := by
    intro f hf N a ha
    refine Submodule.smul_induction_on ha (fun b hb y _ => ?_) fun x y hx hy => ?_
    · rw [Algebra.smul_def, map_mul]
      refine Ideal.mul_mem_right _ _ ?_
      have h3 : algebraMap S.B S.A b ∈ S.x0 ^ N := by
        have := Ideal.mem_map_of_mem (S.inc : S.B →+* S.A) hb
        rw [Ideal.map_pow] at this
        exact this
      have h4 := Ideal.pow_right_mono hf N h3
      exact Ideal.le_comap_pow (f : S.A →+* C) N h4
    · rw [map_add (f := _)]
      exact add_mem hx hy
  have hB : S.B ≤ E := by
    intro b hb
    refine (hE ⟨b, S.B_le_A hb⟩).2 ?_
    rw [← sub_eq_zero, ← Ideal.mem_bot,
      ← Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal C) (maximalIdeal.isMaximal C).ne_top, Ideal.mem_iInf]
    intro N
    obtain ⟨M, hM⟩ := hc 0 N
    obtain ⟨y, hy, hby⟩ := hb M
    have hyB : y ∈ S.B := le_adicClosure _ hy
    have hg : S.inc ⟨b - y, sub_mem hb hyB⟩ ∈ S.gr 0 := by
      have h5 : (1 : S.A) ∈ S.gr 0 := Submodule.subset_span ⟨[], by simp, by simp⟩
      have h6 := Submodule.smul_mem _ (⟨b - y, sub_mem hb hyB⟩ : S.B) h5
      rw [Algebra.smul_def, mul_one] at h6
      exact h6
    have hm := hM _ hg hby
    have he : ξ ⟨y, S.B_le_A hyB⟩ = ξ' ⟨y, S.B_le_A hyB⟩ := (hE _).1 (h0 hy)
    have hs : (⟨b, S.B_le_A hb⟩ : S.A) = S.inc ⟨b - y, sub_mem hb hyB⟩ + ⟨y, S.B_le_A hyB⟩ :=
      Subtype.ext (sub_add_cancel b y).symm
    rw [hs, map_add (f := _), map_add (f := _), he, add_sub_add_right_eq_sub]
    exact sub_mem (hpow ξ h1 N _ hm) (hpow ξ' h2 N _ hm)
  have hA : S.A ≤ E := by
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨g, i, j, rfl⟩)
    · exact hB hx
    · exact hr g i j
  exact AlgHom.ext fun a => (hE a).1 (hA a.2)
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem residue_eq_residueField_map_comp_res {O' C : Type} [CommRing O'] [IsLocalRing O'] [CommRing C] [Algebra O' C]
    [IsCO O' C] [IsLocalHom (algebraMap O' C)] :
    IsLocalRing.residue C =
      (IsLocalRing.ResidueField.map (algebraMap O' C)).comp (res O' C : C →+* ResidueField O') := by
  ext z
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O') z
  have h1 : (res O' C) z = (res O' C) (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, res_eq_zero_iff]
    exact ha
  have h2 : IsLocalRing.residue C z = IsLocalRing.residue C (algebraMap O' C a) := by
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff]
    exact ha
  rw [RingHom.comp_apply, RingHom.coe_coe, h1, h2, AlgHom.commutes]
  exact (IsLocalRing.ResidueField.map_residue _ a).symm

private theorem nRep_isBar_comp_map_iff {l : ℕ} [Fact l.Prime] {k : Type} [Field k] {F : Frame l k} {n : ℕ}
    {K K' : Type} [Field K] [CommRing K'] [Nontrivial K'] (f : k →+* K) (j : K →+* K')
    (σ : NRep F n K) : NRep.IsBar (j.comp f) (NRep.map j σ) ↔ NRep.IsBar f σ := by
  unfold NRep.IsBar
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun g i => j.injective (h1 g i), fun v i g => j.injective (h2 v i g)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun g i => congrArg j (h1 g i), fun v i g => congrArg j (h2 v i g)⟩

theorem UpperTheory.V.Fr.def_iso :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (x : Ideal S.A) (L : S.Loc x), ∀ (C : Type) [CommRing C] [Algebra L.O' C] [IsCO L.O' C] (ρ : NRep F n C), ρ.Cont (maximalIdeal C) → ρ.map (res L.O' C : C →+* ResidueField L.O') = L.ρ.map (res L.O' L.R : L.R →+* ResidueField L.O') → ∃! g : L.R →ₐ[L.O'] C, L.ρ.map (g : L.R →+* C) = ρ := by
  intro l _ O _ _ _ _ F C₀ n hF hn S x L C _ _ _ ρ hc hres
  have hOloc : IsLocalHom (algebraMap O L.O') := by
    refine ⟨fun a ha => ?_⟩
    by_contra h
    have hm : algebraMap O L.O' a ∈ maximalIdeal L.O' := by
      rw [← L.unr]
      exact Ideal.mem_map_of_mem _ ((IsLocalRing.mem_maximalIdeal a).mpr h)
    exact (IsLocalRing.mem_maximalIdeal _).mp hm ha
  haveI : IsLocalHom (algebraMap L.O' C) := IsCO.isLocalHom
  haveI : IsLocalHom (algebraMap L.O' L.R) := IsCO.isLocalHom
  letI : Algebra O C := ((algebraMap L.O' C).comp (algebraMap O L.O')).toAlgebra
  haveI : IsScalarTower O L.O' C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have hCloc : IsLocalHom (algebraMap O C) :=
    inferInstanceAs (IsLocalHom ((algebraMap L.O' C).comp (algebraMap O L.O')))
  have hCL : UpperTheory.V.CA.IsCL O C := by
    refine ⟨inferInstance, IsCO.complete (O := L.O'), hCloc, ?_⟩
    let φ : L.O' →ₐ[O] ResidueField C :=
      (IsScalarTower.toAlgHom O C (ResidueField C)).comp (IsScalarTower.toAlgHom O L.O' C)
    refine Module.Finite.of_surjective φ.toLinearMap ?_
    intro y
    obtain ⟨z, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨a, ha⟩ := IsCO.res_surj (O := L.O') z
    refine ⟨a, ?_⟩
    show IsLocalRing.residue C (algebraMap L.O' C a) = IsLocalRing.residue C z
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, ← neg_sub]
    exact neg_mem ha
  let f0 : ResidueField O →+* ResidueField L.O' := IsLocalRing.ResidueField.map (algebraMap O L.O')
  let jC : ResidueField L.O' →+* ResidueField C := IsLocalRing.ResidueField.map (algebraMap L.O' C)
  let jR : ResidueField L.O' →+* ResidueField L.R :=
    IsLocalRing.ResidueField.map (algebraMap L.O' L.R)
  have hfC : IsResMap O C (jC.comp f0) := by
    intro a
    show jC (f0 (IsLocalRing.residue O a)) = _
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue]
    rfl
  have hfR : IsResMap O L.R (jR.comp f0) := by
    intro a
    show jR (f0 (IsLocalRing.residue O a)) = _
    rw [IsLocalRing.ResidueField.map_residue, IsLocalRing.ResidueField.map_residue,
      IsScalarTower.algebraMap_apply O L.O' L.R a]
  have hbR := (loc_rho hF hn S x L).2.1 _ hfR
  rw [residue_eq_residueField_map_comp_res (O' := L.O') (C := L.R)] at hbR
  have hσ : NRep.IsBar f0 (NRep.map (res L.O' L.R : L.R →+* ResidueField L.O') L.ρ) :=
    (nRep_isBar_comp_map_iff f0 jR _).mp hbR
  have hbar : NRep.IsBar (jC.comp f0) (NRep.map (IsLocalRing.residue C) ρ) := by
    rw [residue_eq_residueField_map_comp_res (O' := L.O') (C := C)]
    show NRep.IsBar (jC.comp f0) (NRep.map jC (NRep.map (res L.O' C : C →+* ResidueField L.O') ρ))
    rw [hres]
    exact (nRep_isBar_comp_map_iff f0 jC _).mpr hσ
  obtain ⟨ξ, hξ, hξx⟩ := point_loc hF hn S C hCL (jC.comp f0) hfC ρ hc hbar
  have hx0 : S.x0 ≤ x := by
    unfold Space.x0
    exact Ideal.map_le_iff_le_comap.mpr (loc_flat hF hn S x L).2.2
  let ξ1 : S.A →ₐ[O] ResidueField L.O' := ((res L.O' C).restrictScalars O).comp ξ
  let ξ2 : S.A →ₐ[O] ResidueField L.O' := ((res L.O' L.R).restrictScalars O).comp L.ι
  have h12 : ξ1 = ξ2 := by
    refine ext_A hF hn S (ResidueField L.O') ξ1 ξ2 ?_ ?_ ?_
    · exact (congrArg (NRep.map (res L.O' C : C →+* ResidueField L.O')) hξ).trans hres
    · intro a ha
      refine Ideal.mem_comap.mpr ?_
      show res L.O' C (ξ a) ∈ _
      rw [(res_eq_zero_iff L.O' C (ξ a)).mpr (hξx ha)]
      exact zero_mem _
    · intro a ha
      have hm : a ∈ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R) := by
        rw [L.lies]
        exact hx0 ha
      refine Ideal.mem_comap.mpr ?_
      show res L.O' L.R (L.ι a) ∈ _
      rw [(res_eq_zero_iff L.O' L.R (L.ι a)).mpr hm]
      exact zero_mem _
  obtain ⟨g, hg, huniq⟩ := L.univ C ξ (fun a => AlgHom.congr_fun h12 a)
  have hgι : (g : L.R →+* C).comp (L.ι : S.A →+* L.R) = (ξ : S.A →+* C) := RingHom.ext hg
  refine ⟨g, ?_, fun g' hg' => huniq g' ?_⟩
  · show NRep.map ((g : L.R →+* C).comp (L.ι : S.A →+* L.R)) S.u = ρ
    rw [hgι]
    exact hξ
  · let ξ' : S.A →ₐ[O] C := (g'.restrictScalars O).comp L.ι
    have h' : ξ' = ξ := by
      refine ext_A hF hn S C ξ' ξ ?_ ?_ hξx
      · exact hg'.trans hξ.symm
      · intro a ha
        have hm : a ∈ Ideal.comap (L.ι : S.A →+* L.R) (maximalIdeal L.R) := by
          rw [L.lies]
          exact hx0 ha
        refine Ideal.mem_comap.mpr ?_
        show g' (L.ι a) ∈ maximalIdeal C
        rw [← res_eq_zero_iff L.O' C, res_map]
        exact (res_eq_zero_iff L.O' L.R _).mpr hm
    intro a
    exact AlgHom.congr_fun h' a
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Seedpt
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.FrobeniusCornerLiftTwoToThree
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

private theorem ex_core {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A) [GradedAlgebra 𝒜]
    (h0 : 𝒜 0 = 1) (hinj : Function.Injective (algebraMap B A)) (p : Ideal B) [p.IsPrime] :
    ∃ η : Ideal A, η.IsPrime ∧ η.IsHomogeneous 𝒜 ∧ η.comap (algebraMap B A) = p := by
  classical
  have key : ∀ x ∈ Ideal.map (algebraMap B A) p, ∃ c ∈ p, GradedAlgebra.proj 𝒜 0 x = algebraMap B A c := by
    intro x hx
    have hx' : x ∈ (p • (⊤ : Submodule B A)) := by
      rw [Ideal.smul_top_eq_map]
      exact hx
    refine Submodule.smul_induction_on (p := fun x => ∃ c ∈ p, GradedAlgebra.proj 𝒜 0 x = algebraMap B A c)
      hx' ?_ ?_
    · intro b hb y _
      have hy : GradedAlgebra.proj 𝒜 0 y ∈ 𝒜 0 := by
        rw [GradedAlgebra.proj_apply]
        exact SetLike.coe_mem _
      rw [h0] at hy
      obtain ⟨c, hc⟩ := Submodule.mem_one.mp hy
      refine ⟨b * c, p.mul_mem_right c hb, ?_⟩
      rw [LinearMap.map_smul, ← hc, Algebra.smul_def, map_mul]
    · intro x y hx hy
      obtain ⟨c, hc, hxc⟩ := hx
      obtain ⟨d, hd, hyd⟩ := hy
      exact ⟨c + d, p.add_mem hc hd, by rw [map_add (f := _), hxc, hyd, map_add (f := _)]⟩
  have hdisj : Disjoint ((Ideal.map (algebraMap B A) p : Ideal A) : Set A)
      (Algebra.algebraMapSubmonoid A p.primeCompl : Set A) := by
    rw [Set.disjoint_left]
    rintro x hxJ ⟨s, hs, rfl⟩
    obtain ⟨c, hc, he⟩ := key _ hxJ
    rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (SetLike.algebraMap_mem_graded 𝒜 s)] at he
    exact hs (by rw [hinj he]; exact hc)
  obtain ⟨P, hP, hJP, hPd⟩ := Ideal.exists_le_prime_disjoint _ _ hdisj
  refine ⟨(P.homogeneousCore 𝒜).toIdeal, Ideal.IsPrime.homogeneousCore (𝒜 := 𝒜) hP,
    (P.homogeneousCore 𝒜).isHomogeneous, ?_⟩
  apply le_antisymm
  · intro b hb
    rw [Ideal.mem_comap] at hb
    have hbP : algebraMap B A b ∈ P := Ideal.toIdeal_homogeneousCore_le 𝒜 P hb
    by_contra hnb
    exact Set.disjoint_left.mp hPd hbP ⟨b, hnb, rfl⟩
  · intro b hb
    rw [Ideal.mem_comap]
    exact Ideal.mem_homogeneousCore_of_homogeneous_of_mem ⟨0, SetLike.algebraMap_mem_graded 𝒜 b⟩
      (hJP (Ideal.mem_map_of_mem _ hb))

private theorem one_le_td {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    [GradedAlgebra 𝒜] (η : Ideal A) (hη : η.IsPrime) (hh : η.IsHomogeneous 𝒜) {a : A} {α : ℤ} (ha : a ∈ 𝒜 α)
    (hα : α ≠ 0) (ha' : a ∉ η) : 1 ≤ Algebra.trdeg (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := by
  classical
  have key : ∀ Q : Polynomial B, Polynomial.aeval a Q ∈ η → ∀ k, Q.coeff k ∈ η.comap (algebraMap B A) := by
    intro Q hQ k
    have hn : Q.natDegree < Q.natDegree + k + 1 := by omega
    rw [Polynomial.aeval_eq_sum_range' hn] at hQ
    have hmem : ∀ i : ℕ, Q.coeff i • a ^ i ∈ 𝒜 (i • α) := fun i =>
      Submodule.smul_mem _ _ (SetLike.pow_mem_graded i ha)
    have h2 : GradedAlgebra.proj 𝒜 (k • α)
        (∑ i ∈ Finset.range (Q.natDegree + k + 1), Q.coeff i • a ^ i) ∈ η := by
      rw [GradedAlgebra.proj_apply]
      exact (Ideal.IsHomogeneous.mem_iff 𝒜 hh).1 hQ _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single k] at h2
    · rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_same 𝒜 (hmem k), Algebra.smul_def] at h2
      rcases hη.mem_or_mem h2 with h | h
      · exact h
      · exact absurd (hη.mem_of_pow_mem _ h) ha'
    · intro i _ hik
      rw [GradedAlgebra.proj_apply, DirectSum.decompose_of_mem_ne 𝒜 (hmem i)]
      intro he
      apply hik
      have he' : (i : ℤ) * α = (k : ℤ) * α := by simpa [nsmul_eq_mul] using he
      exact_mod_cast mul_right_cancel₀ hα he'
    · intro hk
      exact absurd (Finset.mem_range.2 (by omega)) hk
  have htr : Transcendental (B ⧸ η.comap (algebraMap B A)) (Ideal.Quotient.mk η a) := by
    rw [transcendental_iff]
    intro P hP
    obtain ⟨Q, rfl⟩ := Polynomial.map_surjective (Ideal.Quotient.mk (η.comap (algebraMap B A)))
      Ideal.Quotient.mk_surjective P
    have e : Polynomial.aeval (Ideal.Quotient.mk η a) (Q.map (Ideal.Quotient.mk (η.comap (algebraMap B A))))
        = Ideal.Quotient.mk η (Polynomial.aeval a Q) := by
      have e1 := Polynomial.aeval_map_algebraMap (B ⧸ η.comap (algebraMap B A)) (Ideal.Quotient.mk η a) Q
      rw [Ideal.Quotient.algebraMap_eq] at e1
      rw [e1, ← Ideal.Quotient.mkₐ_eq_mk B η, Polynomial.aeval_algHom_apply]
    rw [e, Ideal.Quotient.eq_zero_iff_mem] at hP
    ext k
    rw [Polynomial.coeff_map, Polynomial.coeff_zero, Ideal.Quotient.eq_zero_iff_mem]
    exact key Q hP k
  haveI : Algebra.Transcendental (B ⧸ η.comap (algebraMap B A)) (A ⧸ η) := ⟨⟨_, htr⟩⟩
  exact Cardinal.one_le_iff_pos.2 (trdeg_pos _ _)

private theorem pair {B A : Type} [CommRing B] [CommRing A] [Algebra B A] (𝒜 : ℤ → Submodule B A)
    [SetLike.GradedMonoid 𝒜] (h0 : 𝒜 0 = 1) {ξ η : Ideal A} (hξ : ξ.IsPrime)
    (hle : η.comap (algebraMap B A) ≤ ξ.comap (algebraMap B A)) {a b : A} {α β : ℤ} (ha : a ∈ 𝒜 α) (hb : b ∈ 𝒜 β)
    (hα : 0 < α) (hβ : β < 0) (ha' : a ∉ ξ) (hb' : b ∉ ξ) : a ∉ η ∧ b ∉ η := by
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (m : ℤ) = α := ⟨α.toNat, Int.toNat_of_nonneg hα.le⟩
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : ℤ) = -β := ⟨(-β).toNat, Int.toNat_of_nonneg (by omega)⟩
  have hm0 : 0 < m := by omega
  have hk0 : 0 < k := by omega
  have hmem : a ^ k * b ^ m ∈ 𝒜 0 := by
    have h1 := SetLike.mul_mem_graded (SetLike.pow_mem_graded k ha) (SetLike.pow_mem_graded m hb)
    have he : k • α + m • β = 0 := by
      rw [nsmul_eq_mul, nsmul_eq_mul, hk, hm]
      ring
    rwa [he] at h1
  rw [h0] at hmem
  obtain ⟨x, hx⟩ := Submodule.mem_one.mp hmem
  have hc : a ^ k * b ^ m ∉ ξ := by
    intro hin
    rcases hξ.mem_or_mem hin with h | h
    · exact ha' (hξ.mem_of_pow_mem _ h)
    · exact hb' (hξ.mem_of_pow_mem _ h)
  have hxξ : x ∉ ξ.comap (algebraMap B A) := by
    rw [Ideal.mem_comap, hx]
    exact hc
  have hxη : x ∉ η.comap (algebraMap B A) := fun hin => hxξ (hle hin)
  rw [Ideal.mem_comap, hx] at hxη
  constructor
  · intro hin
    exact hxη (Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ hin _ hk0))
  · intro hin
    exact hxη (Ideal.mul_mem_left _ _ (Ideal.pow_mem_of_mem _ hin _ hm0))

private theorem w_lt {n : ℕ} {i j : Fin n} (h : i < j) : w n j < w n i := by
  have : (i : ℕ) < j := h
  unfold w
  split_ifs <;> omega

theorem UpperTheory.V.Fr.frobenius_corner_lift_two_to_three :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (p : Ideal S.B) (ξ : Ideal S.A), p.IsPrime → ξ.IsPrime → S.u.TI ξ → p ≤ S.π ξ → ∃ η : Ideal S.A, η.IsPrime ∧ S.IsHom η ∧ S.π η = p ∧ S.u.TI η ∧ S.td η = 1 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S p ξ hp hξ hTI hle
  obtain ⟨hint, hgm, h0, -, -, -, hr⟩ := gr_A hF hn S
  letI : GradedAlgebra S.gr := { hgm, hint.chooseDecomposition with }
  have hinj : Function.Injective (algebraMap S.B S.A) := by
    intro x y hxy
    apply Subtype.ext
    exact congrArg (fun z : S.A => (z : S.R)) hxy
  obtain ⟨η, hηp, hηh, hηc⟩ := ex_core S.gr h0 hinj p
  have hP := hTI.1.1
  have hM := hTI.1.2
  simp only [NRep.triP, NRep.triM, Ideal.span_le, Set.not_subset] at hP hM
  obtain ⟨_, ⟨g, i, j, hji, rfl⟩, hb⟩ := hP
  obtain ⟨_, ⟨g', i', j', hij', rfl⟩, ha⟩ := hM
  have hbd : w n i - w n j < 0 := by have := w_lt hji; omega
  have had : 0 < w n i' - w n j' := by have := w_lt hij'; omega
  have hle' : η.comap (algebraMap S.B S.A) ≤ ξ.comap (algebraMap S.B S.A) := by
    rw [hηc]; exact hle
  have hab := pair S.gr h0 hξ hle' (hr g' i' j') (hr g i j) had hbd ha hb
  refine ⟨η, hηp, ?_, hηc, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · apply le_antisymm
    · have e := (Ideal.IsHomogeneous.iff_eq S.gr η).mp hηh
      calc η = _ := e.symm
        _ ≤ _ := Ideal.span_mono ?_
      rintro _ ⟨⟨x, hxh⟩, hx, rfl⟩
      exact ⟨hx, hxh⟩
    · exact Ideal.span_le.2 fun x hx => hx.1
  · intro h
    exact hab.2 (h (Ideal.subset_span ⟨g, i, j, hji, rfl⟩))
  · intro h
    exact hab.1 (h (Ideal.subset_span ⟨g', i', j', hij', rfl⟩))
  · intro h3 h
    have hE := hTI.2 h3
    simp only [NRep.ee, Ideal.span_le, Set.not_subset] at hE
    obtain ⟨_, ⟨g'', i'', j'', hodd, rfl⟩, hc⟩ := hE
    have hne : w n i'' - w n j'' ≠ 0 := by
      rintro h0'
      rw [h0'] at hodd
      exact (Int.not_odd_iff_even.2 ⟨0, by norm_num⟩) hodd
    have hcη : S.u.r g'' i'' j'' ∉ η := by
      rcases lt_or_gt_of_ne hne with hneg | hpos
      · exact (pair S.gr h0 hξ hle' (hr g' i' j') (hr g'' i'' j'') had hneg ha hc).2
      · exact (pair S.gr h0 hξ hle' (hr g'' i'' j'') (hr g i j) hpos hbd hc hb).1
    exact hcη (h (Ideal.subset_span ⟨g'', i'', j'', hodd, rfl⟩))
  · exact le_antisymm (fibre hF hn S η hηp ⟨fun h => hab.2 (h (Ideal.subset_span ⟨g, i, j, hji, rfl⟩)),
      fun h => hab.1 (h (Ideal.subset_span ⟨g', i', j', hij', rfl⟩))⟩)
      (one_le_td S.gr η hηp hηh (hr g' i' j') had.ne' hab.1)
end

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr

theorem UpperTheory.V.Fr.seedpt :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (p : Ideal S.B) (ξ : Ideal S.A), p.IsPrime → ξ.IsPrime → S.u.TI ξ → p ≤ S.π ξ → ∃ x : PrimeSpectrum S.A, x.asIdeal.IsMaximal ∧ x ∈ S.BB ∧ ∀ L : S.Loc x.asIdeal, ∃ P : Ideal L.R, P.IsPrime ∧ L.ρ.TI P ∧ L.π P = p ∧ ringKrullDim (L.R ⧸ P) = ringKrullDim (S.B ⧸ p) + 1 := by
  intro l _ O _ _ _ _ F C₀ n hF hn S p ξ hp hξ hTI hpξ
  obtain ⟨η, hηp, hhom, hπ, hTIη, htd⟩ := frobenius_corner_lift_two_to_three hF hn S p ξ hp hξ hTI hpξ
  have hTIη' := hTIη
  unfold NRep.TI NRep.OffTri at hTIη'
  obtain ⟨x, hxmax, hxBB, hηx⟩ := l41 hF hn S η hηp hhom hTIη'.1.1
  refine ⟨x, hxmax, hxBB, fun L => ?_⟩
  have htd' : S.td η = ((1 : ℕ) : _) := by
    rw [htd]
    rfl
  obtain ⟨P, hP, himP, hdim⟩ := (loc_dim hF hn S x.asIdeal L).2 η hηp hηx 1 htd'
  have hloc := (loc_rho hF hn S x.asIdeal L).2.2.1 P
  rw [himP] at hloc
  refine ⟨P, hP, ?_, ?_, ?_⟩
  · unfold NRep.TI NRep.OffTri
    exact ⟨⟨fun h => hTIη'.1.1 (hloc.1.mp h), fun h => hTIη'.1.2 (hloc.2.1.mp h)⟩,
      fun h3 h => hTIη'.2 h3 (hloc.2.2.mp h)⟩
  · show S.π (L.im P) = p
    rw [himP, hπ]
  · rw [hdim, hπ]
    norm_num
end
