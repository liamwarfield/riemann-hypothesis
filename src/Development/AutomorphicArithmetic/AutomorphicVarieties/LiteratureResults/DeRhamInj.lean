module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.DExact
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Window
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ExistsCurve
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.CorrUniq

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.GeoProper
open UpperTheory.V.Lit.Dr
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af

theorem UpperTheory.V.Lit.Dr.geoProper :
    GeoProper := by
  intro E _ _ _ a ho U Ξ hU K hK hKc s s'
  obtain ⟨C, hC⟩ := boundInf E a K hK hKc
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective s'
  have hT : ∀ i j : Fin a, IsCompact
      ((fun u : GL (Fin a) (Af E) => (x' * u * x⁻¹).val i j) '' (U : Set (GL (Fin a) (Af E)))) := by
    intro i j
    refine hU.image ?_
    have h1 : Continuous fun u : GL (Fin a) (Af E) => (x' * u * x⁻¹).val :=
      Units.continuous_val.comp ((continuous_const.mul continuous_id).mul continuous_const)
    exact h1.matrix_elem i j
  have hF := Set.Finite.pi' fun i : Fin a => Set.Finite.pi' fun j : Fin a => finField E C _ (hT i j)
  have hinj : Function.Injective fun (γ : (⊤ : Subgroup (GL (Fin a) E))) (i j : Fin a) => γ.1.val i j := by
    intro γ δ h
    exact Subtype.ext (Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))
  refine (hF.preimage hinj.injOn).subset ?_
  rintro γ ⟨hσ, p, hp, hp'⟩ i j
  refine ⟨fun w => ?_, ?_⟩
  · have h := hC _ p hp hp'
    have h2 : ‖toL (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)).val i j w‖ ≤ C :=
      ((norm_le_pi_norm _ w).trans ((norm_le_pi_norm _ j).trans (norm_le_pi_norm _ i))).trans h
    have h3 : toL (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1)).val i j w
        = pInf E (algebraMap E (Ad E) (γ.1.val i j)) w := rfl
    rwa [h3, pInf_algebraMap, InfinitePlace.norm_embedding_eq] at h2
  · rw [geo_σ, MulAction.Quotient.smul_mk, eq_comm, QuotientGroup.eq] at hσ
    refine ⟨_, hσ, ?_⟩
    have h4 : x' * (x'⁻¹ * (GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 • x)) * x⁻¹
        = GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 := by
      rw [smul_eq_mul]; group
    beta_reduce
    rw [h4]
    rfl
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Retract
open UpperTheory.V.Lit.Dr
open scoped ContDiff

theorem UpperTheory.V.Lit.Dr.retract :
    Retract := by
  intro Γ V S _ _ _ _ d G hY l hl q η hη hd
  classical
  obtain ⟨hgauge, hinv⟩ := hl
  have hmem : ∀ s, ContDiffOn ℝ ∞ ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
      ∀ p ∉ G.Y, (η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 := η.2
  have hmem' : ∀ s, ContDiffOn ℝ ∞ (((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
      ∀ p ∉ G.Y, ((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p = 0 :=
    ((G.dOm q) η).2
  let w : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun s => G.Y.indicator (pull (l s) ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s))
  have hwmem : w ∈ G.Om q := by
    show ∀ s, ContDiffOn ℝ ∞ (w s) G.Y ∧ ∀ p ∉ G.Y, w s p = 0
    intro s
    refine ⟨?_, ?_⟩
    · refine (pullB V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) q _ (hmem s).1).1.congr ?_
      intro p hp
      simp only [w, Set.indicator_of_mem hp]
    · intro p hp
      simp only [w, Set.indicator_of_notMem hp]
  refine ⟨⟨w, hwmem⟩, ?_, ?_, ?_⟩
  · intro γ
    apply Subtype.ext
    funext s p
    show (G.tr q γ) (w ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) p)) = w s p
    by_cases hp : p ∈ G.Y
    · have hp' : (G.ρ γ⁻¹) p ∈ G.Y := G.maps _ _ hp
      simp only [w, Set.indicator_of_mem hp, Set.indicator_of_mem hp']
      exact pullEquiv Γ V S d G hY l ⟨hgauge, hinv⟩ q η hη γ s p hp
    · have hback : (G.ρ γ) ((G.ρ γ⁻¹) p) = p := by
        rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
        rfl
      have hp' : (G.ρ γ⁻¹) p ∉ G.Y := by
        intro h
        exact hp (hback ▸ G.maps γ _ h)
      simp only [w, Set.indicator_of_notMem hp, Set.indicator_of_notMem hp', map_zero]
  · intro s p hp v i hv
    show w s p v = 0
    simp only [w, Set.indicator_of_mem hp]
    exact (pullA V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) q _).1 p hp v i hv
  · apply Subtype.ext
    funext s p
    show G.Y.indicator (extDeriv (w s)) p =
      ((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s p
    set u := ((G.dOm q) η : S → V → V [⋀^Fin (q + 1)]→L[ℝ] (Fin d → ℂ)) s with hu_def
    have hu : u = G.Y.indicator (extDeriv ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) := rfl
    by_cases hp : p ∈ G.Y
    · rw [Set.indicator_of_mem hp]
      have hev : w s =ᶠ[nhds p] pull (l s) ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) := by
        filter_upwards [G.isOpen.mem_nhds hp] with x hx
        simp only [w, Set.indicator_of_mem hx]
      rw [hev.extDeriv_eq, (pullB V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) q _ (hmem s).1).2 p hp]
      have hq : l s p • p ∈ G.Y := hY _ ((hgauge s).2.1 p hp) p hp
      have hpu : pull (l s) (extDeriv ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s)) p =
          pull (l s) u p := by
        simp only [pull, hu, Set.indicator_of_mem hq]
      have hsm : minSmoothness ℝ 2 ≤ (∞ : WithTop ℕ∞) := by
        simp only [minSmoothness_of_isRCLikeNormedField]
        exact WithTop.coe_le_coe.2 le_top
      have hclosed : ∀ x ∈ G.Y, extDeriv u x = 0 := by
        intro x hx
        have hev2 : u =ᶠ[nhds x] extDeriv ((η : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) := by
          filter_upwards [G.isOpen.mem_nhds hx] with y hy
          rw [hu, Set.indicator_of_mem hy]
        rw [hev2.extDeriv_eq]
        exact extDeriv_extDeriv_apply ((hmem s).1.contDiffAt (G.isOpen.mem_nhds hx)) hsm
      have hhom := homog V (Fin d → ℂ) G.Y G.isOpen hY (q + 1) u (hmem' s).1 (hd s) hclosed
      rw [hpu, (pullA V (Fin d → ℂ) G.Y G.isOpen hY (l s) (hgauge s) (q + 1) u).2 (hd s) hhom p hp]
    · rw [Set.indicator_of_notMem hp]
      exact ((hmem' s).2 p hp).symm
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AbsMain
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ShiftOne
noncomputable section

namespace UpperTheory.V.Lit.Dr

open groupCohomology

theorem shiftOne : ShiftOne := by
  intro Γ M Ω Z _ _ _ _ _ _ _ ρM ρΩ ρZ ι π hι hπ hinj hsurj hex n w hw hlift
  classical
  choose y hy using fun i => hsurj (w i)
  have hker : ∀ i γ, π (ρΩ γ (y i) - y i) = 0 := by
    intro i γ
    rw [map_sub, hπ, hy, hw, sub_self]
  choose φ hφ using fun i γ => (hex (ρΩ γ (y i) - y i)).1 (hker i γ)
  have hcoc : ∀ i, φ i ∈ groupCohomology.cocycles₁ (Rep.of ρM) := by
    intro i
    rw [groupCohomology.mem_cocycles₁_iff]
    intro g h
    apply hinj
    rw [Rep.of_ρ]
    change ι (φ i (g * h)) = ι ((ρM g) (φ i h) + φ i g)
    rw [map_add (f := _), hι, hφ, hφ, hφ, map_mul, Module.End.mul_apply, map_sub]
    abel
  let v : Fin n → groupCohomology (Rep.of ρM) 1 :=
    fun i => (groupCohomology.H1π (Rep.of ρM)).hom ⟨φ i, hcoc i⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hsum : (∑ i, g i • v i) =
        (groupCohomology.H1π (Rep.of ρM)).hom (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM))) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, v]
    rw [hsum, groupCohomology.H1π_eq_zero_iff] at hg
    obtain ⟨m, hm⟩ := hg
    have key : Subtype.val (∑ i, g i • (⟨φ i, hcoc i⟩ : groupCohomology.cocycles₁ (Rep.of ρM))) = ∑ i, g i • φ i := by
      rw [Submodule.coe_sum]
      rfl
    have hm' : ∀ γ, ρM γ m - m = ∑ i, g i • φ i γ := by
      intro γ
      have := congrFun hm γ
      rw [groupCohomology.d₀₁_hom_apply, Rep.of_ρ] at this
      rw [this]
      exact (congrFun key γ).trans (Finset.sum_apply _ _ _)
    have hzero := hlift g ⟨(∑ i, g i • y i) - ι m, ?_, ?_⟩
    · intro i
      rw [hzero]
      rfl
    · intro γ
      have h1 : ι (ρM γ m) - ι m = ∑ i, g i • (ρΩ γ (y i) - y i) := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sub, hm', map_sum]
        simp only [map_smul, hφ]
      rw [hι] at h1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum]
      simp only [map_smul]
      simp only [smul_sub, Finset.sum_sub_distrib] at h1
      rw [sub_eq_iff_eq_add] at h1
      rw [h1]
      abel
    set_option synthInstance.maxHeartbeats 100000 in
      · rw [map_sub, hex.apply_apply_eq_zero, sub_zero, map_sum]
        simp only [map_smul, hy]
  have := hli.cardinal_le_rank
  simpa using this

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Acyclic
noncomputable section

open CategoryTheory

namespace UpperTheory.V.Lit.Dr

theorem acyclic : Acyclic := by
  intro Γ Ω _ _ _ ρ hP n
  obtain ⟨P, hconst, hequi⟩ := hP
  let S : Subgroup Γ := ⊥
  haveI : Subsingleton S := ⟨fun a b => Subtype.ext ((Subgroup.mem_bot.1 a.2).trans (Subgroup.mem_bot.1 b.2).symm)⟩
  let A : Rep ℂ S := Rep.of (Representation.trivial ℂ S Ω)
  let C : Rep ℂ Γ := Rep.coind S.subtype A
  have hC : Subsingleton (groupCohomology C (n + 1)) := by
    have hz : Limits.IsZero (groupCohomology C (n + 1)) :=
      (isZero_groupCohomology_succ_of_subsingleton A n).of_iso (groupCohomology.coindIso A (n + 1))
    have h0 : 𝟙 (groupCohomology C (n + 1)) = 0 := hz.eq_of_src _ _
    refine ⟨fun a b => ?_⟩
    have ha := congrArg (fun f => f.hom a) h0
    have hb := congrArg (fun f => f.hom b) h0
    simp only [ModuleCat.hom_id, ModuleCat.hom_zero, LinearMap.id_apply, LinearMap.zero_apply] at ha hb
    rw [ha, hb]
  let L : Ω →ₗ[ℂ] (Γ → Ω) := LinearMap.pi fun h => ρ h
  have hL : ∀ x, L x ∈ Representation.coindV S.subtype A.ρ := by
    intro x g h
    have hg : (g : Γ) = 1 := Subgroup.mem_bot.1 g.2
    simp [L, hg, A]
  let iL : Ω →ₗ[ℂ] Representation.coindV S.subtype A.ρ := LinearMap.codRestrict _ L hL
  let M : Representation.coindV S.subtype A.ρ →ₗ[ℂ] (Γ → Ω) :=
    LinearMap.pi fun g => ρ g ∘ₗ LinearMap.proj g⁻¹ ∘ₗ Submodule.subtype _
  let rL : Representation.coindV S.subtype A.ρ →ₗ[ℂ] Ω := P ∘ₗ M
  let i : Rep.of ρ ⟶ C := Rep.ofHom ⟨iL, fun γ => by
    refine LinearMap.ext fun x => Subtype.ext (funext fun h => ?_)
    simp only [iL, L, LinearMap.comp_apply]
    show (ρ h) ((ρ γ) x) = (ρ (h * γ)) x
    rw [map_mul, Module.End.mul_apply]⟩
  let r : C ⟶ Rep.of ρ := Rep.ofHom ⟨rL, fun γ => by
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, rL, M]
    rw [hequi]
    congr 1
    funext g
    simp [mul_inv_rev, ← Module.End.mul_apply, ← map_mul]
    rfl⟩
  have hri : i ≫ r = 𝟙 _ := by
    ext x
    simp [i, r, rL, M, iL, L, ← Module.End.mul_apply, ← map_mul, hconst]
    show P (fun g => ρ g (ρ g⁻¹ x)) = x
    rw [show (fun g => ρ g (ρ g⁻¹ x)) = fun _ => x from
      funext fun g => by rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply], hconst]
  let F := groupCohomology.functor ℂ Γ (n + 1)
  have hinj : Function.Injective (F.map i).hom := by
    intro a b hab
    have key : ∀ z, (F.map r).hom ((F.map i).hom z) = z := by
      intro z
      rw [← ModuleCat.comp_apply, ← F.map_comp, hri, F.map_id]
      rfl
    rw [← key a, ← key b, hab]
  haveI : Subsingleton (F.obj C) := hC
  exact hinj.subsingleton

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ShiftUp
noncomputable section

open CategoryTheory

namespace UpperTheory.V.Lit.Dr

theorem shiftUp : ShiftUp := by
  intro Γ M Ω Z _ _ _ _ _ _ _ ρM ρΩ ρZ ι π hι hπ hinj hsurj hex hΩ n
  let f : Rep.of ρM ⟶ Rep.of ρΩ := Rep.ofHom ⟨ι, fun γ => by ext m; exact hι γ m⟩
  let g : Rep.of ρΩ ⟶ Rep.of ρZ := Rep.ofHom ⟨π, fun γ => by ext x; exact hπ γ x⟩
  have hfg : f ≫ g = 0 := by
    ext m
    exact hex.apply_apply_eq_zero m
  let X : ShortComplex (Rep ℂ Γ) := ShortComplex.mk f g hfg
  have hX : X.ShortExact :=
    { exact := (forget₂ (Rep ℂ Γ) (ModuleCat ℂ)).reflects_exact_of_faithful _ <|
        (ShortComplex.moduleCat_exact_iff _).2 fun x hx => (hex x).1 hx
      mono_f := (Rep.mono_iff_injective _).2 hinj
      epi_g := (Rep.epi_iff_surjective _).2 hsurj }
  have hz : Limits.IsZero (groupCohomology X.X₂ (n + 1)) := by
    haveI := hΩ n
    exact ModuleCat.isZero_of_subsingleton _
  have hmono := groupCohomology.mono_δ_of_isZero hX (n + 1) hz
  have hinjδ := (ModuleCat.mono_iff_injective _).1 hmono
  exact LinearMap.rank_le_of_injective _ hinjδ

end UpperTheory.V.Lit.Dr
end
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.ShiftZero
noncomputable section

namespace UpperTheory.V.Lit.Dr

theorem shiftZero : ShiftZero := by
  intro Γ M _ _ _ ρ n w hw hlin
  let v : Fin n → (Rep.of ρ).ρ.invariants :=
    fun i => ⟨w i, (Representation.mem_invariants _ _).2 (hw i)⟩
  have hli : LinearIndependent ℂ v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 : ∑ i, g i • w i = 0 := by
      have := congrArg Subtype.val hg
      rw [Submodule.coe_sum] at this
      exact this
    rw [hlin g h0]
    intro i
    rfl
  have h1 := hli.cardinal_le_rank
  rw [Cardinal.mk_fin] at h1
  have hinj : Function.Injective (groupCohomology.H0Iso (Rep.of ρ)).inv.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  exact h1.trans (LinearMap.rank_le_of_injective _ hinj)

end UpperTheory.V.Lit.Dr
end
end

open UpperTheory.V.Lit.Dr

private def UpperTheory.V.Lit.Dr.kerRep {Γ A B : Type} [Group Γ] [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]
    (ρ : Representation ℂ Γ A) (σ : Representation ℂ Γ B) (f : A →ₗ[ℂ] B) (hf : ∀ γ x, f (ρ γ x) = σ γ (f x)) :
    Representation ℂ Γ (LinearMap.ker f) where
  toFun γ := (ρ γ).restrict (fun x hx => by
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hf, hx, map_zero])
  map_one' := by ext x; simp
  map_mul' γ δ := by ext x; simp

private theorem UpperTheory.V.Lit.Dr.absPos (q : ℕ) :
    ∀ (Γ M : Type) (Ω : ℕ → Type) [Group Γ] [AddCommGroup M] [Module ℂ M] [∀ q, AddCommGroup (Ω q)] [∀ q, Module ℂ (Ω q)]
    (ρM : Representation ℂ Γ M) (ρ : ∀ q, Representation ℂ Γ (Ω q)) (ι : M →ₗ[ℂ] Ω 0) (d : ∀ q, Ω q →ₗ[ℂ] Ω (q + 1)),
    (∀ γ m, ι (ρM γ m) = ρ 0 γ (ι m)) → (∀ q γ x, d q (ρ q γ x) = ρ (q + 1) γ (d q x)) → Function.Injective ι →
    Function.Exact ι (d 0) → (∀ q, Function.Exact (d q) (d (q + 1))) → (∀ q, HasAverage (ρ q)) →
    ∀ (n : ℕ) (w : Fin n → Ω (q + 1)), (∀ i γ, ρ (q + 1) γ (w i) = w i) → (∀ i, d (q + 1) (w i) = 0) →
    (∀ c : Fin n → ℂ, (∃ y, (∀ γ, ρ q γ y = y) ∧ d q y = ∑ i, c i • w i) → c = 0) →
    (n : Cardinal) ≤ Module.rank ℂ (groupCohomology (Rep.of ρM) (q + 1)) := by
  induction q with
  | zero =>
    intro Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
    let π : Ω 0 →ₗ[ℂ] LinearMap.ker (d 1) := (d 0).codRestrict _ (fun x => (hex 0).apply_apply_eq_zero x)
    refine shiftOne Γ M (Ω 0) (LinearMap.ker (d 1)) ρM (ρ 0) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1)) ι π hι
      (fun γ x => Subtype.ext (hd 0 γ x)) hinj
      (fun z => by obtain ⟨y, hy⟩ := (hex 0 z.1).1 z.2; exact ⟨y, Subtype.ext hy⟩)
      (fun x => by rw [← hex0 x, Subtype.ext_iff]; rfl) n (fun i => ⟨w i, hdw i⟩)
      (fun i γ => Subtype.ext (hw i γ)) ?_
    rintro c ⟨y, hy, hy'⟩
    refine hind c ⟨y, hy, ?_⟩
    have h : (π y).1 = ∑ i, c i • w i := by rw [hy']; simp
    exact h
  | succ q ih =>
    intro Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
    let π : Ω 0 →ₗ[ℂ] LinearMap.ker (d 1) := (d 0).codRestrict _ (fun x => (hex 0).apply_apply_eq_zero x)
    refine le_trans (ih Γ (LinearMap.ker (d 1)) (fun k => Ω (k + 1)) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1))
      (fun k => ρ (k + 1)) (LinearMap.ker (d 1)).subtype (fun k => d (k + 1)) (fun γ m => rfl)
      (fun k => hd (k + 1)) Subtype.val_injective (LinearMap.exact_subtype_ker_map _) (fun k => hex (k + 1))
      (fun k => hav (k + 1)) n w hw hdw hind) ?_
    exact shiftUp Γ M (Ω 0) (LinearMap.ker (d 1)) ρM (ρ 0) (kerRep (ρ 1) (ρ 2) (d 1) (hd 1)) ι π hι
      (fun γ x => Subtype.ext (hd 0 γ x)) hinj
      (fun z => by obtain ⟨y, hy⟩ := (hex 0 z.1).1 z.2; exact ⟨y, Subtype.ext hy⟩)
      (fun x => by rw [← hex0 x, Subtype.ext_iff]; rfl) (acyclic Γ (Ω 0) (ρ 0) (hav 0)) q

theorem UpperTheory.V.Lit.Dr.absMain :
    AbsMain := by
  intro q Γ M Ω _ _ _ _ _ ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
  cases q with
  | zero =>
    choose m hm using fun i => (hex0 (w i)).1 (hdw i)
    refine shiftZero Γ M ρM n m (fun i γ => hinj (by rw [hι, hm, hw])) (fun c hc => hind c ?_)
    have := congrArg ι hc
    simpa [InvExact, hm] using this
  | succ q => exact absPos q Γ M Ω ρM ρ ι d hι hd hinj hex0 hex hav n w hw hdw hind
end

section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Average
section -- merged from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.AvgMem
noncomputable section

open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

theorem avgMem : AvgMem := by
  intro Γ V S _ _ _ d G u hu q c
  obtain ⟨hsm, hfin, -⟩ := hu
  have hc : ∀ γ s, ContDiffOn ℝ ∞ ((c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s) G.Y ∧
      ∀ p ∉ G.Y, (c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s p = 0 :=
    fun γ s => (c γ).2 s
  simp only [Geo.Om, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk, Set.mem_setOf_eq]
  intro s
  refine ⟨?_, ?_⟩
  · apply contDiffOn_of_locally_contDiffOn
    intro p hp
    obtain ⟨N, hN, hF⟩ := hfin s p hp
    obtain ⟨O, hON, hO, hpO⟩ := mem_nhds_iff.mp hN
    refine ⟨O, hO, hpO, ?_⟩
    have hsum : ContDiffOn ℝ ∞ (fun x => ∑ γ ∈ hF.toFinset,
        u ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x) • (c γ : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) s x) (G.Y ∩ O) := by
      apply ContDiffOn.sum
      intro γ _
      have h1 : ContDiffOn ℝ ∞ (fun x => u ((G.σ γ⁻¹) s) ((G.ρ γ⁻¹) x)) (G.Y ∩ O) :=
        ((hsm _).comp (G.ρ γ⁻¹).contDiff.contDiffOn
          (fun x hx => G.maps γ⁻¹ x hx.1))
      exact h1.smul ((hc γ s).1.mono Set.inter_subset_left)
    refine hsum.congr ?_
    intro x hx
    apply finsum_eq_sum_of_support_subset
    intro γ hγ
    rw [Set.Finite.coe_toFinset]
    refine ⟨x, hON hx.2, ?_⟩
    intro h0
    rw [Function.mem_support] at hγ
    exact hγ (by rw [h0, zero_smul])
  · intro p hp
    apply finsum_eq_zero_of_forall_eq_zero
    intro γ
    simp [(hc γ s).2 p hp]

end UpperTheory.V.Lit.Dr
end
end

noncomputable section

open Matrix
open scoped ContDiff

namespace UpperTheory.V.Lit.Dr

section

variable {Γ V S : Type} [Group Γ] [NormedAddCommGroup V] [NormedSpace ℝ V] {d : ℕ} {G : Geo Γ V S d} {u : S → V → ℝ}

end

theorem average : Average := by
  intro Γ V S _ _ _ d G u hu q
  have hu' := hu
  obtain ⟨hsm, hfin, hone⟩ := hu
  have hfs : ∀ (c : Γ → G.Om q) s p, Function.HasFiniteSupport
      (fun g => u (G.σ g⁻¹ s) (G.ρ g⁻¹ p) • (c g).1 s p) := by
    intro c s p
    by_cases hp : p ∈ G.Y
    · obtain ⟨N, hN, hNfin⟩ := hfin s p hp
      refine hNfin.subset ?_
      intro g hg
      refine ⟨p, mem_of_mem_nhds hN, ?_⟩
      intro h0
      apply hg
      simp only [h0, zero_smul]
    · refine Set.finite_empty.subset ?_
      intro g hg
      apply hg
      simp only [((c g).2 _).2 _ hp, smul_zero]
  let A : (Γ → G.Om q) →ₗ[ℂ] G.Om q :=
    { toFun := fun c => ⟨fun s p => ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (c γ).1 s p,
        avgMem Γ V S d G u hu' q c⟩
      map_add' := by
        intro a b
        apply Subtype.ext
        funext s p
        show ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (a γ + b γ).1 s p =
          ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (a γ).1 s p + ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (b γ).1 s p
        simp only [Submodule.coe_add, Pi.add_apply, smul_add]
        exact finsum_add_distrib (hfs a s p) (hfs b s p)
      map_smul' := by
        intro z a
        apply Subtype.ext
        funext s p
        show ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (z • a γ).1 s p =
          z • ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • (a γ).1 s p
        have hm := map_finsum (DistribSMul.toAddMonoidHom (V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)) z)
          (hfs a s p)
        simp only [DistribSMul.toAddMonoidHom_apply] at hm
        rw [hm]
        congr 1
        funext i
        simp only [Submodule.coe_smul, Pi.smul_apply]
        exact smul_comm _ _ _ }
  refine ⟨A, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    funext s p
    show ∑ᶠ γ, u (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) • x.1 s p = x.1 s p
    by_cases hp : p ∈ G.Y
    · rw [← finsum_smul, hone s p hp, one_smul]
    · have hx0 : x.1 s p = 0 := (x.2 s).2 p hp
      simp [hx0]
  · intro γ c
    apply Subtype.ext
    funext s p
    show G.tr q γ (∑ᶠ g, u (G.σ g⁻¹ (G.σ γ⁻¹ s)) (G.ρ g⁻¹ (G.ρ γ⁻¹ p)) • (c g).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
      = ∑ᶠ g, u (G.σ g⁻¹ s) (G.ρ g⁻¹ p) • G.tr q γ ((c (γ⁻¹ * g)).1 (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p))
    rw [map_finsum (G.tr q γ) (hfs c _ _)]
    conv_rhs => rw [← finsum_comp_equiv (Equiv.mulLeft γ)]
    congr 1
    funext h
    simp [_root_.mul_inv_rev, map_mul, Equiv.Perm.mul_apply]

end UpperTheory.V.Lit.Dr
end
end

open UpperTheory.V.Lit

theorem UpperTheory.V.Lit.deRhamInj :
    DeRhamInj :=
  Dr.deRhamInj_of Dr.absMain Dr.dEquiv Dr.inclFacts Dr.dExact Dr.average Dr.window Dr.cutoff Dr.retract Dr.locSec Dr.coneConvex Dr.geoProper Dr.gauge Dr.levelVal Dr.centralOf Dr.corrFwd Dr.corrSmooth Dr.corrBwd Dr.corrCochain Dr.corrUniq Dr.corrInv Dr.corrBasic Dr.corrD
