module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ProperRelAmpleKTrivOfFieldExtension
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsAbelianSchemeModelOfIsogenyDedekind
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.AppellHumbertUnifTangentWeilPairing
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LieFreeNearTwoPrimes
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsRegularOfFnOfRingKrullDimQuotientAddLe
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.TopologicalKrullDimLeOfFiniteCommonZeros

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PolarisationOfFaithfullyFlat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section

namespace GlobalTheory.PolFlatDescent

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A']
  {φ : A'.left ⟶ A.left}

theorem isCommMonObj_of_pull [Flat f] [Surjective f] (h : IsGrpPullback A' A f φ) [IsCommMonObj A'] :
    IsCommMonObj A := by
  refine ⟨GrpFlatDesc.hom_ext_of_points f fun T t => ?_⟩
  obtain ⟨x, hx⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ fst _ _)
  obtain ⟨y, hy⟩ := GrpDense.pushPt_surjective h.1 T (t ≫ snd _ _)
  obtain rfl : t = lift (pushPt h.1.w x) (pushPt h.1.w y) :=
    CartesianMonoidalCategory.hom_ext _ _ (by rw [lift_fst, hx]) (by rw [lift_snd, hy])
  rw [lift_braiding_hom_assoc]
  exact Over.OverMorphism.ext ((h.2 T y x _ _ rfl rfl).trans
    ((congrArg (fun z => z.left ≫ φ) (_root_.mul_comm y x)).trans (h.2 T x y _ _ rfl rfl).symm))

theorem isAbelianScheme_of_pull [Flat f] [Surjective f] [QuasiCompact f] (h : IsGrpPullback A' A f φ)
    (hA : IsAbelianScheme A') : IsAbelianScheme A := by
  have := hA.comm
  have := hA.proper
  have := hA.geomConnected
  exact ⟨isCommMonObj_of_pull h, MorphismProperty.of_isPullback_of_descendsAlong (P := @Smooth)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) h.1.flip ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hA.smooth,
    GrpFlatDesc.isProper_of_isPullback h.1, GrpFlatDesc.geometricallyConnected_of_isPullback h.1⟩

theorem inv_left_comp (h : IsGrpPullback A' A f φ) :
    (GrpObj.inv : A' ⟶ A').left ≫ φ = φ ≫ (GrpObj.inv : A ⟶ A).left := by
  have e := congrArg (fun q => q.left) (map_inv (pushHom h A') (𝟙 A'))
  simp only [Hom.inv_def, Category.id_comp] at e
  exact e.trans (congrArg (· ≫ _) (Category.id_comp φ))

theorem exists_gen_pull_of_sym (hG : Out.GlobalFnsSt) (h : IsGrpPullback A' A f φ) (hA : IsAbelianScheme A')
    {L : LB A.left} {L' : LB A'.left} (hL : L.IsLB) (hL' : L'.IsLB) (hw : LBIso L' (L.pull φ)) (hS : Out.Sym A' L')
    {Y : Scheme.{0}} (r : Y ⟶ A'.left) :
    ∃ t : ((LB.LinComb L (K := Fin 2) ![(GrpObj.inv : A ⟶ A).left, 𝟙 _] ![1, -1]).pull (r ≫ φ)).Gen, t.IsGen := by
  obtain ⟨w, hw⟩ := hw
  obtain ⟨c, hc⟩ := exists_gen_neg_of_sym hG hA hL' hS
  let δ : Fin 2 → (A.left ⟶ A.left) := ![(GrpObj.inv : A ⟶ A).left, 𝟙 _]
  let δ' : Fin 2 → (A'.left ⟶ A'.left) := ![(GrpObj.inv : A' ⟶ A').left, 𝟙 _]
  let ε : Fin 2 → ℤ := ![1, -1]
  let q := r ≫ φ
  let ψ : Fin 2 → (Y ⟶ A'.left) := fun k => r ≫ δ' k
  have e (k : Fin 2) : ψ k ≫ φ = q ≫ δ k := by
    fin_cases k <;> simp [ψ, q, δ, δ', Category.assoc, inv_left_comp h]
  let B := LB.LinComb L' ψ ε
  let C := LB.LinComb (L.pull φ) ψ ε
  let N := LB.LinComb L δ ε
  let D := N.pull q
  let b : B.Gen := LB.pullGen L' δ' ε c r
  have hb : b.IsGen := DVR.pullGen_isGen L' δ' ε c hc r
  have hB : B.IsLB := DVR.linComb_isLB _ hL' ψ ε
  have hC : C.IsLB := DVR.linComb_isLB _ (LB.isLB_pull hL φ) ψ ε
  let v := LB.linCombIso w ψ ε
  have hv := (Transport.invIso_spec hB hC v (DVR.linCombIso_isGen w hw ψ ε)).1
  obtain ⟨u, hu, -⟩ := Transport.exists_transport hC hB (Transport.invIso v) hv b hb
  let idx (j : D.ι) : C.ι := fun k _ => j PUnit.unit k
  have le' (j : D.ι) : D.U j ≤ LB.wchart L (fun k => q ≫ δ k) (j PUnit.unit) :=
    fun _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy PUnit.unit) k
  have le (j : D.ι) : D.U j ≤ C.U (idx j) := by
    intro y hy
    refine Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun _ => ?_
    change y ∈ (ψ k ≫ φ) ⁻¹ᵁ L.U (j PUnit.unit k)
    rw [e k]
    exact Set.mem_iInter.1 (le' j hy) k
  have transition (i j : D.ι) : D.g i j =
      res (le_inf (inf_le_left.trans (le i)) (inf_le_right.trans (le j))) (C.g (idx i) (idx j)) := by
    let leOverlap := le_inf (inf_le_left.trans (le' i)) (inf_le_right.trans (le' j))
    calc
      D.g i j = res leOverlap (L.lcg (fun k => q ≫ δ k) ε (i PUnit.unit) (j PUnit.unit)) := by
        change N.lcg (fun _ : PUnit => q) (fun _ => 1) i j = _
        erw [LB.lcg_pull, LB.lcg_comp, LB.res_res]
        rfl
      _ = _ := by
        change _ = res _ ((L.pull φ).lcg ψ ε (idx i) (idx j))
        erw [LB.res_lcg, LB.res_lcg]
        refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
        change _ = res _ (pullU (ψ k) _ (L.lcg (fun _ : PUnit => φ) (fun _ => 1) (idx i k) (idx j k)))
        have pull_eq {a a' : Y ⟶ A.left} (ha : a = a') {U : A.left.Opens} {V : Y.Opens}
            (hle : V ≤ a ⁻¹ᵁ U) (hle' : V ≤ a' ⁻¹ᵁ U) (x : Γ(A.left, U)ˣ) :
            res hle (pullU a U x) = res hle' (pullU a' U x) := by
          subst a'
          rfl
        erw [LB.lcg_pull, LB.pull_res_comp]
        · exact pull_eq (e k).symm _ _ _
        · rw [e k]
          exact leOverlap.trans (LB.wchart_inter_le L _ _ _ k)
  refine ⟨⟨fun j => res (le j) (u.s (idx j))⟩, fun i j => ?_⟩
  change res inf_le_left (res (le i) (u.s (idx i))) =
    D.g i j * res inf_le_right (res (le j) (u.s (idx j)))
  have eq := congrArg (res (le_inf (inf_le_left.trans (le i)) (inf_le_right.trans (le j)))) (hu (idx i) (idx j))
  rw [transition]
  simpa only [map_mul, LB.res_res] using eq

theorem polarisation_of_faithfullyFlat : Out.Laws → ∀ (R₀ R : Type) [CommRing R₀] [IsDomain R₀] [IsLocalRing R₀] [IsPrincipalIdealRing R₀] [CommRing R] [IsNoetherianRing R] [Algebra R₀ R] [Module.FaithfullyFlat R₀ R] (P : Out.PolAV (Sp R)) (A₀ : Over (Sp R₀)) [GrpObj A₀] [Flat A₀.hom] (L₀ : LB A₀.left) (π : P.A.left ⟶ A₀.left), IsProjBy A₀.hom → L₀.IsLB → IsGrpPullback P.A A₀ (spMap (algebraMap R₀ R)) π → LBIso P.L (L₀.pull π) → IsAbelianScheme A₀ ∧ SmoothOfRelativeDimension P.g A₀.hom ∧ Out.Rigidified A₀ L₀ ∧ Out.Sym A₀ L₀ ∧ Out.RelAmple A₀ L₀ ∧ Out.KTriv A₀ L₀ := by
  intro hL R₀ R _ _ _ _ _ _ _ _ P A₀ _ _ L₀ π _ hL₀ h hw
  have : Flat (spMap (algebraMap R₀ R)) := Flat.SpecMap_iff.2 (RingHom.flat_algebraMap_iff.2 inferInstance)
  have : Surjective (spMap (algebraMap R₀ R)) := ⟨PrimeSpectrum.comap_surjective_of_faithfullyFlat⟩
  have hA : IsAbelianScheme A₀ := isAbelianScheme_of_pull h P.isAb
  have := hA.smooth
  have := hA.proper
  have := P.isAb.proper
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ A₀.hom hA.smooth hA.geomConnected
  have : CompactSpace A₀.left := QuasiCompact.compactSpace_of_compactSpace A₀.hom
  have : QuasiSeparatedSpace A₀.left := quasiSeparatedSpace_of_quasiSeparated A₀.hom
  obtain ⟨q, hq⟩ := PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R₀) (B := R) ⊥
  let β : R →+* q.asIdeal.ResidueField := algebraMap _ _
  have hj : Function.Injective (β.comp (algebraMap R₀ R)) := by
    rw [RingHom.injective_iff_ker_eq_bot, ← RingHom.comap_ker, Ideal.ker_algebraMap_residueField]
    exact congrArg PrimeSpectrum.asIdeal hq
  have H : IsPullback (pullback.fst P.A.hom (spMap β) ≫ π) (pullback.snd P.A.hom (spMap β)) A₀.hom
      (spMap (β.comp (algebraMap R₀ R))) := by
    rw [show spMap (β.comp (algebraMap R₀ R)) = spMap β ≫ spMap (algebraMap R₀ R) from
      Spec.map_comp (CommRingCat.ofHom (algebraMap R₀ R)) (CommRingCat.ofHom β)]
    exact (IsPullback.of_hasPullback P.A.hom (spMap β)).paste_horiz h.1
  refine ⟨hA, ?_, DVR.exists_gen_of_local L₀ hL₀ _ _, ?_, ?_, AmpleDescent.kTriv_of_pull h hL₀ P.isLB hw P.ktriv⟩
  · exact CM.smoothOfRelativeDimension_of_fibre R₀ _ _ A₀ _ _ _ P.g hA H
      ((smoothOfRelativeDimension_isStableUnderBaseChange P.g).of_isPullback
        (IsPullback.of_hasPullback P.A.hom (spMap β)) P.smoothDim)
  · have hN := DVR.linComb_isLB L₀ hL₀ (K := Fin 2) ![(GrpObj.inv : A₀ ⟶ A₀).left, 𝟙 _] ![1, -1]
    obtain ⟨ρ, hρ⟩ := DVR.exists_gen_of_local (V := R₀) _ hN (K := PUnit) (fun _ => eSec A₀) (fun _ => 1)
    obtain ⟨t, ht⟩ := exists_gen_pull_of_sym hL.globalFns h P.isAb hL₀ P.isLB hw P.sym
      (pullback.fst P.A.hom (spMap β))
    obtain ⟨c, hc⟩ := GenericTriv.exists_gen_of_fibre _ hj A₀.hom (eSec A₀) (Over.w η[A₀]) _ _ H
      (Out.TLinPf.const_pullback hL.globalFns (spMap β) P.A P.isAb) hN ρ hρ t ht
    intro s
    let i := (A₀.hom ⁻¹ᵁ ⊤).ι
    have e : ![i ≫ (GrpObj.inv : A₀ ⟶ A₀).left, i] =
        fun k : Fin 2 => i ≫ ![(GrpObj.inv : A₀ ⟶ A₀).left, 𝟙 _] k := by
      funext k
      fin_cases k
      · rfl
      · exact (Category.comp_id i).symm
    refine ⟨⊤, trivial, ?_⟩
    change ∃ u : (LB.LinComb L₀ ![i ≫ (GrpObj.inv : A₀ ⟶ A₀).left, i] ![1, -1]).Gen, u.IsGen
    rw [e]
    exact ⟨_, DVR.pullGen_isGen L₀ _ _ c hc i⟩
  · have : Flat (Out.specOf (algebraMap R₀ R)) := ‹Flat (spMap (algebraMap R₀ R))›
    have : Surjective (Out.specOf (algebraMap R₀ R)) := ‹Surjective (spMap (algebraMap R₀ R))›
    refine (relAmple_iff_isAmpleLB_of_isAffine A₀ hL₀).2 (AmpleDescent.isAmpleLB_of_pull _ h.1 hL₀ ?_)
    exact (isAmpleLB_of_relAmple_of_isAffine P.A P.isLB P.ample).of_lbIso (LB.isLB_pull hL₀ π) hw.symm

end GlobalTheory.PolFlatDescent
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataNearTwoPrimes
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSectionNonzeroNearTwo
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSectionNonzeroNearTwo
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TwoPrimeSection

open TopologicalSpace

section General

variable {X : Scheme.{0}} {L : LB X}

theorem exists_global [CompactSpace X] [QuasiSeparatedSpace X] (hL : L.IsLB) (a : Γ(X, ⊤)) {V : X.Opens}
    (hV : X.basicOpen a ≤ V) {θ : ∀ i, Γ(X, V ⊓ L.U i)} (hθ : θ ∈ secOn L V) {g : X} (hg : g ∈ X.basicOpen a)
    {i : L.ι} (hi : g ∈ X.basicOpen (θ i)) : ∃ u : L.Sec, g ∈ Out.nonzeroLocus u := by
  have mem_nonzeroLocus (s : L.Sec) (x : X) :
      x ∈ Out.nonzeroLocus s ↔ ∃ k, x ∈ L.U k ∧ IsUnit (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (s.f k)) := by
    refine Opens.mem_iSup.trans (exists_congr fun k => ⟨fun h => ?_, fun ⟨h, hu⟩ => ?_⟩)
    · have hk : x ∈ L.U k := X.basicOpen_le _ h
      refine ⟨hk, ?_⟩
      rw [gs_eq (𝟙 X) x _ hk]
      exact (X.mem_basicOpen _ _ hk).1 h
    · rw [gs_eq (𝟙 X) x _ h] at hu
      exact (X.mem_basicOpen _ _ h).2 hu
  let topSec (s : Γ(GlobalTheory.LB.toMod L, ⊤)) : L.Sec :=
    ⟨fun i => resG X (le_inf le_top le_rfl) (GlobalTheory.LB.coord s i),
      fun i j => by
        change resG X _ (resG X _ _) = _ * resG X _ (resG X _ _)
        rw [GlobalTheory.LB.resG_resG, GlobalTheory.LB.resG_resG, GlobalTheory.LB.coord_rel s i j _ _ le_rfl, GlobalTheory.LB.resG_self]⟩
  haveI := GlobalTheory.LB.isQuasicoherent_toMod hL
  obtain ⟨n, t, ht⟩ := QCoh.Qcqs.exists_pow_smul_eq_res_of_qcqs (GlobalTheory.LB.toMod L)
    isCompact_univ isQuasiSeparated_univ a le_top rfl
    (((GlobalTheory.LB.toMod L).presheaf.map (homOfLE hV).op ((GlobalTheory.LB.secOnEquiv _ _).symm ⟨θ, hθ⟩)))
  have hi' : g ∈ V ⊓ L.U i := X.basicOpen_le _ hi
  have hm : (𝟙 X : X ⟶ X) g ∈ X.basicOpen a ⊓ L.U i := ⟨hg, hi'.2⟩
  refine ⟨topSec t, (mem_nonzeroLocus _ _).2 ⟨i, hi'.2, ?_⟩⟩
  have q := congrArg (fun s => gs (𝟙 X) g _ (GlobalTheory.LB.coord s i)) ht
  have e : gs (𝟙 X) g (L.U i) ((topSec t).f i) =
      gs (𝟙 X) g ⊤ a ^ n * gs (𝟙 X) g (V ⊓ L.U i) (θ i) := by
    refine (gs_res (𝟙 X) g _ hi'.2 _).trans ((gs_res (𝟙 X) g _ hm _).symm.trans (q.symm.trans
      ((gs_mul (𝟙 X) g _ hm _ _).trans (congrArg₂ (· * ·) ?_ (gs_res (𝟙 X) g _ hm _)))))
    exact (gs_res (𝟙 X) g _ hm _).trans ((LBGerm.gs_pow (𝟙 X) g _ hg _ _).trans
      (congrArg (· ^ n) (gs_res (𝟙 X) g _ hg _)))
  rw [e]
  exact (((LBGerm.isUnit_gs_iff (𝟙 X) g ⊤ trivial a).2 hg).pow n).mul
    ((LBGerm.isUnit_gs_iff (𝟙 X) g _ hi' _).2 hi)

def add (s t : L.Sec) : L.Sec :=
  ⟨fun i => s.f i + t.f i, fun i j => by rw [map_add (f := _), map_add (f := _), s.compat i j, t.compat i j, mul_add]⟩

theorem add_comm' (s t : L.Sec) : add s t = add t s := by
  unfold add
  simp only [add_comm (s.f _)]

theorem mem_nonzeroLocus_add {s t : L.Sec} {y : X} (hs : y ∈ Out.nonzeroLocus s) (ht : y ∉ Out.nonzeroLocus t) :
    y ∈ Out.nonzeroLocus (add s t) := by
  have mem_nonzeroLocus (s : L.Sec) (x : X) :
      x ∈ Out.nonzeroLocus s ↔ ∃ k, x ∈ L.U k ∧ IsUnit (ReciprocityTheory.ChartRestriction.G.Geo.Tor.gs (𝟙 X) x _ (s.f k)) := by
    refine Opens.mem_iSup.trans (exists_congr fun k => ⟨fun h => ?_, fun ⟨h, hu⟩ => ?_⟩)
    · have hk : x ∈ L.U k := X.basicOpen_le _ h
      refine ⟨hk, ?_⟩
      rw [gs_eq (𝟙 X) x _ hk]
      exact (X.mem_basicOpen _ _ hk).1 h
    · rw [gs_eq (𝟙 X) x _ h] at hu
      exact (X.mem_basicOpen _ _ h).2 hu
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hs
  refine (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩
  have hn : ¬ IsUnit (gs (𝟙 X) y (L.U k) (t.f k)) := fun h => ht ((mem_nonzeroLocus _ _).2 ⟨k, hk, h⟩)
  have e : gs (𝟙 X) y (L.U k) ((add s t).f k) = gs (𝟙 X) y (L.U k) (s.f k) + gs (𝟙 X) y (L.U k) (t.f k) :=
    gs_add (𝟙 X) y _ hk _ _
  rw [e]
  by_contra h
  have h₁ := (IsLocalRing.mem_maximalIdeal _).2 h
  have h₂ := (IsLocalRing.mem_maximalIdeal _).2 hn
  have h₃ := Ideal.sub_mem _ h₁ h₂
  rw [add_sub_cancel_right] at h₃
  exact (IsLocalRing.mem_maximalIdeal _).1 h₃ u

end General

theorem exists_basicOpen_two {R : Type} [CommRing R] {U : Set (PrimeSpectrum R)} (hU : IsOpen U)
    {p q : PrimeSpectrum R} (hp : p ∈ U) (hq : q ∈ U) :
    ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∀ z : PrimeSpectrum R, r ∉ z.asIdeal → z ∈ U := by
  obtain ⟨I, hI⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).1 hU.isClosed_compl
  have key : ∀ z : PrimeSpectrum R, z ∈ U ↔ ¬ I ≤ z.asIdeal := fun z => by
    rw [← Set.notMem_compl_iff, hI]
    rfl
  have : ¬ (I : Set R) ⊆ p.asIdeal ∪ q.asIdeal := fun h =>
    (Ideal.subset_union.1 h).elim ((key p).1 hp) ((key q).1 hq)
  obtain ⟨r, hr, hn⟩ := Set.not_subset.1 this
  exact ⟨r, fun h => hn (Or.inl h), fun h => hn (Or.inr h), fun z hz => (key z).2 fun h => hz (h hr)⟩

theorem exists_sec_fibre (hL : Out.Laws) (hL₂ : Out.Laws2) {R : Type} [CommRing R] (Q : Out.PolAV (Sp R)) (p : Sp R) :
    ∃ th : Q.L.Sec, ∃ x : Q.A.left, Q.A.hom x = p ∧ x ∈ Out.nonzeroLocus th := by
  obtain ⟨V, hV, θ, hθ, -, nz⟩ := PushInv.pushInvertible_any hL₂.secBaseChangeAny hL.globalSectionsRank _ Q p
  obtain ⟨g, i, hg, hi⟩ := nz p hV
  obtain ⟨f, hf, hpf⟩ := (isAffineOpen_top (Sp R)).exists_basicOpen_le (V := V) ⟨p, hV⟩ trivial
  have := Q.isAb.proper
  have : CompactSpace Q.A.left := QuasiCompact.compactSpace_of_compactSpace Q.A.hom
  have : QuasiSeparatedSpace Q.A.left := quasiSeparatedSpace_of_quasiSeparated Q.A.hom
  have e := Scheme.preimage_basicOpen_top Q.A.hom f
  obtain ⟨u, hu⟩ := exists_global Q.isLB (Q.A.hom.appTop f) (e.ge.trans (Q.A.hom.preimage_mono hf)) hθ
    (g := g) (e.le (show Q.A.hom g ∈ (Sp R).basicOpen f from hg ▸ hpf)) hi
  exact ⟨u, g, hg, hu⟩

open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

theorem main : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), ∃ (th : Q.L.Sec) (r : R), r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∀ z : Sp R, r ∉ z.asIdeal → ∃ x : Q.A.left, Q.A.hom x = z ∧ x ∈ Out.nonzeroLocus th := by
  intro hL hL₂ R _ _ Q p q
  obtain ⟨th, hp, hq⟩ : ∃ th : Q.L.Sec, (∃ x : Q.A.left, Q.A.hom x = p ∧ x ∈ Out.nonzeroLocus th) ∧
      ∃ x : Q.A.left, Q.A.hom x = q ∧ x ∈ Out.nonzeroLocus th := by
    obtain ⟨s, x, hx, hs⟩ := exists_sec_fibre hL hL₂ Q p
    obtain ⟨t, y, hy, ht⟩ := exists_sec_fibre hL hL₂ Q q
    by_cases h₁ : y ∈ Out.nonzeroLocus s
    · exact ⟨s, ⟨x, hx, hs⟩, y, hy, h₁⟩
    by_cases h₂ : x ∈ Out.nonzeroLocus t
    · exact ⟨t, ⟨x, hx, h₂⟩, y, hy, ht⟩
    exact ⟨add s t, ⟨x, hx, mem_nonzeroLocus_add hs h₂⟩, y, hy, add_comm' t s ▸ mem_nonzeroLocus_add ht h₁⟩
  have := Q.isAb.smooth
  obtain ⟨x, hx, hx'⟩ := hp
  obtain ⟨y, hy, hy'⟩ := hq
  obtain ⟨r, h₁, h₂, h₃⟩ := exists_basicOpen_two (R := R) (p := p) (q := q)
    (Q.A.hom.isOpenMap _ (Out.nonzeroLocus th).isOpen) ⟨x, hx', hx⟩ ⟨y, hy', hy⟩
  refine ⟨th, r, h₁, h₂, fun z hz => ?_⟩
  obtain ⟨w, hw, e⟩ := h₃ z hz
  exact ⟨w, e, hw⟩

end GlobalTheory.TwoPrimeSection
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsPrincipalPolarizationSectionNonzeroNearTwoStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalPolarization_section_nonzero_near_two_primes : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), ∃ (th : Q.L.Sec) (r : R), r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∀ z : Sp R, r ∉ z.asIdeal → ∃ x : Q.A.left, Q.A.hom x = z ∧ x ∈ Out.nonzeroLocus th := by
  first | exact @GlobalTheory.TwoPrimeSection.main | exact GlobalTheory.TwoPrimeSection.main | (intros; apply GlobalTheory.TwoPrimeSection.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataNearTwoPrimes
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam

theorem exists_keyIn_polPB {R R₁ R' : Type} [CommRing R] [CommRing R₁] [CommRing R'] (Q : Out.PolAV (Sp R))
    (hg : 1 ≤ Q.g) (f₁ : R →+* R₁) (g : R₁ →+* R') (f : R →+* R') (hf : g.comp f₁ = f) (th : Q.L.Sec)
    (hth : ∀ s : Sp R', ∃ x : Q.A.left, Q.A.hom x = spMap f s ∧ x ∈ Out.nonzeroLocus th)
    (v : Fin Q.g → (epsR R₁ ⟶ (Over.pullback (spMap f₁)).obj Q.A)) (hv : IsLieBasis v) :
    ∃ (y : KeyIn R') (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap f) φ := by
  have h := isGrpPullback_pullback Q.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj Q.A).left ⟶ Q.A.left := pullback.fst Q.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := LB.isLB_pull Q.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  let P' : Out.PolAV (Sp R') :=
    { A := (Over.pullback (spMap f)).obj Q.A
      isAb := Out.TLinPf.isAb_pullback (spMap f) Q.A Q.isAb
      g := Q.g
      smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 Q.smoothDim
      L := Q.L.pull φ
      isLB := hL'
      rigid := PolBaseChange.rigidified_pull h Q.rigid
      sym := PolBaseChange.sym_pull h Q.sym
      ample := relAmple_pull h.1 Q.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) Q.ample
      ktriv := kTriv_pull h Q.isLB hL' hw Q.ktriv }
  obtain ⟨rig, hr⟩ := P'.rigid
  obtain ⟨th', hth'⟩ := sec_pull_down hw Q.isLB hL' th
  have h₁ := isGrpPullback_pullback Q.A (spMap f₁)
  have hA₁ := Out.TLinPf.isAb_pullback (spMap f₁) Q.A Q.isAb
  have c₁ := hA₁.comm
  have c₂ : IsCommMonObj P'.A := P'.isAb.comm
  have e : spMap g ≫ spMap f₁ = spMap f := by
    rw [← hf, ← Spec.map_comp]; rfl
  have w : φ ≫ Q.A.hom = P'.A.hom ≫ spMap g ≫ spMap f₁ := by rw [e]; exact h.1.w
  have w₁ : φ ≫ Q.A.hom = (P'.A.hom ≫ spMap g) ≫ spMap f₁ := by rw [Category.assoc]; exact w
  have h₂ : IsGrpPullback P'.A _ (spMap g) (h₁.1.lift _ _ w₁) :=
    IsGrpPullback.cancel h₁ (h.congr e.symm (h₁.1.lift_fst _ _ w₁).symm) (h₁.1.lift_snd _ _ w₁)
  obtain ⟨v', hb', -⟩ := exists_isLieBasis_baseChange R₁ R' g _ P'.A _ h₂ hA₁.smooth Q.g v hv
  refine ⟨⟨P', hg, rig, hr, th', fun s => ?_, v', hb'⟩, φ, h, rfl, ⟨idIso _, idIso_isGen hL'⟩⟩
  obtain ⟨z, hz, hz'⟩ := hth s
  obtain ⟨y, rfl, hy⟩ := Scheme.exists_preimage_of_isPullback h.1 z s hz
  obtain ⟨k, hk, u⟩ := (mem_nonzeroLocus _ _).1 hz'
  refine ⟨y, hy, (mem_nonzeroLocus _ _).2 ⟨fun _ => k, mem_pull.2 hk, ?_⟩⟩
  have u₁ : IsUnit (gs φ y _ (th.f k)) := by rw [gs_stalkMap φ y _ hk]; exact u.map _
  have e := hth' _ (𝟙 _) y k (fun _ => k) hk (mem_pull.2 hk)
  rw [Category.id_comp] at e
  exact isUnit_of_mul_isUnit_right (e ▸ u₁)

theorem exists_keyIn_near_two : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), 1 ≤ Q.g → ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ (y : KeyIn (Localization.Away r)) (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap (algebraMap R (Localization.Away r))) φ := by
  intro hL hL₂ R _ _ Q p q hg
  obtain ⟨th, a, ap, aq, ha⟩ := GlobalTheory.T.exists_principalPolarization_section_nonzero_near_two_primes hL hL₂ R Q p q
  have c : IsCommMonObj Q.A := Q.isAb.comm
  obtain ⟨b, bp, bq, v, hv⟩ := GlobalTheory.T.exists_lieBasis_away_avoiding_two_primes R Q.A Q.g Q.smoothDim p q
  refine ⟨b * a, fun h => (p.isPrime.mem_or_mem h).elim bp ap, fun h => (q.isPrime.mem_or_mem h).elim bq aq, ?_⟩
  refine exists_keyIn_polPB Q hg (algebraMap R (Localization.Away b))
    (IsLocalization.Away.awayToAwayRight (S := Localization.Away b) (P := Localization.Away (b * a)) b a) _
    (RingHom.ext fun x => IsLocalization.Away.awayToAwayRight_eq (S := Localization.Away b) b a x) th
    (fun s => ha _ fun h => ?_) v hv
  have h' : algebraMap R (Localization.Away (b * a)) a ∈ s.asIdeal := h
  have u : IsUnit (algebraMap R (Localization.Away (b * a)) (b * a)) := IsLocalization.Away.algebraMap_isUnit _
  rw [map_mul] at u
  exact s.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h' (isUnit_of_mul_isUnit_right u))

end GlobalTheory.KeyFam
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyDataNearTwoPrimesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_keyData_near_two_primes : Out.Laws → Out.Laws2 → ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (Q : Out.PolAV (Sp R)) (p q : PrimeSpectrum R), 1 ≤ Q.g → ∃ r : R, r ∉ p.asIdeal ∧ r ∉ q.asIdeal ∧ ∃ (y : KeyIn (Localization.Away r)) (φ : y.P.A.left ⟶ Q.A.left), PolPB y.P Q (spMap (algebraMap R (Localization.Away r))) φ := by
  first | exact @GlobalTheory.KeyFam.exists_keyIn_near_two | exact GlobalTheory.KeyFam.exists_keyIn_near_two | (intros; apply GlobalTheory.KeyFam.exists_keyIn_near_two <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.RingKrullDimLocalizationQuotientLe
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

namespace GlobalTheory.KeyKa

theorem ringKrullDim_localization_quotient_le {R : Type} [CommRing R] {k : ℕ} (f : Fin k → R) (m : Ideal R)
    [m.IsPrime] :
    ringKrullDim (Localization.AtPrime m ⧸
        Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))) ≤
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range f) : Set (PrimeSpectrum R)) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  have h₁ := (PrimeSpectrum.localization_comap_isInducing (R := R) (Localization.AtPrime m) m.primeCompl).comp
    (PrimeSpectrum.isEmbedding_comap_of_surjective _ (Ideal.Quotient.mk
      (Ideal.span (Set.range fun j => algebraMap R (Localization.AtPrime m) (f j))))
      Ideal.Quotient.mk_surjective).isInducing
  refine (h₁.codRestrict (s := PrimeSpectrum.zeroLocus (Set.range f)) fun p => ?_).topologicalKrullDim_le
  rintro _ ⟨j, rfl⟩
  change Ideal.Quotient.mk _ (algebraMap R (Localization.AtPrime m) (f j)) ∈ p.asIdeal
  rw [Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_range_self (f := fun j => algebraMap R (Localization.AtPrime m) (f j)) j))]
  exact p.asIdeal.zero_mem

theorem ofList_take_ofFn {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R) (i : ℕ) :
    Ideal.ofList ((List.ofFn f).take i) = Ideal.span (f '' {j | j.val < i}) := by
  unfold Ideal.ofList
  congr 1
  ext a
  simp only [Set.mem_setOf_eq, List.mem_take_iff_getElem, List.length_ofFn, List.getElem_ofFn, Set.mem_image]
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨⟨j, by omega⟩, by simp only; omega, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨j, by have := j.2; omega, rfl⟩

theorem isWeaklyRegular_of_dim_zeroLocus {R : Type} [CommRing R] {g : ℕ} (f : Fin g → R)
    (hreg : ∀ (m : Ideal R) [m.IsMaximal],
      IsRegularLocalRing (Localization.AtPrime m) ∧ ringKrullDim (Localization.AtPrime m) = g)
    (hdim : ∀ (k : ℕ) (hk : k ≤ g),
      (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) : Set (PrimeSpectrum R)).Nonempty →
      topologicalKrullDim (PrimeSpectrum.zeroLocus (Set.range fun j => f (Fin.castLE hk j)) :
        Set (PrimeSpectrum R)) ≤ ((g - k : ℕ) : WithBot ℕ∞)) :
    RingTheory.Sequence.IsWeaklyRegular R (List.ofFn f) := by
  refine ⟨fun i hi => ?_⟩
  have hi' : i < g := by simpa using hi
  rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn]
  simp only [smul_eq_mul, Ideal.mul_top]
  intro a ha
  refine Ideal.mem_of_localization_maximal fun m hm => ?_
  have ha' := Ideal.mem_map_of_mem (algebraMap R (Localization.AtPrime m)) ha
  rw [map_mul] at ha'
  by_cases hall : ∀ j : Fin g, j.val ≤ i → f j ∈ m
  · obtain ⟨h₁, h₂⟩ := hreg m
    have hk : i + 1 ≤ g := hi'
    have hd := (ringKrullDim_localization_quotient_le (fun j => f (Fin.castLE hk j)) m).trans
      (hdim (i + 1) hk ⟨⟨m, hm.isPrime⟩, by
        rintro _ ⟨j, rfl⟩
        exact hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)⟩)
    have hr := GlobalTheory.isRegular_ofFn_of_ringKrullDim_quotient_add_le (Localization.AtPrime m) g (i + 1)
      (fun j => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) h₂
      (fun j => (IsLocalization.AtPrime.to_map_mem_maximal_iff _ m _).2
        (hall _ (by have := j.2; simp only [Fin.val_castLE]; omega)))
      ((add_le_add_left hd _).trans (by
        rw [← Nat.cast_add, Nat.sub_add_cancel hk]))
    have h₃ := hr.toIsWeaklyRegular.regular_mod_prev i (by simp)
    rw [isSMulRegular_quotient_iff_mem_of_smul_mem, ofList_take_ofFn, List.getElem_ofFn] at h₃
    simp only [smul_eq_mul, Ideal.mul_top] at h₃
    have e : Ideal.map (algebraMap R (Localization.AtPrime m)) (Ideal.span (f '' {j | j.val < i})) =
        Ideal.span ((fun j : Fin (i + 1) => algebraMap R (Localization.AtPrime m) (f (Fin.castLE hk j))) ''
          {j | j.val < i}) := by
      rw [Ideal.map_span]
      congr 1
      ext b
      constructor
      · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        exact ⟨⟨j, Nat.lt_succ_of_lt hj⟩, hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        exact ⟨_, ⟨Fin.castLE hk j, hj, rfl⟩, rfl⟩
    rw [e] at ha' ⊢
    exact h₃ _ ha'
  · push Not at hall
    obtain ⟨j, hj, hjm⟩ := hall
    have hu : IsUnit (algebraMap R (Localization.AtPrime m) (f j)) :=
      IsLocalization.map_units _ (⟨f j, hjm⟩ : m.primeCompl)
    rcases hj.eq_or_lt with hj | hj
    · subst hj
      exact (Ideal.unit_mul_mem_iff_mem _ hu).1 ha'
    · rw [Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_image_of_mem f (show j ∈ {j : Fin g | j.val < i} from hj)))) hu]
      trivial

theorem isWeaklyRegular_of_finZ : Out.Laws → ∀ (K : Type) [Field K] [IsAlgClosed K] (x : KeyIn K) (n : ℕ) (s : Fin x.P.g → RR x n) (V : x.P.A.left.Opens) (c : x.P.L.ι) (h : V ≤ x.P.L.U c), 1 ≤ n → FinZ x s → IsAffineOpen V → RingTheory.Sequence.IsWeaklyRegular Γ(x.P.A.left, V) (List.ofFn fun i => resG x.P.A.left h ((s i).f c)) := by
  intro hL K _ _ x n s V c h hn hZ hV
  refine isWeaklyRegular_of_dim_zeroLocus _ (fun m _ => ?_) fun k hk hne => ?_
  · exact GlobalTheory.isRegularLocalRing_and_ringKrullDim_eq_of_polAV K x.P Γ(x.P.A.left, V) hV.fromSpec m _ inferInstance
  · let W : Set x.P.A.left := {y | ∀ j : Fin k, y ∉ Out.nonzeroLocus (s (Fin.castLE hk j))}
    have hW : IsClosed W := by
      have : W = ⋂ j : Fin k, (Out.nonzeroLocus (s (Fin.castLE hk j)) : Set x.P.A.left)ᶜ := by
        ext y; simp [W]
      rw [this]
      exact isClosed_iInter fun j => (Out.nonzeroLocus _).isOpen.isClosed_compl
    have hmem : ∀ p : (PrimeSpectrum.zeroLocus (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))), hV.fromSpec p.1 ∈ W := by
      intro p j hj
      have hpV : hV.fromSpec p.1 ∈ V := by
        have : hV.fromSpec p.1 ∈ Set.range hV.fromSpec := ⟨_, rfl⟩
        rwa [hV.range_fromSpec] at this
      have h₁ := (GlobalTheory.AmpleSpan.isUnit_gs_iff (𝟙 _) _ _ (h hpV) _).1
        ((GlobalTheory.AmpleSpan.mem_nonzeroLocus_iff_gs (s (Fin.castLE hk j)) (𝟙 _) (hV.fromSpec p.1) (k := c) (h hpV)).1 hj)
      have h₂ : hV.fromSpec p.1 ∈ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := by
        have := x.P.A.left.basicOpen_res (show Γ(x.P.A.left, x.P.L.U c) from (s (Fin.castLE hk j)).f c) (homOfLE h).op
        exact this.ge ⟨hpV, h₁⟩
      have h₃ : p.1 ∈ hV.fromSpec ⁻¹ᵁ x.P.A.left.basicOpen (resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) := h₂
      rw [hV.fromSpec_preimage_basicOpen] at h₃
      exact h₃ (p.2 ⟨j, rfl⟩)
    have hind : Topology.IsInducing fun p : (PrimeSpectrum.zeroLocus
        (Set.range fun j => resG x.P.A.left h ((s (Fin.castLE hk j)).f c)) :
        Set (PrimeSpectrum Γ(x.P.A.left, V))) => hV.fromSpec p.1 :=
      hV.fromSpec.isOpenEmbedding.isInducing.comp Topology.IsInducing.subtypeVal
    refine (hind.codRestrict hmem).topologicalKrullDim_le.trans ?_
    obtain ⟨p, hp⟩ := hne
    refine GlobalTheory.T.topologicalKrullDim_le_of_finite_common_zeros hL K x n (x.P.g - k) (fun j => s ⟨k + j, by have := j.2; omega⟩) W hn hW
      ⟨_, hmem ⟨p, hp⟩⟩ (Set.Finite.subset hZ ?_)
    rintro y ⟨hy₁, hy₂⟩ i
    by_cases hi : i.val < k
    · exact hy₁ ⟨i, hi⟩
    · have := hy₂ ⟨i - k, by have := i.2; omega⟩
      simp only [show k + (i.val - k) = i.val by omega] at this
      exact this

end GlobalTheory.KeyKa
end
