module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSemiAbelianImage
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgHomLiftsSqZeroClassifiedByDifferentials

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Special

theorem spc {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

theorem lbIso_pull' {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {a : Y ⟶ X} (h : LBIso M (L.pull a)) (j : Z ⟶ Y)
    {a' : Z ⟶ X} (e : a' = j ≫ a) : LBIso (M.pull j) (L.pull a') :=
  LBIso.chartPull (Geo.Tor.chartPullPull M j j rfl) (Geo.Tor.chartPullSame L _ (fun _ => a) _ j fun _ => e) h

theorem main : ∀ (R₁ R₂ O K F₁ F₂ M Γ : Type) [CommRing R₁] [CommRing R₂] [CommRing O] [Field K] [Field F₁] [Field F₂] [Algebra F₁ K] [Algebra F₂ K] (P₁ : PolAV (Sp R₁)) (P₂ : PolAV (Sp R₂)) (f₁ : R₁ →+* O) (f₂ : R₂ →+* O) (e₁ : M → (P₁.A ⟶ P₁.A)) (e₂ : M → (P₂.A ⟶ P₂.A)) (t₁ : Γ → (baseOver (Sp R₁) ⟶ P₁.A)) (t₂ : Γ → (baseOver (Sp R₂) ⟶ P₂.A)), (∃ (P : PolAV (Sp O)) (b₁ : P.A.left ⟶ P₁.A.left) (b₂ : P.A.left ⟶ P₂.A.left), IsGrpPullback P.A P₁.A (spMap f₁) b₁ ∧ IsGrpPullback P.A P₂.A (spMap f₂) b₂ ∧ LBIso P.L (P₁.L.pull b₁) ∧ LBIso P.L (P₂.L.pull b₂) ∧ (∀ E, ∃ e : P.A ⟶ P.A, e.left ≫ b₁ = b₁ ≫ (e₁ E).left ∧ e.left ≫ b₂ = b₂ ≫ (e₂ E).left) ∧ ∀ x, ∃ w : Sp O ⟶ P.A.left, w ≫ P.A.hom = 𝟙 _ ∧ w ≫ b₁ = spMap f₁ ≫ (t₁ x).left ∧ w ≫ b₂ = spMap f₂ ≫ (t₂ x).left) → ∀ (v : O →+* K) (k₁ : R₁ →+* F₁) (k₂ : R₂ →+* F₂), (algebraMap F₁ K).comp k₁ = v.comp f₁ → (algebraMap F₂ K).comp k₂ = v.comp f₂ → ∀ (A₁ : PolAV (Sp F₁)) (A₂ : PolAV (Sp F₂)) (φ₁ : A₁.A.left ⟶ P₁.A.left) (φ₂ : A₂.A.left ⟶ P₂.A.left), IsGrpPullback A₁.A P₁.A (spMap k₁) φ₁ → IsGrpPullback A₂.A P₂.A (spMap k₂) φ₂ → LBIso A₁.L (P₁.L.pull φ₁) → LBIso A₂.L (P₂.L.pull φ₂) → ∃ (P₀ : PolAV (Sp K)) (a₁ : P₀.A.left ⟶ A₁.A.left) (a₂ : P₀.A.left ⟶ A₂.A.left), IsGrpPullback P₀.A A₁.A (spMap (algebraMap F₁ K)) a₁ ∧ IsGrpPullback P₀.A A₂.A (spMap (algebraMap F₂ K)) a₂ ∧ LBIso P₀.L (A₁.L.pull a₁) ∧ LBIso P₀.L (A₂.L.pull a₂) ∧ (∀ x, ∃ w : Sp K ⟶ P₀.A.left, w ≫ P₀.A.hom = 𝟙 _ ∧ w ≫ a₁ ≫ φ₁ = spMap (v.comp f₁) ≫ (t₁ x).left ∧ w ≫ a₂ ≫ φ₂ = spMap (v.comp f₂) ≫ (t₂ x).left) ∧ ∀ (E : M) (w w₂ : Sp K ⟶ P₀.A.left), w ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ P₀.A.hom = 𝟙 _ → w₂ ≫ a₁ ≫ φ₁ = w ≫ a₁ ≫ φ₁ ≫ (e₁ E).left → w₂ ≫ a₂ ≫ φ₂ = w ≫ a₂ ≫ φ₂ ≫ (e₂ E).left := by
  intro R₁ R₂ O K F₁ F₂ M Γ _ _ _ _ _ _ _ _ P₁ P₂ f₁ f₂ e₁ e₂ t₁ t₂ hS v k₁ k₂ hk₁ hk₂ A₁ A₂ φ₁ φ₂ hA₁ hA₂ hL₁ hL₂
  obtain ⟨P, b₁, b₂, hb₁, hb₂, hPL₁, hPL₂, he, ht⟩ := hS
  let P₀ : PolAV (Sp K) := GlobalTheory.StrictPull.polPull P (spMap v)
  let β : P₀.A.left ⟶ P.A.left := pullback.fst P.A.hom (spMap v)
  have hβ : IsGrpPullback P₀.A P.A (spMap v) β := isGrpPullback_pullback P.A (spMap v)
  have eq₁ : spMap (algebraMap F₁ K) ≫ spMap k₁ = spMap v ≫ spMap f₁ := by rw [spc, spc, hk₁]
  have eq₂ : spMap (algebraMap F₂ K) ≫ spMap k₂ = spMap v ≫ spMap f₂ := by rw [spc, spc, hk₂]
  have c₁ := hβ.comp hb₁
  have c₂ := hβ.comp hb₂
  have w₁ : (β ≫ b₁) ≫ P₁.A.hom = (P₀.A.hom ≫ spMap (algebraMap F₁ K)) ≫ spMap k₁ := by
    rw [c₁.1.w, Category.assoc, eq₁]
  have w₂ : (β ≫ b₂) ≫ P₂.A.hom = (P₀.A.hom ≫ spMap (algebraMap F₂ K)) ≫ spMap k₂ := by
    rw [c₂.1.w, Category.assoc, eq₂]
  let a₁ : P₀.A.left ⟶ A₁.A.left := hA₁.1.lift _ _ w₁
  let a₂ : P₀.A.left ⟶ A₂.A.left := hA₂.1.lift _ _ w₂
  have ha₁ : a₁ ≫ φ₁ = β ≫ b₁ := hA₁.1.lift_fst _ _ w₁
  have ha₂ : a₂ ≫ φ₂ = β ≫ b₂ := hA₂.1.lift_fst _ _ w₂
  have ga₁ : IsGrpPullback P₀.A A₁.A (spMap (algebraMap F₁ K)) a₁ :=
    IsGrpPullback.cancel hA₁ (c₁.congr eq₁.symm ha₁.symm) (hA₁.1.lift_snd _ _ w₁)
  have ga₂ : IsGrpPullback P₀.A A₂.A (spMap (algebraMap F₂ K)) a₂ :=
    IsGrpPullback.cancel hA₂ (c₂.congr eq₂.symm ha₂.symm) (hA₂.1.lift_snd _ _ w₂)
  have hP₀L : P₀.L = P.L.pull β := rfl
  refine ⟨P₀, a₁, a₂, ga₁, ga₂, ?_, ?_, fun x => ?_, fun E w w₂' hw hw₂ h => ?_⟩
  · rw [hP₀L]
    exact LBIso.trans (pull_isLB P.isLB _) (pull_isLB P₁.isLB _) (pull_isLB A₁.isLB _)
      (lbIso_pull' hPL₁ β rfl) (lbIso_pull' hL₁ a₁ ha₁.symm).symm
  · rw [hP₀L]
    exact LBIso.trans (pull_isLB P.isLB _) (pull_isLB P₂.isLB _) (pull_isLB A₂.isLB _)
      (lbIso_pull' hPL₂ β rfl) (lbIso_pull' hL₂ a₂ ha₂.symm).symm
  · obtain ⟨wO, hs, h₁, h₂⟩ := ht x
    have sq : (spMap v ≫ wO) ≫ P.A.hom = 𝟙 _ ≫ spMap v := by
      rw [Category.assoc, hs, Category.comp_id, Category.id_comp]
    have hl : pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β = spMap v ≫ wO := pullback.lift_fst _ _ _
    refine ⟨pullback.lift (spMap v ≫ wO) (𝟙 _) sq, pullback.lift_snd _ _ _, ?_, ?_⟩
    · calc pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ a₁ ≫ φ₁ = pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β ≫ b₁ := congrArg (fun z => pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ z) ha₁
        _ = (pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β) ≫ b₁ := (Category.assoc _ _ _).symm
        _ = _ := by rw [hl, Category.assoc, h₁, ← Category.assoc, spc]
    · calc pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ a₂ ≫ φ₂ = pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β ≫ b₂ := congrArg (fun z => pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ z) ha₂
        _ = (pullback.lift (spMap v ≫ wO) (𝟙 _) sq ≫ β) ≫ b₂ := (Category.assoc _ _ _).symm
        _ = _ := by rw [hl, Category.assoc, h₂, ← Category.assoc, spc]
  · obtain ⟨e, he₁, he₂⟩ := he E
    have sqe : (β ≫ e.left) ≫ P.A.hom = P₀.A.hom ≫ spMap v := by
      rw [Category.assoc, Over.w e]; exact pullback.condition
    let e₀ : P₀.A.left ⟶ P₀.A.left := pullback.lift (β ≫ e.left) P₀.A.hom sqe
    have he₀ : e₀ ≫ β = β ≫ e.left := pullback.lift_fst _ _ _
    have he₀' : e₀ ≫ P₀.A.hom = P₀.A.hom := pullback.lift_snd _ _ _
    have key : w₂' = w ≫ e₀ := by
      apply c₁.1.hom_ext
      · calc w₂' ≫ β ≫ b₁ = w₂' ≫ a₁ ≫ φ₁ := by rw [ha₁]
          _ = w ≫ a₁ ≫ φ₁ ≫ (e₁ E).left := h
          _ = w ≫ (a₁ ≫ φ₁) ≫ (e₁ E).left := by simp only [Category.assoc]
          _ = w ≫ β ≫ (b₁ ≫ (e₁ E).left) := by rw [ha₁, Category.assoc]
          _ = w ≫ (β ≫ e.left) ≫ b₁ := by rw [← he₁, Category.assoc]
          _ = (w ≫ e₀) ≫ β ≫ b₁ := by rw [← he₀]; simp only [Category.assoc]
      · rw [hw₂, Category.assoc, he₀', hw]
    calc w₂' ≫ a₂ ≫ φ₂ = (w ≫ e₀) ≫ β ≫ b₂ := by rw [key, ha₂]
      _ = w ≫ (e₀ ≫ β) ≫ b₂ := by simp only [Category.assoc]
      _ = w ≫ β ≫ (e.left ≫ b₂) := by rw [he₀, Category.assoc]
      _ = w ≫ (β ≫ b₂) ≫ (e₂ E).left := by rw [he₂]; simp only [Category.assoc]
      _ = w ≫ a₂ ≫ φ₂ ≫ (e₂ E).left := by rw [← ha₂]; simp only [Category.assoc]

end GlobalTheory.Poinc.Special
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplAtFactorOfIsAdicComplete
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TChart

theorem exists_complAt_factor_of_isAdicComplete : ∀ (W : Type) [CommRing W] [IsRegularLocalRing W] (I : Type) [Fintype I] (V : Type) [CommRing V] [IsLocalRing V], IsAdicComplete (maximalIdeal V) V → ∀ ψV : MvPolynomial I W →+* V, IsLocalHom (ψV.comp MvPolynomial.C) → ∃ (R : Type) (_ : CommRing R) (_ : IsDomain R) (_ : IsLocalRing R) (ψ : MvPolynomial I W →+* R) (θ : R →+* V), IsComplAt ψ ∧ IsLocalHom θ ∧ θ.comp ψ = ψV ∧ IsLocalHom (ψ.comp MvPolynomial.C) := by
  intro W _ _ I _ V _ _ hV ψV hC
  haveI := hV
  let A := MvPolynomial I W
  let q : Ideal A := (maximalIdeal V).comap ψV
  haveI : q.IsPrime := Ideal.comap_isPrime _ _
  let L := Localization.AtPrime q
  haveI : IsRegularRing W := GlobalTheory.isRegularRing_of_isRegularLocalRing W
  haveI : IsRegularLocalRing L := inferInstance
  let R := AdicCompletion (maximalIdeal L) L
  haveI : IsRegularLocalRing R := GlobalTheory.RegularCompletion.isRegularLocalRing_adicCompletion L
  haveI : IsDomain R := inferInstance
  haveI : IsNoetherianRing R := inferInstance
  have hfg : (maximalIdeal L).FG := (maximalIdeal L).fg_of_isNoetherianRing
  have hunit : ∀ y : q.primeCompl, IsUnit (ψV y) := fun y => by
    have := y.2
    exact IsLocalRing.notMem_maximalIdeal.mp this
  let φ : L →+* V := IsLocalization.lift (M := q.primeCompl) (S := L) hunit
  have hφ : φ.comp (algebraMap A L) = ψV := IsLocalization.lift_comp hunit
  have hmL : (maximalIdeal L) = q.map (algebraMap A L) := (Localization.AtPrime.map_eq_maximalIdeal).symm
  have hk : (maximalIdeal L).map φ ^ 1 ≤ maximalIdeal V := by
    rw [pow_one, hmL, Ideal.map_map, hφ]
    exact Ideal.map_comap_le
  obtain ⟨θ, hθ, -⟩ := GlobalTheory.exists_extend_adicCompletion φ (maximalIdeal L) (maximalIdeal V) hk
  let c : L →+* R := algebraMap L R
  let ψ : A →+* R := c.comp (algebraMap A L)
  have hθψ : θ.comp ψ = ψV := by
    show θ.comp (c.comp (algebraMap A L)) = ψV
    rw [← RingHom.comp_assoc]
    show (θ.comp (algebraMap L R)).comp (algebraMap A L) = ψV
    rw [hθ, hφ]
  have hmR : maximalIdeal R = q.map ψ := by
    have h0 := AdicCompletion.maximalIdeal_eq_map (R := L)
    have hmL' : q.map (algebraMap A L) = maximalIdeal L := Localization.AtPrime.map_eq_maximalIdeal
    rw [h0]
    show _ = q.map (c.comp (algebraMap A L))
    rw [← Ideal.map_map, hmL']
  refine ⟨R, inferInstance, inferInstance, inferInstance, ψ, θ, ⟨inferInstance, inferInstance, ?_, ?_, ?_⟩, ?_, hθψ, ?_⟩
  · exact RingHom.Flat.comp (RingHom.flat_algebraMap_iff.2 (IsLocalization.flat L q.primeCompl))
      (RingHom.flat_algebraMap_iff.2 (AdicCompletion.flat_of_isNoetherian _))
  · apply le_antisymm Ideal.map_comap_le
    have : q ≤ (maximalIdeal R).comap ψ := by
      rw [← Ideal.map_le_iff_le_comap, ← hmR]
    rw [hmR]
    exact Ideal.map_mono (hmR ▸ this)
  · intro r
    obtain ⟨x, hx⟩ := (AdicCompletion.residueField_map_bijective_of_fg (R := L) hfg).2 (residue R r)
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl y
    refine ⟨a, s, ?_, ?_⟩
    · exact (IsLocalization.map_units L s).map c
    · have h1 : residue R (c (IsLocalization.mk' L a s)) = residue R r := by
        rw [← hx, ResidueField.map_residue]
      have h2 : r - c (IsLocalization.mk' L a s) ∈ maximalIdeal R := by
        rw [← residue_eq_zero_iff, (residue R).map_sub, h1, sub_self]
      have h3 : c (IsLocalization.mk' L a s) * ψ s = ψ a := by
        show c (IsLocalization.mk' L a s) * c (algebraMap A L s) = c (algebraMap A L a)
        rw [← map_mul, IsLocalization.mk'_spec]
      have : r * ψ s - ψ a = (r - c (IsLocalization.mk' L a s)) * ψ s := by
        rw [sub_mul, h3]
      rw [this]
      exact Ideal.mul_mem_right _ _ h2
  · haveI : IsLocalHom (θ.comp (algebraMap L R)) := by
      rw [hθ]
      apply ((IsLocalRing.local_hom_tfae φ).out 1 3).mpr
      simpa using hk
    exact GlobalTheory.isLocalHom_of_extend_adicCompletion hfg θ
  · refine ⟨fun a ha => hC.map_nonunit a ?_⟩
    have : θ ((ψ.comp MvPolynomial.C) a) = (ψV.comp MvPolynomial.C) a := by
      simp only [RingHom.comp_apply]
      exact congrArg (fun f : A →+* V => f (MvPolynomial.C a)) hθψ
    rw [← this]
    exact ha.map θ

end GlobalTheory.TChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsAmplePowSectionsCuttingOutClosed
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsAmplePowSectionsCuttingOutClosed
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CutOutSections

theorem sec_eq_zero_of_nonzeroLocus_eq_bot {Y : Scheme.{0}} [IsReduced Y] {M : LB Y} (s : M.Sec)
    (h : nonzeroLocus s = ⊥) : s = 0 := by
  apply DVR.SecOps.sec_ext
  intro k
  have hk : Y.basicOpen (s.f k) = ⊥ := le_bot_iff.1 ((basicOpen_le_nonzeroLocus s k).trans h.le)
  rw [AlgebraicGeometry.basicOpen_eq_bot_iff] at hk
  rw [hk]
  rfl

theorem eventually_isGenerated_lbPow {X : Scheme.{0}} {N : LB X} (hN : IsAmpleLB N) :
    ∀ᶠ k in atTop, IsGenerated (lbPow N k) := by
  refine (hN.eventually_isGenerated_tens_lbPow (LB.isLB_triv X)).mono fun k hk => ?_
  obtain ⟨c, u, hu⟩ := hk
  have hP := isLB_lbPow hN.isLB k
  have hT := isLB_tens (LB.isLB_triv X) hP
  obtain ⟨v, hv⟩ := CechPic.exists_generating_secs_of_cls_eq X _ _ hT hP
    (by simp only [CechPic.cls_tens (LB.isLB_triv X) hP, cls_triv, zero_add]) (Fin c) u hu
  exact ⟨c, v, hv⟩

theorem eventually_exists_secs_cutting_out : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∃ (r : ℕ) (κ : Fin r → (lbPow N l).Sec), (∀ i, GlobalTheory.secPull (κ i) (redι Z) = 0) ∧ (∀ i, ∀ y ∈ Z, y ∉ nonzeroLocus (κ i)) ∧ ∀ y, y ∉ Z → ∃ i, y ∈ nonzeroLocus (κ i) := by
  intro X _ _ p hp N Z hN
  have : AlgebraicGeometry.IsNoetherian X := isNoetherian_of_isProjOver hp
  let U : X.Opens := ⟨(Z : Set X)ᶜ, Z.isClosed.isOpen_compl⟩
  have hloc : ∀ y : U, ∃ n, 1 ≤ n ∧ ∃ s : (lbPow N n).Sec, (y : X) ∈ nonzeroLocus s ∧
      nonzeroLocus s ≤ U ∧ IsAffineOpen (nonzeroLocus s) := fun y => hN.exists_affine_le y.2
  choose n hn s hys hle _ using hloc
  have hc : IsCompact (U : Set X) := NoetherianSpace.isCompact _
  obtain ⟨T, hT⟩ := hc.elim_finite_subcover (fun y : U => (nonzeroLocus (s y) : Set X))
    (fun y => (nonzeroLocus (s y)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hys ⟨y, hy⟩⟩)
  obtain ⟨m, -, t, ht⟩ := exists_common_pow (fun y : T => n y) (fun y => hn y) (fun y => s y)
  obtain ⟨K, hK⟩ := eventually_atTop.1 (eventually_isGenerated_lbPow hN)
  refine eventually_atTop.2 ⟨K + m, fun l hl => ?_⟩
  obtain ⟨c, g, hg⟩ := hK (l - m) (by omega)
  have hml : m + (l - m) = l := by omega
  let κ' : T × Fin c → (lbPow N l).Sec := fun q => secCast hml (secMul (t q.1) (g q.2))
  have hκ' : ∀ q, nonzeroLocus (κ' q) = nonzeroLocus (s q.1) ⊓ nonzeroLocus (g q.2) := fun q => by
    simp only [κ', nonzeroLocus_secCast, nonzeroLocus_secMul, ht]
  have hb : ∀ q, ∀ y ∈ Z, y ∉ nonzeroLocus (κ' q) := fun q y hy h => by
    rw [hκ'] at h
    exact hle _ h.1 hy
  obtain ⟨r, ⟨e⟩⟩ := Finite.exists_equiv_fin (T × Fin c)
  refine ⟨r, fun i => κ' (e.symm i), fun i => ?_, fun i => hb _, fun y hy => ?_⟩
  · have := ReducedSubgroup.isReduced_subscheme_vanishingIdeal Z
    apply sec_eq_zero_of_nonzeroLocus_eq_bot
    rw [GlobalTheory.nonzeroLocus_secPull]
    refine le_bot_iff.1 fun z hz => ?_
    have hz' : redι Z z ∈ (Z : Set X) := by
      rw [← range_redι Z]
      exact Set.mem_range_self z
    exact hb _ _ hz' hz
  · obtain ⟨a, ha', hya'⟩ := Set.mem_iUnion₂.1 (hT hy)
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 (hg.ge (Set.mem_univ y))
    refine ⟨e (⟨a, ha'⟩, j), ?_⟩
    show y ∈ nonzeroLocus (κ' (e.symm (e (⟨a, ha'⟩, j))))
    rw [e.symm_apply_apply, hκ']
    exact ⟨hya', hj⟩

end GlobalTheory.CutOutSections
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsAmplePowSectionsCuttingOutClosedStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.PairStep
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_exists_ample_pow_sections_cutting_out_closed : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] (p : X ⟶ Sp ℂ), IsProjOver p → ∀ (N : LB X) (Z : Closeds X), IsAmpleLB N → ∀ᶠ l in atTop, ∃ (r : ℕ) (κ : Fin r → (lbPow N l).Sec), (∀ i, GlobalTheory.secPull (κ i) (redι Z) = 0) ∧ (∀ i, ∀ y ∈ Z, y ∉ nonzeroLocus (κ i)) ∧ ∀ y, y ∉ Z → ∃ i, y ∈ nonzeroLocus (κ i) := by
  first | exact @GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out | exact GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out | (intros; apply GlobalTheory.CutOutSections.eventually_exists_secs_cutting_out <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourRescaleApproximatedUnits
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourRescaleApproximatedUnits
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Poinc.VPre

theorem four_rescale : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.Four N₁ → ∀ v : ∀ y, (Φ.V y)ˣ, (∀ e : ℕ, ∃ a : A, ∀ y, Φ.ev y a - ((v y)⁻¹ : (Φ.V y)ˣ) ∈ (maximalIdeal A ^ e).map (Φ.ev y)) → (Φ.rescale v).Four N₁ := by
  intro O _ bar q s W A _ _ Φ N₁ hF w hw (y₀ : Φ.Y) N₀
  obtain ⟨N, hN0, hN1, k, hk0, hku, hmain⟩ := hF y₀ N₀
  refine ⟨N, hN0, hN1, k, hk0, hku, ?_⟩
  intro l a c e
  obtain ⟨f, hf⟩ := hmain l a c e
  obtain ⟨b, hb⟩ := hw (e + 1)

  have hmax : ∀ (y : Φ.Y) (x : A), x ∈ maximalIdeal A → Φ.ev y x ∈ maximalIdeal (Φ.V y) := by
    intro y x hx
    haveI := Φ.ev_loc y
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hu
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp hx) (isUnit_of_map_unit (Φ.ev y) x hu)
  have hle : ∀ y : Φ.Y, (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ maximalIdeal (Φ.V y) := by
    intro y
    rw [Ideal.map_le_iff_le_comap]
    exact le_trans (Ideal.pow_le_self (Nat.succ_ne_zero e)) (fun x hx => hmax y x hx)
  have hbu : IsUnit b := by
    by_contra hn
    have hbm : b ∈ maximalIdeal A := (IsLocalRing.mem_maximalIdeal _).mpr hn
    have h1 : Φ.ev y₀ b ∈ maximalIdeal (Φ.V y₀) := hmax y₀ b hbm
    have h2 := hle y₀ (hb y₀)
    have h3 : (((w y₀)⁻¹ : (Φ.V y₀)ˣ) : Φ.V y₀) ∈ maximalIdeal (Φ.V y₀) := by
      have := Ideal.sub_mem _ h1 h2
      simpa using this
    exact (IsLocalRing.mem_maximalIdeal _ |>.mp h3) (Units.isUnit _)
  refine ⟨f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l, fun (y : Φ.Y) j => ?_⟩
  obtain ⟨S, hS1, hS2, hS3⟩ := hf y j
  refine ⟨S, hS1, hS2, ?_⟩
  set J := maximalIdeal (Φ.V y) ^ j ⊔ (maximalIdeal A ^ e).map (Φ.ev y) with hJ
  have hIe : (maximalIdeal A ^ (e + 1)).map (Φ.ev y) ≤ J :=
    le_trans (Ideal.map_mono (Ideal.pow_le_pow_right (Nat.le_succ e))) le_sup_right
  set z : Φ.V y := Φ.ev y ((hbu.unit⁻¹ : Aˣ) : A) with hz
  set ww : Φ.V y := ((w y : (Φ.V y)ˣ) : Φ.V y) with hww
  have hzb : z * Φ.ev y b = 1 := by
    rw [hz, ← map_mul]
    simp
  have hzw : z - ww ∈ J := by
    apply hIe
    have h := (hb y)
    have hx : z - ww = -(z * ww * (Φ.ev y b - (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y))) := by
      have : ww * (((w y)⁻¹ : (Φ.V y)ˣ) : Φ.V y) = 1 := by simp [hww]
      linear_combination ww * hzb - z * this
    rw [hx]
    exact neg_mem (Ideal.mul_mem_left _ _ h)
  have hprod : ∀ mu : Fin l × Fin s → Φ.X y,
      (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x)))
        = (∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww ^ l := by
    intro mu
    rw [show (fun i => Φ.u y (fun x => mu (i, x)) (c i) * ww * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x)))
        = fun i => (Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) * ww from
        funext fun i => by ring]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  show Φ.ev y (f * ((hbu.unit⁻¹ : Aˣ) : A) ^ l) - ∑ mu ∈ S, (∏ i, (Φ.u y (fun x => mu (i, x)) (c i) * ww) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))) ∈ J
  simp_rw [hprod]
  rw [← Finset.sum_mul, map_mul, map_pow, ← hz]
  set P := ∑ mu ∈ S, ∏ i, Φ.u y (fun x => mu (i, x)) (c i) * mono W (Φ.t y) (Φ.δ y) (fun x => mu (i, x))
  have hd : z ^ l - ww ^ l ∈ J := by
    obtain ⟨r, hr⟩ := sub_dvd_pow_sub_pow z ww l
    rw [hr]
    exact Ideal.mul_mem_right _ _ hzw
  have : Φ.ev y f * z ^ l - P * ww ^ l = z ^ l * (Φ.ev y f - P) + P * (z ^ l - ww ^ l) := by ring
  rw [this]
  exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hS3) (Ideal.mul_mem_left _ _ hd)

end GlobalTheory.Poinc.VPre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FourierTermSystemFourRescaleApproximatedUnitsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourierTermSystem_four_rescale_approximated_units : ∀ (O : Type) [CommRing O] (bar : O → O) (q s : ℕ) (W : Matrix (Fin s) (Fin s) ℤ) (A : Type) [CommRing A] [IsLocalRing A] (Φ : VPre bar q W A) (N₁ : ℕ), Φ.Four N₁ → ∀ v : ∀ y, (Φ.V y)ˣ, (∀ e : ℕ, ∃ a : A, ∀ y, Φ.ev y a - ((v y)⁻¹ : (Φ.V y)ˣ) ∈ (maximalIdeal A ^ e).map (Φ.ev y)) → (Φ.rescale v).Four N₁ := by
  first | exact @GlobalTheory.Poinc.VPre.four_rescale | exact GlobalTheory.Poinc.VPre.four_rescale | (intros; apply GlobalTheory.Poinc.VPre.four_rescale <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemOneIffIsIntegral
set_option autoImplicit false

noncomputable section

open NumberField GlobalTheory.CMVal

namespace GlobalTheory.RoadE

variable {E : Type} [Field E] [NumberField E]

theorem exists_nat_mul_isIntegral (a : E) : ∃ k : ℕ, 0 < k ∧ IsIntegral ℤ ((k : E) * a) := by
  have h : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨k, hk, hi⟩ := h.exists_integral_multiple
  refine ⟨k.natAbs, Int.natAbs_pos.2 hk, ?_⟩
  rw [zsmul_eq_mul] at hi
  rw [Nat.cast_natAbs]
  rcases abs_choice k with h | h <;> rw [h]
  · exact hi
  · push_cast; rw [neg_mul]; exact hi.neg

theorem mem_one_iff_isIntegral (a : maximalRealSubfield E) :
    a ∈ (1 : Submodule (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)) ↔ IsIntegral ℤ (a : E) := by
  rw [Submodule.mem_one]
  have e : IsIntegral ℤ (a : E) ↔ IsIntegral ℤ a :=
    isIntegral_algebraMap_iff (R := ℤ) (A := maximalRealSubfield E) (B := E) (x := a) 
  rw [e]
  exact ⟨fun ⟨b, hb⟩ => hb ▸ b.isIntegral_coe, fun h => ⟨⟨a, h⟩, rfl⟩⟩

def passMul (t : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (n : ℕ) : GlobalTheory.HilbFam.Lat (maximalRealSubfield E) where
  carrier := {x | ∃ y' ∈ lattice c y, (n : E) * y' = ptE t x}
  add_mem' := fun {x x'} ⟨u, hu, e⟩ ⟨u', hu', e'⟩ => ⟨u + u', (latticeSub c y).add_mem hu hu', by
    rw [mul_add, e, e']; simp only [ptE, Pi.add_apply, Subfield.coe_add]; ring⟩
  zero_mem' := ⟨0, (latticeSub c y).zero_mem, by simp [ptE]⟩
  smul_mem' := fun a x ⟨u, hu, e⟩ => ⟨algebraMap (OF E) E a * u, mul_mem_lattice (algebraMap_mem_orderC c a) hu, by
    rw [ptE_smul, ← e]; ring⟩

theorem exists_coord_integral [IsCMField E] {θ : E} (hθ : θ ∉ maximalRealSubfield E) :
    ∃ k : ℕ, 0 < k ∧ ∀ (z : E) (a b : maximalRealSubfield E), IsIntegral ℤ z → (k : E) * z = (a : E) * θ + b →
      IsIntegral ℤ (a : E) ∧ IsIntegral ℤ (b : E) := by
  set σ := IsCMField.complexConj E with hσ
  have hδ : θ - σ θ ≠ 0 := fun h => hθ ((IsCMField.complexConj_eq_self_iff E θ).1 (sub_eq_zero.1 h).symm)
  obtain ⟨k₁, h₁, i₁⟩ := exists_nat_mul_isIntegral (θ - σ θ)⁻¹
  obtain ⟨k₂, h₂, i₂⟩ := exists_nat_mul_isIntegral θ
  refine ⟨k₁ * k₂, Nat.mul_pos h₁ h₂, fun z a b hz e => ?_⟩
  have hσz : IsIntegral ℤ (σ z) := hz.map (σ : E →+* E).toIntAlgHom
  have ea : σ (a : E) = a := σ.commutes a
  have eb : σ (b : E) = b := σ.commutes b
  have e' : ((k₁ * k₂ : ℕ) : E) * σ z = (a : E) * σ θ + b := by
    have := congrArg σ e
    rwa [map_mul, map_add, map_mul, map_natCast, ea, eb] at this
  push_cast at e e'
  have hn : ∀ m : ℕ, IsIntegral ℤ (m : E) := fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  have ha : (a : E) = k₂ * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z)) := by
    field_simp
    linear_combination e' - e
  refine ⟨ha ▸ (hn k₂).mul (i₁.mul (hz.sub hσz)), ?_⟩
  have hb : (b : E) = k₁ * (k₂ * z) - (k₂ * θ) * ((k₁ * (θ - σ θ)⁻¹) * (z - σ z)) := by
    linear_combination -e - θ * ha
  exact hb ▸ ((hn k₁).mul ((hn k₂).mul hz)).sub (i₂.mul (i₁.mul (hz.sub hσz)))

theorem exists_level : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (θ : E) (c : Ideal (OF E)) (y : (Af E)ˣ) (N₀ : ℕ),
    c ≠ ⊥ → θ ∉ Set.range (fun x : maximalRealSubfield E => (x : E)) → 0 < N₀ →
    ∃ (n N : ℕ) (L : GlobalTheory.HilbFam.Lat (maximalRealSubfield E)), 0 < n ∧ 0 < N ∧ N₀ ∣ N ∧ GlobalTheory.HilbFam.HasLevel N L ∧
      ∀ x : Fin 2 → maximalRealSubfield E, x ∈ L ↔ ∃ y' ∈ lattice c y,
        (n : E) * y' = ((x 0 : maximalRealSubfield E) : E) * θ + ((x 1 : maximalRealSubfield E) : E) := by
  intro E _ _ _ θ c y N₀ hc hθ hN₀
  obtain ⟨M, hM, hlo, hhi⟩ := GlobalTheory.CMVal.LatBound.lattice_between E c hc y
  obtain ⟨k, hk, hco⟩ := exists_coord_integral (θ := θ) fun h => hθ ⟨⟨θ, h⟩, rfl⟩
  obtain ⟨D, hD, iD⟩ := exists_nat_mul_isIntegral θ
  have hn : ∀ m : ℕ, IsIntegral ℤ (m : E) := fun m => by exact_mod_cast (isIntegral_algebraMap (R := ℤ) (A := E) (x := (m : ℤ)))
  refine ⟨k * M, N₀ * (k * M * M * D), passMul θ c y (k * M), by positivity, by positivity, dvd_mul_right _ _,
    ⟨fun x hx => ?_, fun x hx => ?_⟩, fun x => Iff.rfl⟩
  · have h0 := (mem_one_iff_isIntegral _).1 (hx 0 trivial)
    have h1 := (mem_one_iff_isIntegral _).1 (hx 1 trivial)
    have hi : IsIntegral ℤ ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E))) :=
      (hn N₀).mul ((h0.mul iD).add ((hn D).mul h1))
    refine ⟨_, hlo ⟨_, hi⟩, ?_⟩
    rw [ptE_smul, map_natCast]
    show ((k * M : ℕ) : E) * ((M : E) * ((N₀ : E) * ((x 0 : E) * (D * θ) + D * (x 1 : E)))) = _
    simp only [ptE]
    push_cast
    ring
  · obtain ⟨u, hu, e⟩ := hx
    obtain ⟨h0, h1⟩ := hco (M * u) (x 0) (x 1) (hhi u hu) (by rw [← mul_assoc, ← Nat.cast_mul]; exact e)
    intro i _
    fin_cases i
    · exact (mem_one_iff_isIntegral _).2 h0
    · exact (mem_one_iff_isIntegral _).2 h1

end GlobalTheory.RoadE
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentIndepOfIsComplAt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.Poinc GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open scoped TensorProduct

namespace GlobalTheory.TChart

theorem cotangent_indep_of_isComplAt : ∀ (W : Type) [CommRing W] [IsLocalRing W] [IsNoetherianRing W] (I : Type) [Fintype I] (R : Type) [CommRing R] [IsLocalRing R] (ψ : MvPolynomial I W →+* R), IsComplAt ψ → IsLocalHom (ψ.comp MvPolynomial.C) → ∀ (m : ℕ) (ι₀ : Fin m ↪ I), (∀ k, ψ (MvPolynomial.X (ι₀ k)) ∈ maximalIdeal R) → ∀ c : Fin m → R, ∑ k, c k * ψ (MvPolynomial.X (ι₀ k)) ∈ maximalIdeal R ^ 2 ⊔ (maximalIdeal W).map (ψ.comp MvPolynomial.C) → ∀ k, c k ∈ maximalIdeal R := by
  intro W _ _ _ I _ R _ _ ψ hψ hloc m ι₀ hX c hc k
  classical
  letI : Algebra (MvPolynomial I W) R := ψ.toAlgebra
  haveI hflat : Module.Flat (MvPolynomial I W) R := hψ.2.2.1
  haveI := hloc
  have hsmul : ∀ (a : MvPolynomial I W) (r : R), a • r = ψ a * r := fun a r => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
  let P : Ideal (MvPolynomial I W) := (maximalIdeal R).comap ψ
  have hPm : P.map ψ = maximalIdeal R := hψ.2.2.2.1
  let δ : MvPolynomial I W → ResidueField R := fun f => residue R (ψ (MvPolynomial.pderiv (ι₀ k) f))
  have hπP : ∀ p ∈ P, residue R (ψ p) = 0 := fun p hp => (residue_eq_zero_iff _).2 hp
  have hδmul : ∀ a b, δ (a * b) = residue R (ψ a) * δ b + residue R (ψ b) * δ a := by
    intro a b; simp only [δ, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul]
  have hδadd : ∀ a b, δ (a + b) = δ a + δ b := by intro a b; simp [δ]
  let K : Ideal (MvPolynomial I W) :=
    { carrier := {x | x ∈ P ∧ δ x = 0}
      add_mem' := fun {a b} ha hb => ⟨P.add_mem ha.1 hb.1, by rw [hδadd, ha.2, hb.2, add_zero]⟩
      zero_mem' := ⟨P.zero_mem, by simp [δ]⟩
      smul_mem' := fun a x hx => ⟨P.mul_mem_left a hx.1, by
        rw [smul_eq_mul, hδmul, hx.2, hπP x hx.1, mul_zero, zero_mul, add_zero]⟩ }
  have hCW : (maximalIdeal W).map (MvPolynomial.C : W →+* MvPolynomial I W) ≤ K := by
    refine Ideal.map_le_iff_le_comap.2 fun w hw => ⟨?_, by simp [δ]⟩
    show ψ (MvPolynomial.C w) ∈ maximalIdeal R
    exact map_nonunit (ψ.comp MvPolynomial.C) w hw
  have hP2 : P ^ 2 ≤ K := by
    rw [pow_two]
    refine Ideal.mul_le.2 fun p hp q hq => ⟨P.mul_mem_left p hq, ?_⟩
    show δ (p * q) = 0
    rw [hδmul, hπP p hp, hπP q hq]; simp
  have hJ : maximalIdeal R ^ 2 ⊔ (maximalIdeal W).map (ψ.comp MvPolynomial.C) ≤ K.map ψ := by
    rw [← hPm, ← Ideal.map_pow, ← Ideal.map_map, ← Ideal.map_sup]
    exact Ideal.map_mono (sup_le hP2 hCW)
  let muT : TensorProduct (MvPolynomial I W) R P →ₗ[MvPolynomial I W] R :=
    (TensorProduct.rid (MvPolynomial I W) R).toLinearMap ∘ₗ (Submodule.subtype P).lTensor R
  have hmu : Function.Injective muT :=
    (TensorProduct.rid (MvPolynomial I W) R).injective.comp
      (Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective)
  have hmut : ∀ (r : R) (p : P), muT (r ⊗ₜ p) = ψ p * r := fun r p => by
    simp [muT, hsmul]
  let f : R →+ P →+ ResidueField R := AddMonoidHom.mk'
    (fun r => AddMonoidHom.mk' (fun p : P => residue R r * δ p) (by intro a b; simp [hδadd, mul_add]))
    (by intro a b; ext p; simp [add_mul])
  have hf : ∀ (a : MvPolynomial I W) (r : R) (p : P), f (a • r) p = f r (a • p) := by
    intro a r p
    simp only [f, AddMonoidHom.mk'_apply, hsmul, Submodule.coe_smul, smul_eq_mul, hδmul, hπP p p.2, map_mul]
    ring
  let L : TensorProduct (MvPolynomial I W) R P →+ ResidueField R := TensorProduct.liftAddHom f hf
  have hLt : ∀ (r : R) (p : P), L (r ⊗ₜ p) = residue R r * δ p := fun r p => by
    simp [L, f]
  have hspan : ∀ y ∈ K.map ψ, ∀ r : R, ∃ t, muT t = r * y ∧ L t = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨j, hj, rfl⟩ := hx
      intro r
      exact ⟨r ⊗ₜ ⟨j, hj.1⟩, by rw [hmut]; ring, by rw [hLt]; simp [hj.2]⟩
    | zero => intro r; exact ⟨0, by simp, by simp⟩
    | add x y _ _ hx hy =>
      intro r
      obtain ⟨t₁, h₁, h₁'⟩ := hx r
      obtain ⟨t₂, h₂, h₂'⟩ := hy r
      exact ⟨t₁ + t₂, by rw [map_add (f := _), h₁, h₂]; ring, by rw [map_add (f := _), h₁', h₂', add_zero]⟩
    | smul a x _ hx =>
      intro r
      obtain ⟨t, h₁, h₂⟩ := hx (r * a)
      exact ⟨t, by rw [h₁, smul_eq_mul]; ring, h₂⟩
  have hX' : ∀ j, MvPolynomial.X (ι₀ j) ∈ P := hX
  let t₀ : TensorProduct (MvPolynomial I W) R P := ∑ j, c j ⊗ₜ ⟨MvPolynomial.X (ι₀ j), hX' j⟩
  have hmu0 : muT t₀ = ∑ j, c j * ψ (MvPolynomial.X (ι₀ j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [t₀, map_sum, hmut]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hL₀ : L t₀ = residue R (c k) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [t₀, map_sum, hLt, δ, MvPolynomial.pderiv_X, Pi.single_apply, ι₀.injective.eq_iff]
    simp
  obtain ⟨t, ht₁, ht₂⟩ := hspan _ (hJ hc) 1
  have : t = t₀ := hmu (by rw [ht₁, _root_.one_mul, hmu0])
  rw [this, hL₀] at ht₂
  exact (residue_eq_zero_iff _).1 ht₂

end GlobalTheory.TChart
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationsCommonGenericFibreOfCommonThird
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationsCommonGenericFibreOfCommonThird
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.SameComb

theorem sp_endo_eq_id {o K : Type} [CommRing o] [Field K] [Algebra o K] (R : Subalgebra o K)
    (frac : ∀ x : K, ∃ a ∈ R, ∃ b ∈ R, x = a / b) (g : Sp K ⟶ Sp K)
    (h : g ≫ spMap R.val.toRingHom = spMap R.val.toRingHom) : g = 𝟙 _ := by
  rw [← Spec.map_preimage g] at h ⊢
  set ψ := Spec.preimage g
  have h' : CommRingCat.ofHom R.val.toRingHom ≫ ψ = CommRingCat.ofHom R.val.toRingHom := by
    apply Spec.map_injective
    rw [Spec.map_comp]; exact h
  have hψ : ψ = 𝟙 _ := by
    ext x
    obtain ⟨a, ha, b, hb, rfl⟩ := frac x
    have ea := congrArg (fun f => f.hom ⟨a, ha⟩) h'
    have eb := congrArg (fun f => f.hom ⟨b, hb⟩) h'
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply] at ea eb
    change ψ.hom (a / b) = a / b
    rw [map_div₀]
    exact congrArg₂ (· / ·) ea eb
  rw [hψ, Spec.map_id]

theorem lbIso_pull_along {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} (h : LBIso M (L.pull φ)) (r : Z ⟶ Y)
    {ψ : Z ⟶ X} (e : ψ = r ≫ φ) : LBIso (M.pull r) (L.pull ψ) :=
  h.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull M r r rfl) (chartPullSame L (fun _ => ψ) (fun _ => φ) _ r fun _ => e)

theorem sec_of_pt {o K : Type} [CommRing o] [Field K] [Algebra o K] (R : Subalgebra o K)
    (frac : ∀ x : K, ∃ a ∈ R, ∃ b ∈ R, x = a / b) {Q : PolAV (Sp K)} {P : PolAV (Sp R)} {a : Q.A.left ⟶ P.A.left}
    (ha : IsGrpPullback Q.A P.A (spMap R.val.toRingHom) a) (t : baseOver (Sp R) ⟶ P.A) (w : Sp K ⟶ Q.A.left)
    (hw : w ≫ a = spMap R.val.toRingHom ≫ t.left) : w ≫ Q.A.hom = 𝟙 _ := by
  apply sp_endo_eq_id R frac
  have e := congrArg (· ≫ P.A.hom) hw
  simp only [Category.assoc, ha.1.w, Over.w t] at e
  simpa using e

theorem combine : ∀ (o Ω o₁ o₂ Ω' : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o₁] [CommRing o₂] [Field Ω'] [Algebra o₁ Ω'] [Algebra o₂ Ω'] (S : ThetaSys o Ω) (S₁ : ThetaSys o₁ Ω') (S₂ : ThetaSys o₂ Ω') (ρ : S.Real) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (lab₁ : S.Gam → S₁.Gam) (lab₂ : S.Gam → S₂.Gam) (φ : Ω →+* Ω'), Same ρ ε ρ₁ ε₁ lab₁ φ → Same ρ ε ρ₂ ε₂ lab₂ φ → SameAt ρ₁.P ρ₂.P S₁.R.val.toRingHom S₂.R.val.toRingHom ε₁ ε₂ (fun x => ρ₁.pt (lab₁ x)) (fun x => ρ₂.pt (lab₂ x)) := by
  intro o Ω o₁ o₂ Ω' _ _ _ _ _ _ _ _ S S₁ S₂ ρ ρ₁ ρ₂ ε ε₁ ε₂ lab₁ lab₂ φ h₁ h₂
  obtain ⟨P₀, a, a₁, ε₀, ha, ha₁, hLa, hLa₁, hε, hw⟩ := h₁
  obtain ⟨P₀', b, b₂, ε₀', hb, hb₂, hLb, hLb₂, hε', hw'⟩ := h₂
  obtain ⟨θ, hθm, hθ⟩ := grpPullback_iso ha hb
  haveI := hθm

  have ext : ∀ {T : Scheme.{0}} (u v : T ⟶ P₀'.A.left), u ≫ b = v ≫ b → u ≫ P₀'.A.hom = v ≫ P₀'.A.hom → u = v :=
    fun u v e₁ e₂ => hb.1.hom_ext e₁ e₂
  refine ⟨P₀, a₁, θ.hom.left ≫ b₂, ha₁, ((isGrpPullback_of_iso θ).comp hb₂).congr (Category.id_comp _) rfl, hLa₁, ?_,
    fun E => ⟨ε₀ E, (hε E).2, ?_⟩, fun x => ?_⟩
  · refine LBIso.trans P₀.isLB (pull_isLB ρ.P.isLB _) (pull_isLB ρ₂.P.isLB _) hLa ?_
    refine LBIso.trans (pull_isLB ρ.P.isLB _) (pull_isLB P₀'.isLB θ.hom.left) (pull_isLB ρ₂.P.isLB _)
      (lbIso_pull_along hLb θ.hom.left hθ.symm).symm (lbIso_pull_along hLb₂ θ.hom.left rfl)
  · have key : (ε₀ E).left ≫ θ.hom.left = θ.hom.left ≫ (ε₀' E).left := by
      apply ext
      · rw [Category.assoc, hθ, (hε E).1, Category.assoc, (hε' E).1, ← Category.assoc, hθ]
      · simp only [Category.assoc, Over.w]
    rw [← Category.assoc, key, Category.assoc, (hε' E).2, Category.assoc]
  · obtain ⟨w, hwa, hwa₁⟩ := hw x
    obtain ⟨w', hwb, hwb₂⟩ := hw' x
    refine ⟨w, hwa₁, ?_⟩
    have s₁ := sec_of_pt S₁.R S₁.frac ha₁ _ w hwa₁
    have s₂ := sec_of_pt S₂.R S₂.frac hb₂ _ w' hwb₂
    have hww : w ≫ θ.hom.left = w' := by
      apply ext
      · rw [Category.assoc, hθ, hwa, hwb]
      · rw [Category.assoc, Over.w, s₁, s₂]
    rw [← Category.assoc, hww, hwb₂]

end GlobalTheory.Poinc.SameComb
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisationsCommonGenericFibreOfCommonThirdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisations_common_generic_fibre_of_common_third : ∀ (o Ω o₁ o₂ Ω' : Type) [CommRing o] [Field Ω] [Algebra o Ω] [CommRing o₁] [CommRing o₂] [Field Ω'] [Algebra o₁ Ω'] [Algebra o₂ Ω'] (S : ThetaSys o Ω) (S₁ : ThetaSys o₁ Ω') (S₂ : ThetaSys o₂ Ω') (ρ : S.Real) (ρ₁ : S₁.Real) (ρ₂ : S₂.Real) (ε : Matrix (Fin 8) (Fin 8) ℤ → (ρ.P.A ⟶ ρ.P.A)) (ε₁ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₁.P.A ⟶ ρ₁.P.A)) (ε₂ : Matrix (Fin 8) (Fin 8) ℤ → (ρ₂.P.A ⟶ ρ₂.P.A)) (lab₁ : S.Gam → S₁.Gam) (lab₂ : S.Gam → S₂.Gam) (φ : Ω →+* Ω'), Same ρ ε ρ₁ ε₁ lab₁ φ → Same ρ ε ρ₂ ε₂ lab₂ φ → SameAt ρ₁.P ρ₂.P S₁.R.val.toRingHom S₂.R.val.toRingHom ε₁ ε₂ (fun x => ρ₁.pt (lab₁ x)) (fun x => ρ₂.pt (lab₂ x)) := by
  first | exact @GlobalTheory.Poinc.SameComb.combine | exact GlobalTheory.Poinc.SameComb.combine | (intros; apply GlobalTheory.Poinc.SameComb.combine <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimAddEqOfTrBasis
set_option autoImplicit false

noncomputable section

open Algebra

namespace GlobalTheory.LocModelDim

theorem isAlgebraic_of_forall_mul {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
    (h : ∀ s : S, ∃ a b : R, algebraMap R S b ≠ 0 ∧ s * algebraMap R S b = algebraMap R S a) :
    Algebra.IsAlgebraic R S := by
  refine ⟨fun s => ?_⟩
  obtain ⟨a, b, hb, e⟩ := h s
  refine ⟨Polynomial.C b * Polynomial.X - Polynomial.C a, fun h0 => hb ?_, ?_⟩
  · have h1 := congrArg (fun p => _root_.AddMonoidAlgebra.coeff (M := ℕ) p 1) h0
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X, Polynomial.coeff_C_succ,
      sub_zero, Polynomial.coeff_zero, if_true] at h1
    rw [h1, map_zero]
  · rw [map_sub, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, Polynomial.aeval_C, mul_comm, e,
      sub_self]

set_option synthInstance.maxHeartbeats 200000 in
theorem ringKrullDim_add_trdeg {k R Ω : Type} [Field k] [CommRing R] [IsDomain R]
    [IsLocalRing R] [Algebra k R] [Algebra.EssFiniteType k R] [Field Ω] [Algebra R Ω]
    [Algebra k Ω] [IsScalarTower k R Ω] (hχ : Function.Surjective (algebraMap R Ω)) {n m : ℕ}
    (hn : trdeg k Ω = n) (hm : trdeg k R = m) : ringKrullDim R + n = m := by
  set A := EssFiniteType.subalgebra k R
  set ι := algebraMap A R
  set f : A →+* Ω := (algebraMap R Ω).comp ι with hf
  set P := RingHom.ker f with hP
  haveI : P.IsPrime := RingHom.ker_isPrime f
  have hmax : RingHom.ker (algebraMap R Ω) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective _ hχ)
  have hunit : ∀ r : R, IsUnit r ↔ algebraMap R Ω r ≠ 0 := by
    intro r
    have := congrArg (r ∈ ·) hmax
    simp only [RingHom.mem_ker, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at this
    rw [Ne, this, not_not]
  have hM : EssFiniteType.submonoid k R = P.primeCompl := by
    ext x
    simp only [EssFiniteType.submonoid, Submonoid.mem_comap, IsUnit.mem_submonoid_iff,
      Ideal.mem_primeCompl_iff, hP, RingHom.mem_ker, hf, RingHom.comp_apply, hunit]
    rfl
  haveI : IsLocalization.AtPrime R P := by
    unfold IsLocalization.AtPrime
    rw [← hM]
    infer_instance

  have hdimR : ringKrullDim R = P.height := IsLocalization.AtPrime.ringKrullDim_eq_height P R
  have hform := GlobalTheory.height_add_ringKrullDim_quotient_of_finiteType k P
  obtain ⟨s, hs1, hs2⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A)
  haveI : Algebra.FiniteType k (A ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k P) Ideal.Quotient.mk_surjective
  obtain ⟨s', hs1', hs2'⟩ := ReciprocityTheory.CA.exists_dim_trdeg_field (K := k) (A := A ⧸ P)

  haveI : FaithfulSMul A R := (faithfulSMul_iff_algebraMap_injective _ _).2 Subtype.val_injective
  haveI : Algebra.IsAlgebraic A R := IsLocalization.isAlgebraic R (EssFiniteType.submonoid k R)
  have hAR := trdeg_add_eq k A (A := R)
  rw [trdeg_eq_zero (R := A) (A := R), add_zero, hs2, hm] at hAR

  letI : Algebra (A ⧸ P) Ω := (RingHom.kerLift f).toAlgebra
  haveI : IsScalarTower k (A ⧸ P) Ω := IsScalarTower.of_algebraMap_eq fun x => by
    change algebraMap k Ω x = f (algebraMap k A x)
    rw [hf, RingHom.comp_apply, IsScalarTower.algebraMap_apply k R Ω]
    rfl
  haveI : FaithfulSMul (A ⧸ P) Ω :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective f)
  haveI : Algebra.IsAlgebraic (A ⧸ P) Ω := by
    apply isAlgebraic_of_forall_mul
    intro ω
    obtain ⟨r, rfl⟩ := hχ ω
    obtain ⟨⟨a, t⟩, e⟩ := IsLocalization.surj (EssFiniteType.submonoid k R) r
    refine ⟨Ideal.Quotient.mk P a, Ideal.Quotient.mk P t, ?_, ?_⟩
    · change f t ≠ 0
      exact (hunit _).1 t.2
    · change algebraMap R Ω r * f t = f a
      rw [hf, RingHom.comp_apply, RingHom.comp_apply, ← map_mul]
      exact congrArg (algebraMap R Ω) e
  haveI hdom : IsDomain (A ⧸ P) := Ideal.Quotient.isDomain P
  haveI : Nontrivial (A ⧸ P) := hdom.toNontrivial
  haveI : FaithfulSMul k (A ⧸ P) :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (algebraMap k (A ⧸ P)).injective
  have hPΩ := trdeg_add_eq k (A ⧸ P) (A := Ω)
  rw [trdeg_eq_zero (R := A ⧸ P) (A := Ω), add_zero, hs2', hn] at hPΩ
  have hss : s' = n := by exact_mod_cast hPΩ
  have hsm : s = m := by exact_mod_cast hAR
  rw [hdimR, ← hss, ← hsm, ← hs1', ← hs1]
  exact hform

end GlobalTheory.LocModelDim

open CategoryTheory AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.Discrepancy GlobalTheory.FieldPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAw
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAw
open GlobalTheory.LogDerProj

set_option autoImplicit false

namespace GlobalTheory.LogDerProj

theorem exists_pow_smul_eq_res : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R)
    [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R)
    (n : (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R),
    ∃ x : logSub φ J × Submonoid.powers f, x.2 • n = res (S := S) f φ J x.1 := by
  intro k R S _ _ _ _ f _ φ hφ J n
  letI : Algebra k R := φ.toAlgebra
  haveI : Algebra.FiniteType k R := hφ
  haveI : Algebra.FinitePresentation k R := Algebra.FinitePresentation.of_finiteType.mp inferInstance
  haveI : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  letI : Algebra k S := ((algebraMap R S).comp φ).toAlgebra
  haveI : IsScalarTower k R S := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hn0 : ∀ c : k, n.1 (algebraMap R S (φ c)) = 0 := fun c => n.2.1 c
  have hnJ : ∀ y ∈ J.map (algebraMap R S), n.1 y ∈ J.map (algebraMap R S) := n.2.2
  let gl : R →ₗ[k] S :=
    { toFun := fun r => n.1 (algebraMap R S r)
      map_add' := fun a b => by simp
      map_smul' := fun c r => by
        rw [RingHom.id_apply, Algebra.smul_def, map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        show _ = algebraMap R S (φ c) * _
        rw [show algebraMap k R c = φ c from rfl, hn0, mul_zero, add_zero] }
  let g : Derivation k R S := Derivation.mk' gl fun a b => by
    show n.1 (algebraMap R S (a * b)) = a • n.1 (algebraMap R S b) + b • n.1 (algebraMap R S a)
    rw [map_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul, Algebra.smul_def, Algebra.smul_def]
  have hg : ∀ r, g r = n.1 (algebraMap R S r) := fun r => rfl
  obtain ⟨h, s, hs⟩ := Module.FinitePresentation.exists_lift_of_isLocalizedModule (Submonoid.powers f)
    (Algebra.linearMap R S) g.liftKaehlerDifferential
  let D' : Derivation k R R := h.compDer (KaehlerDifferential.D k R)
  have hD' : ∀ r, algebraMap R S (D' r) = algebraMap R S s * n.1 (algebraMap R S r) := by
    intro r
    have := congrArg (fun L : Ω[R⁄k] →ₗ[R] S => L (KaehlerDifferential.D k R r)) hs
    simp only [LinearMap.coe_comp, Function.comp_apply, Algebra.linearMap_apply, LinearMap.smul_apply,
      Derivation.liftKaehlerDifferential_comp_D] at this
    rw [Submonoid.smul_def, Algebra.smul_def] at this
    rw [← hg]
    exact this
  have hJfg : J.FG := IsNoetherian.noetherian J
  obtain ⟨T, hT⟩ := hJfg
  have hex : ∀ t : T, ∃ m : Submonoid.powers f, (m : R) * D' t ∈ J := by
    intro t
    have ht : (t : R) ∈ J := hT ▸ Ideal.subset_span t.2
    have h1 : algebraMap R S (D' t) ∈ J.map (algebraMap R S) := by
      rw [hD']
      exact Ideal.mul_mem_left _ _ (hnJ _ (Ideal.mem_map_of_mem _ ht))
    obtain ⟨m, hm, hmJ⟩ := (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers f) S J _).1 h1
    exact ⟨⟨m, hm⟩, hmJ⟩
  choose c hc using hex
  let m : Submonoid.powers f := ∏ t, c t
  have hmT : ∀ t ∈ T, (m : R) * D' t ∈ J := by
    intro t ht
    have hdvd : (c ⟨t, ht⟩ : R) ∣ (m : R) := by
      show (c ⟨t, ht⟩ : R) ∣ ((∏ t, c t : Submonoid.powers f) : R)
      change (c ⟨t, ht⟩ : R) ∣ (Submonoid.subtype (Submonoid.powers f)) (∏ t, c t)
      rw [map_prod]
      exact Finset.dvd_prod_of_mem _ (Finset.mem_univ _)
    obtain ⟨q, hq⟩ := hdvd
    rw [hq, mul_comm _ q, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hc ⟨t, ht⟩)
  let D : Derivation ℤ R R := (m : R) • D'.restrictScalars ℤ
  have hDapp : ∀ r, D r = (m : R) * D' r := fun r => rfl
  have hDmem : D ∈ logSub φ J := by
    refine ⟨fun a => ?_, fun y hy => ?_⟩
    · rw [hDapp, show φ a = algebraMap k R a from rfl, D'.map_algebraMap, mul_zero]
    · rw [← hT] at hy
      induction hy using Submodule.span_induction with
      | mem x hx => rw [hDapp]; exact hmT x hx
      | zero => rw [map_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
      | smul a x hx' hx =>
        rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
        have hxJ : x ∈ J := by rw [← hT]; exact hx'
        exact add_mem (Ideal.mul_mem_left _ _ hx) (Ideal.mul_mem_right _ _ hxJ)
  refine ⟨(⟨D, hDmem⟩, m * s), ?_⟩
  apply Subtype.ext
  refine der_ext f _ _ fun r => ?_
  rw [res_apply, hDapp]
  show ((m * s : Submonoid.powers f) : R) • n.1 (algebraMap R S r) = _
  rw [Algebra.smul_def, Submonoid.coe_mul, map_mul, map_mul, hD', mul_assoc]

end GlobalTheory.LogDerProj
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowSmulEqLogDerivationExtendLocalizationAwStatement
open GlobalTheory.LogDerProj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_smul_eq_logDerivation_extend_localizationAway : ∀ {k R S : Type} [Field k] [CommRing R] [CommRing S] [Algebra R S] (f : R) [IsLocalization.Away f S] (φ : k →+* R), φ.FiniteType → ∀ (J : Ideal R) (n : (logSub ((algebraMap R S).comp φ) (J.map (algebraMap R S))).restrictScalars R), ∃ x : logSub φ J × Submonoid.powers f, x.2 • n = res (S := S) f φ J x.1 := by
  first | exact @GlobalTheory.LogDerProj.exists_pow_smul_eq_res | exact GlobalTheory.LogDerProj.exists_pow_smul_eq_res | (intros; apply GlobalTheory.LogDerProj.exists_pow_smul_eq_res <;> assumption)
end
end
