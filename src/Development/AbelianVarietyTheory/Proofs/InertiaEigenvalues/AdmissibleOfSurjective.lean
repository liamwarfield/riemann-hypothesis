module

public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OcTensorCoeffActionMatrixMultiplicative
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LeKurOfNorm
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousOrbitOfEventually
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.H2EquivOfTorsionCharacter
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalPeriodRingsDataUnramifiedLaws
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisRadiusPosDefinite
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSumRootsOfUnity

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdmissibleOfSurjective
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open scoped LaurentSeries PowerSeries

noncomputable section

namespace GlobalTheory.AdmClosure

section Lat

variable {G : Type} [Group G] {LL O : Type} [Field LL] [CommRing O] [Algebra O LL]
variable {V : Type} [AddCommGroup V] [Module LL V] [Module O V] [IsScalarTower O LL V]
  {ρ : Representation LL G V}

def between [IsDomain O] [IsPrincipalIdealRing O] (L₁ L₂ : Lattice (O := O) ρ) (N : Submodule O V)
    (h₁ : N ≤ L₁.T) (h₂ : L₂.T ≤ N) (hs : ∀ g, ∀ x ∈ N, ρ g x ∈ N) : Lattice (O := O) ρ where
  T := N
  stable := hs
  fg := L₁.fg.of_le h₁
  free := by
    haveI := L₁.free
    haveI : Module.Finite O L₁.T := Module.Finite.iff_fg.mpr L₁.fg
    haveI : Module.Finite O (N.comap L₁.T.subtype) := inferInstance
    haveI : Module.Free O (N.comap L₁.T.subtype) := Module.free_of_finite_type_torsion_free'
    exact Module.Free.of_equiv (Submodule.comapSubtypeEquivOfLe h₁)
  span := by
    rw [eq_top_iff, ← L₂.span]
    exact Submodule.span_mono h₂

variable {V' : Type} [AddCommGroup V'] [Module LL V'] [Module O V'] [IsScalarTower O LL V']
  {ρ' : Representation LL G V'}

def prodEquiv (A : Submodule O V) (B : Submodule O V') : ↥(A.prod B) ≃ₗ[O] (↥A × ↥B) where
  toFun x := (⟨x.1.1, x.2.1⟩, ⟨x.1.2, x.2.2⟩)
  invFun y := ⟨(y.1.1, y.2.1), ⟨y.1.2, y.2.2⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def prodLattice (L : Lattice (O := O) ρ) (L' : Lattice (O := O) ρ') : Lattice (O := O) (ρ.prod ρ') where
  T := L.T.prod L'.T
  stable := fun g x hx => ⟨L.stable g _ hx.1, L'.stable g _ hx.2⟩
  fg := L.fg.prod L'.fg
  free := by
    haveI := L.free
    haveI := L'.free
    exact Module.Free.of_equiv (prodEquiv L.T L'.T).symm
  span := by
    have h := Submodule.span_prod_eq (R := LL) (s := (L.T : Set V)) (t := (L'.T : Set V')) L.T.zero_mem L'.T.zero_mem
    rw [L.span, L'.span, Submodule.prod_top] at h
    exact h

end Lat

section Bundled

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL O : Type} [Field Qp] [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] [IsTopologicalRing LL]

def prodLoc (T T' : LocLat G Qp LL O) : LocLat G Qp LL O where
  V := T.V × T'.V
  ρ := T.ρ.prod T'.ρ
  cont := fun x => (T.cont x.1).prodMk (T'.cont x.2)
  L := prodLattice T.L T'.L

end Bundled

def appendEquiv {R : Type} [CommRing R] {A : Type 1} (W : A → Type) [∀ x, AddCommGroup (W x)] [∀ x, Module R (W x)]
    {ι κ : Type} (F : ι → A) (F' : κ → A) :
    ((∀ j, W (F j)) × (∀ j, W (F' j))) ≃ₗ[R] (∀ j : ι ⊕ κ, W (Sum.elim F F' j)) where
  toFun x j := match j with
    | .inl a => x.1 a
    | .inr b => x.2 b
  invFun y := (fun a => y (.inl a), fun b => y (.inr b))
  map_add' _ _ := by funext j; cases j <;> rfl
  map_smul' _ _ := by funext j; cases j <;> rfl
  left_inv _ := rfl
  right_inv _ := by funext j; cases j <;> rfl

section Per

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {n : ℕ} {emb : ZMod n → (K₀ →ₐ[Qp] LL)}
    {Γ : GalData G Qp LL O} {t : ℕ} {Ut : ZMod n → Multiset ℤ}

theorem sumFull_prod [IsTopologicalRing LL] {μ μ' : ℕ} {T T' : LocLat G Qp LL O} (h : SumFull PD emb Γ t Ut μ T)
    (h' : SumFull PD emb Γ t Ut μ' T') : SumFull PD emb Γ t Ut (μ + μ') (prodLoc T T') := by
  obtain ⟨F, hF, e, he⟩ := h
  obtain ⟨F', hF', e', he'⟩ := h'
  let s : Fin (μ + μ') ≃ Fin μ ⊕ Fin μ' := finSumFinEquiv.symm
  have key : ∀ (g : G) (x : T.V × T'.V) (j : Fin μ ⊕ Fin μ'),
      appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F' (e (T.ρ g x.1), e' (T'.ρ g x.2)) j =
        (Sum.elim F F' j).ρ g (appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F' (e x.1, e' x.2) j) := by
    intro g x j
    cases j with
    | inl a => exact he g x.1 a
    | inr b => exact he' g x.2 b
  refine ⟨fun j => Sum.elim F F' (s j), fun j => ?_,
    ((e.prodCongr e').trans (appendEquiv (R := LL) (fun T : LocLat G Qp LL O => T.V) F F')).trans
      (LinearEquiv.piCongrLeft LL (fun j => (Sum.elim F F' j).V) s).symm, fun g x j => key g x (s j)⟩
  beta_reduce
  cases s j with
  | inl a => exact hF a
  | inr b => exact hF' b

variable {M M' : Type} [AddCommGroup M] [Module O M] [AddCommGroup M'] [Module O M']
    {π : Representation O G M} {π' : Representation O G M'}

theorem admissible_prod [IsTopologicalRing LL] (h : Admissible PD emb Γ t Ut π) (h' : Admissible PD emb Γ t Ut π') :
    Admissible PD emb Γ t Ut (π.prod π') := by
  obtain ⟨hf, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  obtain ⟨hf', μ', T', hT', L₂', p', hle', hp', hg', hk'⟩ := h'
  refine ⟨inferInstance, μ + μ', prodLoc T T', sumFull_prod hT hT', prodLattice L₂ L₂',
    (p.prodMap p') ∘ₗ (prodEquiv T.L.T T'.L.T).toLinearMap, Submodule.prod_mono hle hle',
    (hp.prodMap hp').comp (prodEquiv T.L.T T'.L.T).surjective, fun g x => ?_, fun x => ?_⟩
  · exact Prod.ext (hg g (prodEquiv T.L.T T'.L.T x).1) (hg' g (prodEquiv T.L.T T'.L.T x).2)
  · exact Prod.ext_iff.trans (and_congr (hk (prodEquiv T.L.T T'.L.T x).1) (hk' (prodEquiv T.L.T T'.L.T x).2))

variable [IsDomain O] [IsPrincipalIdealRing O]

theorem admissible_of_surjective (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (hs : Function.Surjective f) (h : Admissible PD emb Γ t Ut π) : Admissible PD emb Γ t Ut π' := by
  obtain ⟨hfin, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  let N : Submodule O T.V := (LinearMap.ker (f ∘ₗ p)).map T.L.T.subtype
  have hN : ∀ x : T.L.T, (x : T.V) ∈ N ↔ f (p x) = 0 := fun x =>
    ⟨fun ⟨_, hy, e⟩ => (Subtype.ext e : _ = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have h₁ : N ≤ T.L.T := Submodule.map_subtype_le _ _
  refine ⟨Finite.of_surjective f hs, μ, T, hT, between T.L L₂ N h₁ (fun x hx => ?_) (fun g x hx => ?_),
    f ∘ₗ p, h₁, hs.comp hp, fun g x => ?_, fun x => (hN x).symm⟩
  · refine (hN ⟨x, hle hx⟩).mpr ?_
    rw [(hk _).mpr hx, map_zero]
  · refine (hN (latRep T.L g ⟨x, h₁ hx⟩)).mpr ?_
    rw [hg, hf, (hN ⟨x, h₁ hx⟩).mp hx, map_zero]
  · simp only [LinearMap.comp_apply, hg, hf]

theorem admissible_of_injective (f : M →ₗ[O] M') (hf : ∀ σ x, f (π σ x) = π' σ (f x))
    (hi : Function.Injective f) (h : Admissible PD emb Γ t Ut π') : Admissible PD emb Γ t Ut π := by
  obtain ⟨hfin, μ, T, hT, L₂, p, hle, hp, hg, hk⟩ := h
  let N : Submodule O T.V := ((LinearMap.range f).comap p).map T.L.T.subtype
  have hN : ∀ x : T.L.T, (x : T.V) ∈ N ↔ p x ∈ LinearMap.range f := fun x =>
    ⟨fun ⟨_, hy, e⟩ => (Subtype.ext e : _ = x) ▸ hy, fun h => ⟨x, h, rfl⟩⟩
  have h₁ : N ≤ T.L.T := Submodule.map_subtype_le _ _
  have h₂ : L₂.T ≤ N := fun x hx => by
    refine (hN ⟨x, hle hx⟩).mpr ?_
    rw [(hk _).mpr hx]
    exact zero_mem _
  have hs : ∀ g, ∀ x ∈ N, T.ρ g x ∈ N := fun g x hx => by
    refine (hN (latRep T.L g ⟨x, h₁ hx⟩)).mpr ?_
    obtain ⟨y, hy⟩ := (hN ⟨x, h₁ hx⟩).mp hx
    exact ⟨π g y, by rw [hg, hf, hy]⟩
  let q : N →ₗ[O] M := (LinearEquiv.ofInjective f hi).symm.toLinearMap ∘ₗ
    (p ∘ₗ Submodule.inclusion h₁).codRestrict (LinearMap.range f) (fun x => (hN ⟨x, h₁ x.2⟩).mp x.2)
  have hq : ∀ x : N, f (q x) = p ⟨x, h₁ x.2⟩ := fun x =>
    congrArg Subtype.val ((LinearEquiv.ofInjective f hi).apply_symm_apply ⟨_, (hN ⟨x, h₁ x.2⟩).mp x.2⟩)
  refine ⟨Finite.of_injective f hi, μ, withLat T (between T.L L₂ N h₁ h₂ hs), hT.withLat _, L₂, q, h₂,
    fun y => ?_, fun g x => hi ?_, fun x => ?_⟩
  · obtain ⟨x, hx⟩ := hp (f y)
    exact ⟨⟨x.1, (hN x).mpr ⟨y, hx.symm⟩⟩, hi ((hq _).trans hx)⟩
  · exact (hq _).trans ((hg g ⟨x.1, h₁ x.2⟩).trans ((congrArg (π' g) (hq x).symm).trans (hf g _).symm))
  · refine Iff.trans ?_ (hk ⟨x.1, h₁ x.2⟩)
    rw [← hq x, ← map_zero f]
    exact hi.eq_iff.symm

end Per

theorem admissible_closed : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (S : TopSit P), S.Closed := by
  intro l _ P S M M' _ _ _ _ π π'
  obtain ⟨⟨hD, hDV, -⟩, -, -, hT, -⟩ := GlobalTheory.LocalIntegers.goodO_integers l S.LL
  exact ⟨fun f hf => ⟨admissible_of_injective f hf, admissible_of_surjective f hf⟩, admissible_prod⟩

end GlobalTheory.AdmClosure
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatio
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatio
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.FracAlg

theorem ratio_adjoin {k Ω B D : Type} [Field k] [Field Ω] [Algebra k Ω] [CommRing B] [CommRing D] [IsDomain D]
    (ι : B →+* D) (hι : Function.Injective ι) (o : Ω →+* D)
    (hk : ∀ c : k, ∃ b : B, ι b = o (algebraMap k Ω c)) (x : Ω)
    (hx : ∃ a b : B, b ≠ 0 ∧ ι a = o x * ι b) (y : Ω) (hy : y ∈ IntermediateField.adjoin k {x}) :
    ∃ a b : B, b ≠ 0 ∧ ι a = o y * ι b := by
  have hne : ∀ b : B, b ≠ 0 → ι b ≠ 0 := fun b hb h => hb (hι (by rw [h, map_zero]))
  have hmul : ∀ b b' : B, b ≠ 0 → b' ≠ 0 → b * b' ≠ 0 := fun b b' hb hb' h =>
    mul_ne_zero (hne b hb) (hne b' hb') (by rw [← map_mul, h, map_zero])
  have h1 : (1 : B) ≠ 0 := fun h => one_ne_zero (α := D) (by rw [← map_one ι, h, map_zero])
  induction hy using IntermediateField.adjoin_induction with
  | mem z hz => rw [Set.mem_singleton_iff.1 hz]; exact hx
  | algebraMap c =>
    obtain ⟨b, hb⟩ := hk c
    exact ⟨b, 1, h1, by rw [hb, map_one, mul_one]⟩
  | add z w _ _ hz hw =>
    obtain ⟨a, b, hb, e⟩ := hz
    obtain ⟨a', b', hb', e'⟩ := hw
    refine ⟨a * b' + a' * b, b * b', hmul _ _ hb hb', ?_⟩
    simp only [map_add (f := _), map_mul, e, e']
    ring
  | inv z _ hz =>
    obtain ⟨a, b, hb, e⟩ := hz
    by_cases h0 : z = 0
    · exact ⟨0, 1, h1, by simp [h0]⟩
    · have ho : o z ≠ 0 := by simpa using h0
      refine ⟨b, a, fun h => mul_ne_zero ho (hne b hb) (by rw [← e, h, map_zero]), ?_⟩
      rw [e, ← mul_assoc, ← map_mul, inv_mul_cancel₀ h0, map_one, one_mul]
  | mul z w _ _ hz hw =>
    obtain ⟨a, b, hb, e⟩ := hz
    obtain ⟨a', b', hb', e'⟩ := hw
    refine ⟨a * a', b * b', hmul _ _ hb hb', ?_⟩
    simp only [map_mul, e, e']
    ring

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

open GlobalTheory.MemLoc in
theorem norm_of_ratio {l : ℕ} [Fact l.Prime] (C : Core l) (a b : Per.Bcris l) (x : Om l) (hb : b ≠ 0)
    (hx : x ≠ 0) (e : C.ι a = C.oD x * C.ι b) : ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k := by
  obtain ⟨r, a', ha'⟩ := bcris_eq_acris_localization_periodT_alt l C a
  obtain ⟨s, b', hb'⟩ := bcris_eq_acris_localization_periodT_alt l C b
  have hu := (core_t_unit_fil l C).1
  have hA : algebraMap (Per.Acris l) (Per.Bcris l) (a' * C.t ^ s) =
      a * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ (r + s) := by
    rw [map_mul, map_pow, ← ha', pow_add, mul_assoc]
  have hB : algebraMap (Per.Acris l) (Per.Bcris l) (b' * C.t ^ r) =
      b * algebraMap (Per.Acris l) (Per.Bcris l) C.t ^ (r + s) := by
    rw [map_mul, map_pow, ← hb', add_comm r s, pow_add, mul_assoc]
  refine GlobalTheory.MemLoc.GaussCore.norm_eq_zpow l C (a' * C.t ^ s) (b' * C.t ^ r) x (fun h => hb ?_) hx ?_
  · rw [h, map_zero] at hB
    exact ((hu.pow _).mul_left_eq_zero).1 hB.symm
  · apply (BdRField.bdR_isField l).2.1
    rw [map_mul (algebraMap (Per.BdRp l) (Per.BdR l)), ← C.ι_j, ← C.ι_j, hA, hB, map_mul C.ι, map_mul C.ι, e,
      mul_assoc]
    rfl

end

theorem mem_Kur_of_ratio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (a b : P.R.B) (x : Om l), b ≠ 0 → P.ιB a = algebraMap (Om l) P.R.BdR x * P.ιB b → x ∈ MaximalUnramifiedExtension l := by
  intro l _ P AI T a b x hb e
  obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI T
  obtain ⟨hF, -, hinj, -⟩ := GlobalTheory.Per.TiedField.tied_field l P AI T
  have : IsDomain P.R.BdR := hF.isDomain
  have hint : IsIntegral ℚ_[l] x := Algebra.IsIntegral.isIntegral _
  refine GlobalTheory.UnramValue.le_Kur_of_norm l ⟨IntermediateField.adjoin ℚ_[l] {x}, IntermediateField.adjoin.finiteDimensional hint⟩
    (fun y hy hy0 => ?_) (IntermediateField.mem_adjoin_simple_self ℚ_[l] x)
  obtain ⟨a', b', hb', e'⟩ := ratio_adjoin (k := ℚ_[l]) (P.ιB : P.R.B →+* P.R.BdR) hinj
    (algebraMap (Om l) P.R.BdR)
    (fun c => ⟨algebraMap ℚ_[l] P.R.B c,
      (P.ιB.commutes c).trans (IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR c)⟩) x ⟨a, b, hb, e⟩ y hy
  refine norm_of_ratio C (T.eB a') (T.eB b') y (fun h => hb' (T.eB.injective (h.trans (map_zero _).symm))) hy0 ?_
  rw [← hC.ι, ← hC.ι, ← hC.o, ← map_mul]
  exact congrArg T.eD e'

end GlobalTheory.FracAlg
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemMaxUnramifiedOfCrystallineRatioStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_maxUnramified_of_crystallineRatio : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (a b : P.R.B) (x : Om l), b ≠ 0 → P.ιB a = algebraMap (Om l) P.R.BdR x * P.ιB b → x ∈ MaximalUnramifiedExtension l := by
  first | exact @GlobalTheory.FracAlg.mem_Kur_of_ratio | exact GlobalTheory.FracAlg.mem_Kur_of_ratio | (intros; apply GlobalTheory.FracAlg.mem_Kur_of_ratio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqOfExhaustive
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct

namespace GlobalTheory.Per.FilCount

theorem exists_eq_of_exhaustive {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
    (D : Submodule k M) [FiniteDimensional k D] (F : ℤ → Submodule k M) (hF : Antitone F)
    (hle : ∀ a, F a ≤ D) (hex : ∀ x ∈ D, ∃ a, x ∈ F a) : ∃ b : ℤ, ∀ a ≤ b, F a = D := by
  obtain ⟨s, hs⟩ : D.FG := (Submodule.fg_iff_finiteDimensional D).2 inferInstance
  have hsD : ∀ x ∈ s, x ∈ D := fun x hx => hs ▸ Submodule.subset_span hx
  choose! f hf using hex
  obtain ⟨b, hb⟩ := (s.image f).bddBelow
  refine ⟨b, fun a ha => le_antisymm (hle a) ?_⟩
  rw [← hs, Submodule.span_le]
  intro x hx
  have hbx : b ≤ f x := hb (Finset.mem_coe.2 (Finset.mem_image_of_mem f hx))
  exact hF (ha.trans hbx) (hf x (hsD x hx))

theorem telescope (d : ℤ → ℤ) (c : ℤ) (b : ℤ) (hb : ∀ a ≤ b, d a = c) (J : Finset ℤ)
    (hJ : ∀ a, a ∉ J → d a - d (a + 1) = 0) :
    c - d 0 = ∑ a ∈ J.filter (· < 0), (d a - d (a + 1)) := by
  have tel : ∀ n : ℕ, ∑ a ∈ Finset.Ico (-(n : ℤ)) 0, (d a - d (a + 1)) = d (-n) - d 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have e : Finset.Ico (-((n + 1 : ℕ) : ℤ)) 0
          = insert (-((n + 1 : ℕ) : ℤ)) (Finset.Ico (-(n : ℤ)) 0) := by
        ext x
        simp only [Finset.mem_Ico, Finset.mem_insert]
        push_cast
        omega
      rw [e, Finset.sum_insert (by simp only [Finset.mem_Ico]; push_cast; omega), ih]
      have e2 : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by push_cast; ring
      rw [e2]; ring
  obtain ⟨m, hm⟩ := J.bddBelow
  obtain ⟨n, hn1, hn2⟩ : ∃ n : ℕ, -(n : ℤ) ≤ m ∧ -(n : ℤ) ≤ b :=
    ⟨m.natAbs + b.natAbs, by omega, by omega⟩
  rw [← hb _ hn2, ← tel n]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro x hx
    rw [Finset.mem_filter] at hx
    exact Finset.mem_Ico.2 ⟨hn1.trans (hm (Finset.mem_coe.2 hx.1)), hx.2⟩
  · intro x hx hx'
    refine hJ x fun h => hx' (Finset.mem_filter.2 ⟨h, (Finset.mem_Ico.1 hx).2⟩)

section

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem tmul_mem_filV (a : ℤ) (v : V) (b : BdR) (hb : b ∈ PD.Fil a) :
    v ⊗ₜ[Qp] b ∈ FilV PD (LL := LL) (V := V) a :=
  ⟨v ⊗ₜ[Qp] ⟨b, hb⟩, rfl⟩

theorem filV_antitone : Antitone (FilV PD (LL := LL) (V := V)) := by
  have hA : Antitone PD.Fil := antitone_int_of_succ_le PD.Fil_anti
  rintro a b hab _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | tmul v c => exact tmul_mem_filV PD a v c.1 (hA hab c.2)
  | add x y hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy

theorem filV_exhaustive (x : V ⊗[Qp] BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v c =>
    obtain ⟨a, ha⟩ := PD.Fil_exh c
    exact ⟨a, tmul_mem_filV PD a v c ha⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filV_antitone PD (min_le_left a b) ha)
      (filV_antitone PD (min_le_right a b) hb)⟩

theorem codim_fil_zero (ρ : Representation LL G V) [FiniteDimensional LL ↥(DdR PD ρ)]
    (τ : K →ₐ[Qp] LL) (J : Finset ℤ) (hJ : ∀ a, a ∉ J → multV PD ρ τ a = 0) :
    (Module.finrank LL ↥(DdRE PD ρ τ) : ℤ) - Module.finrank LL ↥(FildR PD ρ τ 0)
      = ∑ a ∈ J.filter (· < 0), multV PD ρ τ a := by
  have : FiniteDimensional LL ↥(DdRE PD ρ τ) :=
    Submodule.finiteDimensional_of_le (S₂ := DdR PD ρ) inf_le_left
  obtain ⟨b, hb⟩ := exists_eq_of_exhaustive (DdRE PD ρ τ) (FildR PD ρ τ)
    (fun a b hab => inf_le_inf_left _ (filV_antitone PD hab)) (fun a => inf_le_left)
    (fun x hx => (filV_exhaustive PD (LL := LL) x).imp fun a ha => ⟨hx, ha⟩)
  exact telescope (fun a => (Module.finrank LL ↥(FildR PD ρ τ a) : ℤ)) _ b
    (fun a ha => by rw [hb a ha]) J hJ

end

theorem fil_count : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
    ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
      [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)
      (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (J : Finset ℤ), (∀ a, a ∉ J → multV (P.PD K) ρ τ a = 0) →
      (Module.finrank ↥LL.1 ↥(DdRE (P.PD K) ρ τ) : ℤ) - Module.finrank ↥LL.1 ↥(FildR (P.PD K) ρ τ 0)
        = ∑ a ∈ J.filter (· < 0), multV (P.PD K) ρ τ a := by
  intro l _ P AI T K LL V _ _ _ _ _ ρ τ J hJ
  have := (GlobalTheory.Per.TiedDdR.ddR_finrank_le l P AI T K LL V ρ).1
  exact codim_fil_zero (P.PD K) ρ τ J hJ

end GlobalTheory.Per.FilCount
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAndEventuallySubMemLat
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAndEventuallySubMemLat
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem io_mem_Lat_of_mem_span {M n : ℕ} {x : Ainf l}
    (hx : x ∈ Ideal.span {((l : ℕ) : Ainf l) ^ n, AI.ξ ^ M}) : io AI x ∈ Lat AI M n := by
  obtain ⟨p, q, rfl⟩ := Ideal.mem_span_pair.1 hx
  rw [map_add (f := _), mul_comm p]
  refine add_mem (io_mem_Lat AI M n p) (FilB_le_Lat AI ?_)
  rw [map_mul, map_pow]
  exact FilB_zero_mul (io_mem AI q) (by simpa using FilB_pow (io_ξ_mem AI) M)

theorem bounded_and_eventually_sub_mem_Lat : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l)
    (AI : LocAinf l P), LocTied l P AI → ∀ b ∈ FilB P 0, ∀ M n : ℕ,
    (∃ k : ℕ, (l : P.R.BdR) ^ k * b ∈ Lat AI M n) ∧
      ∀ᶠ σ in nhds (1 : GQ l), P.actQdR σ b - b ∈ Lat AI M n := by
  intro l _ P AI T b hb M n
  obtain ⟨k, a, ha⟩ := GlobalTheory.BdRQuot.exists_approx T M b hb
  change (l : P.R.BdR) ^ k * b - io AI a ∈ FilB P (M : ℤ) at ha
  constructor
  · have h0 : (l : P.R.BdR) ^ k * b ∈ Lat AI M 0 := ⟨a, by simpa using ha⟩
    refine ⟨n + k, ?_⟩
    rw [pow_add, mul_assoc]
    exact (pow_mul_mem_Lat_iff AI (k := n) (n := 0)).2 h0
  · filter_upwards [GlobalTheory.AinfCont.eventually_sub_mem AI (k + n) M a] with g hg
    rw [← pow_mul_mem_Lat_iff AI (k := k)]
    have h1 := io_mem_Lat_of_mem_span AI hg
    have h2 := FilB_le_Lat AI (n := k + n) (sub_mem (act_mem g ha) ha)
    have h3 := add_mem h1 h2
    rw [map_sub, io_act, map_sub, map_mul, map_pow, map_natCast] at h3
    convert h3 using 1
    ring

end GlobalTheory.ExpImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BoundedAndEventuallySubMemLatStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_and_eventually_sub_mem_Lat_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ b ∈ FilB P 0, ∀ M n : ℕ, (∃ k : ℕ, (l : P.R.BdR) ^ k * b ∈ Lat AI M n) ∧ ∀ᶠ σ in nhds (1 : GQ l), P.actQdR σ b - b ∈ Lat AI M n := by
  first | exact @GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat | exact GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat | (intros; apply GlobalTheory.ExpImage.bounded_and_eventually_sub_mem_Lat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatum
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatum
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
open Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.Cyc.TwistLift GlobalTheory.TateTop

namespace GlobalTheory.TateTop

theorem tateH2_of_duality_loc (hT : Formalism.GaloisCohomology.LocalTateDualityK) :
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), LocalTateTopDegree (P.PD K) := by
  intro l _ P K LL _ _ _ O _ _ hO L1 hL1
  obtain ⟨hΦ1, hΦ2⟩ := continuous_fixingSubgroupEquiv K.1
  set Φ := K.1.fixingSubgroupEquiv with hΦ
  have hcyc : IsCyc P.χQ := P.χQ_cyc
  let χZ : Formalism.GaloisCohomology.GK l K.1 →* ℤ_[l]ˣ := (cyclotomicCharacter (PadicAlgCl l) l).comp
      (MulSemiringAction.toRingAut (Formalism.GaloisCohomology.GK l K.1) (PadicAlgCl l))
  have hχZ : ∀ g, ((χZ g : ℤ_[l]) : ℚ_[l]) = (P.χQ (Φ.symm g : GQ l) : ℚ_[l]) := fun g => by
    rw [isCyc_unique hcyc (isCyc_cycChar l)]; rfl
  have hχc : Continuous fun g => (χZ g : ℤ_[l]) := by
    rw [continuous_iff_coe]
    simp only [hχZ]
    exact hcyc.continuous.comp (continuous_subtype_val.comp hΦ1)
  obtain ⟨c, hc⟩ := exists_gen_all hχc fun r => by
    have : NeZero (l ^ (r + 1)) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
    exact exists_gen hχc
      (hT l K.1 K.2 (r + 1) (ZMod (l ^ (r + 1))) (ReciprocityTheory.Gal.charRep (redChar χZ (r + 1)))
        (Nat.succ_pos _) (contAction_charRep _ ((continuous_toZModPow _).comp hχc))).1
      fun M _ _ _ _ _ rho hrho => (hT l K.1 K.2 (r + 1) M rho (Nat.succ_pos _) hrho).2.2.2.2
  have hcpt : CompactSpace (GK K) := Φ.symm.surjective.compactSpace hΦ1
  obtain ⟨ι, hι⟩ := exists_ringHom hO
  let : Module ℤ_[l] (LL ⧸ L1.T) := Module.compHom _ ι
  have : SMulCommClass ℤ_[l] O (LL ⧸ L1.T) := ⟨fun a o x => smul_comm (ι a) o x⟩
  have hs : ∀ (a : ℤ_[l]) (x : LL), a • (Submodule.Quotient.mk x : LL ⧸ L1.T) =
      Submodule.Quotient.mk (algebraMap ℚ_[l] LL a * x) := fun a x => by
    rw [← hι, ← Algebra.smul_def]
    rfl
  refine @h2_equiv_of_torsion_character l _ (GK K) _ _ _ _ _ _ hcpt _ (fun r => (hc r).transport Φ hΦ2 hΦ1)
    (fun x => ?_) O _ _ _ _ fun g x => ?_
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨n, hn⟩ := exists_pow_smul_mem hO x
    refine ⟨n, ?_⟩
    rw [hs, Submodule.Quotient.mk_eq_zero, hL1]
    simpa using hn 1
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [hs]
    have h1 := hχZ (Φ g)
    rw [show Φ.symm (Φ g) = g from Φ.symm_apply_apply g, ← P.PD_χ K g] at h1
    change Submodule.Quotient.mk (algebraMap ℚ_[l] LL ((P.PD K).χ g : ℚ_[l]) * x) = _
    rw [← h1]
    rfl

end GlobalTheory.TateTop
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateH2PeriodDatumStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tate_H2_period_datum : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K : FinExt l), LocalTateTopDegree (P.PD K) := by
  first | exact @GlobalTheory.TateTop.tateH2_of_duality_loc | exact GlobalTheory.TateTop.tateH2_of_duality_loc | (intros; apply GlobalTheory.TateTop.tateH2_of_duality_loc <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjective
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjective
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TensorInj

theorem exists_div_of_mem_closure {A D : Type} [CommRing A] [Field D] (g : A →+* D) {y : D}
    (hy : y ∈ Subfield.closure (Set.range g)) (h0 : y ≠ 0) : ∃ a b : A, b ≠ 0 ∧ g a = y * g b := by
  obtain ⟨p, hp, q, hq, e⟩ := Subfield.mem_closure_iff.1 hy
  have hr : Subring.closure (Set.range g) = g.range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  rw [hr] at hp hq
  obtain ⟨a, rfl⟩ := hp
  obtain ⟨b, rfl⟩ := hq
  have hb : g b ≠ 0 := fun h => h0 (by rw [← e, h, div_zero])
  refine ⟨a, b, fun h => hb (by rw [h, map_zero]), ?_⟩
  rw [← e, div_mul_cancel₀ _ hb]

theorem indep_of_fractions (l : ℕ) [Fact l.Prime] {A B D : Type} [CommRing A] [CommRing B] [CommRing D]
    (hD : IsField D) (g : A →+* D) (ι : B →+* D) (hι : Function.Injective ι) (o : Om l →+* D)
    (hB : ∀ b : B, ∃ a a' : A, g a' ≠ 0 ∧ ι b * g a' = g a)
    (hu : ∀ c : ↥(MaximalUnramifiedExtension l), ∃ b : B, ι b = o (c : Om l))
    (hv : ∀ (a b : A) (x : Om l), b ≠ 0 → x ≠ 0 → g a = o x * g b → ∃ k : ℤ, ‖x‖ = (l : ℝ) ^ k)
    (m : ℕ) (x : Fin m → Om l) (hx : LinearIndependent ↥(MaximalUnramifiedExtension l) x) (b : Fin m → B)
    (hb : ∑ i, o (x i) * ι (b i) = 0) (i : Fin m) : b i = 0 := by
  letI : Field D := hD.toField
  let F : Subfield D := Subfield.closure (Set.range g)
  have hg : ∀ a, g a ∈ F := fun a => Subfield.subset_closure ⟨a, rfl⟩
  have hιF : ∀ b, ι b ∈ F := fun b => by
    obtain ⟨a, a', h0, e⟩ := hB b
    rw [eq_div_of_mul_eq h0 e]
    exact F.div_mem (hg a) (hg a')
  have hK : ∀ c : ↥(MaximalUnramifiedExtension l), o (c : Om l) ∈ F := fun c => by
    obtain ⟨b, e⟩ := hu c
    exact e ▸ hιF b
  let E : IntermediateField ℚ_[l] (Om l) :=
    (F.comap o).toIntermediateField fun q => hK (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q)
  have hE : ∀ y : Om l, o y ∈ F → y ∈ MaximalUnramifiedExtension l := fun y hy => by
    have hint : IsIntegral ℚ_[l] y := Algebra.IsIntegral.isIntegral y
    have hle : IntermediateField.adjoin ℚ_[l] {y} ≤ E :=
      IntermediateField.adjoin_simple_le_iff.2 hy
    refine GlobalTheory.UnramValue.le_Kur_of_norm l ⟨IntermediateField.adjoin ℚ_[l] {y},
      IntermediateField.adjoin.finiteDimensional hint⟩ (fun z hz h0 => ?_)
      (IntermediateField.mem_adjoin_simple_self ℚ_[l] y)
    obtain ⟨a, a', h1, e⟩ := exists_div_of_mem_closure g (y := o z) (hle hz) ((map_ne_zero o).2 h0)
    exact hv a a' z h1 h0 e
  haveI : IsGalois ℚ_[l] (Om l) := {}
  haveI : IsGalois ↥(MaximalUnramifiedExtension l) (Om l) := IsGalois.tower_top_of_isGalois ℚ_[l] _ _
  have := GlobalTheory.T.eq_zero_of_sum_map_mul_eq_zero_of_linearIndependent ↥(MaximalUnramifiedExtension l) (Om l) D o F
    (fun y => ⟨fun h => ⟨⟨y, hE y h⟩, rfl⟩, fun ⟨c, h⟩ => h ▸ hK c⟩) m x hx (fun i => ι (b i))
    (fun i => hιF _) hb i
  exact hι (this.trans (map_zero ι).symm)

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem tensorInj (l : ℕ) [Fact l.Prime] (c : Core l) : c.TensorInj := by
  obtain ⟨-, hinj, hD, -⟩ := BdRField.bdR_isField l
  have hι : Function.Injective c.ι := (ULaws.u_laws l c).2.2.2.1
  haveI : Nontrivial (Per.BdR l) := ⟨hD.exists_pair_ne⟩
  refine indep_of_fractions l hD ((algebraMap (Per.BdRp l) (Per.BdR l)).comp c.j) c.ι hι c.oD
    (fun b => ?_) (fun x => ⟨c.u x, c.ι_u x⟩) (fun a b x hb hx e => ?_)
  · obtain ⟨r, a, e⟩ := bcris_eq_acris_localization_periodT_alt l c b
    refine ⟨a, c.t ^ r, ?_, ?_⟩
    · rw [RingHom.comp_apply, ← c.ι_j, map_pow]
      exact ((((core_t_unit_fil l c).1).pow r).map c.ι).ne_zero
    · rw [RingHom.comp_apply, RingHom.comp_apply, ← c.ι_j, ← c.ι_j, ← map_mul, map_pow, e]
  · refine @GlobalTheory.MemLoc.GaussCore.norm_eq_zpow l _ c a b x hb hx (hinj ?_)
    rw [map_mul]
    exact e

end GlobalTheory.MemLoc.TensorInj
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective : ∀ (l : ℕ) [Fact l.Prime] (c : Core l), c.TensorInj := by
  first | exact @GlobalTheory.MemLoc.TensorInj.tensorInj | exact GlobalTheory.MemLoc.TensorInj.tensorInj | (intros; apply GlobalTheory.MemLoc.TensorInj.tensorInj <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DetCharacterIrreducibleLabel
noncomputable section

namespace GlobalTheory.GLq.LabelDet

open GlobalTheory.GLq GlobalTheory.GLp Formalism.MainNotions.ArithmeticCylinders Formalism.CyclotomicNorms Polynomial
open scoped Classical ComplexOrder

variable {g : ℕ} [hg : Fact g.Prime]

theorem _root_.GlobalTheory.GLq.LabelDet.isIrr_hom {G : Type} [Group G] [Fintype G] (φ : G →* ℂˣ) :
    _root_.GlobalTheory.GLq.IsIrr (fun x : G => ((φ x : ℂˣ) : ℂ)) := by
  have hchar : ∀ x : G, (FDRep.of (_root_.GlobalTheory.GLp.Model.chRep φ)).character x = φ x := by
    intro x
    have : _root_.GlobalTheory.GLp.Model.chRep φ x = (φ x : ℂ) • LinearMap.id := by
      ext; simp [_root_.GlobalTheory.GLp.Model.chRep_apply]
    simp [FDRep.character, FDRep.of_ρ, this]
  refine ⟨FDRep.of (_root_.GlobalTheory.GLp.Model.chRep φ), ?_, hchar⟩
  rw [FDRep.simple_iff_char_is_norm_one]
  simp [hchar, Nat.card_eq_fintype_card]

theorem _root_.GlobalTheory.GLq.LabelDet.theta_gen_pow (L : _root_.GlobalTheory.GLq.LabelDatum g) {x : _root_.Formalism.CyclotomicNorms.Fbar g}
    (hx : x ^ (g ^ 1 - 1) = 1) (n : ℕ) :
    _root_.GlobalTheory.GLq.thetaOf L 1 x (L.gen 1 ^ n) =
      L.teich x ^ n :=
  _root_.GlobalTheory.GLq.Model.thetaOf_gen_pow L one_pos hx n

theorem _root_.GlobalTheory.GLq.LabelDet.gen_one_mem (L : _root_.GlobalTheory.GLq.LabelDatum g) :
    ∃ u : (ZMod g)ˣ, algebraMap (ZMod g) (_root_.Formalism.CyclotomicNorms.Fbar g) u = L.gen 1 := by
  obtain ⟨u, hu, -⟩ := _root_.GlobalTheory.GLp.Model.exists_gen L
  exact ⟨u, hu⟩

theorem _root_.GlobalTheory.GLq.LabelDet.det_inPar (a b : ℕ) (M : _root_.GlobalTheory.GLq.Mt g (a + b))
    (h : _root_.GlobalTheory.GLq.InPar a M) :
    M.det = (_root_.GlobalTheory.GLq.tl a M).det * (_root_.GlobalTheory.GLq.br a b M).det := by
  have key : M.submatrix finSumFinEquiv finSumFinEquiv = Matrix.fromBlocks (_root_.GlobalTheory.GLq.tl a M)
      (M.submatrix (Fin.castAdd b) (Fin.natAdd a)) 0 (_root_.GlobalTheory.GLq.br a b M) := by
    ext (i | i) (j | j)
    · show M (Fin.castAdd b i) (Fin.castAdd b j) = _root_.Formalism.MainNotions.ArithmeticCylinders.entN M i j
      have hi := i.isLt
      have hj := j.isLt
      unfold _root_.Formalism.MainNotions.ArithmeticCylinders.entN
      rw [dite_eq_left ⟨by omega, by omega⟩]
      rfl
    · simp
    · exact h _ _ (by simp) (by simp)
    · simp [_root_.GlobalTheory.GLq.br, _root_.Formalism.MainNotions.ArithmeticCylinders.entN, Fin.natAdd]
  rw [← Matrix.det_submatrix_equiv_self finSumFinEquiv M, key, Matrix.det_fromBlocks_zero₂₁]

theorem _root_.GlobalTheory.GLq.LabelDet.det_toG {n : ℕ} (M : _root_.GlobalTheory.GLq.Mt g n) (h : M.det ≠ 0) :
    ((Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG M) : (ZMod g)ˣ) : ZMod g) = M.det := by
  unfold _root_.GlobalTheory.GLq.toG
  rw [dite_eq_left ((Matrix.isUnit_iff_isUnit_det M).mpr (isUnit_iff_ne_zero.mpr h))]
  simp [Matrix.GeneralLinearGroup.val_det_apply]

theorem _root_.GlobalTheory.GLq.LabelDet.det_par (a b : ℕ) (p : _root_.GlobalTheory.GLq.Gn g (a + b))
    (h : _root_.GlobalTheory.GLq.InPar a (p : _root_.GlobalTheory.GLq.Mt g (a + b))) :
    Matrix.GeneralLinearGroup.det p =
      Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.tl a
        (p : _root_.GlobalTheory.GLq.Mt g (a + b)))) *
      Matrix.GeneralLinearGroup.det (_root_.GlobalTheory.GLq.toG (_root_.GlobalTheory.GLq.br a b
        (p : _root_.GlobalTheory.GLq.Mt g (a + b)))) := by
  have hdet := _root_.GlobalTheory.GLq.LabelDet.det_inPar a b _ h
  have hp := (Matrix.GeneralLinearGroup.det p).ne_zero
  rw [Matrix.GeneralLinearGroup.val_det_apply] at hp
  rw [hdet] at hp
  obtain ⟨h1, h2⟩ := mul_ne_zero_iff.mp hp
  apply Units.ext
  rw [Units.val_mul, _root_.GlobalTheory.GLq.LabelDet.det_toG _ h1, _root_.GlobalTheory.GLq.LabelDet.det_toG _ h2,
    Matrix.GeneralLinearGroup.val_det_apply, ← hdet]

theorem _root_.GlobalTheory.GLq.LabelDet.toG_one {n : ℕ} : _root_.GlobalTheory.GLq.toG (1 : _root_.GlobalTheory.GLq.Mt g n) = 1 := by
  unfold _root_.GlobalTheory.GLq.toG
  rw [dite_eq_left isUnit_one]
  exact Units.ext (by simp)

end GlobalTheory.GLq.LabelDet
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemRangeOfIsIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL
open scoped Formalism.Per

namespace GlobalTheory.ExpImage.EmbFil

theorem mem_range_of_isIntegral {F Ω L B : Type*} [Field F] [Field Ω] [IsAlgClosed Ω] [Algebra F Ω]
    [CommRing L] [Algebra F L] [CommRing B] [IsDomain B] [Algebra F B] [Algebra Ω B]
    [IsScalarTower F Ω B] (ι : L →ₐ[F] B) {x : L} (hx : IsIntegral F x) :
    ∃ a : Ω, algebraMap Ω B a = ι x :=
  IsAlgClosed.algebraMap_bijective_of_isIntegral (k := Ω) (K := integralClosure Ω B) |>.2
    ⟨ι x, (hx.map ι).tower_top⟩ |>.imp fun _ h => congrArg Subtype.val h

theorem algebraMap_mem_zero {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
    (T : LocTied l P AI) (a : Om l) : algebraMap (Om l) P.R.BdR a ∈ GlobalTheory.ExpImage.FilB P 0 := by
  obtain ⟨y, h1, -⟩ := T.om a
  obtain ⟨-, hone, -⟩ := GlobalTheory.MemLoc.filD_laws l
  refine (T.fil _ 0 _).2 ?_
  have := Submodule.smul_mem _ y hone
  rwa [Algebra.smul_def, mul_one, ← h1] at this

theorem emb_mem_fil_zero : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P),
    LocTied l P AI → ∀ (LL : FinExt l) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥LL.1),
      ι x ∈ GlobalTheory.ExpImage.FilB P 0 := by
  intro l _ P AI T LL ι x
  have := (GlobalTheory.Per.TiedField.tied_field l P AI T).1.isDomain
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  obtain ⟨a, ha⟩ := mem_range_of_isIntegral (Ω := Om l) ι (IsIntegral.of_finite ℚ_[l] x)
  rw [← ha]
  exact algebraMap_mem_zero T a

end GlobalTheory.ExpImage.EmbFil
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftsOfNormLeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftsOfNormLeOne
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage

namespace GlobalTheory.ExpImage

theorem exists_lifts_of_norm_le_one : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (c : ↥(K0 K)), ‖(c : Om l)‖ ≤ 1 → ∃ w : Ainf l, Lifts AI K w c := by
  intro l _ P AI T K c hc
  obtain ⟨n, z, ω, hω, hsum⟩ := GlobalTheory.T.exists_eq_sum_padicInt_mul_rootsOfUnity l K c c.2 hc
  have h1 : ∀ i, ∃ w : Ainf l, Lifts AI K w ⟨ω i, (hω i).1⟩ := by
    intro i
    obtain ⟨hK, m, hm, hl, hx⟩ := hω i
    obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (ω i) m hm hl hx
    exact ⟨_, AI.ιA_teich ⟨ω i, hK.2⟩ m hm hl hx xb hxb⟩
  choose w hw using h1
  have h2 : c = ∑ i, algebraMap ℚ_[l] ↥(K0 K) (z i : ℚ_[l]) * ⟨ω i, (hω i).1⟩ := by
    apply Subtype.ext
    rw [hsum]
    push_cast
    rfl
  refine ⟨∑ i, algebraMap ℤ_[l] (Ainf l) (z i) * w i, ?_⟩
  unfold Lifts at hw ⊢
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h2, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, map_mul, hw, ιA_zl AI T, ← IsScalarTower.algebraMap_apply]

end GlobalTheory.ExpImage
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLiftsOfNormLeOneStatement
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc GlobalTheory.ExpImage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lifts_of_norm_le_one_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (c : ↥(K0 K)), ‖(c : Om l)‖ ≤ 1 → ∃ w : Ainf l, Lifts AI K w c := by
  first | exact @GlobalTheory.ExpImage.exists_lifts_of_norm_le_one | exact GlobalTheory.ExpImage.exists_lifts_of_norm_le_one | (intros; apply GlobalTheory.ExpImage.exists_lifts_of_norm_le_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjective
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjective
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.PMon.ThetaFil

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI)

def fil0 : Subring P.R.BdR :=
  (algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l)).range.comap T.eD.toRingHom

theorem mem_deRhamFilZeroSubringPreimage_iff (x : P.R.BdR) : x ∈ fil0 T ↔ x ∈ Fil P 0 := by
  change (∃ z, algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) z = T.eD x) ↔ _
  exact (GlobalTheory.ThetaTie.fil_zero T x).symm

def theta : ↥(fil0 T) →+* ℂ_[l] where
  toFun x := (GlobalTheory.ThetaTie.thetaL T).θ x
  map_one' := (GlobalTheory.ThetaTie.thetaL T).θ_one
  map_mul' x y := (GlobalTheory.ThetaTie.thetaL T).θ_mul _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2) _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 y.2)
  map_zero' := by
    have h0 : (0 : P.R.BdR) ∈ Fil P 0 := (mem_deRhamFilZeroSubringPreimage_iff T 0).1 (zero_mem _)
    have h := (GlobalTheory.ThetaTie.thetaL T).θ_add _ h0 _ h0
    rw [add_zero] at h
    change (GlobalTheory.ThetaTie.thetaL T).θ 0 = 0
    exact left_eq_add.1 h
  map_add' x y := (GlobalTheory.ThetaTie.thetaL T).θ_add _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2) _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 y.2)

theorem theta_apply (x : ↥(fil0 T)) : theta T x = (GlobalTheory.ThetaTie.thetaL T).θ x := rfl

theorem act_mem (g : GQ l) (x : P.R.BdR) (hx : x ∈ fil0 T) : P.actQdR g x ∈ fil0 T := by
  obtain ⟨a, ha⟩ := hx
  refine ⟨Formalism.Per.σDp g a, ?_⟩
  change _ = T.eD (P.actQdR g x)
  rw [T.actD]
  change _ = Formalism.Per.σD g (T.eD x)
  have ha' : algebraMap (Formalism.Per.BdRp l) (Formalism.Per.BdR l) a = T.eD x := ha
  rw [← ha']
  exact (GlobalTheory.MemLoc.ActLaws.σD_alg g a).symm

end GlobalTheory.PMon.ThetaFil

namespace GlobalTheory.PMon

open GlobalTheory.PMon.ThetaFil in
theorem exists_theta_deRhamFilZero_surjective_alt : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI),
    ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ Function.Surjective θ ∧
      (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧
      (∀ y : Om l, ∃ h, θ ⟨algebraMap (Om l) P.R.BdR y, h⟩ = (y : ℂ_[l])) ∧
      ∀ (g : GQ l) (x : ↥S), ∃ h, θ ⟨P.actQdR g x, h⟩ = Formalism.Per.σC g (θ x) := by
  intro l _ P AI T
  refine ⟨fil0 T, theta T, mem_deRhamFilZeroSubringPreimage_iff T, ?_, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨x, hx, e⟩ := (GlobalTheory.ThetaTie.thetaL T).θ_onto c
    exact ⟨⟨x, (mem_deRhamFilZeroSubringPreimage_iff T x).2 hx⟩, e⟩
  · intro x
    exact (GlobalTheory.ThetaTie.thetaL T).θ_ker _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2)
  · intro y
    obtain ⟨z, h1, -⟩ := T.om y
    exact ⟨⟨z, h1.symm⟩, (GlobalTheory.ThetaTie.thetaL T).θ_Om y⟩
  · intro g x
    refine ⟨act_mem T g x x.2, ?_⟩
    rw [theta_apply, theta_apply, (GlobalTheory.ThetaTie.thetaL T).θ_act g _ ((mem_deRhamFilZeroSubringPreimage_iff T _).1 x.2)]
    exact GlobalTheory.ThetaTie.actC_eq AI g _

end GlobalTheory.PMon
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsThetaDeRhamFilZeroSurjectiveStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_deRhamFilZero_surjective : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI), ∃ (S : Subring P.R.BdR) (θ : ↥S →+* ℂ_[l]), (∀ x, x ∈ S ↔ x ∈ Fil P 0) ∧ Function.Surjective θ ∧ (∀ x : ↥S, θ x = 0 ↔ (x : P.R.BdR) ∈ Fil P 1) ∧ (∀ y : Om l, ∃ h, θ ⟨algebraMap (Om l) P.R.BdR y, h⟩ = (y : ℂ_[l])) ∧ ∀ (g : GQ l) (x : ↥S), ∃ h, θ ⟨P.actQdR g x, h⟩ = Formalism.Per.σC g (θ x) := by
  first | exact @GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt | exact GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt | (intros; apply GlobalTheory.PMon.exists_theta_deRhamFilZero_surjective_alt <;> assumption)
end
end
