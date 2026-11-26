module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst
public import Development.WeilBound.CoreStatements.ThetaDilations.SdTransport
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
public import Development.WeilBound.RepresentationTheoryGL.FormalDegree.FormalDegreeHilbert.HlamStable
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.HaarMirror
public import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingIsoOfComponentIsos
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingIsoOfComponentIsos
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.KunGlue.Transfer

variable {K : Type} [Field K]

theorem exCls (C : Cx.{1} K) {n : ℕ} (c : C.H n) : ∃ (x : C.X n) (hx : C.d n x = 0), C.cls x hx = c := by
  obtain ⟨⟨x, hx⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨x, hx, rfl⟩

theorem sub_mem_of_cls_eq {C : Cx.{1} K} {n : ℕ} {x y : C.X n} {hx : C.d n x = 0} {hy : C.d n y = 0}
    (h : C.cls x hx = C.cls y hy) : x - y ∈ C.B n :=
  (Submodule.Quotient.eq ((C.B n).submoduleOf (C.Z n)) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)).1 h

theorem cls_eq_of_sub_mem {C : Cx.{1} K} {n : ℕ} {x y : C.X n} {hx : C.d n x = 0} {hy : C.d n y = 0}
    (h : x - y ∈ C.B n) : C.cls x hx = C.cls y hy :=
  (Submodule.Quotient.eq ((C.B n).submoduleOf (C.Z n)) (x := ⟨x, hx⟩) (y := ⟨y, hy⟩)).2 h

theorem d_map_cocycle {C D : Cx.{1} K} (φ : Cx.Hom C D (RingHom.id K)) {n : ℕ} {x : C.X n} (hx : C.d n x = 0) :
    D.d n (φ.f n x) = 0 := by
  rw [φ.comm, hx, map_zero]

theorem d_mu_cocycle {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x : A.X p} {y : B.X q}
    (hx : A.d p x = 0) (hy : B.d q y = 0) : M.d n (pr.μ h x y) = 0 := by
  rw [pr.leib, hx, hy]
  simp

theorem cls_mu_left {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x x' : A.X p} {y : B.X q}
    {hx : A.d p x = 0} {hx' : A.d p x' = 0} (hy : B.d q y = 0) {hz : M.d n (pr.μ h x y) = 0}
    {hz' : M.d n (pr.μ h x' y) = 0} (e : A.cls x hx = A.cls x' hx') :
    M.cls (pr.μ h x y) hz = M.cls (pr.μ h x' y) hz' := by
  apply cls_eq_of_sub_mem
  have hb := sub_mem_of_cls_eq e
  rw [← LinearMap.sub_apply, ← map_sub]
  cases p with
  | zero =>
    have h0 : x - x' = 0 := hb
    rw [h0, map_zero, LinearMap.zero_apply]
    exact zero_mem _
  | succ p =>
    obtain ⟨w, hw⟩ := hb
    obtain rfl : n = (p + q) + 1 := by omega
    change _ ∈ LinearMap.range (M.d (p + q))
    refine ⟨pr.μ rfl w y, ?_⟩
    rw [pr.leib, hw, hy]
    simp

theorem cls_mu_right {A B M : Cx.{1} K} (pr : CxPairing A B M) {p q n : ℕ} (h : p + q = n) {x : A.X p} {y y' : B.X q}
    (hx : A.d p x = 0) {hy : B.d q y = 0} {hy' : B.d q y' = 0} {hz : M.d n (pr.μ h x y) = 0}
    {hz' : M.d n (pr.μ h x y') = 0} (e : B.cls y hy = B.cls y' hy') :
    M.cls (pr.μ h x y) hz = M.cls (pr.μ h x y') hz' := by
  apply cls_eq_of_sub_mem
  have hb := sub_mem_of_cls_eq e
  rw [← map_sub]
  cases q with
  | zero =>
    have h0 : y - y' = 0 := hb
    rw [h0, map_zero]
    exact zero_mem _
  | succ q =>
    obtain ⟨w, hw⟩ := hb
    obtain rfl : n = (p + q) + 1 := by omega
    change _ ∈ LinearMap.range (M.d (p + q))
    refine ⟨(-1 : ℤ) ^ p • pr.μ rfl x w, ?_⟩
    rw [map_zsmul, pr.leib, hw, hx]
    simp [smul_smul, ← mul_pow]

def sumCongr {I : Type} [DecidableEq I] {A B : I → Type 1} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module K (A i)] [∀ i, Module K (B i)] (e : ∀ i, A i ≃ₗ[K] B i) : (⨁ i, A i) ≃ₗ[K] ⨁ i, B i :=
  DFinsupp.mapRange.linearEquiv e

theorem sumCongr_lof {I : Type} [DecidableEq I] {A B : I → Type 1} [∀ i, AddCommGroup (A i)] [∀ i, AddCommGroup (B i)]
    [∀ i, Module K (A i)] [∀ i, Module K (B i)] (e : ∀ i, A i ≃ₗ[K] B i) (i : I) (x : A i) :
    sumCongr e (DirectSum.lof K I A i x) = DirectSum.lof K I B i (e i x) :=
  DFinsupp.mapRange_single (hf := fun i => map_zero (e i))

theorem kunE_iff : ∀ {K : Type} [Field K] {P P' Q Q' T T' : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (pr' : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P' a) (Q' a') (T' c)) (p : ∀ a, Cx.Hom (P a) (P' a) (RingHom.id K)) (f : ∀ a, Cx.Hom (Q a) (Q' a) (RingHom.id K)) (g : ∀ a, Cx.Hom (T a) (T' a) (RingHom.id K)), (∀ a n, Function.Bijective ((p a).mapH n)) → (∀ a n, Function.Bijective ((f a).mapH n)) → (∀ a n, Function.Bijective ((g a).mapH n)) → (∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j), (g c).f n ((pr ha).μ h x y) = (pr' ha).μ h ((p a).f i x) ((f a').f j y)) → (KunE pr ↔ KunE pr') := by
  intro K _ P P' Q Q' T T' pr pr' p f g hp hf hg hc
  let eP : ∀ a n, (P a).H n ≃ₗ[K] (P' a).H n := fun a n => LinearEquiv.ofBijective ((p a).mapH n) (hp a n)
  let eQ : ∀ a n, (Q a).H n ≃ₗ[K] (Q' a).H n := fun a n => LinearEquiv.ofBijective ((f a).mapH n) (hf a n)
  let eT : ∀ a n, (T a).H n ≃ₗ[K] (T' a).H n := fun a n => LinearEquiv.ofBijective ((g a).mapH n) (hg a n)
  let eS : ∀ c n : ℕ, (⨁ t : Idx c n, (P t.a).H t.i ⊗[K] (Q t.a').H t.j) ≃ₗ[K]
      ⨁ t : Idx c n, (P' t.a).H t.i ⊗[K] (Q' t.a').H t.j :=
    fun c n => sumCongr fun t => TensorProduct.congr (eP t.a t.i) (eQ t.a' t.j)
  have hS : ∀ (c n : ℕ) (t : Idx c n) (x : (P t.a).X t.i) (y : (Q t.a').X t.j) (hx : (P t.a).d t.i x = 0)
      (hy : (Q t.a').d t.j y = 0),
      eS c n (DirectSum.lof K _ (fun t : Idx c n => (P t.a).H t.i ⊗[K] (Q t.a').H t.j) t
        ((P t.a).cls x hx ⊗ₜ (Q t.a').cls y hy)) =
      DirectSum.lof K _ (fun t : Idx c n => (P' t.a).H t.i ⊗[K] (Q' t.a').H t.j) t
        ((P' t.a).cls ((p t.a).f t.i x) (d_map_cocycle _ hx) ⊗ₜ (Q' t.a').cls ((f t.a').f t.j y) (d_map_cocycle _ hy)) := by
    intro c n t x y hx hy
    exact sumCongr_lof _ t _
  have hG : ∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j)
      (hz : (T c).d n ((pr ha).μ h x y) = 0) (hz' : (T' c).d n ((pr' ha).μ h ((p a).f i x) ((f a').f j y)) = 0),
      eT c n ((T c).cls ((pr ha).μ h x y) hz) = (T' c).cls ((pr' ha).μ h ((p a).f i x) ((f a').f j y)) hz' := by
    intro a a' c ha i j n h x y hz hz'
    have e0 := hc ha h x y
    change (T' c).cls ((g c).f n ((pr ha).μ h x y)) (d_map_cocycle _ hz) = _
    exact cls_eq_of_sub_mem (by rw [e0, sub_self]; exact zero_mem _)
  constructor
  · intro H c n
    obtain ⟨e, he⟩ := H c n
    refine ⟨(eS c n).symm ≪≫ₗ e ≪≫ₗ eT c n, ?_⟩
    intro t x y hx hy hz
    obtain ⟨x0, hx0, e1⟩ := exCls (P t.a) ((eP t.a t.i).symm ((P' t.a).cls x hx))
    obtain ⟨y0, hy0, e2⟩ := exCls (Q t.a') ((eQ t.a' t.j).symm ((Q' t.a').cls y hy))
    have e1' : (P' t.a).cls ((p t.a).f t.i x0) (d_map_cocycle _ hx0) = (P' t.a).cls x hx := by
      have := congrArg (eP t.a t.i) e1
      rwa [LinearEquiv.apply_symm_apply] at this
    have e2' : (Q' t.a').cls ((f t.a').f t.j y0) (d_map_cocycle _ hy0) = (Q' t.a').cls y hy := by
      have := congrArg (eQ t.a' t.j) e2
      rwa [LinearEquiv.apply_symm_apply] at this
    have hS' := hS c n t x0 y0 hx0 hy0
    rw [e1', e2'] at hS'
    have hz0 := d_mu_cocycle (pr t.ha) t.h hx0 hy0
    have hz1 := d_mu_cocycle (pr' t.ha) t.h (d_map_cocycle (p t.a) hx0) (d_map_cocycle (f t.a') hy0)
    have hz2 := d_mu_cocycle (pr' t.ha) t.h hx (d_map_cocycle (f t.a') hy0)
    simp only [LinearEquiv.trans_apply]
    rw [← hS', LinearEquiv.symm_apply_apply, he t x0 y0 hx0 hy0 hz0, hG t.ha t.h x0 y0 hz0 hz1,
      cls_mu_left (pr' t.ha) t.h (d_map_cocycle (f t.a') hy0) (hz' := hz2) e1',
      cls_mu_right (pr' t.ha) t.h hx (hz' := hz) e2']
  · intro H c n
    obtain ⟨e, he⟩ := H c n
    refine ⟨eS c n ≪≫ₗ e ≪≫ₗ (eT c n).symm, ?_⟩
    intro t x y hx hy hz
    have hz1 := d_mu_cocycle (pr' t.ha) t.h (d_map_cocycle (p t.a) hx) (d_map_cocycle (f t.a') hy)
    simp only [LinearEquiv.trans_apply]
    rw [hS c n t x y hx hy, he t _ _ _ _ hz1, ← hG t.ha t.h x y hz hz1, LinearEquiv.symm_apply_apply]

end GlobalTheory.CompanionTheory.KunGlue.Transfer
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PairingIsoOfComponentIsosStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct DirectSum GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT GlobalTheory.CompanionTheory.KunGlue
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pairing_iso_of_component_isos : ∀ {K : Type} [Field K] {P P' Q Q' T T' : ℕ → Cx.{1} K} (pr : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P a) (Q a') (T c)) (pr' : ∀ {a a' c : ℕ}, a + a' = c → CxPairing (P' a) (Q' a') (T' c)) (p : ∀ a, Cx.Hom (P a) (P' a) (RingHom.id K)) (f : ∀ a, Cx.Hom (Q a) (Q' a) (RingHom.id K)) (g : ∀ a, Cx.Hom (T a) (T' a) (RingHom.id K)), (∀ a n, Function.Bijective ((p a).mapH n)) → (∀ a n, Function.Bijective ((f a).mapH n)) → (∀ a n, Function.Bijective ((g a).mapH n)) → (∀ {a a' c : ℕ} (ha : a + a' = c) {i j n : ℕ} (h : i + j = n) (x : (P a).X i) (y : (Q a').X j), (g c).f n ((pr ha).μ h x y) = (pr' ha).μ h ((p a).f i x) ((f a').f j y)) → (KunE pr ↔ KunE pr') := by
  first | exact @GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff | exact GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff | (intros; apply GlobalTheory.CompanionTheory.KunGlue.Transfer.kunE_iff <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormula
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW PositivityTheory.Rg.Mass NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.RgMass

section Alg

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem sigma_sigma (hcm : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  apply τ.injective
  rw [hcm.2.2.2, hcm.2.2.2]
  simp

theorem hE_self_fixed (hcm : IsCMExt F E σ) {M : ℕ} {J : Matrix (Fin M) (Fin M) E} (hJ : IsHermND σ J) (x : Fin M → E) :
    σ (hE σ J x x) = hE σ J x x := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hE, hform, map_sum, map_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have h1 : σ ((σ : E →+* E) (x j)) = x j := sigma_sigma hcm _
  have h2 : (σ : E →+* E) (x i) = σ (x i) := rfl
  rw [h1, hJ.1 i j, h2]
  ring

theorem exists_len (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J)
    {X : Fin 1 → Fin 2 → E} (hX : X ≠ 0) : ∃ β : F, β ≠ 0 ∧ X ∈ sph σ J β := by
  have hT : ∀ a b, σ (gramE σ J X b a) = gramE σ J X a b := fun a b => by
    rw [Subsingleton.elim a b]
    exact hE_self_fixed hcm hJ _
  obtain ⟨β, e, h, -⟩ := GlobalTheory.T.hermitian_one_by_one_is_scalar F E σ hcm _ hT
  refine ⟨β, h ?_, e⟩
  rw [Matrix.det_unique]
  intro h0
  exact hX (funext fun a => by rw [Subsingleton.elim a default]; exact hA _ h0)

theorem sph_unique {J : Matrix (Fin 2) (Fin 2) E} {X : Fin 1 → Fin 2 → E} {β β' : F} (h : X ∈ sph σ J β)
    (h' : X ∈ sph σ J β') : β = β' := by
  have e : (fun _ _ => algebraMap F E β : Matrix (Fin 1) (Fin 1) E) = fun _ _ => algebraMap F E β' := h.symm.trans h'
  exact (algebraMap F E).injective (congrFun (congrFun e 0) 0)

theorem ne_zero_of_mem_sph {J : Matrix (Fin 2) (Fin 2) E} {X : Fin 1 → Fin 2 → E} {β : F} (hβ : β ≠ 0)
    (h : X ∈ sph σ J β) : X ≠ 0 := by
  rintro rfl
  refine hβ (sph_unique h ?_)
  funext a c
  simp [gramE, hE, hform]

def sphEquiv (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J) :
    (Σ β : {β : F // β ≠ 0}, sph σ J β.1) ≃ {X : Fin 1 → Fin 2 → E | X ≠ 0} :=
  Equiv.ofBijective (fun p => ⟨p.2.1, ne_zero_of_mem_sph p.1.2 p.2.2⟩) (by
    constructor
    · rintro ⟨β, X⟩ ⟨β', X'⟩ h
      have hX : X.1 = X'.1 := congrArg Subtype.val h
      have hb : β = β' := Subtype.ext (sph_unique X.2 (hX ▸ X'.2))
      subst hb
      obtain rfl : X = X' := Subtype.ext hX
      rfl
    · rintro ⟨X, hX⟩
      obtain ⟨β, h0, hβ⟩ := exists_len hcm hJ hA hX
      exact ⟨⟨⟨β, h0⟩, ⟨X, hβ⟩⟩, rfl⟩)

theorem thetaMeas_ne (hcm : IsCMExt F E σ) {J : Matrix (Fin 2) (Fin 2) E} (hJ : IsHermND σ J) (hA : Aniso σ J)
    (μ : Measure (HA (AF F) σ J)) (𝓕 : Set (HA (AF F) σ J)) :
    thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0} =
      Measure.sum fun β : {β : F // β ≠ 0} => thetaMeas σ J μ 𝓕 (sph σ J β.1) := by
  ext s hs
  simp only [thetaMeas, Measure.sum_apply _ hs, Measure.smul_apply, smul_eq_mul, ENNReal.tsum_mul_left]
  congr 1
  rw [← (sphEquiv hcm hJ hA).tsum_eq, ENNReal.tsum_sigma']
  rfl

end Alg


set_option maxHeartbeats 1000000 in
theorem cnt : TestEx → LSide → RSide → Cnt := by
  intro hTE hL hR F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm κ hκ
  obtain ⟨⟨θ, hθ⟩, -⟩ := PositivityTheory.PlacePermOperatorBicommutantSpan.theta_real F hcm.1
  obtain ⟨S, hS⟩ := hR F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ
  obtain ⟨φ, A, ht, hv0, hvT⟩ := hTE F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm S
  have hLt := hL F E σ J d b li lam μ 𝓕 mi m hcm hJ hAn hli hlam hμ h𝓕 hmi hm θ hθ S φ A ht
  have hRt := hS S (Finset.Subset.refl _) φ A ht
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : BorelSpace (Ainf F ⊗[F] E) := ⟨rfl⟩
  obtain ⟨_, _, _, _, -⟩ := GlobalTheory.T.infinite_adeles_local_ring_totally_real F hcm.1
  obtain ⟨_, -, -, -, -, -, -, hBinf, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Ainf F)
  have := hBinf 1 2
  obtain ⟨hφc, -, -, -, hAS, hAo⟩ := ht
  have hdil : ∀ ε : ℝ, Continuous (dil θ ε : (Fin 1 → Fin 2 → Ainf F ⊗[F] E) → _) := fun ε =>
    continuous_pi fun a => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have hloc : ∀ v, IsCompact (A v) ∧ MeasurableSet (A v) ∧
      ∀ s : HermR (Fv F v) σ 1, m v s (A v) < ⊤ := fun v => by
    have hRv := GlobalTheory.T.completion_is_local_ring F v
    have hRv' := hRv
    obtain ⟨_, _, _, _, -⟩ := hRv'
    have : BorelSpace (Fv F v) := ⟨rfl⟩
    obtain ⟨_, _, _, _, -, -, -, hB, -⟩ := GlobalTheory.T.tensor_locally_compact_ring F E σ hcm (Fv F v)
    have := hB 1 2
    obtain ⟨-, k1, k2⟩ := GlobalTheory.T.coordinate_haar_measure F E σ hcm (Fv F v) d b (lam v) (hlam v).1
    have hco : IsCompact (A v) ∧ IsOpen (A v) := by
      by_cases hv : v ∈ S
      · exact ⟨(hAS v hv).1, (hAS v hv).2.1⟩
      · rw [hAo v hv]
        exact (GlobalTheory.T.adelic_tuple_projections F E σ hcm d b 1 2).2.2.2.1 v
    refine ⟨hco.1, hco.2.measurableSet, fun s => ?_⟩
    have := (GlobalTheory.T.gram_fiber_measure_locallyFinite_and_ne_zero_of_isOpen F E σ hcm 2 J hJ (Fv F v) hRv 1 _ _ _ (k1 1 2) (k2 1) (hm v) s).1
    exact hco.1.measure_lt_top
  have hcof : ∀ᶠ v in cofinite, A v = latV b v :=
    S.finite_toSet.eventually_cofinite_notMem.mono fun v hv => hAo v (by simpa using hv)
  have key : ∀ ε : ℝ, ∫⁻ X in {X | ∀ v, projV v (projFin X) ∈ A v}, ENNReal.ofReal (φ (dil θ ε (projInf X)))
        ∂(thetaMeas σ J μ 𝓕 {X : Fin 1 → Fin 2 → E | X ≠ 0}) =
      (κ : ℝ≥0∞) * ∑' β : {β : F // β ≠ 0},
        (∫⁻ X, ENNReal.ofReal (φ (dil θ ε X)) ∂(mi (hermScal (Ainf F) σ (algebraMap F _ β.1)))) *
          ENNReal.ofReal (∏' v, (m v (hermScal (Fv F v) σ (algebraMap F _ β.1)) (A v)).toReal) := fun ε => by
    rw [thetaMeas_ne hcm hJ hAn, Measure.restrict_sum_of_countable, lintegral_sum_measure, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun β => ?_
    have hEu : IsEulerProd b (thetaMeas σ J μ 𝓕 (sph σ J β.1)) κ (mi (hermScal (Ainf F) σ (algebraMap F _ β.1)))
        (fun v => m v (hermScal (Fv F v) σ (algebraMap F _ β.1))) := hκ β.1 β.2
    obtain ⟨-, e⟩ := GlobalTheory.T.euler_product_measure_integral F E σ hcm d b 1 2 _ κ _ _ hEu (fun Y => ENNReal.ofReal (φ (dil θ ε Y))) A
      (hφc.comp (hdil ε)).measurable.ennreal_ofReal (fun v => (hloc v).2.1) (fun v => (hloc v).2.2 _) hcof
    rw [e, mul_assoc]
  simp only [key] at hLt
  have h1 := ENNReal.Tendsto.const_mul (a := (κ : ℝ≥0∞)) hRt (Or.inr ENNReal.coe_ne_top)
  have h2 : (vol b li lam S φ A) = (κ : ℝ≥0∞) * vol b li lam S φ A :=
    tendsto_nhds_unique hLt (h1.congr fun ε => mul_left_comm _ _ _)
  have h3 : (κ : ℝ≥0∞) = 1 := by
    have h4 : (κ : ℝ≥0∞) * vol b li lam S φ A = 1 * vol b li lam S φ A := by rw [one_mul]; exact h2.symm
    exact (ENNReal.mul_left_inj hv0 hvT).1 h4
  exact_mod_cast h3

end GlobalTheory.CompanionTheory.RgMass

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CountingFormulaStatement
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.counting_formula : TestEx → LSide → RSide → Cnt := by
  first | exact @GlobalTheory.CompanionTheory.RgMass.cnt | exact GlobalTheory.CompanionTheory.RgMass.cnt | (intros; apply GlobalTheory.CompanionTheory.RgMass.cnt <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HsOpIntegralRankOne
noncomputable section

open Finset MeasureTheory Matrix
open scoped InnerProductSpace ComplexOrder

namespace GlobalTheory.CompanionTheory.HsPsProof

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgFd

section General

variable {K V : Type*} [TopologicalSpace K] [T2Space K] [CompactSpace K] [SecondCountableTopology K]
  [MeasurableSpace K] [BorelSpace K] [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  [FiniteDimensional ℂ V] [CompleteSpace V]

theorem hsOp_integral_rank_one (m : Measure K) [IsFiniteMeasure m] {u : K → V} (hu : Continuous u)
    {φ : K → ℝ} (hφ : Continuous φ) {P : K → V →L[ℂ] V} (hPc : Continuous P)
    (hP : ∀ k b, P k b = ⟪u k, b⟫_ℂ • u k) (d : ℝ) :
    hsOp ((d : ℂ) • ∫ k, ((φ k : ℝ) : ℂ) • P k ∂m) =
      d ^ 2 * ∫ p, φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2 ∂(m.prod m) := by
  have hφC : Continuous fun k => ((φ k : ℝ) : ℂ) := Complex.continuous_ofReal.comp hφ
  have hInt : Integrable (fun k => ((φ k : ℝ) : ℂ) • P k) m :=
    (integrableOn_univ).mp ((hφC.smul hPc).continuousOn.integrableOn_compact isCompact_univ)
  set A : V →L[ℂ] V := (d : ℂ) • ∫ k, ((φ k : ℝ) : ℂ) • P k ∂m with hA
  have hkey : ∀ y x : V, ⟪y, A x⟫_ℂ =
      (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, x⟫_ℂ * ⟪y, u k⟫_ℂ) ∂m := by
    intro y x
    have hIx : Integrable (fun k => (((φ k : ℝ) : ℂ) • P k) x) m :=
      (ContinuousLinearMap.apply ℂ V x).integrable_comp hInt
    rw [hA, _root_.smul_apply, inner_smul_right, ContinuousLinearMap.integral_apply hInt,
      ← integral_inner hIx]
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    simp only [_root_.smul_apply, inner_smul_right, hP]
  have hQ : ∀ v : V, ⟪v, A v⟫_ℂ = ((d * ∫ k, φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 ∂m : ℝ) : ℂ) := by
    intro v
    rw [hkey]
    have : ∀ k, ((φ k : ℝ) : ℂ) * (⟪u k, v⟫_ℂ * ⟪v, u k⟫_ℂ) =
        ((φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro k
      rw [← inner_conj_symm (u k) v, Complex.conj_mul']
      push_cast; ring
    simp_rw [this]
    rw [integral_complex_ofReal]
    push_cast; ring
  have hQ' : ∀ v : V, ⟪A v, v⟫_ℂ = ((d * ∫ k, φ k * ‖⟪v, u k⟫_ℂ‖ ^ 2 ∂m : ℝ) : ℂ) := by
    intro v
    rw [← inner_conj_symm, hQ, Complex.conj_ofReal]
  set b := stdOrthonormalBasis ℂ V with hb
  have hsum : ∀ v : V, ∑ i, ⟪v, b i⟫_ℂ * ⟪A (b i), v⟫_ℂ = ⟪A v, v⟫_ℂ := by
    intro v
    simp_rw [← ContinuousLinearMap.adjoint_inner_right]
    rw [b.sum_inner_mul_inner]
  have hterm : ∀ i, ((‖A (b i)‖ ^ 2 : ℝ) : ℂ) =
      (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m := by
    intro i
    rw [← hkey, inner_self_eq_norm_sq_to_K]
    push_cast; rfl
  have hintg : ∀ i ∈ (Finset.univ : Finset _), Integrable
      (fun k => ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ)) m := by
    intro i _
    have hc : Continuous fun k => ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) :=
      hφC.mul ((hu.inner continuous_const).mul (continuous_const.inner hu))
    exact (integrableOn_univ).mp (hc.continuousOn.integrableOn_compact isCompact_univ)
  have hC : ((hsOp A : ℝ) : ℂ) =
      ((d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m : ℝ) : ℂ) := by
    calc ((hsOp A : ℝ) : ℂ) = ∑ i, ((‖A (b i)‖ ^ 2 : ℝ) : ℂ) := by
          simp only [hsOp, hb]; push_cast; rfl
      _ = ∑ i, (d : ℂ) * ∫ k, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m :=
          sum_congr rfl fun i _ => hterm i
      _ = (d : ℂ) * ∫ k, ∑ i, ((φ k : ℝ) : ℂ) * (⟪u k, b i⟫_ℂ * ⟪A (b i), u k⟫_ℂ) ∂m := by
          rw [← mul_sum, integral_finsetSum _ hintg]
      _ = (d : ℂ) * ∫ k, ((φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) : ℝ) : ℂ) ∂m := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
          simp only []
          rw [← mul_sum, hsum, hQ']
          push_cast; rfl
      _ = ((d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m : ℝ) : ℂ) := by
          rw [integral_complex_ofReal]
          push_cast; rfl
  have hR : hsOp A = d * ∫ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) ∂m := by
    exact_mod_cast hC
  have hF : Continuous fun p : K × K => φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2 :=
    ((hφ.comp continuous_fst).mul (hφ.comp continuous_snd)).mul
      (((hu.comp continuous_fst).inner (hu.comp continuous_snd)).norm.pow 2)
  have hFi : Integrable (fun p : K × K => φ p.1 * φ p.2 * ‖⟪u p.1, u p.2⟫_ℂ‖ ^ 2) (m.prod m) :=
    (integrableOn_univ).mp (hF.continuousOn.integrableOn_compact isCompact_univ)
  rw [hR, integral_prod _ hFi]
  have e1 : ∀ k, ∫ k', φ k * φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m =
      φ k * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m := by
    intro k
    rw [← integral_const_mul]
    simp only [mul_assoc]
  have e2 : ∀ k, φ k * (d * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) =
      d * (φ k * ∫ k', φ k' * ‖⟪u k, u k'⟫_ℂ‖ ^ 2 ∂m) := fun k => by ring
  simp_rw [e1, e2]
  rw [integral_const_mul]
  ring

end General

variable {n : ℕ} {ε : Fin n → Bool}

private lemma posDef_conj (k : KG ε) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    (toMK k⁻¹ * x * toMK k).PosDef := by
  rw [toMK_inv]
  refine hx.conjTranspose_mul_mul_same ?_
  intro a b hab
  have h := congrArg (fun y => (toMK k)ᴴ.mulVec y) hab
  simpa only [Matrix.mulVec_mulVec, (toMK_facts k).1, Matrix.one_mulVec] using h

private lemma cont_phiK (μ : Fin n → ℤ) {x : Matrix (Fin n) (Fin n) ℂ} (hx : x.PosDef) :
    Continuous (phiK μ x : KG ε → ℝ) := by
  have hm : Continuous (fun k : KG ε => toMK k) :=
    (continuous_toM ε).comp continuous_subtype_val
  have hz : Continuous (fun k : KG ε => toMK k⁻¹ * x * toMK k) :=
    ((hm.comp continuous_inv).mul continuous_const).mul hm
  refine Complex.continuous_re.comp ?_
  exact (phiM_differentiableOn μ).continuousOn.comp_continuous hz
    (fun k => posSet_subset_omega (posDef_conj k hx))

private lemma cK_mul {Λ : Fin n → ℝ} (T : KType ε Λ) (a b : KG ε) :
    cK T (a⁻¹ * b) = ‖⟪T.op a T.w, T.op b T.w⟫_ℂ‖ := by
  rw [cK, CompactHaarProbability.op_mul, KType_op_inv_eq_adjoint, ContinuousLinearMap.mul_apply,
    ContinuousLinearMap.adjoint_inner_right]

theorem hsPs : HsPs := by
  intro n ε Λ T μ x hx
  have hφc : Continuous (phiK μ x : KG ε → ℝ) := cont_phiK μ hx
  have hφeq : ∀ k : KG ε, PhiM μ (toMK k⁻¹ * x * toMK k) = ((phiK μ x k : ℝ) : ℂ) := fun k =>
    Complex.ext (by simp [phiK]) (by simp [(phiM_posDef μ (posDef_conj k hx)).2])
  have hps : psM T μ x = ((Module.finrank ℂ T.V : ℝ) : ℂ) •
      ∫ k, ((phiK μ x k : ℝ) : ℂ) • (T.op k * projW T * T.op k⁻¹) ∂(dk ε) := by
    unfold psM
    delta dk
    simp_rw [hφeq]
    rw [integral_smul_measure, ENNReal.toReal_inv, ← Complex.coe_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hu : Continuous fun k : KG ε => T.op k T.w :=
    (KType_continuous_op T).clm_apply continuous_const
  have hPc : Continuous fun k : KG ε => T.op k * projW T * T.op k⁻¹ :=
    ((KType_continuous_op T).mul continuous_const).mul ((KType_continuous_op T).comp continuous_inv)
  rw [hps, hsOp_integral_rank_one (dk ε) hu hφc hPc (conj_projection_apply T)]
  congr 1
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hI, cK_mul]

end GlobalTheory.CompanionTheory.HsPsProof
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactExhaustionStatement
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactExhaustionStatement
noncomputable section

open Finset MeasureTheory Matrix

namespace GlobalTheory.CompanionTheory.WordFam

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

variable {n : ℕ} {ε : Fin n → Bool} {lam : Fin n → ℝ} {T : KType ε (lowK ε lam)}
  {Ψ : Matrix (Fin n) (Fin n) ℂ → (T.V →L[ℂ] T.V)}

theorem eword_smooth (hP : IsPsiFor ε lam T Ψ) (v : T.V) :
    ∀ w : List (Fin n × Fin n), IsSmoothL2 ε (Formalism.REAL.Eword ε w (jfun Ψ T.w v))
  | [] => datumFunction_isSmoothL2 hP T.w v
  | p :: w => (eword_smooth hP v w).Eab p.1 p.2

def cD (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) (v : T.V) : smD ε (rreg ε) :=
  ⟨toL2 ε (Formalism.REAL.Eword ε w (jfun Ψ T.w v)), toL2_mem_smD_of_isSmoothL2 (eword_smooth hP v w)⟩

theorem cD_cons (hP : IsPsiFor ε lam T Ψ) (p : Fin n × Fin n) (w : List (Fin n × Fin n)) (v : T.V) :
    cD hP (p :: w) v = smE ε (rreg ε) p.1 p.2 (cD hP w v) :=
  Subtype.ext (rightDerivative_toL2 (eword_smooth hP v w) p.1 p.2).symm

theorem cD_add (hP : IsPsiFor ε lam T Ψ) (u v : T.V) :
    ∀ w : List (Fin n × Fin n), cD hP w (u + v) = cD hP w u + cD hP w v
  | [] => Subtype.ext (datumEmbedding_add hP T.w u v)
  | p :: w => by rw [cD_cons, cD_cons, cD_cons, cD_add hP u v w, map_add (f := _)]

theorem cD_smul (hP : IsPsiFor ε lam T Ψ) (c : ℂ) (v : T.V) :
    ∀ w : List (Fin n × Fin n), cD hP w (c • v) = c • cD hP w v
  | [] => Subtype.ext (datumEmbedding_smul hP T.w c v)
  | p :: w => by rw [cD_cons, cD_cons, cD_smul hP c v w, map_smul]

theorem cD_zero (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) : cD hP w (0 : T.V) = 0 := by
  simpa using cD_smul hP (0 : ℂ) (0 : T.V) w

theorem actL_eq (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a : AS T m) :
    actL T Ψ a = ∑ x, (cD hP (ofW x) (a x) : L2 ε) := by
  have h := toL2_finset_sum_of_memLp (ε := ε) univ
    (fun x : Wd n m => Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (a x)))
    (fun x => (eword_smooth hP (a x) (ofW x)).2 [])
  have e : actF T Ψ a = fun g => ∑ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (a x)) g := by
    funext g
    exact Finset.sum_apply _ _ _
  unfold actL
  rw [e]
  exact h

theorem ofW_inj {m : ℕ} {x y : Wd n m} (h : ofW x = ofW y) : x = y := by
  obtain ⟨⟨l, hl⟩, w⟩ := x
  obtain ⟨⟨l', hl'⟩, w'⟩ := y
  have hlen : l = l' := by simpa [ofW] using congrArg List.length h
  subst hlen
  have : w = w' := List.ofFn_injective h
  subst this
  rfl


open Classical in
def sgl (m : ℕ) (w : List (Fin n × Fin n)) (v : T.V) : AS T m := fun y => if ofW y = w then v else 0

theorem actL_sgl (hP : IsPsiFor ε lam T Ψ) {m : ℕ} {w : List (Fin n × Fin n)} (h : w.length ≤ m) (v : T.V) :
    actL T Ψ (sgl m w v) = (cD hP w v : L2 ε) := by
  have hx0 : ofW (⟨⟨w.length, Nat.lt_succ_of_le h⟩, w.get⟩ : Wd n m) = w := List.ofFn_get w
  rw [actL_eq hP, Finset.sum_eq_single (⟨⟨w.length, Nat.lt_succ_of_le h⟩, w.get⟩ : Wd n m)]
  · simp only [sgl, hx0, if_true]
  · intro y _ hy
    have hne : ofW y ≠ w := fun e => hy (ofW_inj (e.trans hx0.symm))
    simp only [sgl, if_neg hne, cD_zero]
    rfl
  · intro hn
    exact absurd (Finset.mem_univ _) hn

def actLin (hP : IsPsiFor ε lam T Ψ) (m : ℕ) : AS T m →ₗ[ℂ] L2 ε where
  toFun := actL T Ψ
  map_add' a b := by
    simp only [actL_eq hP, Pi.add_apply, cD_add, Submodule.coe_add, Finset.sum_add_distrib]
  map_smul' c a := by
    simp only [actL_eq hP, Pi.smul_apply, cD_smul, Submodule.coe_smul, Finset.smul_sum, RingHom.id_apply]

theorem actLin_apply (hP : IsPsiFor ε lam T Ψ) {m : ℕ} (a : AS T m) : actLin hP m a = actL T Ψ a := rfl

theorem pad (hP : IsPsiFor ε lam T Ψ) {m m' : ℕ} (h : m ≤ m') (a : AS T m) :
    ∃ a' : AS T m', actL T Ψ a' = actL T Ψ a := by
  refine ⟨∑ x : Wd n m, sgl m' (ofW x) (a x), ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← actLin_apply hP, map_sum, actL_eq hP a]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [actLin_apply, actL_sgl hP]
  have : (ofW x).length = x.1 := by simp [ofW]
  have h2 := x.1.2
  omega

def exS (hP : IsPsiFor ε lam T Ψ) : Submodule ℂ (smD ε (rreg ε)) where
  carrier := {x | ∃ (m : ℕ) (a : AS T m), (x : L2 ε) = actL T Ψ a}
  add_mem' := by
    rintro x y ⟨m, a, ha⟩ ⟨m', b, hb⟩
    obtain ⟨a', ea⟩ := pad hP (le_max_left m m') a
    obtain ⟨b', eb⟩ := pad hP (le_max_right m m') b
    refine ⟨_, a' + b', ?_⟩
    rw [Submodule.coe_add, ha, hb, ← ea, ← eb]
    exact ((actLin hP _).map_add a' b').symm
  zero_mem' := ⟨0, 0, ((actLin hP 0).map_zero).symm⟩
  smul_mem' := by
    rintro c x ⟨m, a, ha⟩
    refine ⟨m, c • a, ?_⟩
    rw [Submodule.coe_smul, ha]
    exact ((actLin hP m).map_smul c a).symm

theorem cD_mem_exS (hP : IsPsiFor ε lam T Ψ) (w : List (Fin n × Fin n)) (v : T.V) : cD hP w v ∈ exS hP :=
  ⟨w.length, sgl _ w v, (actL_sgl hP le_rfl v).symm⟩

theorem eq_sum (hP : IsPsiFor ε lam T Ψ) {x : smD ε (rreg ε)} {m : ℕ} {a : AS T m}
    (h : (x : L2 ε) = actL T Ψ a) : x = ∑ y, cD hP (ofW y) (a y) :=
  Subtype.ext (by rw [h, actL_eq hP, Submodule.coe_sum])

theorem genSub_le_exS (hP : IsPsiFor ε lam T Ψ) :
    genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) ≤ exS hP := by
  refine sInf_le ⟨fun x hx => ?_, fun a b x hx => ?_⟩
  · obtain ⟨v, hv⟩ := (mem_datumV_iff hP T.w x).1 hx
    have : x = cD hP [] v := Subtype.ext hv
    rw [this]
    exact cD_mem_exS hP [] v
  · obtain ⟨m, f, hf⟩ := hx
    set_option synthInstance.maxHeartbeats 100000 in
      rw [eq_sum hP hf, map_sum]
    refine Submodule.sum_mem _ fun y _ => ?_
    have := cD_cons hP (a, b) (ofW y) (f y)
    simp only at this
    rw [← this]
    exact cD_mem_exS hP _ _

theorem cD_mem_genSub (hP : IsPsiFor ε lam T Ψ) (v : T.V) (w : List (Fin n × Fin n)) :
    cD hP w v ∈ genSub (smE ε (rreg ε)) (datumV ε Ψ T.w) := by
  refine (Submodule.mem_sInf).2 fun N hN => ?_
  induction w with
  | nil => exact hN.1 ((mem_datumV_iff hP T.w _).2 ⟨v, rfl⟩)
  | cons p w ih =>
    rw [cD_cons]
    exact hN.2 _ _ _ ih

theorem exhaust : Exhaust := by
  intro n ε lam T Ψ hP
  refine ⟨fun x hx => genSub_le_exS hP hx, fun m m' h a => pad hP h a, fun m a => ?_⟩
  refine ⟨∑ x, cD hP (ofW x) (a x),
    Submodule.sum_mem _ fun x _ => cD_mem_genSub hP _ _, ?_⟩
  rw [actL_eq hP]
  simp only [Submodule.subtype_apply, Submodule.coe_sum]

end GlobalTheory.CompanionTheory.WordFam
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactExhaustionStatementStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.compact_exhaustion_statement : PositivityTheory.RgDs.K.Exhaust := by
  first | exact @GlobalTheory.CompanionTheory.WordFam.exhaust | exact GlobalTheory.CompanionTheory.WordFam.exhaust | (intros; apply GlobalTheory.CompanionTheory.WordFam.exhaust <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsAdicCompleteOfEquiv
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatCHyp

theorem isAdicComplete_of_equiv {Q R : Type*} [CommRing Q] [CommRing R] (e : Q ≃+* R) (a : Q)
    (h : IsAdicComplete (Ideal.span {e a}) R) : IsAdicComplete (Ideal.span {a}) Q := by
  have hmem : ∀ (n : ℕ) (x y : Q),
      x ≡ y [SMOD (Ideal.span {a} ^ n • ⊤ : Submodule Q Q)] ↔
        e x ≡ e y [SMOD (Ideal.span {e a} ^ n • ⊤ : Submodule R R)] := by
    intro n x y
    rw [SModEq.sub_mem, SModEq.sub_mem, smul_eq_mul, smul_eq_mul, Ideal.mul_top, Ideal.mul_top,
      Ideal.span_singleton_pow, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
      Ideal.mem_span_singleton, ← map_pow, ← map_sub]
    exact (map_dvd_iff e).symm
  refine { haus' := ?_, prec' := ?_ }
  · intro x hx
    have h0 : e x = 0 := by
      refine h.toIsHausdorff.haus' (e x) fun n => ?_
      have := (hmem n x 0).1 (hx n)
      rwa [map_zero] at this
    exact (map_eq_zero_iff e e.injective).1 h0
  · intro f hf
    obtain ⟨L, hL⟩ := h.toIsPrecomplete.prec' (fun n => e (f n))
      (fun {m n} hmn => (hmem m _ _).1 (hf hmn))
    refine ⟨e.symm L, fun n => (hmem n _ _).2 ?_⟩
    rw [RingEquiv.apply_symm_apply]
    exact hL n

variable (l : ℕ) [Fact l.Prime]

def eQ : (Ainf l ⧸ Ideal.span {xi0 l}) ≃+* OC l :=
  (Ideal.quotEquivOfEq (ker_theta0 (l := l)).symm).trans
    (RingHom.quotientKerEquivOfSurjective (IsPerfectoidField.surjective_fontaineTheta (K := ℂ_[l]) l))

theorem eQ_natCast (n : ℕ) : eQ l (n : Ainf l ⧸ Ideal.span {xi0 l}) = (n : OC l) := map_natCast _ n

theorem norm_l_lt_one : ‖((l : OC l) : ℂ_[l])‖ < 1 :=
  IsPerfectoidField.norm_natCast_integer_lt_one (K := ℂ_[l]) l

theorem l_ne_zero : (l : OC l) ≠ 0 := by
  intro h
  have h1 : ((l : OC l) : ℂ_[l]) = (l : ℂ_[l]) := by simp
  rw [h] at h1
  exact (Nat.cast_ne_zero (R := ℂ_[l])).2 (Fact.out : l.Prime).ne_zero (by simpa using h1.symm)

theorem dvd_pow_l {x : OC l} (hx : x ≠ 0) : ∃ n : ℕ, x ∣ (l : OC l) ^ n := by
  have hx0 : (x : ℂ_[l]) ≠ 0 := fun h => hx (Subtype.ext h)
  have hxp : 0 < ‖(x : ℂ_[l])‖ := norm_pos_iff.2 hx0
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hxp (norm_l_lt_one l)
  refine ⟨n, ⟨((l : OC l) : ℂ_[l]) ^ n / x, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div, norm_pow]
    exact div_le_one_of_le₀ hn.le hxp.le
  · simp [mul_div_cancel₀ _ hx0]

theorem dvd_total_OC (x y : OC l) : x ∣ y ∨ y ∣ x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact Or.inr (dvd_zero y)
  have hx0 : (x : ℂ_[l]) ≠ 0 := fun h => hx (Subtype.ext h)
  rcases le_total ‖(y : ℂ_[l])‖ ‖(x : ℂ_[l])‖ with h | h
  · refine Or.inl ⟨⟨(y : ℂ_[l]) / x, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · simp [mul_div_cancel₀ _ hx0]
  · have hy : y ≠ 0 := by
      rintro rfl
      exact hx0 (norm_eq_zero.1 (le_antisymm (by simpa using h) (norm_nonneg _)))
    have hy0 : (y : ℂ_[l]) ≠ 0 := fun h => hy (Subtype.ext h)
    refine Or.inr ⟨⟨(x : ℂ_[l]) / y, mem_normInteger.2 ?_⟩, Subtype.ext ?_⟩
    · rw [norm_div]; exact div_le_one_of_le₀ h (norm_nonneg _)
    · simp [mul_div_cancel₀ _ hy0]

theorem unit_ainf (n : ℕ) (hn : n ≠ 0) : ∃ (k : ℕ) (u : Ainf l), (n : Ainf l) * u = (l : Ainf l) ^ k := by
  have h0 : (n : ℤ_[l]) ≠ 0 := by exact_mod_cast hn
  refine ⟨(n : ℤ_[l]).valuation, IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l
    (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]), ?_⟩
  have h1 : (n : ℤ_[l]) * (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) =
      (l : ℤ_[l]) ^ (n : ℤ_[l]).valuation := by
    have e2 := congrArg (· * (((PadicInt.unitCoeff h0)⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) (PadicInt.unitCoeff_spec h0)
    refine e2.trans ?_
    change ((PadicInt.unitCoeff h0 : ℤ_[l]ˣ) : ℤ_[l]) * _ * _ = _
    rw [mul_comm ((PadicInt.unitCoeff h0 : ℤ_[l]ˣ) : ℤ_[l]), mul_assoc, Units.mul_inv, mul_one]
  have h2 := congrArg (IsPerfectoidField.padicIntToWitt (K := ℂ_[l]) l) h1
  simpa only [map_mul, map_pow, map_natCast] using h2

abbrev xiB : BdRp l := wittToBDeRhamPlus (normInteger ℂ_[l]) l (xi0 l)

theorem span_xiB : Ideal.span {xiB l} = Ideal.span {tBdR l} := by
  rw [← IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))]
  exact maximalIdeal_eq_span_tBdR

theorem xi_dvd_fontaine_t : xiB l ∣ tBdR l :=
  Ideal.mem_span_singleton.1 ((span_xiB l).symm ▸ Ideal.mem_span_singleton_self _)

theorem t_dvd_xiB : tBdR l ∣ xiB l :=
  Ideal.mem_span_singleton.1 ((span_xiB l) ▸ Ideal.mem_span_singleton_self _)

theorem xiB_ne_zero : xiB l ≠ 0 :=
  (IsPerfectoidField.irreducible_wittToBDeRhamPlus (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))).ne_zero

theorem nil_k (k : ℕ) : fk l k (xi0 l) ^ k = 0 := by
  change Ideal.Quotient.mk _ (xiB l) ^ k = 0
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.2
    (Ideal.mem_span_singleton.2 (pow_dvd_pow_of_dvd (t_dvd_xiB l) k))

theorem dvd_of_witt_mem {a : Ainf l} (h : xiB l ∣ wittToBDeRhamPlus (normInteger ℂ_[l]) l a) : xi0 l ∣ a := by
  have h1 : wittToBDeRhamPlus (normInteger ℂ_[l]) l a ∈
      IsLocalRing.maximalIdeal (BDeRhamPlus (normInteger ℂ_[l]) l) := by
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus_eq_span (K := ℂ_[l]) (p := l) (ker_theta0 (l := l))]
    exact Ideal.mem_span_singleton.2 h
  rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus (K := ℂ_[l]) (p := l), RingHom.mem_ker,
    IsPerfectoidField.thetaBDeRhamPlusField_wittToBDeRhamPlus] at h1
  have h2 : a ∈ RingHom.ker (theta0 l) := Subtype.ext h1
  rw [ker_theta0] at h2
  exact Ideal.mem_span_singleton.1 h2

theorem gr_k (k i : ℕ) (hi : i < k) (a : Ainf l) (b : Bk l k)
    (h : fk l k a * fk l k (xi0 l) ^ i = fk l k (xi0 l) ^ (i + 1) * b) : xi0 l ∣ a := by
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  apply dvd_of_witt_mem
  set w := wittToBDeRhamPlus (normInteger ℂ_[l]) l a with hw
  have h1 : Ideal.Quotient.mk (Ideal.span {tBdR l ^ k}) (w * xiB l ^ i) =
      Ideal.Quotient.mk _ (xiB l ^ (i + 1) * b) := by
    rw [map_mul, map_mul, map_pow, map_pow]
    exact h
  have h2 := Ideal.mem_span_singleton.1 (Ideal.Quotient.eq.1 h1)
  have h3 : xiB l ^ (i + 1) ∣ tBdR l ^ k :=
    (pow_dvd_pow _ hi).trans (pow_dvd_pow_of_dvd (xi_dvd_fontaine_t l) k)
  have h4 : xiB l ^ (i + 1) ∣ w * xiB l ^ i := by
    obtain ⟨c, hc⟩ := h3.trans h2
    exact ⟨c + b, by linear_combination hc⟩
  rw [pow_succ', mul_comm w, mul_comm (xiB l)] at h4
  exact (mul_dvd_mul_iff_left (pow_ne_zero i (xiB_ne_zero l))).1 h4

theorem hyp_k (l : ℕ) [Fact l.Prime] (k : ℕ) (hk : 1 ≤ k) : Lat.Hyp (Lat.fk l k) (xi0 l) l k := by
  have hl : eQ l (l : Ainf l ⧸ Ideal.span {xi0 l}) = (l : OC l) := eQ_natCast l l
  refine
    { one_le := hk
      nil := nil_k l k
      gr := fun i hi a b h => gr_k l k i hi a b h
      dom := (eQ l).toMulEquiv.isDomain _
      val := fun x y => ?_
      dv := fun x hx => ?_
      l0 := fun h => ?_
      cpl := ?_
      unit := unit_ainf l }
  · rcases dvd_total_OC l (eQ l x) (eQ l y) with h | h
    · exact Or.inl ((map_dvd_iff (eQ l)).1 h)
    · exact Or.inr ((map_dvd_iff (eQ l)).1 h)
  · obtain ⟨n, hn⟩ := dvd_pow_l l (x := eQ l x) ((map_ne_zero_iff _ (eQ l).injective).2 hx)
    refine ⟨n, (map_dvd_iff (eQ l)).1 ?_⟩
    rwa [map_pow, hl]
  · apply l_ne_zero l
    rw [← hl, h, map_zero]
  · refine isAdicComplete_of_equiv (eQ l) _ ?_
    rw [hl]
    exact IsPerfectoidField.isAdicComplete (K := ℂ_[l]) l

end GlobalTheory.CompanionTheory.LatCHyp
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuGaloisCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuGaloisCompat
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.MuGal

theorem mu_gal {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (t : Mid.HM r M n j) :
    B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j (Mid.mu r M n j hT t) = Mid.mu r M n j hT (galM r M σ hσ n j t) := by
  unfold B.galHc Mid.mu galM B.galMorC Mid.muMor galT'
  symm
  exact cr_square
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl)
    (Mid.mIn r M n hT)
    (Mid.mIn r M n hT)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (B.gal_κb (okToOC l K) σ (galOC_okToOC σ) true n)) fun _ _ _ => rfl)
    (galBase_cris σ n) (fun _ => rfl) (fun _ => rfl) (galBase_cris σ n) (fun _ => rfl)
    (fun _ _ => rfl) j t

end GlobalTheory.CompanionTheory.MuGal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuGaloisCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_mu_galois_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (t : Mid.HM r M n j), B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j (Mid.mu r M n j hT t) = Mid.mu r M n j hT (galM r M σ hσ n j t) := by
  first | exact @GlobalTheory.CompanionTheory.MuGal.mu_gal | exact GlobalTheory.CompanionTheory.MuGal.mu_gal | (intros; apply GlobalTheory.CompanionTheory.MuGal.mu_gal <;> assumption)
end
end
