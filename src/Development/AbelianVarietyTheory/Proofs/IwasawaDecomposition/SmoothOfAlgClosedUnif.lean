module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedEffectiveCartierDivisorPullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReducedCartierDivisorOfSncClosed
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GeneratorCorrespondencePullback
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocallyHolomorphicPeriodsFamily
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftThetaMapOrthogonalKernelEqRationalSpan
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsUnique

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjectiveBundlePointsOfRationalModel
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjectiveBundlePointsOfRationalModel
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle.ProjPts

open GlobalTheory.ZH.RatModel GlobalTheory.Points

variable {F Ω Ω' : Type} [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
  {M : RatModel F Ω} {M' : RatModel F Ω'} {φ : Ω →ₐ[F] Ω'} {f : M'.Z ⟶ M.Z}

theorem exists_open_span_le {J : Type} [Fintype J] (a b : J → J → Ω) {z : M.Z}
    (h : Submodule.span (M.O z) (Set.range a) ≤ Submodule.span (M.O z) (Set.range b)) :
    ∃ V : M.Z.Opens, z ∈ V ∧ ∀ w ∈ V, Submodule.span (M.O w) (Set.range a) ≤ Submodule.span (M.O w) (Set.range b) := by
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun _).1 (h (Submodule.subset_span ⟨i, rfl⟩))
  refine ⟨⟨⋂ i, ⋂ l, {w | (c i l : Ω) ∈ M.O w}, isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun l =>
    M.isOpen_setOf_mem_O _⟩, Set.mem_iInter.2 fun i => Set.mem_iInter.2 fun l => (c i l).2, fun w hw => ?_⟩
  rw [Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact (Submodule.mem_span_range_iff_exists_fun _).2
    ⟨fun l => ⟨c i l, Set.mem_iInter.1 (Set.mem_iInter.1 hw i) l⟩, hc i⟩

theorem exists_affine_basis {J : Type} [Fintype J] [DecidableEq J] (EE : M.Lat J) (B : Matrix J J Ω) {z : M.Z}
    (h : EE.E z = Submodule.span (M.O z) (Set.range B)) :
    ∃ W : M.Z.Opens, IsAffineOpen W ∧ z ∈ W ∧ ∀ w ∈ W, EE.E w = Submodule.span (M.O w) (Set.range B) := by
  obtain ⟨U, b, hz, -, H⟩ := EE.loc z
  have e := (H z hz).symm.trans h
  obtain ⟨V₁, h₁, H₁⟩ := exists_open_span_le b B e.le
  obtain ⟨V₂, h₂, H₂⟩ := exists_open_span_le B b e.ge
  obtain ⟨W, hW, hzW, hle⟩ := exists_isAffineOpen_mem_and_subset (U := U ⊓ V₁ ⊓ V₂) (x := z) ⟨⟨hz, h₁⟩, h₂⟩
  exact ⟨W, hW, hzW, fun w hw => (H w (hle hw).1.1).trans (le_antisymm (H₁ w (hle hw).1.2) (H₂ w (hle hw).2))⟩

variable {K : Type} [Field K]

theorem range_subset {p : Sp K ⟶ M.Z} {U : M.Z.Opens} (h : p (IsLocalRing.closedPoint K) ∈ U) :
    Set.range p ⊆ U := by
  rw [range_eq_singleton p (IsLocalRing.closedPoint K), Set.singleton_subset_iff]
  exact h

theorem exists_point {U : M.Z.Opens} (hU : IsAffineOpen U) (hne : (U : Set M.Z).Nonempty)
    (ψ : M.ringOn U →+* K) :
    ∃ p : Sp K ⟶ M.Z, p (IsLocalRing.closedPoint K) ∈ U ∧ ∀ a : M.ringOn U, M.val p a = ψ a := by
  let χ : Γ(M.Z, U) ⟶ CommRingCat.of K := CommRingCat.ofHom (ψ.comp (M.sectionsEquiv U hne).toRingHom)
  have h := le_preimage_specMap_fromSpec hU χ
  refine ⟨Spec.map χ ≫ hU.fromSpec, (le_preimage_iff _ _).1 h, fun a => ?_⟩
  obtain ⟨a, rfl⟩ := (M.sectionsEquiv U hne).surjective a
  rw [coe_sectionsEquiv, val_valF ((top_le_preimage_iff _ _).1 h), valF_eq_valR, valR_eq _ _ h,
    valMap_specMap_fromSpec]
  rfl

theorem ext_of_val {U : M.Z.Opens} (hU : IsAffineOpen U) {p q : Sp K ⟶ M.Z}
    (hp : p (IsLocalRing.closedPoint K) ∈ U) (hq : q (IsLocalRing.closedPoint K) ∈ U)
    (H : ∀ a ∈ M.ringOn U, M.val p a = M.val q a) : p = q := by
  refine ext_of_valR hU ((le_preimage_iff _ _).2 hp) ((le_preimage_iff _ _).2 hq) fun g => ?_
  have := H _ ((mem_ringOn_iff_exists ⟨_, hp⟩).2 ⟨g, rfl⟩)
  rwa [val_valF (range_subset hp), val_valF (range_subset hq)] at this

theorem val_eq_of_adjoin {U : M.Z.Opens} {p q : Sp K ⟶ M.Z}
    (hp : p (IsLocalRing.closedPoint K) ∈ U) (hq : q (IsLocalRing.closedPoint K) ∈ U) {T : Set Ω}
    (hT : M.ringOn U = Algebra.adjoin F T) (h0 : ∀ a, M.val p (algebraMap F Ω a) = M.val q (algebraMap F Ω a))
    (h1 : ∀ a ∈ T, M.val p a = M.val q a) : ∀ a ∈ M.ringOn U, M.val p a = M.val q a := by
  have sp := specializes_of_range_eq (range_eq_singleton p (IsLocalRing.closedPoint K))
  have sq := specializes_of_range_eq (range_eq_singleton q (IsLocalRing.closedPoint K))
  intro a ha
  rw [hT] at ha
  induction ha using Algebra.adjoin_induction with
  | mem x hx => exact h1 x hx
  | algebraMap r => exact h0 r
  | add x y hx hy ex ey =>
    rw [← hT] at hx hy
    rw [val_add sp (ringOn_le_O hp hx) (ringOn_le_O hp hy), val_add sq (ringOn_le_O hq hx) (ringOn_le_O hq hy), ex, ey]
  | mul x y hx hy ex ey =>
    rw [← hT] at hx hy
    rw [val_mul sp (ringOn_le_O hp hx) (ringOn_le_O hp hy), val_mul sq (ringOn_le_O hq hx) (ringOn_le_O hq hy), ex, ey]

theorem exists_ringHom (R : Subalgebra F Ω) {σ : Type} (t : σ → Ω')
    (ht : ∀ P : MvPolynomial σ Ω, MvPolynomial.eval₂ (φ : Ω →+* Ω') t P = 0 → P = 0) (S : Subalgebra F Ω')
    {T : Set Ω'} (hS : S = Algebra.adjoin F (φ '' (R : Set Ω) ∪ T)) (hT : ∀ y ∈ T, y = 1 ∨ y ∈ Set.range t)
    (v : R →+* K) (c : σ → K) :
    ∃ ψ : S →+* K, (∀ (r : R) (h : φ r ∈ S), ψ ⟨φ r, h⟩ = v r) ∧ ∀ j (h : t j ∈ S), ψ ⟨t j, h⟩ = c j := by
  let g : MvPolynomial σ R →+* Ω' := MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp R.val.toRingHom) t
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro P hP
    have := ht (MvPolynomial.map R.val.toRingHom P) (by rw [MvPolynomial.eval₂_map]; exact hP)
    exact MvPolynomial.map_injective R.val.toRingHom Subtype.val_injective (this.trans (map_zero _).symm)
  have hC : ∀ r : R, g (MvPolynomial.C r) = φ r := fun r => MvPolynomial.eval₂Hom_C _ _ r
  have hX : ∀ j, g (MvPolynomial.X j) = t j := fun j => MvPolynomial.eval₂Hom_X' _ _ j
  have hle : ∀ y ∈ S, y ∈ g.range := by
    intro y hy
    rw [hS] at hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      rcases hx with ⟨r, hr, rfl⟩ | hx
      · exact ⟨_, hC ⟨r, hr⟩⟩
      · rcases hT x hx with rfl | ⟨j, rfl⟩
        · exact one_mem _
        · exact ⟨_, hX j⟩
    | algebraMap r => exact ⟨_, (hC (algebraMap F R r)).trans (φ.commutes r)⟩
    | add x y _ _ ex ey => exact add_mem ex ey
    | mul x y _ _ ex ey => exact mul_mem ex ey
  let e : MvPolynomial σ R ≃+* g.range := RingEquiv.ofBijective g.rangeRestrict
    ⟨fun _ _ h => hg (congrArg Subtype.val h), g.rangeRestrict_surjective⟩
  let ι : S →+* g.range := S.val.toRingHom.codRestrict g.range fun y => hle y y.2
  have key : ∀ (P : MvPolynomial σ R) (y : S), g P = y → e.symm (ι y) = P := fun P y h =>
    e.symm_apply_eq.2 (Subtype.ext h.symm)
  refine ⟨(MvPolynomial.eval₂Hom v c).comp (e.symm.toRingHom.comp ι), fun r h => ?_, fun j h => ?_⟩
  · exact (congrArg (MvPolynomial.eval₂Hom v c) (key _ ⟨_, h⟩ (hC r))).trans (MvPolynomial.eval₂Hom_C _ _ r)
  · exact (congrArg (MvPolynomial.eval₂Hom v c) (key _ ⟨_, h⟩ (hX j))).trans (MvPolynomial.eval₂Hom_X' _ _ j)

theorem div_of_ne_zero {J : Type} {t : J → Ω} {p : Sp K ⟶ M.Z} {c : J → K} {i k : J} (hi : c i ≠ 0)
    (hk : M.Div t k (p (IsLocalRing.closedPoint K))) (h : ∀ j, c j = c k * M.val p (t j / t k)) :
    M.Div t i (p (IsLocalRing.closedPoint K)) ∧ ∀ j, M.val p (t j / t i) = c j / c i := by
  have hr := range_eq_singleton p (IsLocalRing.closedPoint K)
  have h0 : M.val p (t i / t k) ≠ 0 := right_ne_zero_of_mul (h i ▸ hi)
  have hd : M.Div t i (p (IsLocalRing.closedPoint K)) :=
    (hk.div_iff_isUnit i).2 ((val_ne_zero_iff hr ⟨_, hk.2 i⟩).1 h0)
  refine ⟨hd, fun j => ?_⟩
  have e := val_mul (specializes_of_range_eq hr) (hd.2 j) (hk.2 i)
  rw [div_mul_div_cancel₀ hd.1] at e
  rw [eq_div_iff hi, h j, h i, e]
  ring

theorem projPoints {J : Type} [Fintype J] [DecidableEq J] {EE : M.Lat J} {s : J → Ω'}
    (H : ProjBundle M EE M' φ f s) : ProjPoints M EE M' φ f s := by
  refine ⟨H.hom, fun z' B _ hB => ?_, fun K _ x B hB hE c hc => ?_⟩
  · obtain ⟨W, hW, hz, hE⟩ := exists_affine_basis EE B hB
    exact (H.chart W B hW ⟨_, hz⟩ hE).1 z' hz
  obtain ⟨W, hW, hz, hEW⟩ := exists_affine_basis EE B hE
  obtain ⟨i, hi⟩ := Function.ne_iff.1 hc
  replace hi : c i ≠ 0 := hi
  obtain ⟨hti, hind⟩ := H.gen B hB i
  obtain ⟨U, hU, hUeq, hR⟩ := (H.chart W B hW ⟨_, hz⟩ hEW).2 i hti
  set t := (B.map φ).mulVec s with ht
  have hmem : ∀ z', z' ∈ U ↔ f z' ∈ W ∧ M'.Div t i z' := fun z' => Set.ext_iff.1 hUeq z'
  have hne : (U : Set M'.Z).Nonempty := by
    refine ⟨genericPoint M'.Z, (hmem _).2 ⟨?_, div_genericPoint hti⟩⟩
    rw [← M'.pt_apply (IsLocalRing.closedPoint Ω')]
    have e : (M'.pt ≫ f) (IsLocalRing.closedPoint Ω') ∈ W := by
      rw [H.hom]
      exact M.top_le_preimage_pt ⟨_, hz⟩ (x := spMap φ.toRingHom (IsLocalRing.closedPoint Ω')) trivial
    exact e
  let v : M.ringOn W →+* K := (valHom x _ (range_eq_singleton x (IsLocalRing.closedPoint K))).comp
    (Subalgebra.inclusion (ringOn_le_O hz)).toRingHom
  obtain ⟨ψ, hψ₁, hψ₂⟩ := exists_ringHom (M.ringOn W) _ hind (M'.ringOn U) hR (by
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · exact Or.inl (by rw [hj]; exact div_self hti)
    · exact Or.inr ⟨⟨j, hj⟩, rfl⟩) v fun j => c j.1 / c i
  obtain ⟨p, hp, hv⟩ := exists_point hU hne ψ
  have hφ : ∀ a ∈ M.ringOn W, φ a ∈ M'.ringOn U := fun a ha =>
    hR ▸ Algebra.subset_adjoin (Or.inl ⟨a, ha, rfl⟩)
  have hcomp : ∀ q : Sp K ⟶ M'.Z, q (IsLocalRing.closedPoint K) ∈ U → ∀ a ∈ M.ringOn W,
      M.val (q ≫ f) a = M'.val q (φ a) := fun q hq a ha =>
    H.hom.val_comp q _ (ringOn_le_O ((hmem _).1 hq).1 ha)
  have hpf : p ≫ f = x := by
    refine ext_of_val hW ((hmem _).1 hp).1 hz fun a ha => ?_
    exact (hcomp p hp a ha).trans ((hv ⟨_, hφ a ha⟩).trans (hψ₁ ⟨a, ha⟩ _))
  have hrat : ∀ j, M'.val p (t j / t i) = c j / c i := fun j => by
    by_cases hj : j = i
    · rw [hj, div_self hti, div_self hi, RatModel.val_one]
    · have hm : t j / t i ∈ M'.ringOn U := hR ▸ Algebra.subset_adjoin (Or.inr ⟨j, rfl⟩)
      exact (hv ⟨_, hm⟩).trans (hψ₂ ⟨j, hj⟩ hm)
  refine ⟨p, ⟨hpf, i, ((hmem _).1 hp).2, fun j => by rw [hrat, mul_div_cancel₀ _ hi]⟩, ?_⟩
  rintro q ⟨hqf, k, hk, hq⟩
  obtain ⟨hd, hqr⟩ := div_of_ne_zero hi hk hq
  have hqU : q (IsLocalRing.closedPoint K) ∈ U := (hmem _).2 ⟨by rw [← hqf] at hz; exact hz, hd⟩
  have hb : ∀ a ∈ M.ringOn W, M'.val q (φ a) = M'.val p (φ a) := fun a ha => by
    rw [← hcomp q hqU a ha, ← hcomp p hp a ha, hqf, hpf]
  refine ext_of_val hU hqU hp (val_eq_of_adjoin hqU hp hR (fun a => ?_) ?_)
  · rw [← φ.commutes]
    exact hb _ (Subalgebra.algebraMap_mem _ a)
  · rintro _ (⟨a, ha, rfl⟩ | ⟨j, rfl⟩)
    · exact hb a ha
    · exact (hqr j).trans (hrat j).symm

end GlobalTheory.FlagBundle.ProjPts

theorem GlobalTheory.FlagBundle.projPoints_of_projBundle : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω']
    [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J]
    [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → ProjPoints M EE M' φ f s :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H => GlobalTheory.FlagBundle.ProjPts.projPoints H

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ProjectiveBundlePointsOfRationalModelStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.projective_bundle_points_of_rational_model : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (J : Type) [Fintype J] [DecidableEq J] (EE : M.Lat J) (s : J → Ω'), ProjBundle M EE M' φ f s → ProjPoints M EE M' φ f s := by
  first | exact @GlobalTheory.FlagBundle.projPoints_of_projBundle | exact GlobalTheory.FlagBundle.projPoints_of_projBundle | (intros; apply GlobalTheory.FlagBundle.projPoints_of_projBundle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeDualBasisQuotientFrameBlock
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeDualBasisQuotientFrameBlock
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

noncomputable section

namespace GlobalTheory.FlagBundle.QuotDual

variable {ι : Type} {m k : ι → ℕ} {K : Type} [Field K]

abbrev restBlock (k : ι → ℕ) (τ : ι) (g : Mat m K) : Matrix (Rest m k τ) (Rest m k τ) K :=
  (g τ).submatrix Subtype.val Subtype.val

theorem restBlock_mul {O : Subring K} (τ : ι) (g : Mat m K) {h : Mat m K} (hh : Par k O h) :
    restBlock k τ (g * h) = restBlock k τ g * restBlock k τ h := by
  ext i j
  simp only [Matrix.submatrix_apply, Pi.mul_apply, Matrix.mul_apply]
  rw [← Finset.sum_subtype (Finset.univ.filter fun l : Fin (m τ) => k τ ≤ (l : ℕ)) (by simp)
    (fun l => g τ i.1 l * h τ l j.1)]
  refine (Finset.sum_subset (Finset.filter_subset _ _) fun l _ hl => ?_).symm
  have hl' : (l : ℕ) < k τ := by simpa using hl
  have hj := j.2
  rw [(hh τ).2.2.2 l j.1 hl' (by show (l : ℕ) < j.1; omega), mul_zero]

theorem restBlock_one (τ : ι) : restBlock k τ (1 : Mat m K) = 1 :=
  Matrix.submatrix_one _ Subtype.val_injective

theorem restBlock_inv_mul {O : Subring K} (τ : ι) {g : Mat m K} (hg : Par k O g) :
    restBlock k τ g⁻¹ * restBlock k τ g = 1 := by
  rw [← restBlock_mul τ _ hg, Mat.inv_mul hg.det_ne, restBlock_one]

theorem restBlock_inv {O : Subring K} (τ : ι) {g : Mat m K} (hg : Par k O g) :
    (restBlock k τ g)⁻¹ = restBlock k τ g⁻¹ :=
  Matrix.inv_eq_left_inv (restBlock_inv_mul τ hg)

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω]

theorem span_mul_le {J : Type} [Fintype J] (O : Subalgebra F Ω) (P B : Matrix J J Ω) (hP : ∀ i j, P i j ∈ O) :
    Submodule.span O (Set.range (P * B)) ≤ Submodule.span O (Set.range B) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨i, rfl⟩
  refine (Submodule.mem_span_range_iff_exists_fun _).2 ⟨fun l => ⟨P i l, hP i l⟩, ?_⟩
  ext j
  simp [Matrix.mul_apply, Finset.sum_apply, Subalgebra.smul_def]

variable {M : RatModel F Ω} {S : Fr M m k} {A₀ : Mat m Ω}

theorem par_generic (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A : Mat m Ω} (hA : A ∈ S.S z) :
    Par k (M.O (genericPoint M.Z)).toSubring (A * A₀⁻¹) :=
  (Fr.mem_iff h₀).1 (Fr.mem_genericPoint hA)

theorem det_dualBlock_ne (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A : Mat m Ω} (hA : A ∈ S.S z) :
    (dualBlock k τ A₀ A).det ≠ 0 := by
  have h := par_generic h₀ hA
  have e := congrArg Matrix.det (restBlock_inv_mul τ h)
  rw [Matrix.det_mul, Matrix.det_one] at e
  show ((restBlock k τ (A * A₀⁻¹))⁻¹).transpose.det ≠ 0
  rw [Matrix.det_transpose, restBlock_inv τ h]
  exact left_ne_zero_of_mul_eq_one e

theorem span_dualBlock_le (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A A' : Mat m Ω} (hA : A ∈ S.S z)
    (hA' : A' ∈ S.S z) : Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A')) ≤
      Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  have hg := (Fr.mem_iff hA).1 hA'
  have e : A' * A₀⁻¹ = (A' * A⁻¹) * (A * A₀⁻¹) := by
    rw [← mul_assoc, mul_assoc A', Mat.inv_mul (Fr.det_ne hA), mul_one]
  have e2 : dualBlock k τ A₀ A' = (restBlock k τ (A' * A⁻¹)⁻¹).transpose * dualBlock k τ A₀ A := by
    show ((restBlock k τ (A' * A₀⁻¹))⁻¹).transpose = _ * ((restBlock k τ (A * A₀⁻¹))⁻¹).transpose
    rw [e, restBlock_mul τ _ (par_generic h₀ hA), Matrix.mul_inv_rev, Matrix.transpose_mul, restBlock_inv τ hg]
  rw [e2]
  exact span_mul_le _ _ _ fun i j => (hg.inv τ).1 _ _

theorem span_dualBlock_eq (τ : ι) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) {z : M.Z} {A A' : Mat m Ω} (hA : A ∈ S.S z)
    (hA' : A' ∈ S.S z) : Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A')) =
      Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) :=
  le_antisymm (span_dualBlock_le τ h₀ hA hA') (span_dualBlock_le τ h₀ hA' hA)

theorem exists_lat_dualBlock (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (ι : Type)
    (m k : ι → ℕ) (S : Fr M m k) (τ : ι) (A₀ : Mat m Ω) (h₀ : A₀ ∈ S.S (genericPoint M.Z)) :
    ∃ EE : M.Lat (Rest m k τ), ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  refine ⟨⟨fun z => Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ (S.nonempty z).some)), fun z => ?_⟩,
    fun z A hA => ⟨det_dualBlock_ne τ h₀ hA, span_dualBlock_eq τ h₀ hA (S.nonempty z).some_mem⟩⟩
  obtain ⟨U, A, hz, hA, hU⟩ := S.loc z
  have hm : ∀ z' ∈ U, A ∈ S.S z' := fun z' hz' => (hU z' hz' A).2 (by rw [Mat.mul_inv hA]; exact Par.one)
  exact ⟨U, dualBlock k τ A₀ A, hz, det_dualBlock_ne τ h₀ (hm z hz),
    fun z' hz' => span_dualBlock_eq τ h₀ (hm z' hz') (S.nonempty z').some_mem⟩

end GlobalTheory.FlagBundle.QuotDual
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLatticeDualBasisQuotientFrameBlockStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lattice_dualBasisQuotientFrameBlock : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (ι : Type) (m k : ι → ℕ) (S : Fr M m k) (τ : ι) (A₀ : Mat m Ω), A₀ ∈ S.S (genericPoint M.Z) → ∃ EE : M.Lat (Rest m k τ), ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)) := by
  first | exact @GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock | exact GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock | (intros; apply GlobalTheory.FlagBundle.QuotDual.exists_lat_dualBlock <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreservesRadicalPrincipalIdealsOfAffineSpaceCove
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreservesRadicalPrincipalIdealsOfAffineSpaceCove
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle

namespace GlobalTheory.FlagBundle.AffRad

theorem C_dvd_of_C_dvd_pow {A σ : Type} [CommRing A] {g : A} (hg : ∀ (x : A) (n : ℕ), g ∣ x ^ n → g ∣ x)
    {P : MvPolynomial σ A} {n : ℕ} (h : MvPolynomial.C g ∣ P ^ n) : MvPolynomial.C g ∣ P := by
  have hq : ∀ a : A, Ideal.Quotient.mk (Ideal.span {g}) a = 0 ↔ g ∣ a := fun a => by
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rw [MvPolynomial.C_dvd_iff_map_hom_eq_zero _ g hq] at h ⊢
  rw [map_pow] at h
  have hn := (MvPolynomial.isNilpotent_iff).1 ⟨n, h⟩
  apply MvPolynomial.ext
  intro i
  obtain ⟨k, hk⟩ := hn i
  rw [MvPolynomial.coeff_map] at hk ⊢
  rw [← map_pow, hq] at hk
  change Ideal.Quotient.mk (Ideal.span {g}) (P.coeff i) = 0
  exact (hq _).2 (hg _ _ hk)

theorem exists_div_of_mem_O {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω}
    {V : M.Z.Opens} (hV : IsAffineOpen V) {z : M.Z} (hz : z ∈ V) {x : Ω} (hx : x ∈ M.O z) :
    ∃ a b : Ω, a ∈ M.ringOn V ∧ b ∈ M.ringOn V ∧ b ≠ 0 ∧ b⁻¹ ∈ M.O z ∧ x * b = a := by
  obtain ⟨U, f, hU, rfl⟩ := hx
  have hne : (V : Set M.Z).Nonempty := ⟨z, hz⟩
  obtain ⟨g, hgU, hwg⟩ := hV.exists_basicOpen_le (V := U) ⟨z, hU⟩ hz
  have hg : ((M.Z.basicOpen g : M.Z.Opens) : Set M.Z).Nonempty := ⟨z, hwg⟩
  have := hV.isLocalization_basicOpen g
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj g (resG M.Z hgU f)
  have h1 := congrArg (M.res _ hg) ha
  have h2 : ∀ t : Γ(M.Z, V), M.res _ hg (algebraMap Γ(M.Z, V) Γ(M.Z, M.Z.basicOpen g) t) = M.res V hne t :=
    fun t => M.res_resG (M.Z.basicOpen_le g) hg t
  rw [map_mul, map_pow, h2, h2, RatModel.res_resG, RatModel.res_apply, RatModel.res_apply,
    RatModel.res_apply] at h1
  have hu := (RatModel.isUnit_O_iff _).1 ((RatModel.isUnit_valF_iff hz g).2 hwg)
  refine ⟨_, _, (RatModel.mem_ringOn_iff_exists hne).2 ⟨a, rfl⟩,
    pow_mem ((RatModel.mem_ringOn_iff_exists hne).2 ⟨g, rfl⟩) n, pow_ne_zero _ hu.1, ?_, h1⟩
  rw [← inv_pow]
  exact pow_mem hu.2 n

theorem keepsRad_of_affCover (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ)
    (h : AffCover M M' φ f r) : KeepsRad M M' φ f := by
  rintro z' g ⟨hg0, hgO, hg⟩
  obtain ⟨hf, hc⟩ := h
  obtain ⟨U, W, t, hU, -, hz, hW, hinj, hR⟩ := hc z'
  have hφ0 : φ g ≠ 0 := (map_ne_zero φ).2 hg0
  refine ⟨hφ0, hf.map_mem_O hgO, fun x n hx hxn => ?_⟩
  let A := (M.O (f z')).toSubring
  let ψ : MvPolynomial (Fin r) A →+* Ω' := MvPolynomial.eval₂Hom ((φ : Ω →+* Ω').comp A.subtype) t
  have hψ : Function.Injective ψ := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro P hP
    have := hinj (MvPolynomial.map A.subtype P) (by rw [MvPolynomial.eval₂_map]; exact hP)
    exact (map_eq_zero_iff _ (MvPolynomial.map_injective _ A.subtype_injective)).1 this
  have hO : ∀ P, ψ P ∈ M'.O z' := fun P => by
    induction P using MvPolynomial.induction_on with
    | C a => rw [MvPolynomial.eval₂Hom_C]; exact hf.map_mem_O a.2
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p i hp =>
      rw [map_mul, MvPolynomial.eval₂Hom_X']
      exact mul_mem hp (RatModel.ringOn_le_O hz (hR ▸ Algebra.subset_adjoin (Or.inr ⟨i, rfl⟩)))
  have hS : ∀ y ∈ M'.ringOn U, ∃ P, ψ P = y := by
    intro y hy
    rw [hR] at hy
    induction hy using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨w, hw, rfl⟩ | ⟨i, rfl⟩
      · exact ⟨MvPolynomial.C ⟨w, RatModel.ringOn_le_O (hW z' hz) hw⟩, MvPolynomial.eval₂Hom_C _ _ _⟩
      · exact ⟨MvPolynomial.X i, MvPolynomial.eval₂Hom_X' _ _ _⟩
    | algebraMap c =>
      exact ⟨MvPolynomial.C ⟨algebraMap F Ω c, (M.O (f z')).algebraMap_mem c⟩,
        (MvPolynomial.eval₂Hom_C _ _ _).trans (φ.commutes c)⟩
    | add a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P + Q, map_add _ _ _⟩
    | mul a b _ _ ha hb => obtain ⟨P, rfl⟩ := ha; obtain ⟨Q, rfl⟩ := hb; exact ⟨P * Q, map_mul _ _ _⟩
  have hrad : ∀ (y : A) (k : ℕ), (⟨g, hgO⟩ : A) ∣ y ^ k → (⟨g, hgO⟩ : A) ∣ y := by
    rintro y k ⟨c, hc⟩
    have e : (y : Ω) ^ k = g * c := congrArg Subtype.val hc
    have := hg y k y.2 (by rw [e, mul_div_cancel_left₀ _ hg0]; exact c.2)
    exact ⟨⟨_, this⟩, Subtype.ext (mul_div_cancel₀ _ hg0).symm⟩
  have hC : ψ (MvPolynomial.C ⟨g, hgO⟩) = φ g := MvPolynomial.eval₂Hom_C _ _ _
  obtain ⟨a, b, ha, hb, hb0, hbi, e1⟩ := exists_div_of_mem_O hU hz hx
  obtain ⟨c, d, hc, hd, hd0, hdi, e2⟩ := exists_div_of_mem_O hU hz hxn
  obtain ⟨a, rfl⟩ := hS a ha
  obtain ⟨b, rfl⟩ := hS b hb
  obtain ⟨c, rfl⟩ := hS c hc
  obtain ⟨d, rfl⟩ := hS d hd
  have hdvd : MvPolynomial.C (⟨g, hgO⟩ : A) ∣ (a * d) ^ (n + 1) := by
    refine ⟨c * b ^ n * a * d ^ n, hψ ?_⟩
    simp only [map_mul, map_pow, hC, ← e2]
    rw [← e1]
    field_simp
    ring
  obtain ⟨Q, hQ⟩ := C_dvd_of_C_dvd_pow hrad hdvd
  have e3 := congrArg ψ hQ
  rw [map_mul, map_mul, hC, ← e1] at e3
  have e4 : x / φ g = ψ Q * (ψ b)⁻¹ * (ψ d)⁻¹ := by
    field_simp
    linear_combination e3
  rw [e4]
  exact mul_mem (mul_mem (hO Q) hbi) hdi

end GlobalTheory.FlagBundle.AffRad
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PreservesRadicalPrincipalIdealsOfAffineSpaceCoveStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (r : ℕ), AffCover M M' φ f r → KeepsRad M M' φ f := by
  first | exact @GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover | exact GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover | (intros; apply GlobalTheory.FlagBundle.AffRad.keepsRad_of_affCover <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjectiveBundleOfLatticeIsProjOver
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjectiveBundleOfLatticeIsProjOver
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

section Generic

variable {Ω : Type} [Field Ω] {J : Type} [Fintype J] [DecidableEq J]

def genPoly (Ω : Type) [Field Ω] (j₀ j : J) : MvPolynomial {j // j ≠ j₀} Ω :=
  if h : j = j₀ then 1 else MvPolynomial.X ⟨j, h⟩

def genPt (Ω : Type) [Field Ω] (j₀ j : J) : FractionRing (MvPolynomial {j // j ≠ j₀} Ω) :=
  algebraMap _ _ (genPoly Ω j₀ j)

omit [Fintype J] in
theorem genPt_self (j₀ : J) : genPt Ω j₀ j₀ = 1 := by simp [genPt, genPoly]


omit [Fintype J] in
theorem eq_top_of_genPt_mem (j₀ : J) (K : Subfield (FractionRing (MvPolynomial {j // j ≠ j₀} Ω)))
    (h1 : ∀ a : Ω, algebraMap Ω _ a ∈ K) (h2 : ∀ j, genPt Ω j₀ j ∈ K) : K = ⊤ := by
  have h : ∀ p : MvPolynomial {j // j ≠ j₀} Ω, algebraMap _ _ p ∈ K := fun p => by
    induction p using MvPolynomial.induction_on with
    | C a => exact h1 a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      simpa [genPt, genPoly, j.2] using h2 j.1
  refine top_unique fun x _ => ?_
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial {j // j ≠ j₀} Ω) x
  exact div_mem (h p) (h q)

theorem eq_zero_of_sum_genPt (j₀ : J) (b : J → Ω) (h : ∑ j, algebraMap Ω _ (b j) * genPt Ω j₀ j = 0) : b = 0 := by
  have h' : ∑ j, MvPolynomial.C (b j) * genPoly Ω j₀ j = 0 := by
    apply IsFractionRing.injective _ (FractionRing (MvPolynomial {j // j ≠ j₀} Ω))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum, ← h]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; rfl
  have e : ∀ x : J → Ω, x j₀ = 1 → ∑ j, b j * x j = 0 := fun x hx => by
    have := congrArg (MvPolynomial.eval fun j : {j // j ≠ j₀} => x j.1) h'
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀
    · subst hj; simp [genPoly, hx]
    · simp [genPoly, hj]
  have h0 : b j₀ = 0 := by simpa [Pi.single_apply] using e (Pi.single j₀ 1) (by simp)
  funext j
  by_cases hj : j = j₀
  · exact hj ▸ h0
  · have := e (fun l => Pi.single (M := fun _ => Ω) j₀ 1 l + Pi.single (M := fun _ => Ω) j 1 l) (by simp [Ne.symm hj])
    simpa [Pi.single_apply, mul_add, Finset.sum_add_distrib, h0] using this

theorem genPt_ratio (j₀ : J) (B : Matrix J J Ω) (hB : B.det ≠ 0) (i : J) :
    (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) i ≠ 0 ∧ AlgebraicIndependent Ω fun j : {j // j ≠ i} =>
      (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) j.1 / (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) i := by
  set u := (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) with hu
  have hi : u i ≠ 0 := fun h => hB (Matrix.det_eq_zero_of_row_eq_zero i
    (congrFun (eq_zero_of_sum_genPt j₀ (B i) h)))
  refine ⟨hi, ?_⟩
  set r : {j // j ≠ i} → _ := fun j => u j.1 / u i
  have hs : (B⁻¹.map (algebraMap Ω _)).mulVec u = genPt Ω j₀ := by
    rw [hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  set K := IntermediateField.adjoin Ω (Set.range r)
  have h1 : ∀ j, u j / u i ∈ K := fun j => by
    by_cases hj : j = i
    · rw [hj, div_self hi]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨j, hj⟩, rfl⟩
  have h2 : ∀ j, genPt Ω j₀ j / u i ∈ K := fun j => by
    rw [← hs, Matrix.mulVec, dotProduct, Finset.sum_div]
    refine sum_mem fun l _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (K.algebraMap_mem _) (h1 l)
  have h3 : K.toSubfield = ⊤ := eq_top_of_genPt_mem j₀ _ K.algebraMap_mem fun j => by
    have := div_mem (h2 j) (h2 j₀)
    rwa [div_div_div_cancel_right₀ hi, genPt_self, div_one] at this
  have h4 : Algebra.IsAlgebraic K (FractionRing (MvPolynomial {j // j ≠ j₀} Ω)) := ⟨fun x =>
    isAlgebraic_algebraMap (⟨x, (h3 ▸ Subfield.mem_top x : x ∈ K.toSubfield)⟩ : K)⟩
  have h5 := IntermediateField.isAlgebraic_adjoin_iff_top.1 h4
  refine (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω r ?_).1
  have h6 := trdeg_add_eq Ω (MvPolynomial {j // j ≠ j₀} Ω) (A := FractionRing (MvPolynomial {j // j ≠ j₀} Ω))
  rw [← h6, MvPolynomial.trdeg_of_isDomain]
  refine le_trans (le_of_eq ?_) le_self_add
  simp [Cardinal.mk_fintype]

end Generic

theorem exists_projBundle : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] (EE : M.Lat J), IsProjOver M.s → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : J → Ω'), ProjBundle M EE M' φ f s ∧ IsProjOver M'.s := by
  intro F Ω _ _ _ M J _ inst ⟨j₀⟩ EE hM
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  let : DecidableEq J := fun a b => Classical.propDecidable (a = b)
  let Ω' := FractionRing (MvPolynomial {j // j ≠ j₀} Ω)
  let φ : Ω →ₐ[F] Ω' := IsScalarTower.toAlgHom F Ω Ω'
  obtain ⟨M', f, hf, hp, hc⟩ := RatModel.exists_projBundle_closure F Ω M Ω' φ J EE (genPt Ω j₀) hM
    ⟨j₀, by rw [genPt_self]; exact one_ne_zero⟩
    (eq_top_of_genPt_mem j₀ _ (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      fun j => Subfield.subset_closure (Or.inr ⟨j₀, j, by rw [genPt_self, div_one]⟩))
  refine ⟨Ω', inferInstance, inferInstance, M', φ, f, genPt Ω j₀, ⟨hf, fun B hB i => ?_, hc⟩, hp⟩
  obtain ⟨h1, h2⟩ := genPt_ratio j₀ B hB i
  exact ⟨h1, fun P hP => algebraicIndependent_iff.1 h2 P hP⟩

end GlobalTheory.FlagBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsProjectiveBundleOfLatticeIsProjOverStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_projectiveBundleOfLattice_isProjOver : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] (EE : M.Lat J), IsProjOver M.s → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : J → Ω'), ProjBundle M EE M' φ f s ∧ IsProjOver M'.s := by
  first | exact @GlobalTheory.FlagBundle.exists_projBundle | exact GlobalTheory.FlagBundle.exists_projBundle | (intros; apply GlobalTheory.FlagBundle.exists_projBundle <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFrameFamilyLongerFlagGenericLine
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFrameFamilyLongerFlagGenericLine
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

namespace StepLoc

variable {ι : Type} {m k : ι → ℕ} {K : Type} [Field K] {O : Subring K} {τ : ι}

abbrev blk (k : ι → ℕ) (τ : ι) (P : Mat m K) : Matrix (Rest m k τ) (Rest m k τ) K :=
  (P τ).submatrix Subtype.val Subtype.val

theorem mul_apply_rest {P : Mat m K} (hP : Par k O P) (g : Mat m K) (a : Fin (m τ)) (j : Rest m k τ) :
    (g * P) τ a j.1 = Matrix.vecMul (fun l : Rest m k τ => g τ a l.1) (blk k τ P) j := by
  rw [Pi.mul_apply, Matrix.mul_apply, ← Fintype.sum_subtype_add_sum_subtype (fun l : Fin (m τ) => k τ ≤ (l : ℕ))]
  have : ∑ l : {l : Fin (m τ) // ¬ k τ ≤ (l : ℕ)}, g τ a l.1 * P τ l.1 j.1 = 0 :=
    Finset.sum_eq_zero fun l _ => by
      have h1 := l.2
      have h2 := j.2
      rw [(hP τ).2.2.2 l.1 j.1 (by omega) (by show (l.1 : ℕ) < j.1; omega), mul_zero]
  rw [this, add_zero]
  rfl

theorem blk_mul_inv {P : Mat m K} (hP : Par k O P) : blk k τ P * blk k τ P⁻¹ = 1 := by
  ext a j
  have := mul_apply_rest hP.inv P a.1 j
  rw [Mat.mul_inv hP.det_ne] at this
  refine this.symm.trans ?_
  show (1 : Matrix _ _ K) a.1 j.1 = _
  simp only [Matrix.one_apply, Subtype.ext_iff]

theorem line_iff {Q : Mat m K} (hQ : Par k O Q) (hk : k τ < m τ) {s : Rest m k τ → K} {b : K}
    (hs : ∀ j : Rest m k τ, s j = b * Q τ ⟨k τ, hk⟩ j.1) (hb : b ≠ 0) (g : Mat m K) :
    (∃ a : K, ∀ j : Rest m k τ, (g * Q) τ ⟨k τ, hk⟩ j.1 = a * s j) ↔
      ∀ j : Fin (m τ), k τ < j → g τ ⟨k τ, hk⟩ j = 0 := by
  have e : ∀ (x : K) (j : Rest m k τ), Matrix.vecMul (Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) x) (blk k τ Q) j
      = x * Q τ ⟨k τ, hk⟩ j.1 := fun x j => by
    rw [Matrix.single_vecMul]
    simp
  constructor
  · rintro ⟨a, ha⟩ j hj
    have h1 : Matrix.vecMul (fun l : Rest m k τ => g τ ⟨k τ, hk⟩ l.1) (blk k τ Q) =
        Matrix.vecMul (Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) (a * b)) (blk k τ Q) := by
      funext l
      rw [← mul_apply_rest hQ, ha, e, hs, mul_assoc]
    have h2 := congrArg (Matrix.vecMul · (blk k τ Q⁻¹)) h1
    simp only [Matrix.vecMul_vecMul, blk_mul_inv hQ, Matrix.vecMul_one] at h2
    have h3 := congrFun h2 ⟨j, hj.le⟩
    rwa [Pi.single_eq_of_ne (fun h => hj.ne' (congrArg (fun x : Rest m k τ => (x.1 : ℕ)) h))] at h3
  · intro h
    refine ⟨g τ ⟨k τ, hk⟩ ⟨k τ, hk⟩ / b, fun j => ?_⟩
    have h1 : (fun l : Rest m k τ => g τ ⟨k τ, hk⟩ l.1) =
        Pi.single (⟨⟨k τ, hk⟩, le_rfl⟩ : Rest m k τ) (g τ ⟨k τ, hk⟩ ⟨k τ, hk⟩) := by
      funext l
      by_cases hl : l = ⟨⟨k τ, hk⟩, le_rfl⟩
      · rw [hl, Pi.single_eq_same]
      · rw [Pi.single_eq_of_ne hl]
        exact h _ (lt_of_le_of_ne l.2 fun h' => hl (Subtype.ext (Fin.ext h'.symm)))
    rw [mul_apply_rest hQ, h1, e, hs, ← mul_assoc, div_mul_cancel₀ _ hb]

theorem par_succ_iff {k' : ι → ℕ} (hk : k τ < m τ) (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (g : Mat m K) :
    Par k' O g ↔ Par k O g ∧ ∀ j : Fin (m τ), k τ < j → g τ ⟨k τ, hk⟩ j = 0 := by
  constructor
  · intro h
    refine ⟨h.mono (fun t => ?_) le_rfl, fun j hj => (h τ).2.2.2 _ j (by rw [h1]; exact Nat.lt_succ_self _) hj⟩
    by_cases ht : t = τ
    · rw [ht, h1]; exact Nat.le_succ _
    · exact (h2 t ht).ge
  · rintro ⟨h, h'⟩ t
    refine ⟨(h t).1, (h t).2.1, (h t).2.2.1, fun i j hi hij => ?_⟩
    by_cases ht : t = τ
    · subst ht
      rw [h1] at hi
      rcases (Nat.lt_succ_iff.1 hi).lt_or_eq with hi | hi
      · exact (h t).2.2.2 i j hi hij
      · obtain rfl : i = ⟨k t, hk⟩ := Fin.ext hi
        exact h' j hij
    · exact (h t).2.2.2 i j (h2 t ht ▸ hi) hij

theorem exists_completion (hk : k τ < m τ) (c : Rest m k τ → K) (i : Rest m k τ) (hi : c i = 1) :
    ∃ N : Mat m K, (∀ j : Rest m k τ, N τ ⟨k τ, hk⟩ j.1 = c j) ∧
      ∀ O : Subring K, (∀ j, c j ∈ O) → Par k O N := by
  classical
  let v : Fin (m τ) → K := fun j => if h : k τ ≤ (j : ℕ) then c ⟨j, h⟩ else 0
  have hv : ∀ j : Rest m k τ, v j.1 = c j := fun j => dif_pos j.2
  let T : Matrix (Fin (m τ)) (Fin (m τ)) K :=
    ((1 : Matrix _ _ K).updateRow i.1 v).submatrix (Equiv.swap ⟨k τ, hk⟩ i.1) id
  have hd : T.det * T.det = 1 := by
    have e : ((1 : Matrix _ _ K).updateRow i.1 v).det = 1 := by
      rw [← Matrix.cramer_transpose_apply, Matrix.transpose_one, Matrix.cramer_one]
      exact (hv i).trans hi
    rw [Matrix.det_permute, e, mul_one, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
    simp
  refine ⟨Function.update (1 : Mat m K) τ T, fun j => ?_, fun O hO t => ?_⟩
  · rw [Function.update_self]
    show ((1 : Matrix _ _ K).updateRow i.1 v) (Equiv.swap ⟨k τ, hk⟩ i.1 ⟨k τ, hk⟩) j.1 = _
    rw [Equiv.swap_apply_left, Matrix.updateRow_self, hv]
  by_cases ht : t = τ
  · subst ht
    rw [Function.update_self]
    have hm : ∀ a b, T a b ∈ O := fun a b => by
      show ((1 : Matrix _ _ K).updateRow i.1 v) _ b ∈ O
      rw [Matrix.updateRow_apply]
      split_ifs
      · show dite _ _ _ ∈ O
        split_ifs
        exacts [hO _, O.zero_mem]
      · rw [Matrix.one_apply]; split_ifs; exacts [O.one_mem, O.zero_mem]
    refine ⟨hm, left_ne_zero_of_mul_eq_one hd, ?_, fun a b ha hab => ?_⟩
    · rw [← eq_inv_of_mul_eq_one_left hd]; exact det_mem hm
    · have h1 : a ≠ ⟨k t, hk⟩ := fun h => ha.ne (congrArg Fin.val h)
      have h2 : a ≠ i.1 := fun h => (h ▸ ha).not_ge i.2
      show ((1 : Matrix _ _ K).updateRow i.1 v) (Equiv.swap ⟨k t, hk⟩ i.1 a) b = 0
      rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Matrix.updateRow_ne h2, Matrix.one_apply_ne hab.ne]
  · rw [Function.update_of_ne ht]
    exact Par.one t

end StepLoc


open StepLoc in
theorem exists_fr_stepSet (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω']
    (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι]
    (m k k' : ι → ℕ) (S : Fr M m k) (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ))
    (s : Rest m k τ → Ω') (h1 : k' τ = k τ + 1) (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ')
    (hA₀ : A₀ ∈ S.S (genericPoint M.Z))
    (hE : ∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧
      EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A)))
    (hP : ProjPoints M EE M' φ f s) :
    ∃ S' : Fr M' m k', ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z' := by
  refine ⟨⟨stepSet S τ hk A₀ M' φ f s, fun z' => ?_⟩, fun _ => rfl⟩
  obtain ⟨U, A, hz, hA, hU⟩ := S.loc (f z')
  have hAU : ∀ w ∈ U, A ∈ S.S w := fun w hw => (hU w hw A).2 (by rw [Mat.mul_inv hA]; exact Par.one)
  obtain ⟨hd, hE'⟩ := hE _ A (hAU _ hz)
  obtain ⟨i, hi⟩ := hP.cover z' _ hd hE'
  set c := ((dualBlock k τ A₀ A).map φ).mulVec s with hc
  let ψ : Ω →+* Ω' := φ
  obtain ⟨N, hN, hNO⟩ := exists_completion hk (fun j => c j / c i) i (div_self hi.1)
  have hAφ : ∀ t, (A.map ψ t).det ≠ 0 := fun t => by rw [Mat.det_map]; exact (map_ne_zero ψ).2 (hA t)
  have hN0 : Par k ⊤ N := hNO ⊤ fun _ => trivial
  have hP0 : Par k ⊤ ((A * A₀⁻¹).map ψ) :=
    ((Fr.mem_iff hA₀).1 (Fr.mem_genericPoint (hAU _ hz))).map ψ fun _ _ => trivial
  have hs : s = Matrix.vecMul c (blk k τ ((A * A₀⁻¹).map ψ)) := by
    have hP1 := (Fr.mem_iff hA₀).1 (Fr.mem_genericPoint (hAU _ hz))
    have e1 : (blk k τ (A * A₀⁻¹))⁻¹ * blk k τ (A * A₀⁻¹) = 1 :=
      Matrix.nonsing_inv_mul _ (Matrix.isUnit_det_of_right_inverse (blk_mul_inv hP1))
    have e2 : c = Matrix.vecMul s ((blk k τ (A * A₀⁻¹))⁻¹.map ψ) := by
      rw [hc, ← Matrix.mulVec_transpose]
      rfl
    have e3 : blk k τ ((A * A₀⁻¹).map ψ) = (blk k τ (A * A₀⁻¹)).map ψ := rfl
    rw [e2, e3, Matrix.vecMul_vecMul, ← Matrix.map_mul, e1, Matrix.map_one _ ψ.map_zero ψ.map_one,
      Matrix.vecMul_one]
  have hQ : ∀ j : Rest m k τ, s j = c i * (N * (A * A₀⁻¹).map ψ) τ ⟨k τ, hk⟩ j.1 := fun j => by
    have e : (fun l : Rest m k τ => N τ ⟨k τ, hk⟩ l.1) = (c i)⁻¹ • c := by
      funext l
      rw [hN, Pi.smul_apply, smul_eq_mul, div_eq_inv_mul]
    rw [mul_apply_rest hP0, e, Matrix.smul_vecMul, ← hs, Pi.smul_apply, smul_eq_mul, mul_inv_cancel_left₀ hi.1]
  have hA₁ : ∀ t, ((N * A.map ψ) t).det ≠ 0 := fun t => by
    rw [Pi.mul_apply, Matrix.det_mul]; exact mul_ne_zero (hN0.det_ne t) (hAφ t)
  refine ⟨f ⁻¹ᵁ U ⊓ ⟨_, M'.isOpen_setOf_div c i⟩, N * A.map ψ, ⟨hz, hi⟩, hA₁, fun w hw A' => ?_⟩
  have hNw : Par k (M'.O w).toSubring N := hNO _ hw.2.2
  have hAw : A ∈ S.S (f w) := hAU _ hw.1
  rw [par_succ_iff hk h1 h2, ← line_iff (hN0.mul hP0) hk hQ hi.1]
  have e1 : A' * (N * A.map ψ)⁻¹ * (N * (A * A₀⁻¹).map ψ) = A' * (A₀.map ψ)⁻¹ := by
    rw [Mat.map_mul, Mat.map_inv, ← mul_assoc N, mul_assoc A', ← mul_assoc _ (N * A.map ψ), Mat.inv_mul hA₁,
      one_mul]
  rw [e1]
  refine and_congr_left' ⟨fun h => ?_, fun h B hB => ?_⟩
  · have := (h A hAw).mul hNw.inv
    rwa [Mat.mul_inv_rev, ← mul_assoc]
  · have h3 : Par k (M'.O w).toSubring ((A * B⁻¹).map ψ) :=
      ((Fr.mem_iff hB).1 hAw).map ψ fun _ hx => hP.hom.map_mem_O hx
    have := h.mul (hNw.mul h3)
    rw [Mat.map_mul, Mat.map_inv, ← mul_assoc N, mul_assoc A', ← mul_assoc _ (N * A.map ψ), Mat.inv_mul hA₁,
      one_mul] at this
    exact this

end GlobalTheory.FlagBundle
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAdaptedFrameFamilyLongerFlagGenericLineStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier GlobalTheory.FlagBundle
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_adaptedFrameFamily_longerFlag_genericLine : ∀ (F Ω Ω' : Type) [Field F] [Field Ω] [Algebra F Ω] [Field Ω'] [Algebra F Ω'] (M : RatModel F Ω) (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (ι : Type) [Finite ι] (m k k' : ι → ℕ) (S : Fr M m k) (τ : ι) (hk : k τ < m τ) (A₀ : Mat m Ω) (EE : M.Lat (Rest m k τ)) (s : Rest m k τ → Ω'), k' τ = k τ + 1 → (∀ τ', τ' ≠ τ → k' τ' = k τ') → A₀ ∈ S.S (genericPoint M.Z) → (∀ z, ∀ A ∈ S.S z, (dualBlock k τ A₀ A).det ≠ 0 ∧ EE.E z = Submodule.span (M.O z) (Set.range (dualBlock k τ A₀ A))) → ProjPoints M EE M' φ f s → ∃ S' : Fr M' m k', ∀ z', S'.S z' = stepSet S τ hk A₀ M' φ f s z' := by
  first | exact @GlobalTheory.FlagBundle.exists_fr_stepSet | exact GlobalTheory.FlagBundle.exists_fr_stepSet | (intros; apply GlobalTheory.FlagBundle.exists_fr_stepSet <;> assumption)
end
end

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

theorem step {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {ι : Type} [Finite ι]
    {m k : ι → ℕ} (S : Fr M m k) (hM : Good M d) (τ : ι) (hk : k τ < m τ) (k' : ι → ℕ) (h1 : k' τ = k τ + 1)
    (h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ') :
    ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z)
      (S' : Fr M' m k'), Good M' (d + (m τ - k τ - 1)) ∧ Refines S S' φ f := by
  obtain ⟨A₀, hA₀⟩ := S.nonempty (genericPoint M.Z)
  obtain ⟨EE, hE⟩ := GlobalTheory.T.exists_lattice_dualBasisQuotientFrameBlock F Ω M ι m k S τ A₀ hA₀
  have : Nonempty (Rest m k τ) := ⟨⟨⟨k τ, hk⟩, le_rfl⟩⟩
  obtain ⟨Ω', _, _, M', φ, f, s, hP, hpr⟩ := GlobalTheory.T.exists_projectiveBundleOfLattice_isProjOver F Ω M _ EE hM.1
  have hc : Fintype.card (Rest m k τ) = m τ - k τ := by
    rw [Fintype.card_subtype, ← Fin.card_Ici ⟨k τ, hk⟩]
    exact congrArg _ (Finset.ext fun j => by simp [Fin.le_def])
  have hA := GlobalTheory.T.isAffineSpaceCoveredMorphism F Ω Ω' M M' φ f _ EE s hP
  rw [hc] at hA
  have hp := GlobalTheory.T.projective_bundle_points_of_rational_model F Ω Ω' M M' φ f _ EE s hP
  obtain ⟨S', hS'⟩ := GlobalTheory.T.exists_adaptedFrameFamily_longerFlag_genericLine F Ω Ω' M M' φ f ι m k k' S τ hk A₀ EE s h1 h2 hA₀ hE hp
  refine ⟨Ω', _, _, M', φ, f, S', ⟨hpr, GlobalTheory.T.affineSpaceCovered_smoothOfRelativeDimension_add F Ω Ω' M M' φ f _ d hA hM.2.1, GlobalTheory.T.geometricallyIntegral_of_affCover F Ω Ω' M M' φ f _ hA hM.2.2⟩,
    fun τ' => ?_, hP.hom, fun z' A' hA' => ?_, GlobalTheory.T.preservesRadicalPrincipalIdeals_of_affineSpaceCovered F Ω Ω' M M' φ f _ hA,
    GlobalTheory.T.existsUnique_projectiveBundle_flagRefinement F Ω Ω' M M' φ f ι m k k' S S' τ hk A₀ EE s h1 h2 hA₀ hE hp hS'⟩
  · by_cases h : τ' = τ
    · subst h; exact h1 ▸ Nat.le_succ _
    · exact (h2 τ' h).ge
  · rw [hS'] at hA'
    exact hA'.1

theorem tower {F : Type} [Field F] {ι : Type} [Fintype ι] {m : ι → ℕ} (n : ℕ) :
    ∀ {Ω : Type} [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (d : ℕ) {k : ι → ℕ} (S : Fr M m k), Good M d → k ≤ m →
      ∑ τ, (m τ - k τ) = n → ∃ (Y : GlobalTheory.ProjVar.Var F) (φ : Ω →ₐ[F] Y.Fn) (f : Y.X ⟶ M.Z) (S' : Fr (ratOf Y) m m),
        Y.dim = d + ∑ τ, (m τ - k τ).choose 2 ∧ Refines S S' φ f := by
  classical
  induction n with
  | zero =>
    intro Ω _ _ M d k S hM hk hn
    obtain rfl : k = m := funext fun τ => le_antisymm (hk τ)
      (Nat.sub_eq_zero_iff_le.1 (Finset.sum_eq_zero_iff.1 hn τ (Finset.mem_univ _)))
    obtain ⟨Y, φ, f, S', h1, h2⟩ := GlobalTheory.T.exists_variety_flagRefinementBundle_of_goodModel F Ω M d ι k k S hM
    exact ⟨Y, φ, f, S', by simpa using h1, h2⟩
  | succ n ih =>
    intro Ω _ _ M d k S hM hk hn
    obtain ⟨τ, -, hτ⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hn.trans_ne n.succ_ne_zero)
    have hτ' : k τ < m τ := by omega
    let k' := Function.update k τ (k τ + 1)
    have h1 : k' τ = k τ + 1 := Function.update_self _ _ _
    have h2 : ∀ τ', τ' ≠ τ → k' τ' = k τ' := fun τ' h => Function.update_of_ne h _ _
    obtain ⟨Ω', _, _, M', φ, f, S', hM', hR⟩ := step M d S hM τ hτ' k' h1 h2
    have key : ∀ g : ℕ → ℕ, ∑ t, g (m t - k' t) + g (m τ - k τ) = ∑ t, g (m t - k t) + g (m τ - k τ - 1) := fun g => by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ τ), ← Finset.add_sum_erase _ (fun t => g (m t - k t)) (Finset.mem_univ τ),
        h1, Finset.sum_congr rfl fun t ht => by rw [h2 t (Finset.ne_of_mem_erase ht)], Nat.sub_add_eq]
      ring
    obtain ⟨Y, φ', f', S'', hd, hR'⟩ := ih M' _ S' hM' (fun t => by
      by_cases h : t = τ
      · subst h; rw [h1]; exact hτ'
      · rw [h2 t h]; exact hk t) (by have := key id; simp only [id] at this; omega)
    refine ⟨Y, φ'.comp φ, f' ≫ f, S'', ?_, GlobalTheory.T.isFlagRefinementBundle_comp F Ω Ω' M M' φ f Y.Fn (ratOf Y) φ' f' ι m k k' m S S' S'' hR hR'⟩
    have := key fun a => a.choose 2
    obtain ⟨a, ha⟩ : ∃ a, m τ - k τ = a + 1 := ⟨m τ - k τ - 1, by omega⟩
    rw [ha, Nat.choose_succ_succ' a 1, Nat.choose_one_right, Nat.add_sub_cancel] at this
    rw [hd, ha, Nat.add_sub_cancel]
    simp only [Nat.reduceAdd] at this
    omega

open Limits NumberField Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.ShFam

section Component

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β)
  {F : Type} [Field F] (e : F ≃+* c.F)

theorem genericPoint_mem {B : Scheme.{0}} [IsIntegral B] (j : B ⟶ gen Z) [IsOpenImmersion j] :
    j (genericPoint B) ∈ Set.range Z.jQ := by
  have := Z.jQ_open
  obtain ⟨_, ⟨b, rfl⟩, hb⟩ := Z.jQ_dense.inter_open_nonempty _ j.isOpenEmbedding.isOpen_range ⟨_, genericPoint B, rfl⟩
  exact ((genericPoint_specializes b).map j.continuous).mem_open Z.jQ.isOpenEmbedding.isOpen_range hb

theorem exists_flagCpt (hS : ReciprocityTheory.AnForm.R.FinalTheorems.Snc (genBdIdeal Z)) (B : GlobalTheory.ProjVar.Var F) (j : B.X ⟶ gen Z)
    [IsOpenImmersion j] (hj : j ≫ genStr Z ≫ spMap e.toRingHom = B.str) :
    ∃ (C : FlagCpt Z e) (f : C.Y.X ⟶ B.X), C.π = f ≫ j ∧ C.Y.dim = B.dim + ∑ τ : E →+* ℂ, (Dw.mult τ).choose 2 ∧
      ∀ (K : Type) [Field K] (χ : c.F →+* K) (x : Sp K ⟶ gen Z) (x' : Sp K ⟶ B.X), x' ≫ j = x →
        x ≫ genStr Z = spMap χ → ∀ g : EigFrame Z χ (x ≫ genι Z), ∃! p : Sp K ⟶ C.Y.X, p ≫ f = x' ∧ C.Carries p g := by
  have := Z.jQ_open
  obtain ⟨f₀, S, A₀, hT⟩ := GlobalTheory.T.exists_lieEigenparts_frame_family_over_variety E H Dw l Xo c O β Z F e B j hj
  obtain ⟨Y, φ, f, S', hd, hR⟩ := tower _ (ratOf B) B.dim S (good_ratOf B) (fun _ => Nat.zero_le _) rfl
  change Y.X ⟶ B.X at f
  obtain ⟨g₀, A₁, hT', hC⟩ := GlobalTheory.T.tautologicalFamily_refinement_compatible_lieAlgebraFrame E H Dw l Xo c O β Z F e B Y j f₀ S A₀ _ S' φ f hT hR
  obtain ⟨gr, hgr⟩ := GlobalTheory.T.exists_graded_line_divisors_full_flag E H Dw l Xo c O β Z F e Y (f ≫ j) g₀ S' A₁ hT'
  have hgen := genericPoint_mem Z j
  obtain ⟨D, hD1, hD2, hD3⟩ := GlobalTheory.T.exists_reduced_cartierDivisor_of_snc_closed (gen Z) B.X j (genBd Z) hS fun h => h hgen
  obtain ⟨D', hD1', hD2', hD3'⟩ := GlobalTheory.T.exists_reduced_effective_cartierDivisor_pullback F B Y φ f D hR.hom hR.rad hD1 hD3
  have hstr : (f ≫ j) ≫ genStr Z ≫ spMap e.toRingHom = Y.str := by
    rw [Category.assoc, hj]; exact hR.hom.inducedModelMorphism_comp_structureMap
  have hrange : Set.range (genericPt Y ≫ f ≫ j) ⊆ Set.range Z.jQ := by
    rintro _ ⟨w, rfl⟩
    have h : genericPt Y ≫ f = spMap φ.toRingHom ≫ genericPt B := hR.hom
    have h' : genericPt B (spMap φ.toRingHom w) = genericPoint B.X := (ratOf B).pt_apply _
    rw [← Category.assoc, h, Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, h']
    exact hgen
  let z : Sp Y.Fn ⟶ Xo.XF c := IsOpenImmersion.lift Z.jQ (genericPt Y ≫ f ≫ j) hrange
  have hz : z ≫ Z.jQ = genericPt Y ≫ f ≫ j := IsOpenImmersion.lift_fac _ _ _
  have hzs : z ≫ pullback.snd _ _ = spMap (constF e Y) := by
    have h1 : genericPt Y ≫ Y.str = spMap (algebraMap F Y.Fn) := (ratOf Y).pt_s
    have h2 : spMap e.toRingHom ≫ spMap e.symm.toRingHom = 𝟙 _ := by
      refine (Spec.map_comp _ _).symm.trans ((congrArg Spec.map ?_).trans (Spec.map_id _))
      exact CommRingCat.hom_ext (RingHom.ext fun a => e.apply_symm_apply a)
    rw [← Z.jQ_over, ← Category.assoc, hz, ← Category.comp_id (pullback.snd Z.s (spMap β)), ← h2]
    refine Eq.trans ?_ ((congrArg (· ≫ spMap e.symm.toRingHom) h1).trans (Spec.map_comp _ _).symm)
    rw [← hstr]
    simp only [Category.assoc]
  obtain ⟨y0, hy1, hy2⟩ := GlobalTheory.T.exists_framed_point_over_of_lie_eigenspace_frame E H Dw l Xo c O β Z Y.Fn (constF e Y) z _ g₀ hzs (by
    rw [← Category.assoc, hz]; simp only [Category.assoc])
  let C : FlagCpt Z e :=
    { Y := Y, π := f ≫ j, π_str := hstr, y0 := y0, f0 := g₀, y0_x := by rw [hy1, hz], flagComponentFramedPoint_frame := by rw [hy1]; exact hy2, gr := gr,
      gr_spec := hgr, bd := D', bd_eff := hD1', bd_red := hD3'
      bd_supp := fun y => (hD2' y).trans ((hD2 _).trans (by rw [Scheme.Hom.comp_apply])) }
  exact ⟨C, f, rfl, by simpa using hd,
    GlobalTheory.T.eigenFrameBasePoint_lifts_unique_flagSpace E H Dw l Xo c O β Z F e C B j f₀ S A₀ S' A₁ φ f hj rfl hT hT' hC hR⟩

end Component

end GlobalTheory.FlagBundle
