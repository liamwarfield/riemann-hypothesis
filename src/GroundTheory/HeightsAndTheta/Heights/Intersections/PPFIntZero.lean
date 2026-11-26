module

public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogRenameCoordPow
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PotentialContDiffAt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedE

@[expose] public section

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFIntZero
section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PFIntZeroMixed
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Matrix Module ReciprocityTheory.ChartRestriction.G.Geo

variable {D : ℕ}

theorem sum_neg_one_pow_superset_eq_zero (p : Finset (Fin D) → Prop) [DecidablePred p] (a : Fin D)
    (hp : ∀ T, p (insert a T) ↔ p T) (X : ℂ) :
    ∑ T : Finset (Fin D), (-1 : ℂ) ^ (D - T.card) * (if p T then X else 0) = 0 := by
  rw [← Finset.powerset_univ, ← Finset.insert_erase (Finset.mem_univ a),
    Finset.sum_powerset_insert (Finset.notMem_erase a _), ← Finset.sum_add_distrib]
  refine Finset.sum_eq_zero fun T hT => ?_
  have haT : a ∉ T := fun h => Finset.notMem_erase a _ (Finset.mem_powerset.mp hT h)
  have hlt : T.card < D := by
    have := Finset.card_le_card (Finset.mem_powerset.mp hT)
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ, Fintype.card_fin] at this
    have : 0 < D := Fin.pos a
    omega
  rw [Finset.card_insert_of_notMem haT]
  have hD : D - T.card = (D - (T.card + 1)) + 1 := by omega
  by_cases h : p T
  · rw [if_pos h, if_pos ((hp T).mpr h), hD, pow_succ]
    ring
  · rw [if_neg h, if_neg fun h' => h ((hp T).mp h')]
    ring

theorem mixedDisc_eq_zero_of_cols (B : Fin D → Matrix (Fin D) (Fin D) ℂ) (S C : Finset (Fin D))
    (hcard : D < C.card + S.card) (hB : ∀ k ∈ S, ∀ j ∈ C, ∀ i, B k i j = 0) : mixedDisc B = 0 := by
  classical
  unfold mixedDisc
  refine mul_eq_zero_of_right _ ?_
  have hdet : ∀ T : Finset (Fin D), (∑ k ∈ T, B k).det = ∑ σ : Equiv.Perm (Fin D), ∑ f : Fin D → Fin D,
      (if ∀ i, f i ∈ T then (Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i else 0) := by
    intro T
    rw [Matrix.det_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    simp only [Matrix.sum_apply]
    rw [Finset.prod_univ_sum, Units.smul_def, zsmul_eq_mul, Finset.mul_sum]
    have hpi : Fintype.piFinset (fun _ : Fin D => T) = Finset.univ.filter (fun f : Fin D → Fin D => ∀ i, f i ∈ T) := by
      ext f; simp [Fintype.mem_piFinset]
    rw [hpi, Finset.sum_filter]
  simp_rw [hdet, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun σ _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun f _ => ?_
  by_cases hf : Function.Surjective f
  · have hbij : Function.Bijective f := ⟨Finite.injective_iff_surjective.mpr hf, hf⟩
    have hpre : (S.preimage f hbij.1.injOn).card = S.card := by
      rw [Finset.card_preimage]
      congr 1
      exact Finset.filter_true_of_mem fun x _ => hf x
    obtain ⟨i, hi⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (Finset.subset_univ C)
      (Finset.subset_univ (S.preimage f hbij.1.injOn)) (by rw [hpre, Finset.card_univ, Fintype.card_fin]; exact hcard)
    rw [Finset.mem_inter, Finset.mem_preimage] at hi
    have h0 : ∏ i, B (f i) (σ i) i = 0 := Finset.prod_eq_zero (Finset.mem_univ i) (hB _ hi.2 _ hi.1 _)
    refine Finset.sum_eq_zero fun T _ => ?_
    simp [h0]
  · obtain ⟨a, ha⟩ := not_forall.mp hf
    push Not at ha
    have := sum_neg_one_pow_superset_eq_zero (fun T => ∀ i, f i ∈ T) a
      (fun T => ⟨fun h i => (Finset.mem_insert.mp (h i)).resolve_left (ha i), fun h i => Finset.mem_insert_of_mem (h i)⟩)
      ((Equiv.Perm.sign σ : ℂ) * ∏ i, B (f i) (σ i) i)
    exact this

theorem mixedDisc_mul_right (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (P : Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => A k * P) = mixedDisc A * P.det := by
  unfold mixedDisc
  simp_rw [← Finset.sum_mul, Matrix.det_mul, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun T _ => by ring

theorem mixedDisc_map_star (A : Fin D → Matrix (Fin D) (Fin D) ℂ) :
    mixedDisc (fun k => (A k).map (starRingEnd ℂ)) = starRingEnd ℂ (mixedDisc A) := by
  unfold mixedDisc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, map_sum]
  congr 1
  · simp
  · refine Finset.sum_congr rfl fun T _ => ?_
    rw [map_mul, map_pow, map_neg, map_one, RingHom.map_det]
    congr 2
    ext i j
    simp [Matrix.sum_apply]

theorem mixedDisc_eq_zero_of_ker (A : Fin D → Matrix (Fin D) (Fin D) ℂ) (V : Submodule ℂ (Fin D → ℂ))
    (S : Finset (Fin D)) (hdim : D < Module.finrank ℂ V + S.card) (hA : ∀ k ∈ S, ∀ x ∈ V, A k *ᵥ x = 0) :
    mixedDisc A = 0 := by
  classical
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl V
  set b0 := ((Module.finBasis ℂ V).prod (Module.finBasis ℂ U)).map (Submodule.prodEquivOfIsCompl V U hU) with hb0
  have hcardι : Fintype.card (Fin (Module.finrank ℂ V) ⊕ Fin (Module.finrank ℂ U)) = D := by
    rw [← Module.finrank_eq_card_basis b0, Module.finrank_fin_fun]
  set e := Fintype.equivFinOfCardEq hcardι
  set b := b0.reindex e
  have hbV : ∀ i, b (e (Sum.inl i)) ∈ V := by
    intro i
    simp [b, hb0, Basis.reindex_apply, Basis.map_apply, Basis.prod_apply]
  set P : Matrix (Fin D) (Fin D) ℂ := (Pi.basisFun ℂ (Fin D)).toMatrix b
  have hP : IsUnit P.det := by
    rw [← Basis.det_apply]
    exact (Pi.basisFun ℂ (Fin D)).isUnit_det b
  set C := Finset.univ.image fun i => e (Sum.inl i)
  have hC : C.card = Module.finrank ℂ V := by
    rw [Finset.card_image_of_injective (f := fun i => e (Sum.inl i)) _
      (fun x y h => Sum.inl_injective (e.injective h)), Finset.card_univ, Fintype.card_fin]
  have hcol : ∀ k ∈ S, ∀ j ∈ C, ∀ i, (A k * P) i j = 0 := by
    intro k hk j hj i
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp hj
    have h := congrFun (hA k hk _ (hbV l)) i
    simpa [P, Matrix.mul_apply, Matrix.mulVec, dotProduct, Basis.toMatrix_apply] using h
  have h := mixedDisc_eq_zero_of_cols (fun k => A k * P) S C (by rw [hC]; exact hdim) hcol
  rw [mixedDisc_mul_right] at h
  exact (mul_eq_zero.mp h).resolve_right hP.ne_zero

end GroundTheory.Heights₂.Heights.Inter
end
end

set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

def eulerDirs {n : ℕ} (F : (Fin n → ℂ) → (Σ k, ι k) → ℂ) (y : Fin n → ℂ) : Submodule ℂ (Fin n → ℂ) where
  carrier := {x | ∃ c : K → ℂ, fderiv ℂ F y x = bsmul c (F y)}
  add_mem' := by
    rintro x x' ⟨c, hc⟩ ⟨c', hc'⟩
    exact ⟨c + c', by rw [map_add (f := _), hc, hc']; funext p; simp [bsmul, add_mul]⟩
  zero_mem' := ⟨0, by rw [map_zero]; funext p; simp [bsmul]⟩
  smul_mem' := by
    rintro a x ⟨c, hc⟩
    exact ⟨a • c, by rw [map_smul, hc]; funext p; simp [bsmul, mul_assoc]⟩

theorem eulerDirs_finrank (hR : pointFormRank_holds.Statement) {Q : Ideal (MRing ι)} {d n : ℕ} (hQ : IsArithVar Q d)
    {F : (Fin n → ℂ) → (Σ k, ι k) → ℂ} {y : Fin n → ℂ} (hF : AnalyticAt ℂ F y)
    (hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts Q) : n < Module.finrank ℂ (eulerDirs F y) + d := by
  by_contra hlt
  push Not at hlt
  obtain ⟨U, hU⟩ := Submodule.exists_isCompl (eulerDirs F y)
  have hsum := Submodule.finrank_add_eq_of_isCompl hU
  rw [Module.finrank_fin_fun] at hsum
  have hdm : d ≤ Module.finrank ℂ U := by omega
  set bU := Module.finBasis ℂ U
  let Mlin : (Fin (Module.finrank ℂ U) → ℂ) →ₗ[ℂ] (Fin n → ℂ) := U.subtype ∘ₗ bU.equivFun.symm.toLinearMap
  let M : (Fin (Module.finrank ℂ U) → ℂ) →L[ℂ] (Fin n → ℂ) := LinearMap.toContinuousLinearMap Mlin
  have hMU : ∀ x, M x ∈ U := fun x => Submodule.coe_mem (bU.equivFun.symm x)
  have hMinj : Function.Injective M := fun a b h => bU.equivFun.symm.injective (Subtype.ext h)
  have hA : HasFDerivAt (fun y' => y + M y') M 0 := (M.hasFDerivAt).const_add y
  have hy : y + M 0 = y := by rw [map_zero, add_zero]
  have hF' : AnalyticAt ℂ F (y + M 0) := by rw [hy]; exact hF
  have hGa : AnalyticAt ℂ (fun y' => F (y + M y')) 0 :=
    hF'.comp (f := fun y' => y + M y') (analyticAt_const.add (M.analyticAt 0))
  have hGQ : ∀ᶠ y' in 𝓝 (0 : Fin (Module.finrank ℂ U) → ℂ), F (y + M y') ∈ mcPts Q := by
    have ht : Tendsto (fun y' => y + M y') (𝓝 0) (𝓝 y) := by
      have := hA.continuousAt.tendsto
      rwa [hy] at this
    exact ht.eventually hFQ
  obtain ⟨x, hx, c, hxc⟩ := hR K ι Q d _ (fun y' => F (y + M y')) 0 hQ hdm hGa hGQ
  have hFd : HasFDerivAt F (fderiv ℂ F y) (y + M 0) := by rw [hy]; exact hF.differentiableAt.hasFDerivAt
  have hGd : HasFDerivAt (fun y' => F (y + M y')) ((fderiv ℂ F y).comp M) 0 :=
    hFd.comp (f := fun y' => y + M y') 0 hA
  rw [hGd.fderiv, ContinuousLinearMap.comp_apply, hy] at hxc
  have hmem : M x ∈ eulerDirs F y ⊓ U := ⟨⟨c, hxc⟩, hMU x⟩
  rw [hU.inf_eq_bot, Submodule.mem_bot] at hmem
  exact hx (hMinj (by rw [hmem, map_zero]))

theorem map_star_mulVec {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) :
    M.map (starRingEnd ℂ) *ᵥ x = star (M *ᵥ star x) := by
  funext i
  simp [Matrix.mulVec, dotProduct]

theorem PFIntZero.maDensity_eq_zero (hR : pointFormRank_holds.Statement)
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {d r : ℕ}
    {L : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {L' : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (N : Fin r → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') (hv : IsBlockMap κ v)
    (hQ : IsArithVar (imageZ v P') d) (hL : ∀ j, IsSmoothHerm (L j))
    (hLL : ∀ j, IsPullHerm κ v (L j) (L' j))
    {Ψ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (d + r + 1) → ℂ)} {y : Fin (d + r) → ℂ}
    {w : ((k : K') → ι' k) → ℂ} {γ : (Fin (d + r) → ℂ) → (Σ k', ι' k') → ℂ} (hγ : IsSheet P' Ψ y w γ) :
    maDensity (fun j y' => Real.log ((Fin.append L' N j).h (γ y'))) y = 0 := by
  set F : (Fin (d + r) → ℂ) → (Σ k, ι k) → ℂ := fun y' p => γ y' (v p) with hF
  have hγa : AnalyticAt ℂ γ y := sheet_analyticAt osgood hγ
  have hFa : AnalyticAt ℂ F y := analyticAt_pi_iff.mpr fun p => analyticAt_coord hγa (v p)
  have hFy : ∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0 := blocks_ne_zero_restrict hv hγ.2.self_of_nhds.2.1.1
  have hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts (imageZ v P') := by
    filter_upwards [hγ.2] with y' h
    refine ⟨blocks_ne_zero_restrict hv h.2.1.1, fun f hf => ?_⟩
    have h0 := h.2.1.2 _ (Ideal.mem_comap.mp hf)
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h0
    exact h0
  set A : Fin (d + r) → Matrix (Fin (d + r)) (Fin (d + r)) ℂ :=
    fun j => cxHessian (fun y' => Real.log ((Fin.append L' N j).h (γ y'))) y with hAdef
  have hker : ∀ k ∈ Finset.univ.map (Fin.castAddEmb r), ∀ x ∈ eulerDirs F y,
      (A k).map (starRingEnd ℂ) *ᵥ x = 0 := by
    intro k hk x hx
    obtain ⟨j, -, rfl⟩ := Finset.mem_map.mp hk
    obtain ⟨c, hc⟩ := hx
    have hpot : (fun y' => Real.log ((Fin.append L' N (Fin.castAddEmb r j)).h (γ y'))) =
        fun y' => Real.log ((L j).h (F y')) := by
      funext y'
      rw [Fin.coe_castAddEmb, Fin.append_left, (hLL j).2]
    have h := pointFormEuler_holds.proof K ι (L j) (d + r) F y x c (hL j) hFa hFy hc
    rw [map_star_mulVec, hAdef]
    simp only
    rw [hpot, h, star_zero]
  have hmix := mixedDisc_eq_zero_of_ker (fun k => (A k).map (starRingEnd ℂ)) (eulerDirs F y) _
    (by rw [Finset.card_map, Finset.card_univ, Fintype.card_fin]; exact eulerDirs_finrank hR hQ hFa hFQ) hker
  rw [mixedDisc_map_star, map_eq_zero] at hmix
  show _ * _ * (mixedDisc A).re = 0
  rw [hmix, Complex.zero_re, mul_zero]

theorem PFIntZero.proof (hR : pointFormRank_holds.Statement) : PFIntZero.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d r L L' N A s hv _ hQ hL hLL
  classical
  unfold arInt ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P' hΨ.choose (fun j z => Real.log ((Fin.append L' N j).h z)) (logNorm A s) y w
        = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · exact mul_eq_zero_of_right _ (PFIntZero.maDensity_eq_zero hR N hv hQ hL hLL hγ.choose_spec)
      · rfl
    simp [h0]
  · rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.StatementsPFHoriz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

section Fibre

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]


open Classical in
def baseSubst (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P') :
    MRing ι' →+* MRingOver G.Φ (fibreIdx ι' κ) :=
  eval₂Hom (algebraMap ℤ _) fun q =>
    if h : q.1 ∈ Set.range κ then
      (if h' : q ∈ Set.range v then C (G.x h'.choose) else 0)
    else X ⟨⟨q.1, h⟩, q.2⟩

def fibreOf (κ : K → K') {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} (G : GenFibre v P')
    (W : Ideal (MRing ι')) : Ideal (MRingOver G.Φ (fibreIdx ι' κ)) :=
  Ideal.map (baseSubst κ G) W

end Fibre

def PFHoriz.Statement : Prop :=
  ∀ (I : AllFam) (r : ℕ), PFAt I r →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' W : Ideal (MRing ι')) (d : ℕ)
      (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
      (L : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (L' : Fin d → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') (N : Fin r → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'),
      IsBlockMap κ v → IsArithVar W (d + r) → imageZ v W = imageZ v P' → IsArithVar (imageZ v P') d →
      IsFieldIntersection J → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      (∀ j, IsSmoothHerm (N j)) →
      I K' ι' W (d + r) (Fin.append L' N) =
        (J (fibreOf κ G W) r (fun j => fibreDeg κ (N j).a) : ℝ) * I K ι (imageZ v P') d L

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.MixedDiscEqZeroOfMulVec
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem mixedDisc_eq_zero_of_mulVec {D : ℕ} {A : Fin D → Matrix (Fin D) (Fin D) ℂ} {u : Fin D → ℂ} (hu : u ≠ 0)
    (hA : ∀ k, A k *ᵥ u = 0) : mixedDisc A = 0 := by
  unfold mixedDisc
  rw [Finset.sum_eq_zero, mul_zero]
  intro S _
  have hS : (∑ k ∈ S, A k) *ᵥ u = 0 :=
    Finset.sum_induction _ (fun M => M *ᵥ u = 0) (fun M N hM hN => by rw [add_mulVec, hM, hN, add_zero])
      (zero_mulVec u) fun k _ => hA k
  rw [Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hu, hS⟩, mul_zero]

theorem pointForm_holds.maDensity_eq_zero (hR : pointFormRank_holds.Statement) (hE : pointFormEuler_holds.Statement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {d n : ℕ}
    {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} {L' : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι'} (hv : IsBlockMap κ v)
    (hQ : IsArithVar (imageZ v P') d) (hdn : d < n + 1) (hL : ∀ j, IsSmoothHerm (L j))
    (hLL : ∀ j, IsPullHerm κ v (L j) (L' j))
    {Ψ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)} {y : Fin n → ℂ} {w : ((k : K') → ι' k) → ℂ}
    {γ : (Fin n → ℂ) → (Σ k', ι' k') → ℂ} (hγ : IsSheet P' Ψ y w γ) :
    maDensity (fun j y' => Real.log ((L' j).h (γ y'))) y = 0 := by
  set F : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y' p => γ y' (v p) with hF
  have hγa : AnalyticAt ℂ γ y := sheet_analyticAt osgood hγ
  have hFa : AnalyticAt ℂ F y := analyticAt_pi_iff.mpr fun p => analyticAt_coord hγa (v p)
  have hFy : ∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0 := blocks_ne_zero_restrict hv hγ.2.self_of_nhds.2.1.1
  have hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts (imageZ v P') := by
    filter_upwards [hγ.2] with y' h
    refine ⟨blocks_ne_zero_restrict hv h.2.1.1, fun f hf => ?_⟩
    have h0 := h.2.1.2 _ (Ideal.mem_comap.mp hf)
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h0
    exact h0
  obtain ⟨x, hx, c, hxc⟩ := hR K ι (imageZ v P') d n F y hQ (by omega) hFa hFQ
  have hpot : ∀ j, (fun y' => Real.log ((L' j).h (γ y'))) = fun y' => Real.log ((L j).h (F y')) :=
    fun j => funext fun y' => by rw [(hLL j).2]
  simp only [maDensity, hpot]
  rw [mixedDisc_eq_zero_of_mulVec (u := star x) (star_ne_zero.mpr hx)
    fun j => hE K ι (L j) n F y x c (hL j) hFa hFy hxc]
  simp

theorem pointForm_holds.proof (hR : pointFormRank_holds.Statement) (hE : pointFormEuler_holds.Statement) : pointForm_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d n L L' g hv _ hQ hdn hL hLL
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P' hΨ.choose (fun j z => Real.log ((L' j).h z)) g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · exact mul_eq_zero_of_right _ (pointForm_holds.maDensity_eq_zero hR hE hv hQ hdn hL hLL hγ.choose_spec)
      · rfl
    simp [h0]
  · rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PPFSecRed
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

noncomputable section

theorem PFSecRed.exists_form_not_mem {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {P : Ideal (MRing ι)} {n : ℕ} (hP : IsArithVar P n) (c : K → ℕ) :
    ∃ s : MRing ι, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog s c ∧ s ∉ P :=
  ⟨∏ k, (X ⟨k, (hP.2.1.2.2 k).choose⟩ : MRing ι) ^ c k, AvoidRing.isMultiHomog_coordProd _ c,
    AvoidRing.coordProd_not_mem hP.2.1.1 _ (fun k => (hP.2.1.2.2 k).choose_spec) c⟩

theorem PFSecRed.proof
    (hMult : ∀ (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)],
      MultilinStatement F ι)
    (hDim : FibreDimStatement) : PFSecRed.Statement := by
  intro I hI r hsec K _ ι _ K' _ ι' _ κ v P' d G J L L' N hv hP' hP hJ hL hL' hN

  let c : K' → ℕ := fun k => (-(N (Fin.last r)).a k).toNat
  let H : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι' := ReciprocityTheory.ChartRestriction.G.Geo.HermLine.sqMetric c
  let A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι' := (N (Fin.last r)).tensor H
  have hHs : IsSmoothHerm H := isSmoothHerm_sqMetric c
  have hAs : IsSmoothHerm A := isSmoothHerm_tensor (hN _) hHs
  let a : K' → ℕ := fun k => ((N (Fin.last r)).a k + c k).toNat
  have hAa : ∀ k, A.a k = a k := by
    intro k
    show (N (Fin.last r)).a k + ((-(N (Fin.last r)).a k).toNat : ℤ) =
      (((N (Fin.last r)).a k + ((-(N (Fin.last r)).a k).toNat : ℤ)).toNat : ℤ)
    omega
  have hHa : ∀ k, H.a k = c k := fun k => rfl
  obtain ⟨sA, hsA, hsAP⟩ := PFSecRed.exists_form_not_mem hP' a
  obtain ⟨sH, hsH, hsHP⟩ := PFSecRed.exists_form_not_mem hP' c
  have hsnoc : ∀ B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι', IsSmoothHerm B →
      ∀ j, IsSmoothHerm ((Fin.snoc (Fin.init N) B : Fin (r + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') j) := by
    intro B hB j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simpa using hB
    · rw [Fin.snoc_castSucc]; exact hN _
  have e1 := hsec K ι K' ι' κ v P' d G J L L' (Fin.snoc (Fin.init N) A) sA a hv hP' hP hJ hL hL'
    (hsnoc A hAs) (by simpa using hAa) hsA hsAP
  have e2 := hsec K ι K' ι' κ v P' d G J L L' (Fin.snoc (Fin.init N) H) sH c hv hP' hP hJ hL hL'
    (hsnoc H hHs) (by simpa using hHa) hsH hsHP

  have hM : ∀ j, IsSmoothHerm (Fin.append L' (Fin.init N) j) := by
    intro j
    induction j using Fin.addCases with
    | left i => rw [Fin.append_left]; exact IsPullHerm.isSmoothHerm hv (hL' i) (hL i)
    | right i => rw [Fin.append_right]; exact hN _
  have hadd := (hI K' ι').2.1 P' (d + r) (Fin.append L' (Fin.init N)) (N (Fin.last r)) H hP' hM (hN _) hHs
  rw [← Fin.append_snoc, ← Fin.append_snoc, ← Fin.append_snoc, Fin.snoc_init_self] at hadd

  have hV := hDim K ι K' ι' κ v P' d (r + 1) G hv hP' hP
  have hJadd := hMult G.Φ (FibreBlock κ) (fibreIdx ι' κ) J hJ (fibreIdeal κ G) (r + 1)
    (Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a)) (Fin.last r)
    (fibreDeg κ (N (Fin.last r)).a) (fibreDeg κ H.a) hV
  simp only [Fin.update_snoc_last] at hJadd
  have f0 : (fun j => fibreDeg κ (N j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp
  have f1 : (fun j => fibreDeg κ ((Fin.snoc (Fin.init N) A : Fin (r + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ (N (Fin.last r)).a + fibreDeg κ H.a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.snoc_last]; rfl
    · simp [Fin.init]
  have f2 : (fun j => fibreDeg κ ((Fin.snoc (Fin.init N) H : Fin (r + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι') j).a) =
      Fin.snoc (fun i => fibreDeg κ (N i.castSucc).a) (fibreDeg κ H.a) := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [Fin.init]
  rw [f1] at e1
  rw [f2] at e2
  have key : I K' ι' P' (d + (r + 1)) (Fin.append L' N) =
      I K' ι' P' (d + (r + 1)) (Fin.append L' (Fin.snoc (Fin.init N) A)) -
        I K' ι' P' (d + (r + 1)) (Fin.append L' (Fin.snoc (Fin.init N) H)) := by
    rw [eq_sub_iff_add_eq]
    exact hadd.symm
  rw [f0, key, e1, e2, hJadd]
  push_cast
  ring

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreFurther
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityMaximalSurjective.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∀ m : Ideal (regRing P), m.IsMaximal →
    ∃ W : Ideal (MRing ι), IsClosedPt W ∧ P ≤ W ∧ ∀ x ∈ m, ∀ z ∈ locRing P W,
      ((x : funField P) : FractionRing (MRing ι ⧸ P)) * z ≠ 1

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreMore
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityMaximalSpectrum.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)),
    IsArithVar P 1 → ∃ e : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} ≃ MaximalSpectrum (regRing P),
      ∀ (W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}) (y : FractionRing (MRing ι ⧸ P)),
        y ∈ locRing P W.1 ↔ ∃ x s : regRing P, s ∉ (e W).asIdeal ∧
          y * ((s : funField P) : FractionRing (MRing ι ⧸ P)) = ((x : funField P) : FractionRing (MRing ι ⧸ P))

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreBis
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocal.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (b : regRing P),
    IsArithVar P 1 → b ≠ 0 →
    {W | IsClosedPt W ∧ P ≤ W ∧
        Nat.card (locRing P W ⧸ locIdeal P W ((b : funField P) : FractionRing (MRing ι ⧸ P))) ≠ 1}.Finite ∧
      ∑ᶠ W ∈ {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W},
          Real.log (Nat.card (locRing P W ⧸ locIdeal P W ((b : funField P) : FractionRing (MRing ι ⧸ P)))) =
        Real.log (Nat.card (regRing P ⧸ Ideal.span {b}))

end

end GroundTheory.Heights₂.Heights.Inter
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.ArIntMul
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem arInt_mul (hInt : PtsIntegrableStatement) {P : Ideal (MRing ι)} {n : ℕ}
    (hP : IsArithVar P (n + 1)) {L : Fin n → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hL : ∀ j, IsSmoothHerm (L j))
    {A B : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (hA : IsSmoothHerm A) (hB : IsSmoothHerm B) {s t : MRing ι}
    (hs : IsSectionOn P A s) (ht : IsSectionOn P B t) :
    arInt P (s * t) (A.tensor B) L = arInt P s A L + arInt P t B L := by
  obtain ⟨a, -, hsa, hsP⟩ := id hs
  obtain ⟨b, -, htb, htP⟩ := id ht
  show ptsIntegral P (pot L) _ = ptsIntegral P (pot L) _ + ptsIntegral P (pot L) _
  unfold ptsIntegral
  split_ifs with hΨ
  · have hΨg : IsGoodProj P hΨ.choose := hΨ.choose_spec
    unfold ptsIntegralAt
    rw [← integral_add (hInt K ι P n _ L A s hP hΨg hL hA hs) (hInt K ι P n _ L B t hP hΨg hL hB ht)]
    refine integral_congr_ae ?_
    filter_upwards [ae_eval_ne_zero hP hΨg ⟨a, hsa⟩ hsP, ae_eval_ne_zero hP hΨg ⟨b, htb⟩ htP]
      with y hys hyt
    rw [← finsum_mem_add_distrib' ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left)
      ((fibreFinite K ι P n _ hP hΨg y).subset Set.inter_subset_left)]
    refine finsum_mem_congr rfl fun w _ ↦ ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hsh := hγ.choose_spec.2.self_of_nhds
      set z := hγ.choose y
      have hz : z ∈ mcPts P := hsh.2.1
      have hs0 := norm_pos_iff.mpr (hys z hz hsh.2.2)
      have ht0 := norm_pos_iff.mpr (hyt z hz hsh.2.2)
      have hA0 := A.pos z hz.1
      have hB0 := B.pos z hz.1
      rw [← add_mul]
      congr 1
      show Real.log (‖eval z (map (Int.castRingHom ℂ) (s * t))‖ / (A.h z * B.h z)) =
        Real.log (‖eval z (map (Int.castRingHom ℂ) s)‖ / A.h z) +
          Real.log (‖eval z (map (Int.castRingHom ℂ) t)‖ / B.h z)
      rw [map_mul, map_mul, norm_mul, mul_div_mul_comm]
      exact Real.log_mul (div_pos hs0 hA0).ne' (div_pos ht0 hB0).ne'
    · simp
  · simp

theorem RMul.proof (hInt : PtsIntegrableStatement) : RMulStatement := by
  intro K _ ι _ I P n L A B s t hP hL hA hB hs ht
  obtain ⟨-, -, -, hsP⟩ := id hs
  obtain ⟨-, -, -, htP⟩ := id ht
  rw [recR_eq, recR_eq, recR_eq, cycR_mul I hP.2.1.1 L hsP htP, arInt_mul hInt hP hL hA hB hs ht]
  ring

end GroundTheory.Heights₂.Heights.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagPivotIdentity
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace FlagPivotIdentity

variable {R : Type} [CommRing R] {n : ℕ}

def leadDet (M : Matrix (Fin n) (Fin n) R) (k : ℕ) : R :=
  if h : k ≤ n then (M.submatrix (Fin.castLE h) (Fin.castLE h)).det else 0

def pivotCof (M : Matrix (Fin n) (Fin n) R) {a : ℕ} (ha : a + 1 ≤ n) (i : Fin (a + 1)) : R :=
  (-1) ^ ((i : ℕ) + a) * (M.submatrix (Fin.castLE ha ∘ i.succAbove) (Fin.castLE (by omega))).det

theorem pivotMinor_eq_sum (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) (b : Fin n) :
    pivotMinor M a b = ∑ i : Fin (a + 1),
      pivotCof M (a := a) (by have := a.2; omega) i * M (Fin.castLE (by have := a.2; omega) i) b := by
  unfold pivotMinor
  rw [Matrix.det_succ_column _ (Fin.last a)]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hcol : pivotCols a b ∘ (Fin.last (a : ℕ)).succAbove = Fin.castLE (by have := a.2; omega) := by
    funext c
    rw [Fin.succAbove_last]
    ext
    simp [pivotCols]
  have hlast : pivotCols a b (Fin.last a) = b := by simp [pivotCols]
  simp only [pivotCof, Matrix.submatrix_apply, Matrix.submatrix_submatrix, Fin.val_last, hlast, hcol]
  ring

def pivotCoeff (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) : Matrix (Fin (j + 1)) (Fin (j + 1)) R :=
  Matrix.of fun a i =>
    if h : (i : ℕ) ≤ a then pivotCof M (a := a) (by have := j.2; have := a.2; omega) ⟨i, by omega⟩ else 0

theorem sum_castLE {m k : ℕ} (h : k ≤ m) (f : Fin m → R) (hf : ∀ i : Fin m, k ≤ (i : ℕ) → f i = 0) :
    ∑ i : Fin k, f (Fin.castLE h i) = ∑ i : Fin m, f i := by
  have e : ∑ i : Fin k, f (Fin.castLE h i) = ∑ i ∈ Finset.univ.map (Fin.castLEEmb h), f i := by
    rw [Finset.sum_map]; rfl
  rw [e]
  refine Finset.sum_subset (Finset.subset_univ _) fun i _ hi => hf i ?_
  by_contra hlt
  push Not at hlt
  exact hi (Finset.mem_map.2 ⟨⟨i, hlt⟩, Finset.mem_univ _, Fin.ext rfl⟩)

theorem pivotMatrix_rows (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) {m : ℕ} (e : Fin m → Fin n) :
    (pivotMatrix M).submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e =
      pivotCoeff M j * M.submatrix (Fin.castLE (n := (j : ℕ) + 1) (by have := j.2; omega)) e := by
  ext a b
  have ha : (a : ℕ) < n - 1 := by have := j.2; have := a.2; omega
  rw [Matrix.mul_apply]
  simp only [Matrix.submatrix_apply, pivotMatrix, Matrix.of_apply, Fin.val_castLE, dif_pos ha]
  rw [pivotMinor_eq_sum M ⟨a, ha⟩ (e b)]
  rw [← sum_castLE (m := (j : ℕ) + 1) (k := (a : ℕ) + 1) (Nat.succ_le_of_lt a.2)]
  · refine Finset.sum_congr rfl fun i _ => ?_
    have hi : ((Fin.castLE (n := (a : ℕ) + 1) (m := (j : ℕ) + 1) (Nat.succ_le_of_lt a.2) i) : ℕ) ≤ a :=
      Nat.lt_succ_iff.mp i.2
    simp only [pivotCoeff, Matrix.of_apply]
    rw [dif_pos hi]
    rfl
  · intro i hi
    have : ¬ ((i : ℕ) ≤ a) := by omega
    simp only [pivotCoeff, Matrix.of_apply]
    rw [dif_neg this, zero_mul]

theorem pivotCoeff_isLowerTriangular (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) :
    (pivotCoeff M j).IsLowerTriangular := by
  intro a i hai
  have hai' : (a : ℕ) < i := OrderDual.toDual_lt_toDual.mp hai
  have : ¬ ((i : ℕ) ≤ a) := by omega
  simp only [pivotCoeff, Matrix.of_apply, dif_neg this]

theorem pivotCoeff_diag (M : Matrix (Fin n) (Fin n) R) (j : Fin (n - 1)) (a : Fin (j + 1)) :
    pivotCoeff M j a a = leadDet M a := by
  have ha : (a : ℕ) ≤ n := by have := j.2; have := a.2; omega
  simp only [pivotCoeff, Matrix.of_apply, dif_pos le_rfl, pivotCof, leadDet, dif_pos ha]
  have hl : (⟨a, Nat.lt_succ_self _⟩ : Fin ((a : ℕ) + 1)) = Fin.last a := rfl
  rw [hl, Fin.succAbove_last, Even.neg_one_pow ⟨a, rfl⟩, one_mul]
  rfl

theorem leadMinor_eq (M : Matrix (Fin n) (Fin n) R) (a : Fin (n - 1)) :
    leadMinor M a = leadDet M (a + 1) := by
  have h : (a : ℕ) + 1 ≤ n := by have := a.2; omega
  unfold leadMinor pivotMinor leadDet
  rw [dif_pos h]
  congr 2
  funext c
  rcases c with ⟨c, hc⟩
  ext
  simp only [pivotCols, Fin.castLE_mk]
  split_ifs <;> (simp; try omega)

theorem leadDet_zero (M : Matrix (Fin n) (Fin n) R) : leadDet M 0 = 1 := by
  simp [leadDet]

theorem proof : FlagPivotIdentity.Statement := by
  intro R _ n M j S
  have hP : flagMinor (pivotMatrix M) j S =
      (∏ k ∈ Finset.range j, leadDet M (k + 1)) * flagMinor M j S := by
    unfold flagMinor
    rw [pivotMatrix_rows, Matrix.det_mul,
      Matrix.det_of_isLowerTriangular _ (pivotCoeff_isLowerTriangular M j)]
    simp only [pivotCoeff_diag]
    rw [Fin.prod_univ_eq_prod_range (fun k => leadDet M k), Finset.prod_range_succ', leadDet_zero, mul_one]
  have hI : ∏ a ∈ Finset.Iic j, leadMinor M a = ∏ k ∈ Finset.range (j + 1), leadDet M (k + 1) := by
    simp only [leadMinor_eq]
    have e := Finset.prod_map (Finset.Iic j) Fin.valEmbedding (fun k => leadDet M (k + 1))
    rw [Fin.map_valEmbedding_Iic] at e
    rw [← show (Finset.Iic (j : ℕ)) = Finset.range (j + 1) by ext; simp, e]
    rfl
  rw [hP, hI, Finset.prod_range_succ, leadMinor_eq]
  ring

end FlagPivotIdentity

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

section -- merged from GroundTheory.HeightsAndTheta.Heights.Intersections.PDeSlotAdd
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.AnForm.M Filter Topology

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


omit [∀ k, Fintype (ι k)] in
theorem ptsIntegral_eq_zero_of_vanish (P : Ideal (MRing ι)) {e : ℕ}
    (φ : Fin e → ((Σ k, ι k) → ℂ) → ℝ) {g : ((Σ k, ι k) → ℂ) → ℝ}
    (hg : ∀ z ∈ mcPts P, g z = 0) : ptsIntegral P φ g = 0 := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P hΨ.choose φ g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · rw [hg _ hγ.choose_spec.2.self_of_nhds.2.1, zero_mul]
      · rfl
    simp [h0]
  · rfl

theorem ptsIntegral_update_tensor (hE : ResExistsStatement) {P : Ideal (MRing ι)} {e : ℕ}
    (hP : IsArithVar P (e + 1)) {L : Fin e → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι} (j : Fin e) {M N A : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι}
    {s : MRing ι} (hL : ∀ i, IsSmoothHerm (L i)) (hM : IsSmoothHerm M) (hN : IsSmoothHerm N)
    (hA : IsSmoothHerm A) (hs : IsSectionOn P A s) :
    ptsIntegral P (pot (Function.update L j (M.tensor N))) (logNorm A s) =
      ptsIntegral P (pot (Function.update L j M)) (logNorm A s) +
        ptsIntegral P (pot (Function.update L j N)) (logNorm A s) := by
  obtain ⟨m, rfl⟩ : ∃ m, e = m + 1 := ⟨e - 1, by have := j.pos; omega⟩
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  set T : Fin m → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι := fun i => L (Equiv.swap 0 j i.succ) with hT
  have hT' : ∀ i, IsSmoothHerm (T i) := fun i => hL _
  have hU : ∀ X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, IsSmoothHerm X → ∀ i, IsSmoothHerm (Function.update L j X i) := by
    intro X hX i
    rcases eq_or_ne i j with rfl | h
    · simpa using hX
    · rw [Function.update_of_ne h]
      exact hL i
  have hC : ∀ X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, IsSmoothHerm X →
      ∀ i, IsSmoothHerm ((Fin.cons X T : Fin (m + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) i) :=
    fun X hX i => Fin.cases hX hT' i
  have key : ∀ X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, IsSmoothHerm X →
      ptsIntegral P (pot (Function.update L j X)) (logNorm A s) =
        mInt R.A (Fin.cons (potOf R X) fun i => potOf R (T i))
          (fun x => logNorm A s (R.lift x x)) := by
    intro X hX
    rw [ptsIntegral_eq_mInt' hE resBridge R hP (hU X hX) hA hs, ← potOf_cons R X T,
      ← mIntSymm R.A (fun i => potOf R (Function.update L j X i)) (Equiv.swap 0 j)]
    congr 1
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp
    · have hne : Equiv.swap 0 j i.succ ≠ j := by
        intro h
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact Fin.succ_ne_zero _ h
      simp only [Function.comp_apply, Fin.cons_succ, hT, Function.update_of_ne hne]
  rw [key _ (isSmoothHerm_tensor hM hN), key M hM, key N hN]
  have hΦ : ∀ i, IsPotential R.A (potOf R (T i)) := fun i => isPotential_potOf R (hT' i)
  have hPM := isPotential_potOf R hM
  have hPN := isPotential_potOf R hN
  have e1 : mInt R.A (Fin.cons (potOf R (M.tensor N)) fun i => potOf R (T i))
      (fun x => logNorm A s (R.lift x x)) =
      mInt R.A (Fin.cons (potOf R M + potOf R N) fun i => potOf R (T i))
        (fun x => logNorm A s (R.lift x x)) := by
    refine ReciprocityTheory.ChartRestriction.G.Geo.mInt_congr _ (locDens_cons_congr _ _ fun j y hy =>
      germ_of_eqOn R (fun x z hz => ?_) j y hy) fun _ => rfl
    have hm := (R.mem x z hz).1
    show Real.log (M.h (R.lift x z) * N.h (R.lift x z)) =
      Real.log (M.h (R.lift x z)) + Real.log (N.h (R.lift x z))
    exact Real.log_mul (M.pos _ hm).ne' (N.pos _ hm).ne'
  have hI : ∀ X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι, IsSmoothHerm X →
      MIntegrable R.A (Fin.cons (potOf R X) fun i => potOf R (T i))
        (fun x => logNorm A s (R.lift x x)) := by
    intro X hX
    rw [← potOf_cons R X T]
    exact brIntegrable R _ A s hP (hC X hX) hA hs
  rw [e1]
  exact mIntAdd R.A _ _ _ hPM hPN hΦ _ (hI M hM) (hI N hN)

theorem DeSlotAdd.proof (hE : ResExistsStatement) : DeSlotAdd.Statement := by
  intro K _ ι _ P n L j M N A A' s s' hP hL hM hN hA hA' hs hs' _

  have hZ : ∀ (B C : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) (t : MRing ι), IsSmoothHerm B → IsSmoothHerm C →
      IsSectionOn P C t →
      ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j (M.tensor N))))
          (logNorm C t) =
        ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j M)))
            (logNorm C t) +
          ptsIntegral P (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j N)))
            (logNorm C t) := by
    intro B C t hB hC ht
    have hc : ∀ X : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι,
        (Fin.cons (fun z => Real.log (B.h z)) (pot (Function.update L j X)) :
          Fin (n + 1) → ((Σ k, ι k) → ℂ) → ℝ) =
          pot (Function.update (Fin.cons B L : Fin (n + 1) → ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι) j.succ X) := by
      intro X
      rw [← Fin.cons_update]
      funext i
      exact Fin.cases rfl (fun i => rfl) i
    rw [hc, hc, hc]
    exact ptsIntegral_update_tensor hE hP j.succ (fun i => Fin.cases hB hL i) hM hN hC ht

  have hW : ∀ (t t' : MRing ι) (C C' : ReciprocityTheory.ChartRestriction.G.Geo.HermLine ι), IsSectionOn P C t → IsSmoothHerm C' →
      IsSectionOn P C' t' →
      (∑ᶠ (W) (_ : W ∈ divSupp P t ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
          ptsIntegral W (pot (Function.update L j (M.tensor N))) (logNorm C' t')) =
        (∑ᶠ (W) (_ : W ∈ divSupp P t ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j M)) (logNorm C' t')) +
          (∑ᶠ (W) (_ : W ∈ divSupp P t ∧ IsHorizontal W), (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j N)) (logNorm C' t')) := by
    intro t t' C C' ht hC' ht'
    have hfin : {W | W ∈ divSupp P t ∧ IsHorizontal W}.Finite :=
      (divSupp_finite P t).subset fun W hW => hW.1
    have hpt : ∀ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W},
        (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j (M.tensor N))) (logNorm C' t') =
          (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
              ptsIntegral W (pot (Function.update L j M)) (logNorm C' t') +
            (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
              ptsIntegral W (pot (Function.update L j N)) (logNorm C' t') := by
      intro W hW
      rw [← mul_add]
      congr 1
      have hWa : IsArithVar W (n + 1) := (divSuppArith K ι P (n + 1) C t W hP ht hW.1).1 hW.2
      by_cases hsW : t' ∈ W
      · have h0 : ∀ z ∈ mcPts W, logNorm C' t' z = 0 := by
          intro z hz
          simp [logNorm, hz.2 t' hsW]
        rw [ptsIntegral_eq_zero_of_vanish W _ h0, ptsIntegral_eq_zero_of_vanish W _ h0,
          ptsIntegral_eq_zero_of_vanish W _ h0, add_zero]
      · obtain ⟨a, ha, hta, -⟩ := ht'
        exact ptsIntegral_update_tensor hE hWa j hL hM hN hC' ⟨a, ha, hta, hsW⟩
    show ∑ᶠ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W}, (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
          ptsIntegral W (pot (Function.update L j (M.tensor N))) (logNorm C' t') =
        ∑ᶠ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W}, (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j M)) (logNorm C' t') +
          ∑ᶠ W ∈ {W | W ∈ divSupp P t ∧ IsHorizontal W}, (multAt (P ⊔ Ideal.span {t}) W : ℝ) *
            ptsIntegral W (pot (Function.update L j N)) (logNorm C' t')
    rw [← finsum_mem_add_distrib hfin]
    exact finsum_mem_congr rfl hpt
  unfold De
  rw [hW s s' A A' hs hA' hs', hW s' s A' A hs' hA hs, hZ A' A s hA' hA hs, hZ A A' s' hA hA' hs']
  ring

end GroundTheory.Heights₂.Heights.Inter
end
end
