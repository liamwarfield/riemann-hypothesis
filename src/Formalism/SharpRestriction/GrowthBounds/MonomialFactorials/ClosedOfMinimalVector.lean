module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfCoefficientFunction
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.OrthBasisLatOf
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.BlockValuationZpOfLatticeInclusion
public import Formalism.MahlerMeasure.MahlerMeasureProofs.GamDeg
public import Formalism.MahlerMeasure.MahlerMeasureProofs.PhiInt

@[expose] public section

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfSplittingMatrix
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfOrthogonalSplitting
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.IntegralityFromMetricOfOrthBasisLat
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfOrthogonalBasis
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ClosedOfOrthogonalLattice
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SymmetryWindowOnAdmissible
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.SymmetryWindowLevelDimOnAdmissible
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestLjjFinProved
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Formalism.MainNotions.G Formalism.MainNotions.G.CountingStatementReduction

section Lvl

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem mem_xiMons_of (n : ℕ) (m : Formalism.GM.M.BVar N r G.T.t →₀ ℕ)
    (hsupp : ∀ v ∈ m.support, ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c)
    (hsum : ∑ c, m (Formalism.GM.M.xiVar N r G.T.t c) = n) : m ∈ xiMons (r := r) G n := by
  classical
  unfold xiMons
  rw [Finset.mem_image]
  refine ⟨fun c => m (Formalism.GM.M.xiVar N r G.T.t c), (CountingStatementReduction.mem_Ev _).2 hsum, ?_⟩
  ext v
  rw [Finsupp.finsetSum_apply]
  by_cases hv : ∃ c, v = Formalism.GM.M.xiVar N r G.T.t c
  · obtain ⟨c, rfl⟩ := hv
    rw [Finset.sum_eq_single c]
    · simp
    · intro d _ hd
      rw [Finsupp.single_apply, if_neg]
      intro h
      exact hd (xiVar_inj G h)
    · intro h; exact absurd (Finset.mem_univ c) h
  · have h0 : m v = 0 := by
      by_contra hne
      exact hv (hsupp v (Finsupp.mem_support_iff.2 hne))
    rw [h0]
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro h
    exact hv ⟨c, h.symm⟩

theorem xi_mem_spanZ (n : ℕ) (g : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (hg : g ∈ Formalism.GM.M.XiPolZ p N r G.T.t n) :
    g ∈ Submodule.span ℤ_[p] ((fun m => (monomial m (1 : ℚ_[p]))) '' (xiMons (r := r) G n : Set _)) := by
  classical
  obtain ⟨hs, hint⟩ := Submodule.mem_inf.1 hg
  rw [Submodule.restrictScalars_mem, MvPolynomial.mem_restrictSupport_iff] at hs
  obtain ⟨g0, hg0⟩ := hint
  have hc : ∀ m, AddMonoidAlgebra.coeff g m = algebraMap ℤ_[p] ℚ_[p] (AddMonoidAlgebra.coeff g0 m) := by
    intro m
    rw [← hg0]
    simp [MvPolynomial.coeff_map]
  rw [g.as_sum]
  refine Submodule.sum_mem _ fun m hm => ?_
  obtain ⟨hsupp, hsum⟩ := hs hm
  have hmono : monomial m (AddMonoidAlgebra.coeff g m) = (AddMonoidAlgebra.coeff g0 m) • monomial m (1 : ℚ_[p]) := by
    rw [hc m, smul_monomial, Algebra.smul_def, mul_one]
  rw [hmono]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨m, mem_xiMons_of G n m hsupp hsum, rfl⟩)

theorem Ljj_fg (j : Fin G.T.t → ℕ) (jp : ℕ) : (Ljj p (r := r) G j jp).FG := by
  classical
  obtain ⟨A, hA⟩ := Formalism.GM.TM.yZ_fg (p := p) (r := r) (G.lettersAt j jp) G.T.J G.T.thr
  let S : Set (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :=
    (fun am : _ × _ => rename (Formalism.GM.M.chainEmb N r G.T.t) am.1 * monomial am.2 (1 : ℚ_[p])) ''
      ((A : Set _) ×ˢ (xiMons (r := r) G (G.B - jp) : Set _))
  have hS : S.Finite := (A.finite_toSet.prod (xiMons (r := r) G (G.B - jp)).finite_toSet).image _
  have hle : Ljj p (r := r) G j jp ≤ Submodule.span ℤ_[p] S := by
    unfold Ljj
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, g, hg, rfl⟩
    have hy' : y ∈ Submodule.span ℤ_[p] (A : Set _) := by rw [hA]; exact hy
    have hg' := xi_mem_spanZ G (G.B - jp) g hg
    clear hy hg
    induction hy' using Submodule.span_induction with
    | mem a ha =>
      induction hg' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨m, hm, rfl⟩ := hx
        exact Submodule.subset_span ⟨(a, m), ⟨ha, hm⟩, rfl⟩
      | zero => simp
      | add u v _ _ hu hv => rw [mul_add]; exact Submodule.add_mem _ hu hv
      | smul c u _ hu =>
        rw [mul_smul_comm]
        exact Submodule.smul_mem _ c hu
    | zero => simp
    | add u v _ _ hu hv => rw [map_add (f := _), add_mul]; exact Submodule.add_mem _ hu hv
    | smul c u _ hu =>
      have : rename (Formalism.GM.M.chainEmb N r G.T.t) (c • u) = c • rename (Formalism.GM.M.chainEmb N r G.T.t) u := by
        rw [← algebraMap_smul ℚ_[p] c u, ← algebraMap_smul ℚ_[p] c (rename (Formalism.GM.M.chainEmb N r G.T.t) u)]
        exact map_smul (rename (Formalism.GM.M.chainEmb N r G.T.t)) _ _
      rw [this, smul_mul_assoc]
      exact Submodule.smul_mem _ c hu
  exact Submodule.FG.of_le (Submodule.fg_span hS) hle

end Lvl

section Lvl2

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem ljjFin_gen (j : Fin G.T.t → ℕ) (jp : ℕ) :
    (Ljj p (r := r) G j jp).FG ∧
    ∃ W : Submodule ℚ_[p] (MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]),
      FiniteDimensional ℚ_[p] W ∧ ∀ u ∈ Ljj p (r := r) G j jp, u ∈ W :=
  ⟨Ljj_fg G j jp, _, Ljj_span_fd G j jp, fun _ hu => Submodule.subset_span hu⟩

end Lvl2

theorem restLjjFin_proved (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestLjjFin C0 CE1 CE2 X :=
  fun _ _ aTop _ x _ => ljjFin_gen (p := X.p) (r := X.r) (gB C0 CE1 CE2 X aTop 0 x.1) x.2.1 x.2.2

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def SymmetryWindowLevelDimConditions (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X →
    RestSymm C0 CE1 CE2 X ∧ RestWin C0 CE1 CE2 X CM ∧ RestLvlDim C0 CE1 CE2 X

def SymmetryWindowLevelDimOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → SymmetryWindowLevelDimConditions C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem symmetric_finite_of_windows (D : Formalism.BasicNotions.D7) (h : SymmetryWindowLevelDimOnAdmissible D) : SymmetryFinitenessWindowLevelDimOnAdmissible D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b, c⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, restLjjFin_proved C0 CE1 CE2 X, b, c⟩) h

theorem closed_of_symmetric_windows (D : Formalism.BasicNotions.D7) (hF : RestFunY) (hO : OrthLat) (h : SymmetryWindowLevelDimOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_coefficient_function D hF hO (symmetric_finite_of_windows D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LvlDimCondition
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LvlDimGen
section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.LiRenameMon
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.GM.M.SSD

section LI

variable {σ τ K : Type} [Field K] [DecidableEq σ] (e : τ → σ) (he : Function.Injective e)

def decode (M : Finset (σ →₀ ℕ)) : MvPolynomial σ K →ₗ[K] (M → MvPolynomial τ K) where
  toFun Q := fun β => Formalism.GM.M.SSD.kap _ (F_inj e he 0 (β : σ →₀ ℕ)) Q
  map_add' Q Q' := by funext β; exact kap_add _ _ Q Q'
  map_smul' c Q := by funext β; exact kap_smul _ _ c Q

theorem decode_gen (M : Finset (σ →₀ ℕ)) (hM : ∀ β ∈ M, ∀ x, β (e x) = 0) (y : MvPolynomial τ K) (β : M) :
    decode e he M (rename e y * monomial (β : σ →₀ ℕ) 1) = Pi.single β y := by
  funext γ
  have h1 : rename e y * monomial (β : σ →₀ ℕ) (1 : K) = monomial 0 1 * rename e y * monomial (β : σ →₀ ℕ) 1 := by
    rw [← MvPolynomial.C_apply, MvPolynomial.C_1, one_mul]
  have hg : ∀ w ∈ (monomial (β : σ →₀ ℕ) (1 : K)).support, ∀ x, w (e x) = 0 := by
    intro w hw x
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_monomial] at hw
    split_ifs at hw with h
    · rw [← h]
      exact hM _ β.2 x
    · exact absurd rfl hw
  show Formalism.GM.M.SSD.kap _ (F_inj e he 0 (γ : σ →₀ ℕ)) (rename e y * monomial (β : σ →₀ ℕ) 1) = (Pi.single β y : M → MvPolynomial τ K) γ
  rw [h1, kap_gen e he 0 (γ : σ →₀ ℕ) (hM _ γ.2) y _ hg, MvPolynomial.coeff_monomial, Pi.single_apply]
  by_cases h : γ = β
  · subst h
    simp
  · rw [if_neg h, if_neg (fun h' => h (Subtype.ext h'.symm))]
    exact zero_smul K y

include he in
theorem li_rename_mon (M : Finset (σ →₀ ℕ)) (hM : ∀ β ∈ M, ∀ x, β (e x) = 0) {ι : Type} (b : ι → MvPolynomial τ K)
    (hb : LinearIndependent K b) :
    LinearIndependent K (fun q : (Σ _ : M, ι) => rename e (b q.2) * monomial ((q.1 : σ →₀ ℕ)) 1) := by
  apply LinearIndependent.of_comp (decode e he M)
  have h1 : (decode e he M) ∘ (fun q : (Σ _ : M, ι) => rename e (b q.2) * monomial ((q.1 : σ →₀ ℕ)) 1) =
      (Finsupp.linearEquivFunOnFinite K (MvPolynomial τ K) M) ∘
        (fun q : (Σ _ : M, ι) => Finsupp.single q.1 (b q.2)) := by
    funext q
    simp only [Function.comp_apply, Finsupp.linearEquivFunOnFinite_single]
    exact decode_gen e he M hM (b q.2) q.1
  rw [h1]
  first
  | exact (Finsupp.linearIndependent_single (fun _ : M => b) (fun _ => hb)).map' _ (LinearEquiv.ker _)
  | exact (Finsupp.linearIndependent_single (f := fun _ : M => b) (fun _ => hb)).map' _ (LinearEquiv.ker _)
  | exact (Finsupp.linearIndependent_single (v := fun _ : M => b) (fun _ => hb)).map' _ (LinearEquiv.ker _)


set_option maxHeartbeats 800000 in
theorem li_mul_left {ι : Type} (F : MvPolynomial σ K) (hF : F ≠ 0) (v : ι → MvPolynomial σ K) (hv : LinearIndependent K v) :
    LinearIndependent K (fun i => F * v i) := by
  have hinj : Function.Injective (LinearMap.mulLeft K F) := by
    intro a c h
    rw [LinearMap.mulLeft_apply, LinearMap.mulLeft_apply] at h
    exact mul_left_cancel₀ hF h
  have hfun : (fun i => F * v i) = (LinearMap.mulLeft K F) ∘ v := by
    funext i
    rw [Function.comp_apply, LinearMap.mulLeft_apply]
  rw [hfun]
  exact hv.map' _ (LinearMap.ker_eq_bot.mpr hinj)

end LI

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

def preF (j : Fin G.T.t → ℕ) (jp : ℕ) : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p] :=
  (∏ i, G.Ehat p (r := r) i ^ j i) * G.Eplus p (r := r) ^ jp *
    (∏ i, X (Formalism.GM.M.scalZ N r G.T.t (Fin.castSucc i)) ^ G.T.z i) * X (Formalism.GM.M.scalZ N r G.T.t (Fin.last G.T.t)) ^ G.zPlus

theorem lvlDim_gen (j : Fin G.T.t → ℕ) (jp : ℕ) (hpre : preF (p := p) (r := r) G j jp ≠ 0)
    (hden : ∀ y ∈ Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr, ∃ c : ℤ_[p], c ≠ 0 ∧
      ((c : ℚ_[p]) • y) ∈ Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr)
    (hfd : FiniteDimensional ℚ_[p] (Submodule.span ℚ_[p] (G.gens p (r := r) j jp)))
    (hM : ∀ β ∈ xiMons (r := r) G (G.B - jp), ∀ x, β (Formalism.GM.M.chainEmb N r G.T.t x) = 0)
    (hxi : ∀ β ∈ xiMons (r := r) G (G.B - jp), (monomial β (1 : ℚ_[p])) ∈ Formalism.GM.M.XiPolZ p N r G.T.t (G.B - jp)) :
    dimY p (r := r) G j jp * dXi r (G.B - jp) ≤
      Module.finrank ℚ_[p] (Submodule.span ℚ_[p] (G.gens p (r := r) j jp)) := by
  classical
  set Yq := Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr with hYq
  have : FiniteDimensional ℚ_[p] (Formalism.GM.M.Pol p r (G.lettersAt j jp)) :=
    Formalism.CountingSumsFrames.pol_finiteDimensional (p := p) (G.lettersAt j jp)
  have : FiniteDimensional ℚ_[p] Yq := Submodule.finiteDimensional_of_le (inf_le_left)
  let b := Module.finBasis ℚ_[p] Yq
  choose c hc0 hcY using fun a => hden (b a) (b a).2
  have hc0' : ∀ a, (c a : ℚ_[p]) ≠ 0 := fun a h => hc0 a (PadicInt.coe_eq_zero.1 h)
  let w : Fin (Module.finrank ℚ_[p] Yq) → ℚ_[p]ˣ := fun a => Units.mk0 _ (hc0' a)
  have hb0 : LinearIndependent ℚ_[p] (fun a => ((b a : Yq) : MvPolynomial (Fin N × Fin r) ℚ_[p])) :=
    b.linearIndependent.map' Yq.subtype (Submodule.ker_subtype _)
  have hb' : LinearIndependent ℚ_[p] (fun a => (c a : ℚ_[p]) • ((b a : Yq) : MvPolynomial (Fin N × Fin r) ℚ_[p])) :=
    hb0.units_smul w
  have hinj : Function.Injective (Formalism.GM.M.chainEmb N r G.T.t) := by
    intro x y h
    simp only [Formalism.GM.M.chainEmb, Sum.inl.injEq, Prod.mk.injEq] at h
    exact Prod.ext (Fin.castSucc_injective _ h.1) h.2
  have hli := li_mul_left (preF (p := p) (r := r) G j jp) hpre _
    (li_rename_mon (Formalism.GM.M.chainEmb N r G.T.t) hinj (xiMons (r := r) G (G.B - jp)) hM _ hb')
  have hmem : ∀ q : (Σ _ : xiMons (r := r) G (G.B - jp), Fin (Module.finrank ℚ_[p] Yq)),
      preF (p := p) (r := r) G j jp * (rename (Formalism.GM.M.chainEmb N r G.T.t)
        ((c q.2 : ℚ_[p]) • ((b q.2 : Yq) : MvPolynomial (Fin N × Fin r) ℚ_[p])) * monomial (q.1 : _ →₀ ℕ) 1) ∈
        G.gens p (r := r) j jp := by
    intro q
    refine ⟨_, hcY q.2, monomial (q.1 : _ →₀ ℕ) 1, hxi _ q.1.2, ?_⟩
    unfold preF
    ring
  let v : (Σ _ : xiMons (r := r) G (G.B - jp), Fin (Module.finrank ℚ_[p] Yq)) →
      Submodule.span ℚ_[p] (G.gens p (r := r) j jp) := fun q => ⟨_, Submodule.subset_span (hmem q)⟩
  have hv : LinearIndependent ℚ_[p] v := LinearIndependent.of_comp (Submodule.subtype _) hli
  have hcard := hv.fintype_card_le_finrank
  rw [Fintype.card_sigma] at hcard
  simp only [Fintype.card_fin, Finset.sum_const, Finset.card_univ, smul_eq_mul, Fintype.card_coe] at hcard
  rw [card_xiMons_eq] at hcard
  unfold dimY
  rw [mul_comm]
  exact hcard

end Gen

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Gen

variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem preF_ne_zero (j : Fin G.T.t → ℕ) (jp : ℕ) : preF (p := p) (r := r) G j jp ≠ 0 := by
  classical
  obtain ⟨s, hs1, hs2⟩ := Formalism.GM.M.good_pre (p := p) (r := r) G j jp
  have hpre : Formalism.GM.M.pre (p := p) (r := r) G j jp ≠ 0 := by
    intro h0
    rw [h0, zero_sub] at hs2
    have hmem : s ∈ (-(monomial s (1 : ℚ_[p]))).support := by
      rw [support_neg, support_monomial, if_neg one_ne_zero]
      exact Finset.mem_singleton_self s
    exact (hs2 s hmem).2 hs1
  have e : preF (p := p) (r := r) G j jp =
      Formalism.GM.M.pre (p := p) (r := r) G j jp * monomial (Formalism.GM.M.zmS G) 1 := by
    rw [← Formalism.GM.M.zmon_eq]
    unfold preF Formalism.GM.M.pre
    ring
  rw [e]
  exact mul_ne_zero hpre (by rw [Ne, monomial_eq_zero]; exact one_ne_zero)

theorem den_Y (j : Fin G.T.t → ℕ) (jp : ℕ) :
    ∀ y ∈ Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr, ∃ c : ℤ_[p], c ≠ 0 ∧
      ((c : ℚ_[p]) • y) ∈ Formalism.GM.M.YZ p (r := r) (G.lettersAt j jp) G.T.J G.T.thr := by
  intro y hy
  obtain ⟨k, hk⟩ := Formalism.GM.TM.exists_pow_smul_intPol (p := p) y
  refine ⟨(p : ℤ_[p]) ^ k, pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero), ?_⟩
  have e : (((p : ℤ_[p]) ^ k : ℤ_[p]) : ℚ_[p]) = (p : ℚ_[p]) ^ k := by push_cast; rfl
  rw [e]
  refine ⟨Submodule.smul_mem _ _ hy, ?_, hk⟩
  exact Submodule.smul_mem _ _ ((inf_le_left : Formalism.GM.M.Y p (r := r) (G.lettersAt j jp) G.T.J G.T.thr ≤ _) hy)

theorem xiMons_free (n : ℕ) : ∀ β ∈ xiMons (r := r) G n, ∀ x, β (Formalism.GM.M.chainEmb N r G.T.t x) = 0 := by
  intro β hβ x
  by_contra h
  have hmem : Formalism.GM.M.chainEmb N r G.T.t x ∈ β.support := Finsupp.mem_support_iff.2 h
  obtain ⟨c, hc⟩ := (xiMons_spec G n β hβ).1 _ hmem
  simp only [Formalism.GM.M.chainEmb, Formalism.GM.M.xiVar, Sum.inl.injEq, Prod.mk.injEq] at hc
  exact Fin.castSucc_ne_last _ hc.1

theorem xiMons_mem (n : ℕ) : ∀ β ∈ xiMons (r := r) G n, (monomial β (1 : ℚ_[p])) ∈ Formalism.GM.M.XiPolZ p N r G.T.t n := by
  classical
  intro β hβ
  obtain ⟨h1, h2, -⟩ := xiMons_spec G n β hβ
  refine ⟨?_, Formalism.GM.M.intPol_monomial' β⟩
  show monomial β (1 : ℚ_[p]) ∈ MvPolynomial.restrictSupport ℚ_[p] _
  rw [MvPolynomial.mem_restrictSupport_iff, support_monomial, if_neg one_ne_zero]
  intro m hm
  rw [Finset.coe_singleton, Set.mem_singleton_iff] at hm
  subst hm
  exact ⟨h1, h2⟩

end Gen

variable {C0 CE1 CE2 : ℝ} {X : flipOneThree.Inst}

set_option maxHeartbeats 800000 in
theorem lvlDimCondition : RestLvlDim C0 CE1 CE2 X := by
  classical
  intro aTop _ aPlus _ b _ x hx
  have hL : (gB C0 CE1 CE2 X aTop aPlus b).LevelOK x.1 x.2 := by
    unfold lv levels at hx
    exact (Finset.mem_filter.1 hx).2
  have hfd : FiniteDimensional ℚ_[X.p]
      (Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2)) := by
    have h1 := span_SSZ_fin C0 CE1 CE2 X aTop aPlus b
    have hle : Submodule.span ℚ_[X.p] ((gB C0 CE1 CE2 X aTop aPlus b).gens X.p (r := X.r) x.1 x.2) ≤
        Submodule.span ℚ_[X.p]
          (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
            Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
              Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :=
      Submodule.span_le.2 fun y hy => Submodule.subset_span
        (Formalism.GM.M.gens_mem_SSZ (p := X.p) (r := X.r) (gB C0 CE1 CE2 X aTop aPlus b) x.1 x.2 hL y hy)
    exact Submodule.finiteDimensional_of_le hle
  exact lvlDim_gen (gB C0 CE1 CE2 X aTop aPlus b) x.1 x.2 (preF_ne_zero _ _ _) (den_Y _ _ _) hfd
    (xiMons_free _ _) (xiMons_mem _ _)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def SymmetryWindowConditions (C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM : ℝ) (X : flipOneThree.Inst) : Prop :=
  flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestSymm C0 CE1 CE2 X ∧ RestWin C0 CE1 CE2 X CM

def SymmetryWindowOnAdmissible (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X → SymmetryWindowConditions C0 CYb Cde Ck CD Cb CE1 CE2 Cc CM X

theorem windows_of_symmetric_dims (D : Formalism.BasicNotions.D7) (h : SymmetryWindowOnAdmissible D) : SymmetryWindowLevelDimOnAdmissible D :=
  thr_mono (fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc hP Ckap Cs CM hCM X hA hH => by
    obtain ⟨a, b⟩ := hP Ckap Cs CM hCM X hA hH
    exact ⟨a, b, (lvlDimCondition (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X))⟩) h

theorem closed_of_symmetric_dims (D : Formalism.BasicNotions.D7) (hF : RestFunY) (hO : OrthLat) (h : SymmetryWindowOnAdmissible D) : IntegralityFromMetricForLargeConstants D :=
  closed_of_symmetric_windows D hF hO (windows_of_symmetric_dims D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CmapMemRestrictSupport
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G

section CMap

variable {K L σ : Type} [CommRing K] [CommRing L] (f : K →+ L)

theorem cmap_add (y z : MvPolynomial σ K) : cmap f (y + z) = cmap f y + cmap f z := by
  ext m; simp only [MvPolynomial.coeff_add, coeff_cmap, map_add (f := _)]

theorem cmap_zero : cmap f (0 : MvPolynomial σ K) = 0 := by
  ext m; simp only [coeff_cmap, AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply, map_zero]

theorem cmap_neg (y : MvPolynomial σ K) : cmap f (-y) = -cmap f y := by
  ext m; simp only [coeff_cmap, coeff_neg, map_neg]

theorem cmap_monomial (n : σ →₀ ℕ) (c : K) : cmap f (monomial n c) = monomial n (f c) := by
  classical
  ext m
  rw [coeff_cmap, coeff_monomial, coeff_monomial]
  split_ifs <;> simp

def cmapHom : MvPolynomial σ K →+ MvPolynomial σ L where
  toFun := cmap f
  map_zero' := cmap_zero f
  map_add' := cmap_add f

theorem X_mul_monomial' (v : σ) (n : σ →₀ ℕ) (c : K) :
    (X v : MvPolynomial σ K) * monomial n c = monomial (Finsupp.single v 1 + n) c := by
  rw [X, monomial_mul, one_mul]

theorem cmap_X_pderiv (v w : σ) (y : MvPolynomial σ K) :
    cmap f (X v * pderiv w y) = X v * pderiv w (cmap f y) := by
  classical
  induction y using MvPolynomial.induction_on' with
  | monomial n c =>
    rw [pderiv_monomial, cmap_monomial, pderiv_monomial, X_mul_monomial', X_mul_monomial', cmap_monomial]
    congr 1
    rw [mul_comm c, mul_comm (f c)]
    have e1 : ((n w : ℕ) : K) * c = (n w) • c := (nsmul_eq_mul _ _).symm
    have e2 : ((n w : ℕ) : L) * f c = (n w) • f c := (nsmul_eq_mul _ _).symm
    rw [e1, e2, map_nsmul]
  | add p q hp hq =>
    rw [map_add (f := _), mul_add, cmap_add, hp, hq, cmap_add, map_add (f := _), mul_add]

end CMap

section Fun

variable {O : Type} [CommRing O] [IsDomain O] {p : ℕ} [Fact p.Prime] (f : KK O →+ ℚ_[p])

theorem cmap_glAct {N r : ℕ} (LL : ChainLetters N) (j : ℕ) (c d : Fin r) (y : MvPolynomial (Fin N × Fin r) (KK O)) :
    cmap f (glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d y) =
      Formalism.GM.M.glAct p (gmL LL) j c d (cmap f y) := by
  unfold Formalism.MainNotions.G.glAct Formalism.GM.M.glAct
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  show cmapHom f _ = _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  show cmap f _ = _
  by_cases hi : (i : ℕ) < j
  · have hi' : i ∈ {i : Fin N | (i : ℕ) < j} := hi
    rw [if_pos hi', if_pos hi]
    by_cases hv : LL.vec i = true
    · have hv' : (gmL LL).vec i = true := hv
      have hv'' : (⟨LL.vec⟩ : Letters (Fin N)).vec i = true := hv
      rw [if_pos hv'', if_pos hv']
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]
      exact cmap_X_pderiv f _ _ y
    · have hv' : ¬ (gmL LL).vec i = true := hv
      have hv'' : ¬ (⟨LL.vec⟩ : Letters (Fin N)).vec i = true := hv
      rw [if_neg hv'', if_neg hv']
      simp only [LinearMap.neg_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.mulLeft_apply]
      rw [cmap_neg]
      exact congrArg Neg.neg (cmap_X_pderiv f _ _ y)
  · have hi' : i ∉ {i : Fin N | (i : ℕ) < j} := hi
    rw [if_neg hi', if_neg hi]
    simp only [LinearMap.zero_apply]
    exact cmap_zero f

theorem cmap_support_subset {σ : Type} (y : MvPolynomial σ (KK O)) : (cmap f y).support ⊆ y.support := by
  intro m hm
  rw [mem_support_iff] at hm ⊢
  intro h0
  apply hm
  rw [coeff_cmap, h0, map_zero]

theorem sk_ycond_stable {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ) (c d : Fin r) :
    ∀ x ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt,
      glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d x ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt := by
  unfold Formalism.MainNotions.G.YCond
  intro x hx
  have : sSup {S : Submodule (KK O) (MvPolynomial (Fin N × Fin r) (KK O)) |
      S ≤ restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧
        chStable (KK O) LL j S} ≤
      (sSup {S : Submodule (KK O) (MvPolynomial (Fin N × Fin r) (KK O)) |
      S ≤ restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} ∧
        chStable (KK O) LL j S}).comap (glAct (KK O) (⟨LL.vec⟩ : Letters (Fin N)) {i : Fin N | (i : ℕ) < j} c d) :=
    sSup_le fun S hS x hx => le_sSup hS (hS.2 c d x hx)
  exact this hx

theorem sk_ycond_supp {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ) :
    Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt ≤
      restrictSupport (KK O) {m : Fin N × Fin r →₀ ℕ | ((chWt LL j 0 m : ℤ) : WithTop ℤ) ≤ Mt} :=
  sSup_le fun _ hS => hS.1

theorem cmap_mem_restrictSupport {σ : Type} {s : Set (σ →₀ ℕ)} (y : MvPolynomial σ (KK O))
    (hy : y ∈ restrictSupport (KK O) s) : cmap f y ∈ restrictSupport ℚ_[p] s := by
  rw [mem_restrictSupport_iff] at hy ⊢
  exact (Finset.coe_subset.2 (cmap_support_subset f y)).trans hy

theorem cmap_ycond (ι : ℚ_[p] →+* KK O) (_hf : ∀ (a : ℚ_[p]) (x : KK O), f (ι a * x) = a * f x)
    {N r : ℕ} [NeZero r] (LL : ChainLetters N) (j : ℕ) (Mt : WithTop ℤ)
    (y : MvPolynomial (Fin N × Fin r) (KK O)) (hy : y ∈ Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt) :
    cmap f y ∈ Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt := by
  set S' : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p]) :=
    Submodule.span ℚ_[p] (cmap f '' (Formalism.MainNotions.G.YCond (KK O) (r := r) LL j Mt : Set _)) with hS'
  have h1 : S' ≤ restrictSupport ℚ_[p] {m | ((Formalism.GM.M.wt (gmL LL) j 0 m : ℤ) : WithTop ℤ) ≤ Mt} := by
    rw [hS', Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact cmap_mem_restrictSupport f z (sk_ycond_supp LL j Mt hz)
  have h2 : Formalism.GM.M.GlStable p (gmL LL) j S' := by
    intro c d x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      rw [← cmap_glAct]
      exact Submodule.subset_span ⟨_, sk_ycond_stable LL j Mt c d z hz, rfl⟩
    | zero => rw [map_zero]; exact S'.zero_mem
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact S'.add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact S'.smul_mem a hx
  have h3 : S' ≤ Formalism.GM.M.YCond p (r := r) (gmL LL) j Mt := by
    unfold Formalism.GM.M.YCond
    exact le_sSup ⟨h1, h2⟩
  exact h3 (Submodule.subset_span ⟨y, hy, rfl⟩)

end Fun

theorem restFunY_proved : RestFunY := by
  intro O _ _ p _ ι N r _ LL q J M f hf y hy
  obtain ⟨hP, hC⟩ := hy
  refine ⟨cmap_mem_restrictSupport f y hP, ?_⟩
  have hC' : y ∈ ⨅ k, Formalism.MainNotions.G.YCond (KK O) (r := r) LL (J k) (M k) := hC
  show cmap f y ∈ ⨅ k, Formalism.GM.M.YCond p (r := r) (gmL LL) (J k) (M k)
  rw [Submodule.mem_iInf] at hC' ⊢
  exact fun k => cmap_ycond f ι hf LL (J k) (M k) y (hC' k)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_orthogonal_lattice (D : Formalism.BasicNotions.D7) (hO : OrthLat) (h : SymmetryWindowOnAdmissible D) : Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_symmetric_dims D restFunY_proved hO h

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_orthogonal_basis (D : Formalism.BasicNotions.D7) (hB : OrthBasisLat) (hG : GoodLeSmall) (h : SymmetryWindowOnAdmissible D) :
    Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_orthogonal_lattice D (orthLat_of' hB hG) h

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- restored from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PhisBSelfAdj
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section Gen

variable {K V ι : Type*} [Field K] [AddCommGroup V] [Module K V]

theorem foldr_comm_of (φ : ι → V →ₗ[K] V) (ψ : V →ₗ[K] V) (l : List ι) (h : ∀ j ∈ l, ∀ x, ψ (φ j x) = φ j (ψ x))
    (x : V) : ψ ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) x) = (l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) (ψ x) := by
  induction l generalizing x with
  | nil => simp
  | cons j l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [h j (by simp), ih (fun k hk => h k (by simp [hk]))]

theorem foldr_selfAdj (B : V → V → K) (hB : ∀ a b, B a b = B b a) (φ : ι → V →ₗ[K] V) (l : List ι)
    (hs : ∀ i ∈ l, ∀ a b, B (φ i a) b = B (φ i b) a)
    (hc : l.Pairwise (fun i j => ∀ x, φ i (φ j x) = φ j (φ i x))) (a b : V) :
    B ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) a) b = B ((l.foldr (fun i acc => φ i ∘ₗ acc) LinearMap.id) b) a := by
  induction l generalizing a b with
  | nil => simpa using hB a b
  | cons j l ih =>
    rw [List.pairwise_cons] at hc
    have hsl : ∀ i ∈ l, ∀ a b, B (φ i a) b = B (φ i b) a := fun i hi => hs i (by simp [hi])
    have hcomm := foldr_comm_of φ (φ j) l (fun i hi x => (hc.1 i hi x)) b
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [hs j (by simp), hB, ih hsl hc.2, hcomm]

end Gen

def RestTieComm : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (N r : ℕ) [NeZero r] (G : Formalism.GM.M.BlockData N), G.BlockOK →
    ∀ (j : Fin G.T.t → ℕ) (jp : ℕ) (i i' : Fin G.T.t), i ≠ i' → ∀ x : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
                (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
                ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
                (G.T.z i)
        (Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i'), c))
          (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i' + 1), c))
          ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i'))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i' + 1)))
          (G.T.z i') x) =
      Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i'), c))
                (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i' + 1), c))
                ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i'))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i' + 1)))
                (G.T.z i')
        (Formalism.GM.tiePhi (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i), c))
          (fun c => Sum.inl (Formalism.GM.M.finPos N (G.T.pos i + 1), c))
          ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i))) ((G.lettersAt j jp).deg (G.letterAt (G.T.pos i + 1)))
          (G.T.z i) x)

theorem phisB_selfAdj (hT : RestTieComm) (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)
    (hG : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (u v : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p]) :
    Formalism.GM.M.fockK (phisB p (r := r) G j jp u) v = Formalism.GM.M.fockK (phisB p (r := r) G j jp v) u := by
  have hfk : ∀ F G : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p],
      Formalism.GM.M.fockK F G = Formalism.GM.M.fock p F G := fun F G => rfl
  unfold phisB
  rw [hfk, hfk]
  refine foldr_selfAdj (fun a b => Formalism.GM.M.fock p a b) (fun a b => by apply Formalism.GM.GammaExpansion.fock_comm) _ _
    (fun i _ a b => by apply Formalism.GM.GammaExpansion.fock_phi_symm) ?_ u v
  refine (List.nodup_finRange G.T.t).pairwise_of_forall_ne fun i _ i' _ hii' x => ?_
  exact hT p N r G hG j jp i i' hii' x

theorem restSymm_of (hT : RestTieComm) (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst) : RestSymm C0 CE1 CE2 X := by
  intro dl _ aTop _ x _ u _ v _
  unfold bePhi
  congr 1
  exact phisB_selfAdj hT X.p _ (gB_blockOK C0 CE1 CE2 X aTop 0 x.1) _ _ u v

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- restored from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CommuteEPderiv
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset

section Comm

variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}

theorem pderiv_mul_free (v : σ) (g f : MvPolynomial σ ℚ_[p]) (hg : pderiv v g = 0) :
    pderiv v (g * f) = g * pderiv v f := by
  rw [Derivation.leibniz, hg, smul_zero, add_zero, smul_eq_mul]

theorem pderiv_pair_free (w e : Fin r → σ) (v : σ) (hw : ∀ c, w c ≠ v) (he : ∀ c, e c ≠ v) :
    pderiv v (∑ c, X (w c) * X (e c) : MvPolynomial σ ℚ_[p]) = 0 := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [Derivation.leibniz, pderiv_X, pderiv_X, Pi.single_eq_of_ne (he c), Pi.single_eq_of_ne (hw c)]
  simp

theorem commute_E_pderiv (w e : Fin r → σ) (v : σ) (hw : ∀ c, w c ≠ v) (he : ∀ c, e c ≠ v) :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (pderiv v : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap := by
  refine LinearMap.ext fun f => ?_
  show (∑ c, X (w c) * X (e c)) * pderiv v f = pderiv v ((∑ c, X (w c) * X (e c)) * f)
  rw [pderiv_mul_free v _ f (pderiv_pair_free w e v hw he)]

theorem commute_E_F (w e w' e' : Fin r → σ) (h1 : ∀ c c', w c ≠ w' c') (h2 : ∀ c c', e c ≠ w' c')
    (h3 : ∀ c c', w c ≠ e' c') (h4 : ∀ c c', e c ≠ e' c') :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (Formalism.GM.tieF (k := ℚ_[p]) w' e') := by
  unfold Formalism.GM.tieF
  refine Commute.sum_right _ _ _ fun c' _ => ?_
  rw [← Module.End.mul_eq_comp]
  exact (commute_E_pderiv w e (w' c') (fun c => h1 c c') (fun c => h2 c c')).mul_right
    (commute_E_pderiv w e (e' c') (fun c => h3 c c') (fun c => h4 c c'))

theorem commute_E_E (w e w' e' : Fin r → σ) :
    Commute (Formalism.GM.tieE (k := ℚ_[p]) w e) (Formalism.GM.tieE (k := ℚ_[p]) w' e') := by
  refine LinearMap.ext fun f => ?_
  show (∑ c, X (w c) * X (e c)) * ((∑ c, X (w' c) * X (e' c)) * f) =
    (∑ c, X (w' c) * X (e' c)) * ((∑ c, X (w c) * X (e c)) * f)
  ring

set_option maxHeartbeats 1000000 in
theorem commute_F_F (w e w' e' : Fin r → σ) :
    Commute (Formalism.GM.tieF (k := ℚ_[p]) w e) (Formalism.GM.tieF (k := ℚ_[p]) w' e') := by
  unfold Formalism.GM.tieF
  refine Commute.sum_left _ _ _ fun c _ => Commute.sum_right _ _ _ fun c' _ => ?_
  rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
  have h1 : Commute (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap) :=
    (Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (w c) (e' c'))
  have h2 : Commute (pderiv (e c) : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      ((pderiv (w' c')).toLinearMap * (pderiv (e' c')).toLinearMap) :=
    (Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (w' c')).mul_right (Formalism.GM.M.PhiIntegrality.commute_pderiv (e c) (e' c'))
  exact h1.mul_left h2

theorem commute_tiePhi (w e w' e' : Fin r → σ) (h1 : ∀ c c', w c ≠ w' c') (h2 : ∀ c c', e c ≠ w' c')
    (h3 : ∀ c c', w c ≠ e' c') (h4 : ∀ c c', e c ≠ e' c') (o n z o' n' z' : ℕ) (x : MvPolynomial σ ℚ_[p]) :
    Formalism.GM.tiePhi w e o n z (Formalism.GM.tiePhi w' e' o' n' z' x) = Formalism.GM.tiePhi w' e' o' n' z' (Formalism.GM.tiePhi w e o n z x) := by
  have cEE := commute_E_E (p := p) w e w' e'
  have cFF := commute_F_F (p := p) w e w' e'
  have cEF := commute_E_F (p := p) w e w' e' h1 h2 h3 h4
  have cFE := (commute_E_F (p := p) w' e' w e (fun c c' => (h1 c' c).symm) (fun c c' => (h3 c' c).symm)
    (fun c c' => (h2 c' c).symm) (fun c c' => (h4 c' c).symm)).symm
  have cP : Commute (Formalism.GM.tiePhi (k := ℚ_[p]) w e o n z) (Formalism.GM.tiePhi (k := ℚ_[p]) w' e' o' n' z') := by
    unfold Formalism.GM.tiePhi
    refine Commute.sum_left _ _ _ fun j _ => Commute.sum_right _ _ _ fun j' _ => ?_
    refine (Commute.smul_left ?_ _).smul_right _
    rw [← Module.End.mul_eq_comp, ← Module.End.mul_eq_comp]
    exact ((cEE.pow_pow j j').mul_right (cEF.pow_pow j j')).mul_left ((cFE.pow_pow j j').mul_right (cFF.pow_pow j j'))
  exact LinearMap.congr_fun cP.eq x

end Comm

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- restored from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.CommCondition
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem inl_ne {N r t : ℕ} (a b : ℕ) (ha : a < N) (hb : b < N) (hab : a ≠ b) (c c' : Fin r) :
    (Sum.inl (Formalism.GM.M.finPos N a, c) : Formalism.GM.M.BVar N r t) ≠ Sum.inl (Formalism.GM.M.finPos N b, c') := by
  intro h
  have h2 := congrArg Fin.val (Prod.mk.inj (Sum.inl.inj h)).1
  simp only [Formalism.GM.M.finPos] at h2
  rw [min_eq_left ha.le, min_eq_left hb.le] at h2
  exact hab h2

theorem commCondition : RestTieComm := by
  intro p _ N r _ G hG j jp i i' hii' x
  obtain ⟨⟨hmono, hvec, -⟩, hlt, -, -⟩ := hG
  have hpN : ∀ k, G.T.pos k + 1 < N := fun k => (hlt k).trans G.uPos.isLt
  have hne : G.T.pos i ≠ G.T.pos i' := hmono.injective.ne hii'
  have hcross : ∀ a b : Fin G.T.t, G.T.pos a + 1 ≠ G.T.pos b := by
    intro a b hab
    obtain ⟨ha, -, ha2⟩ := hvec a
    obtain ⟨hb, hb1, -⟩ := hvec b
    have e : G.LL.vec ⟨G.T.pos a + 1, ha⟩ = G.LL.vec ⟨G.T.pos b, by omega⟩ :=
      congrArg G.LL.vec (Fin.ext hab)
    rw [e] at ha2
    exact absurd (hb1.symm.trans ha2) (by decide)
  exact commute_tiePhi _ _ _ _
    (fun c c' => inl_ne _ _ (by have := hpN i; omega) (by have := hpN i'; omega) hne c c')
    (fun c c' => inl_ne _ _ (hpN i) (by have := hpN i'; omega) (hcross i i') c c')
    (fun c c' => inl_ne _ _ (by have := hpN i; omega) (hpN i') (hcross i' i).symm c c')
    (fun c c' => inl_ne _ _ (hpN i) (hpN i') (fun h => hne (by omega)) c c')
    _ _ _ _ _ _ x

theorem symmCondition (C0 CE1 CE2 : ℝ) (X : Formalism.MainNotions.flipOneThree.Inst) : RestSymm C0 CE1 CE2 X :=
  restSymm_of commCondition C0 CE1 CE2 X

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

def RestWinE (D : Formalism.BasicNotions.D7) : Prop :=
  flipOneThree.TransportedAlt fun C0 CYb Cde Ck CD Cb CE1 CE2 Cc => ∀ Ckap Cs CM : ℝ, 1 ≤ CM →
    ∀ X : flipOneThree.Inst, AdmNoK D C0 CYb Cde Ck CD Cb CE1 CE2 Ckap Cc Cs X →
      flipOneThree.HI C0 CYb Cde Ck CD Cb Cc X → RestWin C0 CE1 CE2 X CM

theorem symmetric_dims_of_windows (D : Formalism.BasicNotions.D7) (h : RestWinE D) : SymmetryWindowOnAdmissible D := by
  unfold RestWinE at h
  unfold SymmetryWindowOnAdmissible
  unfold Formalism.MainNotions.flipOneThree.TransportedAlt at h ⊢
  intro Cc hCc
  obtain ⟨T0, hT0, h0⟩ := h Cc hCc
  refine ⟨T0, hT0, fun C0 hC0 => ?_⟩
  obtain ⟨T1, hT1, h1⟩ := h0 C0 hC0
  refine ⟨T1, hT1, fun CE1 CE2 hE1 hE2 => ?_⟩
  obtain ⟨T2, hT2, h2⟩ := h1 CE1 CE2 hE1 hE2
  refine ⟨T2, hT2, fun CYb Cde Ck CD Cb ha hb hc hd he => ?_⟩
  intro Ckap Cs CM hCM X hX hHI
  exact ⟨symmCondition C0 CE1 CE2 X, h2 CYb Cde Ck CD Cb ha hb hc hd he Ckap Cs CM hCM X hX hHI⟩

theorem integralityFromMetric_of_orthBasisLat (D : Formalism.BasicNotions.D7) (hB : OrthBasisLat) (hG : GoodLeSmall) (h : RestWinE D) :
    IntegralityFromMetricForLargeConstants D :=
  closed_of_orthogonal_basis D hB hG (symmetric_dims_of_windows D h)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_orthogonal_splitting (D : Formalism.BasicNotions.D7) (hS : OrthSplit) (hG : GoodLeSmall) (h : RestWinE D) :
    Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  integralityFromMetric_of_orthBasisLat D (orthBasisLat_of freeLat_proved hS) hG h

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.GoodLeSmallMat
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset


open Classical in
def GoodLeSmallMat : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (n m : ℕ) (X Y : Fin n → Fin m → ℤ_[p]) (c : Fin m → ℚ_[p]) (D : ℤ),
    (∀ i j, ∑ a, (X i a : ℚ_[p]) * c a * (Y j a : ℚ_[p]) = if i = j then (p : ℚ_[p]) ^ D else 0) →
    n ≤ (Finset.univ.filter (fun a : Fin m => c a ≠ 0 ∧ (c a).valuation ≤ D)).card

theorem B_sum_left {p : ℕ} [Fact p.Prime] {σ ι : Type} (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (hsm : ∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) (hadd : ∀ u u' v, B (u + u') v = B u v + B u' v)
    (s : Finset ι) (g : ι → MvPolynomial σ ℚ_[p]) (v : MvPolynomial σ ℚ_[p]) :
    B (∑ i ∈ s, g i) v = ∑ i ∈ s, B (g i) v := by
  classical
  have h0 : B 0 v = 0 := by
    have := hsm 0 0 v
    simpa using this
  induction s using Finset.induction_on with
  | empty => simpa using h0
  | insert a s ha ih => rw [Finset.sum_insert ha, hadd, ih, Finset.sum_insert ha]

theorem goodLeSmall_of (h : GoodLeSmallMat) : GoodLeSmall := by
  intro p _ σ B L W D _ _ hsm hadd hsy m f hf _ hspan horth
  obtain ⟨x, y, hx, hy, hxy⟩ := goodCount_mem p B L D
  have hcoord : ∀ v ∈ L, ∃ X : Fin m → ℤ_[p], ∑ a, X a • f a = v := by
    intro v hv
    rw [← hspan] at hv
    exact (Submodule.mem_span_range_iff_exists_fun ℤ_[p]).1 hv
  choose! X hX using hcoord
  have hsmZ : ∀ (c : ℤ_[p]) (u : MvPolynomial σ ℚ_[p]), c • u = (c : ℚ_[p]) • u :=
    fun c u => (algebraMap_smul ℚ_[p] c u).symm
  have hexp : ∀ v ∈ L, ∀ w, B v w = ∑ a, (X v a : ℚ_[p]) * B (f a) w := by
    intro v hv w
    conv_lhs => rw [← hX v hv]
    rw [B_sum_left B hsm hadd]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hsmZ, hsm]
  have hfy : ∀ a j, B (f a) (y j) = (X (y j) a : ℚ_[p]) * B (f a) (f a) := by
    intro a j
    rw [hsy _ (hf a) _ (hy j), hexp _ (hy j)]
    rw [Finset.sum_eq_single a]
    · intro b _ hb
      rw [horth b a hb, mul_zero]
    · intro ha; exact absurd (Finset.mem_univ a) ha
  exact h p _ m (fun i => X (x i)) (fun j => X (y j)) (fun a => B (f a) (f a)) D (fun i j => by
    rw [← hxy i j, hexp _ (hx i)]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [hfy]
    ring)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_splitting_matrix (D : Formalism.BasicNotions.D7) (hS : OrthSplit) (hM : GoodLeSmallMat) (h : RestWinE D) :
    Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_orthogonal_splitting D hS (goodLeSmall_of hM) h

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

section -- merged from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.OrthSplitOfMin
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial

def OrthMin : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (B : MvPolynomial σ ℚ_[p] → MvPolynomial σ ℚ_[p] → ℚ_[p])
    (L : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p])) (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])),
    p ≠ 2 → FiniteDimensional ℚ_[p] W → (∀ x ∈ L, x ∈ W) → L.FG →
    (∀ (c : ℚ_[p]) u v, B (c • u) v = c * B u v) → (∀ u u' v, B (u + u') v = B u v + B u' v) →
    (∀ u ∈ L, ∀ v ∈ L, B u v = B v u) → (∃ u ∈ L, ∃ v ∈ L, B u v ≠ 0) →
    ∃ x ∈ L, B x x ≠ 0 ∧ ∀ u ∈ L, ∃ c : ℤ_[p], B u x = (c : ℚ_[p]) * B x x

def SplitRank : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (σ : Type) (L L' : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]))
    (W : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (x : MvPolynomial σ ℚ_[p]),
    FiniteDimensional ℚ_[p] W → (∀ y ∈ L, y ∈ W) → L.FG → L' ≤ L → x ∈ L → x ≠ 0 →
    Submodule.span ℤ_[p] {x} ⊔ L' = L → (∀ (c : ℤ_[p]) (y : MvPolynomial σ ℚ_[p]), y ∈ L' → c • x + y = 0 → c = 0) →
    Module.finrank ℤ_[p] L' < Module.finrank ℤ_[p] L

theorem zsmul_eq' {p : ℕ} [Fact p.Prime] {σ : Type} (c : ℤ_[p]) (u : MvPolynomial σ ℚ_[p]) :
    c • u = (c : ℚ_[p]) • u := rfl

theorem orthSplit_of (hM : OrthMin) (hR : SplitRank) : OrthSplit := by
  intro p _ σ B L W hp hW hLW hfg hsm hadd hsym hne
  obtain ⟨x, hxL, hxx, hdiv⟩ := hM p σ B L W hp hW hLW hfg hsm hadd hsym hne
  have hB0 : ∀ v, B 0 v = 0 := by
    intro v
    have h := hsm 0 0 v
    rwa [zero_smul, zero_mul] at h
  have hsub : ∀ u v w, B (u - v) w = B u w - B v w := by
    intro u v w
    have h := hadd (u - v) v w
    rw [sub_add_cancel] at h
    rw [h]
    ring
  let K : Submodule ℤ_[p] (MvPolynomial σ ℚ_[p]) :=
    { carrier := {u | u ∈ L ∧ B u x = 0}
      add_mem' := fun {u v} hu hv => ⟨L.add_mem hu.1 hv.1, by rw [hadd, hu.2, hv.2, add_zero]⟩
      zero_mem' := ⟨L.zero_mem, hB0 x⟩
      smul_mem' := fun c u hu => ⟨L.smul_mem c hu.1, by
        rw [zsmul_eq' c u, hsm, hu.2, mul_zero]⟩ }
  have hKL : K ≤ L := fun u hu => hu.1
  have hx0 : x ≠ 0 := by
    intro h
    apply hxx
    rw [h, hB0]
  have hdirect : ∀ (c : ℤ_[p]) (y : MvPolynomial σ ℚ_[p]), y ∈ K → c • x + y = 0 → c = 0 := by
    intro c y hy hcy
    have h1 : B (c • x + y) x = 0 := by
      rw [hcy, hB0]
    rw [hadd, zsmul_eq' c x, hsm, hy.2, add_zero] at h1
    have h2 : (c : ℚ_[p]) = 0 := (mul_eq_zero.mp h1).resolve_right hxx
    first
    | exact PadicInt.coe_eq_zero.mp h2
    | exact Subtype.ext h2
  have hsup : Submodule.span ℤ_[p] {x} ⊔ K = L := by
    apply le_antisymm
    · exact sup_le ((Submodule.span_le).mpr (Set.singleton_subset_iff.mpr hxL)) hKL
    · intro u hu
      obtain ⟨c, hc⟩ := hdiv u hu
      refine Submodule.mem_sup.mpr ⟨c • x, Submodule.mem_span_singleton.mpr ⟨c, rfl⟩, u - c • x, ⟨?_, ?_⟩, ?_⟩
      · exact L.sub_mem hu (L.smul_mem c hxL)
      · rw [hsub, zsmul_eq' c x, hsm, hc, sub_self]
      · abel
  refine ⟨x, hxL, K, hKL, hfg.of_le hKL, hR p σ L K W x hW hLW hfg hKL hxL hx0 hsup hdirect, ?_, hsup, hdirect⟩
  intro u hu
  rw [hsym x hxL u hu.1]
  exact hu.2

theorem splitRank_proved : SplitRank := by
  intro p _ σ L L' W x hW hLW hfg hL'L hxL hx0 hsup hdirect
  haveI : NoZeroSMulDivisors ℤ_[p] (MvPolynomial σ ℚ_[p]) := by
    constructor
    intro c y h
    rw [zsmul_eq'] at h
    rcases smul_eq_zero.mp h with h | h
    · left
      first
      | exact PadicInt.coe_eq_zero.mp h
      | exact Subtype.ext h
    · right
      exact h
  haveI : Module.Finite ℤ_[p] L := Module.Finite.iff_fg.mpr hfg
  haveI : Module.Finite ℤ_[p] L' := Module.Finite.iff_fg.mpr (hfg.of_le hL'L)
  haveI : Module.Free ℤ_[p] L' := Module.free_of_finite_type_torsion_free'
  haveI : Module.Free ℤ_[p] L := Module.free_of_finite_type_torsion_free'
  let f : (ℤ_[p] × L') →ₗ[ℤ_[p]] L :=
    { toFun := fun q => ⟨q.1 • x + (q.2 : MvPolynomial σ ℚ_[p]), L.add_mem (L.smul_mem _ hxL) (hL'L q.2.2)⟩
      map_add' := fun q q' => by
        apply Subtype.ext
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_smul]
        abel
      map_smul' := fun c q => by
        apply Subtype.ext
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply, smul_add,
          mul_smul] }
  have hbij : Function.Bijective f := by
    constructor
    · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
      rintro ⟨c, y⟩ hq
      have h1 : c • x + (y : MvPolynomial σ ℚ_[p]) = 0 := congrArg Subtype.val hq
      have hc : c = 0 := hdirect c y y.2 h1
      subst hc
      rw [zero_smul, zero_add] at h1
      exact Prod.ext rfl (Subtype.ext h1)
    · rintro ⟨u, hu⟩
      rw [← hsup] at hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      exact ⟨(c, ⟨b, hb⟩), rfl⟩
  have he := (LinearEquiv.ofBijective f hbij).finrank_eq
  rw [Module.finrank_prod, Module.finrank_self] at he
  omega

theorem orthSplit_of_min (hM : OrthMin) : OrthSplit := by
  exact orthSplit_of hM splitRank_proved

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

theorem closed_of_minimal_vector (D : Formalism.BasicNotions.D7) (hO : OrthMin) (hM : GoodLeSmallMat) (h : RestWinE D) :
    Formalism.MainNotions.flipOneThree.IntegralityFromMetricForLargeConstants D :=
  closed_of_splitting_matrix D (orthSplit_of_min hO) hM h

end Formalism.MainNotions.G.SymmetricFormBlocks

end
