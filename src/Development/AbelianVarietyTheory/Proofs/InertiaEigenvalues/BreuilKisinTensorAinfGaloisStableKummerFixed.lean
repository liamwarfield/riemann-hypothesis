module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTensorAinfGaloisStableKummerFixed
section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTensorAinfGaloisStableKummerFixed
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.StableFix

theorem SemiBC.span_eq {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) :
    Submodule.span B (Set.range u) = ⊤ := by
  have h1 : (Submodule.span B (Set.range u)).mkQ = 0 := h.hom_ext fun x => by
    rw [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨x, rfl⟩
  exact Submodule.eq_top_iff'.2 fun y => by
    have := LinearMap.congr_fun h1 y
    rwa [LinearMap.zero_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem kappa_act {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (s : GQ l) (g : G) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, TWact (galOW O s) T g (kappa T y) =
      kappa T (TensorProduct.map (galW l s).toLinearMap (actZ T g) y) := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul w x => rfl
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

theorem kappa_smul' {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (w : WCb l) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (w • y) = ((1 : O) ⊗ₜ[ℤ_[l]] w) • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul w' x =>
    rw [smul_tmul', kappa_tmul, kappa_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => simp only [smul_add, map_add (f := _), hx, hy]

variable (P : PhiMod O K l e a ι)

theorem inclO_smul_mem_MA (r : OA l O) {v : ι → OW l O} (hv : v ∈ MA P) : inclO l O r • v ∈ MA P := by
  obtain ⟨c, rfl⟩ := hv
  exact ⟨r • c, funext fun i => (map_mul (inclO l O) r (c i))⟩

theorem inclO_smul_mem_LA (r : OA l O) {v : ι → OW l O} (hv : v ∈ LA t ϖ P) : inclO l O r • v ∈ LA t ϖ P := by
  obtain ⟨c, rfl⟩ := hv
  refine ⟨r • c, ?_⟩
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul (inclO l O) r (c i))

abbrev eb (i : ι) : ι → OW l O := fun j => if i = j then 1 else 0

theorem phiW_eb (i : ι) : phiW t ϖ P (eb i) = frobMat t ϖ P *ᵥ eb i := by
  rw [phiW_apply]
  congr 1
  funext j
  show frobOW l O (if i = j then 1 else 0) = if i = j then 1 else 0
  split_ifs <;> simp

theorem phiW_inclV (c : ι → OA l O) : phiW t ϖ P (inclV l O ι c) = inclL t ϖ P (fun i => frobOA l O (c i)) := by
  rw [phiW_apply, inclL_apply]
  congr 1
  funext j
  exact frobOW_inclO (c j)

def mb (i : ι) : Vec K a ι := fun _ j => if i = j then 1 else 0

theorem mb_mem (i : ι) : (mb i : Vec K a ι) ∈ P.M :=
  mem_tot.2 fun τ j => by
    change (if i = j then (1 : K⟦X⟧) else 0) ∈ A O K
    split_ifs
    · exact one_mem _
    · exact zero_mem _

theorem toW_mb (i : ι) : toW t ϖ P ⟨mb i, mem_ME_of_mem_M (mb_mem P i)⟩ = eb i := by
  funext j
  rw [toW_apply]
  show _ = (if i = j then (1 : OW l O) else 0)
  split_ifs with h
  · convert map_one (ϖ.iW t K) using 2
    funext τ
    apply Subtype.ext
    simp [mb, h]
  · convert map_zero (ϖ.iW t K) using 2
    funext τ
    apply Subtype.ext
    simp [mb, h]

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem add_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T))
      (z z' : E.M (ainfObj (ϖ.field a))) (v v' : ι → OW l O), I.j v = kappa T (j z) → I.j v' = kappa T (j z') →
      I.j (v + v') = kappa T (j (z + z')) := by
  letI := zlLat T
  intro j z z' v v' hv hw
  rw [I.j.map_add, hv, hw, j.map_add, (kappa T).map_add]

theorem smul_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T))
      (c : (ainfObj (ϖ.field a)).A) (z : E.M (ainfObj (ϖ.field a))) (v : ι → OW l O), I.j v = kappa T (j z) →
      I.j (inclO l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfId (ϖ.field a) c) • v) = kappa T (j (c • z)) := by
  letI := zlLat T
  intro j c z v hv
  have e1 : j (c • z) = inclW l (ainfId (ϖ.field a) c) • j z := j.map_smulₛₗ c z
  rw [e1, kappa_smul', LinearEquiv.map_smul, hv, inclO_tmul]

theorem span_step {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (E : FCrys l ↥(OL (ϖ.field a))) :
    letI := zlLat T
    ∀ (j : E.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)),
      (∀ y : TW (OW l O) T, (∃ x : E.M (ϖ.prism a), y = kappa T (j (E.tr (ϖ.toAinf a) x))) ↔
        ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) →
      ∀ z : E.M (ainfObj (ϖ.field a)), ∃ v ∈ MA P, I.j v = kappa T (j z) := by
  letI := zlLat T
  intro j hE z
  have hz : z ∈ Submodule.span (ainfObj (ϖ.field a)).A (Set.range (E.tr (ϖ.toAinf a))) := by
    rw [SemiBC.span_eq (E.tr_bc (ϖ.toAinf a))]
    exact Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨y, rfl⟩ := hz
    obtain ⟨m', hm', h'⟩ := (hE (kappa T (j (E.tr (ϖ.toAinf a) y)))).1 ⟨y, rfl⟩
    exact ⟨_, toW_mem_MA t ϖ P hm', h'.symm⟩
  | zero => exact ⟨0, zero_mem _, by rw [I.j.map_zero, j.map_zero, (kappa T).map_zero]⟩
  | add z z' _ _ h h' =>
    obtain ⟨v, hv, hv'⟩ := h
    obtain ⟨v', hw, hw'⟩ := h'
    exact ⟨v + v', add_mem hv hw, add_step I E j z z' v v' hv' hw'⟩
  | smul c z _ h =>
    obtain ⟨v, hv, hv'⟩ := h
    exact ⟨_, inclO_smul_mem_MA P _ hv, smul_step I E j c z v hv'⟩

theorem core {P : PhiMod O K l e a ι} {T : Lat a O K ϖ} (I : Ident t ϖ P T) (hI : IsBK I)
    (g : ↥(GK (ϖ.field a))) (m : Vec K a ι) (hm : m ∈ P.M) :
    I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) ∈ MA P ∧
      ((g : GQ l) ∈ ϖ.GfieldInf a →
        I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) = toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := by
  letI := zlLat T
  obtain ⟨E, j, H, hE⟩ := hI
  obtain ⟨x, hx⟩ := (hE (I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩))).2 ⟨m, hm, rfl⟩
  have hact : I.j (I.act (g : GQ l) g (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) =
      kappa T (j (E.tr (ainfHom (ϖ.field a) g) (E.tr (ϖ.toAinf a) x))) := by
    rw [Ident.j_act, hx, kappa_act]
    exact congrArg (kappa T) (H.j_act g _).symm
  refine ⟨?_, fun hg => I.j.injective ?_⟩
  · obtain ⟨v, hv, hv'⟩ := span_step I E j hE (E.tr (ainfHom (ϖ.field a) g) (E.tr (ϖ.toAinf a) x))
    rw [← hact, I.j.injective.eq_iff] at hv'
    exact hv' ▸ hv
  · have h1 : (ainfHom (ϖ.field a) g).comp (ϖ.toAinf a) = ϖ.toAinf a :=
      Hom.ext' (RingHom.ext fun y => PiSys.gal_ev l a ϖ hg y)
    rw [hact, ← E.tr_comp, h1, ← hx]

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {P : PhiMod O K l e a ι} {T : Lat a O K ϖ}

theorem act_eb_mem (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) (i : ι) :
    I.act (g : GQ l) g (eb i) ∈ MA P := by
  rw [← toW_mb P i]
  exact (core I hI g _ (mb_mem P i)).1

theorem act_MA (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) :
    ∀ v ∈ MA P, I.act (g : GQ l) g v ∈ MA P := by
  rintro _ ⟨c, rfl⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [pi_eq_sum_univ (inclV l O ι c), map_sum]
  refine sum_mem fun i _ => ?_
  rw [Ident.act_smul]
  change galOW O (g : GQ l) (inclO l O (c i)) • _ ∈ _
  rw [galOW_inclO]
  exact inclO_smul_mem_MA P _ (act_eb_mem I hI g i)

theorem act_LA (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) :
    ∀ v ∈ LA t ϖ P, I.act (g : GQ l) g v ∈ LA t ϖ P := by
  rintro _ ⟨c, rfl⟩
  have h1 : inclL t ϖ P c = ∑ i, inclO l O (c i) • phiW t ϖ P (eb i) := by
    rw [inclL_apply]
    conv_lhs => rw [pi_eq_sum_univ (fun i => inclO l O (c i)), Matrix.mulVec_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Matrix.mulVec_smul, phiW_eb]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum]
  refine sum_mem fun i _ => ?_
  rw [Ident.act_smul, galOW_inclO, Ident.act_phiW]
  refine inclO_smul_mem_LA P _ ?_
  obtain ⟨d, hd⟩ := act_eb_mem I hI g i
  rw [← hd, phiW_inclV]
  exact ⟨_, rfl⟩

theorem act_fix (I : Ident t ϖ P T) (hI : IsBK I) (g : ↥(GK (ϖ.field a))) (hg : (g : GQ l) ∈ ϖ.GfieldInf a)
    (v : ME P) : I.act (g : GQ l) g (toW t ϖ P v) = toW t ϖ P v := by
  set_option synthInstance.maxHeartbeats 100000 in
    conv_lhs => rw [pi_eq_sum_univ (toW t ϖ P v), map_sum]
  conv_rhs => rw [pi_eq_sum_univ (toW t ϖ P v)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Ident.act_smul, toW_apply, ϖ.galOW_iW t K hg]
  congr 1
  have h := (core I hI g _ (mb_mem P i)).2 hg
  rw [toW_mb P i] at h
  exact h

end GlobalTheory.BKGal.StableFix

namespace GlobalTheory.BKGal.StableFix

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) ∧ ∀ g : Gl l, sQ l g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v := by
  intro l _ a e _ _ ϖ LL _ _ ι _ _ P T I hBK
  refine ⟨fun g => ⟨act_LA _ hBK g, act_MA _ hBK g⟩, fun g hg v => ?_⟩
  exact act_fix (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) hBK
    ⟨sQ l g, PiSys.fixing_fieldInf_le a ϖ hg⟩ hg v

end GlobalTheory.BKGal.StableFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinTensorAinfGaloisStableKummerFixedStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.breuilKisin_tensorAinf_galoisStable_kummerFixed : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (LL : FinExt l) [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod ↥(OL LL) ↥LL.1 l e a ι) (T : QLat LL) (I : Ident (thetaW a LL) ϖ P T), IsBK (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) → Ident.Stable (T := resF T (ϖ.field a)) (I.res (inclG (ϖ.field a)) (continuous_subtype_val.subtype_mk _)) ∧ ∀ g : Gl l, sQ l g ∈ ϖ.GfieldInf a → ∀ v : ME P, I.act (sQ l g) g (toW (thetaW a LL) ϖ P v) = toW (thetaW a LL) ϖ P v := by
  first | exact @GlobalTheory.BKGal.StableFix.main | exact GlobalTheory.BKGal.StableFix.main | (intros; apply GlobalTheory.BKGal.StableFix.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallySubMemPow
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.AcrisGal

open Filter Topology

variable {l : ℕ} [hl : Fact l.Prime]

private theorem sigO_coe_pt (g : Per.Gq l) (y : Per.OC l) :
    ((Per.σO g y : Per.OC l) : ℂ_[l]) = Per.σC g (y : ℂ_[l]) := by
  apply GlobalTheory.RingIface.sigO_coe

private theorem tower_pt (x : Per.Ainf l) : algebraMap (Per.Acris0 l) (Per.Acris l)
    (algebraMap (Per.Ainf l) (Per.Acris0 l) x) = ainfToAcris l x := by
  change _ = algebraMap (Per.Ainf l) (Per.Acris l) x
  symm
  apply GlobalTheory.RingIface.tower

theorem eventually_norm_σC_sub_lt (y : ℂ_[l]) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ g : GQ l in 𝓝 1, ‖Per.σC g y - y‖ < ε := by
  have hd : DenseRange (fun x : Om l => (x : ℂ_[l])) := UniformSpace.Completion.denseRange_coe
  obtain ⟨x, hx⟩ := hd.exists_dist_lt y (half_pos hε)
  rw [dist_eq_norm] at hx
  filter_upwards [GlobalTheory.Cyc.eventually_apply_eq x 1] with g hg
  have e : Per.σC g y - y = Per.σC g (y - x) - (y - x) := by
    rw [map_sub, GlobalTheory.RingBasics.σC_coe, hg, AlgEquiv.one_apply]; ring
  rw [e]
  calc ‖Per.σC g (y - x) - (y - x)‖ ≤ ‖Per.σC g (y - x)‖ + ‖y - x‖ := norm_sub_le _ _
    _ < ε := by rw [GlobalTheory.RingBasics.norm_σC]; linarith

theorem exists_eq_l_mul (z : Per.OC l) (hz : ‖(z : ℂ_[l])‖ ≤ ‖((l : ℕ) : ℂ_[l])‖) :
    ∃ c : Per.OC l, z = (l : Per.OC l) * c := by
  have h0 : ((l : ℕ) : ℂ_[l]) ≠ 0 := GlobalTheory.RingBasics.p_ne_zero
  refine ⟨⟨(z : ℂ_[l]) / l, (GlobalTheory.RingBasics.mem_OC _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [norm_div]; exact div_le_one_of_le₀ hz (norm_nonneg _)
  · change (z : ℂ_[l]) = ((l : Per.OC l) : ℂ_[l]) * ((z : ℂ_[l]) / l)
    have : ((l : Per.OC l) : ℂ_[l]) = l := by simp
    rw [this]; field_simp

variable {ξ : Per.Ainf l}

theorem eventually_sub_mem_one (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, Per.σA g y - y ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} := by
  have hl0 : (0 : ℝ) < ‖((l : ℕ) : ℂ_[l])‖ := norm_pos_iff.2 GlobalTheory.RingBasics.p_ne_zero
  filter_upwards [eventually_norm_σC_sub_lt ((Per.θ l y : Per.OC l) : ℂ_[l]) hl0] with g hg
  have h1 : Per.θ l (Per.σA g y - y) = Per.σO g (Per.θ l y) - Per.θ l y := by rw [map_sub, GlobalTheory.RingBasics.θ_σA]
  obtain ⟨c, hc⟩ := exists_eq_l_mul (Per.σO g (Per.θ l y) - Per.θ l y)
    (by rw [AddSubgroupClass.coe_sub, sigO_coe_pt]; exact hg.le)
  obtain ⟨c', rfl⟩ := GlobalTheory.MemLoc.ThetaD.θ_surj l c
  have hk : Per.σA g y - y - (l : Per.Ainf l) * c' ∈ RingHom.ker (Per.θ l) := by
    rw [RingHom.mem_ker, map_sub, h1, hc, map_mul, map_natCast, sub_self]
  rw [hξ, Ideal.mem_span_singleton'] at hk
  obtain ⟨d, hd⟩ := hk
  rw [Ideal.mem_span_pair]
  exact ⟨c', d, by linear_combination hd⟩

theorem eventually_sub_mem_pow (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (N : ℕ) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, Per.σA g y - y ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} ^ (N + 1) := by
  set I : Ideal (Per.Ainf l) := Ideal.span {((l : ℕ) : Per.Ainf l), ξ} with hI
  have hlI : ((l : ℕ) : Per.Ainf l) ∈ I := Ideal.subset_span (by simp)
  have ht : ∀ z : Per.Fl l, ∀ᶠ g : GQ l in 𝓝 1,
      Per.σA g (WittVector.teichmuller l z) - WittVector.teichmuller l z ∈ I ^ (N + 1) := by
    intro z
    obtain ⟨w, rfl⟩ := (iterateFrobeniusEquiv (Per.Fl l) l N).surjective z
    filter_upwards [eventually_sub_mem_one hξ (WittVector.teichmuller l w)] with g hg
    have := SModEq.sub_mem.1 ((SModEq.sub_mem.2 hg).pow_pow_add_one hlI N)
    rw [iterateFrobeniusEquiv_def, map_pow, map_pow]
    exact this
  obtain ⟨c, hc⟩ := WittVector.dvd_sub_sum_teichmuller_iterateFrobeniusEquiv_coeff y N
  have hall := (Filter.eventually_all_finset (Finset.Iic N)).2
    (fun i _ => ht ((((_root_.frobeniusEquiv (Per.Fl l) l).symm ^ i) (y.coeff i))))
  filter_upwards [hall] with g hg
  rw [sub_eq_iff_eq_add] at hc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [hc, map_add (f := _), map_mul, map_pow, map_natCast, map_sum, add_sub_add_comm, ← mul_sub,
    ← Finset.sum_sub_distrib]
  refine add_mem (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hlI _)) (sum_mem fun i hi => ?_)
  rw [map_mul, map_pow, map_natCast, ← sub_mul]
  exact Ideal.mul_mem_right _ _ (hg i hi)

theorem dvd_of_mem (hξ : RingHom.ker (Per.θ l) = Ideal.span {ξ}) (N : ℕ) {z : Per.Ainf l}
    (hz : z ∈ Ideal.span {((l : ℕ) : Per.Ainf l), ξ} ^ (N + l * N)) :
    (l : Per.Acris l) ^ N ∣ ainfToAcris l z := by
  have hθ : Per.θ l ξ = 0 := by rw [← RingHom.mem_ker, hξ]; exact Ideal.mem_span_singleton_self ξ
  have hxl : (l : Per.Acris l) ∣ ainfToAcris l ξ ^ l := by
    rw [← factorial_mul_dpow ξ hθ l]
    obtain ⟨k, hk⟩ := Nat.dvd_factorial hl.out.pos le_rfl
    rw [hk]; push_cast
    exact Dvd.dvd.mul_right (dvd_mul_right _ _) _
  rw [Ideal.span_insert] at hz
  have h1 := Ideal.sup_pow_add_le_pow_sup_pow hz
  rw [Ideal.span_singleton_pow, Ideal.span_singleton_pow, Submodule.mem_sup] at h1
  obtain ⟨a, ha, b, hb, rfl⟩ := h1
  obtain ⟨a', rfl⟩ := Ideal.mem_span_singleton'.1 ha
  obtain ⟨b', rfl⟩ := Ideal.mem_span_singleton'.1 hb
  rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, map_natCast, pow_mul]
  exact dvd_add (Dvd.intro_left _ rfl) (Dvd.dvd.mul_left (pow_dvd_pow_of_dvd hxl N) _)

theorem eventually_dvd_ainf (N : ℕ) (y : Per.Ainf l) :
    ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g (ainfToAcris l y) - ainfToAcris l y := by
  obtain ⟨ξ, hξ, -, -⟩ := GlobalTheory.Prism.exists_generator l
  filter_upwards [eventually_sub_mem_pow hξ (N + l * N) y] with g hg
  have h := dvd_of_mem hξ N (Ideal.pow_le_pow_right (Nat.le_succ _) hg)
  have e : galC g (ainfToAcris l y) = ainfToAcris l (Per.σA g y) := (GlobalTheory.CrisMaps.sigA_extends g).alg y
  rwa [e, ← map_sub]

theorem eventually_dvd_dpow {x : Per.Ainf l} (hx : Per.θ l x = 0) (k N : ℕ) :
    ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g (dpow x hx k) - dpow x hx k := by
  choose c hc using GlobalTheory.RingBasics.exists_pow_div_factorial l
  have hc' : ∀ n : ℕ, (n.factorial : Per.Acris l) * algebraMap ℤ_[l] _ (c n) = (l : Per.Acris l) ^ n :=
    fun n => by
      simpa only [map_mul, map_natCast, map_pow] using congrArg (algebraMap ℤ_[l] (Per.Acris l)) (hc n)
  filter_upwards [eventually_dvd_ainf (N + 1) x] with g ⟨D, hD⟩
  set X := ainfToAcris l x with hX
  set Y := ∑ m ∈ Finset.range (k + 1), dpow x hx m * (algebraMap ℤ_[l] (Per.Acris l) (c (k - m)) *
    (l : Per.Acris l) ^ (N * (k - m)) * D ^ (k - m)) with hYdef
  have hY : (k.factorial : Per.Acris l) * Y = (X + (l : Per.Acris l) ^ (N + 1) * D) ^ k := by
    rw [hYdef, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hmk := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
    rw [← Nat.choose_mul_factorial_mul_factorial hmk, ← factorial_mul_dpow x hx m, mul_pow, ← pow_mul,
      show (N + 1) * (k - m) = (k - m) + N * (k - m) by ring, pow_add, ← hc' (k - m)]
    push_cast
    ring
  have hσ : galC g (dpow x hx k) = Y := by
    have h1 := congrArg (galC g) (factorial_mul_dpow x hx k)
    rw [map_mul, map_natCast, map_pow, ← hX, show galC g X = X + (l : Per.Acris l) ^ (N + 1) * D by
      rw [← hD]; ring] at h1
    exact sub_eq_zero.1 (acris_nat_cancel k.factorial_ne_zero (by rw [mul_sub, h1, hY, sub_self]))
  have hc0 : algebraMap ℤ_[l] (Per.Acris l) (c 0) = 1 := by simpa using hc' 0
  rw [hσ, hYdef, Finset.sum_range_succ, Nat.sub_self, hc0, pow_zero, mul_zero, pow_zero, mul_one, mul_one,
    mul_one, add_sub_cancel_right]
  refine Finset.dvd_sum fun m hm => Dvd.dvd.mul_left (Dvd.dvd.mul_right (Dvd.dvd.mul_left
    (pow_dvd_pow _ (Nat.le_mul_of_pos_right N (by have := Finset.mem_range.1 hm; omega))) _) _) _


variable (l) in
def fixNear : Subring (Per.Acris l) where
  carrier := {x | ∀ N : ℕ, ∀ᶠ g : GQ l in 𝓝 1, (l : Per.Acris l) ^ N ∣ galC g x - x}
  mul_mem' {a b} ha hb N := by
    filter_upwards [ha N, hb N] with g ⟨u, hu⟩ ⟨v, hv⟩
    refine ⟨galC g a * v + u * b, ?_⟩
    rw [map_mul]
    linear_combination galC g a * hv + b * hu
  one_mem' N := .of_forall fun g => ⟨0, by simp⟩
  add_mem' {a b} ha hb N := by
    filter_upwards [ha N, hb N] with g ⟨u, hu⟩ ⟨v, hv⟩
    exact ⟨u + v, by rw [map_add (f := _)]; linear_combination hu + hv⟩
  zero_mem' N := .of_forall fun g => ⟨0, by simp⟩
  neg_mem' {a} ha N := by
    filter_upwards [ha N] with g ⟨u, hu⟩
    exact ⟨-u, by rw [map_neg]; linear_combination -hu⟩

theorem algebraMap_mem_fixNear (s : Per.Acris0 l) :
    algebraMap (Per.Acris0 l) (Per.Acris l) s ∈ fixNear l := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.exists_isEps_for_inj l
  have hx : Per.θ l (GlobalTheory.MemLoc.xi e) = 0 := (GlobalTheory.T.fontaineTheta_eq_zero_iff_fontaineXiElement_dvd l e he _).2 dvd_rfl
  obtain ⟨s, hs⟩ := s
  have key : ∀ y ∈ Submodule.span (Per.Ainf l) {y : Per.AinfP l | ∃ n : ℕ,
      ((n.factorial : ℕ) : Per.AinfP l) * y = algebraMap (Per.Ainf l) (Per.AinfP l) (GlobalTheory.MemLoc.xi e) ^ n},
      ∀ hy : y ∈ Per.Acris0 l, algebraMap (Per.Acris0 l) (Per.Acris l) ⟨y, hy⟩ ∈ fixNear l := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      intro hy0
      obtain ⟨n, hn⟩ := hy
      have h1 : (n.factorial : Per.Acris0 l) * ⟨y, hy0⟩ =
          algebraMap (Per.Ainf l) (Per.Acris0 l) (GlobalTheory.MemLoc.xi e) ^ n := Subtype.ext (by simpa using hn)
      have h2 := congrArg (algebraMap (Per.Acris0 l) (Per.Acris l)) h1
      rw [map_mul, map_natCast, map_pow, tower_pt] at h2
      rw [eq_dpow hx h2]
      exact fun N => eventually_dvd_dpow hx n N
    | zero =>
      intro h0
      have e0 : (⟨0, h0⟩ : Per.Acris0 l) = 0 := Subtype.ext rfl
      rw [e0, map_zero]; exact zero_mem _
    | add y z hy hz ihy ihz =>
      intro h0
      have hy0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he y).2 hy
      have hz0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he z).2 hz
      have e0 : (⟨y + z, h0⟩ : Per.Acris0 l) = ⟨y, hy0⟩ + ⟨z, hz0⟩ := Subtype.ext rfl
      set_option synthInstance.maxHeartbeats 200000 in
        rw [e0, map_add (f := _)]; exact add_mem (ihy hy0) (ihz hz0)
    | smul r y hy ihy =>
      intro h0
      have hy0 := (GlobalTheory.MemLoc.mem_Acris0_iff_span l e he y).2 hy
      have e0 : (⟨r • y, h0⟩ : Per.Acris0 l) = algebraMap (Per.Ainf l) (Per.Acris0 l) r * ⟨y, hy0⟩ :=
        Subtype.ext (Algebra.smul_def r y)
      rw [e0, map_mul, tower_pt]
      exact mul_mem (fun N => eventually_dvd_ainf N r) (ihy hy0)
  exact key s ((GlobalTheory.MemLoc.mem_Acris0_iff_span l e he s).1 hs) hs

theorem galC_sub_dvd_mem_nhds : ∀ (l : ℕ) [Fact l.Prime] (x : Per.Acris l) (n : ℕ),
    {g : GQ l | (l : Per.Acris l) ^ n ∣ galC g x - x} ∈ nhds (1 : GQ l) := by
  intro l _ x n
  obtain ⟨s, z, rfl⟩ := (GlobalTheory.MemLoc.acris_basic l).2.2.1 x n
  filter_upwards [algebraMap_mem_fixNear s n] with g ⟨u, hu⟩
  refine ⟨u + (galC g z - z), ?_⟩
  rw [map_add (f := _), map_mul, map_pow, map_natCast]
  linear_combination hu

end GlobalTheory.AcrisGal
end
end
