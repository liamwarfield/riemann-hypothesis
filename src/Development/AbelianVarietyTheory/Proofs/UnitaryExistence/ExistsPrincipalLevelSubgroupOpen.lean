module

public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongruenceLatticeFractionalMultipleAgree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
noncomputable section

namespace GlobalTheory.Member.PrincLevel

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem smul_mem_hat (L : Set (Fin n → E)) (a : FiniteAdeleRing (𝓞 F) F)
    (ha : ∀ v, a v ∈ v.adicCompletionIntegers F) {z : Fin n → GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat F L) : a • z ∈ GlobalTheory.AdLat.hat F L := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨b, hb, x, hx, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * b, fun v => ?_, x, hx, ?_⟩
    · exact mul_mem (ha v) (hb v)
    · funext i
      simp only [Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

def congSub {R : Type} [CommRing R] (M : Matrix (Fin n) (Fin n) R) (H : AddSubgroup (Fin n → R)) (N : ℕ) :
    AddSubgroup (Fin n → R) where
  carrier := {z | ∃ y ∈ H, M *ᵥ z - z = N • y}
  zero_mem' := ⟨0, zero_mem _, by simp⟩
  add_mem' := by
    rintro a b ⟨x, hx, ha⟩ ⟨y, hy, hb⟩
    refine ⟨x + y, add_mem hx hy, ?_⟩
    rw [Matrix.mulVec_add, smul_add, ← ha, ← hb]; abel
  neg_mem' := by
    rintro a ⟨x, hx, ha⟩
    refine ⟨-x, neg_mem hx, ?_⟩
    rw [Matrix.mulVec_neg, smul_neg, ← ha]; abel

theorem cong_of_gen (L : Set (Fin n → E)) (S : Set (Fin n → E)) (hS : L ⊆ AddSubgroup.closure S)
    (M : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (N : ℕ)
    (h : ∀ x ∈ S, ∃ y ∈ GlobalTheory.AdLat.hat F L, M *ᵥ GlobalTheory.AdLat.fv F x - GlobalTheory.AdLat.fv F x = N • y) :
    ∀ z ∈ GlobalTheory.AdLat.hat F L, ∃ y ∈ GlobalTheory.AdLat.hat F L, M *ᵥ z - z = N • y := by
  have h1 : ∀ x ∈ AddSubgroup.closure S, GlobalTheory.AdLat.fv F x ∈ congSub M (GlobalTheory.AdLat.hat F L) N := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem z hz => exact h z hz
    | zero =>
      have : GlobalTheory.AdLat.fv F (0 : Fin n → E) = 0 := by funext i; simp [GlobalTheory.AdLat.fv]
      rw [this]; exact zero_mem _
    | add x y _ _ hx hy =>
      have : GlobalTheory.AdLat.fv F (x + y) = GlobalTheory.AdLat.fv F x + GlobalTheory.AdLat.fv F y := by
        funext i; simp [GlobalTheory.AdLat.fv, TensorProduct.tmul_add]
      rw [this]; exact add_mem hx hy
    | neg x _ hx =>
      have : GlobalTheory.AdLat.fv F (-x) = -GlobalTheory.AdLat.fv F x := by
        funext i; simp [GlobalTheory.AdLat.fv, TensorProduct.tmul_neg]
      rw [this]; exact neg_mem hx
  have h2 : GlobalTheory.AdLat.hat F L ≤ congSub M (GlobalTheory.AdLat.hat F L) N := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro z ⟨a, ha, x, hx, rfl⟩
    obtain ⟨y, hy, e⟩ := h1 x (hS hx)
    have hz : (fun i => a ⊗ₜ[F] x i : Fin n → GlobalTheory.AdLat.RA F E) = a • GlobalTheory.AdLat.fv F x := by
      funext i
      simp only [GlobalTheory.AdLat.fv, Pi.smul_apply, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    refine ⟨a • y, smul_mem_hat L a ha hy, ?_⟩
    rw [hz, Matrix.mulVec_smul, ← smul_sub, e, smul_comm]
  exact fun z hz => h2 hz

theorem continuous_mulVec_sub {X R : Type} [TopologicalSpace X] [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] {f : X → Matrix (Fin n) (Fin n) R} (hf : Continuous f) (v : Fin n → R) :
    Continuous fun k => f k *ᵥ v - v :=
  (hf.matrix_mulVec continuous_const).sub continuous_const

end General

variable {D : D7}

theorem finCong_map {V : HSp D} {N : ℕ} {k : GA D V} (hk : FinCong V N k) :
    ∀ z ∈ latHat V, (finHom V k).1 *ᵥ z ∈ latHat V := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  rw [sub_eq_iff_eq_add] at e
  rw [e]
  exact add_mem (nsmul_mem hy N) hz

theorem finCong_one (V : HSp D) (N : ℕ) : FinCong V N 1 := by
  intro z _
  exact ⟨0, zero_mem _, by simp⟩

theorem finCong_mul {V : HSp D} {N : ℕ} {a b : GA D V} (ha : FinCong V N a) (hb : FinCong V N b) :
    FinCong V N (a * b) := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hb z hz
  obtain ⟨x, hx, e'⟩ := ha _ (finCong_map hb z hz)
  refine ⟨x + y, add_mem hx hy, ?_⟩
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, nsmul_add, ← e, ← e']
  abel

theorem finCong_inv {V : HSp D} {N : ℕ} {a : GA D V} (ha : FinCong V N a) : FinCong V N a⁻¹ := by
  obtain ⟨h1, -, h3, h4, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hinv : ∀ z ∈ latHat V, (finHom V a⁻¹).1 *ᵥ z ∈ latHat V := by
    have hm := finCong_map ha
    rw [h1] at hm ⊢
    rw [map_inv]
    exact GlobalTheory.AdLat.inv_mulVec_mem_hat D.host.F D.host.E V.rank (latC V) (finHom V a) (cF D) h3 h4 hm
      (GlobalTheory.Member.finHom_herm_det D V a).2.1
  intro z hz
  obtain ⟨y, hy, e⟩ := ha _ (hinv z hz)
  refine ⟨-y, neg_mem hy, ?_⟩
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one,
    Matrix.one_mulVec] at e
  rw [neg_nsmul, ← e, neg_sub]

def levelGroup (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | k ∈ GfC V ∧ FinCong V N k}
  one_mem' := ⟨one_mem _, finCong_one V N⟩
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, finCong_mul ha.2 hb.2⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, finCong_inv ha.2⟩

theorem finCong_mem_nhds (V : HSp D) {N : ℕ} (hN : 0 < N) :
    {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V) := by
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨hop, hc, -⟩ := GlobalTheory.Member.latHat_open_and_continuous D V
  have : IsTopologicalRing (Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (Af D.host.F) _
  obtain ⟨S, hS⟩ := h3.restrictScalars (R := ℤ)
  have hLS : (latC V : Set (Fin V.rank → D.host.E)) ⊆
      (AddSubgroup.closure (S : Set (Fin V.rank → D.host.E)) : AddSubgroup (Fin V.rank → D.host.E)) := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (S : Set (Fin V.rank → D.host.E)) := by rw [hS]; exact hx
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    exact hx'
  have hU : (⋂ x ∈ S, {k : GA D V | ∃ y ∈ latHat V,
      (finHom V k).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x - GlobalTheory.AdLat.fv D.host.F x = N • y}) ∈ 𝓝 (1 : GA D V) := by
    refine (Filter.biInter_finset_mem S).2 fun x _ => ?_
    have hcx : Continuous fun k : GA D V =>
        (finHom V k).1 *ᵥ GlobalTheory.AdLat.fv D.host.F x - GlobalTheory.AdLat.fv D.host.F x :=
      continuous_mulVec_sub hc _
    refine ((hop N hN).preimage hcx).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hU fun k hk => ?_
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at hk
  unfold FinCong
  rw [Set.mem_ofPred_eq]
  rw [h1] at hk ⊢
  exact cong_of_gen _ _ hLS _ N fun x hx => hk x hx

theorem exists_levelK_and_nhds : ∀ (D : D7) (V : HSp D), ∀ N : ℕ,
    (∃ Kf : Subgroup (GA D V), IsLevelK V N Kf) ∧
      (0 < N → {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V)) :=
  fun _ V N => ⟨⟨levelGroup V N, fun _ => Iff.rfl⟩, fun hN => finCong_mem_nhds V hN⟩

end GlobalTheory.Member.PrincLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpenStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_principalLevel_subgroup_open : ∀ (D : D7) (V : HSp D), ∀ N : ℕ, (∃ Kf : Subgroup (GA D V), IsLevelK V N Kf) ∧ (0 < N → {k : GA D V | FinCong V N k} ∈ 𝓝 (1 : GA D V)) := by
  first | exact @GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds | exact GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds | (intros; apply GlobalTheory.Member.PrincLevel.exists_levelK_and_nhds <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpace
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem map_span_eq_latG (D : D7) (V : HSp D) :
    (Submodule.span (𝓞 D.host.E) {v | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ x ∈ V.L0, v = a • x}).map
      ((V.frame.equivFun : V.V →ₗ[D.host.E] (Fin V.rank → D.host.E)).restrictScalars (𝓞 D.host.E)) = latG V 1 := by
  rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.2, Submodule.map_span]
  congr 1
  ext w
  constructor
  · rintro ⟨v, ⟨a, ha, x, hx, rfl⟩, rfl⟩
    exact ⟨a, ha, V.frame.equivFun x, ⟨x, hx, rfl⟩, by simp⟩
  · rintro ⟨a, ha, y, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨a • x, ⟨a, ha, x, hx, rfl⟩, by simp⟩

theorem exists_iotaOK : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → (∃ ι, IotaOK (Q.Dw j) (D.sp.W j) ι) ∧ (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ (Q.Dw j).q = WeightFamilies.rho D j ∧ 2 * (Q.Dw j).q < D.R.r := by
  intro D Q hP j hj
  obtain ⟨⟨-, hrt, hrt0, -⟩, -, -, hD⟩ := hP
  obtain ⟨hp, hq, φ, ε, hinj, hrange, hiso⟩ := hD j hj
  have hk := D.R.m_add_three_le_k
  obtain ⟨h1, h2⟩ := hj
  refine ⟨?_, ?_, hq, ?_⟩
  · let e := (((D.sp.W j).frame.equivFun : (D.sp.W j).V →ₗ[D.host.E]
      (Fin (D.sp.W j).rank → D.host.E)).restrictScalars (𝓞 D.host.E))
    have hr : LinearMap.range (e ∘ₗ φ) = latG (D.sp.W j) 1 := by
      rw [LinearMap.range_comp, hrange]
      exact map_span_eq_latG D (D.sp.W j)
    have hspan : Submodule.span D.host.E (Set.range φ) = ⊤ := by
      have h := (GlobalTheory.T.adelicElementLattice_full_and_completion D (D.sp.W j) 1).2.1
      rw [← hr] at h
      have hs : ((LinearMap.range (e ∘ₗ φ) : Submodule _ _) : Set (Fin (D.sp.W j).rank → D.host.E)) =
          ((D.sp.W j).frame.equivFun : (D.sp.W j).V →ₗ[D.host.E] (Fin (D.sp.W j).rank → D.host.E)) ''
            Set.range φ := by
        rw [← Set.range_comp]
        rfl
      rw [hs, ← Submodule.map_span] at h
      exact (Submodule.map_eq_top_iff (e := (D.sp.W j).frame.equivFun)).mp h
    have hε : ε = 1 := GlobalTheory.T.liftDatum_alternatingForm_sign_eq_one D Q.H (Q.Dw j) j ⟨h1, h2⟩ hrt hrt0 hp hq φ ε hinj hspan hiso
    refine ⟨e ∘ₗ φ, hrt, hrt0, ⟨(D.sp.W j).frame.equivFun.injective.comp hinj, hr⟩, fun x y => ?_⟩
    have hx : ∀ z, (D.sp.W j).frame.equivFun.symm ((e ∘ₗ φ) z) = φ z := fun z =>
      (D.sp.W j).frame.equivFun.symm_apply_apply (φ z)
    rw [hx, hx, hiso x y, hε]
    simp
  · rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]
    omega
  · rw [hq]
    simp only [Ranks.sigW, Ranks.r]
    omega

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLatticeEmbeddingLiftDatumHermitianSpaceStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_latticeEmbedding_liftDatum_hermitianSpace : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → (∃ ι, IotaOK (Q.Dw j) (D.sp.W j) ι) ∧ (Q.Dw j).p + (Q.Dw j).q = D.R.r ∧ (Q.Dw j).q = WeightFamilies.rho D j ∧ 2 * (Q.Dw j).q < D.R.r := by
  first | exact @GlobalTheory.Member.exists_iotaOK | exact GlobalTheory.Member.exists_iotaOK | (intros; apply GlobalTheory.Member.exists_iotaOK <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceForm
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.LatSelfDual

variable {D : D7}

theorem cF_eq_conj (D : D7) (x : D.host.E) : cF D x = D.host.conj x :=
  bridge_star_holds D.R D.host x

noncomputable def frameForm (V : HSp D) (v y : Fin V.rank → D.host.E) : D.host.E :=
  ∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)

theorem frameForm_smul_left (V : HSp D) (e : D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V (e • v) y = e * frameForm V v y := by
  simp only [frameForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem frameForm_smul_right (V : HSp D) (e : D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V v (e • y) = D.host.conj e * frameForm V v y := by
  rw [← cF_eq_conj]
  simp only [frameForm, Finset.mul_sum, Pi.smul_apply, smul_eq_mul, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

theorem frameForm_add_left (V : HSp D) (v w y : Fin V.rank → D.host.E) :
    frameForm V (v + w) y = frameForm V v y + frameForm V w y := by
  simp only [frameForm, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem frameForm_add_right (V : HSp D) (v w y : Fin V.rank → D.host.E) :
    frameForm V v (w + y) = frameForm V v w + frameForm V v y := by
  simp only [frameForm, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem frameForm_int_smul_left (V : HSp D) (c : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V (c • v) y = c • frameForm V v y := by
  rw [← algebraMap_smul D.host.E c v, frameForm_smul_left, Algebra.smul_def]

theorem frameForm_int_smul_right (V : HSp D) (c : 𝓞 D.host.E) (v y : Fin V.rank → D.host.E) :
    frameForm V v (c • y) = (D.host.conj • c) • frameForm V v y := by
  rw [← algebraMap_smul D.host.E c y, frameForm_smul_right, Algebra.smul_def, algebraMap_conj_smul]

theorem mem_iff_trace (D : D7) (z : D.host.E) :
    z ∈ D.host.AA * D.host.AAbar ↔
      ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hξ := cmHost_imaginaryGenerator_ne_zero hP D
  constructor
  · intro hz a
    have h : a • z ∈ NAA D := Submodule.smul_mem _ a hz
    rw [Algebra.smul_def] at h
    exact trace_int_of_mem hP D h
  · intro h
    have hz : D.host.xi0 * z ∈
        FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
      rw [FractionalIdeal.mem_dual
        (@one_ne_zero (FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) _ _ _)]
      intro a ha
      rw [FractionalIdeal.mem_one_iff] at ha
      obtain ⟨c, rfl⟩ := ha
      obtain ⟨n, hn⟩ := h c
      rw [Algebra.traceForm_apply, mul_assoc, mul_comm z]
      exact ⟨n, (eq_intCast (algebraMap ℤ ℚ) _).trans hn.symm⟩
    rw [← dual_eq hP D] at hz
    have h4 := FractionalIdeal.mul_mem_mul
      (FractionalIdeal.mem_spanSingleton_self (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹) hz
    have e1 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0⁻¹ *
        (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar) =
        D.host.AA * D.host.AAbar := by
      rw [mul_assoc, ← mul_assoc, FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hξ,
        FractionalIdeal.spanSingleton_one, one_mul]
    rwa [e1, ← mul_assoc, inv_mul_cancel₀ hξ, one_mul] at h4

theorem AAbar_ne_zero (D : D7) : D.host.AAbar ≠ 0 := by
  intro h
  have h1 := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  rw [h, mul_zero, zero_mul] at h1
  exact zero_ne_one h1

theorem selfDual_one (V : HSp D) (v : Fin V.rank → D.host.E) :
    (∀ y ∈ latG V 1, frameForm V v y ∈ D.host.AA * D.host.AAbar) ↔ v ∈ latG V 1 := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have hAA := AA_ne_zero hP D
  have hAb := AAbar_ne_zero D
  have hC : ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latC V, frameForm V v y ∈
      (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)) ↔ v ∈ latC V :=
    (GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V).2.2.2.2.2.2.2.2.2.2
  rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.2]
  constructor
  · intro h
    have h5 : ∀ y0 ∈ latC V, frameForm V v y0 ∈ D.host.AA := by
      intro y0 hy0
      have hle : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0) *
          D.host.AAbar ≤ D.host.AA * D.host.AAbar := by
        rw [FractionalIdeal.spanSingleton_mul_le_iff]
        intro b hb
        have := h (D.host.conj b • y0) (Submodule.subset_span ⟨_, conj_mem_AA D hb, y0, hy0, rfl⟩)
        rw [frameForm_smul_right, conj_conj, mul_comm b] at this
        exact this
      have hle2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0) ≤
          D.host.AA := by
        calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (frameForm V v y0)
            = D.host.AAbar⁻¹ * (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E))
                (frameForm V v y0) * D.host.AAbar) := by
              rw [mul_comm _ D.host.AAbar, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
          _ ≤ D.host.AAbar⁻¹ * (D.host.AA * D.host.AAbar) := CovariantClass.elim D.host.AAbar⁻¹ hle
          _ = D.host.AA := by rw [mul_comm D.host.AA, ← mul_assoc, inv_mul_cancel₀ hAb, one_mul]
      exact hle2 (FractionalIdeal.mem_spanSingleton_self _ _)
    have h6 : ∀ c ∈ D.host.AA⁻¹, c • v ∈ latC V := by
      intro c hc
      refine (hC _).1 fun y hy => ?_
      rw [frameForm_smul_left, ← inv_mul_cancel₀ hAA]
      exact FractionalIdeal.mul_mem_mul hc (h5 y hy)
    have h7 : ∀ e ∈ D.host.AA * D.host.AA⁻¹, e • v ∈ Submodule.span (𝓞 D.host.E)
        {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x} := by
      intro e he
      refine FractionalIdeal.mul_induction_on (C := fun e => e • v ∈ Submodule.span (𝓞 D.host.E)
        {w | ∃ a ∈ D.host.AA, ∃ x ∈ latC V, w = a • x}) he (fun a ha c hc => ?_) (fun u w hu hw => ?_)
      · show (a * c) • v ∈ _
        rw [mul_smul]; exact Submodule.subset_span ⟨a, ha, c • v, h6 c hc, rfl⟩
      · show (u + w) • v ∈ _
        rw [add_smul]; exact add_mem hu hw
    have := h7 1 (by rw [mul_inv_cancel₀ hAA]; exact FractionalIdeal.one_mem_one _)
    rwa [one_smul] at this
  · intro hv w hw
    show frameForm V v w ∈ NAA D
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hv
      induction hw using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨b, hb, y, hy, rfl⟩ := hw
        obtain ⟨r, hr⟩ := (FractionalIdeal.mem_one_iff _).1 ((hC x).2 hx y hy)
        rw [frameForm_smul_left, frameForm_smul_right, ← hr, ← mul_assoc, mul_comm, ← Algebra.smul_def]
        exact Submodule.smul_mem _ r (FractionalIdeal.mul_mem_mul ha (conj_mem_AAbar D hb))
      | zero => simp [frameForm]
      | add w w' _ _ h h' => rw [frameForm_add_right]; exact add_mem h h'
      | smul c w _ h => rw [frameForm_int_smul_right]; exact Submodule.smul_mem _ _ h
    | zero => simp [frameForm]
    | add v v' _ _ h h' => rw [frameForm_add_left]; exact add_mem h h'
    | smul c v _ h => rw [frameForm_int_smul_left]; exact Submodule.smul_mem _ _ h

theorem selfDual (V : HSp D) (g : GA D V) (v : Fin V.rank → D.host.E) :
    (∀ y ∈ latG V g, frameForm V v y ∈ D.host.AA * D.host.AAbar) ↔ v ∈ latG V g := by
  obtain ⟨-, -, -, -, hcc, -, -, hG, hdet, -, -⟩ := GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V
  obtain ⟨hfg, hspan, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  have hlat := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.1
  have key := GlobalTheory.AdLat.latOf_selfDual D.host.F D.host.E V.rank (latG V 1) (cF D) V.gramᵀ
    (D.host.AA * D.host.AAbar) (finHom V g) hfg hspan hcc hG hdet
    (mul_ne_zero (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D) (AAbar_ne_zero D))
    (selfDual_one V) (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V g).1 v
  rw [← hlat] at key
  exact key

end GlobalTheory.Member.LatSelfDual

namespace GlobalTheory.Member

open LatSelfDual

theorem latG_selfDual : ∀ (D : D7) (V : HSp D), ∀ (g : GA D V) (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), J = D.host.AA * D.host.AAbar → (∀ z : D.host.E, z ∈ J ↔ ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n) ∧ (∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ J) ↔ v ∈ latG V g) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) v y) = n) ↔ v ∈ latG V g := by
  intro D V g J hJ
  subst hJ
  refine ⟨mem_iff_trace D, selfDual V g, fun v => ?_⟩
  have hcc := (GlobalTheory.T.completedLattice_eq_adelicCompletion_and_gram D V).2.2.2.2.2.1
  have hh : ∀ y, herm (-V.gramᵀ) v y = - frameForm V v y := by
    intro y
    simp only [herm, frameForm, hcc, Matrix.neg_apply, mul_neg, neg_mul, Finset.sum_neg_distrib]
  have ht : ∀ y, (∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) v y) = n) ↔
      ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * frameForm V v y) = n := by
    intro y
    rw [hh, neg_neg, mul_neg, map_neg]
    exact ⟨fun ⟨n, hn⟩ => ⟨-n, by rw [Int.cast_neg, ← hn, neg_neg]⟩,
      fun ⟨n, hn⟩ => ⟨-n, by rw [Int.cast_neg, hn]⟩⟩
  simp only [ht]
  rw [← selfDual V g v]
  constructor
  · intro h y hy
    refine (mem_iff_trace D _).2 fun a => ?_
    have h1 := h _ ((latG V g).smul_mem (D.host.conj⁻¹ • a) hy)
    rw [frameForm_int_smul_right, smul_inv_smul, Algebra.smul_def] at h1
    exact h1
  · intro h y hy
    exact trace_int_of_mem Formalism.IndefR.Fin.factPrincipalDatum D (h y hy)

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeSelfDualTraceFormStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitaryLattice_selfDual_traceForm : ∀ (D : D7) (V : HSp D), ∀ (g : GA D V) (J : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E), J = D.host.AA * D.host.AAbar → (∀ z : D.host.E, z ∈ J ↔ ∀ a : 𝓞 D.host.E, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * (a * z)) = n) ∧ (∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, (∑ a, ∑ b, v a * V.gramᵀ a b * cF D (y b)) ∈ J) ↔ v ∈ latG V g) ∧ ∀ v : Fin V.rank → D.host.E, (∀ y ∈ latG V g, ∃ n : ℤ, Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) v y) = n) ↔ v ∈ latG V g := by
  first | exact @GlobalTheory.Member.latG_selfDual | exact GlobalTheory.Member.latG_selfDual | (intros; apply GlobalTheory.Member.latG_selfDual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member.LatMove

variable {D : D7} (V : HSp D)

theorem mem_hat_iff (g : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ latGHat V g ↔ ∃ z ∈ latGHat V 1, (finHom V g).1 *ᵥ z = w := by
  have h1 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.1
  have h2 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1
  rw [h2, ← SetLike.mem_coe, h1]
  rfl

theorem mem_lat_iff (g : GA D V) (v : Fin V.rank → D.host.E) :
    v ∈ latG V g ↔ finVec V v ∈ latGHat V g := by
  have h0 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.1
  have h1 := (GlobalTheory.T.adelicElementLattice_full_and_completion D V g).2.2.2.1
  rw [← SetLike.mem_coe, h0, ← SetLike.mem_coe, h1]
  rfl

theorem fin_mul (g h : GA D V) (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V (g * h)).1 *ᵥ z = (finHom V g).1 *ᵥ ((finHom V h).1 *ᵥ z) := by
  rw [map_mul, Units.val_mul, Matrix.mulVec_mulVec]

theorem fin_one (z : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    (finHom V 1).1 *ᵥ z = z := by
  rw [map_one, Units.val_one, Matrix.one_mulVec]

theorem move_mem (g h : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E)
    (hw : w ∈ latGHat V h) : (finHom V g).1 *ᵥ w ∈ latGHat V (g * h) := by
  obtain ⟨z, hz, rfl⟩ := (mem_hat_iff V h w).1 hw
  exact (mem_hat_iff V _ _).2 ⟨z, hz, fin_mul V g h z⟩

theorem move_iff (g h : GA D V) (w : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E) :
    w ∈ latGHat V h ↔ (finHom V g).1 *ᵥ w ∈ latGHat V (g * h) := by
  refine ⟨move_mem V g h w, fun hw => ?_⟩
  have := move_mem V g⁻¹ _ _ hw
  rwa [← fin_mul, inv_mul_cancel, fin_one, inv_mul_cancel_left] at this

theorem lat_eq_of_hat_eq {h h' : GA D V} (e : latGHat V h = latGHat V h') : latG V h = latG V h' := by
  ext v
  rw [mem_lat_iff, mem_lat_iff, e]

theorem finCong_one {N : ℕ} {k : GA D V} (hk : FinCong V N k) : FinCong V 1 k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := hk z hz
  exact ⟨N • y, AddSubgroup.nsmul_mem _ hy N, by rw [one_nsmul, e]⟩

theorem hat_eq_of_finCong {N : ℕ} {k : GA D V} (hk : FinCong V N k) : latGHat V k = latGHat V 1 := by
  have h1 := (GlobalTheory.T.congruence_lattice_fractionalMultiple_agree D V k).1.2 (finCong_one V hk)
  have h2 : ∀ z ∈ latGHat V 1, (finHom V k⁻¹).1 *ᵥ z ∈ latGHat V 1 := by
    have hh := (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.2.2.2.1
    rw [hh] at h1 ⊢
    rw [map_inv]
    exact GlobalTheory.AdLat.inv_mulVec_mem_hat D.host.F D.host.E V.rank (latG V 1) (finHom V k) (cF D)
      (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).1 (GlobalTheory.T.adelicElementLattice_full_and_completion D V 1).2.1 h1 (GlobalTheory.T.finitePart_preserves_form_det_norm_one D V k).2.1
  ext w
  rw [mem_hat_iff]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact h1 z hz
  · intro hw
    exact ⟨_, h2 w hw, by rw [← fin_mul, mul_inv_cancel, fin_one]⟩

end GlobalTheory.Member.LatMove

open GlobalTheory.Member.LatMove in
theorem GlobalTheory.Member.latG_move : ∀ (D : D7) (V : HSp D), (∀ γ γ' h, IsRat V γ γ' → (∀ v, v ∈ latG V h ↔ (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v ∈ latG V (γ * h)) ∧ ∀ w, w ∈ latGHat V h ↔ (finHom V γ).1 *ᵥ w ∈ latGHat V (γ * h)) ∧ (∀ h h', finHom V h = finHom V h' → latG V h = latG V h' ∧ latGHat V h = latGHat V h') ∧ (∀ (N : ℕ) h k, FinCong V N k → latG V (h * k) = latG V h ∧ latGHat V (h * k) = latGHat V h) ∧ ∀ h h', latG V h = latG V h' → FinCong V 1 (h⁻¹ * h') := by
  intro D V
  refine ⟨fun γ γ' h hγ => ⟨fun v => ?_, fun w => move_iff V γ h w⟩, fun h h' e => ?_, fun N h k hk => ?_,
    fun h h' e => ?_⟩
  · rw [mem_lat_iff, mem_lat_iff, move_iff V γ h, ((GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V).2.2.2.2 γ γ' hγ).1 v]
  · have : latGHat V h = latGHat V h' := by
      ext w
      rw [mem_hat_iff V h, mem_hat_iff V h', e]
    exact ⟨lat_eq_of_hat_eq V this, this⟩
  · have : latGHat V (h * k) = latGHat V h := by
      ext w
      rw [move_iff V h⁻¹ (h * k), move_iff V h⁻¹ h, inv_mul_cancel_left, inv_mul_cancel,
        hat_eq_of_finCong V hk]
    exact ⟨lat_eq_of_hat_eq V this, this⟩
  · have e' : latGHat V h = latGHat V h' := by
      rw [(GlobalTheory.T.adelicElementLattice_full_and_completion D V h).2.2.2.2.1, (GlobalTheory.T.adelicElementLattice_full_and_completion D V h').2.2.2.2.1, e]
    refine (GlobalTheory.T.congruence_lattice_fractionalMultiple_agree D V (h⁻¹ * h')).1.1 fun z hz => ?_
    have h1 := move_mem V h' 1 z hz
    rw [mul_one, ← e'] at h1
    have h2 := move_mem V h⁻¹ h _ h1
    rwa [← fin_mul, inv_mul_cancel] at h2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvarianceStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance : ∀ (D : D7) (V : HSp D), (∀ γ γ' h, IsRat V γ γ' → (∀ v, v ∈ latG V h ↔ (γ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v ∈ latG V (γ * h)) ∧ ∀ w, w ∈ latGHat V h ↔ (finHom V γ).1 *ᵥ w ∈ latGHat V (γ * h)) ∧ (∀ h h', finHom V h = finHom V h' → latG V h = latG V h' ∧ latGHat V h = latGHat V h') ∧ (∀ (N : ℕ) h k, FinCong V N k → latG V (h * k) = latG V h ∧ latGHat V (h * k) = latGHat V h) ∧ ∀ h h', latG V h = latG V h' → FinCong V 1 (h⁻¹ * h') := by
  first | exact @GlobalTheory.Member.latG_move | exact GlobalTheory.Member.latG_move | (intros; apply GlobalTheory.Member.latG_move <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralFramesModelInvertiblePushforward
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralFramesModelInvertiblePushforward
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem _root_.GlobalTheory.intFrames_of_laws : _root_.ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt → _root_.ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H)
      (l : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l), _root_.Formalism.L2.Pj.IntFramesSt Xo c :=
  fun hBase hTwist E _ _ _ H Dw l Xo c =>
    _root_.Formalism.L2.Pj.intFrames Xo c _root_.ReciprocityTheory.ChartRestriction.G.Out.CubePf.cubePull (_root_.Formalism.L2.Pj.lieFree Xo c) (_root_.Formalism.L2.Pj.thetaFrame_of Xo c hTwist)
      (_root_.GlobalTheory.Frames.framedPoint_field_fromTest hBase E H Dw l Xo c)

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIntegralFramesModelInvertiblePushforwardStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integralFrames_model_invertible_pushforward : Out.SecBaseChangeSt → Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), IntFramesSt Xo c := by
  first | exact @GlobalTheory.intFrames_of_laws | exact GlobalTheory.intFrames_of_laws | (intros; apply GlobalTheory.intFrames_of_laws <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChange
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsBorelPairsUniversalFrameOpenChart
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsBorelPairsUniversalFrameOpenChart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem univFrame_borelPairs : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p A : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (π : p.R →ₐ[c.F] A.R) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ) (u : FrPt Xo c A.R), OpenChart j y₀ → UnivFrame y₀ π X s u → ∃ (B : TRing c.F) (uB uB' : FrPt Xo c B.R) (tB : Ix Dw → (B.R)ˣ) (q q' : A.R →ₐ[c.F] B.R), FrMap q u uB ∧ FrMap q' u uB' ∧ FrBor tB uB uB' ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A.R →ₐ[c.F] T) (z z' : FrPt Xo c T) (t : Ix Dw → Tˣ), FrMap a u z → FrMap a' u z' → FrBor t z z' → ∃ b : B.R →ₐ[c.F] T, b.comp q = a ∧ b.comp q' = a' ∧ ∀ i, b (tB i : B.R) = (t i : T) := by
  intro hS E _ _ _ H Dw l Xo c p A j y₀ π X s u hj hU
  obtain ⟨B, q, Y, r, hYd, hYz, hY⟩ := GlobalTheory.T.exists_triangularFrameRing_over_testRing c.F (E →+* ℂ) (fun τ => Dw.mult τ) A
  obtain ⟨uB, huB⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c A.R B.R q u
  obtain ⟨uB', huB', -⟩ := GlobalTheory.T.existsUnique_frameChangeByMatrices E H Dw l Xo c B.R uB Y r
    fun τ => lowerTri_isUnit_det _ (hYz τ) (hYd τ)
  have hux : u.x = spMap π.toRingHom ≫ y₀.x := by
    obtain ⟨-, u₀, h₀, h₁⟩ := hU
    exact h₁.1.trans h₀.1
  have hx' : uB'.x = spMap (q.comp π).toRingHom ≫ y₀.x := by
    rw [huB'.1, huB.1, hux, spMap_algHom_comp, Category.assoc]
  obtain ⟨q', ⟨-, hq'⟩, -⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c p.R A.R y₀ π X s u hU B.R uB' (q.comp π) hx'
  refine ⟨B, uB, uB', fun k => match k with
    | none => r
    | some ⟨τ, i⟩ => (hYd τ i).unit, q, q', huB, hq',
    (frBor_iff_frChg uB uB' _).2 ⟨Y, hYz, fun τ i => (hYd τ i).unit_spec.symm, huB'⟩, ?_⟩
  intro T _ _ a a' z z' t hz hz' hb
  obtain ⟨g, hgz, hgd, hgc⟩ := (frBor_iff_frChg z z' t).1 hb
  obtain ⟨b, ⟨hb1, hb2, hb3⟩, -⟩ := hY T a g (t none)
    (fun τ i => by rw [hgd]; exact Units.isUnit _) hgz
  have h1 : FrMap b uB z :=
    frMap_cancel (Xo := Xo) (c := c) _ _ _ q b u uB z huB (by rw [hb1]; exact hz)
  have h2 : FrMap b uB' z' := by
    refine (GlobalTheory.T.frameChange_comm_baseChange E H Dw l Xo c B.R T b uB uB' z z' Y r huB' h1).2 ?_
    rw [hb3, funext hb2]
    exact hgc
  have h3 : FrMap (b.comp q') u z' := frMap_trans (Xo := Xo) (c := c) _ _ _ q' b u uB' z' hq' h2
  refine ⟨b, hb1, GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hU T _ _ z' h3 hz', ?_⟩
  rintro (_ | ⟨τ, i⟩)
  · exact hb3
  · show b (Y τ i i) = _
    rw [← hgd, ← hb2 τ]
    rfl

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsBorelPairsUniversalFrameOpenChartStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_borelPairs_universalFrame_openChart : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (p A : TRing c.F) (j : Sp p.R ⟶ Xo.XF c) (y₀ : FrPt Xo c p.R) (π : p.R →ₐ[c.F] A.R) (X : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R)) (s : (A.R)ˣ) (u : FrPt Xo c A.R), OpenChart j y₀ → UnivFrame y₀ π X s u → ∃ (B : TRing c.F) (uB uB' : FrPt Xo c B.R) (tB : Ix Dw → (B.R)ˣ) (q q' : A.R →ₐ[c.F] B.R), FrMap q u uB ∧ FrMap q' u uB' ∧ FrBor tB uB uB' ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (a a' : A.R →ₐ[c.F] T) (z z' : FrPt Xo c T) (t : Ix Dw → Tˣ), FrMap a u z → FrMap a' u z' → FrBor t z z' → ∃ b : B.R →ₐ[c.F] T, b.comp q = a ∧ b.comp q' = a' ∧ ∀ i, b (tB i : B.R) = (t i : T) := by
  first | exact @GlobalTheory.Frames.univFrame_borelPairs | exact GlobalTheory.Frames.univFrame_borelPairs | (intros; apply GlobalTheory.Frames.univFrame_borelPairs <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

theorem ChartCover.exists_lift {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S) :
    ∃ xF : Sp S ⟶ Xo.XF c, xF ≫ pullback.fst _ _ = w.x ∧ xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S) := by
  refine ⟨pullback.lift w.x (spMap (algebraMap c.F S)) ?_, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  rw [w.x_over, spMap_comp_ring]
  rfl

theorem ChartCover.near (hS : Out.SecBaseChangeSt) {R A : Type} [CommRing R] [Algebra c.F R] [CommRing A]
    [Algebra c.F A] {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A} {s : Aˣ} {u : FrPt Xo c A}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (p : Sp S) (hp : xF p ∈ Set.range j) :
    ∃ g : S, g ∉ p.asIdeal ∧ ∀ (T : Type) [CommRing T] [Algebra c.F T] (lam : S →ₐ[c.F] T), IsUnit (lam g) →
      ∃ (z : FrPt Xo c T) (a : A →ₐ[c.F] T), FrMap lam w z ∧ FrMap a u z := by
  obtain ⟨g, hg, hT⟩ := openChart_factor_near_prime E H Dw l Xo c R j y₀ hj S xF h2 p hp
  refine ⟨g, hg, fun T _ _ lam hl => ?_⟩
  obtain ⟨ψ, hψ⟩ := hT T lam hl
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_framedPoint_baseChange_algebraMap hS E H Dw l Xo c S T lam w
  have hx : z.x = spMap ψ.toRingHom ≫ y₀.x := by
    rw [hz.1, ← h1, ← hj.2.1, ← Category.assoc, hψ, Category.assoc]
  obtain ⟨a, ⟨_, ha⟩, _⟩ := GlobalTheory.T.universalFrame_classifies_framedPoints hS E H Dw l Xo c R A y₀ π X s u hu T z ψ hx
  exact ⟨z, a, hz, ha⟩

theorem ChartCover.cls_loc (hS : Out.SecBaseChangeSt) {R : Type} [CommRing R] [Algebra c.F R] {A : TRing c.F}
    {j : Sp R ⟶ Xo.XF c} {y₀ : FrPt Xo c R} {π : R →ₐ[c.F] A.R}
    {X : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) A.R} {s : (A.R)ˣ} {u : FrPt Xo c A.R}
    (hj : OpenChart j y₀) (hu : UnivFrame y₀ π X s u) {S : Type} [CommRing S] [Algebra c.F S] (w : FrPt Xo c S)
    (xF : Sp S ⟶ Xo.XF c) (h1 : xF ≫ pullback.fst _ _ = w.x)
    (h2 : xF ≫ pullback.snd _ _ = spMap (algebraMap c.F S)) (m : Ideal S) [hm : m.IsPrime]
    (hp : xF (⟨m, hm⟩ : PrimeSpectrum S) ∈ Set.range j) :
    ∃ cw : A.R →ₐ[c.F] Localization.AtPrime m,
      ChartCls (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m u cw ∧
      ChartLoc (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) w m A u := by
  obtain ⟨g, hg, hT⟩ := ChartCover.near hS hj hu w xF h1 h2 (⟨m, hm⟩ : PrimeSpectrum S) hp
  obtain ⟨z, a, hz, ha⟩ := hT (Localization.AtPrime m) (locM c.F m)
    (IsLocalization.map_units (Localization.AtPrime m) (⟨g, hg⟩ : m.primeCompl))
  refine ⟨a, ⟨z, hz, ha⟩, ?_⟩
  intro p φ y hy
  obtain ⟨yF, k1, k2⟩ := ChartCover.exists_lift y
  have e : spMap φ.toRingHom ≫ yF = xF := by
    apply pullback.hom_ext
    · rw [Category.assoc, k1, h1, hy.1]
    · rw [Category.assoc, k2, h2, spMap_comp_ring]
      congr 1
      exact φ.comp_algebraMap
  have hq : yF (spMap φ.toRingHom (⟨m, hm⟩ : PrimeSpectrum S)) ∈ Set.range j := by
    rw [← e] at hp
    exact hp
  obtain ⟨g', hg', hT'⟩ := ChartCover.near hS hj hu y yF k1 k2 _ hq
  obtain ⟨p', lam, hl, hlam⟩ := GlobalTheory.testRing_localizationAway c.F p g'
  obtain ⟨z', a', hz', ha'⟩ := hT' p'.R lam hl
  exact ⟨g', hg', p', lam, z', a', hlam, hz', ha'⟩

end

theorem chartCoverF_of_secBaseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartCoverF Xo c := by
  intro hS E _ _ _ H Dw l Xo c S _ _ w w' hw m hm
  obtain ⟨xF, h1, h2⟩ := ChartCover.exists_lift w
  obtain ⟨p, j, y₀, hj, hp⟩ := GlobalTheory.T.exists_openChart_framedPoint_testRing hS E H Dw l Xo c (xF (⟨m, hm.isPrime⟩ : PrimeSpectrum S))
  obtain ⟨A, π, X, s, u, hu⟩ := GlobalTheory.T.exists_universalFrame_testRing hS E H Dw l Xo c p y₀
  obtain ⟨cw, hc, hl⟩ := ChartCover.cls_loc hS hj hu w xF h1 h2 m hp
  obtain ⟨cw', hc', hl'⟩ := ChartCover.cls_loc hS hj hu w' xF (h1.trans hw.symm) h2 m hp
  exact ⟨A, u, cw, cw', GlobalTheory.T.universalFrame_classifies_unique_openChart hS E H Dw l Xo c p.R A.R j y₀ π X s u hj hu,
    GlobalTheory.T.exists_borelPairs_universalFrame_openChart hS E H Dw l Xo c p A j y₀ π X s u hj hu, hc, hl, hc', hl'⟩

end GlobalTheory.Frames
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ChartCoverFOfSectionBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartCoverF_of_sectionBaseChange : Out.SecBaseChangeSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), ChartCoverF Xo c := by
  first | exact @GlobalTheory.Frames.chartCoverF_of_secBaseChange | exact GlobalTheory.Frames.chartCoverF_of_secBaseChange | (intros; apply GlobalTheory.Frames.chartCoverF_of_secBaseChange <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnit
section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnit
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member

namespace GlobalTheory.Member

theorem reindex_finCongr_self {n : ℕ} {α : Type} (h : n = n) (A : Matrix (Fin n) (Fin n) α) :
    Matrix.reindex (finCongr h) (finCongr h) A = A := by
  ext a b
  rfl

theorem fr_orthonormal_unit : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h k, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat (C.fr h k) τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) ∧ C.fr h k ∈ (C.M.X k).dom ∧ (∀ τ i, ‖dmin (C.M.X k).Gm (C.fr h k) τ i‖ = 1) ∧ Continuous (fun u => C.fr u k) ∧ (∀ u ∈ GfC V, C.fr (h * u) k = C.fr h k) ∧ (∀ u, C.fr (h * u) k = rmul (C.fr h k) (archMat V C.th C.hr (fun k => C.fr 1 k) u k)) ∧ ∀ x : Frame (C.M.X k).Ψ r, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) → ∃ u ∈ GinfC V, C.fr u k = x := by
  intro D H Dw l Xo c σ V r C hC h k
  have hr := C.hr
  subst hr
  obtain ⟨hA, -, hL⟩ := GlobalTheory.T.archimedeanMatrix_unitary_continuous_multiplicative D V C.θ hC.inf
  have hG : (C.M.X k).Gm = -V.gramᵀ := by
    rw [(hC.modelW k).1, reindex_finCongr_self]
  have hfr : ∀ u (τ : (C.M.X k).Ψ), mat (C.fr u k) τ = archM V (C.θ τ.1) u * C.x₀ τ.1 := fun u τ => rfl
  have hext : ∀ x y : Frame (C.M.X k).Ψ V.rank, (∀ τ, mat x τ = mat y τ) → x = y :=
    fun x y hxy => funext fun τ => hxy τ
  obtain ⟨-, h2, h3⟩ := GlobalTheory.UnitFrames.unit_frame_eq_orthonormal_mul_triangular D.host.E V.rank (C.M.X k).p0
    (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm
  obtain ⟨-, h4⟩ := GlobalTheory.UnitFrames.frame_mul_triangular_orthonormal D.host.E V.rank (C.M.X k).p0
    (C.M.X k).Ψ (C.M.X k).Gm (C.M.X k).Gm_herm
  have horth : ∀ u (τ : (C.M.X k).Ψ), gram τ.1 (C.M.X k).Gm (mat (C.fr u k) τ) =
      Matrix.diagonal fun a : Fin V.rank => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ) := by
    intro u τ
    rw [hfr, h3 τ.1 _ _ (by rw [hG]; exact (hA τ.1).2.2.2.2 u)]
    exact hC.orth k τ.1 τ.2
  refine ⟨horth h, (h2 _ (horth h)).1, (h2 _ (horth h)).2, ?_, fun u hu => ?_, fun u => ?_, fun x hx => ?_⟩
  · refine continuous_pi fun τ => ?_
    exact (hA τ.1).2.2.2.1.matrix_mul (continuous_const (y := C.x₀ τ.1))
  · refine hext _ _ fun τ => ?_
    rw [hfr, hfr, (hA τ.1).2.1, (hA τ.1).2.2.1 u hu, mul_one]
  · refine hext _ _ fun τ => ?_
    have hd : IsUnit (C.x₀ τ.1).det := by
      have := ((h2 _ (horth 1)).1 τ).1
      rw [hfr, (hA τ.1).1, one_mul] at this
      exact isUnit_iff_ne_zero.2 this
    show _ = mat (C.fr h k) τ * ((mat (C.fr 1 k) τ)⁻¹ * archM V (C.θ τ.1) u * mat (C.fr 1 k) τ)
    rw [hfr, hfr, hfr, (hA τ.1).2.1, (hA τ.1).1, one_mul, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_nonsing_inv_cancel_left _ _ hd]
  · have hmem : ∀ τ : D.host.E →+* ℂ, τ ∈ (C.M.X k).Ψ ↔
        τ D.host.sqrtMinusD = D.host.φ₀ D.host.sqrtMinusD := by
      intro τ
      rw [(hC.base.type k).2 τ, hC.iota.rt, hC.iota.rt0]
    have hex : ∀ τ : D.host.E →+* ℂ, ∃ u : Matrix (Fin V.rank) (Fin V.rank) ℂ, ∀ hτ : τ ∈ (C.M.X k).Ψ,
        uᵀ * (-V.gramᵀ).map τ * u.map (starRingEnd ℂ) = (-V.gramᵀ).map τ ∧ mat x ⟨τ, hτ⟩ = u * C.x₀ τ := by
      intro τ
      by_cases hτ : τ ∈ (C.M.X k).Ψ
      · obtain ⟨u, hu⟩ := h4 τ (C.x₀ τ) (mat x ⟨τ, hτ⟩) (hC.orth k τ hτ)
          ((hx ⟨τ, hτ⟩).trans (hC.orth k τ hτ).symm)
        rw [hG] at hu
        exact ⟨u, fun _ => hu⟩
      · exact ⟨1, fun h' => absurd h' hτ⟩
    choose u hu using hex
    obtain ⟨a, ha, hau⟩ := hL u fun τ hτ => (hu τ ((hmem τ).2 hτ)).1
    refine ⟨a, ha, hext _ _ fun τ => ?_⟩
    rw [hfr, hau τ.1 ((hmem τ.1).1 τ.2)]
    exact ((hu τ.1 τ.2).2).symm

end GlobalTheory.Member
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MemberDictionaryFramesOrthonormalUnitStatement
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Member
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.memberDictionary_frames_orthonormal_unit : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → ∀ h k, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat (C.fr h k) τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) ∧ C.fr h k ∈ (C.M.X k).dom ∧ (∀ τ i, ‖dmin (C.M.X k).Gm (C.fr h k) τ i‖ = 1) ∧ Continuous (fun u => C.fr u k) ∧ (∀ u ∈ GfC V, C.fr (h * u) k = C.fr h k) ∧ (∀ u, C.fr (h * u) k = rmul (C.fr h k) (archMat V C.th C.hr (fun k => C.fr 1 k) u k)) ∧ ∀ x : Frame (C.M.X k).Ψ r, (∀ τ : (C.M.X k).Ψ, gram τ.1 (C.M.X k).Gm (mat x τ) = Matrix.diagonal fun a : Fin r => ((sgn (C.M.X k).p0 (a : ℕ) : ℝ) : ℂ)) → ∃ u ∈ GinfC V, C.fr u k = x := by
  first | exact @GlobalTheory.Member.fr_orthonormal_unit | exact GlobalTheory.Member.fr_orthonormal_unit | (intros; apply GlobalTheory.Member.fr_orthonormal_unit <;> assumption)
end
end
