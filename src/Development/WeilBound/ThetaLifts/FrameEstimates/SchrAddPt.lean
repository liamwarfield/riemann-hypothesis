module

public import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
public import Development.WeilBound.ThetaLifts.LeviDeterminants.GrowFin
public import Development.WeilBound.CoreStatements.LocalThetaKernels.LinearIndependentOfNotMem
public import Development.AutomorphicSpectrum.Proofs.TwistedProofs.EqZeroOfPiInf

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.FrameEstimates.LevelA
noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace levelStructure

open LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem finiteAdeleIdempotentOfF_mul_self (a : AF F) : e0 F * a = ((0, a.2) : Ainf F × Af F) := Prod.ext (zero_mul a.1) (one_mul a.2)

theorem int_mul {a b : Af F} (ha : Int' a) (hb : Int' b) : Int' (a * b) := fun v => mul_mem (ha v) (hb v)

theorem int_add {a b : Af F} (ha : Int' a) (hb : Int' b) : Int' (a + b) := fun v => add_mem (ha v) (hb v)

theorem int_neg {a : Af F} (ha : Int' a) : Int' (-a) := fun v => neg_mem (ha v)

theorem int_zero : Int' (0 : Af F) := fun _ => zero_mem _

theorem int_sum {ι : Type} (s : Finset ι) {a : ι → Af F} (ha : ∀ i, Int' (a i)) : Int' (∑ i ∈ s, a i) :=
  Finset.sum_induction _ _ (fun _ _ => int_add) int_zero fun i _ => ha i


variable (E) in
theorem exists_lattice (V : Set (AE F E)) (hV : V ∈ 𝓝 (0 : AE F E)) :
    ∃ Λ : AddSubgroup (AE F E), (∀ z ∈ Λ, ∀ z' ∈ Λ, z * z' ∈ Λ) ∧ (Λ : Set (AE F E)) ⊆ V ∧
      ∃ V' ∈ 𝓝 (0 : AE F E), ∀ z ∈ V', e0 F • z = z → z ∈ Λ := by
  classical
  have := ring_AE F E
  have : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have hs : ContinuousSMul (AF F) (AE F E) := IsModuleTopology.toContinuousSMul _ _
  let b := Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)
  let c : AE F E → Fin (Module.finrank F E) → Af F := fun z i => (b.repr z i).2
  have hc : Continuous c := continuous_pi fun i =>
    continuous_snd.comp (IsModuleTopology.continuous_of_linearMap (b.coord i))
  let j : (Fin (Module.finrank F E) → Af F) → AE F E := fun y => ∑ i, (show AF F from ((0, y i) : Ainf F × Af F)) • b i
  have hj : Continuous j := continuous_finsetSum _ fun i _ =>
    (show Continuous fun y : Fin (Module.finrank F E) → Af F => (show AF F from ((0, y i) : Ainf F × Af F)) from
      continuous_const.prodMk (continuous_apply i)).smul continuous_const
  have hj0 : j 0 = 0 := Finset.sum_eq_zero fun i _ => zero_smul (AF F) (b i)
  have hO : {a : Af F | Int' a} ∈ 𝓝 (0 : Af F) := (GlobalTheory.AdLat.OpenLat.isOpen_integral F).mem_nhds int_zero
  have h1 : j ⁻¹' V ∈ 𝓝 0 := hj.continuousAt.preimage_mem_nhds (hj0 ▸ hV)
  obtain ⟨N₁, hN₁, h₁⟩ := exists_pi _ h1
  have h2 : ∀ᶠ a in 𝓝 (0 : Af F), ∀ i j k, Int' (a * c (b i * b j) k) :=
    eventually_all.2 fun i => eventually_all.2 fun j => eventually_all.2 fun k =>
      ((continuous_mul_const (c (b i * b j) k)).tendsto' 0 0 (zero_mul _)).eventually hO
  obtain ⟨N₂, hN₂, h₂⟩ := GlobalTheory.AdLat.OpenLat.exists_nsmul_adele F _ h2
  let Λ : AddSubgroup (AE F E) :=
    { carrier := {z | e0 F • z = z ∧ ∃ a : Fin (Module.finrank F E) → Af F, (∀ i, Int' (a i)) ∧ c z = (N₁ * N₂) • a}
      zero_mem' := ⟨smul_zero _, 0, fun _ => int_zero, by funext i; simp [c]⟩
      add_mem' := fun {x y} hx hy => by
        obtain ⟨h, a, ha, e⟩ := hx
        obtain ⟨h', a', ha', e'⟩ := hy
        refine ⟨by rw [smul_add, h, h'], a + a', fun i => int_add (ha i) (ha' i), ?_⟩
        rw [smul_add, ← e, ← e']
        funext i
        simp only [c, map_add (f := _)]
        rfl
      neg_mem' := fun {x} hx => by
        obtain ⟨h, a, ha, e⟩ := hx
        refine ⟨by rw [smul_neg, h], -a, fun i => int_neg (ha i), ?_⟩
        rw [smul_neg, ← e]
        funext i
        simp only [c, map_neg]
        rfl }
  refine ⟨Λ, ?_, ?_, ?_⟩
  · rintro z ⟨h, a, ha, e⟩ z' ⟨h', a', ha', e'⟩
    refine ⟨by rw [← smul_mul_assoc, h], fun k => ∑ i, ∑ j, N₂ • (N₁ • (a i * a' j)) * c (b i * b j) k,
      fun k => int_sum _ fun i => int_sum _ fun j => h₂ _ ((int_mul (ha i) (ha' j)).nsmul N₁) i j k, ?_⟩
    funext k
    have e1 : c (z * z') k = ∑ i, ∑ j, c z i * c z' j * c (b i * b j) k := by
      have e1 : z * z' = ∑ i, ∑ j, (b.repr z i * b.repr z' j) • (b i * b j) := by
        conv_lhs => rw [← b.sum_repr z, ← b.sum_repr z', Finset.sum_mul_sum]
        simp only [smul_mul_smul_comm]
      change (RingHom.snd (Ainf F) (Af F) : AF F →+* Af F) (b.repr (z * z') k) = _
      rw [e1]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]
      simp only [map_mul, c]
      rfl
    rw [e1, e, e', Pi.smul_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Pi.smul_apply, nsmul_eq_mul, Nat.cast_mul]
    ring
  · rintro z ⟨h, a, ha, e⟩
    have e1 : j (c z) = z := by
      conv_rhs => rw [← h, ← b.sum_repr z, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, finiteAdeleIdempotentOfF_mul_self]
    rw [← e1, e]
    exact h₁ _ (dvd_mul_right _ _) a ha
  · have hN : ((N₁ * N₂ : ℕ) : F) ≠ 0 := Nat.cast_ne_zero.2 (Nat.mul_pos hN₁ hN₂).ne'
    let t : Af F := algebraMap F (Af F) ((N₁ * N₂ : ℕ) : F)⁻¹
    have h3 : ∀ᶠ z in 𝓝 (0 : AE F E), ∀ i, Int' (t * c z i) := eventually_all.2 fun i =>
      ((show Continuous fun z => t * c z i from continuous_const.mul ((continuous_apply i).comp hc)).tendsto' 0 0 (by
        have : c 0 i = 0 := by simp [c]
        rw [this, mul_zero])).eventually hO
    refine ⟨_, h3, fun z hz h => ⟨h, fun i => t * c z i, hz, funext fun i => ?_⟩⟩
    rw [Pi.smul_apply, nsmul_eq_mul, ← mul_assoc, ← map_natCast (algebraMap F (Af F)), ← map_mul, mul_inv_cancel₀ hN,
      map_one, one_mul]

variable {d : ℕ} {J : Matrix (Fin d) (Fin d) E}

def IsFin (u : UA σ J) : Prop := e0 F • (mat u - 1) = mat u - 1

omit [NumberField E] in
theorem IsFin.inv {u : UA σ J} (h : IsFin u) : IsFin u⁻¹ := by
  have e : mat u⁻¹ - 1 = -(mat u⁻¹ * (mat u - 1)) := by
    rw [mul_sub, show mat u⁻¹ * mat u = 1 from Units.inv_mul u.1, mul_one, neg_sub]
  unfold IsFin at h ⊢
  rw [e, smul_neg, ← Matrix.mul_smul, h]

theorem pow_near (U : Set (UA σ J)) (hU : U ∈ 𝓝 (1 : UA σ J)) :
    ∀ᶠ u in 𝓝 (1 : UA σ J), IsFin u → ∀ p : ℕ, u ^ p ∈ U := by
  classical
  have := ring_AE F E
  let L : Filter (UA σ J) := ⨅ V ∈ 𝓝 (0 : AE F E), 𝓟 {h | (∀ i j, (mat h - 1) i j ∈ V) ∧ ∀ i j, (mat h⁻¹ - 1) i j ∈ V}
  have ent : ∀ f : UA σ J → Matrix (Fin d) (Fin d) (AE F E),
      (∀ V ∈ 𝓝 (0 : AE F E), ∀ᶠ h in L, ∀ i j, (f h - 1) i j ∈ V) → Tendsto f L (𝓝 1) := fun f hf => by
    refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => fun V hV => ?_
    have hc : Continuous fun z : AE F E => z + (1 : Matrix (Fin d) (Fin d) (AE F E)) i j :=
      continuous_id.add continuous_const
    rw [mem_map]
    filter_upwards [hf _ (hc.continuousAt.preimage_mem_nhds (by rwa [zero_add]))] with h hh
    simpa using hh i j
  have hL : L ≤ 𝓝 1 := by
    have : Tendsto (fun h : UA σ J => h) L (𝓝 1) := by
      refine tendsto_subtype_rng.2 (Units.isInducing_embedProduct.tendsto_nhds_iff.2 ?_)
      exact (ent mat fun V hV => mem_iInf_of_mem V (mem_iInf_of_mem hV fun h hh => hh.1)).prodMk_nhds
        ((MulOpposite.continuous_op.tendsto _).comp
          (ent (fun h => mat h⁻¹) fun V hV => mem_iInf_of_mem V (mem_iInf_of_mem hV fun h hh => hh.2)))
    exact this
  obtain ⟨V, hV, hVU⟩ : ∃ V ∈ 𝓝 (0 : AE F E),
      {h | (∀ i j, (mat h - 1) i j ∈ V) ∧ ∀ i j, (mat h⁻¹ - 1) i j ∈ V} ⊆ U := by
    refine (mem_biInf_of_directed ?_ ⟨_, univ_mem⟩).1 (hL hU)
    intro V hV V' hV'
    exact ⟨V ∩ V', inter_mem hV hV', principal_mono.2 fun h hh => ⟨fun i j => (hh.1 i j).1, fun i j => (hh.2 i j).1⟩,
      principal_mono.2 fun h hh => ⟨fun i j => (hh.1 i j).2, fun i j => (hh.2 i j).2⟩⟩
  obtain ⟨Λ, hmul, hΛ, V', hV', hop⟩ := exists_lattice E V hV
  have key : ∀ u : UA σ J, (∀ i j, (mat u - 1) i j ∈ Λ) → ∀ p : ℕ, ∀ i j, (mat (u ^ p) - 1) i j ∈ Λ := by
    intro u hu p
    induction p with
    | zero => intro i j; rw [pow_zero, show mat (1 : UA σ J) = 1 from rfl, sub_self]; exact zero_mem _
    | succ p ih =>
      intro i j
      have e : mat (u ^ (p + 1)) - 1 = (mat (u ^ p) - 1) * (mat u - 1) + (mat (u ^ p) - 1) + (mat u - 1) := by
        rw [pow_succ, show mat (u ^ p * u) = mat (u ^ p) * mat u from rfl]; noncomm_ring
      rw [e, Matrix.add_apply, Matrix.add_apply, Matrix.mul_apply]
      exact add_mem (add_mem (sum_mem fun k _ => hmul _ (ih i k) _ (hu k j)) (ih i j)) (hu i j)
  have ent' : ∀ f : UA σ J → Matrix (Fin d) (Fin d) (AE F E), Continuous f → f 1 = 1 →
      ∀ᶠ h in 𝓝 (1 : UA σ J), ∀ i j, (f h - 1) i j ∈ V' := fun f hf h1 => by
    refine eventually_all.2 fun i => eventually_all.2 fun j => ?_
    have hc : Continuous fun h => (f h - 1) i j := (hf.sub continuous_const).matrix_elem i j
    exact hc.continuousAt.preimage_mem_nhds (by simpa [h1] using hV')
  filter_upwards [ent' mat (Units.continuous_val.comp continuous_subtype_val) rfl,
    ent' (fun h => mat h⁻¹) continuous_mat_inv rfl] with u h1 h2 hu p
  refine hVU ⟨fun i j => hΛ (key u (fun i j => hop _ (h1 i j) (congrFun (congrFun hu i) j)) p i j), fun i j => hΛ ?_⟩
  rw [← inv_pow]
  exact key u⁻¹ (fun i j => hop _ (h2 i j) (congrFun (congrFun hu.inv i) j)) p i j

end levelStructure

end PositivityTheory.ThKEst

end
end

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

namespace levelStructure

open LatticeQuotientMeasure PositivityTheory.ThKF0.Grow PositivityTheory.ThKF0.Grow.Fi

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem schr_add_pt (ψ : AddChar (AF F) ℂ) (w δ : Pt F κ) (Φ : (κ → AF F) → ℂ) :
    schr ψ (w + δ) Φ = ψ (⅟(2 : AF F) * (δ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ δ.2)) • schr ψ w (schr ψ δ Φ) := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x]
  congr 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (w.1 ⬝ᵥ δ.2) * invOf_mul_self (2 : AF F)

theorem lc_fin {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) :
    IsLocallyConstant fun a : Af F => ψ ((0, a) : Ainf F × Af F) :=
  GlobalTheory.CompanionTheory.AdelicHeis.isLocallyConstant_fin (ψ.compAddMonoidHom (AddMonoidHom.inr (Ainf F) (Af F)))
    (hψ.1.comp (continuous_const.prodMk continuous_id)) fun _ => GlobalTheory.CompanionTheory.AdelicHeis.norm_eq_one ψ hψ.1 hψ.2.1 _

theorem fst_zero {a : AF F} (h : e0 F * a = a) : a.1 = 0 := by
  rw [← h, finiteAdeleIdempotentOfF_mul_self]

theorem fix_near {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F)) :
    ∀ᶠ u in 𝓝 (0 : Pt F κ), e0 F • u = u → ∀ f, schr ψ u (pureA F f g) = pureA F f g := by
  have hc : Continuous fun u : Pt F κ => ((fun i => (u.1 i).2, fun i => (u.2 i).2) : (κ → Af F) × (κ → Af F)) :=
    (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp continuous_fst)).prodMk
      (continuous_pi fun i => continuous_snd.comp ((continuous_apply i).comp continuous_snd))
  have h := (hc.tendsto 0).eventually
    (eventually_fix _ (lc_fin hψ) ψ.map_zero_eq_one (⅟(2 : AF F)).2 hg)
  filter_upwards [h] with u key hu f
  funext x
  have h1 : ∀ i, (u.1 i).1 = 0 := fun i => fst_zero (congrFun (congrArg Prod.fst hu) i)
  have h2 : ∀ i, (u.2 i).1 = 0 := fun i => fst_zero (congrFun (congrArg Prod.snd hu) i)
  have p : ψ (x ⬝ᵥ u.2 + ⅟(2 : AF F) * (u.1 ⬝ᵥ u.2)) = ψ ((0, ((fun i => (x i).2) ⬝ᵥ fun i => (u.2 i).2) +
      (⅟(2 : AF F)).2 * ((fun i => (u.1 i).2) ⬝ᵥ fun i => (u.2 i).2)) : Ainf F × Af F) := by
    rw [← dot_snd, ← dot_snd]
    refine congrArg ψ (Prod.ext ?_ rfl)
    change (x ⬝ᵥ u.2).1 + (⅟(2 : AF F)).1 * (u.1 ⬝ᵥ u.2).1 = 0
    rw [dot_fst _ _ h2, dot_fst _ _ h2, mul_zero, add_zero]
  have q : (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F ((x + u.1) i).1) =
      fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (x i).1 := by
    funext i
    change InfiniteAdeleRing.ringEquiv_mixedSpace F ((x i).1 + (u.1 i).1) = _
    rw [h1 i, add_zero]
  simp only [schr, pureA]
  rw [p, q, mul_left_comm]
  exact congrArg _ (key fun i => (x i).2)

theorem schr_near {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {g : (κ → Af F) → ℂ} (hg : g ∈ SB (κ → Af F))
    {K : Set (Pt F κ)} (hK : IsCompact K) : ∀ᶠ δ in 𝓝 (0 : Pt F κ), e0 F • δ = δ → ∀ c ∈ K, ∀ w, e0 F • w = e0 F • c →
      ∀ f, schr ψ (w + δ) (pureA F f g) = schr ψ w (pureA F f g) := by
  have h1 : ∀ᶠ δ in 𝓝 (0 : Pt F κ), ∀ c ∈ K, ψ (e0 F * (⅟(2 : AF F) * (δ.1 ⬝ᵥ c.2 - c.1 ⬝ᵥ δ.2))) = 1 := by
    refine hK.eventually_forall_of_forall_eventually fun c _ => ?_
    have hc : Continuous fun z : Pt F κ × Pt F κ => ⅟(2 : AF F) * (z.1.1 ⬝ᵥ z.2.2 - z.2.1 ⬝ᵥ z.1.2) := by
      unfold dotProduct; fun_prop
    filter_upwards [((lc_fin hψ).comp_continuous (continuous_snd.comp hc)).eventually_eq (0, c)] with z hz
    rw [finiteAdeleIdempotentOfF_mul_self]
    refine hz.trans ?_
    simp only [Function.comp, Prod.fst_zero, Prod.snd_zero, zero_dotProduct, dotProduct_zero, sub_zero, mul_zero]
    exact ψ.map_zero_eq_one
  filter_upwards [h1, fix_near hψ hg] with δ h1 h2 hδ c hc w hw f
  have e : ⅟(2 : AF F) * (δ.1 ⬝ᵥ w.2 - w.1 ⬝ᵥ δ.2) = e0 F * (⅟(2 : AF F) * (δ.1 ⬝ᵥ c.2 - c.1 ⬝ᵥ δ.2)) := by
    have a1 : e0 F • δ.1 = δ.1 := congrArg Prod.fst hδ
    have a2 : e0 F • δ.2 = δ.2 := congrArg Prod.snd hδ
    have b1 : e0 F • w.1 = e0 F • c.1 := congrArg Prod.fst hw
    have b2 : e0 F • w.2 = e0 F • c.2 := congrArg Prod.snd hw
    have c1 : δ.1 ⬝ᵥ w.2 = e0 F * (δ.1 ⬝ᵥ c.2) := by
      conv_lhs => rw [← a1, smul_dotProduct, ← dotProduct_smul, b2, dotProduct_smul, smul_eq_mul]
    have c2 : w.1 ⬝ᵥ δ.2 = e0 F * (c.1 ⬝ᵥ δ.2) := by
      conv_lhs => rw [← a2, dotProduct_smul, ← smul_dotProduct, b1, smul_dotProduct, smul_eq_mul]
    rw [c1, c2]; ring
  rw [schr_add_pt, h2 hδ f, e, h1 c hc, one_smul]

open Classical in
theorem ev_adm (y : κ → AF F) : (LinearMap.proj y : ((κ → AF F) → ℂ) →ₗ[ℂ] ℂ) ∈ (adeleClass F).adm κ := by
  intro g _
  refine ⟨g (fun i => (y i).2) •
    (BoundedContinuousFunction.evalCLM ℂ (fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ _ ℂ), fun f => ?_⟩
  exact mul_comm _ _

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isFin_of (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {d : ℕ} {J : Matrix (Fin d) (Fin d) E}
    {u : UA σ J} (hu : ∀ w, (mat u).map (piInf (τ w)) = 1) : IsFin u := by
  refine Matrix.ext fun i j => ?_
  have h0 : ∀ w, piInf (τ w) ((mat u - 1) i j) = 0 := fun w => by
    have : (mat u - 1).map (piInf (τ w)) = 0 := by
      rw [Matrix.map_sub _ (map_sub _), hu, Matrix.map_one _ (map_zero _) (map_one _), sub_self]
    exact congrFun (congrFun this i) j
  have := GlobalTheory.CompanionTheory.CMAdele.eq_zero_of_piInf σ h τ ((1 - e0 F) • (mat u - 1) i j) ((at_iff _).2 (by
    rw [smul_smul, mul_sub, mul_one, show e0 F * e0 F = e0 F from finiteAdeleIdempotentOfF_mul_self _, sub_self, zero_smul])) fun w => by
      rw [Algebra.smul_def, map_mul, h0, mul_zero]
  rw [sub_smul, one_smul, sub_eq_zero] at this
  exact this.symm

theorem coef_near {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {g : (Fin n × Fin d → Af F) → ℂ} (hg : g ∈ SB _) {C : Set (Ten F E n d)} (hC : IsCompact C) :
    ∀ᶠ u in 𝓝 (1 : UA σ W.J), IsFin u → ∀ z : Ten F E n d, (∃ c ∈ C, At (evI F) (z - c)) → ∀ f,
      schr ψ (M.co.e (z * (mat u)ᵀ)) (pureA F f g) = schr ψ (M.co.e z) (pureA F f g) := by
  have := ring_AE F E
  have : IsModuleTopology (AF F) (Ten F E n d) := inferInstanceAs (IsModuleTopology (AF F) (Fin n → Fin d → AE F E))
  have he : Continuous M.co.e := IsModuleTopology.continuous_of_linearMap M.co.e.toLinearMap
  have hV := schr_near hψ hg (hC.image he)
  have hm : Continuous fun z : UA σ W.J × Ten F E n d => M.co.e (z.2 * (mat z.1 - 1)ᵀ) :=
    he.comp (continuous_snd.matrix_mul
      (((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).sub continuous_const).matrix_transpose)
  have h1 := hC.eventually_forall_of_forall_eventually (x₀ := (1 : UA σ W.J))
    (P := fun u c => M.co.e (c * (mat u - 1)ᵀ) ∈ _) fun c _ => hm.continuousAt.preimage_mem_nhds (by
      rwa [show mat (1 : UA σ W.J) = 1 from rfl, sub_self, Matrix.transpose_zero, Matrix.mul_zero, map_zero])
  filter_upwards [h1] with u h1 hu z hz f
  obtain ⟨c, hc, hz⟩ := hz
  rw [at_iff, smul_sub, sub_eq_zero] at hz
  have hu' : e0 F • (mat u - 1)ᵀ = (mat u - 1)ᵀ := by rw [← Matrix.transpose_smul, hu]
  have e : z * (mat u)ᵀ = z + c * (mat u - 1)ᵀ := by
    rw [← hu', Matrix.mul_smul, ← Matrix.smul_mul, ← hz, Matrix.smul_mul, ← Matrix.mul_smul, hu', Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.mul_sub, Matrix.mul_one, add_sub_cancel]
  rw [e, map_add (f := _)]
  exact h1 c hc (by rw [← map_smul, ← Matrix.mul_smul, hu']) _ ⟨c, hc, rfl⟩ _ (by rw [← map_smul, ← map_smul, hz]) f

end levelStructure


open levelStructure in
theorem level_of (hC : CoefEq) (hF : FourierInj) (hB : CoefBd) : Level := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hp φ hφ
  by_cases h0 : ∀ f : SInf F (Fin n × Fin d), pureA F f φ = 0
  · exact ⟨Set.univ, univ_mem, fun u _ _ f => by rw [h0, map_zero]⟩
  push Not at h0
  obtain ⟨f₀, h0⟩ := h0
  obtain ⟨y, hy⟩ := Function.ne_iff.1 h0
  have hy : pureA F f₀ φ y ≠ 0 := hy
  have hs := IsUWeilPair.isUSplitting hp.weil
  have mem : ∀ f : SInf F (Fin n × Fin d), pureA F f φ ∈ schA F (Fin n × Fin d) := fun f =>
    Submodule.subset_span ⟨f, φ, hφ, rfl⟩
  obtain ⟨μ, hμ, -⟩ := ParityOfCoefficients.exists_haar (F := F) (κ := Fin n × Fin d)
  obtain ⟨p, C, -, hCc, hb⟩ := hB F E σ B n d X W M χX χW om r s r' s' hp μ hμ φ hφ φ hφ 0
  have h1 := coef_near M hp.base.std hφ hCc
  have := LatticeQuotientMeasure.ring_AE F E
  have hi : Continuous fun u : UA σ W.J => u⁻¹ :=
    ((continuous_inv (G := GL (Fin d) (AE F E))).comp continuous_subtype_val).subtype_mk fun u => (u⁻¹).2
  have h2 := (hi.tendsto' 1 1 inv_one).eventually h1
  have hc : Continuous fun u : UA σ W.J => ‖om (1, u) (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ :=
    ((((hs.cont _ (ev_adm y) _ (mem f₀)).comp (continuous_const.prodMk continuous_id)).div_const _).sub
      continuous_const).norm
  have h3 := pow_near _ ((isOpen_lt hc (continuous_const (y := (1 / 2 : ℝ)))).mem_nhds (by
    change ‖om 1 (pureA F f₀ φ) y / pureA F f₀ φ y - 1‖ < 1 / 2
    rw [map_one, Module.End.one_apply, div_self hy]
    norm_num))
  refine ⟨_, h1.and (h2.and h3), fun u ⟨h1, h2, h3⟩ hu => ?_⟩
  have hu := isFin_of hp.base.cm B.emb hu
  have key : ∀ (f : SInf F (Fin n × Fin d)) x, om (1, u) (pureA F f φ) x * (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) =
      pureA F f φ x * (starRingEnd ℂ) (pureA F f₀ φ y) := by
    intro f x
    refine hF F _ B.ψ hp.base.std μ hμ _ (hs.pres _ _ (mem f)) _ (hs.pres _ _ (mem f₀)) _ (mem f) _ (mem f₀) ?_ x y
    funext w
    obtain ⟨z, rfl⟩ := M.co.e.surjective w
    rw [hC F E σ B n d X W M χX χW om r s r' s' hp μ hμ _ (mem f) _ (mem f₀), ParityOfCoefficients.mat_one_inv, Matrix.one_mul]
    by_cases a : ∃ c ∈ C, At (evI F) (z - c)
    · unfold coef
      rw [h2 hu.inv z a]
    by_cases a' : ∃ c ∈ C, At (evI F) (z * (mat u⁻¹)ᵀ - c)
    · unfold coef
      rw [← h1 hu _ a', Matrix.mul_assoc, ← Matrix.transpose_mul, show mat u * mat u⁻¹ = 1 from Units.mul_inv u.1,
        Matrix.transpose_one, Matrix.mul_one]
    have b := hb f f₀ z
    have b' := hb f f₀ (z * (mat u⁻¹)ᵀ)
    rw [maj, if_neg a, mul_zero, norm_le_zero_iff] at b
    rw [maj, if_neg a', mul_zero, norm_le_zero_iff] at b'
    rw [b, b']
  have h4 : (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y) ≠ 0 := fun h => by
    have := key f₀ y
    rw [h, mul_zero, eq_comm, mul_eq_zero, map_eq_zero, or_self] at this
    exact hy this
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ f : SInf F (Fin n × Fin d), om (1, u) (pureA F f φ) = c • pureA F f φ :=
    ⟨(starRingEnd ℂ) (pureA F f₀ φ y) / (starRingEnd ℂ) (om (1, u) (pureA F f₀ φ) y), fun f => funext fun x => by
      rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff h4, key, mul_comm]⟩
  have h5 : ∀ k : ℕ, om (1, u ^ k) (pureA F f₀ φ) = c ^ k • pureA F f₀ φ := fun k => by
    induction k with
    | zero => rw [pow_zero, pow_zero, one_smul]; exact congrArg (· (pureA F f₀ φ)) (map_one om)
    | succ k ih =>
      rw [pow_succ, show ((1, u ^ k * u) : UA σ X.J × UA σ W.J) = (1, u ^ k) * (1, u) from by simp, map_mul,
        Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ']
  have h6 : c = 1 := PositivityTheory.ThKH.Locrep.eq_one_of_pow_near fun k => by
    have := h3 hu k
    rwa [Set.mem_ofPred_eq, h5, Pi.smul_apply, smul_eq_mul, mul_div_assoc, div_self hy, mul_one] at this
  intro f
  rw [hc, h6, one_smul]

end PositivityTheory.ThKEst

end
