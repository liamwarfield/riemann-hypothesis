module

public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.TrMulComm
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PCompat
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfConv
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.InfinitesimalCharacterGL.PChart

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.ContinuousEmbInf
noncomputable section

open NumberField MeasureTheory Matrix
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc
open PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4

namespace PositivityTheory.Rg.BcB.CG

namespace PSumH

variable {n : ℕ}

theorem isClosed_nilrad (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) :
    IsClosed (nilrad W₁ W₂ : Set (Matrix (Fin n) (Fin n) ℂ)) := by
  have hW : ∀ W : Submodule ℂ (Fin n → ℂ), IsClosed (W : Set (Fin n → ℂ)) := fun W =>
    W.closed_of_finiteDimensional
  have hc : ∀ y : Fin n → ℂ, Continuous fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y := fun y =>
    continuous_id.matrix_mulVec continuous_const
  have e : (nilrad W₁ W₂ : Set (Matrix (Fin n) (Fin n) ℂ)) =
      (⋂ y, (fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y) ⁻¹' W₂) ∩
        ((⋂ y ∈ W₂, (fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y) ⁻¹' W₁) ∩
          ⋂ y ∈ W₁, (fun X : Matrix (Fin n) (Fin n) ℂ => X *ᵥ y) ⁻¹' {0}) := by
    ext X
    simp only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe, Set.mem_singleton_iff]
    exact Iff.rfl
  rw [e]
  refine (isClosed_iInter fun y => (hW W₂).preimage (hc y)).inter
    ((isClosed_biInter fun y _ => (hW W₁).preimage (hc y)).inter
      (isClosed_biInter fun y _ => isClosed_singleton.preimage (hc y)))

theorem integrable_nil {f : GL (Fin n) ℂ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f)
    {W₁ W₂ : Submodule ℂ (Fin n → ℂ)} (u : nilrad W₁ W₂ → GL (Fin n) ℂ) (hu : ∀ X, (u X).val = 1 + X.1)
    (d : GL (Fin n) ℂ) [MeasurableSpace (nilrad W₁ W₂)] [BorelSpace (nilrad W₁ W₂)] (ν : Measure (nilrad W₁ W₂))
    [ν.IsAddHaarMeasure] : Integrable (fun X => f (u X * d)) ν := by
  have hu' : u = fun X => ((PVC.eH W₁ W₂ X : PVC.nilSub W₁ W₂) : GL (Fin n) ℂ) :=
    funext fun X => Units.ext (by rw [hu X]; rfl)
  have hcu : Continuous u := by
    rw [hu']; exact continuous_subtype_val.comp (PVC.eH W₁ W₂).continuous
  have hF : Continuous fun X => f (u X * d) := hf.comp (hcu.mul continuous_const)
  refine hF.integrable_of_hasCompactSupport ?_
  have hL : IsCompact ((fun k : GL (Fin n) ℂ => (k * d⁻¹).val - 1) '' tsupport f) :=
    hfc.isCompact.image ((Units.continuous_val.comp (continuous_id.mul continuous_const)).sub continuous_const)
  have hK : IsCompact (Subtype.val ⁻¹' ((fun k : GL (Fin n) ℂ => (k * d⁻¹).val - 1) '' tsupport f) :
      Set (nilrad W₁ W₂)) :=
    (isClosed_nilrad W₁ W₂).isClosedEmbedding_subtypeVal.isCompact_preimage hL
  refine HasCompactSupport.intro hK fun X hX => ?_
  by_contra h
  apply hX
  refine ⟨u X * d, subset_tsupport _ h, ?_⟩
  show ((u X * d) * d⁻¹).val - 1 = X.1
  rw [mul_inv_cancel_right, hu X, add_sub_cancel_left]

theorem veryCusp_add {f g : GL (Fin n) ℂ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) (hg : Continuous g)
    (hgc : HasCompactSupport g) (hf' : VeryCusp f) (hg' : VeryCusp g) : VeryCusp fun x => f x + g x := by
  refine ⟨fun k d hk => by dsimp only; rw [hf'.1 k d hk, hg'.1 k d hk], fun d W₁ W₂ hne hle hp1 hp2 u hu _ _ ν _ => ?_⟩
  rw [integral_add (integrable_nil hf hfc u hu d ν) (integrable_nil hg hgc u hu d ν),
    hf'.2 d W₁ W₂ hne hle hp1 hp2 u hu ν, hg'.2 d W₁ W₂ hne hle hp1 hp2 u hu ν, add_zero]

theorem veryCusp_smul {f : GL (Fin n) ℂ → ℂ} (c : ℂ) (hf : VeryCusp f) : VeryCusp fun x => c * f x := by
  refine ⟨fun k d hk => by dsimp only; rw [hf.1 k d hk], fun d W₁ W₂ hne hle hp1 hp2 u hu _ _ ν _ => ?_⟩
  rw [integral_const_mul, hf.2 d W₁ W₂ hne hle hp1 hp2 u hu ν, mul_zero]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem gInf_embInf (v : InfinitePlace E) (d : GL (Fin n) ℂ) : gInf v (embInf n v d) = d := by
  classical
  have e : embInf n v d = infP n (Pi.mulSingle v d) := rfl
  rw [e, gInf_infP, Pi.mulSingle_eq_same]

theorem continuous_embInf (v : InfinitePlace E) : Continuous (embInf (E := E) n v) := by
  classical
  have e : (embInf (E := E) n v : GL (Fin n) ℂ → GA E n) = fun d => infP n (Pi.mulSingle v d) := rfl
  rw [e]
  exact (continuous_infP n).comp (continuous_mulSingle (A := fun _ : InfinitePlace E => GL (Fin n) ℂ) v)

theorem slice {φ : GA E n → ℂ} (hφ : Continuous φ) (hc : HasCompactSupport φ) (v : InfinitePlace E) (g : GA E n)
    (hg : GeneralLinearGroup.map (cV v) g = 1) :
    Continuous (fun d => φ (embInf n v d * g)) ∧ HasCompactSupport (fun d => φ (embInf n v d * g)) := by
  refine ⟨hφ.comp ((continuous_embInf v).mul continuous_const), ?_⟩
  refine HasCompactSupport.intro (hc.isCompact.image (continuous_gInf n v)) fun d hd => ?_
  by_contra h
  apply hd
  refine ⟨embInf n v d * g, subset_tsupport _ h, ?_⟩
  have hg' : gInf v g = 1 := hg
  rw [map_mul, gInf_embInf, hg', mul_one]

omit [IsCMField E] in
theorem isTest_add [_root_.NumberField.IsTotallyComplex E] {φ ψ : GA E n → ℂ} (hφ : IsTest φ) (hψ : IsTest ψ) : IsTest fun x => φ x + ψ x := by
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  obtain ⟨U', hU', hUψ⟩ := hψ.level
  refine ⟨hφ.cont.add hψ.cont, hφ.supp.add hψ.supp, U ⊓ U', by rw [Subgroup.coe_inf]; exact hU.inter hU',
    fun u hu g => ?_⟩
  rw [Subgroup.mem_inf] at hu
  exact ⟨by rw [(hUφ u hu.1 g).1, (hUψ u hu.2 g).1], by rw [(hUφ u hu.1 g).2, (hUψ u hu.2 g).2]⟩

omit [IsCMField E] in
theorem isTest_smul [_root_.NumberField.IsTotallyComplex E] {φ : GA E n → ℂ} (c : ℂ) (hφ : IsTest φ) : IsTest fun x => c * φ x := by
  obtain ⟨U, hU, hUφ⟩ := hφ.level
  refine ⟨continuous_const.mul hφ.cont, hφ.supp.mono fun x hx => right_ne_zero_of_mul hx, U, hU,
    fun u hu g => ?_⟩
  exact ⟨by rw [(hUφ u hu g).1], by rw [(hUφ u hu g).2]⟩

theorem regSupp_add {φ ψ : GA E n → ℂ} (hφ : RegSupp φ) (hψ : RegSupp ψ) : RegSupp fun x => φ x + ψ x := by
  intro d x h
  dsimp only at h
  by_cases h0 : φ (twConj (thetaA E n) x (ratGL E n d)) = 0
  · exact hψ d x (by rwa [h0, zero_add] at h)
  · exact hφ d x h0

theorem regSupp_smul {φ : GA E n → ℂ} (c : ℂ) (hφ : RegSupp φ) : RegSupp fun x => c * φ x :=
  fun d x h => hφ d x (right_ne_zero_of_mul h)

theorem vCAt_add {φ ψ : GA E n → ℂ} (hφ : IsTest φ) (hψ : IsTest ψ) (v : InfinitePlace E) (h₁ : VCAt v φ)
    (h₂ : VCAt v ψ) : VCAt v fun x => φ x + ψ x := fun g hg =>
  veryCusp_add (slice hφ.cont hφ.supp v g hg).1 (slice hφ.cont hφ.supp v g hg).2
    (slice hψ.cont hψ.supp v g hg).1 (slice hψ.cont hψ.supp v g hg).2 (h₁ g hg) (h₂ g hg)

theorem vCAt_smul {φ : GA E n → ℂ} (c : ℂ) (v : InfinitePlace E) (h : VCAt v φ) : VCAt v fun x => c * φ x :=
  fun g hg => veryCusp_smul c (h g hg)

end PSumH

open PSumH

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem isTest2J_zero (r : ℝ) : IsTest2J (0 : GA E a × GA E b → ℂ) r :=
  ⟨⟨continuous_const, HasCompactSupport.zero, fun _ h => absurd rfl h,
    fun _ => ⟨isTest_zero, regSupp_zero, fun _ _ _ => veryCusp_zero⟩,
    fun _ => ⟨isTest_zero, regSupp_zero, fun _ _ _ => veryCusp_zero⟩⟩,
    ⊤, ⊤, isOpen_univ, isOpen_univ, fun _ _ _ _ _ => ⟨rfl, rfl⟩⟩

theorem isTest2J_smul {φ : GA E a × GA E b → ℂ} {r : ℝ} (c : ℂ) (h : IsTest2J φ r) : IsTest2J (c • φ) r := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU⟩ := h.level
  refine ⟨⟨h.cont.const_smul c, h.supp.mono fun x hx => right_ne_zero_of_mul hx,
    fun g hg => h.size g (right_ne_zero_of_mul hg), fun g₂ => ?_, fun g₁ => ?_⟩,
    U₁, U₂, hU₁, hU₂, fun u₁ h₁ u₂ h₂ g => ?_⟩
  · obtain ⟨t, s, w⟩ := h.test₁ g₂
    exact ⟨isTest_smul c t, regSupp_smul c s, fun v => vCAt_smul c v (w v)⟩
  · obtain ⟨t, s, w⟩ := h.test₂ g₁
    exact ⟨isTest_smul c t, regSupp_smul c s, fun v => vCAt_smul c v (w v)⟩
  · exact ⟨by simp only [Pi.smul_apply, (hU u₁ h₁ u₂ h₂ g).1], by simp only [Pi.smul_apply, (hU u₁ h₁ u₂ h₂ g).2]⟩

theorem isTest2J_add {φ ψ : GA E a × GA E b → ℂ} {r : ℝ} (h : IsTest2J φ r) (h' : IsTest2J ψ r) :
    IsTest2J (φ + ψ) r := by
  obtain ⟨U₁, U₂, hU₁, hU₂, hU⟩ := h.level
  obtain ⟨U₁', U₂', hU₁', hU₂', hU'⟩ := h'.level
  refine ⟨⟨h.cont.add h'.cont, h.supp.add h'.supp, fun g hg => ?_, fun g₂ => ?_, fun g₁ => ?_⟩,
    U₁ ⊓ U₁', U₂ ⊓ U₂', by rw [Subgroup.coe_inf]; exact hU₁.inter hU₁', by rw [Subgroup.coe_inf]; exact hU₂.inter hU₂',
    fun u₁ h₁ u₂ h₂ g => ?_⟩
  · by_cases h0 : φ g = 0
    · exact h'.size g (by simpa [h0] using hg)
    · exact h.size g h0
  · obtain ⟨t, s, w⟩ := h.test₁ g₂
    obtain ⟨t', s', w'⟩ := h'.test₁ g₂
    exact ⟨isTest_add t t', regSupp_add s s', fun v => vCAt_add t t' v (w v) (w' v)⟩
  · obtain ⟨t, s, w⟩ := h.test₂ g₁
    obtain ⟨t', s', w'⟩ := h'.test₂ g₁
    exact ⟨isTest_add t t', regSupp_add s s', fun v => vCAt_add t t' v (w v) (w' v)⟩
  · rw [Subgroup.mem_inf] at h₁ h₂
    exact ⟨by simp only [Pi.add_apply, (hU u₁ h₁.1 u₂ h₂.1 g).1, (hU' u₁ h₁.2 u₂ h₂.2 g).1],
      by simp only [Pi.add_apply, (hU u₁ h₁.1 u₂ h₂.1 g).2, (hU' u₁ h₁.2 u₂ h₂.2 g).2]⟩

theorem isTest2J_mono {φ : GA E a × GA E b → ℂ} {r r' : ℝ} (h : IsTest2J φ r) (hr : r ≤ r') : IsTest2J φ r' :=
  ⟨⟨h.cont, h.supp, fun g hg => ⟨(h.size g hg).1.trans hr, (h.size g hg).2.trans hr⟩, h.test₁, h.test₂⟩, h.level⟩

theorem isTest2J_sum {ι : Type*} (s : Finset ι) {φ : ι → GA E a × GA E b → ℂ} {r : ℝ}
    (h : ∀ i ∈ s, IsTest2J (φ i) r) : IsTest2J (∑ i ∈ s, φ i) r := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isTest2J_zero r
  | insert i s hi ih =>
    rw [Finset.sum_insert hi]
    exact isTest2J_add (h i (Finset.mem_insert_self i s)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

end PositivityTheory.Rg.BcB.CG

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.IntegrableTens
noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.BcB.E PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.Rg.BcB.SpectralAccumulation (Hf finH TypeH)
open scoped Classical

attribute [local instance] PositivityTheory.Rg.BcB.E.borelH

namespace PositivityTheory.Rg.BcB.CG

namespace prime_not_mem_section_base_place

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b n : ℕ}

def evV (v : InfinitePlace E) : Cinf E →+* ℂ := Pi.evalRingHom (fun _ : InfinitePlace E => ℂ) v

def uAt (v : InfinitePlace E) (k : Kinf E n) : Matrix.unitaryGroup (Fin n) ℂ :=
  ⟨(k : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v), by
    rw [Matrix.mem_unitaryGroup_iff]
    have h := Matrix.mem_unitaryGroup_iff.1 k.2
    have e : star ((k : Matrix (Fin n) (Fin n) (Cinf E)).map (evV v)) =
        (star (k : Matrix (Fin n) (Fin n) (Cinf E))).map (evV v) := by
      ext i j; rfl
    rw [e, ← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]⟩

def coef (M : Mods E n) (I L : IxA M) (k : Kinf E n) : ℂ := ∏ v, ent (M v) ((M v).ρ (uAt v k⁻¹)) (I v) (L v)

def Wsp (M : Mods E n) : Submodule ℂ (Kinf E n → ℂ) :=
  Submodule.span ℂ (Set.range fun p : IxA M × IxA M => coef M p.1 p.2)

theorem fd_Wsp (M : Mods E n) : FiniteDimensional ℂ (Wsp M) :=
  FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

theorem gInf_inv_val (v : InfinitePlace E) (k : Kinf E n) :
    (gInf v ((infGL E n (Unitary.toUnits k))⁻¹)).val = (uAt v k⁻¹).1 := by
  rw [← map_inv (infGL E n), ← map_inv (Unitary.toUnits (R := Matrix (Fin n) (Fin n) (Cinf E))) k]
  ext i j
  exact gInf_infGL n v _ i j

theorem entA_inf [MeasurableSpace (G n)] {μ : Measure (G n)} {M : Mods E n} {k : Kers M}
    {val : InfinitePlace E → Inf n → ℂ} {T : ℝ} (hk : IsMults μ k val T) (K : Kinf E n) (I J : IxA M) (y : GA E n) :
    entA k I J ((infGL E n (Unitary.toUnits K))⁻¹ * y) = ∑ L : IxA M, coef M I L K * entA k L J y := by
  have h1 : ∀ v, ent (M v) (k v (gInf v ((infGL E n (Unitary.toUnits K))⁻¹ * y)).val) (I v) (J v) =
      ∑ l, ent (M v) ((M v).ρ (uAt v K⁻¹)) (I v) l * ent (M v) (k v (gInf v y).val) l (J v) := by
    intro v
    have h2 := mult_equivariant_val (hk v) (gInf v y) (uAt v K⁻¹) 1
    simp only [OneMemClass.coe_one, map_one, mul_one] at h2
    have e : (gInf v ((infGL E n (Unitary.toUnits K))⁻¹ * y)).val = (uAt v K⁻¹).1 * (gInf v y).val := by
      rw [map_mul, Units.val_mul, gInf_inv_val]
    rw [e, h2, PMul.ent_mul]
  simp only [entA, coef]
  rw [Finset.prod_congr rfl fun v _ => h1 v, Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun L _ => ?_
  rw [Finset.prod_mul_distrib]

theorem gInf_fin_mul (v : InfinitePlace E) (u : GL (Fin n) (Af E)) (z : GA E n) :
    gInf v ((finGL E n u)⁻¹ * z) = gInf v z := by
  rw [map_mul, map_inv, gInf_finGL, inv_one, one_mul]

theorem entA_fin {M : Mods E n} (k : Kers M) (I J : IxA M) (u : GL (Fin n) (Af E)) (z : GA E n) :
    entA k I J ((finGL E n u)⁻¹ * z) = entA k I J z := by
  simp only [entA, gInf_fin_mul]

theorem hFin_fin (u₁ : GL (Fin a) (Af E)) (u₂ : GL (Fin b) (Af E)) (y : H E a b) :
    hFin ((finGL E a u₁, finGL E b u₂)⁻¹ * y) = (u₁⁻¹, u₂⁻¹) * hFin y := by
  show (gFin ((finGL E a u₁)⁻¹ * y.1), gFin ((finGL E b u₂)⁻¹ * y.2)) = (u₁⁻¹ * gFin y.1, u₂⁻¹ * gFin y.2)
  rw [map_mul, map_mul, map_inv, map_inv, gFin_finGL, gFin_finGL]

theorem hFin_inf (A : GL (Fin a) (Cinf E)) (B : GL (Fin b) (Cinf E)) (y : H E a b) :
    hFin ((infGL E a A, infGL E b B)⁻¹ * y) = hFin y := by
  show (gFin ((infGL E a A)⁻¹ * y.1), gFin ((infGL E b B)⁻¹ * y.2)) = (gFin y.1, gFin y.2)
  have h1 : gFin (infGL E a A) = 1 := pFin_infGL A
  have h2 : gFin (infGL E b B) = 1 := pFin_infGL B
  rw [map_mul, map_mul, map_inv, map_inv, h1, h2, inv_one, inv_one, one_mul, one_mul]

theorem f_mul (D : Dom E a b) {ι : Type} [Fintype ι] (Φ : Matrix ι ι (H E a b → ℂ)) (f : ι → H E a b → ℂ) {c : ℂ}
    (h : PositivityTheory.Rg.BcB.E.conv D.μ Φ f = c • f) (i : ι) (x g : H E a b) :
    c * f i (x * g) = ∑ j, ∫ y, Φ i j (g⁻¹ * y) * f j (x * y) ∂D.μ := by
  have : BorelSpace (H E a b) := ⟨rfl⟩
  have : D.μ.IsMulLeftInvariant := D.haar.1
  have h1 := congrFun (congrFun h i) (x * g)
  simp only [PositivityTheory.Rg.BcB.E.conv, Pi.smul_apply, smul_eq_mul] at h1
  rw [← h1]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h2 := integral_mul_left_eq_self (μ := D.μ) (fun y => Φ i j (g⁻¹ * y) * f j (x * y)) g
  simp only [← mul_assoc, inv_mul_cancel, one_mul] at h2
  exact h2

theorem cs_pi {ι X : Type} [Fintype ι] [TopologicalSpace X] [T2Space X] {g : ι → X → ℂ}
    (hg : ∀ v, HasCompactSupport (g v)) : HasCompactSupport fun y : ι → X => ∏ v, g v (y v) := by
  refine HasCompactSupport.intro (isCompact_univ_pi fun v => (hg v).isCompact) fun y hy => ?_
  simp only [Set.mem_pi, Set.mem_univ, true_implies, not_forall] at hy
  obtain ⟨v, hv⟩ := hy
  exact Finset.prod_eq_zero (Finset.mem_univ v) (image_eq_zero_of_notMem_tsupport hv)

theorem cs_prod3 {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] [T2Space X]
    [T2Space Y] [T2Space Z] {f : X → ℂ} {g : Y → ℂ} {h : Z → ℂ} (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hh : HasCompactSupport h) : HasCompactSupport fun z : X × (Y × Z) => f z.1 * g z.2.1 * h z.2.2 := by
  refine HasCompactSupport.intro (hf.isCompact.prod (hg.isCompact.prod hh.isCompact)) fun z hz => ?_
  simp only [Set.mem_prod, not_and_or] at hz
  rcases hz with h1 | h1 | h1
  · rw [image_eq_zero_of_notMem_tsupport h1, zero_mul, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero, zero_mul]
  · rw [image_eq_zero_of_notMem_tsupport h1, mul_zero]

theorem continuous_entA [MeasurableSpace (G n)] {μ : Measure (G n)} {M : Mods E n} {k : Kers M}
    {val : InfinitePlace E → Inf n → ℂ} {T : ℝ} (hk : IsMults μ k val T) (I J : IxA M) : Continuous (entA k I J) := by
  have e : entA k I J = fun g => ∏ v, ent (M v) (k v (gInf v g).val) (I v) (J v) := rfl
  rw [e]
  exact continuous_finsetProd _ fun v _ => (mult_ent (hk v) (I v) (J v)).1.comp (continuous_gInf n v)

theorem tens_cs [MeasurableSpace (G a)] [MeasurableSpace (G b)] {μa : Measure (G a)} {μb : Measure (G b)}
    {Ma : Mods E a} {Mb : Mods E b} {κ : Type} {ka : Kers Ma} {kb : Kers Mb} {va : InfinitePlace E → Inf a → ℂ}
    {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)} (ha : IsMults μa ka va T)
    (hb : IsMults μb kb vb T) (hψ : IsFinM ψ) (i j : Io Ma Mb κ) :
    Continuous (tens ka kb ψ i j) ∧ HasCompactSupport (tens ka kb ψ i j) := by
  have hh : Continuous (hFin : H E a b → Hf E a b) :=
    ((continuous_gFin a).comp continuous_fst).prodMk ((continuous_gFin b).comp continuous_snd)
  have hcont : Continuous (tens ka kb ψ i j) :=
    (((continuous_entA ha _ _).comp continuous_fst).mul ((continuous_entA hb _ _).comp continuous_snd)).mul
      ((hψ i.2 j.2).1.comp hh)
  set_option synthInstance.maxHeartbeats 200000 in
  have hQ := cs_prod3 (cs_pi fun v => (mult_ent (ha v) (i.1.1 v) (j.1.1 v)).2)
    (cs_pi fun v => (mult_ent (hb v) (i.1.2 v) (j.1.2 v)).2) (hψ i.2 j.2).2
  have hpt : ∀ z, tens ka kb ψ i j (splitH a b z) =
      (∏ v, ent (Ma v) (ka v (z.1 v).val) (i.1.1 v) (j.1.1 v)) *
        (∏ v, ent (Mb v) (kb v (z.2.1 v).val) (i.1.2 v) (j.1.2 v)) * ψ i.2 j.2 z.2.2 := fun z => by
    simp only [tens, entA, gInf_splitH₁, gInf_splitH₂, hFin_splitH]
  have e : tens ka kb ψ i j = (fun z : (InfinitePlace E → G a) × ((InfinitePlace E → G b) × Hf E a b) =>
      (∏ v, ent (Ma v) (ka v (z.1 v).val) (i.1.1 v) (j.1.1 v)) *
        (∏ v, ent (Mb v) (kb v (z.2.1 v).val) (i.1.2 v) (j.1.2 v)) * ψ i.2 j.2 z.2.2) ∘
      (splitH a b).toHomeomorph.symm := by
    funext g
    obtain ⟨z, rfl⟩ := (splitH a b).surjective g
    rw [Function.comp_apply, show (splitH a b).toHomeomorph.symm (splitH a b z) = z from
      (splitH a b).toHomeomorph.symm_apply_apply z]
    exact hpt z
  refine ⟨hcont, ?_⟩
  rw [e]
  exact hQ.comp_homeomorph _

theorem integrable_tens (D : Dom E a b) [MeasurableSpace (G a)] [MeasurableSpace (G b)] {μa : Measure (G a)}
    {μb : Measure (G b)} {Ma : Mods E a} {Mb : Mods E b} {κ : Type} {ka : Kers Ma} {kb : Kers Mb}
    {va : InfinitePlace E → Inf a → ℂ} {vb : InfinitePlace E → Inf b → ℂ} {T : ℝ} {ψ : Matrix κ κ (Hf E a b → ℂ)}
    (ha : IsMults μa ka va T) (hb : IsMults μb kb vb T) (hψ : IsFinM ψ) {F : H E a b → ℂ} (hF : Continuous F)
    (i j : Io Ma Mb κ) (x : H E a b) : Integrable (fun y => tens ka kb ψ i j y * F (x * y)) D.μ := by
  have : BorelSpace (H E a b) := ⟨rfl⟩
  have : IsLocallyFiniteMeasure D.μ := D.haar.2.2.2
  have : IsFiniteMeasureOnCompacts D.μ := ⟨fun K hK => hK.measure_lt_top_of_nhdsWithin fun x _ =>
    (D.μ.finiteAt_nhds x).filter_mono nhdsWithin_le_nhds⟩
  obtain ⟨h1, h2⟩ := tens_cs ha hb hψ i j
  exact (h1.mul (hF.comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
    (h2.mul_right (f' := fun y => F (x * y)))

end prime_not_mem_section_base_place


open prime_not_mem_section_base_place in
theorem typeOf : TypeOf := by
  intro E _ _ _ a b Ma Mb
  refine ⟨Wsp Ma, Wsp Mb, fd_Wsp Ma, fd_Wsp Mb, ?_⟩
  intro D _ _ μa μb κ _ ka kb va vb T ψ K₁ K₂ f hka hkb hψ hlev hrep i
  obtain ⟨hfc, c, hc, hconv⟩ := hrep
  have hint : ∀ i j x, Integrable (fun y => tens ka kb ψ i j y * f j (x * y)) D.μ := fun i j x =>
    integrable_tens D hka hkb hψ (hfc j) i j x
  have hR : ∀ (L : Io Ma Mb κ) x, c * f L x = ∑ j, ∫ y, tens ka kb ψ L j y * f j (x * y) ∂D.μ := fun L x => by
    have h0 := f_mul D _ f hconv L x 1
    simpa only [mul_one, inv_one, one_mul] using h0
  refine ⟨fun u₁ hu₁ u₂ hu₂ x => ?_, fun x => ?_⟩
  · have h1 := f_mul D _ f hconv i x (finGL E a u₁, finGL E b u₂)
    have hΦ : ∀ j y, tens ka kb ψ i j ((finGL E a u₁, finGL E b u₂)⁻¹ * y) = tens ka kb ψ i j y := by
      intro j y
      show entA ka i.1.1 j.1.1 ((finGL E a u₁)⁻¹ * y.1) * entA kb i.1.2 j.1.2 ((finGL E b u₂)⁻¹ * y.2) *
          ψ i.2 j.2 (hFin ((finGL E a u₁, finGL E b u₂)⁻¹ * y)) =
        entA ka i.1.1 j.1.1 y.1 * entA kb i.1.2 j.1.2 y.2 * ψ i.2 j.2 (hFin y)
      rw [entA_fin, entA_fin, hFin_fin, hlev _ _ _ (K₁.inv_mem hu₁) _ (K₂.inv_mem hu₂)]
    simp only [hΦ] at h1
    exact mul_left_cancel₀ hc (h1.trans (hR i x).symm)
  · have hexp : ∀ k : Kinf E a × Kinf E b,
        f i (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))) =
          ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb, f ((L₁, L₂), i.2) x * (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) := by
      intro k
      apply mul_left_cancel₀ hc
      have hΦ : ∀ j y, tens ka kb ψ i j ((infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))⁻¹ * y) =
          ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb,
            (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) * tens ka kb ψ ((L₁, L₂), i.2) j y := by
        intro j y
        show entA ka i.1.1 j.1.1 ((infGL E a (Unitary.toUnits k.1))⁻¹ * y.1) *
            entA kb i.1.2 j.1.2 ((infGL E b (Unitary.toUnits k.2))⁻¹ * y.2) *
            ψ i.2 j.2 (hFin ((infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))⁻¹ * y)) = _
        rw [entA_inf hka, entA_inf hkb, hFin_inf, Finset.sum_mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun L₁ _ => ?_
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun L₂ _ => ?_
        simp only [tens]
        ring
      rw [f_mul D _ f hconv i x]
      calc ∑ j, ∫ y, tens ka kb ψ i j
              ((infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2))⁻¹ * y) * f j (x * y) ∂D.μ
          = ∑ j, ∫ y, ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb, (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) *
              (tens ka kb ψ ((L₁, L₂), i.2) j y * f j (x * y)) ∂D.μ := by
            refine Finset.sum_congr rfl fun j _ => integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
            simp only [hΦ, Finset.sum_mul, mul_assoc]
        _ = ∑ j, ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb, (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) *
              ∫ y, tens ka kb ψ ((L₁, L₂), i.2) j y * f j (x * y) ∂D.μ := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [integral_finsetSum _ fun L₁ _ => integrable_finsetSum _ fun L₂ _ => (hint _ j x).const_mul _]
            refine Finset.sum_congr rfl fun L₁ _ => ?_
            rw [integral_finsetSum _ fun L₂ _ => (hint _ j x).const_mul _]
            exact Finset.sum_congr rfl fun L₂ _ => integral_const_mul _ _
        _ = ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb, (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) *
              (c * f ((L₁, L₂), i.2) x) := by
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun L₁ _ => ?_
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun L₂ _ => ?_
            rw [hR, Finset.mul_sum]
        _ = c * ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb, f ((L₁, L₂), i.2) x * (coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2) := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun L₁ _ => ?_
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun L₂ _ => ?_
            ring
    have e : (fun k : Kinf E a × Kinf E b =>
        f i (x * (infGL E a (Unitary.toUnits k.1), infGL E b (Unitary.toUnits k.2)))) =
          ∑ L₁ : IxA Ma, ∑ L₂ : IxA Mb,
            f ((L₁, L₂), i.2) x • fun k : Kinf E a × Kinf E b => coef Ma i.1.1 L₁ k.1 * coef Mb i.1.2 L₂ k.2 := by
      funext k
      rw [hexp k]
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e]
    exact Submodule.sum_mem _ fun L₁ _ => Submodule.sum_mem _ fun L₂ _ => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨_, Submodule.subset_span ⟨(i.1.1, L₁), rfl⟩, _,
        Submodule.subset_span ⟨(i.1.2, L₂), rfl⟩, rfl⟩)

end PositivityTheory.Rg.BcB.CG

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PInfEx
noncomputable section

open Polynomial Finset NumberField GlobalTheory.CuspRep
open PositivityTheory.RgBcC.Bridge PositivityTheory.Rg.BcB.CG.InfiniteConvergence

namespace PositivityTheory.Rg.BcB.CG

namespace HeckeFubiniEvaluationDefect

theorem eval_sS (t : ℕ → ℂ) (m N : ℕ) : (sS t m N).eval (m : ℂ) = (-1) ^ N * t N := by
  rw [sS, sum_range_succ, eval_add, eval_finsetSum, sum_eq_zero]
  · simp
  · intro k hk
    have := mem_range.mp hk
    simp only [eval_mul, eval_C, eval_pow, eval_sub, eval_X, sub_self]
    rw [zero_pow (by omega), mul_zero]

theorem eq_of_defect (m : ℕ) (t t' : ℕ → ℂ) (Q : ℂ[X]) (hQ : Q.natDegree = m + 1)
    (h : ∀ N, (defect t m N Q).natDegree ≤ m) (h' : ∀ N, (defect t' m N Q).natDegree ≤ m) (k : ℕ) : t k = t' k := by
  have hQ0 : Q ≠ 0 := by intro e; rw [e, natDegree_zero] at hQ; omega
  have hS : sS t m k = sS t' m k := by
    have e : defect t m k Q - defect t' m k Q = Q * (sS t' m k - sS t m k) := by
      simp only [defect_eq]; ring
    by_contra hne
    have hD : sS t' m k - sS t m k ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
    have h1 : (Q * (sS t' m k - sS t m k)).natDegree ≤ m := by
      rw [← e]; exact (natDegree_sub_le _ _).trans (max_le (h k) (h' k))
    rw [natDegree_mul hQ0 hD, hQ] at h1
    omega
  have e := congrArg (fun p => p.eval (m : ℂ)) hS
  simp only [eval_sS] at e
  have hu : ((-1 : ℂ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  exact mul_left_cancel₀ hu e

theorem exists_enum (s : Multiset ℂ) : ∀ n, Multiset.card s = n → ∃ r : Fin n → ℂ, Multiset.map r univ.val = s := by
  induction s using Multiset.induction_on with
  | empty =>
    intro n hn
    simp only [Multiset.card_zero] at hn
    subst hn
    exact ⟨Fin.elim0, by simp⟩
  | cons a s ih =>
    intro n hn
    rw [Multiset.card_cons] at hn
    subst hn
    obtain ⟨r, hr⟩ := ih _ rfl
    refine ⟨Fin.cons a r, ?_⟩
    conv_rhs => rw [← hr]
    simp [Fin.univ_succ, Multiset.map_map, Function.comp_def]

theorem exists_gelf (V : Type) [AddCommGroup V] [Module ℂ V] (m : ℕ) (M : Fin (m + 1) → Fin (m + 1) → Module.End ℂ V)
    (hM : Formalism.REAL.GlRel M) (v : V) (hv : v ≠ 0) (t : ℕ → ℂ) (ht : ∀ k, Formalism.REAL.etr M k v = t k • v) :
    ∃ χ : Fin (m + 1) → ℂ, ∀ k, GlobalTheory.Dec.gelfVal χ k = t k := by
  obtain ⟨f₀, hf₀⟩ : ∃ f : Module.Dual ℂ V, f v ≠ 0 := by
    by_contra hc
    push Not at hc
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).mp hc)
  set f : Module.Dual ℂ V := (f₀ v)⁻¹ • f₀ with hfd
  have hf : f v = 1 := by
    rw [hfd, LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hf₀]
  obtain ⟨c, hc1, hc⟩ := GlobalTheory.T.exists_monic_poly_eq_qdet (Module.End ℂ V) (m + 1) M
  set Q := GlobalTheory.CapelliNewton.polyOf (m + 1) c f v with hQd
  have hQ : ∀ u : ℂ, Q.eval u = f (Formalism.REAL.qdet M u v) := fun u => by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_eval, hc]
  have hQc : Q.coeff (m + 1) = 1 := by
    rw [hQd, GlobalTheory.CapelliNewton.polyOf_coeff, hc1]
    exact hf
  have hQn : Q.natDegree = m + 1 :=
    le_antisymm (GlobalTheory.CapelliNewton.polyOf_natDegree _ _ _ _)
      (le_natDegree_of_ne_zero (by rw [hQc]; exact one_ne_zero))
  have hQm : Q.Monic := by
    rw [Monic, leadingCoeff, hQn, hQc]
  have hcard : Multiset.card Q.roots = m + 1 := by
    rw [IsAlgClosed.card_roots_eq_natDegree, hQn]
  have hprod : (Q.roots.map fun a => X - Polynomial.C a).prod = Q :=
    prod_multiset_X_sub_C_of_monic_of_roots_card_eq hQm (by rw [hcard, hQn])
  obtain ⟨r, hr⟩ := exists_enum Q.roots (m + 1) hcard
  refine ⟨fun s => (m : ℂ) / 2 - r s, fun k => ?_⟩
  have hcq : (∏ s, (X + Polynomial.C ((m : ℂ) / 2 - r s - (m : ℂ) / 2))) = Q := by
    conv_rhs => rw [← hprod, ← hr]
    rw [Multiset.map_map, Finset.prod_eq_multiset_prod]
    congr 1
    refine Multiset.map_congr rfl fun s _ => ?_
    simp only [Function.comp_apply, map_sub]
    ring
  have h1 : ∀ N, (defect (GlobalTheory.Dec.gelfVal fun s => (m : ℂ) / 2 - r s) m N Q).natDegree ≤ m := by
    intro N
    have := natDegree_defect_gelf m (fun s => (m : ℂ) / 2 - r s) N
    rwa [hcq] at this
  have h2 : ∀ N, (defect t m N Q).natDegree ≤ m := fun N =>
    natDegree_defect_op V m M hM v t ht f Q hQ N
  exact eq_of_defect m _ t Q hQn h1 h2 k

theorem one_mem_GLs' {a : ℕ} : (1 : Matrix (Fin a) (Fin a) ℂ) ∈ PositivityTheory.RgBcC.GLs a := by
  simp [PositivityTheory.RgBcC.GLs]

end HeckeFubiniEvaluationDefect

open HeckeFubiniEvaluationDefect in
theorem infEx : InfEx := by
  intro E _ _ _ n S v t ⟨φ, hφS, hφ0⟩ h
  have hs : ∀ s k, Formalism.REAL.etr (eopW v s) k φ = t s k • φ := by
    intro s k
    apply Subtype.ext
    funext g
    have h1 := h φ hφS g s k 1 one_mem_GLs'
    rw [gel_along v g s k φ one_mem_GLs', along_one, along_one] at h1
    rw [Submodule.coe_smul, Pi.smul_apply]
    exact h1
  rcases n with _ | m
  · refine ⟨fun _ => Fin.elim0, fun s k => ?_⟩
    have ht0 : t s k = 0 := by
      have e : t s k • φ = 0 := by rw [← hs s k]; simp [Formalism.REAL.etr]
      exact (smul_eq_zero.mp e).resolve_right hφ0
    rw [ht0]
    simp [GlobalTheory.Dec.gelfVal]
  · have hgl : ∀ s, Formalism.REAL.GlRel (eopW (E := E) (a := m + 1) v s) := by
      intro s
      unfold eopW
      split <;> exact glRel_Eop _
    choose χ hχ using fun s => exists_gelf (Sm E (m + 1)) m (eopW v s) (hgl s) φ hφ0 (t s) (hs s)
    exact ⟨χ, fun s k => hχ s k⟩

end PositivityTheory.Rg.BcB.CG

end
end
