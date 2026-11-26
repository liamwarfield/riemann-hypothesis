module

public import Development.WeilBound.ThetaLifts.LocalTheory.UnramifiedDeterminedBySpherical
public import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.AtSingle
public import Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.KilEmpty

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LocalTheory.DixmierCommutants.LocalMultiplicityOneIrreducibleGL
noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open GlobalTheory.WeilM Filter Topology ValuativeRel Matrix PositivityTheory.KCo GlobalTheory.SplitFlip

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [T2Space k]
  {n d d₁ : ℕ} (e : Fin d₁ ⊕ Bool ≃ Fin d) {W : Type} [AddCommGroup W] [Module ℂ W]

def tn (ψ : Matrix (Fin n) (Fin d₁) k → ℂ) (f f' : (Fin n → k) → ℂ) : Matrix (Fin n) (Fin d) k → ℂ :=
  fun Y => ψ (mid e Y) * f (cl e false Y) * f' (cl e true Y)

def tn₁ (f f' : (Fin n → k) → ℂ) : (Matrix (Fin n) (Fin d₁) k → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun ψ := tn e ψ f f'
  map_add' _ _ := funext fun _ => by simp [tn, add_mul]
  map_smul' _ _ := funext fun _ => by simp [tn, mul_assoc]

def tn₃ (ψ : Matrix (Fin n) (Fin d₁) k → ℂ) (f : (Fin n → k) → ℂ) : ((Fin n → k) → ℂ) →ₗ[ℂ] (Matrix (Fin n) (Fin d) k → ℂ) where
  toFun f' := tn e ψ f f'
  map_add' _ _ := funext fun _ => by simp [tn, mul_add]
  map_smul' _ _ := funext fun _ => by simp [tn, mul_left_comm]

def one (n : ℕ) : (Fin n → k) → ℂ := cs (bx (Fin n) (1 : k)) 0

def blk (g : Matrix (Fin d₁) (Fin d₁) k) : Matrix (Fin d) (Fin d) k := reindex e e (fromBlocks g 0 0 1)

variable {e} {ν : kˣ →* ℂˣ} {L : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W}

theorem one_sb : (one n : (Fin n → k) → ℂ) ∈ SB (Fin n → k) := by
  unfold one
  exact cs_mem (V := Fin n → k) (H := bx (Fin n) (1 : k)) (bx_open (one_ne_zero' k)) (bx_compact (1 : k)) 0

theorem cm : Continuous (mid e : Matrix (Fin n) (Fin d) k → _) := continuous_id.matrix_submatrix _ _

theorem cc (t : Bool) : Continuous (cl e t : Matrix (Fin n) (Fin d) k → _) := continuous_pi fun i => continuous_id.matrix_elem i _

theorem tn_mem {ψ : Matrix (Fin n) (Fin d₁) k → ℂ} {f f' : (Fin n → k) → ℂ} (h : ψ ∈ SB _) (hf : f ∈ SB _) (hf' : f' ∈ SB _) :
    tn e ψ f f' ∈ SB _ := by
  refine ⟨((h.1.comp_continuous cm).mul (hf.1.comp_continuous (cc false))).mul (hf'.1.comp_continuous (cc true)), ?_⟩
  let a : Matrix (Fin n) (Fin d₁) k × (Fin n → k) × (Fin n → k) → Matrix (Fin n) (Fin d) k := fun x =>
    Matrix.of fun i j => Sum.elim (x.1 i) (fun t => cond t (x.2.2 i) (x.2.1 i)) (e.symm j)
  have ca : Continuous a := continuous_matrix fun i j => by
    simp only [a, Matrix.of_apply]
    rcases e.symm j with s | _ | _
    · exact continuous_fst.matrix_elem i s
    · exact (continuous_apply i).comp (continuous_fst.comp continuous_snd)
    · exact (continuous_apply i).comp (continuous_snd.comp continuous_snd)
  refine HasCompactSupport.intro ((h.2.isCompact.prod (hf.2.isCompact.prod hf'.2.isCompact)).image ca) fun Y hY => ?_
  by_contra h0
  refine hY ⟨(mid e Y, cl e false Y, cl e true Y), ⟨subset_tsupport _ (left_ne_zero_of_mul (left_ne_zero_of_mul h0)),
    subset_tsupport _ (right_ne_zero_of_mul (left_ne_zero_of_mul h0)), subset_tsupport _ (right_ne_zero_of_mul h0)⟩, ?_⟩
  ext i j
  obtain ⟨j, rfl⟩ := e.surjective j
  rcases j with s | _ | _ <;> simp [a, mid, cl]

theorem sum_e (a : Fin d → k) : ∑ j, a j = ∑ s, a (e (.inl s)) + (a (e (.inr true)) + a (e (.inr false))) := by
  rw [← e.sum_comp, Fintype.sum_sum_type, Fintype.sum_bool]

theorem trans_inv (hL : Inv e ν L) {ψ : Matrix (Fin n) (Fin d₁) k → ℂ} (h : Full ψ) {f f' : (Fin n → k) → ℂ} (hf : f ∈ SB _)
    (hf' : f' ∈ SB _) (v : Fin n → k) : L (tn e ψ f fun x => f' (x + v)) = L (tn e ψ f f') := by
  obtain ⟨U, hU, hi⟩ := exists_invar hf'
  have : Kil (LinearMap.ker (L ∘ₗ (tn₁ e f (fun x => f' (x + v)) - tn₁ e f f'))) {Z | RI Z} := by
    refine kil_loc hV_mat fun Z₀ ⟨R, hR⟩ => ⟨{Z | v - Z *ᵥ (R *ᵥ v) ∈ U}, ?_, fun φ hφ hs => ?_⟩
    · exact (continuous_const.sub (continuous_id.matrix_mulVec continuous_const)).continuousAt.preimage_mem_nhds (by
        simpa [mulVec_mulVec, hR] using hU)
    let w : Fin d → k := fun j => Sum.elim (R *ᵥ v) 0 (e.symm j)
    let g : Matrix (Fin d) (Fin d) k := 1 + vecMulVec w (Pi.single (e (.inr true)) 1)
    have hg : InP e g := by
      refine ⟨fun r hr => ?_, ?_, ?_, fun s s' => ?_, fun s => ?_⟩ <;> simp [g, w, vecMulVec_apply, Matrix.one_apply, *]
    have e1 := (hL.right g hg _ (tn_mem (e := e) hφ hf hf')).2
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply, map_sub, sub_eq_zero]
    refine Eq.trans (congrArg L (funext fun Y => ?_)) e1
    have yw : Y *ᵥ w = mid e Y *ᵥ (R *ᵥ v) := funext fun i => by
      simp only [mulVec, dotProduct]; rw [sum_e (e := e)]; simp [w, mid, mulVec, dotProduct]
    have yg : Y * g = Y + vecMulVec (mid e Y *ᵥ (R *ᵥ v)) (Pi.single (e (.inr true)) 1) := by
      rw [Matrix.mul_add, Matrix.mul_one, mul_vecMulVec, yw]
    have m1 : mid e (Y * g) = mid e Y := by ext i s; rw [yg]; simp [mid, vecMulVec_apply]
    have m2 : cl e false (Y * g) = cl e false Y := by ext i; rw [yg]; simp [cl, vecMulVec_apply]
    have m3 : cl e true (Y * g) = cl e true Y + mid e Y *ᵥ (R *ᵥ v) := by ext i; rw [yg]; simp [cl, vecMulVec_apply]
    change φ _ * f _ * f' _ = φ _ * f _ * f' _
    rw [m1, m2, m3]
    by_cases h0 : φ (mid e Y) = 0
    · simp [h0]
    · rw [← hi _ (hs _ h0) (cl e true Y + mid e Y *ᵥ (R *ᵥ v))]
      congr 2
      abel
  have := this ψ h.1 fun Z hZ => ri_iff.2 (by by_contra h'; exact hZ (h.2 Z h'))
  rwa [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.sub_apply, map_sub, sub_eq_zero] at this

theorem comp_mem {f : (Fin n → k) → ℂ} (hf : f ∈ SB _) (g : GL (Fin n) k) : (fun x => f (g.val *ᵥ x)) ∈ SB (Fin n → k) := by
  let H : (Fin n → k) ≃ₜ (Fin n → k) :=
    { toFun := fun x => g.val *ᵥ x, invFun := fun x => (g⁻¹).val *ᵥ x, left_inv := fun x => by simp [mulVec_mulVec],
      right_inv := fun x => by simp [mulVec_mulVec], continuous_toFun := continuous_const.matrix_mulVec continuous_id,
      continuous_invFun := continuous_const.matrix_mulVec continuous_id }
  exact ⟨hf.1.comp_continuous H.continuous, hf.2.comp_homeomorph H⟩

theorem mod_inv (hL : Inv e ν L) {ψ : Matrix (Fin n) (Fin d₁) k → ℂ} (h : Full ψ) {f f' : (Fin n → k) → ℂ} (hf : f ∈ SB _)
    (hf' : f' ∈ SB _) (g : GL (Fin n) k) :
    ((GlobalTheory.SplitWeil.nabs k (GeneralLinearGroup.det g) : ℝ) : ℂ) • L (tn e ψ f fun x => f' (g.val *ᵥ x)) = L (tn e ψ f f') := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro m
  rw [map_sub, map_smul, sub_eq_zero]
  exact invariant_comp_mulVec (m ∘ₗ L ∘ₗ tn₃ e ψ f) (fun φ hφ a => congrArg m (trans_inv hL h hf hφ a)) g hf' (comp_mem hf' g)

theorem swap_mid (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) {ψ : Matrix (Fin n) (Fin d₁) k → ℂ}
    (h : ψ ∈ SB _) {f f₁ f' : (Fin n → k) → ℂ} (hf : f ∈ SB _) (hf₁ : f₁ ∈ SB _) (hf' : f' ∈ SB _) (c : ℂ) (h0 : f 0 = c * f₁ 0) :
    L (tn e ψ f f') = c • L (tn e ψ f₁ f') := by
  have := kil_one hL hl hν (tn e ψ f f' - c • tn e ψ f₁ f') (sub_mem (tn_mem h hf hf') ((SB _).smul_mem _ (tn_mem h hf₁ hf')))
    fun Y hY h1 => hY (by simp only [Pi.sub_apply, Pi.smul_apply, tn, h1, h0, smul_eq_mul]; ring)
  rwa [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at this

theorem one_zero : (one n : (Fin n → k) → ℂ) 0 = 1 := Set.indicator_of_mem (by simp [zero_mem]) _

theorem red (hL : Inv e ν L) (hu : USm ν) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1)
    (h : ∀ ψ, Full ψ → L (tn e ψ (one n) (one n)) = 0) : ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L Φ = 0 := by
  have h2 : Kil (LinearMap.ker L) {Y | RI (mid e Y)} := by
    refine kil_loc hV_mat fun X₀ ⟨R, hR⟩ => ?_
    obtain ⟨r, r0, hr⟩ := mb_small (nhds_sub (det_nhds hR))
    refine ⟨{Y | mid e Y - mid e X₀ ∈ mb _ _ r}, ((mb_open r0).preimage (cm.sub continuous_const)).mem_nhds (by simp [zero_mem]),
      fun Φ hΦ hs => ?_⟩
    obtain ⟨U, hU, hi⟩ := exists_invar hΦ
    obtain ⟨c, c0, hc⟩ := mb_small (inter_mem hU (cm (e := e).continuousAt.preimage_mem_nhds ((mb_open r0).mem_nhds (zero_mem _))))
    refine mem_of_cs (mb_open c0) hΦ (fun S hS => hi S (hc hS).1) _ fun y hy => ?_
    have e1 : cs (mb _ _ c) y = tn e (cs (mb _ _ c ⊓ mb _ _ r) (mid e y)) (cs (bx _ c) (cl e false y)) (cs (bx _ c) (cl e true y)) := by
      funext Y
      classical
      have : Y - y ∈ mb _ _ c ↔ (mid e Y - mid e y ∈ mb _ _ c ⊓ mb _ _ r ∧ cl e false Y - cl e false y ∈ bx _ c) ∧
          cl e true Y - cl e true y ∈ bx _ c := by
        refine ⟨fun h => ⟨⟨⟨fun i s => h i _, (hc h).2⟩, fun i => h i _⟩, fun i => h i _⟩, fun h i j => ?_⟩
        obtain ⟨j, rfl⟩ := e.surjective j
        rcases j with s | _ | _
        exacts [h.1.1.1 i s, h.1.2 i, h.2 i]
      simp only [tn, cs, Set.indicator_apply, Set.mem_setOf_eq, this, Pi.one_apply]
      split_ifs <;> simp_all
    have o : IsOpen ((mb (Fin n) (Fin d₁) c ⊓ mb _ _ r : AddSubgroup _) : Set (Matrix (Fin n) (Fin d₁) k)) := (mb_open c0).inter (mb_open r0)
    have fu : Full (cs (mb (Fin n) (Fin d₁) c ⊓ mb _ _ r) (mid e y)) := by
      refine ⟨cs_mem o ((mb_compact c).inter_right (AddSubgroup.isClosed_of_isOpen _ (mb_open r0))) _, fun Z hZ => ?_⟩
      by_contra h'
      have := hr (add_mem (cs_ne h').2 (hs y hy))
      exact hZ (ri_iff.1 (ri_of_det (R := R) (by simpa using this)))
    have s1 := fun x : Fin n → k => cs_mem (bx_open (S := Fin n) c0) (bx_compact c) x
    rw [LinearMap.mem_ker, e1, swap_mid hL hl hν fu.1 (s1 _) one_sb (s1 _) (cs (bx _ c) (cl e false y) 0) (by rw [one_zero, mul_one])]
    let g : GL (Fin n) k := GeneralLinearGroup.scalar _ (Units.mk0 c c0)⁻¹
    have e2 := mod_inv hL fu one_sb one_sb g
    have e3 : cs (bx _ c) (cl e true y) = fun x => (fun x => one n (g.val *ᵥ x)) (x + -cl e true y) := by
      funext x
      classical
      have : g.val *ᵥ (x + -cl e true y) - 0 ∈ bx (Fin n) (1 : k) ↔ x - cl e true y ∈ bx _ c := by
        refine forall_congr' fun i => ?_
        have : (g.val *ᵥ (x + -cl e true y) - 0) i = c⁻¹ * (x - cl e true y) i := by
          have gv : g.val = diagonal fun _ => c⁻¹ := by
            change Matrix.scalar _ ((Units.mk0 c c0)⁻¹).val = _
            simp [Matrix.scalar_apply]
          rw [gv]
          rw [sub_zero, mulVec_diagonal, sub_eq_add_neg]
        rw [this, map_mul, map_inv₀, map_one, inv_mul_le_iff₀ (zero_lt_iff.2 (by simpa using c0)), mul_one]
      simp only [one, cs, Set.indicator_apply, Set.mem_setOf_eq, this, Pi.one_apply]
    rw [h _ fu, smul_eq_zero] at e2
    rw [e3, trans_inv hL fu one_sb (comp_mem one_sb g), e2.resolve_left (by simpa [apow] using apow_ne_zero (GeneralLinearGroup.det g) 1), smul_zero]
  intro Φ hΦ
  obtain ⟨Φ₀, h0, ha⟩ := surjectivity_statement k n d ν 1 hu (fun h => hν (by simp [h])) Φ hΦ
  have h3 : aug n d ν 1 ≤ LinearMap.ker L := Submodule.span_le.2 (by
    rintro _ ⟨g, Ψ, hΨ, rfl⟩
    exact LinearMap.mem_ker.2 (by rw [map_sub, hL.left g Ψ hΨ, sub_self]))
  have h4 := kil_full hL hl hν h2 Φ₀ h0.1 fun Y hY => ri_iff.2 (by by_contra h'; exact hY (h0.2 Y h'))
  have := add_mem (h3 ha) h4
  rwa [sub_add_cancel] at this

theorem full_omB {m : ℕ} {ψ : Matrix (Fin n) (Fin m) k → ℂ} (h : Full ψ) (g : GL (Fin n) k) (g' : GL (Fin m) k) :
    Full fun Z : Matrix (Fin n) (Fin m) k => ψ (g.val * Z * g'.val) := by
  let H : Matrix (Fin n) (Fin m) k ≃ₜ Matrix (Fin n) (Fin m) k :=
    { toFun := fun x => g.val * x * g'.val, invFun := fun x => (g⁻¹).val * x * (g'⁻¹).val,
      left_inv := fun x => by simp [Matrix.mul_assoc], right_inv := fun x => by simp [Matrix.mul_assoc],
      continuous_toFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const,
      continuous_invFun := (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const }
  refine ⟨⟨h.1.1.comp_continuous H.continuous, h.1.2.comp_homeomorph H⟩, fun Z hZ => h.2 _ fun h' => hZ ?_⟩
  obtain ⟨R, hR⟩ := ri_iff.2 h'
  refine ri_iff.1 ⟨g'.val * R * g.val, ?_⟩
  have := congrArg (fun A => (g⁻¹).val * A * g.val) hR
  simpa [Matrix.mul_assoc] using this

theorem aug_ker (hL : Inv e ν L) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) :
    augF n d₁ ν 1 ≤ LinearMap.ker (L ∘ₗ tn₁ e (one n) (one n)) := Submodule.span_le.2 (by
  rintro _ ⟨g, ψ, h, rfl⟩
  have hd : (d : ℂ) = d₁ + 2 := by
    have := Fintype.card_congr e
    simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_bool] at this
    exact_mod_cast this.symm
  let g' := invT g⁻¹
  have hg : g'.val = g.valᵀ := by simp [g', invT]
  have dg : GeneralLinearGroup.det g' = gdet g := Units.ext (by simp [hg, gdet])
  have fu := full_omB h g' 1
  have e1 := hL.left g _ (tn_mem (e := e) h.1 one_sb one_sb)
  have e2 : omB ν 1 g 1 (tn e ψ (one n) (one n)) = ((ν (gdet g) : ℂ) * apow (gdet g) ((d : ℂ) / 2)) •
      tn e (fun Z : Matrix (Fin n) (Fin d₁) k => ψ (g'.val * Z * (1 : GL (Fin d₁) k).val)) (fun x => one n (g'.val *ᵥ x)) fun x => one n (g'.val *ᵥ x) := by
    funext Y
    have m1 : mid e (g.valᵀ * Y) = g.valᵀ * mid e Y := rfl
    have m2 : ∀ t, cl e t (g.valᵀ * Y) = g.valᵀ *ᵥ cl e t Y := fun t => rfl
    simp [omB, tn, hg, m1, m2]
  have e3 : omB ν 1 g 1 ψ = ((ν (gdet g) : ℂ) * apow (gdet g) ((d₁ : ℂ) / 2)) • fun Z : Matrix (Fin n) (Fin d₁) k => ψ (g'.val * Z * (1 : GL (Fin d₁) k).val) := by
    funext Y
    simp [omB, hg]
  have e4 := mod_inv hL fu one_sb one_sb g'
  rw [e2, map_smul, swap_mid hL hl hν fu.1 (comp_mem one_sb g') one_sb (comp_mem one_sb g') 1 (by simp)] at e1
  refine LinearMap.mem_ker.2 ?_
  rw [map_sub, e3, map_smul, sub_eq_zero]
  refine Eq.trans ?_ e1
  have e5 : (L ∘ₗ tn₁ e (one n) (one n)) (fun Z : Matrix (Fin n) (Fin d₁) k => ψ (g'.val * Z * (1 : GL (Fin d₁) k).val)) = _ := e4.symm
  rw [e5, dg, smul_smul, one_smul, hd, add_div, apow_add]
  congr 1
  simp [apow, mul_assoc])

theorem local_multiplicity_one_irreducible_GL (hB : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {L' : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] W} (hL : Inv e ν L)
    (hL' : Inv e ν L') (hu : USm ν) {l : kˣ} (hl : valuation k (l : k) = 1) (hν : ν l ≠ 1) (hn : n ≤ d₁)
    (ρ : GL (Fin d₁) k → Module.End ℂ W) (hr : Module.rank ℂ W ≤ Cardinal.aleph0)
    (hi : ∀ N : Submodule ℂ W, (∀ g, ∀ x ∈ N, ρ g x ∈ N) → N = ⊥ ∨ N = ⊤)
    (hM : ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * blk e g.val)) = ρ g (L Φ))
    (hM' : ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L' (fun Y : Matrix (Fin n) (Fin d) k => Φ (Y * blk e g.val)) = ρ g (L' Φ))
    (h0 : ∃ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L Φ ≠ 0) : ∃ c : ℂ, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) k), L' Φ = c • L Φ := by
  let S : Submodule ℂ (Matrix (Fin n) (Fin d₁) k → ℂ) :=
    { carrier := {ψ | Full ψ}, add_mem' := fun ha hb => ⟨add_mem ha.1 hb.1, fun Y h => by simp [ha.2 Y h, hb.2 Y h]⟩,
      zero_mem' := ⟨zero_mem _, fun _ _ => rfl⟩, smul_mem' := fun c a ha => ⟨(SB _).smul_mem c ha.1, fun Y h => by simp [ha.2 Y h]⟩ }
  let j := tn₁ e (one n) (one n : (Fin n → k) → ℂ)
  let A : GL (Fin d₁) k → S → S := fun g ψ => ⟨_, full_omB ψ.2 1 g⟩
  have jA : ∀ (g : GL (Fin d₁) k) (ψ : Matrix (Fin n) (Fin d₁) k → ℂ), j (fun Z : Matrix (Fin n) (Fin d₁) k => ψ ((1 : GL (Fin n) k).val * Z * g.val)) =
      fun Y : Matrix (Fin n) (Fin d) k => j ψ (Y * blk e g.val) := fun (g : GL (Fin d₁) k) ψ => funext fun Y => by
    have m1 : mid e (Y * blk e g.val) = mid e Y * g.val := by
      ext i s; simp only [mid, submatrix_apply, Matrix.mul_apply, id]; rw [sum_e (e := e)]; simp [blk]
    have m2 : ∀ t, cl e t (Y * blk e g.val) = cl e t Y := fun t => by
      ext i; simp only [cl, Matrix.mul_apply]; rw [sum_e (e := e)]; cases t <;> simp [blk]
    simp [j, tn₁, tn, m1, m2]
  let μ := L ∘ₗ j ∘ₗ S.subtype
  let μ' := L' ∘ₗ j ∘ₗ S.subtype
  have eA : ∀ g ψ, μ (A g ψ) = ρ g (μ ψ) := fun g ψ => (congrArg L (jA g ψ)).trans (hM g _ (tn_mem ψ.2.1 one_sb one_sb))
  have eA' : ∀ g ψ, μ' (A g ψ) = ρ g (μ' ψ) := fun g ψ => (congrArg L' (jA g ψ)).trans (hM' g _ (tn_mem ψ.2.1 one_sb one_sb))
  have ne : ¬ ∀ ψ, Full ψ → L (tn e ψ (one n) (one n)) = 0 := fun h => let ⟨Φ, h1, h2⟩ := h0; h2 (red hL hu hl hν h Φ h1)
  have ker : ∀ ψ, μ ψ = 0 → μ' ψ = 0 := by
    rcases irrF' hB (α := 1) hn hu (LinearMap.ker (L ∘ₗ j) ⊓ S) (le_inf (aug_ker hL hl hν) (Submodule.span_le.2 (by
      rintro _ ⟨g, ψ, h, rfl⟩
      refine sub_mem ?_ h
      have := S.smul_mem ((ν (gdet g) : ℂ) * apow (gdet g) ((d₁ : ℂ) / 2)) (full_omB h (invT g⁻¹) 1)
      convert this using 1
      funext Y
      simp [omB, invT]))) (fun g ψ h _ => by
        have e1 : omB ν 1 1 g ψ = apow (gdet g) ((n : ℂ) / 2) • (A g ⟨ψ, h.2⟩).1 := by
          funext Y
          simp [omB, A]
        rw [e1]
        refine Submodule.smul_mem _ _ ⟨?_, (A g ⟨ψ, h.2⟩).2⟩
        have : μ ⟨ψ, h.2⟩ = 0 := h.1
        exact (eA g ⟨ψ, h.2⟩).trans (by rw [this, map_zero])) with h | h
    · exact absurd (fun ψ hψ => (h ψ hψ).1) ne
    · exact fun ψ hψ => aug_ker hL' hl hν (h ψ.1 ⟨hψ, ψ.2⟩ ψ.2)
  have top : LinearMap.range μ = ⊤ := (hi _ (by rintro g _ ⟨ψ, rfl⟩; exact ⟨A g ψ, eA g ψ⟩)).resolve_left fun h =>
    ne fun ψ hψ => by
      have : μ ⟨ψ, hψ⟩ ∈ LinearMap.range μ := ⟨_, rfl⟩
      rwa [h, Submodule.mem_bot] at this
  obtain ⟨s, hs⟩ := μ.exists_rightInverse_of_surjective top
  have th : ∀ ψ, (μ' ∘ₗ s) (μ ψ) = μ' ψ := fun ψ => by
    have := ker (s (μ ψ) - ψ) (by rw [map_sub, ← LinearMap.comp_apply μ s, hs, LinearMap.id_apply, sub_self])
    rwa [map_sub, sub_eq_zero] at this
  obtain ⟨c, hc⟩ := dixmier_commutant_scalar _ W ρ hr hi (μ' ∘ₗ s) fun g => LinearMap.ext fun x => by
    obtain ⟨ψ, rfl⟩ := LinearMap.range_eq_top.1 top x
    rw [Module.End.mul_apply, Module.End.mul_apply, ← eA, th, th, eA']
  refine ⟨c, fun Φ hΦ => sub_eq_zero.1 (red (L := L' - c • L) (e := e) ⟨fun g Ψ h => ?_, fun g hg Ψ h => ⟨(hL.right g hg Ψ h).1, ?_⟩⟩
    hu hl hν (fun ψ hψ => ?_) Φ hΦ)⟩
  · simp [hL.left g Ψ h, hL'.left g Ψ h]
  · simp only [LinearMap.sub_apply, LinearMap.smul_apply, (hL.right g hg Ψ h).2, (hL'.right g hg Ψ h).2]
  · have := th ⟨ψ, hψ⟩
    rw [hc] at this
    exact sub_eq_zero.2 this.symm

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
end
end

noncomputable section

namespace PositivityTheory.ThKG.LocalRamifiedLeviRestriction

open NumberField IsDedekindDomain GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.SplitFlip Matrix GlobalTheory.ThK
open PositivityTheory.KCo PositivityTheory.ThK PositivityTheory.ThK.SplitAsm ValuativeRel PositivityTheory.ThKG.Loc
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem inP_det {k : Type} [Field k] [ValuativeRel k] {d d₁ : ℕ} {e : Fin d₁ ⊕ Bool ≃ Fin d} {h : Matrix (Fin d) (Fin d) k} (hh : InP e h) :
    h.det = h (e (.inr false)) (e (.inr false)) * h (e (.inr true)) (e (.inr true)) := by
  obtain ⟨p1, -, -, p3, p4⟩ := hh
  have e1 : h.submatrix e e = fromBlocks 1 (h.submatrix e e).toBlocks₁₂ (h.submatrix e e).toBlocks₂₁ (h.submatrix e e).toBlocks₂₂ := by
    conv_lhs => rw [← fromBlocks_toBlocks (h.submatrix e e)]
    congr 1
    ext s s'
    exact p3 s s'
  rw [← det_submatrix_equiv_self e, e1, det_fromBlocks_one₁₁, ← det_reindex_self finTwoEquiv.symm, det_fin_two]
  simp [finTwoEquiv, toBlocks₁₂, toBlocks₂₁, toBlocks₂₂, Matrix.mul_apply, p1, p4]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

structure Eqv (om : Rep σ X W) (H : Plane E d d₁) (χ : Chr F E) (r : ℝ) {P : Type} [AddCommGroup P] [Module ℂ P]
    (τ : UA σ W₁.J → Module.End ℂ P) (Λ : Fl F v n d →ₗ[ℂ] P) : Prop where
  aug : augAt om v ≤ LinearMap.ker Λ
  act : ∀ t h₁ m, IsLevi H t h₁ m → h₁ ∈ UAt σ W₁ (evFin F v) → ∀ u ∈ unip σ W H, u ∈ UAt σ W (evFin F v) → m ∈ UAt σ W (evFin F v) →
    ∀ φ ∈ SB _, ∀ φ' ∈ SB _, Acts (evFin F v) (om (1, u * m)) φ φ' →
      Λ φ' = ((χ t : ℂ) * (((absE F E t : ℝ) ^ r : ℝ) : ℂ)) • τ h₁ (Λ φ)

theorem one_UAt {m : ℕ} (Y : Spc F E m) : (1 : UA σ Y.J) ∈ UAt σ Y (evFin F v) := fun u _ => by
  rw [show mat (1 : UA σ Y.J) = 1 from rfl, sub_self, smul_zero]

theorem mul_UAt {m : ℕ} {Y : Spc F E m} {g g' : UA σ Y.J} (h : g ∈ UAt σ Y (evFin F v)) (h' : g' ∈ UAt σ Y (evFin F v)) :
    g * g' ∈ UAt σ Y (evFin F v) := fun u hu => by
  rw [show mat (g * g') - 1 = (mat g - 1) * mat g' + (mat g' - 1) by rw [show mat (g * g') = mat g * mat g' from rfl]; noncomm_ring,
    smul_add, ← Matrix.smul_mul, h u hu, h' u hu]
  simp

theorem ua_ext {t : E →ₐ[F] Fv F v} {sec} (h : IsSec σ t sec) (hJ : IsUnit W.J.det) {g g' : UA σ W.J} (hg : g ∈ UAt σ W (evFin F v))
    (hg' : g' ∈ UAt σ W (evFin F v)) (e : (mat g).map (piW t) = (mat g').map (piW t)) : g = g' := by
  have u1 : ((mat g).map (piW t))ᵀ * W.J.map t * (mat g).map (piW (t.comp σ)) = W.J.map t := by
    have := h.unit_rel g
    rwa [incM_map h] at this
  have u2 : ((mat g').map (piW t))ᵀ * W.J.map t * (mat g').map (piW (t.comp σ)) = W.J.map t := by
    have := h.unit_rel g'
    rwa [incM_map h] at this
  have un : IsUnit (((mat g).map (piW t))ᵀ * W.J.map t) :=
    ((isUnit_transpose _).2 (GeneralLinearGroup.map (piW t) g.1).isUnit).mul
      (((isUnit_iff_isUnit_det _).2 hJ).map (t : E →+* Fv F v).mapMatrix)
  refine Subtype.ext (Units.ext (h.extM (z := mat g) (z' := mat g') (fun u hu => ?_) e (un.mul_left_cancel (by rw [u1, e, u2]))))
  rw [show mat g - mat g' = (mat g - 1) - (mat g' - 1) by abel, smul_sub, hg u hu, hg' u hu, sub_zero]

theorem pair_multiplicity_one_ramified (hBe : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) {B : Base F E} (hB : B.IsGood σ) {r₁ s₁ r₂ s₂ r₃ s₃ : ℕ}
    (hX : X.IsHerm σ B r₁ s₁) (hW : W.IsSkew σ B r₂ s₂) (hW₁ : W₁.IsSkew σ B r₃ s₃) {M : Model σ X W} {om : Rep σ X W} {χX χW : Chr F E}
    (hom : M.IsWeil B.ψ χX χW om) (hk : IsHecke F E χW) {K : Subgroup (AF F)ˣ} {m : ℕ} (res : ResEtaPow K χX m) {H : Plane E d d₁} {i₀ i₁}
    (hH : H.IsAdapted σ B W W₁ i₀ i₁) (t : E →ₐ[F] Fv F v) (ram : ¬ GlobalTheory.SplitWeil.IsUnram (chrW χW t)) (hn : n ≤ d₁)
    (hS : ∀ h₀ : GL (Fin d₁) (Fv F v), ∃ h ∈ UAt σ W₁ (evFin F v), (mat h).map (piW t) = h₀)
    {P : Type} [AddCommGroup P] [Module ℂ P] {τ : UA σ W₁.J → Module.End ℂ P} (τ1 : τ 1 = 1) (hr : Module.rank ℂ P ≤ Cardinal.aleph0)
    (hi : ∀ N : Submodule ℂ P, (∀ h ∈ UAt σ W₁ (evFin F v), ∀ x ∈ N, τ h x ∈ N) → N = ⊥ ∨ N = ⊤) {r : ℝ} {Λ Λ' : Fl F v n d →ₗ[ℂ] P}
    (hΛ : Eqv om H χX r τ Λ) (hΛ' : Eqv om H χX r τ Λ') (h0 : ∃ φ ∈ SB _, Λ φ ≠ 0) : ∃ c : ℂ, ∀ φ ∈ SB _, Λ' φ = c • Λ φ := by
  obtain ⟨⟨sec, h⟩, hu⟩ := section_statement F E σ hB.cm v t
  obtain ⟨⟨ι₀, hι⟩, sX, sW, k⟩ := dictionary_extended F E σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  obtain ⟨kX, kW⟩ := k ι₀ hι
  let e : Fin d₁ ⊕ Bool ≃ Fin d := Fintype.equivFinOfCardEq (by simp [hH.rank])
  have gr := fr_gram (e := e) hB.cm hH hW.skew
  have dC : ((fr H e).map t).det ≠ 0 := by
    have := congrArg det gr
    rw [det_mul, det_mul, det_transpose] at this
    have h1 : (fr H e).det ≠ 0 := fun h' => (gm_det (e := e) (Vac.skew_det hW₁)).ne_zero (by rw [← this, h', zero_mul, zero_mul])
    rw [show (fr H e).map t = (t : E →+* Fv F v).mapMatrix (fr H e) from rfl, ← RingHom.map_det]
    exact (map_ne_zero _).2 h1
  let C : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero _ dC
  have hC : Fr σ t W W₁ H e C := ⟨rfl, gr, Vac.skew_det hW⟩
  let ι := chg 1 C⁻¹ 1 ι₀
  have bij : Set.BijOn ι (SB (Fin n × Fin d → Fv F v) : Set _) (SB (Matrix (Fin n) (Fin d) (Fv F v)) : Set _) :=
    bij_smul (bij_comp hι.bij (lrH 1 C⁻¹)) one_ne_zero
  have rX : ∀ g₀ : GL (Fin n) (Fv F v), ∃ g ∈ UAt σ X (evFin F v), Reads v ι (om (g, 1)) (omB (chrW χW t) (chrW χX t) g₀ 1) := fun g₀ =>
    let ⟨g, hg, e1⟩ := sX g₀
    ⟨g, hg, reads_chg (kX g hg g₀ e1) fun Φ Y => B_left _ Φ Y (by simp) rfl⟩
  have rW : ∀ g ∈ UAt σ W (evFin F v), ∀ p : GL (Fin d) (Fv F v), (mat g).map (piW t) = (C * p * C⁻¹).val →
      Reads v ι (om (1, g)) (omB (chrW χW t) (chrW χX t) 1 p) := fun g hg p e1 =>
    reads_chg (kW g hg _ e1) fun Φ Y => B_right _ Φ Y (by rw [← Units.val_mul, ← Units.val_mul, mul_assoc C, inv_mul_cancel_left])
      (by simpa using gdet_conj C⁻¹ p)
  obtain ⟨s, hs⟩ := (ι ∘ₗ (SB _).subtype).exists_leftInverse_of_injective (LinearMap.ker_eq_bot.2 fun a b hab =>
    Subtype.ext (bij.injOn a.2 b.2 hab))
  have s1 : ∀ φ ∈ SB _, (s (ι φ)).1 = φ := fun φ hφ => congrArg Subtype.val (LinearMap.congr_fun hs ⟨φ, hφ⟩)
  have rd : ∀ {T S}, Reads v ι T S → ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)), S Φ ∈ SB _ ∧
      Acts (evFin F v) T (s Φ).1 (s (S Φ)).1 := fun {T S} hR Φ hΦ => by
    obtain ⟨φ, hφ, rfl⟩ := bij.surjOn hΦ
    obtain ⟨φ₁, h1, h2, h3⟩ := hR φ hφ
    rw [← h3, s1 φ hφ, s1 φ₁ h1]
    exact ⟨bij.mapsTo h1, h2⟩
  have eo : ∀ (p : GL (Fin d) (Fv F v)) (Φ : Matrix (Fin n) (Fin d) (Fv F v) → ℂ), omB (chrW χW t) (chrW χX t) 1 p Φ =
      ((chrW χX t (gdet p) : ℂ) * apow (gdet p) ((n : ℂ) / 2)) • fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * p.val) := fun p Φ => by
    funext Y
    simp [omB]
  have c0 : ∀ p : GL (Fin d) (Fv F v), ((chrW χX t (gdet p) : ℂ) * apow (gdet p) ((n : ℂ) / 2)) ≠ 0 := fun p =>
    mul_ne_zero (Units.ne_zero _) (apow_ne_zero _ _)
  have inv : ∀ {Λ : Fl F v n d →ₗ[ℂ] P}, Eqv om H χX r τ Λ → Inv e (chrW χW t) (Λ ∘ₗ (SB _).subtype ∘ₗ s) := fun {Λ} hΛ => by
    refine ⟨fun g₀ Φ hΦ => ?_, fun a ha Φ hΦ => ?_⟩
    · obtain ⟨g, hg, hR⟩ := rX g₀
      have e1 : omB (chrW χW t) 1 g₀ 1 Φ = omB (chrW χW t) (chrW χX t) g₀ 1 Φ := by
        funext Y
        simp [omB]
      have := hΛ.aug (Submodule.subset_span ⟨g, hg, _, (s Φ).2, _, (s _).2, (rd hR Φ hΦ).2, rfl⟩)
      rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at this
      rw [e1]
      exact this
    · have da := inP_det ha
      obtain ⟨p1, p2, p3, p4, p5⟩ := ha
      have x0 : a (e (.inr false)) (e (.inr false)) ≠ 0 := fun h => by simp [h] at p2
      have y0 : a (e (.inr true)) (e (.inr true)) ≠ 0 := fun h => by simp [h] at p3
      let x := Units.mk0 _ x0
      let y := Units.mk0 _ y0
      let p : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero a (da ▸ mul_ne_zero x0 y0)
      let pm : GL (Fin d) (Fv F v) := GeneralLinearGroup.mkOfDetNeZero (bl e 1 x.val y.val) (by rw [usage₄]; simp)
      have im : (pm⁻¹).val = bl e 1 (x⁻¹).val (y⁻¹).val := by
        refine Units.inv_eq_of_mul_eq_one_right ?_
        ext i j
        obtain ⟨i, rfl⟩ := e.surjective i
        obtain ⟨j, rfl⟩ := e.surjective j
        rw [Matrix.mul_apply, sum_e' (e := e)]
        rcases i with i | _ | _ <;> rcases j with j | _ | _ <;> simp [pm, bl, Matrix.one_apply]
      have pu : ∀ i j, (p * pm⁻¹).val i (e j) = a i (e j) * Sum.elim (fun _ => 1) (fun b => cond b (y⁻¹).val (x⁻¹).val) j := fun i j => by
        rw [Units.val_mul, im, Matrix.mul_apply, sum_e' (e := e)]
        rcases j with j | _ | _ <;> simp [p, bl, Matrix.one_apply]
      obtain ⟨u, hu1, hu2⟩ := sW (C * (p * pm⁻¹) * C⁻¹)
      obtain ⟨m', hm1, hm2⟩ := sW (C * pm * C⁻¹)
      obtain ⟨z, z1, z2, z3, z4, z5⟩ := idele_two hB.cm t x y p2 p3
      have un := mem_unip h hC hu1 hu2 (fun i => by
        rw [pu]; split_ifs with hi
        · simp [hi, x, x0]
        · simp [p1 i hi]) (by rw [pu]; simp [y, y0]) (fun s s' => by rw [pu, p4, Matrix.one_apply]; simp) (fun s => by rw [pu, p5]; simp)
      have lv := is_levi h hC hm1 hm2 (one_UAt W₁) (x := x) (y := y) (by
        rw [show mat (1 : UA σ W₁.J) = 1 from rfl, Matrix.map_one _ (map_zero _) (map_one _)]; rfl) z1 z2 z3
      have hR := rW (u * m') (mul_UAt hu1 hm1) p (by
        rw [show mat (u * m') = mat u * mat m' from rfl, Matrix.map_mul, hu2, hm2, ← Units.val_mul]; congr 1; group)
      obtain ⟨q1, q2⟩ := rd hR Φ hΦ
      have := hΛ.act z 1 m' lv (one_UAt W₁) u un hu1 hm1 _ (s Φ).2 _ (s _).2 q2
      have dp : gdet p = x * y := Units.ext da
      have ap : apow (x * y) ((n : ℂ) / 2) = 1 := apow_of_valuation_eq_one (by simp [x, y, p2, p3]) _
      rw [eo] at q1 this
      rw [map_smul, Submodule.coe_smul, map_smul, dp, ap, z4, z5 _ _ _ res, τ1] at this
      refine ⟨(Submodule.smul_mem_iff _ (c0 p)).1 q1, ?_⟩
      have h9 : Λ (s fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * p.val)).1 = Λ (s Φ).1 := by simpa using this
      exact h9
  choose sc sc1 sc2 using hS
  have bd : ∀ g : GL (Fin d₁) (Fv F v), (bl e g.val 1 1).det ≠ 0 := fun g => by
    rw [usage₄, mul_one, mul_one]; exact g.det_ne_zero
  let pb : GL (Fin d₁) (Fv F v) → GL (Fin d) (Fv F v) := fun g => GeneralLinearGroup.mkOfDetNeZero _ (bd g)
  let ρ : GL (Fin d₁) (Fv F v) → Module.End ℂ P := fun g =>
    ((chrW χX t (gdet (pb g)) : ℂ) * apow (gdet (pb g)) ((n : ℂ) / 2))⁻¹ • τ (sc g)
  have lev : ∀ {Λ : Fl F v n d →ₗ[ℂ] P}, Eqv om H χX r τ Λ → ∀ g, ∀ Φ ∈ SB (Matrix (Fin n) (Fin d) (Fv F v)),
      (Λ ∘ₗ (SB _).subtype ∘ₗ s) (fun Y : Matrix (Fin n) (Fin d) (Fv F v) => Φ (Y * blk e g.val)) = ρ g ((Λ ∘ₗ (SB _).subtype ∘ₗ s) Φ) := fun {Λ} hΛ g Φ hΦ => by
    obtain ⟨m', hm1, hm2⟩ := sW (C * pb g * C⁻¹)
    have lv := is_levi h hC hm1 hm2 (sc1 g) (x := 1) (y := 1) (by rw [sc2]; rfl) (z := 1) (fun u _ => by simp) (by simp) (by simp)
    obtain ⟨-, q2⟩ := rd (rW m' hm1 _ hm2) Φ hΦ
    have := hΛ.act 1 _ m' lv (sc1 g) 1 (one_mem _) (one_UAt W) hm1 _ (s Φ).2 _ (s _).2 (by rw [one_mul]; exact q2)
    have bb : blk e g.val = (pb g).val := by
      change _ = bl e g.val 1 1
      rw [blk, bl]
      congr 2
      ext (_ | _) (_ | _) <;> simp
    rw [eo, map_smul, Submodule.coe_smul, map_smul] at this
    rw [bb]
    apply smul_right_injective _ (c0 (pb g))
    simp only [ρ, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ (c0 (pb g)), one_smul]
    simpa using this
  obtain ⟨l, hl, hν⟩ : ∃ l : (Fv F v)ˣ, valuation (Fv F v) (l : Fv F v) = 1 ∧ chrW χW t l ≠ 1 := by
    by_contra h'
    exact ram fun x hx => by by_contra h''; exact h' ⟨x, hx, h''⟩
  obtain ⟨c, hc⟩ := local_multiplicity_one_irreducible_GL hBe (inv hΛ) (inv hΛ') (hu χW hk) hl hν hn ρ hr (fun N hN => hi N fun g hg x hx => by
    have e1 : sc (GeneralLinearGroup.map (piW t) g.1) = g := ua_ext h (Vac.skew_det hW₁) (sc1 _) hg (sc2 _)
    have := N.smul_mem ((chrW χX t (gdet (pb (GeneralLinearGroup.map (piW t) g.1))) : ℂ) *
      apow (gdet (pb (GeneralLinearGroup.map (piW t) g.1))) ((n : ℂ) / 2)) (hN (GeneralLinearGroup.map (piW t) g.1) x hx)
    simpa only [ρ, LinearMap.smul_apply, smul_smul, mul_inv_cancel₀ (c0 _), one_smul, e1] using this) (lev hΛ) (lev hΛ') (by
      obtain ⟨φ, hφ, h0⟩ := h0
      exact ⟨ι φ, bij.mapsTo hφ, by simpa [s1 φ hφ] using h0⟩)
  exact ⟨c, fun φ hφ => by simpa [s1 φ hφ] using hc (ι φ) (bij.mapsTo hφ)⟩

theorem acts_ex {B : Base F E} (hB : B.IsGood σ) {r₁ s₁ r₂ s₂ : ℕ} (hX : X.IsHerm σ B r₁ s₁) (hW : W.IsSkew σ B r₂ s₂)
    {M : Model σ X W} {om : Rep σ X W} {χX χW : Chr F E} (hom : M.IsWeil B.ψ χX χW om) (t : E →ₐ[F] Fv F v) :
    (∀ h₀ : GL (Fin d) (Fv F v), ∃ h ∈ UAt σ W (evFin F v), (mat h).map (piW t) = h₀) ∧
      ∀ h ∈ UAt σ W (evFin F v), ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) (om (1, h)) φ φ₁ := by
  obtain ⟨⟨ι₀, hι⟩, -, sW, k⟩ := dictionary_extended F E σ n d B X W M om χX χW hB ⟨_, _, hX⟩ ⟨_, _, hW⟩ hom v t
  exact ⟨sW, fun h hh φ hφ => let ⟨φ₁, h1, h2, _⟩ := (k ι₀ hι).2 h hh (GeneralLinearGroup.map (piW t) h.1) rfl φ hφ; ⟨φ₁, h1, h2⟩⟩

theorem acts_zero {κ : Type} [Fintype κ] (T : Module.End ℂ ((κ → AF F) → ℂ)) : Acts (evFin F v) T 0 0 := fun r _ => by
  rw [show tens (evFin F v) (0 : (κ → Fv F v) → ℂ) r = 0 from funext fun _ => zero_mul _, map_zero]

theorem acts_lin {κ : Type} [Fintype κ] {T : Module.End ℂ ((κ → AF F) → ℂ)} (ex : ∀ φ ∈ SB _, ∃ φ₁ ∈ SB _, Acts (evFin F v) T φ φ₁)
    {a b a₁ b₁ : (κ → Fv F v) → ℂ} (ha : a ∈ SB _) (hb : b ∈ SB _) (h1 : Acts (evFin F v) T a a₁) (h2 : Acts (evFin F v) T b b₁) (c : ℂ) :
    Acts (evFin F v) T (a + c • b) (a₁ + c • b₁) := fun r hr => by
  have rest_transfer (r : (κ → AF F) → ℂ) (φ₀ : (κ → Fv F v) → ℂ)
      (hne : φ₀ ≠ 0) (hr : Rest (evFin F v) φ₀ r)
      (φ : (κ → Fv F v) → ℂ) (hφ : φ ∈ SB _) : Rest (evFin F v) φ r := by
    obtain ⟨y, hy⟩ := Function.ne_iff.1 hne
    let S : Module.End ℂ ((κ → Fv F v) → ℂ) :=
      (LinearMap.proj y : ((κ → Fv F v) → ℂ) →ₗ[ℂ] ℂ).smulRight ((φ₀ y)⁻¹ • φ)
    have h := PositivityTheory.Member.ZakTransform.lift_mem (v := v) (S := S) (fun θ _ => Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hφ)) hr.2
    rw [PositivityTheory.Member.ZakTransform.lift_tens _ _ (fun x t => hr.1 x _ ((PositivityTheory.Member.ZakTransform.at_iff _).2 (funext fun i => (PositivityTheory.Member.ZakTransform.ep_mul _).trans (by rw [GlobalTheory.EmbChart.evFin_atPlace]))))] at h
    have e : S φ₀ = φ := by
      change φ₀ y • (φ₀ y)⁻¹ • φ = φ
      rw [smul_smul, mul_inv_cancel₀ hy, one_smul]
    exact ⟨hr.1, e ▸ h⟩
  by_cases h0 : a + c • b = 0
  · have key : a₁ + c • b₁ = 0 := by
      by_cases hb0 : b = 0
      · rw [hb0] at h2 h0
        rw [smul_zero, add_zero] at h0
        rw [h0] at h1
        rw [action_uniqueness F κ v T 0 (zero_mem _) _ _ h1 (acts_zero T), action_uniqueness F κ v T 0 (zero_mem _) _ _ h2 (acts_zero T)]
        simp
      · have ea : a = (-c) • b := by rw [neg_smul]; exact eq_neg_of_add_eq_zero_left h0
        by_cases hc : c = 0
        · rw [hc, neg_zero, zero_smul] at ea
          rw [ea] at h1
          rw [action_uniqueness F κ v T 0 (zero_mem _) _ _ h1 (acts_zero T), hc]
          simp
        have : Acts (evFin F v) T a ((-c) • b₁) := fun r hr => by
          have hr' := rest_transfer r a (by rw [ea]; exact smul_ne_zero (neg_ne_zero.2 hc) hb0) hr b hb
          have e1 : ∀ f : (κ → Fv F v) → ℂ, tens (evFin F v) ((-c) • f) r = (-c) • tens (evFin F v) f r := fun f =>
            funext fun _ => by simp [tens, mul_assoc]
          rw [ea, e1, e1, map_smul, h2 r hr']
        rw [action_uniqueness F κ v T a ha _ _ h1 this]
        simp
    rw [h0, key]
    exact acts_zero T r (h0 ▸ hr)
  · have hs := add_mem ha ((SB _).smul_mem c hb)
    have e1 : ∀ f g : (κ → Fv F v) → ℂ, tens (evFin F v) (f + c • g) r = tens (evFin F v) f r + c • tens (evFin F v) g r := fun f g =>
      funext fun _ => by simp [tens, mul_assoc, add_mul]
    rw [e1, e1, map_add (f := _), map_smul, h1 r (rest_transfer r _ h0 hr a ha), h2 r (rest_transfer r _ h0 hr b hb)]

theorem ramifiedMultiplicityOne_of_bernstein (hBe : GlobalTheory.Published.BernsteinUnitaryProductIrreducible) : RamifiedMultiplicityOne := by
  intro F E _ _ _ _ _ σ B a a' a₁ a₁' G G₁ X om om' om₁ om₁' R Rf R₁ Rf₁ H i₀ i₁ χ r m m₁ st hH v hv lam lam' hl hl' h0
  have T := m.triple
  have T₁ := m₁.triple
  have hB := T.base
  let t := B.τ ⟨v, T.chars.sub hv⟩
  obtain ⟨sW₁, ex₁⟩ := acts_ex hB T₁.geo.hV T₁.geo.hW T₁.weil t
  obtain ⟨-, ex⟩ := acts_ex hB T.geo.hV T.geo.hW T.weil t
  obtain ⟨-, -, hν, -, ram, -⟩ := split_character_facts F E B X a a' v t T.chars
  have onto₁ : ∀ x, ∃ φ ∈ SB _, Rf₁.p v φ = x := fun x => Submodule.mem_map.1 ((m₁.fin.onto v).symm ▸ Submodule.mem_top)
  have onto : ∀ x, ∃ φ ∈ SB _, Rf.p v φ = x := fun x => Submodule.mem_map.1 ((m.fin.onto v).symm ▸ Submodule.mem_top)
  have onto' : ∀ x, ∃ φ ∈ SB _, Rf.p' v φ = x := fun x => Submodule.mem_map.1 ((m.fin.onto' v).symm ▸ Submodule.mem_top)
  have wd : ∀ h ∈ UAt σ G₁.W (evFin F v), ∀ φ ∈ SB _, ∀ ψ ∈ SB _, ∀ φ₁ ∈ SB _, ∀ ψ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ →
      Acts (evFin F v) (om₁ (1, h)) ψ ψ₁ → Rf₁.p v φ = Rf₁.p v ψ → Rf₁.p v φ₁ = Rf₁.p v ψ₁ := fun h hh φ a1 ψ a2 φ₁ a3 ψ₁ a4 b1 b2 e => by
    have := m₁.fin.equiv v h hh _ (add_mem a1 ((SB _).smul_mem (-1) a2)) 0 (zero_mem _) _ (add_mem a3 ((SB _).smul_mem (-1) a4)) 0
      (zero_mem _) (acts_lin (ex₁ h hh) a1 a2 b1 b2 (-1)) (acts_zero _) (by simp [e])
    simpa [← sub_eq_add_neg, sub_eq_zero] using this
  have exτ : ∀ h : UA σ G₁.W.J, ∃ τ : Module.End ℂ (Rf₁.Pi v), h ∈ UAt σ G₁.W (evFin F v) → ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _,
      Acts (evFin F v) (om₁ (1, h)) φ φ₁ → τ (Rf₁.p v φ) = Rf₁.p v φ₁ := fun h => by
    by_cases hh : h ∈ UAt σ G₁.W (evFin F v)
    swap
    · exact ⟨0, fun h' => absurd h' hh⟩
    choose s s1 s2 using onto₁
    choose A A1 A2 using ex₁ h hh
    have k : ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ → Rf₁.p v (A _ (s1 (Rf₁.p v φ))) = Rf₁.p v φ₁ :=
      fun φ b1 φ₁ b2 b3 => wd h hh _ (s1 _) _ b1 _ (A1 _ _) _ b2 (A2 _ _) b3 (s2 _)
    have lin : ∀ x y (c : ℂ), Rf₁.p v (A _ (s1 (x + c • y))) = Rf₁.p v (A _ (s1 x)) + c • Rf₁.p v (A _ (s1 y)) := fun x y c => by
      have := k _ (add_mem (s1 x) ((SB _).smul_mem c (s1 y))) _ (add_mem (A1 _ (s1 x)) ((SB _).smul_mem c (A1 _ (s1 y))))
        (acts_lin (ex₁ h hh) (s1 x) (s1 y) (A2 _ _) (A2 _ _) c)
      rw [map_add (f := _), map_smul, s2, s2, map_add (f := _), map_smul] at this
      exact this
    obtain ⟨f, hf⟩ : ∃ f : Rf₁.Pi v → Rf₁.Pi v, ∀ x, f x = Rf₁.p v (A _ (s1 x)) := ⟨_, fun _ => rfl⟩
    have k' : ∀ φ ∈ SB _, ∀ φ₁ ∈ SB _, Acts (evFin F v) (om₁ (1, h)) φ φ₁ → f (Rf₁.p v φ) = Rf₁.p v φ₁ :=
      fun φ b1 φ₁ b2 b3 => (hf _).trans (k φ b1 φ₁ b2 b3)
    have lin' : ∀ x y (c : ℂ), f (x + c • y) = f x + c • f y := fun x y c => by rw [hf, hf, hf]; exact lin x y c
    have z : f 0 = 0 := by simpa using k' 0 (zero_mem _) 0 (zero_mem _) (acts_zero _)
    exact ⟨{ toFun := f, map_add' := fun x y => by simpa using lin' x y 1,
             map_smul' := fun c y => by simpa [z] using lin' 0 y c }, fun _ => k'⟩
  choose τ hτ using exτ
  have τ1 : τ 1 = 1 := LinearMap.ext fun x => by
    obtain ⟨φ, h1, rfl⟩ := onto₁ x
    exact hτ 1 (one_UAt _) φ h1 φ h1 fun r _ => by rw [show ((1 : UA σ G₁.V.J), (1 : UA σ G₁.W.J)) = 1 from rfl, map_one]; rfl
  have hr : Module.rank ℂ (Rf₁.Pi v) ≤ Cardinal.aleph0 := by
    obtain ⟨_, _⟩ := GlobalTheory.SplitWeil.Model.secondCountable_and_t2_local_field (k := Fv F v)
    refine le_trans ?_ (rank_SB (Fin a₁ × Fin (a₁ + a₁') → Fv F v))
    rw [← rank_top, ← m₁.fin.onto v]
    exact rank_map_le _ _
  have hi : ∀ N : Submodule ℂ (Rf₁.Pi v), (∀ h ∈ UAt σ G₁.W (evFin F v), ∀ x ∈ N, τ h x ∈ N) → N = ⊥ ∨ N = ⊤ := fun N hN =>
    m₁.fin.irred v N fun h hh φ b1 φ₁ b2 b3 b4 => hτ h hh φ b1 φ₁ b2 b3 ▸ hN h hh _ b4
  have eq : ∀ {lam}, IsFiniteLocalEquivariantMap om om₁ H v χ r (Rf.p v) (Rf₁.p v) lam → Eqv om H χ r τ (lam ∘ₗ Rf.p v) := fun {lam} hl =>
    ⟨fun φ hφ => by rw [LinearMap.mem_ker, LinearMap.comp_apply, m.fin.inv v hφ, map_zero],
      fun z h₁ m' lv hh u hu b1 b2 φ b3 φ' b4 b5 => by
        obtain ⟨φ₁, c1, c2⟩ := onto₁ (lam (Rf.p v φ))
        obtain ⟨φ₂, c3, c4⟩ := ex₁ h₁ hh φ₁ c1
        rw [LinearMap.comp_apply, LinearMap.comp_apply, hl z h₁ m' lv u hu b1 b2 φ b3 φ' b4 φ₁ c1 φ₂ c3 b5 c4 c2.symm, ← c2,
          hτ h₁ hh φ₁ c1 φ₂ c3 c4]⟩
  have eq' : ∀ {lam}, IsFiniteLocalEquivariantMap om om₁ H v χ r (Rf.p v) (Rf₁.p v) lam → Eqv om' H χ r τ (lam ∘ₗ Rf.p' v) := fun {lam} hl =>
    ⟨fun φ hφ => by rw [LinearMap.mem_ker, LinearMap.comp_apply, m.fin.inv' v hφ, map_zero],
      fun z h₁ m' lv hh u hu b1 b2 φ b3 φ' b4 b5 => by
        obtain ⟨ψ, c1, c2⟩ := onto (Rf.p' v φ)
        obtain ⟨ψ', c3, c4⟩ := ex _ (mul_UAt b1 b2) ψ c1
        rw [LinearMap.comp_apply, LinearMap.comp_apply, ← m.fin.equiv v _ (mul_UAt b1 b2) ψ c1 φ b3 ψ' c3 φ' b4 c4 b5 c2, ← c2]
        exact (eq hl).act z h₁ m' lv hh u hu b1 b2 ψ c1 ψ' c3 c4⟩
  obtain ⟨x, hx⟩ : ∃ x, lam x ≠ 0 := by
    by_contra h'
    push Not at h'
    exact h0 (LinearMap.ext h')
  rcases st with ⟨e1, e2, -, -, rfl, -⟩ | ⟨e1, e2, -, -, rfl, -⟩
  · obtain ⟨c, hc⟩ := pair_multiplicity_one_ramified hBe hB T.geo.hV T.geo.hW T₁.geo.hW T.weil
      (show IsHecke F E (X.β / X.α) from ⟨T.chars.heckeβ.1.div' T.chars.heckeα.1, fun x => by
        rw [MonoidHom.div_apply, T.chars.heckeβ.2, T.chars.heckeα.2, div_one]⟩) T.chars.resβ hH t
      (fun hu => ram hv fun y hy => by
        have := hu y hy
        rw [chrW_div] at this
        rw [Chars.ν, chrW_div, ← inv_div, this, inv_one]) (by omega) sW₁ τ1 hr hi (eq hl) (eq hl')
      (let ⟨φ, h1, h2⟩ := onto x; ⟨φ, h1, by rwa [LinearMap.comp_apply, h2]⟩)
    exact ⟨c, LinearMap.ext fun y => let ⟨φ, h1, h2⟩ := onto y; h2 ▸ hc φ h1⟩
  · obtain ⟨c, hc⟩ := pair_multiplicity_one_ramified hBe hB T.geo.hV' T.geo.hW T₁.geo.hW T.weil'
      (show IsHecke F E (X.α / X.β) from ⟨T.chars.heckeα.1.div' T.chars.heckeβ.1, fun x => by
        rw [MonoidHom.div_apply, T.chars.heckeβ.2, T.chars.heckeα.2, div_one]⟩) T.chars.resα hH t
      (ram hv) (by omega) sW₁ τ1 hr hi (eq' hl) (eq' hl')
      (let ⟨φ, h1, h2⟩ := onto' x; ⟨φ, h1, by rwa [LinearMap.comp_apply, h2]⟩)
    exact ⟨c, LinearMap.ext fun y => let ⟨φ, h1, h2⟩ := onto' y; h2 ▸ hc φ h1⟩

end PositivityTheory.ThKG.LocalRamifiedLeviRestriction
