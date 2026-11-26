module

public import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.LineFormulas.LineFacts

@[expose] public section

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEquality
noncomputable section

open Matrix
open scoped ComplexOrder

namespace GlobalTheory.CompanionTheory.PSubFlag

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S GlobalTheory.FlagMeas Formalism.MainNotions.S

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

def Pm (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A - A)

def Pp (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A + A)

theorem mem_Vm {x : Fin n → ℂ} : x ∈ Vm A ↔ ∃ z, Pm A *ᵥ z = x := by
  simp only [Vm, LinearMap.mem_range, Matrix.toLin'_apply, Pm]

theorem mem_Wm {y : Fin n → ℂ} : y ∈ Wm A ↔ Pp A *ᵥ y = 0 := by
  simp only [Wm, LinearMap.mem_ker, Matrix.toLin'_apply, Pp]

theorem anti (hA : IsGrad ε A) : Formalism.REAL.Jm ε * A = -(A * Formalism.REAL.Jm ε) := by
  have h := hA.1
  unfold Formalism.REAL.inG at h
  rw [hA.2.1] at h
  exact eq_neg_of_add_eq_zero_right h

theorem Pm_conj (hA : IsGrad ε A) : (Pm A)ᴴ = Pm A := by
  simp [Pm, Matrix.conjTranspose_smul, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, hA.2.1]

theorem Pm_J (hA : IsGrad ε A) : Pm A * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * Pp A := by
  have h := anti hA
  have h2 : Formalism.REAL.Jm ε * (A * A) = A * A * Formalism.REAL.Jm ε := by
    rw [← Matrix.mul_assoc, h, Matrix.neg_mul, Matrix.mul_assoc, h, Matrix.mul_neg, neg_neg, Matrix.mul_assoc]
  simp only [Pm, Pp, Matrix.smul_mul, Matrix.mul_smul, Matrix.add_mul, Matrix.mul_add, h, h2, sub_eq_add_neg, Matrix.neg_mul]

theorem Pp_Pm (hA : IsGrad ε A) : Pp A * Pm A = 0 := by
  have h := hA.2.2.1
  have e : (A * A + A) * (A * A - A) = 0 := by
    have : (A * A + A) * (A * A - A) = (A * A * A) * A - A * A := by
      simp only [Matrix.add_mul, Matrix.mul_sub, Matrix.mul_assoc]
      abel
    rw [this, h, sub_self]
  simp only [Pp, Pm, Matrix.smul_mul, Matrix.mul_smul, e, smul_zero]

theorem Vm_le_Wm (hA : IsGrad ε A) : Vm A ≤ Wm A := by
  intro x hx
  obtain ⟨z, rfl⟩ := mem_Vm.1 hx
  rw [mem_Wm, Matrix.mulVec_mulVec, Pp_Pm hA, Matrix.zero_mulVec]

theorem mem_Wm_iff (hA : IsGrad ε A) (y : Fin n → ℂ) :
    y ∈ Wm A ↔ ∀ x ∈ Vm A, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  have key : ∀ z, star (Pm A *ᵥ z) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = star z ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (Pp A *ᵥ y)) := by
    intro z
    rw [Matrix.star_mulVec, Pm_conj hA, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Pm_J hA,
      Matrix.mulVec_mulVec]
  constructor
  · intro hy x hx
    obtain ⟨z, rfl⟩ := mem_Vm.1 hx
    rw [key, mem_Wm.1 hy, Matrix.mulVec_zero, dotProduct_zero]
  · intro h
    have h1 := h _ (mem_Vm.2 ⟨Formalism.REAL.Jm ε *ᵥ (Pp A *ᵥ y), rfl⟩)
    rw [key, dotProduct_star_self_eq_zero] at h1
    have h2 := congrArg (Formalism.REAL.Jm ε *ᵥ ·) h1
    simp only [Matrix.mulVec_mulVec, Formalism.REAL.Jm_mul_self, ← Matrix.mul_assoc, Matrix.one_mul, Matrix.mulVec_zero] at h2
    exact mem_Wm.2 h2

theorem isoFlag (hA : IsGrad ε A) : IsIsoFlag ε (fun _ : Fin 1 => rk A) (W A) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro i k h
    fin_cases i <;> fin_cases k <;> simp_all [W]
  · intro i
    fin_cases i
    show Module.finrank ℂ (Vm A) = Module.finrank ℂ (⊥ : Submodule ℂ (Fin n → ℂ)) + rk A
    simp [rk]
  · intro x hx y hy
    exact (mem_Wm_iff hA y).1 (Vm_le_Wm hA hy) x hx

theorem keeps_of_stable (g : Formalism.REAL.UJ ε) {S : Submodule ℂ (Fin n → ℂ)} (h : ∀ y ∈ S, uMat g *ᵥ y ∈ S) :
    Keeps (uMat g) S :=
  Submodule.eq_of_le_of_finrank_eq (by rintro _ ⟨y, hy, rfl⟩; exact h y hy)
    (GlobalTheory.RealIwasawa.finrank_map_toLin _ _ (GlobalTheory.RealIwasawa.uMat_inv_mul g) S)

theorem stable_of_keeps {g : Matrix (Fin n) (Fin n) ℂ} {S : Submodule ℂ (Fin n → ℂ)} (h : Keeps g S) :
    ∀ y ∈ S, g *ᵥ y ∈ S := fun y hy => by
  have : Matrix.toLin' g y ∈ S.map (Matrix.toLin' g) := Submodule.mem_map_of_mem hy
  rw [h, Matrix.toLin'_apply] at this
  exact this

theorem flagN_fix {u : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε (W A)) {y : Fin n → ℂ} (hy : y ∈ Vm A) :
    uMat u *ᵥ y = y := by
  have h : uMat u *ᵥ y - y ∈ (⊥ : Submodule ℂ (Fin n → ℂ)) := hu.1 0 y hy
  exact sub_eq_zero.1 ((Submodule.mem_bot ℂ).1 h)

theorem flagN_stable_Wm (hA : IsGrad ε A) {u : Formalism.REAL.UJ ε} (hu : u ∈ flagN ε (W A)) {y : Fin n → ℂ}
    (hy : y ∈ Wm A) : uMat u *ᵥ y ∈ Wm A := by
  have h : uMat u *ᵥ y - y ∈ Vm A := hu.2 y ((mem_Wm_iff hA y).1 hy)
  have := add_mem (Vm_le_Wm hA h) hy
  simpa using this

theorem flagM_stable_Vm {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) {y : Fin n → ℂ} (hy : y ∈ Vm A) :
    uMat m *ᵥ y ∈ Vm A :=
  (hm 1 y hy).1

theorem flagM_stable_Wm (hA : IsGrad ε A) {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) {y : Fin n → ℂ}
    (hy : y ∈ Wm A) : uMat m *ᵥ y ∈ Wm A := by
  refine (mem_Wm_iff hA _).2 fun x hx => ?_
  have hx' : uMat m⁻¹ *ᵥ x ∈ Vm A :=
    GlobalTheory.RealIwasawa.inv_stable _ _ (GlobalTheory.RealIwasawa.uMat_inv_mul m) (Vm A)
      (fun z hz => flagM_stable_Vm hm hz) x hx
  have e : x = uMat m *ᵥ (uMat m⁻¹ *ᵥ x) := by
    rw [Matrix.mulVec_mulVec, GlobalTheory.RealIwasawa.uMat_mul_inv, Matrix.one_mulVec]
  have h0 := (mem_Wm_iff hA y).1 hy _ hx'
  rw [e, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    GlobalTheory.RealIwasawa.uMat_form]
  exact h0

theorem psubEq : PSubEq := by
  intro n ε A hA g
  constructor
  · intro hg
    have hp : ∀ i, ∀ y ∈ W A i, uMat g *ᵥ y ∈ W A i := by
      intro i y hy
      fin_cases i
      · have : y = 0 := (Submodule.mem_bot ℂ).1 hy
        rw [this, Matrix.mulVec_zero]
        exact zero_mem _
      · exact stable_of_keeps hg.1 y hy
    obtain ⟨m, hm, hu⟩ := GlobalTheory.RealIwasawa.exists_unip_mul_levi (isoFlag hA) g hp
    exact ⟨g * m⁻¹, hu, m, hm, by group⟩
  · rintro ⟨u, hu, m, hm, rfl⟩
    refine ⟨?_, ?_⟩
    · exact keeps_mul (keeps_of_stable u fun y hy => by rw [flagN_fix hu hy]; exact hy)
        (keeps_of_stable m fun y hy => flagM_stable_Vm hm hy)
    · exact keeps_mul (keeps_of_stable u fun y hy => flagN_stable_Wm hA hu hy)
        (keeps_of_stable m fun y hy => flagM_stable_Wm hA hm hy)

end GlobalTheory.CompanionTheory.PSubFlag
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.ParabolicSubgroupEqualityStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ParabolicSubgroupEquality : CompanionTheory.RgExh.Dec.N.S.PSubEq := by
  first | exact @GlobalTheory.CompanionTheory.PSubFlag.psubEq | exact GlobalTheory.CompanionTheory.PSubFlag.psubEq | (intros; apply GlobalTheory.CompanionTheory.PSubFlag.psubEq <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFacts
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFacts
open Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.GradFlag

open CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S

variable {n : ℕ} {ε : Fin n → Bool} {A : Matrix (Fin n) (Fin n) ℂ}

def pM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A - A)

def qM (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A * A + A)

theorem J_mul (h : IsGrad ε A) : Formalism.REAL.Jm ε * A = -(A * Formalism.REAL.Jm ε) := by
  obtain ⟨hg, hH, -, -⟩ := h
  have h0 : Aᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * A = 0 := hg
  rw [hH] at h0
  exact eq_neg_of_add_eq_zero_right h0

theorem A4 (h : A * A * A = A) : A * A * A * A = A * A := by rw [h]

theorem pM_idem (h : A * A * A = A) : pM A * pM A = pM A := by
  have h4 := A4 h
  unfold pM
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_sub, ← mul_assoc, h4, h]
  module

theorem pM_mul_qM (h : A * A * A = A) : pM A * qM A = 0 := by
  have h4 := A4 h
  unfold pM qM
  simp only [smul_mul_assoc, mul_smul_comm, smul_smul, sub_mul, mul_add, add_mul, mul_sub, ← mul_assoc, h4, h]
  module

theorem J_mul_pM (h : IsGrad ε A) : Formalism.REAL.Jm ε * pM A = qM A * Formalism.REAL.Jm ε := by
  have hJ := J_mul h
  have h2 : Formalism.REAL.Jm ε * (A * A) = A * A * Formalism.REAL.Jm ε := by
    rw [← mul_assoc, hJ, neg_mul, mul_assoc, hJ, mul_neg, neg_neg, mul_assoc]
  unfold pM qM
  rw [mul_smul_comm, smul_mul_assoc, mul_sub, add_mul, h2, hJ, sub_neg_eq_add]

theorem trace_qM (h : IsGrad ε A) : Matrix.trace (qM A) = Matrix.trace (pM A) := by
  have hJJ := Formalism.REAL.Jm_mul_self ε
  have : qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε := by
    rw [J_mul_pM h, mul_assoc, hJJ, mul_one]
  rw [this, Matrix.trace_mul_comm, ← mul_assoc, hJJ, one_mul]

theorem pM_conjTranspose (h : Aᴴ = A) : (pM A)ᴴ = pM A := by
  unfold pM
  simp [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, h]

theorem isProj (h : A * A * A = A) : LinearMap.IsProj (Vm A) (Matrix.toLin' (pM A)) := by
  refine ⟨fun x => ⟨x, rfl⟩, ?_⟩
  rintro _ ⟨y, rfl⟩
  change Matrix.toLin' (pM A) (Matrix.toLin' (pM A) y) = Matrix.toLin' (pM A) y
  rw [← LinearMap.comp_apply, ← Matrix.toLin'_mul, pM_idem h]

theorem trace_pM (h : A * A * A = A) : Matrix.trace (pM A) = (rk A : ℂ) := by
  have := (isProj h).trace
  rw [Matrix.trace_toLin'_eq] at this
  exact this

theorem one_le_rk (h : IsGrad ε A) : 1 ≤ rk A := by
  obtain ⟨-, -, h3, hA⟩ := id h
  by_contra hc
  have h0 : rk A = 0 := by omega
  have hb : Vm A = ⊥ := Submodule.finrank_eq_zero.mp h0
  have hP : pM A = 0 := by
    have : Matrix.toLin' (pM A) = 0 := LinearMap.range_eq_bot.mp hb
    simpa using this
  have hQ : qM A = 0 := by
    have hJJ := Formalism.REAL.Jm_mul_self ε
    have : qM A = Formalism.REAL.Jm ε * pM A * Formalism.REAL.Jm ε := by
      rw [J_mul_pM h, mul_assoc, hJJ, mul_one]
    rw [this, hP]; simp
  apply hA
  have : A = qM A - pM A := by unfold pM qM; module
  rw [this, hP, hQ, sub_zero]

theorem isotropic (h : IsGrad ε A) {x y : Fin n → ℂ} (hx : x ∈ Vm A) (hy : y ∈ Vm A) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
  obtain ⟨-, hH, h3, -⟩ := id h
  obtain ⟨u, rfl⟩ := hx
  obtain ⟨v, rfl⟩ := hy
  change star (pM A *ᵥ u) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (pM A *ᵥ v)) = 0
  have hz : pM A * (Formalism.REAL.Jm ε * pM A) = 0 := by
    rw [J_mul_pM h, ← mul_assoc, pM_mul_qM h3, zero_mul]
  rw [star_mulVec, pM_conjTranspose hH, mulVec_mulVec, dotProduct_mulVec, vecMul_vecMul, hz]
  simp

theorem flagFacts : FlagFacts := by
  intro n ε A h
  obtain ⟨-, -, h3, -⟩ := id h
  refine ⟨one_le_rk h, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [W]
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have h0 : W A 0 = ⊥ := rfl
    have h1 : W A 1 = Vm A := rfl
    change Module.finrank ℂ (W A 1) = Module.finrank ℂ (W A 0) + rk A
    rw [h0, h1, finrank_bot, zero_add]
    rfl
  · intro x hx y hy
    exact isotropic h hx hy
  · have hj : (Matrix.trace ((1 / 2 : ℂ) • (A * A + A))).re = (rk A : ℝ) := by
      change (Matrix.trace (qM A)).re = _
      rw [trace_qM h, trace_pM h3]
      simp
    unfold rhoA
    simp only [hj]

end GlobalTheory.CompanionTheory.GradFlag
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.FlagFactsStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rgExh_flagFacts : CompanionTheory.RgExh.Dec.N.S.FlagFacts := by
  first | exact @GlobalTheory.CompanionTheory.GradFlag.flagFacts | exact GlobalTheory.CompanionTheory.GradFlag.flagFacts | (intros; apply GlobalTheory.CompanionTheory.GradFlag.flagFacts <;> assumption)
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InitialStatement
section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InitialStatement
noncomputable section

open MeasureTheory Matrix Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.CompanionTheory.RgStart

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec CompanionTheory.RgExh.Dec.N.S ReciprocityTheory.ChartRestriction.DS GlobalTheory.FlagMeas Formalism.MainNotions.S GlobalTheory.Count

variable {n : ℕ} {ε : Fin n → Bool}

theorem measurable_modA (A : Matrix (Fin n) (Fin n) ℂ) : Measurable (modA (ε := ε) A) := by
  unfold modA
  have h1 : Measurable fun τ : Fin 1 → ℝ => layerProd n 1 (fun _ : Fin 1 => rk A) τ id := by
    unfold layerProd
    simp only [id]
    fun_prop
  exact (h1.comp (Measurable.of_eval fun i =>
    measurable_locSize_uMat n ε 1 (fun _ : Fin 1 => rk A) (W A) i)).ennreal_ofReal

theorem detOn_pos_of_left_inv {f g : Matrix (Fin n) (Fin n) ℂ} (hgf : g * f = 1) (V : Submodule ℂ (Fin n → ℂ))
    (hV : ∀ y ∈ V, f *ᵥ y ∈ V) : 0 < detOn f V := by
  classical
  have h : ∀ y ∈ V, Matrix.toLin' f y ∈ V := fun y hy => by
    rw [Matrix.toLin'_apply]
    exact hV y hy
  unfold detOn
  rw [dite_eq_left h]
  refine norm_pos_iff.mpr fun h0 => ?_
  obtain ⟨x, hx, hx0⟩ := SetLike.exists_of_lt (LinearMap.bot_lt_ker_of_det_eq_zero h0)
  have h1 : f *ᵥ (x : Fin n → ℂ) = 0 := by
    have := congrArg Subtype.val (LinearMap.mem_ker.mp hx)
    simpa [Matrix.toLin'_apply] using this
  have h2 : (x : Fin n → ℂ) = 0 := by
    have := congrArg (g *ᵥ ·) h1
    simpa [Matrix.mulVec_mulVec, hgf] using this
  exact hx0 (by simpa using Subtype.ext h2)

theorem modA_ne_zero (A : Matrix (Fin n) (Fin n) ℂ) {m : Formalism.REAL.UJ ε} (hm : m ∈ flagM ε (W A)) :
    modA A m ≠ 0 := by
  have hinv : (((m : (Matrix (Fin n) (Fin n) ℂ)ˣ)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) *
      uMat m = 1 := Units.inv_mul _
  have hd : ∀ i, 0 < detOn (uMat m) (W A i) := fun i =>
    detOn_pos_of_left_inv hinv _ fun y hy => (hm i y hy).1
  have hτ : ∀ i : Fin 1, 0 < locSize (fun _ : Fin 1 => rk A) (W A) (uMat m) i := fun i =>
    Real.rpow_pos_of_pos (div_pos (hd _) (hd _)) _
  have hp : 0 < layerProd n 1 (fun _ : Fin 1 => rk A) (locSize (fun _ : Fin 1 => rk A) (W A) (uMat m)) id := by
    unfold layerProd
    simp only [id]
    exact mul_pos (prod_pos fun i _ => prod_pos fun k _ =>
        mul_pos (pow_pos (div_pos (hτ i) (hτ k)) _) (pow_pos (mul_pos (hτ i) (hτ k)) _))
      (prod_pos fun i _ => mul_pos (pow_pos (hτ i) _) (pow_pos (pow_pos (hτ i) _) _))
  unfold modA
  exact (ENNReal.ofReal_pos.mpr hp).ne'

theorem startOf : StartOf := by
  intro _ _ hLine hSlab hFub hKMaj n ε H _ _ _ σ D E hK hU hL2 A μ hA hμ u ξ
  obtain ⟨F, hFm, hFK, hFint, hFle⟩ := hKMaj n ε H σ D E hK hU hL2 u ξ
  obtain ⟨μN, μM, hN, hM, hMS, hMinv, ⟨κ, hκ0, hκt, hκ⟩, hnull⟩ := hFub n ε A hA
  obtain ⟨a, τ, ha, hτ, haM, hadd, haS, hcent, hmod, htime⟩ := hLine n ε A hA
  haveI := hN
  haveI := hM
  obtain ⟨⟨Msub, eM⟩, hS, -⟩ := GlobalTheory.FlagLeviGroup.levi_compact_subgroups n ε 1 (W A)
  have hfin : (∫⁻ v, ∫⁻ m, modA A m * F (v * m) ∂μM ∂μN) < ⊤ := by
    have h := hFint
    rw [hκ F hFm hFK] at h
    exact ENNReal.lt_top_of_mul_ne_top_right h.ne hκ0
  have h1N : (1 : Formalism.REAL.UJ ε) ∈ flagN ε (W A) := by
    refine ⟨fun i y _ => ?_, fun y _ => ?_⟩ <;>
      · rw [GlobalTheory.FlagLeviGroup.uMat_one, Matrix.one_mulVec, sub_self]
        exact Submodule.zero_mem _
  have hsl := hSlab (Formalism.REAL.UJ ε) μN μM (flagM ε (W A)) a (modA A) τ (rhoA A) hS.measurableSet hMS ha.measurable
    (measurable_modA A) hτ hadd
    (fun m hm t => by
      have : m * a t ∈ Msub := Msub.mul_mem (by rw [← SetLike.mem_coe, eM]; exact hm)
        (by rw [← SetLike.mem_coe, eM]; exact haS t)
      rw [← eM]; exact this)
    (fun t => hMinv (a t) (haS t) (hcent t)) hmod
    (fun m hm t => by simpa using htime 1 h1N m hm t)
    (fun m hm => modA_ne_zero A hm) F hFm hfin
  let I : Formalism.REAL.UJ ε → ℝ≥0∞ := fun x =>
    ∫⁻ t in Set.Ioi (0 : ℝ), F (x * a t) * ENNReal.ofReal (Real.exp (2 * rhoA A * t))
  have hI : Measurable I := Measurable.lintegral_prod_right'
    (f := fun p : Formalism.REAL.UJ ε × ℝ => F (p.1 * a p.2) * ENNReal.ofReal (Real.exp (2 * rhoA A * p.2)))
    ((hFm.comp (measurable_fst.mul (ha.measurable.comp measurable_snd))).mul (by fun_prop))
  have hE : MeasurableSet (I ⁻¹' {⊤}) := hI (measurableSet_singleton ⊤)
  have h0 : (μN.prod μM) {p | p.1 * p.2 ∈ I ⁻¹' {⊤}} = 0 := by
    refine measure_mono_null (fun p hp => ?_) (ae_iff.mp hsl)
    have hp' : I (p.1 * p.2) = ⊤ := hp
    show ¬ I (p.1 * p.2) < ⊤
    rw [hp']
    exact lt_irrefl _
  have hμE : μ (I ⁻¹' {⊤}) = 0 := hnull μ hμ _ hE h0
  have hae : ∀ᵐ x ∂μ, I x ≠ ⊤ := by
    refine ae_iff.mpr (measure_mono_null (fun x hx => ?_) hμE)
    exact not_not.mp hx
  have hle : ∀ y : Formalism.REAL.UJ ε, lineInt ε (baseCoef σ D ξ u) A (-rhoA A) y ≤ I y := by
    intro y
    unfold lineInt
    refine lintegral_mono fun t => ?_
    have e1 : S7.toM y * NormedSpace.exp ((t : ℂ) • A) = uMat (y * a t) := by
      rw [← haM t]
      rfl
    have e2 : Real.exp (-2 * (-rhoA A) * t) = Real.exp (2 * rhoA A * t) := by
      congr 1
      ring
    rw [e1, e2]
    exact mul_le_mul' (hFle _) le_rfl
  filter_upwards [hae] with x hx
  exact lt_of_le_of_lt (hle x) (lt_top_iff_ne_top.mpr hx)

end GlobalTheory.CompanionTheory.RgStart
end
end

section -- merged from CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.InitialStatementStatement
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.InitialStatement : CompanionTheory.RgExh.Dec.N.S.StartOf := by
  first | exact @GlobalTheory.CompanionTheory.RgStart.startOf | exact GlobalTheory.CompanionTheory.RgStart.startOf | (intros; apply GlobalTheory.CompanionTheory.RgStart.startOf <;> assumption)
end
end
