module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MvecLeviMulUv
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicFourierExpansion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfEigOfMemTwKer
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.LocO

open MeasureTheory GlobalTheory.CompanionTheory.TwistedAverage GlobalTheory.CompanionTheory.Rodier

theorem eq_zero_of_eig_of_mem_twKer {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) {x : V}
    (hx : x ∈ twKer ρ L θ) (he : ∀ l : L, ρ (l : G) x = (θ l : ℂ) • x) : x = 0 := by
  classical
  obtain ⟨M, hM, hs⟩ := exists_sum_eq_zero hρ hL θ hθ hx
  haveI : M.FiniteIndex := hM
  haveI : M.normalCore.FiniteIndex := inferInstance
  haveI : M.normalCore.Normal := Subgroup.normalCore_normal _
  haveI : Finite (L ⧸ M.normalCore) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (L ⧸ M.normalCore) := Fintype.ofFinite _
  have h0 := hs M.normalCore (Subgroup.normalCore_le M)
  have h1 : ∀ t : L, twOrbit ρ L θ x t = x := fun t => by
    rw [twOrbit, he t, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  simp only [h1, Finset.sum_const, Finset.card_univ] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · exact h0

theorem isSmooth_cInd {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] (H : Subgroup G) (σ : Representation ℂ H Z) : IsSmooth (cInd H σ) := by
  intro f
  have h : {g : G | cInd H σ g f = f} = {g : G | ind H σ g f.1.1 = f.1.1} := by
    ext g
    exact ⟨fun h => congrArg (fun x : cIndSpace H σ => x.1.1) h, fun h => Subtype.ext (Subtype.ext h)⟩
  rw [h]
  exact f.1.2

def evL {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] (H : Subgroup G) (σ : Representation ℂ H Z) (x : G) : cIndSpace H σ →ₗ[ℂ] Z :=
  (LinearMap.proj x) ∘ₗ (indSpace H σ).subtype ∘ₗ (smoothPart (ind H σ)).subtype ∘ₗ (cIndSpace H σ).subtype

theorem avgVanish_of_fibre {G Z Γ A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ)
    (ρ₁ : Representation ℂ Γ Z) (hρ₁ : IsSmooth ρ₁)
    (C : Subgroup Γ) (hC : IsCompact (C : Set Γ)) (χ : C →* ℂˣ) (hχ : IsOpen (χ.ker : Set C))
    (c : C → H) (hc : ∀ (b : C) (w : Z), σ (c b) w = ρ₁ (b : Γ) w)
    (e : A → G) (he : ∀ a a', e (a + a') = e a * e a')
    (hce : ∀ (b : C) (a : A), ((c b : H) : G) * e a = e a * ((c b : H) : G))
    (y : G) (D : Set A) (hD0 : (0 : A) ∈ D) (hDs : ∀ a a', a ∈ D → a' ∈ D → a - a' ∈ D)
    (hDc : IsCompact D) (hDo : IsOpen D)
    (L : Subgroup G) (hLU : L ≤ U) (hLc : IsCompact (L : Set G))
    (hθ : IsOpen ((θ.comp (Subgroup.inclusion hLU)).ker : Set L))
    (hL1 : ∀ l : L, ∃ (b : C) (a : A), a ∈ D ∧ y * (l : G) * y⁻¹ = ((c b : H) : G) * e a ∧
      θ (Subgroup.inclusion hLU l) = χ b)
    (hL2 : ∀ b : C, ∃ l : L, y * (l : G) * y⁻¹ = ((c b : H) : G) ∧ θ (Subgroup.inclusion hLU l) = χ b)
    (hL3 : ∀ a ∈ D, ∃ l : L, y * (l : G) * y⁻¹ = e a ∧ θ (Subgroup.inclusion hLU l) = 1)
    (hU : ∀ u ∈ U, ∃ h ∈ H, ∃ a : A, y * u * y⁻¹ = h * e a)
    (hfib : ∀ f' : cIndSpace H σ, IsLocallyConstant (fun a => evL H σ (e a * y) f') ∧
      HasCompactSupport (fun a => evL H σ (e a * y) f'))
    (f : cIndSpace H σ) (hsupp : ∀ a, evL H σ (e a * y) f ≠ 0 → a ∈ D)
    (hz : smInt μ (fun a => evL H σ (e a * y) f) ∈ twKer ρ₁ C χ) :
    AvgVanish H σ U θ f y := by
  classical
  have hev : ∀ (x l : G) (f' : cIndSpace H σ), evL H σ x (cInd H σ l f') = evL H σ (x * l) f' := fun _ _ _ => rfl
  have hleft : ∀ (h : H) (x : G) (f' : cIndSpace H σ), evL H σ ((h : G) * x) f' = σ h (evL H σ x f') :=
    fun h x f' => f'.1.1.2 h x
  have he0 : e 0 = 1 := by
    have := he 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  set θL : L →* ℂˣ := θ.comp (Subgroup.inclusion hLU) with hθL
  obtain ⟨ι, _, r, c₀, h1, h2⟩ := GlobalTheory.CompanionTheory.TwAvgInd.exists_finite_average (cInd H σ) (isSmooth_cInd H σ) hLc θL hθ f
  obtain ⟨g, hg⟩ : ∃ g : cIndSpace H σ, g = c₀ • ∑ i, twOrbit (cInd H σ) L θL f (r i) := ⟨_, rfl⟩
  rw [← hg] at h1
  simp only [← hg] at h2

  let T : cIndSpace H σ →ₗ[ℂ] Z :=
    { toFun := fun f' => smInt μ (fun a => evL H σ (e a * y) f')
      map_add' := fun f₁ f₂ => by
        have := SmIntEl.smInt_add μ (hfib f₁).1 (hfib f₁).2 (hfib f₂).1 (hfib f₂).2
        rw [← this]
        congr 1
      map_smul' := fun s f' => by
        have := SmIntEl.smInt_linear μ (s • (LinearMap.id : Z →ₗ[ℂ] Z)) (hfib f').1 (hfib f').2
        simp only [LinearMap.smul_apply, LinearMap.id_apply, RingHom.id_apply] at this ⊢
        rw [← this]
        congr 1 }
  have hTdef : ∀ f', T f' = smInt μ (fun a => evL H σ (e a * y) f') := fun _ => rfl
  have hpoint : ∀ (l : G) (b : C) (a₁ a : A), y * l * y⁻¹ = ((c b : H) : G) * e a₁ →
      e a * y * l = ((c b : H) : G) * (e (a₁ + a) * y) := by
    intro l b a₁ a h
    have h' : y * l = ((c b : H) : G) * e a₁ * y := by rw [← h]; group
    have h2 : e (a₁ + a) = e a * e a₁ := by rw [add_comm, he]
    rw [mul_assoc, h', h2]
    simp only [← mul_assoc]
    rw [← hce b a]
  have hTl : ∀ (l : G) (b : C) (a₁ : A), y * l * y⁻¹ = ((c b : H) : G) * e a₁ → ∀ f',
      T (cInd H σ l f') = ρ₁ (b : Γ) (T f') := by
    intro l b a₁ hl f'
    set φ : A → Z := fun a => evL H σ (e a * y) f' with hφ
    have hfun : (fun a => evL H σ (e a * y) (cInd H σ l f')) = (ρ₁ (b : Γ)) ∘ (φ ∘ (fun a => a₁ + a)) := by
      funext a
      rw [hev, hpoint l b a₁ a hl, hleft, hc]
      rfl
    have hl₂ : IsLocallyConstant (φ ∘ fun a => a₁ + a) := (hfib f').1.comp_continuous (by fun_prop)
    have hc₂ : HasCompactSupport (φ ∘ fun a => a₁ + a) := (hfib f').2.comp_homeomorph (Homeomorph.addLeft a₁)
    rw [hTdef, hfun, SmIntEl.smInt_linear μ _ hl₂ hc₂,
      SmIntEl.smInt_comp_measurePreserving μ (measurePreserving_add_left μ a₁) (hfib f').1]
    rfl
  have hker : ∀ x ∈ twKer (cInd H σ) L θL, T x ∈ twKer ρ₁ C χ := by
    intro x hx
    have hle : twKer (cInd H σ) L θL ≤ (twKer ρ₁ C χ).comap T := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨l, v, rfl⟩
      obtain ⟨b, a, -, h3, h4⟩ := hL1 l
      show T (_ - _) ∈ twKer ρ₁ C χ
      rw [map_sub, map_smul, hTl _ b a h3]
      have : θL l = χ b := h4
      rw [this]
      exact Submodule.subset_span ⟨b, T v, rfl⟩
    exact hle hx
  have hTg : T g ∈ twKer ρ₁ C χ := by
    have : T g = T f - T (f - g) := by rw [map_sub]; abel
    rw [this]
    exact Submodule.sub_mem _ hz (hker _ h1)
  have heig : ∀ b : C, ρ₁ (b : Γ) (T g) = (χ b : ℂ) • T g := by
    intro b
    obtain ⟨l, h3, h4⟩ := hL2 b
    have h5 : y * (l : G) * y⁻¹ = ((c b : H) : G) * e 0 := by rw [he0, mul_one, h3]
    rw [← hTl _ b 0 h5 g, h2 l, map_smul]
    have : θL l = χ b := h4
    rw [this]
  have hTg0 : T g = 0 := eq_zero_of_eig_of_mem_twKer hρ₁ hC χ hχ hTg heig

  have hsg : ∀ a, evL H σ (e a * y) g ≠ 0 → a ∈ D := by
    intro a ha
    by_contra hn
    apply ha
    have hz0 : ∀ i, evL H σ (e a * y) (twOrbit (cInd H σ) L θL f (r i)) = 0 := by
      intro i
      obtain ⟨b, a₁, ha₁, h3, -⟩ := hL1 (r i)
      rw [twOrbit, map_smul, hev, hpoint _ b a₁ a h3, hleft]
      have : evL H σ (e (a₁ + a) * y) f = 0 := by
        by_contra h
        have h6 := hsupp _ h
        apply hn
        have := hDs _ _ h6 ha₁
        rwa [add_sub_cancel_left] at this
      rw [this, map_zero, smul_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hg, map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz0 i, smul_zero]

  have hper : ∀ a ∈ D, evL H σ (e a * y) g = evL H σ (e 0 * y) g := by
    intro a ha
    obtain ⟨l, h3, h4⟩ := hL3 a ha
    have h5 := congrArg (evL H σ (e 0 * y)) (h2 l)
    rw [hev, map_smul] at h5
    have h6 : e 0 * y * (l : G) = e a * y := by
      rw [he0, one_mul]
      have : y * (l : G) = e a * y := by rw [← h3]; group
      exact this
    rw [h6] at h5
    have h7 : θL l = 1 := h4
    rw [h5, h7]
    simp
  have hφ : (fun a => evL H σ (e a * y) g) = D.indicator fun _ => evL H σ (e 0 * y) g := by
    funext a
    by_cases ha : a ∈ D
    · rw [Set.indicator_of_mem ha, hper a ha]
    · rw [Set.indicator_of_notMem ha]
      by_contra h
      exact ha (hsg a h)
  have hv0 : evL H σ (e 0 * y) g = 0 := by
    have h3 : T g = (((μ D).toReal : ℝ) : ℂ) • evL H σ (e 0 * y) g := by
      rw [hTdef, hφ, SmIntEl.smInt_indicator]
    rw [hTg0] at h3
    have hpos : (μ D).toReal ≠ 0 :=
      (ENNReal.toReal_pos (hDo.measure_pos μ ⟨0, hD0⟩).ne' hDc.measure_lt_top.ne).ne'
    rcases smul_eq_zero.1 h3.symm with h4 | h4
    · exact absurd (Complex.ofReal_eq_zero.1 h4) hpos
    · exact h4
  refine ⟨L, hLU, hLc, g, h1, fun l => h2 l, fun u hu => ?_⟩
  obtain ⟨h, hh, a, hua⟩ := hU u hu
  have h3 : y * u = (h : G) * (e a * y) := by
    have : y * u = (y * u * y⁻¹) * y := by group
    rw [this, hua, mul_assoc]
  show evL H σ (y * u) g = 0
  rw [h3]
  have h4 : evL H σ ((h : G) * (e a * y)) g = σ ⟨h, hh⟩ (evL H σ (e a * y) g) := hleft ⟨h, hh⟩ _ g
  rw [h4]
  have h5 : evL H σ (e a * y) g = 0 := by
    rw [show evL H σ (e a * y) g = _ from congrFun hφ a, hv0]
    simp
  rw [h5, map_zero]

end GlobalTheory.CompanionTheory.BZPhiPG.LocO

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDichotomy
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDichotomy
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.Dich

open GlobalTheory.CompanionTheory.BZPhiPhi GlobalTheory.CompanionTheory.BZPhiPG.Cells

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem blockIndex_false_eq (m j : ℕ) (a : Fin m) :
    eGP m j ⟨false, a⟩ = Fin.castSucc (⟨a.1, by have := a.2; omega⟩ : Fin (m + j)) :=
  Fin.ext (blockIndex_false_val m j a)

theorem blockIndex_true_castSucc (m j : ℕ) (b : Fin (j + 1)) :
    eGP m (j + 1) ⟨true, Fin.castSucc b⟩ =
      Fin.castSucc (⟨m + b.1, by have := b.2; omega⟩ : Fin (m + (j + 1))) :=
  Fin.ext (blockIndex_true_val m (j + 1) _)

theorem mem_mirabolicParabolic_of (m j : ℕ) (x : Mir k (m + (j + 1)))
    (h : ∀ r c : Fin (m + j + 1), ¬ r.val < m → c.val < m →
      ((x : GL (Fin (m + (j + 1) + 1)) k) : Matrix _ _ k) (Fin.castSucc r) (Fin.castSucc c) = 0) :
    x ∈ MirabolicParabolic k m (j + 1) := by
  rw [mem_mirabolicParabolic_iff]
  intro b a
  rw [blockIndex_false_eq]
  induction b using Fin.lastCases with
  | last =>
    rw [blockIndex_true_last, (mem_Mir_iff k _).1 x.2]
    exact Pi.single_eq_of_ne (Fin.castSucc_ne_last _) _
  | cast b =>
    rw [blockIndex_true_castSucc]
    exact h _ _ (by simp) (by simp)

theorem unip_mem_HGP (m j : ℕ) (x : Mir k (m + (j + 1))) (v : Fin (m + (j + 1)) → k)
    (hx : (x : GL (Fin (m + (j + 1) + 1)) k) = unip k (m + (j + 1)) (Multiplicative.ofAdd v)) :
    x ∈ MirabolicParabolic k m (j + 1) := by
  refine mem_mirabolicParabolic_of m j x fun r c hr hc => ?_
  rw [hx]
  refine unip_castSucc_castSucc _ v _ _ ?_
  rintro rfl
  exact hr hc

theorem unip_entry (n : ℕ) (v : Fin n → k) (i c : Fin (n + 1))
    (h : c = Fin.last n → ∀ r : Fin n, i = Fin.castSucc r → v r = 0) :
    (unip k n (Multiplicative.ofAdd v)).val i c = (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i c := by
  show (1 + colMat k n v) i c = _
  rw [Matrix.add_apply]
  by_cases hc : c = Fin.last n
  · induction i using Fin.lastCases with
    | last => simp [colMat, hc]
    | cast r => simp [colMat, hc, h hc r rfl]
  · simp [colMat, hc]

theorem gpProj_unip (m j : ℕ) (y : MirabolicParabolic k m (j + 1)) (v : Fin (m + (j + 1)) → k)
    (hv : ∀ r : Fin (m + (j + 1)), ¬ r.val < m → v r = 0)
    (hy : ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k) =
      unip k (m + (j + 1)) (Multiplicative.ofAdd v)) :
    gpProj k m (j + 1) y = 1 := by
  have hone : ∀ (x : Bool) (a b : Two (Fin m) (Fin (j + 1 + 1)) x),
      (1 : Matrix _ _ k) (eGP m (j + 1) ⟨x, a⟩) (eGP m (j + 1) ⟨x, b⟩) =
        (1 : Matrix (Two (Fin m) (Fin (j + 1 + 1)) x) _ k) a b := by
    intro x a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.one_apply_ne hab, Matrix.one_apply_ne]
      intro e
      exact hab (by simpa using (eGP m (j + 1)).injective e)
  refine Prod.ext ?_ (Subtype.ext ?_)
  · apply Units.ext
    ext a b
    show ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k).val (eGP m (j + 1) ⟨false, a⟩)
      (eGP m (j + 1) ⟨false, b⟩) = _
    rw [hy, unip_entry, hone]
    · rfl
    · intro e
      exact absurd e (blockIndex_false_ne_last m (j + 1) b)
  · apply Units.ext
    ext a b
    show ((y : Mir k (m + (j + 1))) : GL (Fin (m + (j + 1) + 1)) k).val (eGP m (j + 1) ⟨true, a⟩)
      (eGP m (j + 1) ⟨true, b⟩) = _
    rw [hy, unip_entry, hone]
    · rfl
    · intro _ r e
      refine hv r ?_
      have := congrArg Fin.val e
      rw [blockIndex_true_val] at this
      simp at this
      omega

end

section

variable {k : Type} [Field k]

theorem conj_unip (n : ℕ) (g : Mir k (n + 1)) (w : Fin (n + 1) → k) :
    ((g⁻¹ * unipM k n (Multiplicative.ofAdd w) * g : Mir k (n + 1)) : GL (Fin (n + 2)) k) =
      unip k (n + 1) (Multiplicative.ofAdd
        (((mirabolicProjection k (n + 1) g⁻¹ : GL (Fin (n + 1)) k) : Matrix _ _ k).mulVec w)) := by
  obtain ⟨v, A, hp, hA⟩ : ∃ v A, (g : GL (Fin (n + 2)) k) = unip k (n + 1) v * glEmb k (n + 1) A ∧
      A = mirabolicProjection k (n + 1) g := ⟨_, _, eq_unip_glEmb g, rfl⟩
  rw [map_inv (mirabolicProjection k (n + 1)) g, ← hA]
  have e := glEmb_mul_unip' k (n + 1) A⁻¹ (Multiplicative.ofAdd w)
  have c : (unip k (n + 1) v)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) * unip k (n + 1) v =
      unip k (n + 1) (Multiplicative.ofAdd w) := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    rw [mul_comm _ (Multiplicative.ofAdd w), mul_assoc]
    simp
  simp only [Subgroup.coe_mul, InvMemClass.coe_inv, unipM_val, hp]
  simp only [toAdd_ofAdd] at e
  calc (unip k (n + 1) v * glEmb k (n + 1) A)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) *
        (unip k (n + 1) v * glEmb k (n + 1) A)
      = (glEmb k (n + 1) A)⁻¹ * ((unip k (n + 1) v)⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) *
          unip k (n + 1) v) * glEmb k (n + 1) A := by group
    _ = glEmb k (n + 1) A⁻¹ * unip k (n + 1) (Multiplicative.ofAdd w) * glEmb k (n + 1) A := by
        rw [c, map_inv]
    _ = _ := by
        rw [e, mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

end

theorem dichotomy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), ψ ≠ 1 → ∀ (m j : ℕ) (g : Mir k (m + (j + 1))),
    (∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x) ∨
    ∃ u : MirUin k (m + (j + 1)), ∃ hx : g * (u : Mir k (m + (j + 1))) * g⁻¹ ∈ MirabolicParabolic k m (j + 1),
      gpProj k m (j + 1) ⟨_, hx⟩ = 1 ∧ mirChar k ψ (m + j) u ≠ 1 := by
  intro k _ _ _ _ ψ hψ m j g
  by_cases hl : ∃ l : Fin (m + j + 1), l.val < m ∧ rowQ k (m + j) g⁻¹ l ≠ 0
  · obtain ⟨l, hlm, hrl⟩ := hl
    obtain ⟨t, ht⟩ := (AddChar.ne_one_iff).1 hψ
    let w : Fin (m + j + 1) → k := Pi.single l (t / rowQ k (m + j) g⁻¹ l)
    let X : Mir k (m + j + 1) := unipM k (m + j) (Multiplicative.ofAdd w)
    have hu := conj_unip (m + j) g w
    have hmem : g⁻¹ * X * g ∈ MirUin k (m + j + 1) := ⟨_, hu.symm⟩
    have hgx : g * (g⁻¹ * X * g) * g⁻¹ = X := by group
    have hX : X ∈ MirabolicParabolic k m (j + 1) := unip_mem_HGP m j X w rfl
    have hw : ∀ r : Fin (m + (j + 1)), ¬ r.val < m → w r = 0 := by
      intro r hr
      refine Pi.single_eq_of_ne ?_ _
      rintro rfl
      exact hr hlm
    refine Or.inr ⟨⟨g⁻¹ * X * g, hmem⟩, hgx.symm ▸ hX, ?_, ?_⟩
    · refine gpProj_unip m j _ w hw ?_
      show ((g * (g⁻¹ * X * g) * g⁻¹ : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) = _
      rw [hgx]
      rfl
    · rw [mirChar_eq k ψ (m + j) _ _ hu]
      have e : (((mirabolicProjection k (m + j + 1) g⁻¹ : GL (Fin (m + j + 1)) k) : Matrix _ _ k).mulVec w)
          (Fin.last (m + j)) = t := by
        show rowQ k (m + j) g⁻¹ ⬝ᵥ w = t
        simp only [w, dotProduct_single]
        field_simp
      simp only [toAdd_ofAdd, e]
      intro h
      apply ht
      have := congrArg Units.val h
      exact Circle.ext (by simpa using this)
  · have hr0 : ∀ l : Fin (m + j + 1), l.val < m → rowQ k (m + j) g⁻¹ l = 0 := by
      intro l hlm
      by_contra h
      exact hl ⟨l, hlm, h⟩
    obtain ⟨c, hc⟩ := row_ne_zero (mirabolicProjection k (m + j + 1) g⁻¹) (Fin.last (m + j))
    have hc' : rowQ k (m + j) g⁻¹ c ≠ 0 := hc
    have hcs : ¬ c.val < m := fun h => hc' (hr0 c h)
    have hlast : ¬ (Fin.last (m + j)).val < m := by simp
    obtain ⟨B, hBj, hB⟩ := exists_row (fun x : Fin (m + j + 1) => x.val < m) (rowQ k (m + j) g⁻¹) c
      (Fin.last (m + j)) hc' (by simp only [hcs, hlast]) (fun _ x hx => hr0 x hx)
    let d : Mir k (m + j + 1) := levi k (m + j + 1) B
    have hd : d ∈ MirabolicParabolic k m (j + 1) := by
      refine mem_mirabolicParabolic_of m j d fun r c hr hc => ?_
      exact (glEmb_castSucc_castSucc _ B _ _).trans (hB _ _ hr hc)
    have hrow : rowQ k (m + j) g⁻¹ = rowQ k (m + j) d := by
      funext c
      exact (congrFun hBj c).symm.trans (glEmb_castSucc_castSucc _ B _ _).symm
    have hQ := mul_inv_mem_Q_of_rowQ_eq (m + j) g⁻¹ d hrow
    have hQ' : d * g ∈ Q k (m + j) := by
      have := (Q k (m + j)).inv_mem hQ
      simpa using this
    obtain ⟨v, hp⟩ : ∃ v, ((d * g : Mir k (m + j + 1)) : GL (Fin (m + j + 2)) k) =
        unip k (m + j + 1) (Multiplicative.ofAdd v) * glEmb k (m + j + 1) (mirabolicProjection k (m + j + 1) (d * g)) :=
      ⟨_, eq_unip_glEmb (d * g)⟩
    let uM : Mir k (m + j + 1) := unipM k (m + j) (Multiplicative.ofAdd v)
    have huM : uM ∈ MirabolicParabolic k m (j + 1) := unip_mem_HGP m j uM v rfl
    refine Or.inl ⟨d⁻¹ * uM, (MirabolicParabolic k m (j + 1)).mul_mem ((MirabolicParabolic k m (j + 1)).inv_mem hd) huM,
      qProj k (m + j) ⟨d * g, hQ'⟩, ?_⟩
    have e : d * g = uM * embedding₂ k (m + j) (qProj k (m + j) ⟨d * g, hQ'⟩) := Subtype.ext hp
    rw [mul_assoc, ← e]
    group

end GlobalTheory.CompanionTheory.LeibPhi.Dich
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDichotomyStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_double_coset_dichotomy : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), ψ ≠ 1 → ∀ (m j : ℕ) (g : Mir k (m + (j + 1))),
    (∃ h ∈ MirabolicParabolic k m (j + 1), ∃ x : Mir k (m + j), g = h * embedding₂ k (m + j) x) ∨
    ∃ u : MirUin k (m + (j + 1)), ∃ hx : g * (u : Mir k (m + (j + 1))) * g⁻¹ ∈ MirabolicParabolic k m (j + 1),
      gpProj k m (j + 1) ⟨_, hx⟩ = 1 ∧ mirChar k ψ (m + j) u ≠ 1 := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Dich.dichotomy | exact GlobalTheory.CompanionTheory.LeibPhi.Dich.dichotomy | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Dich.dichotomy <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedIntegralMatricesFinite
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedIntegralMatricesFinite
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

namespace GlobalTheory.CompanionTheory.CFin

theorem matrices_bounded_denominator_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsTotallyReal F → ∀ {ι : Type} [Finite ι] (d : ℕ) (B : ℝ), 0 < d → {N : Matrix ι ι E | (∀ u v, IsIntegral ℤ ((d : E) * N u v)) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : ι), ‖τ.1 (N u v)‖ ≤ B}.Finite := by
  intro F E _ _ _ _ _ hF ι _ d B hd
  haveI := hF
  have hS : {x : E | IsIntegral ℤ x ∧ ∀ φ : E →+* ℂ, ‖φ x‖ ≤ (d : ℝ) * B}.Finite :=
    Embeddings.finite_of_norm_le E ℂ _
  have hd0 : (d : E) ≠ 0 := Nat.cast_ne_zero.2 hd.ne'
  have hT := hS.preimage (f := fun e : E => (d : E) * e)
    (fun a _ b _ h => mul_left_cancel₀ hd0 h)
  have hM := Set.Finite.pi' (fun _ : ι => Set.Finite.pi' (fun _ : ι => hT))
  refine hM.subset ?_
  rintro N ⟨h1, h2⟩ u v
  refine ⟨h1 u v, fun φ => ?_⟩
  have hr : ComplexEmbedding.IsReal (φ.comp (algebraMap F E)) :=
    IsTotallyReal.complexEmbedding_isReal _
  have hb := h2 (InfinitePlace.mk (φ.comp (algebraMap F E)))
    ⟨φ, (InfinitePlace.embedding_mk_eq_of_isReal hr).symm⟩ u v
  rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast]
  exact mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg d)

end GlobalTheory.CompanionTheory.CFin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedIntegralMatricesFiniteStatement
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.CompanionTheory.CFin
open Formalism.UG (cT)
open GlobalTheory.Orb (archMat)
open scoped TensorProduct NNReal ENNReal

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bounded_integral_matrices_finite : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E], IsTotallyReal F → ∀ {ι : Type} [Finite ι] (d : ℕ) (B : ℝ), 0 < d → {N : Matrix ι ι E | (∀ u v, IsIntegral ℤ ((d : E) * N u v)) ∧ ∀ (w : InfinitePlace F) (τ : EmbOver E w) (u v : ι), ‖τ.1 (N u v)‖ ≤ B}.Finite := by
  first | exact @GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite | exact GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite | (intros; apply GlobalTheory.CompanionTheory.CFin.matrices_bounded_denominator_finite <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixMapBaseChange
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixMapBaseChange
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin

theorem leviMat_map {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}
    (A A' : Type) [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A')
    (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)) :
    leviMat σ J A' X Y (M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) =
      (leviMat σ J A X Y M).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  let f : (A ⊗[F] E) →+* (A' ⊗[F] E) := (Algebra.TensorProduct.map φ (AlgHom.id F E)).toRingHom
  have hf : ∀ e : E, f (inclR (F := F) A e) = inclR (F := F) A' e := fun e => by
    simp [f, inclR]
  have hZ : ∀ {a b : ℕ} (Z : Matrix (Fin a) (Fin b) E),
      (Z.map (inclR (F := F) A)).map f = Z.map (inclR (F := F) A') := fun Z => by
    ext i j
    simp [hf]
  have hmul : ∀ {a b c : ℕ} (P : Matrix (Fin a) (Fin b) (A ⊗[F] E)) (Q : Matrix (Fin b) (Fin c) (A ⊗[F] E)),
      (P * Q).map f = P.map f * Q.map f := fun P Q => Matrix.map_mul
  have hadd : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P + Q).map f = P.map f + Q.map f :=
    fun P Q => Matrix.map_add f (map_add f) P Q
  have hsub : ∀ P Q : Matrix (Fin n) (Fin n) (A ⊗[F] E), (P - Q).map f = P.map f - Q.map f :=
    fun P Q => Matrix.map_sub f (map_sub f) P Q
  have hone : (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)).map f = 1 :=
    Matrix.map_one f (map_zero f) (map_one f)
  have hdiag : ∀ d : Fin r → A ⊗[F] E, (diagonal d).map f = diagonal (fun i => f (d i)) := fun d => by
    ext i j
    by_cases h : i = j <;> simp [diagonal, h]
  change leviMat σ J A' X Y (M.map f) = (leviMat σ J A X Y M).map f
  have hentry : ∀ (P : Matrix (Fin r) (Fin r) (A ⊗[F] E)) (i : Fin r), f (P i i) = (P.map f) i i :=
    fun _ _ => rfl
  simp only [leviMat, hadd, hsub, hmul, hone, hdiag, hentry, hZ]

end GlobalTheory.CompanionTheory.KFin
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixMapBaseChangeStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_matrix_map_base_change : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E} (A A' : Type) [CommRing A] [Algebra F A] [CommRing A'] [Algebra F A'] (φ : A →ₐ[F] A') (M : Matrix (Fin n) (Fin n) (A ⊗[F] E)), leviMat σ J A' X Y (M.map (Algebra.TensorProduct.map φ (AlgHom.id F E))) = (leviMat σ J A X Y M).map (Algebra.TensorProduct.map φ (AlgHom.id F E)) := by
  first | exact @GlobalTheory.CompanionTheory.KFin.leviMat_map | exact GlobalTheory.CompanionTheory.KFin.leviMat_map | (intros; apply GlobalTheory.CompanionTheory.KFin.leviMat_map <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellRightStable
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellRightStable
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

variable {k : Type} [Field k]

theorem sEmb_mul_row (n : ℕ) (m : Mir k n) (q : Mir k (n + 1)) (j : Fin (n + 1 + 1)) :
    (((sEmb (k := k) n m * q : Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k)
        (Fin.castSucc (Fin.last n)) j =
      ((q : GL (Fin (n + 1 + 1)) k) : Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) (Fin.castSucc (Fin.last n)) j := by
  have hm : ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) =
      GlobalTheory.BZMir.eLast k n :=
    (GlobalTheory.BZMir.mem_Mir_iff k (m : GL (Fin (n + 1)) k)).1 m.2
  have hm' : ∀ x, ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) x =
      GlobalTheory.BZMir.eLast k n x := fun x => congrFun hm x
  have he : (((GlobalTheory.CompanionTheory.BZPhiPG.sEmb (k := k) n m : GlobalTheory.BZMir.Mir k (n + 1)) : GL (Fin (n + 1 + 1)) k) :
      Matrix (Fin (n + 1 + 1)) (Fin (n + 1 + 1)) k) =
      GlobalTheory.BZMir.glEmbMat k (n + 1) ((m : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) :=
    rfl
  simp only [Subgroup.coe_mul, Units.val_mul]
  rw [he, Matrix.mul_apply, Fin.sum_univ_castSucc]
  simp only [GlobalTheory.BZMir.glEmbMat, Fin.lastCases_castSucc, Fin.lastCases_last, hm', zero_mul,
    add_zero, GlobalTheory.BZMir.eLast]
  simp [Pi.single_apply]

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

theorem GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) :
    ∀ p ∈ Cl (k := k) i t, ∀ m, p * sO k i t m ∈ Cl (k := k) i t := by
  intro p hp m
  have key : ∀ j, (((GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sO k i t m⁻¹ * p⁻¹ : GlobalTheory.BZMir.Mir k (i + 1 + t + 1)) :
      GL (Fin (i + 1 + t + 1 + 1)) k) : Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k)
        (Fin.castSucc (Fin.last (i + 1 + t))) j =
      (((p⁻¹ : GlobalTheory.BZMir.Mir k (i + 1 + t + 1)) : GL (Fin (i + 1 + t + 1 + 1)) k) :
        Matrix (Fin (i + 1 + t + 1 + 1)) (Fin (i + 1 + t + 1 + 1)) k) (Fin.castSucc (Fin.last (i + 1 + t))) j :=
    fun j => GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sEmb_mul_row (i + 1 + t)
      (GlobalTheory.CompanionTheory.BZPhiPG.castM k (by omega) m⁻¹) p⁻¹ j
  simp only [GlobalTheory.CompanionTheory.BZPhiPG.Cl, Set.mem_setOf_eq] at hp ⊢
  intro c
  rw [_root_.mul_inv_rev, ← map_inv (GlobalTheory.CompanionTheory.BZPhiPG.OntoO.sO k i t) m]
  exact (key _).trans (hp c)
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClosedCellRightStableStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_cell_right_stable : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ), ∀ p ∈ Cl k i t, ∀ m, p * sO k i t m ∈ Cl k i t := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.Cl_mul_sO <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixOne
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.KFin.LeviOne

theorem sum_parts {S : Type} [Ring S] {n r : ℕ} {a b : Matrix (Fin n) (Fin r) S} {c d : Matrix (Fin r) (Fin n) S}
    (ca : c * a = 0) (db : d * b = 0) (cb : c * b = 1) (da : d * a = 1) :
    a * Matrix.diagonal (fun i => (d * (1 : Matrix (Fin n) (Fin n) S) * a) i i) * d +
      b * Matrix.diagonal (fun i => (c * (1 : Matrix (Fin n) (Fin n) S) * b) i i) * c +
      (1 - a * d - b * c) * (1 : Matrix (Fin n) (Fin n) S) * (1 - a * d - b * c) = 1 := by
  have hd : ∀ m : Matrix (Fin r) (Fin r) S, m = 1 → Matrix.diagonal (fun i => m i i) = 1 := by
    intro m hm
    subst hm
    simp
  have hPa : (1 - a * d - b * c) * a = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, da, Matrix.mul_assoc, ca, Matrix.mul_one,
      Matrix.mul_zero]
    simp
  have hPb : (1 - a * d - b * c) * b = 0 := by
    rw [Matrix.sub_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_assoc, db, Matrix.mul_assoc, cb, Matrix.mul_one,
      Matrix.mul_zero]
    simp
  have hPP : (1 - a * d - b * c) * (1 - a * d - b * c) = 1 - a * d - b * c := by
    conv_lhs => rw [Matrix.mul_sub (1 - a * d - b * c) (1 - a * d) (b * c), Matrix.mul_sub (1 - a * d - b * c) 1 (a * d)]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hPa, hPb, Matrix.zero_mul, Matrix.zero_mul, Matrix.mul_one]
    simp
  rw [Matrix.mul_one, Matrix.mul_one, Matrix.mul_one, hPP, hd _ da, hd _ cb, Matrix.mul_one, Matrix.mul_one]
  abel

theorem leviMat_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A], leviMat σ J A X Y (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)) = 1 := by
  intro F E _ _ _ _ _ σ n J r X Y h hJ hW A _ _
  have hX : cT (σ : E →+* E) (cT (σ : E →+* E) X) = X := by
    ext i j
    simp [cT, cm_conj_conj h]
  have hJJ : cT (σ : E →+* E) J = J := by
    ext i j
    simpa [cT] using hJ.1 i j
  have yx : cT (σ : E →+* E) Y * J * X = 1 := by
    have e := congrArg (cT (σ : E →+* E)) hW.xy
    rw [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hX, hJJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at e
    exact e
  have m0 : ∀ {M : Matrix (Fin r) (Fin n) E} {N : Matrix (Fin n) (Fin r) E}, M * N = 0 →
      M.map (inclR (F := F) A) * N.map (inclR (F := F) A) = 0 := by
    intro M N e
    rw [← Matrix.map_mul, e, Matrix.map_zero _ (map_zero _)]
  have m1 : ∀ {M : Matrix (Fin r) (Fin n) E} {N : Matrix (Fin n) (Fin r) E}, M * N = 1 →
      M.map (inclR (F := F) A) * N.map (inclR (F := F) A) = 1 := by
    intro M N e
    rw [← Matrix.map_mul, e, Matrix.map_one _ (map_zero _) (map_one _)]
  exact sum_parts (m0 hW.xx) (m0 hW.yy) (m1 hW.xy) (m1 yx)

end GlobalTheory.CompanionTheory.KFin.LeviOne

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviMatrixOneStatement
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levi_matrix_one : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y → ∀ (A : Type) [CommRing A] [Algebra F A], leviMat σ J A X Y (1 : Matrix (Fin n) (Fin n) (A ⊗[F] E)) = 1 := by
  first | exact @GlobalTheory.CompanionTheory.KFin.LeviOne.leviMat_one | exact GlobalTheory.CompanionTheory.KFin.LeviOne.leviMat_one | (intros; apply GlobalTheory.CompanionTheory.KFin.LeviOne.leviMat_one <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmallCompactOpenBetween
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmallCompactOpenBetween
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.OntoO

theorem exists_compactOpen_between_mul_small
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (K₀ C : Subgroup G) (hK₀o : IsOpen (K₀ : Set G)) (hK₀c : IsCompact (K₀ : Set G)) (hC : C ≤ K₀)
    (N : Set G) (hN : N ∈ 𝓝 (1 : G)) :
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ C ≤ K ∧ K ≤ K₀ ∧
      ∀ x ∈ K, ∃ n ∈ N, ∃ c ∈ C, x = n * c := by
  obtain ⟨K₆, hK₆o, -, hK₆s⟩ := hbase ((K₀ : Set G) ∩ N)
    (Filter.inter_mem (hK₀o.mem_nhds K₀.one_mem) hN)
  haveI : CompactSpace K₀ := isCompact_iff_compactSpace.mp hK₀c

  set H : Subgroup K₀ := K₆.subgroupOf K₀ with hH
  have hHo : IsOpen (H : Set K₀) := hK₆o.preimage continuous_subtype_val
  haveI : Finite (K₀ ⧸ H) := H.quotient_finite_of_isOpen hHo
  haveI : H.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  set M : Subgroup K₀ := H.normalCore with hM
  have hMH : M ≤ H := Subgroup.normalCore_le H
  have hHc : IsClosed (H : Set K₀) := OpenSubgroup.isClosed ⟨H, hHo⟩
  have hMc : IsClosed (M : Set K₀) := by
    have : (M : Set K₀) = ⋂ b : K₀, (fun a : K₀ => b * a * b⁻¹) ⁻¹' (H : Set K₀) := by
      ext a
      simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]
      exact Iff.rfl
    rw [this]
    exact isClosed_iInter fun b => hHc.preimage (by fun_prop)
  haveI : M.FiniteIndex := Subgroup.finiteIndex_normalCore H
  have hMo : IsOpen (M : Set K₀) := Subgroup.isOpen_of_isClosed_of_finiteIndex M hMc

  set D : Subgroup K₀ := C.subgroupOf K₀ with hD
  set L : Subgroup K₀ := M ⊔ D with hL
  have hLo : IsOpen (L : Set K₀) := Subgroup.isOpen_mono (le_sup_left : M ≤ L) hMo
  have hLc : IsClosed (L : Set K₀) := OpenSubgroup.isClosed ⟨L, hLo⟩
  have himg : ((L.map K₀.subtype : Subgroup G) : Set G) = Subtype.val '' (L : Set K₀) := by
    ext x; simp [Subgroup.mem_map]
  refine ⟨L.map K₀.subtype, ?_, ?_, ?_, ?_, ?_⟩
  · rw [himg]
    exact hK₀o.isOpenMap_subtype_val _ hLo
  · rw [himg]
    exact hLc.isCompact.image continuous_subtype_val
  · intro c hc
    refine ⟨⟨c, hC hc⟩, ?_, rfl⟩
    exact (le_sup_right : D ≤ L) (by simpa [hD, Subgroup.mem_subgroupOf] using hc)
  · exact Subgroup.map_subtype_le L
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ ((M ⊔ D : Subgroup K₀) : Set K₀) := hy
    rw [Subgroup.normal_mul] at hy'
    obtain ⟨m, hm, d, hd, rfl⟩ := Set.mem_mul.mp hy'
    refine ⟨(m : G), (hK₆s (hMH hm)).2, (d : G), hd, rfl⟩

end GlobalTheory.CompanionTheory.BZPhiPG.OntoO
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSmallCompactOpenBetweenStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG GlobalTheory.CompanionTheory.BZPhiPG.OntoO Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_small_compact_open_between : ∀ {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (hbase : ∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (K₀ C : Subgroup G) (hK₀o : IsOpen (K₀ : Set G)) (hK₀c : IsCompact (K₀ : Set G)) (hC : C ≤ K₀)
    (N : Set G) (hN : N ∈ 𝓝 (1 : G)),
    ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ C ≤ K ∧ K ≤ K₀ ∧
      ∀ x ∈ K, ∃ n ∈ N, ∃ c ∈ C, x = n * c := by
  first | exact @GlobalTheory.CompanionTheory.BZPhiPG.OntoO.exists_compactOpen_between_mul_small | exact GlobalTheory.CompanionTheory.BZPhiPG.OntoO.exists_compactOpen_between_mul_small | (intros; apply GlobalTheory.CompanionTheory.BZPhiPG.OntoO.exists_compactOpen_between_mul_small <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentNormal
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentNormal
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibPhi.UNorm

theorem mirProj_eq_one_of_mem {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : u ∈ MirUin k n) :
    mirabolicProjection k n u = 1 := by
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range] at hu
  obtain ⟨v, hv⟩ := hu
  apply Units.ext
  ext i j
  change ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc j.castSucc =
    (1 : Matrix (Fin n) (Fin n) k) i j
  rw [← hv]
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd v)) i.castSucc j.castSucc = _
  simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]

theorem mem_of_mirProj_eq_one {k : Type} [Field k] {n : ℕ} (u : Mir k n) (hu : mirabolicProjection k n u = 1) :
    u ∈ MirUin k n := by
  have hrow := (GlobalTheory.BZMir.mem_Mir_iff k (u : GL (Fin (n + 1)) k)).mp u.2
  have hrow' : ∀ j, ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j =
      (Pi.single (Fin.last n) (1 : k) : Fin (n + 1) → k) j := by
    intro j
    rw [hrow]
    rfl
  have hblk : ∀ i j : Fin n,
      ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc j.castSucc =
        (1 : Matrix (Fin n) (Fin n) k) i j := by
    intro i j
    exact congrArg (fun g : GL (Fin n) k => (g : Matrix (Fin n) (Fin n) k) i j) hu
  rw [GlobalTheory.BZMir.MirUin, Subgroup.mem_subgroupOf, GlobalTheory.BZMir.MirU,
    MonoidHom.mem_range]
  refine ⟨Multiplicative.ofAdd (fun i : Fin n =>
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc (Fin.last n)), ?_⟩
  apply Units.ext
  ext i j
  change (1 + GlobalTheory.BZMir.colMat k n (Multiplicative.toAdd (Multiplicative.ofAdd (fun i : Fin n =>
    ((u : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) i.castSucc (Fin.last n))))) i j = _
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.colMat, hrow']
    | cast j =>
      simp [GlobalTheory.BZMir.colMat, hrow', Matrix.one_apply, Pi.single_apply, Fin.castSucc_ne_last,
        (Fin.castSucc_ne_last j).symm]
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last]
    | cast j => simp [GlobalTheory.BZMir.colMat, Matrix.one_apply, Fin.castSucc_ne_last, hblk]

theorem mirUin_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ), (MirUin k n).Normal := by
  intro k _ _ _ _ n
  refine ⟨fun u hu g => ?_⟩
  apply GlobalTheory.CompanionTheory.LeibPhi.UNorm.mem_of_mirProj_eq_one
  rw [map_mul, map_mul, map_inv, GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirProj_eq_one_of_mem u hu,
    mul_one, mul_inv_cancel]

end GlobalTheory.CompanionTheory.LeibPhi.UNorm
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicUnipotentNormalStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mirabolic_unipotent_normal : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), (MirUin k n).Normal := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirUin_normal | exact GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirUin_normal | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.UNorm.mirUin_normal <;> assumption)
end
end
