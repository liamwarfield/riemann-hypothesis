module

public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CoordOfMemXa
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualFlagOfSaturatedIsotropicFlag
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualFlagOfSaturatedIsotropicFlag
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.FullFlag

theorem rkK_mono {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [FiniteDimensional K V] {M N : Submodule (𝓞 K) V} (h : M ≤ N) : Formalism.HN.rkK M ≤ Formalism.HN.rkK N :=
  Submodule.finrank_mono (Submodule.span_mono h)

theorem main : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ (F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (r : ℕ → ℕ), IsDualFlag I.J F (2 * a + 1) ∧ F (2 * a + 1) = lamX I (1, xf) ∧ (∀ i : Fin (a + 1), F i = S i) ∧ (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) ∧ (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) ∧ r a = I.n - 2 * ∑ i, j i ∧ ∀ b, 2 * a + 1 ≤ b → r b = 0 := by
  intro I xf a j S hS
  obtain ⟨h0, hmono, hrk, hsat, hiso⟩ := hS
  set x : I.GA := (1, xf) with hx
  obtain ⟨-, hA, -, -, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨-, -, -, -, hw⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hw v).1
  obtain ⟨-, -, -, hmain⟩ := PerpStep.main I x
  have hform : ∀ s y : Fin I.n → I.E,
      star s ⬝ᵥ (I.J *ᵥ y) = Formalism.UG.hform (starRingEnd I.E) I.J s y := by
    intro s y
    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply,
      -star_trivial]
  have hmem : ∀ N y, y ∈ perpIn I x N ↔ y ∈ lamX I x ∧ ∀ s ∈ N, star s ⬝ᵥ (I.J *ᵥ y) = 0 := by
    intro N y
    rw [PerpStep.perpIn_eq, PerpStep.mem_perp]
    simp only [hform]
  have hsatS : ∀ i, Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S i) := by
    intro i
    have e : S i = lamX I x ⊓ (Submodule.span I.E (S i : Set (Fin I.n → I.E))).restrictScalars (𝓞 I.E) := by
      ext y
      exact hsat i y
    rw [e]
    exact PerpStep.sat_inf (bas I) (frm I x) hX _ hA _
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E),
      ∀ b, G b = S ⟨min b a, Nat.lt_succ_of_le (min_le_right _ _)⟩ := ⟨_, fun _ => rfl⟩
  have hGS : ∀ i : Fin (a + 1), G i = S i := by
    intro i
    rw [hG]
    congr 1
    ext
    have := i.2
    simp only
    omega
  have hG0 : G 0 = ⊥ := (hGS 0).trans h0
  have hGm : Monotone G := by
    intro b c h
    rw [hG, hG]
    exact hmono (Fin.mk_le_mk.2 (min_le_min_right _ h))
  have hGsat : ∀ b, Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (G b) := by
    intro b
    rw [hG]
    exact hsatS _
  have hGr : ∀ i : Fin a, Formalism.HN.rkK (G (i + 1)) = Formalism.HN.rkK (G i) + j i := by
    intro i
    have h1 := hGS i.succ
    have h2 := hGS i.castSucc
    rw [Fin.val_succ] at h1
    rw [Fin.val_castSucc] at h2
    rw [h1, h2, hrk]
  have hGsum : ∀ b (hb : b ≤ a), Formalism.HN.rkK (G b) = ∑ i : Fin b, j (Fin.castLE hb i) := by
    intro b
    induction b with
    | zero => intro _; simp [hG0, Formalism.HN.rkK]
    | succ b ih =>
      intro hb
      rw [Fin.sum_univ_castSucc]
      have := hGr ⟨b, hb⟩
      simp only at this
      rw [this, ih (by omega)]
      rfl
  have hGa : Formalism.HN.rkK (G a) = ∑ i, j i := by
    rw [hGsum a le_rfl]; rfl
  have hPr : ∀ b, Formalism.HN.rkK (perpIn I x (G b)) + Formalism.HN.rkK (G b) = I.n :=
    fun b => (hmain _ _ (hGsat b) (hGsat b) le_rfl).2.1
  have hPP : ∀ b, perpIn I x (perpIn I x (G b)) = G b :=
    fun b => (hmain _ _ (hGsat b) (hGsat b) le_rfl).2.2.1
  have hPa : ∀ b c, b ≤ c → perpIn I x (G c) ≤ perpIn I x (G b) :=
    fun b c h => (hmain _ _ (hGsat b) (hGsat c) (hGm h)).2.2.2.1
  have hP0 : perpIn I x (G 0) = lamX I x := by
    ext y
    rw [hmem, hG0]
    refine ⟨fun h => h.1, fun h => ⟨h, fun s hs => ?_⟩⟩
    rw [(Submodule.mem_bot _).1 hs]
    simp
  have hmid : G a ≤ perpIn I x (G a) := by
    intro y hy
    have e : G a = S (Fin.last a) := hGS (Fin.last a)
    rw [hmem]
    refine ⟨(hGsat a).1 hy, fun s hs => ?_⟩
    rw [hform]
    rw [e] at hs hy
    exact hiso s hs y hy
  obtain ⟨F, hF1, hF2⟩ : ∃ F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E),
      (∀ b, b ≤ a → F b = G b) ∧ ∀ b c, a < b → c = 2 * a + 1 - b → F b = perpIn I x (G c) :=
    ⟨fun b => if b ≤ a then G b else perpIn I x (G (2 * a + 1 - b)), fun b hb => if_pos hb,
      fun b c hb hc => hc ▸ if_neg (by omega)⟩
  have hFm : Monotone F := by
    refine monotone_nat_of_le_succ fun b => ?_
    rcases lt_trichotomy b a with h | rfl | h
    · rw [hF1 b h.le, hF1 (b + 1) h]
      exact hGm (by omega)
    · rw [hF1 b le_rfl, hF2 (b + 1) b (by omega) (by omega)]
      exact hmid
    · rw [hF2 b _ h rfl, hF2 (b + 1) _ (by omega) rfl]
      exact hPa _ _ (by omega)
  have hFtop : ∀ b, 2 * a + 1 ≤ b → F b = lamX I x := fun b hb => by
    rw [hF2 b 0 (by omega) (by omega), hP0]
  refine ⟨F, fun b => Formalism.HN.rkK (F (b + 1)) - Formalism.HN.rkK (F b), ⟨hFm, ?_, ?_, ?_⟩, hFtop _ le_rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF1 0 (by omega), hG0]
  · intro b hb
    rw [hFtop b hb, hFtop _ le_rfl]
  · intro b hb y
    rw [hFtop _ le_rfl, ← hmem]
    by_cases h : b ≤ a
    · rw [hF1 b h, hF2 _ b (by omega) (by omega)]
    · rw [hF2 b _ (by omega) rfl, hPP, hF1 _ (by omega)]
  · intro i
    rw [hF1 i (by have := i.2; omega), hGS]
  · intro b
    have := rkK_mono (hFm (Nat.le_succ b))
    simp only [Nat.succ_eq_add_one] at this ⊢
    omega
  · intro i
    have hi := i.2
    have h1 := hGr i
    have h2 := hPr i
    have h3 := hPr (i + 1)
    simp only
    rw [hF1 i (by omega), hF1 (i + 1) (by omega), hF2 (2 * a - i + 1) i (by omega) (by omega),
      hF2 (2 * a - i) (i + 1) (by omega) (by omega)]
    omega
  · have h2 := hPr a
    simp only
    rw [hF1 a le_rfl, hF2 (a + 1) a (by omega) (by omega)]
    omega
  · intro b hb
    simp only
    rw [hFtop b hb, hFtop _ (by omega), Nat.sub_self]

end GlobalTheory.RadCov.FullFlag
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualFlagOfSaturatedIsotropicFlagStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_selfDual_flag_of_saturated_isotropic_flag : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ (F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (r : ℕ → ℕ), IsDualFlag I.J F (2 * a + 1) ∧ F (2 * a + 1) = lamX I (1, xf) ∧ (∀ i : Fin (a + 1), F i = S i) ∧ (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) ∧ (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) ∧ r a = I.n - 2 * ∑ i, j i ∧ ∀ b, 2 * a + 1 ≤ b → r b = 0 := by
  first | exact @GlobalTheory.RadCov.FullFlag.main | exact GlobalTheory.RadCov.FullFlag.main | (intros; apply GlobalTheory.RadCov.FullFlag.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationMemStandardMiddleSpace
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationMemStandardMiddleSpace
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov

namespace GlobalTheory.DegVol.MidLift

open GlobalTheory.DegVol.RealMat

variable {k r j : ℕ}

private lemma Hpk_esI_apply' (a : Fin r) (i : Fin (2 * r + k + 1)) :
    Hpk k r (esI k r a) i = if i = eI k r a then 1 else 0 := by
  have ha := a.isLt
  simp only [Hpk, esI, eI, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_esI (u : Fin (2 * r + k + 1) → ℂ) (a : Fin r) :
    herm (Hpk k r) u (bvec (esI k r a)) = u (eI k r a) := by
  simp [herm, bvec, dotProduct, Matrix.mulVec, Pi.single_apply, Hpk_esI_apply']

theorem coord_eq_zero {g : Mat k r} (hg : g ∈ UH (Hpk k r))
    (hX : ∀ a : Fin r, a.val < j → g⁻¹ *ᵥ bvec (eI k r a) ∈ XstJ k r j ∧ g *ᵥ bvec (eI k r a) ∈ XstJ k r j)
    {u : Fin (2 * r + k + 1) → ℂ} (hu : ∀ a : Fin r, a.val < j → herm (Hpk k r) u (g⁻¹ *ᵥ bvec (eI k r a)) = 0)
    (b : Fin r) (hb : b.val < j) : u (eI k r b) = 0 := by
  have hdet : IsUnit g.det := GlobalTheory.DegVol.RealMat.isUnit_det hg

  have hinj : Function.Injective (Matrix.mulVecLin g⁻¹) := by
    intro x y hxy
    have h := congrArg (fun v => g *ᵥ v) hxy
    simpa [Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet] using h

  have hli : ∀ f : {a : Fin r // a.val < j} → Fin (2 * r + k + 1), Function.Injective f →
      LinearIndependent ℂ (fun a => bvec (f a)) := by
    intro f hf
    have h := (Pi.basisFun ℂ (Fin (2 * r + k + 1))).linearIndependent.comp f hf
    convert h using 1
    funext a
    simp [bvec, Function.comp]
  have hI1 : Function.Injective fun a : {a : Fin r // a.val < j} => eI k r a.1 := by
    intro a a' h
    have h' := congrArg Fin.val h
    simp only [eI, Fin.val_mk] at h'
    exact Subtype.ext (Fin.ext h')
  have hI2 : Function.Injective fun a : {a : Fin r // a.val < j} => esI k r a.1 := by
    intro a a' h
    have h' := congrArg Fin.val h
    simp only [esI, Fin.val_mk] at h'
    have := a.1.isLt
    have := a'.1.isLt
    exact Subtype.ext (Fin.ext (by omega))
  have hl1 : LinearIndependent ℂ (fun a : {a : Fin r // a.val < j} => bvec (eI k r a.1)) := hli _ hI1
  have hl2 : LinearIndependent ℂ (fun a : {a : Fin r // a.val < j} => bvec (esI k r a.1)) := hli _ hI2

  have hle : (XJ k r j).map (Matrix.mulVecLin g⁻¹) ≤ XstJ k r j := by
    unfold XJ
    rw [Submodule.map_span_le]
    rintro _ ⟨a, rfl⟩
    rw [Matrix.mulVecLin_apply]
    exact (hX a.1 a.2).1
  have hrank : Module.finrank ℂ ((XJ k r j).map (Matrix.mulVecLin g⁻¹)) = Module.finrank ℂ (XstJ k r j) := by
    rw [← (Submodule.equivMapOfInjective _ hinj (XJ k r j)).finrank_eq]
    unfold XJ XstJ
    rw [finrank_span_eq_card hl1, finrank_span_eq_card hl2]
  have heq : (XJ k r j).map (Matrix.mulVecLin g⁻¹) = XstJ k r j :=
    Submodule.eq_of_le_of_finrank_eq hle hrank
  have hmem : bvec (esI k r b) ∈ (XJ k r j).map (Matrix.mulVecLin g⁻¹) := by
    rw [heq]
    unfold XstJ
    exact Submodule.subset_span ⟨⟨b, hb⟩, rfl⟩
  obtain ⟨x, hx, hxe⟩ := Submodule.mem_map.1 hmem
  have hzero : ∀ x ∈ XJ k r j, herm (Hpk k r) u (g⁻¹ *ᵥ x) = 0 := by
    intro x hx
    unfold XJ at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact hu a.1 a.2
    | zero => simp [herm]
    | add x₁ x₂ _ _ h₁ h₂ => rw [Matrix.mulVec_add, GlobalTheory.DegVol.RealMat.herm_add_right, h₁, h₂, add_zero]
    | smul c y _ h => rw [Matrix.mulVec_smul, GlobalTheory.DegVol.RealMat.herm_smul_right, h, mul_zero]
  rw [← herm_esI u b, ← hxe, Matrix.mulVecLin_apply]
  exact hzero x hx

theorem inWb_of_mem_Wn : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ w ∈ N.Wn, inWb k r (Φ w) := by
  intro K V _ _ _ _ _ _ _ _ H r N k σ ρ β Φ z z' g hρ hF w hw
  unfold IsFrameOf at hF
  obtain ⟨hR, -, -, -, ⟨c, hN⟩, he, hist, -, -⟩ := hF
  unfold IsReal at hR
  obtain ⟨-, -, hiso, -⟩ := hR
  unfold IsNormal0 at hN
  obtain ⟨hgG, -, -, -, -, hX, -, -⟩ := hN
  unfold GlobalTheory.DegCnt.NF.Wn at hw
  rw [GlobalTheory.DegCnt.NFGeom.mem_perp'] at hw

  have hBe : ∀ a : Fin r, H.B w (N.F.e a.castSucc) = 0 := by
    intro a
    have h1 : N.F.e a.castSucc ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
    rw [← H.herm (N.F.e a.castSucc) w, hw _ h1, star_zero]
  have hBe' : ∀ a : Fin r, H.B w (N.F'.e a.castSucc) = 0 := by
    intro a
    have h1 : N.F'.e a.castSucc ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.subset_span ⟨a, a.isLt, rfl⟩))
    rw [← H.herm (N.F'.e a.castSucc) w, hw _ h1, star_zero]
  have hBist : ∀ b : Fin r, N.j ≤ b.val → H.B w (N.ist b) = 0 := by
    intro b hb
    have h1 : N.ist b ∈ N.F.X ⊔ N.F'.X ⊔ N.Ist :=
      Submodule.mem_sup_right (Submodule.subset_span ⟨b, hb, rfl⟩)
    rw [← H.herm (N.ist b) w, hw _ h1, star_zero]
  have hρ' : ∀ n : ℕ, ((ρ ^ n : ℝ) : ℂ) ≠ 0 := fun n => Complex.ofReal_ne_zero.2 (pow_pos hρ n).ne'

  have hes : ∀ a : Fin r, Φ w (esI k r a) = 0 := by
    intro a
    have h1 := hiso w (N.F.e a.castSucc)
    rw [(he a).1, GlobalTheory.DegVol.RealMat.herm_smul_right, GlobalTheory.DegVol.RealMat.herm_eI, hBe a, map_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left (star_ne_zero.2 (hρ' _))

  have hhi : ∀ b : Fin r, N.j ≤ b.val → Φ w (eI k r b) = 0 := by
    intro b hb
    have h1 := hiso w (N.ist b)
    rw [hist b hb, GlobalTheory.DegVol.RealMat.herm_smul_right, herm_esI, hBist b hb, map_zero] at h1
    exact (mul_eq_zero.1 h1).resolve_left
      (star_ne_zero.2 (Complex.ofReal_ne_zero.2 (inv_ne_zero (pow_pos hρ _).ne')))

  have hlo : ∀ b : Fin r, b.val < N.j → Φ w (eI k r b) = 0 := by
    have hdet : IsUnit g.det := GlobalTheory.DegVol.RealMat.isUnit_det hgG
    intro b hb
    refine coord_eq_zero (j := N.j) hgG hX (fun a _ => ?_) b hb
    have h3 : Φ (N.F'.e a.castSucc) = ((ρ ^ (r - a.val) : ℝ) : ℂ) • (g⁻¹ *ᵥ bvec (eI k r a)) := by
      rw [← Matrix.mulVec_smul, ← (he a).2, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
        Matrix.one_mulVec]
    have h2 : g⁻¹ *ᵥ bvec (eI k r a) = (((ρ ^ (r - a.val) : ℝ) : ℂ))⁻¹ • Φ (N.F'.e a.castSucc) := by
      rw [h3, inv_smul_smul₀ (hρ' _)]
    rw [h2, GlobalTheory.DegVol.RealMat.herm_smul_right, hiso, hBe' a, map_zero, mul_zero]
  unfold inWb
  intro i hi
  rcases hi with hi | hi
  · have hb : eI k r ⟨i.val, hi⟩ = i := Fin.ext rfl
    rw [← hb]
    by_cases hj : i.val < N.j
    · exact hlo ⟨i.val, hi⟩ hj
    · exact hhi ⟨i.val, hi⟩ (not_lt.1 hj)
  · have hlt : 2 * r + k - i.val < r := by
      have := i.isLt
      omega
    have hb : esI k r ⟨2 * r + k - i.val, hlt⟩ = i := by
      apply Fin.ext
      simp only [esI, Fin.val_mk]
      have := i.isLt
      omega
    rw [← hb]
    exact hes _

end GlobalTheory.DegVol.MidLift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealisationMemStandardMiddleSpaceStatement
open NumberField MeasureTheory Matrix Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp GlobalTheory.DegVol
open scoped Pointwise ENNReal Classical
open GlobalTheory.DegVol.RefCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realisation_mem_standard_middle_space : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V) (r : ℕ) (N : NF H r) (k : ℕ) (σ : K →+* ℂ) (ρ : ℝ) (β : Fin r → ℕ) (Φ : V → Fin (2 * r + k + 1) → ℂ) (z z' : Fin (2 * r + k + 1) → ℂ) (g : Mat k r), 0 < ρ → IsFrameOf N k σ ρ β Φ z z' g → ∀ w ∈ N.Wn, inWb k r (Φ w) := by
  first | exact @GlobalTheory.DegVol.MidLift.inWb_of_mem_Wn | exact GlobalTheory.DegVol.MidLift.inWb_of_mem_Wn | (intros; apply GlobalTheory.DegVol.MidLift.inWb_of_mem_Wn <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBlockFrameLocalSplit
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBlockFrameLocalSplit
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.LocSplit

theorem biorth_decomp {K : Type} [CommRing K] {n m : ℕ} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    (h : Biorth r m T T') (y : Fin n → K) :
    y = ∑ b ∈ Finset.range m, T b *ᵥ (T' b *ᵥ y) := by
  have := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ y) h.2.2
  simp only [Matrix.one_mulVec, Matrix.sum_mulVec] at this
  simp only [Matrix.mulVec_mulVec]
  exact this.symm

theorem biorth_map {E K : Type} [CommRing E] [CommRing K] {n m : ℕ} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) E} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) E}
    (h : Biorth r m T T') (φ : E →+* K) {P : Matrix (Fin n) (Fin n) K} (hP : IsUnit P) :
    Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have key : ∀ b b', (T' b).map φ * P * (P⁻¹ * (T b').map φ) = (T' b * T b').map φ := by
    intro b b'
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, h1, Matrix.one_mul, Matrix.map_mul]
  refine ⟨fun b => ?_, fun b b' hb => ?_, ?_⟩
  · rw [key, h.1 b, Matrix.map_one _ (map_zero φ) (map_one φ)]
  · rw [key, h.2.1 b b' hb, Matrix.map_zero _ (map_zero φ)]
  · have e : ∀ b, P⁻¹ * (T b).map φ * ((T' b).map φ * P)
        = P⁻¹ * φ.mapMatrix (T b * T' b) * P := by
      intro b
      rw [RingHom.mapMatrix_apply, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    simp only [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← map_sum, h.2.2, map_one, mul_one, h2]

theorem map_mulVec_comp {E K : Type} [CommRing E] [CommRing K] {n p : ℕ} (φ : E →+* K)
    (A : Matrix (Fin n) (Fin p) E) (y : Fin p → E) :
    A.map φ *ᵥ (fun l => φ (y l)) = fun l => φ ((A *ᵥ y) l) := by
  ext i
  exact (RingHom.map_mulVec φ A y i).symm

theorem block_mem {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule R (Fin n → K)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    {Λ : ∀ b, Submodule R (Fin (r b) → K)} (h : Biorth r m T T')
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    {b k : ℕ} (hb : b < k) {v : Fin (r b) → K} (hv : v ∈ Λ b) : T b *ᵥ v ∈ F k := by
  rw [hF]
  intro b'
  rw [Matrix.mulVec_mulVec]
  by_cases e : b' = b
  · subst e
    rw [h.1, Matrix.one_mulVec]
    exact ⟨hv, fun hk => absurd hk (by omega)⟩
  · rw [h.2.1 _ _ e, Matrix.zero_mulVec]
    exact ⟨zero_mem _, fun _ => rfl⟩

theorem mem_locFlag_iff {E : Type} [Field E] [NumberField E] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule (𝓞 E) (Fin n → E)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) E} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) E}
    {Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)} (h : Biorth r m T T')
    (hΛ : ∀ b, Submodule.IsFullLattice E (Λ b))
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    (φ : E →+* ℂ) {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (k : ℕ) (y : Fin n → ℂ) :
    y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  constructor
  · intro hy b hb
    unfold locFlag at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      have h0 := ((hF k z).1 hz b).2 hb
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one, map_mulVec_comp, h0]
      ext l
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx, smul_zero]
  · intro hy
    rw [biorth_decomp (biorth_map h φ hP) y]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : k ≤ b
    · simp only [hy b hb, Matrix.mulVec_zero]
      exact zero_mem _
    have A : ∀ v : Fin (r b) → E,
        (P⁻¹ * (T b).map φ) *ᵥ (fun l => φ (v l)) ∈ locFlag φ P F k := by
      intro v
      have hv : v ∈ Submodule.span E (Λ b : Set (Fin (r b) → E)) := by
        letI := hΛ b
        rw [Submodule.IsFullLattice.span_eq_top]; trivial
      induction hv using Submodule.span_induction with
      | mem x hx =>
        rw [← Matrix.mulVec_mulVec, map_mulVec_comp]
        exact Submodule.subset_span ⟨_, block_mem h hF (by omega) hx, rfl⟩
      | zero =>
        have : (fun l => φ ((0 : Fin (r b) → E) l)) = 0 := by ext l; simp
        rw [this, Matrix.mulVec_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        have : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext l; simp
        rw [this, Matrix.mulVec_add]
        exact add_mem hx hy
      | smul c x _ hx =>
        have : (fun l => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext l; simp
        rw [this, Matrix.mulVec_smul]
        exact Submodule.smul_mem _ _ hx
    have B : ∀ u : Fin (r b) → ℂ, (P⁻¹ * (T b).map φ) *ᵥ u ∈ locFlag φ P F k := by
      intro u
      have e : u = ∑ j, u j • fun l => φ ((Pi.single j (1 : E) : Fin (r b) → E) l) := by
        ext l
        simp [Finset.sum_apply, Pi.single_apply, apply_ite φ]
      rw [e, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ (A _)
    exact B _

theorem exists_lowers_blocks {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule R (Fin n → K)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    {Λ : ∀ b, Submodule R (Fin (r b) → K)} (h : Biorth r m T T')
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) (c : ℕ)
    (Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) K)
    (hZ : ∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) :
    ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  refine ⟨∑ b : Fin m, T b * Z b * T' (b + c + 1), fun a y hy => ?_, fun a => ?_⟩
  · rw [Matrix.sum_mulVec]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 := (hF _ y).1 hy (b + c + 1)
    by_cases hb : (b : ℕ) < a
    · exact block_mem h hF hb (hZ b _ h1.1)
    · rw [h1.2 (by omega), Matrix.mulVec_zero, Matrix.mulVec_zero]
      exact zero_mem _
  · rw [Matrix.mul_sum, Matrix.sum_mul, Finset.sum_eq_single a]
    · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.1, Matrix.one_mul, Matrix.mul_assoc, h.1,
        Matrix.mul_one]
    · intro b _ hb
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.2.1 _ _ (fun e => hb (Fin.ext e.symm)),
        Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha

theorem locSplit : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' → (∀ b, Submodule.IsFullLattice E (Λ b)) → (∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) → (∀ (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) ∧ ∀ k y, y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0) ∧ ∀ c, (∀ Y ∈ lowers F c, ∀ b, ∀ y ∈ Λ (b + c + 1), (T' b * Y * T (b + c + 1)) *ᵥ y ∈ Λ b) ∧ ∀ Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) E, (∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) → ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  intro E _ _ n m F r T T' Λ h hΛ hF
  refine ⟨fun φ P hP => ⟨biorth_map h φ hP, mem_locFlag_iff h hΛ hF φ hP⟩, fun c => ⟨?_, ?_⟩⟩
  · intro Y hY b y hy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ((hF (b + 1) _).1 (hY (b + 1) _ (block_mem h hF (by omega) hy)) b).1
  · exact exists_lowers_blocks h hF c

end GlobalTheory.RadCov.LocSplit
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBlockFrameLocalSplitStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_block_frame_local_split : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' → (∀ b, Submodule.IsFullLattice E (Λ b)) → (∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) → (∀ (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) ∧ ∀ k y, y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0) ∧ ∀ c, (∀ Y ∈ lowers F c, ∀ b, ∀ y ∈ Λ (b + c + 1), (T' b * Y * T (b + c + 1)) *ᵥ y ∈ Λ b) ∧ ∀ Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) E, (∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) → ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  first
  | exact @GlobalTheory.RadCov.LocSplit.locSplit
  | intro E _ _ n m F r T T' Λ h hΛ hF
    exact GlobalTheory.RadCov.LocSplit.locSplit E n m F r T T' Λ h
      (fun b => (hΛ b).toIsLattice) hF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumePiLatticeUnitaryCoordinates
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumePiLatticeUnitaryCoordinates
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

noncomputable section

namespace GlobalTheory.CovPi

open GlobalTheory.HomCovolume

theorem hasCov_pi {β : Type} [Fintype β] {V : β → Type} [∀ b, NormedAddCommGroup (V b)]
    [∀ b, NormedSpace ℝ (V b)] [∀ b, FiniteDimensional ℝ (V b)] [∀ b, MeasurableSpace (V b)]
    [∀ b, BorelSpace (V b)] {μ : ∀ b, Measure (V b)} [∀ b, (μ b).IsAddHaarMeasure]
    {L : ∀ b, Submodule ℤ (V b)} {c : β → ℝ} (h : ∀ i, HasCov (μ i) (L i) (c i)) :
    HasCov (Measure.pi μ) (Submodule.pi Set.univ L) (∏ i, c i) := by
  classical
  have hd : ∀ i, DiscreteTopology (L i) := fun i => (h i).1
  have hz : ∀ i, IsZLattice ℝ (L i) := fun i => (h i).2.1
  have hc : ∀ i, ZLattice.covolume (L i) (μ i) = c i := fun i => (h i).2.2
  let B : ∀ i, Module.Basis (Module.Free.ChooseBasisIndex ℤ (L i)) ℝ (V i) := fun i =>
    (Module.Free.chooseBasis ℤ (L i)).ofZLatticeBasis ℝ
  have hBmem : ∀ i j, B i j ∈ L i := fun i j => by
    simp only [B, Module.Basis.ofZLatticeBasis_apply]
    exact (Module.Free.chooseBasis ℤ (L i) j).2
  have hBspan : ∀ i, Submodule.span ℤ (Set.range (B i)) = L i := fun i =>
    (Module.Free.chooseBasis ℤ (L i)).ofZLatticeBasis_span ℝ
  have hspan : Submodule.pi Set.univ L = Submodule.span ℤ (Set.range (Pi.basis B)) := by
    apply le_antisymm
    · intro x hx
      rw [Submodule.mem_pi] at hx
      rw [← Finset.univ_sum_single x]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hxi : x i ∈ Submodule.span ℤ (Set.range (B i)) := by
        rw [hBspan]; exact hx i (Set.mem_univ i)
      refine Submodule.span_induction
        (p := fun y _ => Pi.single i y ∈ Submodule.span ℤ (Set.range (Pi.basis B))) ?_ ?_ ?_ ?_ hxi
      · rintro _ ⟨j, rfl⟩
        exact Submodule.subset_span ⟨⟨i, j⟩, by simp⟩
      · simp
      · intro y z _ _ hy hz
        rw [Pi.single_add]; exact add_mem hy hz
      · intro a y _ hy
        rw [Pi.single_smul]; exact Submodule.smul_mem _ a hy
    · rw [Submodule.span_le]
      rintro _ ⟨⟨i, j⟩, rfl⟩
      rw [SetLike.mem_coe, Submodule.mem_pi]
      intro i' _
      rw [Pi.basis_apply]
      by_cases hi : i' = i
      · subst hi; simpa using hBmem i' j
      · simp [hi]
  rw [hspan]
  refine ⟨inferInstance, inferInstance, ?_⟩
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ _ (ZSpan.isAddFundamentalDomain (Pi.basis B) _)]
  have hfd : ZSpan.fundamentalDomain (Pi.basis B) = Set.univ.pi fun i => ZSpan.fundamentalDomain (B i) := by
    ext x
    simp [ZSpan.mem_fundamentalDomain, Pi.basis_repr, Sigma.forall]
  rw [hfd, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← hc i, ZLattice.covolume_eq_measure_fundamentalDomain _ _
    (ZLattice.isAddFundamentalDomain (Module.Free.chooseBasis ℤ (L i)) (μ i)), measureReal_def]

theorem measurePreserving_of_sum_sq {κ σ : Type} [Fintype κ] [Fintype σ]
    (e : (κ → ℂ) ≃L[ℝ] (σ → ℂ)) (he : ∀ z, ∑ j, ‖e z j‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) :
    MeasurePreserving e volume volume := by
  let T : EuclideanSpace ℂ κ ≃L[ℝ] (κ → ℂ) := ((EuclideanSpace.equiv κ ℂ).toLinearEquiv.restrictScalars ℝ).toContinuousLinearEquiv
  have hnorm : ∀ v : EuclideanSpace ℂ κ, ‖v‖ ^ 2 = ∑ i, ‖T v i‖ ^ 2 := fun v => by
    rw [EuclideanSpace.norm_sq_eq]; rfl
  have hT : MeasurePreserving T volume volume :=
    GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords _ κ T hnorm
  have hTe : MeasurePreserving (T.trans e) volume volume :=
    GlobalTheory.measurePreserving_of_norm_sq_eq_sum_complex_coords _ σ (T.trans e) fun v => by
      rw [hnorm v, ContinuousLinearEquiv.trans_apply, he]
  have hTs := MeasurePreserving.symm T.toHomeomorph.toMeasurableEquiv hT
  have hfun : (⇑e) = (T.trans e) ∘ T.toHomeomorph.toMeasurableEquiv.symm := by
    funext z
    simp
  rw [hfun]
  exact hTe.comp hTs

private theorem measurePreserving_piCurry_complex {I : Type} [Fintype I] {K : I → Type} [∀ i, Fintype (K i)] :
    MeasurePreserving (MeasurableEquiv.piCurry fun (i : I) (_ : K i) => ℂ) volume volume := by
  refine ⟨(MeasurableEquiv.piCurry _).measurable, ?_⟩
  symm
  show Measure.pi (fun i : I => Measure.pi fun _ : K i => (volume : Measure ℂ)) = _
  refine Measure.pi_eq_generateFrom
    (C := fun i => Set.pi Set.univ '' Set.pi Set.univ fun _ : K i => {s : Set ℂ | MeasurableSet s})
    (fun i => generateFrom_pi) (fun i => isPiSystem_pi)
    (fun i => Measure.FiniteSpanningSetsIn.pi fun _ => (volume : Measure ℂ).toFiniteSpanningSetsIn) ?_
  intro s hs
  choose t ht hst using hs
  obtain rfl : s = fun i => Set.univ.pi (t i) := funext fun i => (hst i).symm
  rw [MeasurableEquiv.map_apply]
  have hpre : (MeasurableEquiv.piCurry fun (i : I) (_ : K i) => ℂ) ⁻¹'
      Set.univ.pi (fun i => Set.univ.pi (t i)) = Set.univ.pi fun p : (Σ i, K i) => t p.1 p.2 := by
    ext f
    simp [MeasurableEquiv.coe_piCurry, Sigma.forall]
    exact Iff.rfl
  rw [hpre, volume_pi, Measure.pi_pi, Fintype.prod_sigma]
  simp only [Measure.pi_pi]

attribute [local instance] haar_two haar_three

theorem covolume_pi_unitary : ∀ (ι κ β : Type) [Fintype ι] [Fintype κ] [Fintype β] (r s : β → ℕ) (Φ : ι → ((κ → ℂ) ≃ₗ[ℂ] (∀ b : β, Fin (r b) → Fin (s b) → ℂ))), (∀ v z, ∑ b, ∑ p, ∑ q, ‖Φ v z b p q‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) → ∀ (M : ∀ b : β, Submodule ℤ (ι → Fin (r b) → Fin (s b) → ℂ)), (∀ b, ∃ _ : DiscreteTopology (M b), IsZLattice ℝ (M b)) → ∀ L : Submodule ℤ (ι → κ → ℂ), (∀ z, z ∈ L ↔ ∀ b, (fun v => Φ v (z v) b) ∈ M b) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = ∏ b, ZLattice.covolume (M b) volume := by
  intro ι κ β _ _ _ r s Φ hΦ M hM L hL
  classical
  let Ψ : (ι → κ → ℂ) ≃ₗ[ℂ] (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ) :=
    { toFun := fun z b v => Φ v (z v) b
      invFun := fun w v => (Φ v).symm fun b => w b v
      map_add' := fun x y => by funext b v; simp
      map_smul' := fun c x => by funext b v; simp
      left_inv := fun z => by funext v; simp
      right_inv := fun w => by funext b v; simp }
  let F : ((Σ b : β, Σ _ : ι, Σ _ : Fin (r b), Fin (s b)) → ℂ) ≃ₗ[ℂ]
      (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ) :=
    { toFun := fun w b v p q => w ⟨b, v, p, q⟩
      invFun := fun u x => u x.1 x.2.1 x.2.2.1 x.2.2.2
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  let G := LinearEquiv.piCurry ℂ fun (_ : ι) (_ : κ) => ℂ
  let E := G.trans (Ψ.trans F.symm)
  have hE : MeasurePreserving (E.restrictScalars ℝ).toContinuousLinearEquiv volume volume := by
    apply measurePreserving_of_sum_sq
    intro z
    have hz : ∀ j : (Σ b : β, Σ _ : ι, Σ _ : Fin (r b), Fin (s b)),
        (E.restrictScalars ℝ).toContinuousLinearEquiv z j =
          Φ j.2.1 (fun k => z ⟨j.2.1, k⟩) j.1 j.2.2.1 j.2.2.2 := fun j => rfl
    simp only [hz, Fintype.sum_sigma]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun v _ => hΦ v _
  have hG : MeasurePreserving (MeasurableEquiv.piCurry fun (_ : ι) (_ : κ) => ℂ) volume volume :=
    measurePreserving_piCurry_complex
  have hF : MeasurePreserving F volume volume := by
    have h := (volume_preserving_pi fun b => volume_preserving_pi fun (_ : ι) =>
        measurePreserving_piCurry_complex (I := Fin (r b)) (K := fun _ => Fin (s b))).comp
      ((volume_preserving_pi fun b =>
        measurePreserving_piCurry_complex (I := ι) (K := fun _ => Σ _ : Fin (r b), Fin (s b))).comp
        (measurePreserving_piCurry_complex (I := β) (K := fun b => Σ _ : ι, Σ _ : Fin (r b), Fin (s b))))
    exact h
  have hΨ : MeasurePreserving (Ψ.restrictScalars ℝ).toContinuousLinearEquiv volume volume := by
    have h := hF.comp (hE.comp (MeasurePreserving.symm _ hG))
    convert h using 1
    funext z
    rfl
  have := haar_two ι κ
  have hB3 : ∀ b, (volume : Measure (ι → Fin (r b) → Fin (s b) → ℂ)).IsAddHaarMeasure :=
    fun b => haar_three ι _ _
  have : (volume : Measure (∀ b : β, ι → Fin (r b) → Fin (s b) → ℂ)).IsAddHaarMeasure := by
    rw [← hΨ.map_eq]; infer_instance
  show HasCov volume L _
  refine HasCov.of_measurePreserving (Ψ.restrictScalars ℝ).toContinuousLinearEquiv hΨ
    (L' := Submodule.pi Set.univ M) ?_ ?_
  · intro z
    rw [hL, Submodule.mem_pi]
    simp only [Set.mem_univ, true_implies]
    exact Iff.rfl
  · exact hasCov_pi (μ := fun _ => volume) fun b => by
      obtain ⟨hd, hz⟩ := hM b
      exact ⟨hd, hz, rfl⟩

end GlobalTheory.CovPi
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumePiLatticeUnitaryCoordinatesStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.covolume_pi_lattice_unitary_coordinates : ∀ (ι κ β : Type) [Fintype ι] [Fintype κ] [Fintype β] (r s : β → ℕ) (Φ : ι → ((κ → ℂ) ≃ₗ[ℂ] (∀ b : β, Fin (r b) → Fin (s b) → ℂ))), (∀ v z, ∑ b, ∑ p, ∑ q, ‖Φ v z b p q‖ ^ 2 = ∑ i, ‖z i‖ ^ 2) → ∀ (M : ∀ b : β, Submodule ℤ (ι → Fin (r b) → Fin (s b) → ℂ)), (∀ b, ∃ _ : DiscreteTopology (M b), IsZLattice ℝ (M b)) → ∀ L : Submodule ℤ (ι → κ → ℂ), (∀ z, z ∈ L ↔ ∀ b, (fun v => Φ v (z v) b) ∈ M b) → ∃ _ : DiscreteTopology L, IsZLattice ℝ L ∧ ZLattice.covolume L volume = ∏ b, ZLattice.covolume (M b) volume := by
  first | exact @GlobalTheory.CovPi.covolume_pi_unitary | exact GlobalTheory.CovPi.covolume_pi_unitary | (intros; apply GlobalTheory.CovPi.covolume_pi_unitary <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagAtComplexEmbedding
section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MainTheorem
namespace GlobalTheory.DenominatorTheorem

open NumberField

theorem main_theorem : ∀ {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (G : Submodule (NumberField.RingOfIntegers E) (Fin n → E)),
    Submodule.span E (↑G : Set (Fin n → E)) = ⊤ → ∀ (y : Fin n → E),
    ∃ (c : NumberField.RingOfIntegers E), c ≠ (0 : NumberField.RingOfIntegers E) ∧ c • y ∈ G := by
  intro E _ _ n G hG y
  have hy : y ∈ Submodule.span E (G : Set (Fin n → E)) := hG ▸ Submodule.mem_top
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simpa using G.zero_mem⟩
  | add x z _ _ hx hz =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨d, hd, hdz⟩ := hz
    refine ⟨c * d, mul_ne_zero hc hd, ?_⟩
    rw [smul_add]
    refine G.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact G.smul_mem d hcx
    · rw [mul_smul]; exact G.smul_mem c hdz
  | smul a x _ hx =>
    obtain ⟨c, hc, hcx⟩ := hx
    obtain ⟨⟨p, q⟩, hpq⟩ := IsLocalization.surj (nonZeroDivisors (RingOfIntegers E)) a
    simp only at hpq
    refine ⟨(q : RingOfIntegers E) * c, mul_ne_zero (nonZeroDivisors.ne_zero q.2) hc, ?_⟩
    have key : ((q : RingOfIntegers E) * c) • (a • x) = p • (c • x) := by
      rw [← algebraMap_smul E ((q : RingOfIntegers E) * c) (a • x), smul_smul,
        ← algebraMap_smul E p (c • x), ← algebraMap_smul E c x, smul_smul, map_mul,
        mul_comm (algebraMap _ E (q : RingOfIntegers E)), mul_assoc, mul_comm _ a, hpq, mul_comm]
    rw [key]
    exact G.smul_mem p hcx

end GlobalTheory.DenominatorTheorem
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagAtComplexEmbedding
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.LocDual

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

theorem exists_smul_mem (G : Submodule (𝓞 E) (Fin n → E))
    (h : Submodule.span E (G : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ c : 𝓞 E, c ≠ 0 ∧ c • y ∈ G := by
  first
  | exact @_root_.GlobalTheory.DenominatorTheorem.main_theorem
  | exact _root_.GlobalTheory.DenominatorTheorem.main_theorem
  | (apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)
  | (intros; apply _root_.GlobalTheory.DenominatorTheorem.main_theorem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.DenominatorTheorem.main_theorem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.DenominatorTheorem.main_theorem ..)

theorem mem_locFlag_of_smul (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ)
    (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (b : ℕ) {c : 𝓞 E} (hc : c ≠ 0) {y : Fin n → E}
    (hy : c • y ∈ F b) : (P⁻¹ *ᵥ fun l => φ (y l)) ∈ locFlag φ P F b := by
  have hc1 : φ (algebraMap (𝓞 E) E c) ≠ 0 := by simpa using hc
  have e : (fun l => φ (y l)) = (φ (algebraMap (𝓞 E) E c))⁻¹ • fun l => φ ((c • y) l) := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul, Algebra.algebraMap_self, RingHom.id_apply]
    field_simp
  rw [e, Matrix.mulVec_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hy, rfl⟩)

omit [NumberField E] in
theorem mulVec_mem_of_span (φ : E →+* ℂ) (Q : Matrix (Fin n) (Fin n) ℂ) (S : Set (Fin n → E))
    (W : Submodule ℂ (Fin n → ℂ)) (h : ∀ y ∈ S, (Q *ᵥ fun l => φ (y l)) ∈ W) {u : Fin n → ℂ}
    (hu : u ∈ Submodule.span ℂ ((fun w : Fin n → E => fun i => φ (w i)) '' S)) : Q *ᵥ u ∈ W := by
  induction hu using Submodule.span_induction with
  | mem x hx => obtain ⟨y, hy, rfl⟩ := hx; exact h y hy
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact add_mem hx hy
  | smul c x _ hx => rw [Matrix.mulVec_smul]; exact W.smul_mem _ hx

theorem form_frame {P K M : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (h : Pᴴ * K * P = M)
    (u v : Fin n → ℂ) : star (P⁻¹ *ᵥ u) ⬝ᵥ (M *ᵥ v) = star u ⬝ᵥ (K *ᵥ (P *ᵥ v)) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have e : (P⁻¹)ᴴ * Pᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, ← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    ← Matrix.mul_assoc, ← Matrix.mul_assoc, e, Matrix.one_mul]

omit [NumberField E] in
theorem form_emb [StarRing E] (φ : E →+* ℂ) (hφ : ∀ x, φ (star x) = starRingEnd ℂ (φ x))
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    star (fun l => φ (x l)) ⬝ᵥ (J.map φ *ᵥ fun l => φ (y l)) = φ (star x ⬝ᵥ (J *ᵥ y)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp [dotProduct, Matrix.mulVec, map_sum, map_mul, hφ]

theorem locDual : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n m : ℕ) (J : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (F : ℕ → Submodule (𝓞 E) (Fin n → E)), (∀ x, φ (star x) = starRingEnd ℂ (φ x)) → IsUnit P → Pᴴ * J.map φ * P = Formalism.REAL.Jm ε → IsDualFlag J F m → Submodule.span E (F m : Set (Fin n → E)) = ⊤ → IsDualFlag (Formalism.REAL.Jm ε) (locFlag φ P F) m ∧ locFlag φ P F m = ⊤ := by
  intro E _ _ _ n m J φ P ε F hφ hP hJ hF hsp
  classical
  obtain ⟨hmono, h0, hm, hd⟩ := hF
  have hdet : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have hinv : ∀ z : Fin n → ℂ, P⁻¹ *ᵥ (P *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]
  have hinv' : ∀ z : Fin n → ℂ, P *ᵥ (P⁻¹ *ᵥ z) = z := fun z => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]
  have htop : locFlag φ P F m = ⊤ := by
    refine eq_top_iff.2 fun z _ => ?_
    rw [← hinv z]
    refine mulVec_mem_of_span φ _ _ _ ?_
      (GlobalTheory.PerpBaseChange.mem_span_of_forms φ ∅ (P *ᵥ z) (by simp))
    intro y _
    obtain ⟨c, hc, hy⟩ := exists_smul_mem _ hsp y
    exact mem_locFlag_of_smul φ P F m hc hy
  refine ⟨⟨?_, ?_, ?_, ?_⟩, htop⟩
  · intro a b hab
    exact Submodule.span_mono (Set.image_mono (hmono hab))
  · unfold locFlag
    rw [Submodule.span_eq_bot]
    rintro _ ⟨y, hy, rfl⟩
    rw [h0] at hy
    have : y = 0 := by simpa using hy
    subst this
    have e : (fun l => φ ((0 : Fin n → E) l)) = 0 := by funext l; simp
    simp only [e, Matrix.mulVec_zero]
  · intro b hb
    unfold locFlag
    rw [hm b hb]
  · intro b hb z
    constructor
    · intro hz
      refine ⟨by rw [htop]; trivial, fun x hx => ?_⟩
      induction hz using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy => rw [Matrix.mulVec_add, dotProduct_add, hx, hy, add_zero]
      | smul c x _ hx => rw [Matrix.mulVec_smul, dotProduct_smul, hx, smul_zero]
      | mem z hz =>
        obtain ⟨y, hy, rfl⟩ := hz
        induction hx using Submodule.span_induction with
        | zero => simp
        | add a b _ _ ha hb => rw [star_add, add_dotProduct, ha, hb, add_zero]
        | smul c a _ ha => rw [star_smul, smul_dotProduct, ha, smul_zero]
        | mem a ha =>
          obtain ⟨v, hv, rfl⟩ := ha
          rw [form_frame hP hJ, hinv', form_emb φ hφ, ((hd b hb y).1 hy).2 v hv, map_zero]
    · rintro ⟨-, hz⟩
      rw [← hinv z]
      let f : (Fin n → E) → Module.Dual E (Fin n → E) := fun x =>
        { toFun := fun y => star x ⬝ᵥ (J *ᵥ y)
          map_add' := fun y y' => by rw [Matrix.mulVec_add, dotProduct_add]
          map_smul' := fun c y => by rw [Matrix.mulVec_smul, dotProduct_smul]; rfl }
      have hf : ∀ x y, f x y = star x ⬝ᵥ (J *ᵥ y) := fun _ _ => rfl
      refine mulVec_mem_of_span φ _ _ _ ?_
        (GlobalTheory.PerpBaseChange.mem_span_of_forms φ (f '' (F b : Set _)) (P *ᵥ z) ?_)
      · intro y hy
        obtain ⟨c, hc, hcy⟩ := exists_smul_mem _ hsp y
        refine mem_locFlag_of_smul φ P F _ hc ((hd b hb _).2 ⟨hcy, fun x hx => ?_⟩)
        have h1 : star x ⬝ᵥ (J *ᵥ y) = 0 := hy (f x) ⟨x, hx, rfl⟩
        rw [Matrix.mulVec_smul, dotProduct_smul, h1, smul_zero]
      · rintro _ ⟨x, hx, rfl⟩
        have h1 := hz _ (Submodule.subset_span ⟨x, hx, rfl⟩)
        rw [form_frame hP hJ] at h1
        rw [← h1]
        generalize P *ᵥ z = u
        simp only [hf, Matrix.mulVec_single_one]
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [dotProduct, Matrix.mulVec, map_sum, map_mul, hφ, Finset.sum_mul, Finset.mul_sum,
          Pi.star_apply, Matrix.map_apply, Matrix.col_apply, mul_assoc]
        rw [Finset.sum_comm]
        rfl

end GlobalTheory.LocDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualHermitianFlagAtComplexEmbeddingStatement
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDual_hermitianFlag_at_complex_embedding : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n m : ℕ) (J : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ) (ε : Fin n → Bool) (F : ℕ → Submodule (𝓞 E) (Fin n → E)), (∀ x, φ (star x) = starRingEnd ℂ (φ x)) → IsUnit P → Pᴴ * J.map φ * P = Formalism.REAL.Jm ε → IsDualFlag J F m → Submodule.span E (F m : Set (Fin n → E)) = ⊤ → IsDualFlag (Formalism.REAL.Jm ε) (locFlag φ P F) m ∧ locFlag φ P F m = ⊤ := by
  first | exact @GlobalTheory.LocDual.locDual | exact GlobalTheory.LocDual.locDual | (intros; apply GlobalTheory.LocDual.locDual <;> assumption)
end
end
