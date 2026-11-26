module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsShortVectorUnimodularHermitianLatticeRankT

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImEmbHermSelf
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

namespace GlobalTheory.OrthoFrame

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (u : Fin r → Fin r → E) : Frame Ψ r :=
  fun τ k a => τ.1 (u a k)

theorem col_frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (u : Fin r → Fin r → E) (τ : Ψ) (a : Fin r) :
    col (mat (frm Ψ u) τ) a = Data.emb τ.1 (u a) := rfl

theorem emb_cc (τ : E →+* ℂ) (x : E) : τ (cc x) = conj (τ x) :=
  IsCMField.complexEmbedding_complexConj E τ x

theorem hermC_emb {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermC τ G (Data.emb τ x) (Data.emb τ y) = τ (herm G x y) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [hermC, herm, Data.emb, map_sum, map_mul, emb_cc]

theorem im_emb_herm_self {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (x : Fin r → E) : (τ (herm G x x)).im = 0 := by
  have h2 : conj (τ (herm G x x)) = τ (herm G x x) := by
    rw [← emb_cc, HermitianTraceFormVanishing.herm_conj G hG x x]
  exact Complex.conj_eq_iff_im.1 h2

theorem dmin_frm {r : ℕ} (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (u : Fin r → Fin r → E) (ho : ∀ j k, j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) (i : Fin (r + 1)) :
    dmin G (frm Ψ u) τ i = ∏ k : Fin i, τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
      (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))) := by
  unfold dmin lminor
  have : (gram τ.1 G (mat (frm Ψ u) τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = Matrix.diagonal (fun k => τ.1 (herm G
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))) := by
    ext a b
    simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, col_frm, hermC_emb, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · rw [ho _ _ (fun e => h (Fin.castLE_injective _ e)), map_zero]
  rw [this, Matrix.det_diagonal]

theorem psgn_mul_dmin {r : ℕ} (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (hG : ∀ a b, cc (G a b) = G b a) (p0 : ℕ)
    (u : Fin r → Fin r → E) (ho : ∀ j k, j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) (i : Fin (r + 1)) :
    psgn p0 i * (dmin G (frm Ψ u) τ i).re = ∏ k : Fin i, (sgn p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) k : Fin r) *
      (τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))).re) := by
  have hr : ∀ w : Fin r → E, τ.1 (herm G w w) = ((τ.1 (herm G w w)).re : ℂ) := fun w =>
    Complex.ext (by simp) (by simp [im_emb_herm_self τ.1 G hG w])
  rw [dmin_frm Ψ G u ho τ i, Finset.prod_mul_distrib, psgn, ← Fin.prod_univ_eq_prod_range]
  congr 1
  rw [Finset.prod_congr rfl (fun k _ => hr _), ← Complex.ofReal_prod, Complex.ofReal_re]

theorem prod_succ {r : ℕ} (f : Fin r → ℝ) (j : Fin r) :
    ∏ k : Fin (j.succ : ℕ), f (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) k) =
      (∏ k : Fin (j.castSucc : ℕ), f (Fin.castLE (Nat.le_of_lt_succ j.castSucc.isLt) k)) * f j := by
  change ∏ k : Fin ((j : ℕ) + 1), f (Fin.castLE _ k) = (∏ k : Fin (j : ℕ), f (Fin.castLE _ k)) * f j
  rw [Fin.prod_univ_castSucc]
  rfl

theorem sign_of_mem {r : ℕ} (X : Data E r) (u : Fin r → Fin r → E)
    (ho : ∀ j k, j ≠ k → herm X.Gm (u j) (u k) = 0) (hu : frm X.Ψ u ∈ X.dom) (τ : X.Ψ) (j : Fin r) :
    0 < sgn X.p0 j * (τ.1 (herm X.Gm (u j) (u j))).re := by
  have h1 := (hu τ).2 j.succ
  have h0 := (hu τ).2 j.castSucc
  rw [psgn_mul_dmin X.Ψ X.Gm X.Gm_herm X.p0 u ho τ] at h1 h0
  rw [prod_succ (fun k => sgn X.p0 k * (τ.1 (herm X.Gm (u k) (u k))).re)] at h1
  exact (pos_iff_pos_of_mul_pos h1).1 h0

theorem mem_of_sign {r : ℕ} (X : Data E r) (u : Fin r → Fin r → E)
    (ho : ∀ j k, j ≠ k → herm X.Gm (u j) (u k) = 0) (hd : (Matrix.of u).det ≠ 0)
    (hs : ∀ τ : X.Ψ, ∀ j : Fin r, 0 < sgn X.p0 j * (τ.1 (herm X.Gm (u j) (u j))).re) : frm X.Ψ u ∈ X.dom := by
  intro τ
  refine ⟨?_, fun i => ?_⟩
  · have : mat (frm X.Ψ u) τ = τ.1.mapMatrix (Matrix.of u).transpose := by
      ext k a; rfl
    rw [this, ← RingHom.map_det, Matrix.det_transpose]
    exact (map_ne_zero τ.1).2 hd
  · rw [psgn_mul_dmin X.Ψ X.Gm X.Gm_herm X.p0 u ho τ]
    exact Finset.prod_pos fun k _ => hs τ _

end

end GlobalTheory.OrthoFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmLatticeDataUnfoldingSignatureOneZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmLatticeDataUnfoldingSignatureOneZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT

namespace GlobalTheory.LamT.CMRankOne

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem perFr_pure_of_data (Y : FD.Data E r) (x : FD.Frame Y.Ψ r) (hx : x ∈ Y.dom) (lam : Fin r → Fin r → E)
    (ho : ∀ j k' : Fin r, (j : ℕ) < Y.p0 → Y.p0 ≤ (k' : ℕ) → FD.herm Y.Gm (lam j) (lam k') = 0)
    (hsp : ∀ τ : Y.Ψ, Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.col (FD.mat x τ) (Fin.castLE Y.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.Data.emb τ.1 (lam (Fin.castLE Y.p0_le a))))
    (a : E) (j : Fin r) (τ : E →+* ℂ) (i : ℕ) :
    ((j : ℕ) < Y.p0 → τ ∈ Y.Ψ → perFr Y x (a • lam j) τ i = 0) ∧
      (Y.p0 ≤ (j : ℕ) → τ ∉ Y.Ψ → i < Y.p0 → perFr Y x (a • lam j) τ i = 0) := by
  refine ⟨fun hj hτ => ?_, fun hj hτ hi => ?_⟩
  · unfold perFr
    rw [dite_eq_left hτ]
    split_ifs with h
    · refine GlobalTheory.PurePer.inv_mulVec_eq_zero Y.p0_le _ (hx ⟨τ, hτ⟩).1 ?_ _ (by simp)
      rw [hsp ⟨τ, hτ⟩, GlobalTheory.PurePer.emb_smul']
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨j, hj⟩, rfl⟩)
    · rfl
  · unfold perFr
    rw [dite_eq_right hτ]
    split_ifs with h' h
    · have hm : FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨Y.p0 - 1 - i, h⟩ ∈
          Submodule.span ℂ (Set.range fun a : Fin Y.p0 =>
            FD.Data.emb (conjEmb τ) (lam (Fin.castLE Y.p0_le a))) := by
        have := hsp ⟨conjEmb τ, h'⟩
        simp only at this
        rw [← this]
        exact Submodule.subset_span ⟨⟨Y.p0 - 1 - i, by omega⟩, rfl⟩
      rw [GlobalTheory.PurePer.emb_smul', FD.hermC_smul_right]
      refine mul_eq_zero_of_right _ ?_
      generalize FD.col (FD.mat x ⟨conjEmb τ, h'⟩) ⟨Y.p0 - 1 - i, h⟩ = w at hm
      induction hm using Submodule.span_induction with
      | mem w hw =>
        obtain ⟨k, rfl⟩ := hw
        rw [FD.hermC_emb, ho _ j (by simpa using k.isLt) hj, map_zero]
      | zero => exact FD.hermC_zero_left _ _ _
      | add a b _ _ ha hb => rw [FD.hermC_add_left, ha, hb, add_zero]
      | smul c a _ ha => rw [FD.hermC_smul_left, ha, mul_zero]
    · rfl
    · rfl

theorem exists_cmLat_rankOne (H : Host E) {p q : ℕ} (Y : FD.Data E r) (x₀ : Y.dom)
    (hr : 0 < r) (hrk : r = p + q) (hp0 : Y.p0 = q) (hΨ : ∀ τ : E →+* ℂ, τ ∈ Y.Ψ ↔ τ (H.rt : E) = H.rt0)
    (D : Datum H) {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (φ : D.La ≃ₗ[𝓞 E] Y.Λ)
    (isom : ∀ a b, ((D.EF a b : ℤ) : ℚ) = Algebra.trace ℚ E (-Y.ξ0 * FD.herm Y.Gm (φ a : Fin r → E) (φ b)))
    (ix : Fin g → ℕ) (hix : ∀ j, ty j (H.rt : E) ≠ H.rt0 → ix j < q)
    (pm : ∀ a j, Pe a j = perFr Y x₀.1 (φ a : Fin r → E) (ty j) (ix j))
    (D₁ : Datum H) (hp1 : D₁.p = 1) (hq1 : D₁.q = 0)
    (lam : Fin r → Fin r → E) (hL : ∀ j, lam j ∈ Y.Λ) (hli : LinearIndependent E lam)
    (ho : ∀ j k' : Fin r, (j : ℕ) < Y.p0 → Y.p0 ≤ (k' : ℕ) → FD.herm Y.Gm (lam j) (lam k') = 0)
    (hsp : ∀ τ : Y.Ψ, Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.col (FD.mat x₀.1 τ) (Fin.castLE Y.p0_le a)) =
      Submodule.span ℂ (Set.range fun a : Fin Y.p0 => FD.Data.emb τ.1 (lam (Fin.castLE Y.p0_le a)))) :
    Nonempty (CMLat hP p q) := by
  classical
  have hpure := perFr_pure_of_data Y x₀.1 x₀.2 lam ho hsp
  obtain ⟨G1, io, hioinj, -, -, hG1det, hEF1⟩ :=
    GlobalTheory.exists_herm_coord_of_datum E H D₁ Y.ξ0 Y.ξ0_im Y.ξ0_ne 1 (by omega)
  let lv : D₁.La →ₗ[𝓞 E] E := (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 1 => E) 0) ∘ₗ io
  have hlv : ∀ x, lv x = io x 0 := fun x => rfl
  have hG0 : G1 0 0 ≠ 0 := by simpa [Matrix.det_unique] using hG1det
  have hform1 : ∀ x y, ((D₁.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (Y.ξ0 * G1 0 0 * lv x * FD.cc (lv y)) := by
    intro x y
    rw [hEF1]
    congr 1
    simp [FD.herm, hlv]
    ring
  have h1ne : (1 : Submodule (𝓞 E) E) ≠ ⊥ :=
    (Submodule.ne_bot_iff _).2 ⟨1, Submodule.mem_one.2 ⟨1, map_one _⟩, one_ne_zero⟩

  obtain ⟨S, hS⟩ := D₁.fin.fg_top
  obtain ⟨N₀, hN₀, hc₀⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (1 : Submodule (𝓞 E) E) h1ne (fun s : S => lv s)
  let lv0 : D₁.La →ₗ[𝓞 E] E := (N₀ : 𝓞 E) • lv
  have hlv0 : ∀ x, lv0 x = (N₀ : E) * lv x := fun x => by
    simp [lv0, Algebra.smul_def]
  have hlv01 : ∀ x, lv0 x ∈ (1 : Submodule (𝓞 E) E) := by
    have : (⊤ : Submodule (𝓞 E) D₁.La) ≤ (1 : Submodule (𝓞 E) E).comap lv0 := by
      rw [← hS, Submodule.span_le]
      intro s hs
      change lv0 s ∈ (1 : Submodule (𝓞 E) E)
      rw [hlv0]
      exact hc₀ ⟨s, hs⟩
    exact fun x => this Submodule.mem_top

  obtain ⟨M, hM, hcM⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (1 : Submodule (𝓞 E) E) h1ne
    (fun i : Fin r => (N₀ : E) ^ 2 * FD.herm Y.Gm (lam i) (lam i) / G1 0 0)
  choose t ht using fun i => Submodule.mem_one.1 (hcM i)
  let lv' : D₁.La →ₗ[𝓞 E] E := (M : 𝓞 E) • lv0
  have hlv' : ∀ x, lv' x = ((N₀ * M : ℕ) : E) * lv x := fun x => by
    simp only [lv', LinearMap.smul_apply, Algebra.smul_def, hlv0]
    push_cast
    ring
  have hlv'1 : ∀ x, lv' x ∈ (1 : Submodule (𝓞 E) E) := fun x =>
    Submodule.smul_mem _ (M : 𝓞 E) (hlv01 x)
  have hmem : ∀ x j, lv' x • lam j ∈ Y.Λ := fun x j => by
    obtain ⟨u, hu⟩ := Submodule.mem_one.1 (hlv'1 x)
    rw [← hu, algebraMap_smul]
    exact Y.Λ.smul_mem u (hL j)
  let m : Fin r → D₁.La →ₗ[𝓞 E] Y.Λ := fun j =>
    { toFun := fun a => ⟨_, hmem a j⟩
      map_add' := fun a b => Subtype.ext (by simp [add_smul])
      map_smul' := fun c a => Subtype.ext (by simp [smul_assoc]) }
  let Dp : Bool → Datum H := fun b => match b with
    | true => D₁
    | false => oppDatum D₁
  let e : ∀ b, (Dp b).La ≃ₗ[𝓞 E] D₁.La := fun b => match b with
    | true => LinearEquiv.refl _ _
    | false => LinearEquiv.refl _ _
  let σ : Fin p ⊕ Fin q ≃ Fin r := (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (by omega)))
  have hσl : ∀ j, q ≤ (σ (.inl j) : ℕ) := fun j => by simp [σ]
  have hσr : ∀ j, (σ (.inr j) : ℕ) < q := fun j => by simp [σ]
  let f : ∀ j : Fin p ⊕ Fin q, (Dp j.isLeft).La →ₗ[𝓞 E] D.La := fun j =>
    φ.symm.toLinearMap ∘ₗ m (σ j) ∘ₗ (e _).toLinearMap
  have hf : ∀ j a, (φ (f j a) : Fin r → E) = lv' (e _ a) • lam (σ j) := fun j a => by
    simp [f, m]
  let hh : Fin p ⊕ Fin q → 𝓞 E :=
    Sum.elim (fun j => -((M : 𝓞 E) * t (σ (.inl j)))) (fun j => (M : 𝓞 E) * t (σ (.inr j)))
  have hhl : ∀ j, ((hh (.inl j) : 𝓞 E) : E) =
      -(((N₀ * M : ℕ) : E) ^ 2 * FD.herm Y.Gm (lam (σ (.inl j))) (lam (σ (.inl j))) / G1 0 0) := by
    intro j
    show ((-((M : 𝓞 E) * t (σ (.inl j))) : 𝓞 E) : E) = _
    rw [RingOfIntegers.coe_eq_algebraMap, map_neg, map_mul, ht, map_natCast]
    push_cast
    ring
  have hhr : ∀ j, ((hh (.inr j) : 𝓞 E) : E) =
      ((N₀ * M : ℕ) : E) ^ 2 * FD.herm Y.Gm (lam (σ (.inr j))) (lam (σ (.inr j))) / G1 0 0 := by
    intro j
    show ((((M : 𝓞 E) * t (σ (.inr j))) : 𝓞 E) : E) = _
    rw [RingOfIntegers.coe_eq_algebraMap, map_mul, ht, map_natCast]
    push_cast
    ring
  have hsq : ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := fun τ => by
    refine sq_eq_sq_iff_eq_or_eq_neg.1 ?_
    rw [← map_pow, HostModel.coe_sq_eq_neg H.rt_sq, H.sqrt_neg_disc_sq, map_neg, map_natCast]
  have h3 : ∀ (a b : E) (u : Fin r → E), FD.herm Y.Gm (a • u) (b • u) = a * FD.cc b * FD.herm Y.Gm u u :=
    fun a b u => by
      simp only [FD.herm, FD.cc, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hccN : ∀ n : ℕ, FD.cc (n : E) = n := fun n => by simp [FD.cc]
  have hlvs : ∀ (c : 𝓞 E) x, lv (c • x) = (c : E) * lv x := fun c x => by
    rw [map_smul, Algebra.smul_def]
  refine ⟨⟨Dp, ⟨hp1, hq1⟩, ⟨hq1, hp1⟩, f, ?_, hh, ?_, ?_⟩⟩
  · rintro (j | j) a k hk
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).2 (hp0 ▸ hσl j) (fun h => hk' ((hΨ _).1 h)) (hp0 ▸ hix k hk')
    · rw [pm, hf]
      have hk' : ty k (H.rt : E) ≠ -H.rt0 := by simpa using hk
      exact (hpure _ _ _ _).1 (hp0 ▸ hσr j) ((hΨ _).2 ((hsq _).resolve_right hk'))
  · rintro (j | j) a b
    · apply Int.cast_injective (α := ℚ)
      rw [isom, hf, hf]
      refine Eq.trans ?_ (hform1 (hh (.inl j) • a) b).symm
      erw [hlvs]
      congr 1
      change -Y.ξ0 * FD.herm Y.Gm (lv' a • lam (σ (.inl j))) (lv' b • lam (σ (.inl j))) = _
      rw [h3]
      erw [hlv' a, hlv' b]
      rw [hhl]
      simp only [FD.cc, map_mul, map_natCast]
      field_simp
    · apply Int.cast_injective (α := ℚ)
      rw [isom, hf, hf]
      refine Eq.trans ?_ (congrArg (fun z : ℚ => -z) (hform1 (hh (.inr j) • a) b)).symm |>.trans (by push_cast; rfl)
      erw [hlvs]
      rw [← map_neg]
      congr 1
      change -Y.ξ0 * FD.herm Y.Gm (lv' a • lam (σ (.inr j))) (lv' b • lam (σ (.inr j))) = _
      rw [h3]
      erw [hlv' a, hlv' b]
      rw [hhr]
      simp only [FD.cc, map_mul, map_natCast]
      field_simp
  · haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
    let B := basisOfLinearIndependentOfCardEqFinrank hli (by simp)
    have hB : ∀ j, B j = lam j := fun j => by simp [B]
    let Nm : Submodule (𝓞 E) D.La := LinearMap.range (∑ j, f j ∘ₗ LinearMap.proj j)
    have hN : ∀ a, a ∈ Nm ↔ ∃ x : ∀ j : Fin p ⊕ Fin q, (Dp j.isLeft).La, a = ∑ j, f j (x j) := fun a => by
      simp only [Nm, LinearMap.mem_range, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
      exact exists_congr fun _ => eq_comm
    have hnt : Nontrivial D₁.La :=
      Module.nontrivial_of_finrank_pos (R := 𝓞 E) (by rw [D₁.rank, hp1, hq1]; exact one_pos)
    obtain ⟨a₀, ha₀⟩ := exists_ne (0 : D₁.La)
    have hR : LinearMap.range lv' ≠ ⊥ := by
      refine (Submodule.ne_bot_iff _).2 ⟨lv' a₀, ⟨a₀, rfl⟩, ?_⟩
      rw [hlv']
      refine mul_ne_zero (by exact_mod_cast (Nat.mul_pos hN₀ hM).ne') fun h0 => ha₀ (hioinj ?_)
      funext i
      rw [Subsingleton.elim i 0, map_zero]
      exact h0
    obtain ⟨S', hS'⟩ := D.fin.fg_top
    obtain ⟨n, hn, hc⟩ := GlobalTheory.LamT.CMBasis.exists_nsmul_mem (LinearMap.range lv') hR
      (fun i : S' × Fin r => B.repr (φ i.1 : Fin r → E) i.2)
    choose y hy using fun i : S' × Fin r => LinearMap.mem_range.1 (hc i)
    refine ⟨n, hn, fun a => (hN _).1 ?_⟩
    have : (⊤ : Submodule (𝓞 E) D.La) ≤ Nm.comap (n • LinearMap.id) := by
      rw [← hS', Submodule.span_le]
      intro a ha
      refine (hN _).2 ⟨fun j => (e _).symm (y (⟨a, ha⟩, σ j)), φ.injective (Subtype.ext ?_)⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, AddSubmonoidClass.coe_finsetSum]
      simp only [hf, LinearEquiv.apply_symm_apply, hy]
      rw [Equiv.sum_comp σ (fun j => ((n : E) * B.repr (φ a : Fin r → E) j) • lam j)]
      simp only [mul_smul, ← Finset.smul_sum, ← hB, B.sum_repr]
      simp [Nat.cast_smul_eq_nsmul]
    exact this Submodule.mem_top

theorem exists_cmLat_unfAt_rankOne : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (r : ℕ) (U : Formalism.L2.Pj.Unf Xo c c.F.val.toRingHom r), Formalism.L2.Pj.IsUnf U → 0 < r → ∀ (D₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), D₁.p = 1 → D₁.q = 0 → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k x₀) (lam : Fin r → Fin r → E), (∀ j, lam j ∈ (U.X k).Λ) → LinearIndependent E lam → (∀ j k' : Fin r, (j : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (k' : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam k') = 0) → (∀ j : Fin r, (j : ℕ) < (U.X k).p0 → ∀ τ : (U.X k).Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re) → (∀ j : Fin r, (U.X k).p0 ≤ (j : ℕ) → ∀ τ : (U.X k).Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re < 0) → (∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀.1 τ) (Fin.castLE (U.X k).p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE (U.X k).p0_le a)))) → Nonempty (GlobalTheory.CM.CMLat W.per Dw.p Dw.q) := by
  intro E _ _ _ H Dw l Xo c r U hU hr D₁ hp1 hq1 k x₀ W lam hL hli ho _ _ hsp
  obtain ⟨h1, h2, -⟩ := hU
  refine exists_cmLat_rankOne H (U.X k) x₀ hr h1 (h2 k).1 (h2 k).2 _ W.per (W.φ k) (W.isom k)
    (fun j => (W.e j).2) (fun j hj => ?_) W.pm_eq D₁ hp1 hq1 lam hL hli ho hsp
  exact (W.e j).2.2.trans_eq (if_neg hj)

end GlobalTheory.LamT.CMRankOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmLatticeDataUnfoldingSignatureOneZeroStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmLattice_data_unfolding_signature_one_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H) (Xo : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Moduli Dw l) (c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l) (r : ℕ) (U : Formalism.L2.Pj.Unf Xo c c.F.val.toRingHom r), Formalism.L2.Pj.IsUnf U → 0 < r → ∀ (D₁ : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H), D₁.p = 1 → D₁.q = 0 → ∀ (k : U.Comp) (x₀ : (U.X k).dom) (W : ReciprocityTheory.ChartRestriction.G.PullbackSections.UnfAt U k x₀) (lam : Fin r → Fin r → E), (∀ j, lam j ∈ (U.X k).Λ) → LinearIndependent E lam → (∀ j k' : Fin r, (j : ℕ) < (U.X k).p0 → (U.X k).p0 ≤ (k' : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam k') = 0) → (∀ j : Fin r, (j : ℕ) < (U.X k).p0 → ∀ τ : (U.X k).Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re) → (∀ j : Fin r, (U.X k).p0 ≤ (j : ℕ) → ∀ τ : (U.X k).Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm (U.X k).Gm (lam j) (lam j))).re < 0) → (∀ τ : (U.X k).Ψ, Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x₀.1 τ) (Fin.castLE (U.X k).p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin (U.X k).p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE (U.X k).p0_le a)))) → Nonempty (GlobalTheory.CM.CMLat W.per Dw.p Dw.q) := by
  first | exact @GlobalTheory.LamT.CMRankOne.exists_cmLat_unfAt_rankOne | exact GlobalTheory.LamT.CMRankOne.exists_cmLat_unfAt_rankOne | (intros; apply GlobalTheory.LamT.CMRankOne.exists_cmLat_unfAt_rankOne <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalLatticeFrameFlagDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameMemFlagDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameMemFlagDomain
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.OrthoFrame

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem exists_approx_cmType (Ψ : Finset (E →+* ℂ))
    (hΨ : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) (w : Ψ → ℂ) {ε : ℝ}
    (hε : 0 < ε) : ∃ x : E, ∀ τ : Ψ, dist (w τ) (τ.1 x) < ε := by
  have hε2 : 0 < ε / 2 := half_pos hε
  choose z hz using fun τ : Ψ => Metric.denseRange_iff.1
    (GlobalTheory.ShortVec.denseRange_emb τ.1 (IsTotallyComplex.complexEmbedding_not_isReal τ.1)) (w τ) _ hε2
  obtain ⟨x, hx⟩ := GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt
    (v := fun τ : Ψ => (InfinitePlace.mk τ.1).1) (fun τ => InfinitePlace.isNontrivial _)
    (by
      intro σ τ hne h
      rcases InfinitePlace.mk_eq_iff.1 (InfinitePlace.eq_iff_isEquiv.2 h) with h1 | h1
      · exact hne (Subtype.ext h1)
      · exact (hΨ σ.1).1 σ.2 (h1 ▸ τ.2)) z hε2
  refine ⟨x, fun τ => ?_⟩
  have h1 : ‖τ.1 (z τ - x)‖ < ε / 2 := by
    rw [← InfinitePlace.apply]; exact hx τ
  rw [map_sub, ← dist_eq_norm] at h1
  have h2 := dist_triangle (w τ) (τ.1 (z τ)) (τ.1 x)
  have h3 := hz τ
  linarith

theorem dom_nonempty {r : ℕ} (X : Data E r) : X.dom.Nonempty := by
  choose P hP using X.signature
  refine ⟨fun τ k a => P τ k a, fun τ => ⟨(hP τ).1, fun i => ?_⟩⟩
  have h : dmin X.Gm (fun τ k a => P τ k a) τ i = ((psgn X.p0 i : ℝ) : ℂ) := by
    change lminor (gram τ.1 X.Gm (P τ)) i = _
    rw [(hP τ).2, lminor, Matrix.submatrix_diagonal _ _ (Fin.castLE_injective _),
      Matrix.det_diagonal, psgn, ← Fin.prod_univ_eq_prod_range, Complex.ofReal_prod]
    rfl
  rw [h, Complex.ofReal_re]
  refine mul_self_pos.2 (Finset.prod_ne_zero_iff.2 fun a _ => ?_)
  unfold sgn
  split_ifs <;> norm_num

theorem exists_frm_mem_dom : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r),
    ∃ u : Fin r → Fin r → E, GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom := by
  intro E _ _ _ r X
  obtain ⟨P, hP⟩ := dom_nonempty X
  obtain ⟨ε, hε, hb⟩ := Metric.isOpen_iff.1 (FourierCoefficientDomain.isOpen_dom X) P hP
  choose u hu using fun a k : Fin r =>
    exists_approx_cmType X.Ψ X.cmType (fun τ => P τ k a) hε
  refine ⟨u, hb ?_⟩
  rw [Metric.mem_ball, dist_comm, dist_pi_lt_iff hε]
  intro τ
  rw [dist_pi_lt_iff hε]
  intro k
  rw [dist_pi_lt_iff hε]
  intro a
  exact hu a k τ

end GlobalTheory.OrthoFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalFrameMemFlagDomainStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rational_frame_mem_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ u : Fin r → Fin r → E, GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom := by
  first | exact @GlobalTheory.OrthoFrame.exists_frm_mem_dom | exact GlobalTheory.OrthoFrame.exists_frm_mem_dom | (intros; apply GlobalTheory.OrthoFrame.exists_frm_mem_dom <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalRationalFrameFlagDomain
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalRationalFrameFlagDomain
open NumberField Complex ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

namespace GlobalTheory.OrthoFrame.GramSchmidt

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_sum_left (G : Matrix (Fin r) (Fin r) E) (s : Finset (Fin r)) (f : Fin r → E)
    (w : Fin r → Fin r → E) (y : Fin r → E) :
    herm G (∑ j ∈ s, f j • w j) y = ∑ j ∈ s, f j * herm G (w j) y := by
  induction s using Finset.induction_on with
  | empty => simp [herm]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, HermitianTraceFormVanishing.herm_add_left, HermitianTraceFormVanishing.herm_smul_left, ih]

theorem psi_nonempty (X : Data E r) : ∃ τ, τ ∈ X.Ψ := by
  let τ0 : E →+* ℂ := (IsAlgClosed.lift (R := ℚ) (M := ℂ) (S := E)).toRingHom
  by_cases h : τ0 ∈ X.Ψ
  · exact ⟨τ0, h⟩
  · exact ⟨_, not_not.mp (mt (X.cmType τ0).2 h)⟩

theorem dmin_frm_of_lt (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E)
    (u : Fin r → Fin r → E) (i : Fin (r + 1))
    (ho : ∀ j k : Fin r, (j : ℕ) < i → (k : ℕ) < i → j ≠ k → herm G (u j) (u k) = 0) (τ : Ψ) :
    dmin G (frm Ψ u) τ i = ∏ k : Fin i, τ.1 (herm G (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))
      (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k))) := by
  unfold dmin lminor
  have : (gram τ.1 G (mat (frm Ψ u) τ)).submatrix (Fin.castLE (Nat.le_of_lt_succ i.isLt))
      (Fin.castLE (Nat.le_of_lt_succ i.isLt)) = Matrix.diagonal (fun k => τ.1 (herm G
        (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)) (u (Fin.castLE (Nat.le_of_lt_succ i.isLt) k)))) := by
    ext a b
    simp only [Matrix.submatrix_apply, gram, Matrix.of_apply, col_frm, hermC_emb, Matrix.diagonal_apply]
    split_ifs with h
    · subst h; rfl
    · rw [ho _ _ (by rw [Fin.coe_castLE]; exact a.isLt) (by rw [Fin.coe_castLE]; exact b.isLt)
        (fun e => h (Fin.castLE_injective _ e)), map_zero]
  rw [this, Matrix.det_diagonal]

theorem herm_self_ne (X : Data E r) (v : Fin r → Fin r → E) (hv : frm X.Ψ v ∈ X.dom) (m : ℕ)
    (ho : ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0)
    (j : Fin r) (hj : (j : ℕ) < m) : herm X.Gm (v j) (v j) ≠ 0 := by
  obtain ⟨τ, hτ⟩ := psi_nonempty X
  have h1 := (hv ⟨τ, hτ⟩).2 j.succ
  have hd : dmin X.Gm (frm X.Ψ v) ⟨τ, hτ⟩ j.succ ≠ 0 := by
    intro h0
    rw [h0, Complex.zero_re, mul_zero] at h1
    exact lt_irrefl _ h1
  rw [dmin_frm_of_lt X.Ψ X.Gm v j.succ (fun a b ha hb hab => ho a b
    (by simp only [Fin.val_succ] at ha; omega) (by simp only [Fin.val_succ] at hb; omega) hab)] at hd
  have hf := Finset.prod_ne_zero_iff.mp hd ⟨j, by simp⟩ (Finset.mem_univ _)
  have he : (Fin.castLE (Nat.le_of_lt_succ j.succ.isLt) ⟨(j : ℕ), by simp⟩ : Fin r) = j := Fin.ext rfl
  rw [he] at hf
  intro h0
  exact hf (by rw [h0, map_zero])

def gsMat (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    Matrix (Fin r) (Fin r) E :=
  fun j a => (if j = a then 1 else 0) -
    (if a = m ∧ j < m then herm G (v m) (v j) / herm G (v j) (v j) else 0)

def gsStep (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    Fin r → Fin r → E :=
  fun a k => ∑ j, v j k * gsMat G v m j a

theorem gsStep_ne (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m a : Fin r)
    (h : a ≠ m) : gsStep G v m a = v a := by
  funext k
  simp [gsStep, gsMat, h]

theorem gsStep_self (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E) (m : Fin r) :
    gsStep G v m m = v m - ∑ j, (if j < m then herm G (v m) (v j) / herm G (v j) (v j) else 0) • v j := by
  funext k
  simp only [gsStep, gsMat, true_and, mul_sub, Finset.sum_sub_distrib, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> ring

theorem frm_gsStep (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E)
    (m : Fin r) : frm Ψ (gsStep G v m) = rmul (frm Ψ v) (fun τ j a => τ.1 (gsMat G v m j a)) := by
  funext τ k a
  set_option synthInstance.maxHeartbeats 100000 in
    simp [frm, rmul, mat, Matrix.mul_apply, gsStep, map_sum, map_mul]

theorem gsB_mem (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (v : Fin r → Fin r → E)
    (m : Fin r) : (fun (τ : Ψ) j a => τ.1 (gsMat G v m j a)) ∈ Bor Ψ r := by
  have hlow : ∀ a c : Fin r, c < a → gsMat G v m a c = 0 := by
    intro a c hca
    have h1 : a ≠ c := fun h => lt_irrefl _ (h ▸ hca)
    have h2 : ¬ (c = m ∧ a < m) := fun h => lt_asymm hca (h.1 ▸ h.2)
    simp [gsMat, h1, h2]
  intro τ
  refine ⟨?_, fun a c hca => by simp [hlow a c hca]⟩
  have ht : (mat (fun (τ : Ψ) j a => τ.1 (gsMat G v m j a)) τ).BlockTriangular id := by
    intro a c hca
    simp [mat, hlow a c hca]
  rw [Matrix.det_of_upperTriangular ht]
  refine Finset.prod_ne_zero_iff.2 fun a _ => ?_
  have hn : ¬ (a = m ∧ a < m) := by rintro ⟨rfl, h⟩; exact lt_irrefl _ h
  simp [mat, gsMat, hn]

theorem herm_gsStep_self (X : Data E r) (v : Fin r → Fin r → E) (hv : frm X.Ψ v ∈ X.dom) (m : Fin r)
    (ho : ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0)
    (k : Fin r) (hk : k < m) : herm X.Gm (gsStep X.Gm v m m) (v k) = 0 := by
  have hkm : (k : ℕ) < m := hk
  have hne := herm_self_ne X v hv m ho k hkm
  rw [gsStep_self, HermitianTraceFormVanishing.herm_sub_left, herm_sum_left,
    Finset.sum_eq_single k (fun i _ hik => ?_) (fun h => absurd (Finset.mem_univ k) h),
    if_pos hk, div_mul_cancel₀ _ hne, sub_self]
  split_ifs with him
  · rw [ho i k him hkm hik, mul_zero]
  · rw [zero_mul]

theorem exists_ortho_lt (X : Data E r) (u : Fin r → Fin r → E) (hu : frm X.Ψ u ∈ X.dom) :
    ∀ m ≤ r, ∃ v : Fin r → Fin r → E, frm X.Ψ v ∈ X.dom ∧
      ∀ j k : Fin r, (j : ℕ) < m → (k : ℕ) < m → j ≠ k → herm X.Gm (v j) (v k) = 0 := by
  intro m
  induction m with
  | zero => intro _; exact ⟨u, hu, fun j k hj => absurd hj (Nat.not_lt_zero _)⟩
  | succ m ih =>
    intro hm
    obtain ⟨v, hv, ho⟩ := ih (Nat.le_of_succ_le hm)
    let mf : Fin r := ⟨m, hm⟩
    refine ⟨gsStep X.Gm v mf, ?_, ?_⟩
    · rw [frm_gsStep]
      exact OrthogonalFrameDomain.rmul_mem_dom X hv (gsB_mem X.Ψ X.Gm v mf)
    · intro j k hj hk hjk
      by_cases hjm : j = mf
      · have hkm : k ≠ mf := fun h => hjk (hjm.trans h.symm)
        have hk' : k < mf := by
          rw [Fin.lt_iff_val_lt_val]
          have : (k : ℕ) ≠ m := fun h => hkm (Fin.ext h)
          show (k : ℕ) < m
          omega
        rw [hjm, gsStep_ne X.Gm v mf k hkm]
        exact herm_gsStep_self X v hv mf ho k hk'
      · by_cases hkm : k = mf
        · have hj' : j < mf := by
            rw [Fin.lt_iff_val_lt_val]
            have : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
            show (j : ℕ) < m
            omega
          rw [hkm, gsStep_ne X.Gm v mf j hjm, ← HermitianTraceFormVanishing.herm_conj X.Gm X.Gm_herm,
            herm_gsStep_self X v hv mf ho j hj', HermitianTraceFormVanishing.cc_zero]
        · rw [gsStep_ne X.Gm v mf j hjm, gsStep_ne X.Gm v mf k hkm]
          have hj' : (j : ℕ) ≠ m := fun h => hjm (Fin.ext h)
          have hk' : (k : ℕ) ≠ m := fun h => hkm (Fin.ext h)
          exact ho j k (by omega) (by omega) hjk

theorem exists_ortho_frm (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ)
    (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → Fin r → E) :
    GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom → ∃ v : Fin r → Fin r → E,
      (∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v k) = 0) ∧ GlobalTheory.OrthoFrame.frm X.Ψ v ∈ X.dom := by
  intro hu
  obtain ⟨v, hv, ho⟩ := exists_ortho_lt X u hu r le_rfl
  exact ⟨v, fun j k hjk => ho j k j.isLt k.isLt hjk, hv⟩

end

end GlobalTheory.OrthoFrame.GramSchmidt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalRationalFrameFlagDomainStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_rational_frame_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r) (u : Fin r → Fin r → E), GlobalTheory.OrthoFrame.frm X.Ψ u ∈ X.dom → ∃ v : Fin r → Fin r → E, (∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v k) = 0) ∧ GlobalTheory.OrthoFrame.frm X.Ψ v ∈ X.dom := by
  first | exact @GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm | exact GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm | (intros; apply GlobalTheory.OrthoFrame.GramSchmidt.exists_ortho_frm <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalLatticeFrameFlagDomain
open NumberField

namespace GlobalTheory.OrthoFrame

theorem exists_orthoFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ x ∈ X.dom, ∃ lam : Fin r → Fin r → E, (∀ j, lam j ∈ X.Λ) ∧ LinearIndependent E lam ∧ (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0) ∧ (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re) ∧ (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re < 0) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE X.p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE X.p0_le a))) := by
  intro E _ _ _ r X
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_rational_frame_mem_flagDomain E r X
  obtain ⟨v, ho, hv⟩ := GlobalTheory.T.exists_orthogonal_rational_frame_flagDomain E r X u hu
  have hs := GlobalTheory.OrthoFrame.sign_of_mem X v ho hv
  choose d hd0 hdΛ using fun j => ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.exists_smul_mem X.Λ (x := v j)
    (by rw [X.Λ_span]; exact Submodule.mem_top)
  have hd0' : ∀ j, ((d j : 𝓞 E) : E) ≠ 0 := fun j h => hd0 j (by exact_mod_cast h)
  set lam : Fin r → Fin r → E := fun j => ((d j : 𝓞 E) : E) • v j with hlam
  have hlamΛ : ∀ j, lam j ∈ X.Λ := fun j => by
    have e : (d j) • v j = ((d j : 𝓞 E) : E) • v j := by
      ext a; simp [Algebra.smul_def]
    rw [hlam]; dsimp only; rw [← e]; exact hdΛ j
  have hlo : ∀ j k, j ≠ k → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0 := by
    intro j k h
    simp only [hlam, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_left, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_right, ho j k h,
      mul_zero]
  have hsl : ∀ τ : X.Ψ, ∀ j : Fin r, 0 < ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j *
      (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re := by
    intro τ j
    have hn : 0 < Complex.normSq (τ.1 (d j : E)) := Complex.normSq_pos.2 ((map_ne_zero τ.1).2 (hd0' j))
    have e : τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j)) =
        (Complex.normSq (τ.1 (d j : E)) : ℂ) * τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v j)) := by
      simp only [hlam, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_left, ReciprocityTheory.ChartRestriction.G.FD.HermitianTraceFormVanishing.herm_smul_right, map_mul,
        GlobalTheory.OrthoFrame.emb_cc, ← Complex.mul_conj]
      ring
    rw [e, Complex.re_ofReal_mul]
    have := hs τ j
    calc (0 : ℝ) < Complex.normSq (τ.1 (d j : E)) * (ReciprocityTheory.ChartRestriction.G.FD.sgn X.p0 j *
        (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (v j) (v j))).re) := mul_pos hn this
      _ = _ := by ring
  have hΨ : ∃ τ : E →+* ℂ, τ ∈ X.Ψ := by
    let τ0 : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    by_cases h : τ0 ∈ X.Ψ
    · exact ⟨τ0, h⟩
    · refine ⟨ComplexEmbedding.conjugate τ0, ?_⟩
      by_contra h'
      exact h ((X.cmType τ0).2 h')
  obtain ⟨τ0, hτ0⟩ := hΨ
  have hdv : (Matrix.of v).det ≠ 0 := by
    have h := (hv ⟨τ0, hτ0⟩).1
    have e : ReciprocityTheory.ChartRestriction.G.FD.mat (GlobalTheory.OrthoFrame.frm X.Ψ v) ⟨τ0, hτ0⟩ = τ0.mapMatrix (Matrix.of v).transpose := by
      ext k a; rfl
    rw [e, ← RingHom.map_det, Matrix.det_transpose] at h
    intro h0; exact h (by rw [h0, map_zero])
  have hdl : (Matrix.of lam).det ≠ 0 := by
    have e : Matrix.of lam = Matrix.diagonal (fun j => ((d j : 𝓞 E) : E)) * Matrix.of v := by
      ext j k; simp only [hlam, Matrix.of_apply, Matrix.diagonal_mul, Pi.smul_apply, smul_eq_mul]
    rw [e, Matrix.det_mul, Matrix.det_diagonal]
    exact mul_ne_zero (Finset.prod_ne_zero_iff.2 fun j _ => hd0' j) hdv
  refine ⟨GlobalTheory.OrthoFrame.frm X.Ψ lam, GlobalTheory.OrthoFrame.mem_of_sign X lam hlo hdl hsl, lam, hlamΛ, ?_, ?_, ?_, ?_, ?_⟩
  · exact Matrix.linearIndependent_rows_of_det_ne_zero hdl
  · intro j k hj hk
    exact hlo j k (by intro h; subst h; omega)
  · intro j hj τ
    have := hsl τ j
    simpa [ReciprocityTheory.ChartRestriction.G.FD.sgn, hj] using this
  · intro j hj τ
    have := hsl τ j
    simp only [ReciprocityTheory.ChartRestriction.G.FD.sgn, if_neg (not_lt.2 hj)] at this
    linarith
  · intro τ
    rfl

end GlobalTheory.OrthoFrame
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrthogonalLatticeFrameFlagDomainStatement
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orthogonal_lattice_frame_flagDomain : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∃ x ∈ X.dom, ∃ lam : Fin r → Fin r → E, (∀ j, lam j ∈ X.Λ) ∧ LinearIndependent E lam ∧ (∀ j k : Fin r, (j : ℕ) < X.p0 → X.p0 ≤ (k : ℕ) → ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam k) = 0) ∧ (∀ j : Fin r, (j : ℕ) < X.p0 → ∀ τ : X.Ψ, 0 < (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re) ∧ (∀ j : Fin r, X.p0 ≤ (j : ℕ) → ∀ τ : X.Ψ, (τ.1 (ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm (lam j) (lam j))).re < 0) ∧ ∀ τ : X.Ψ, Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.col (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) (Fin.castLE X.p0_le a)) = Submodule.span ℂ (Set.range fun a : Fin X.p0 => ReciprocityTheory.ChartRestriction.G.FD.Data.emb τ.1 (lam (Fin.castLE X.p0_le a))) := by
  first | exact @GlobalTheory.OrthoFrame.exists_orthoFrame | exact GlobalTheory.OrthoFrame.exists_orthoFrame | (intros; apply GlobalTheory.OrthoFrame.exists_orthoFrame <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmGoodReductionPointOnComponent
namespace GlobalTheory.FlatCore.CMPointExistence

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor _root_.Formalism.L2.LamCM _root_.Formalism.L2.Pj
open scoped ComplexOrder
open GlobalTheory GlobalTheory.CM GlobalTheory.Frames GlobalTheory.LamT


set_option maxHeartbeats 1000000 in
theorem exists_frPt_of_cmObj : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (K : Type) [Field K] [NumberField K] [Algebra c.F K] (ρ : 𝓞 K) (σ : K →+* ℂ) (X : CMObj H K ρ σ Dw.p Dw.q) (La : ℝ) (x : Sp K ⟶ Xo.X) (Φ : FibKey Xo K x) (_ : SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K) K))), (∀ τ, τ ∈ LamF.psiSet H ↔ LamF.labK c K τ (H.rt : E) = (ρ : K)) → (∀ j (τ : E →+* ℂ), ‖τ (X.hh j : E)‖ ≤ La ^ 2) → x ≫ Xo.s = sOf c K → ∃ y : FrPt Xo c K, y.x = x := by
  intro E _ _ _ H Dw l Xo c _ hstar K _ _ _ ρ σ X La x Φ m' hρ hLa hx
  have hfib : LamF.IsFibreOf X.B.pol Φ.key (LamF.gmap K) m'.φ :=
    (LamF.isFibreOf_iff_isPolFibre (𝓞 K) K (algebraMap (𝓞 K) K) X.B.pol Φ.key m'.φ).2
      ((GlobalTheory.T.principalTriple_pullback E H (𝓞 K) K (algebraMap (𝓞 K) K) X.B).2 Φ.T m' inferInstance).2.1
  obtain ⟨oa, oaΨ, oa', xΨ, x', φΨ, φ', τΨ, τ', ℓΨ, ℓ', Tl, LamL, hoa, -, -, hgood⟩ :=
    LamF.exists_lamObjGood_of_cmObj GlobalTheory.firstFiveLaws.2.1.secTwist GlobalTheory.thetaUnifAV_all GlobalTheory.firstFiveLaws.1
      GlobalTheory.homExtension_semiAbelian_dvr_unconditional E H l c hstar K ρ σ Dw.p Dw.q X La hρ hLa Φ.key m'.φ hfib
  obtain ⟨L, hL, hm⟩ := LamF.exists_lamLetters_isGood E H l c _ _ _ _ La hgood
  have hdet := LamF.Ind.lamInd E H l c hstar _ _ _ _ La hgood L hL
  have heig := LamF.LetterEigen.letter_eigen E H l c _ _ _ _ La hgood L hL
  obtain ⟨mm, e, src, U, ℓ⟩ := L
  have hmm : mm = Dw.mult := by
    funext b
    unfold Datum.mult
    split_ifs with h
    · exact (hm b).1 h
    · exact (hm b).2 h
  subst hmm
  choose w hw hU using hL.2.2.1
  obtain ⟨y, hy, -, -⟩ := GlobalTheory.T.exists_framedPoint_of_lie_eigenbasis E H Dw l Xo c K x Φ e U w hx hdet hU (fun τ i =>
    GlobalTheory.T.isEigenvectorAt_of_model E H Dw l Xo c K x Φ.T.t X.B.t Φ.m m' τ (w (e ⟨τ, i⟩)) (fun a => by
      have h := heig τ i (w (e ⟨τ, i⟩)) (hw _) a
      rw [← hoa]
      exact h))
  exact ⟨y, hy⟩

end GlobalTheory.FlatCore.CMPointExistence

namespace GlobalTheory.FlatCore

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions _root_.Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore


set_option maxHeartbeats 1000000 in
theorem exists_cmPt_on_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (y : FrPt Xo c K) (ρ₀ : 𝓞 K) (σ₁ : K →+* ℂ) (X : GlobalTheory.CM.CMObj H K ρ₀ σ₁ Dw.p Dw.q) (t₀ : SAB H (Sp K)), LiesOn Z y ∧ Nonempty (SABMap t₀ Xo.univ.t y.x) ∧ Nonempty (SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K) K))) ∧ ∀ τ : Psi H, ((ρ₀ : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 H.rt) := by
  intro E _ _ _ H Dw l Xo c r U x hL Z
  let σ₀ : c.F →+* ℂ := c.F.val.toRingHom
  have hσ₀ : GoodEmb c σ₀ := rfl
  obtain ⟨k, hk⟩ := framesOn_eq_model E H Dw l Xo c r U x hL Z σ₀ hσ₀
  have hU := hL.unf σ₀ hσ₀
  have hr : 0 < r := by rw [hU.1]; have := hL.pos; omega
  obtain ⟨D₁, hD₁p, hD₁q⟩ := hL.line
  obtain ⟨x₁, hx₁, lam, h1, h2, h3, h4, h5, h6⟩ := GlobalTheory.T.exists_orthogonal_lattice_frame_flagDomain E r ((U σ₀).X k)
  let x₀ : ((U σ₀).X k).dom := ⟨x₁, hx₁⟩
  obtain ⟨W⟩ := ReciprocityTheory.ChartRestriction.G.PullbackSections.nonempty_unfAt hU k x₀
  obtain ⟨Zl⟩ := GlobalTheory.T.exists_cmLattice_data_unfolding_signature_one_zero E H Dw l Xo c r (U σ₀) hU hr D₁ hD₁p hD₁q k x₀ W lam h1 h2 h3 h4 h5 h6
  have hfd : FiniteDimensional ℚ c.F := c.fin
  obtain ⟨K₁, nf, hk1, ρ, X, y, t₀, m, m', -, -, -, -, -, hle, hρ, -, hy, hpt, -⟩ :=
    GlobalTheory.CM.cmExists_holds E H Dw l Xo W.g _ W.F (W.ik k) W.Pm W.per Zl c.F hfd
  letI : Algebra c.F K₁ := (IntermediateField.inclusion hle).toRingHom.toAlgebra
  letI : StarRing (𝓞 E) := H.starRing
  obtain ⟨Φ⟩ := GlobalTheory.LamT.nonempty_fibKey E H Dw l Xo K₁ y (by have := hL.pos; omega)
  obtain ⟨n, -⟩ := (GlobalTheory.sabMap_cancel_and_comp_over E H _ _ _ Xo.univ.t t₀ Φ.T.t y y (𝟙 _) m Φ.m
    (Category.id_comp _).symm).1
  obtain ⟨mB⟩ : Nonempty (SABMap Φ.T.t X.B.t (spMap (algebraMap (𝓞 K₁) K₁))) := by
    obtain ⟨mm, -⟩ := ReciprocityTheory.ChartRestriction.G.Geo.Tor.sabComp ReciprocityTheory.ChartRestriction.G.Geo.Tor.pullCubComp E H _ _ _ X.B.t t₀ Φ.T.t _ _ m' n
    rw [Category.id_comp] at mm
    exact ⟨mm⟩
  obtain ⟨yF, hyF⟩ := GlobalTheory.FlatCore.CMPointExistence.exists_frPt_of_cmObj E H Dw l Xo c (fun _ => rfl) K₁ ρ (algebraMap K₁ ℂ) X
    (1 + ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖) y Φ mB
    (fun τ => by
      show τ (H.rt : E) = H.rt0 ↔ _
      rw [← hρ, Subtype.ext_iff]
      exact Iff.rfl) (fun j τ => by
      have h1 : ‖τ (X.hh j : E)‖ ≤ ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖ :=
        calc ‖τ (X.hh j : E)‖ ≤ ∑ τ' : E →+* ℂ, ‖τ' (X.hh j : E)‖ :=
              Finset.single_le_sum (f := fun τ' : E →+* ℂ => ‖τ' (X.hh j : E)‖) (fun _ _ => norm_nonneg _)
                (Finset.mem_univ τ)
          _ ≤ _ := Finset.single_le_sum (f := fun j' => ∑ τ' : E →+* ℂ, ‖τ' (X.hh j' : E)‖)
                (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ j)
      have h0 : 0 ≤ ∑ j, ∑ τ : E →+* ℂ, ‖τ (X.hh j : E)‖ :=
        Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
      nlinarith) hy
  refine ⟨K₁, inferInstance, nf, inferInstance, yF, ρ, algebraMap K₁ ℂ, X, t₀, ?_, ⟨hyF ▸ m⟩, ⟨m'⟩, fun τ => ?_⟩
  · have hmem : (⟨k, x₁⟩ : Σ k, Frame ((U σ₀).X k).Ψ r) ∈ framesOn (U σ₀) Z := by rw [hk]; exact ⟨rfl, hx₁⟩
    obtain ⟨h', hon⟩ := hmem
    have hpt' : ((U σ₀).un k x₀).x = spMap (algebraMap K₁ ℂ) ≫ yF.x := by rw [hyF, hpt]; exact W.pt
    have key : ptF ((U σ₀).un k x₀) = spMap (algebraMap K₁ ℂ) ≫ ptF yF := by
      apply Limits.pullback.hom_ext
      · unfold ptF
        erw [Category.assoc, Limits.pullback.lift_fst, Limits.pullback.lift_fst]
        exact hpt'
      · unfold ptF
        erw [Category.assoc, Limits.pullback.lift_snd, Limits.pullback.lift_snd]
        erw [← Spec.map_comp]
        rfl
    intro s
    let s' : Sp (CAt σ₀) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    have h7 := hon s'
    change ptF ((U σ₀).un k x₀) s' ∈ _ at h7
    rw [key] at h7
    have hs : (spMap (algebraMap K₁ ℂ)) s' = s := Subsingleton.elim (α := PrimeSpectrum K₁) _ _
    rw [← hs]
    exact h7
  · exact Subtype.ext (hρ.trans τ.2.symm)

end GlobalTheory.FlatCore
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCmGoodReductionPointOnComponentStatement
open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cm_goodReduction_point_on_component : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (Z : Comp Xo c), ∃ (K : Type) (_ : Field K) (_ : NumberField K) (_ : Algebra c.F K) (y : FrPt Xo c K) (ρ₀ : 𝓞 K) (σ₁ : K →+* ℂ) (X : GlobalTheory.CM.CMObj H K ρ₀ σ₁ Dw.p Dw.q) (t₀ : SAB H (Sp K)), LiesOn Z y ∧ Nonempty (SABMap t₀ Xo.univ.t y.x) ∧ Nonempty (SABMap t₀ X.B.t (spMap (algebraMap (𝓞 K) K))) ∧ ∀ τ : Psi H, ((ρ₀ : 𝓞 K) : K) = algebraMap c.F K (embK c τ.1 H.rt) := by
  first | exact @GlobalTheory.FlatCore.exists_cmPt_on_comp | exact GlobalTheory.FlatCore.exists_cmPt_on_comp | (intros; apply GlobalTheory.FlatCore.exists_cmPt_on_comp <;> assumption)
end
