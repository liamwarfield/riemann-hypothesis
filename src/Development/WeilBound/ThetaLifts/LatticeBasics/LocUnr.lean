module

public import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilDatumPowersUnramifiedEtaTilde
public import Development.AutomorphicSpectrum.Proofs.AdelicProofs.LocGram
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.BoundMulTranslate
public import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ExistsBasisCols
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.LocUnr
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

def LocUnrSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (χ : Chr F E), IsHecke F E χ →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0 →
    ∀ K (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ v, Nonempty (E →ₐ[F] Fv F v) → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure → μ {g | IntAt v g.1} = 1 → ∀ (z : ℂ) f, (n : ℝ) / 2 < z.re →
      IsSphAt K χ v (z + n / 2) f → Integrable (fun u : locGrp σ Y v => f (e (u.1, 1))) μ ∧
        (∫ u, f (e (u.1, 1)) ∂μ) * locD E n v z = ∏ i ∈ Finset.range n, Lv (charFam χ) v (z + n / 2 - i)

def LocUnrInert : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) r s, B.IsGood σ → Y.IsHerm σ B r s → ∀ (χ : Chr F E), IsHecke F E χ →
    ResEtaPow (Units.map (algebraMap F (AF F)).toMonoidHom).range χ 0 →
    ∀ K (e : UA σ Y.J × UA σ Y.J →* G2 σ Y), IsStab2 B K → (∀ g g', IsEmb g g' (e (g, g'))) →
    ∀ v, (∃ w, Formalism.UG.IsInertAt F E v w) → (∀ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v → UnrAt χ w) →
    ∀ μ : Measure (locGrp σ Y v), μ.IsHaarMeasure → μ {g | IntAt v g.1} = 1 → ∀ (z : ℂ) f, (n : ℝ) / 2 < z.re →
      IsSphAt K χ v (z + n / 2) f → Integrable (fun u : locGrp σ Y v => f (e (u.1, 1))) μ ∧
        (∫ u, f (e (u.1, 1)) ∂μ) * locD E n v z = ∏ i ∈ Finset.range n, Lv (charFam χ) v (z + n / 2 - i)

theorem locUnr_of (h₁ : LocUnrSplit) (h₂ : LocUnrInert) : LocUnr := fun F E _ _ _ _ _ σ B n Y r s hB hY χ hχ hr K e hK he v =>
  (GlobalTheory.KFinLoc.split_or_inert F E σ B hB v).elim (h₁ F E σ B n Y r s hB hY χ hχ hr K e hK he v)
    (h₂ F E σ B n Y r s hB hY χ hχ hr K e hK he v)

end GlobalTheory.ThK.Dbl

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.HgtArch
section -- merged from Development.AutomorphicSpectrum.Proofs.AdelicProofs.HasIwasawaArch
noncomputable section

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

namespace GlobalTheory.CompanionTheory.IwaDbl

theorem hasIwasawa_arch : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ} {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ {J : Matrix (Fin n) (Fin n) E} {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}, Q = dblGram finSumFinEquiv J → ∀ (w : InfinitePlace F) (b : GL (Fin n) (w.Completion ⊗[F] E)) (ε : Fin n → Bool), locGram σ J b = Matrix.diagonal (fun i => if ε i then 1 else -1) → HasIwasawa σ Q (KArch σ Q w b) := by
  intro F E _ _ _ _ _ n σ hc J Q hQ w b ε hb
  exact GlobalTheory.Core.Rk.IwArch.hasIwasawa_KArch hc hQ w b ε hb

end GlobalTheory.CompanionTheory.IwaDbl

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl.Hgt

open scoped Matrix TensorProduct
open NumberField GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.Doubling GlobalTheory.CompanionTheory.IwaDbl

theorem unitary_iff_commute {ι : Type} [Fintype ι] [DecidableEq ι] {Q Θ : Matrix ι ι ℂ} {s : ℂ} (hs : s ≠ 0) (hQ : IsUnit Q)
    (B g : GL ι ℂ) (hB : B.1ᴴ * (s • (Q * Θ)) * B.1 = 1) (hg : g.1ᴴ * Q * g.1 = Q) :
    (B⁻¹ * g * B).1ᴴ * (B⁻¹ * g * B).1 = 1 ↔ Commute g.1 Θ := by
  have u : ∀ x : GL ι ℂ, IsUnit x.1ᴴ := fun x => (Matrix.isUnit_conjTranspose _).2 x.isUnit
  have h1 : (B⁻¹).1ᴴ * (B⁻¹).1 = s • (Q * Θ) := by
    refine (u B).mul_left_cancel (B.isUnit.mul_right_cancel ?_)
    rw [hB, ← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, Matrix.mul_assoc, Units.inv_mul]; simp
  have h2 : (B⁻¹ * g * B).1ᴴ * (B⁻¹ * g * B).1 = B.1ᴴ * (s • (g.1ᴴ * Q * (Θ * g.1))) * B.1 := by
    simp only [Units.val_mul, Matrix.conjTranspose_mul]
    calc _ = B.1ᴴ * (g.1ᴴ * ((B⁻¹).1ᴴ * (B⁻¹).1) * g.1) * B.1 := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.mul_smul, Matrix.smul_mul]
  rw [h2, ← hB, B.isUnit.mul_left_inj, (u B).mul_right_inj, (smul_right_injective _ hs).eq_iff]
  conv_lhs => rhs; rw [← hg, Matrix.mul_assoc]
  rw [((u g).mul hQ).mul_right_inj]
  exact eq_comm

theorem exists_cartan_frame {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (hd : IsUnit M) (h : IsCartan M θ) {r : ℝ}
    (hr : r ≠ 0) : ∃ (b : GL (Fin n) ℂ) (ε : Fin n → Bool) (s : ℂ), s ≠ 0 ∧
      b.1ᴴ * ((r : ℂ) • Mᵀ) * b.1 = Matrix.diagonal (fun i => if ε i then 1 else -1) ∧
      b.1ᴴ * (s • (((r : ℂ) • Mᵀ) * θ)) * b.1 = 1 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hM' : Mᵀᴴ = Mᵀ := congrArg Matrix.transpose hM
  have h4 : θᴴ * Mᵀ = Mᵀ * θ := by
    have e : θᴴ * Mᵀ * θ = Mᵀ := by
      conv_rhs => rw [← h2]
      rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]; rfl
    calc _ = θᴴ * Mᵀ * (θ * θ) := by rw [h1, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e]
  set N : Matrix (Fin n) (Fin n) ℂ := ((|r| : ℝ) : ℂ) • (Mᵀ * θ) with hN
  have hr' : ((|r| : ℝ) : ℂ) ≠ 0 := by simpa using hr
  have hNh : N.IsHermitian := by
    change Nᴴ = N
    rw [hN, Matrix.conjTranspose_smul, Matrix.conjTranspose_mul, hM', h4]; simp
  obtain ⟨ε, b, hb⟩ := Frames.exists_congr_diagonal_sign hNh (by
    rw [hN, Matrix.det_smul, Matrix.det_mul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ hr') (mul_ne_zero ((Matrix.isUnit_iff_isUnit_det _).1 hd).ne_zero
      (Matrix.isUnit_det_of_left_inverse h1).ne_zero))
  have hb1 : b.1ᴴ * N * b.1 = 1 := by
    rw [hb, ← Matrix.diagonal_one]
    congr 1
    funext i
    have hx : (fun j => b.1 j i) ≠ 0 := fun e => by
      have := congrFun (congrFun b.inv_mul i) i
      simp [Matrix.mul_apply, show ∀ j, b.1 j i = 0 from congrFun e] at this
    have e : (b.1ᴴ * N * b.1) i i = ((|r| : ℝ) : ℂ) * ((θ *ᵥ fun j => b.1 j i) ⬝ᵥ M *ᵥ star fun j => b.1 j i) := by
      rw [hN, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul, dotProduct_comm, ← Matrix.vecMul_transpose,
        ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      rfl
    have := mul_pos (abs_pos.2 hr) (h3 _ hx)
    rw [← Complex.re_ofReal_mul, ← e, hb, Matrix.diagonal_apply_eq] at this
    split_ifs at this ⊢
    · rfl
    · norm_num at this
  set s : ℂ := ((|r| : ℝ) : ℂ) / r with hs
  have hrc : (r : ℂ) ≠ 0 := by simpa using hr
  have hss : s * s = 1 := by
    rw [hs, div_mul_div_comm, ← Complex.ofReal_mul, abs_mul_abs_self, Complex.ofReal_mul, div_self (mul_ne_zero hrc hrc)]
  have hsN : s • (((r : ℂ) • Mᵀ) * θ) = N := by rw [Matrix.smul_mul, smul_smul, hs, div_mul_cancel₀ _ hrc]
  set S := b.1ᴴ * ((r : ℂ) • Mᵀ) * b.1 with hS
  have hSh : S.IsHermitian := by
    change Sᴴ = S
    simp [hS, Matrix.conjTranspose_smul, hM', Matrix.mul_assoc]
  have hS1 : S = s • ((b⁻¹).1 * θ * b.1) := by
    have : (r : ℂ) • Mᵀ = s • (N * θ) := by
      rw [← hsN, Matrix.smul_mul, smul_smul, hss, one_smul, Matrix.mul_assoc, h1, Matrix.mul_one]
    have e : b.1ᴴ * N = (b⁻¹).1 := by
      rw [← Matrix.one_mul (b⁻¹).1, ← hb1, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
    rw [hS, this, Matrix.mul_smul, Matrix.smul_mul, ← Matrix.mul_assoc, e]
  have hS2 : S * S = 1 := by
    rw [hS1, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hss, one_smul]
    calc _ = (b⁻¹).1 * θ * (b.1 * (b⁻¹).1) * θ * b.1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [Units.mul_inv, Matrix.mul_one, Matrix.mul_assoc _ θ θ, h1, Matrix.mul_one, Units.inv_mul]
  have hD := hSh.conjStarAlgAut_star_eigenvectorUnitary
  have hD2 := congrArg (Unitary.conjStarAlgAut ℂ _ (star hSh.eigenvectorUnitary)) hS2
  rw [map_mul, hD, map_one, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one] at hD2
  rw [Unitary.conjStarAlgAut_star_apply] at hD
  set U := hSh.eigenvectorUnitary
  refine ⟨b * Unitary.toUnits U, fun i => decide (hSh.eigenvalues i = 1), s, left_ne_zero_of_mul_eq_one hss, ?_, ?_⟩
  · refine Eq.trans ?_ (hD.trans ?_)
    · simp only [hS, Units.val_mul, Matrix.conjTranspose_mul, Matrix.mul_assoc]; rfl
    · congr 1
      funext i
      have : (hSh.eigenvalues i : ℂ) * hSh.eigenvalues i = 1 := congrFun (Matrix.diagonal_injective hD2) i
      rcases mul_self_eq_one_iff.1 this with e | e
      · rw [if_pos (by simpa using e)]; exact e
      · rw [if_neg (by simp only [decide_eq_true_eq]; intro e'; rw [e'] at e; norm_num at e)]; exact e
  · rw [hsN, Units.val_mul, Matrix.conjTranspose_mul]
    calc _ = (Unitary.toUnits U).1ᴴ * (b.1ᴴ * N * b.1) * (Unitary.toUnits U).1 := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hb1, Matrix.mul_one]; exact U.2.1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}

theorem exists_arch (hc : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w) {J : Matrix (Fin n) (Fin n) E}
    {M θ : Matrix (Fin n) (Fin n) ℂ} (hM : Mᴴ = M) (hd : IsUnit M) (h : IsCartan M θ) {r : ℝ} (hr : r ≠ 0)
    (hJ : J.map τ.1 = (r : ℂ) • Mᵀ) : ∃ b : GL (Fin n) (w.Completion ⊗[F] E),
      HasIwasawa σ (dblGram finSumFinEquiv J) (KArch σ _ w b) ∧ ∀ g : GArch σ (dblGram finSumFinEquiv J) w,
        g ∈ KArch σ _ w b ↔ Commute ((matHom _ σ _ g).1.map (infEmb τ)) (blkMat finSumFinEquiv θ (-θ)) := by
  obtain ⟨b, ε, s, hs, h1, h2⟩ := exists_cartan_frame hM hd h hr
  let e := RingEquiv.ofBijective _ (infEmb_bijective hc τ)
  have e1 : bc (infEmb τ) (bc e.symm.toRingHom b) = b := Units.ext (Matrix.ext fun i j => e.apply_symm_apply _)
  have e2 : ∀ {m : ℕ} (X : Matrix (Fin m) (Fin m) E), (JR w.Completion X).map (infEmb τ) = X.map τ.1 := fun X => by
    ext r s; simp [JR, inclR]
  have inj : ∀ {m : ℕ} {X Y : Matrix (Fin m) (Fin m) (w.Completion ⊗[F] E)}, X = Y ↔ X.map (infEmb τ) = Y.map (infEmb τ) :=
    (Matrix.map_injective e.injective).eq_iff.symm
  refine ⟨bc e.symm.toRingHom b, hasIwasawa_arch hc rfl w _ ε (inj.2 ?_), fun g => ?_⟩
  · rw [locGram, Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR hc, e2, hJ, Matrix.diagonal_map (map_zero _)]
    refine (show _ = _ from ?_).trans (h1.trans ?_)
    · conv_rhs => rw [← e1]
      rfl
    · congr 1; funext i; split_ifs <;> simp
  · have hQ : (dblGram finSumFinEquiv J).map τ.1 = blkMat finSumFinEquiv ((r : ℂ) • Mᵀ) (-((r : ℂ) • Mᵀ)) := by
      rw [dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _), hJ]
    have hu : IsUnit ((r : ℂ) • Mᵀ).det := by
      rw [Matrix.det_smul, Matrix.det_transpose]
      exact (mul_ne_zero (pow_ne_zero _ (by simpa using hr)) ((Matrix.isUnit_iff_isUnit_det _).1 hd).ne_zero).isUnit
    refine Iff.trans ?_ (unitary_iff_commute (Q := (dblGram finSumFinEquiv J).map τ.1) hs ?_ (blkGL finSumFinEquiv (b, b))
      (bc (infEmb τ) (matHom _ σ _ g)) ?_ ?_)
    · rw [mem_stabArch]
      change _ * 1 * _ = 1 ↔ _
      rw [inj, Matrix.mul_one, Matrix.map_mul, Frames.map_cT_sigR hc, Matrix.map_one _ (map_zero _) (map_one _)]
      conv_rhs => rw [← e1, ← bc_blkGL, ← map_inv, ← map_mul, ← map_mul]
      rfl
    · rw [hQ, Matrix.isUnit_iff_isUnit_det, det_blkMat, Matrix.det_neg]
      exact hu.mul ((isUnit_one.neg.pow _).mul hu)
    · rw [hQ, blkMat_mul, neg_mul_neg, val_blkGL, show (blkMat finSumFinEquiv b.1 b.1)ᴴ = blkMat finSumFinEquiv b.1ᴴ b.1ᴴ from
        cT_blkMat _ (starRingEnd ℂ) _ _, Matrix.mul_smul, Matrix.smul_mul, blkMat_mul, blkMat_mul]
      rw [Matrix.mul_smul, Matrix.smul_mul] at h2
      rw [← blkMat_one finSumFinEquiv, ← h2]
      let A : Matrix (Fin n) (Fin n) ℂ := b.1ᴴ * (((r : ℂ) • Mᵀ) * θ) * b.1
      exact (congrArg (fun X => Matrix.submatrix X finSumFinEquiv.symm finSumFinEquiv.symm) (Matrix.fromBlocks_smul s A 0 0 A)).trans
        (by simp only [smul_zero]; rfl)
    · have := inj.1 (show cT _ (matHom _ σ _ g).1 * JR _ _ * (matHom _ σ _ g).1 = JR _ _ from g.2)
      rwa [Matrix.map_mul, Matrix.map_mul, Frames.map_cT_sigR hc, e2] at this

end GlobalTheory.ThK.Dbl.Hgt

end
end

section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.ExistsIsHeckeLOfCompleted
section -- merged from Development.WeilBound.ThetaLifts.LatticeBasics.GoodNe
noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
  {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}

theorem isHecke_nu (h : IsTriple B G X om om') : IsHecke F E X.ν :=
  ⟨(h.chars.heckeα.1.div' h.chars.heckeβ.1 :), fun x => by
    rw [Chars.ν, MonoidHom.div_apply, h.chars.heckeα.2 x, h.chars.heckeβ.2 x, div_one]⟩

theorem hasExp_nu (h : IsTriple B G X om om') : HasExp B.emb X.ν (fun w => B.mα w - B.mβ w) := by
  intro z hz
  show (((X.α z / X.β z : Circle)) : ℂ) = _
  rw [Circle.coe_div, h.chars.expα z hz, h.chars.expβ z hz, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun w _ => ?_
  have hne : piInf (B.emb w) z ≠ 0 := (z.isUnit.map (piInf (B.emb w))).ne_zero
  rw [zpow_sub₀ (div_ne_zero hne (by exact_mod_cast (norm_ne_zero_iff.2 hne)))]

theorem nonempty_emb_of_splitsFully (hB : B.IsGood σ) {v : Pl F} (hv : SplitsFully E v) : Nonempty (E →ₐ[F] Fv F v) := by
  refine (GlobalTheory.KFinLoc.split_or_inert F E σ B hB v).resolve_right ?_
  rintro ⟨w, hw⟩
  have hw' : Ideal.map (algebraMap (𝓞 F) (𝓞 E)) v.asIdeal = w.asIdeal := hw
  have hu : w.under (𝓞 F) = v := (HeightOneSpectrum.ext (v.isMaximal.eq_of_le (w.under (𝓞 F)).isPrime.ne_top
    (Ideal.map_le_iff_le_comap.1 hw'.le))).symm
  obtain ⟨p, hp, hN, -⟩ := GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully F E w (hu ▸ hv)
  rw [← hw', Ideal.absNorm_algebraMap, ← Algebra.IsAlgebraic.finrank_of_isFractionRing (𝓞 F) F (𝓞 E) E, hB.cm.2.2.1] at hN
  exact Nat.Prime.not_prime_pow le_rfl (hN ▸ hp)

theorem nu_pow_ne_one (h : IsTriple B G X om om') {v : Pl F} (hv : X.Good v) (t : E →ₐ[F] Fv F v) {k : ℤ} (hk : k ≠ 0) :
    chrW X.ν t (unifAt v) ^ k ≠ 1 := by
  intro hpow
  have hW : splitPrime t ∉ above E (X.T : Set (Pl F)) := fun hmem => hv.1 (by simpa [above, splitPrime_under] using hmem)
  have hunr : UnrAt X.ν (splitPrime t) := by
    rw [Chars.ν, div_eq_mul_inv]
    exact (h.chars.unrα _ hW).mul (h.chars.unrβ _ hW).inv
  rw [GlobalTheory.ChrWUnif.chrW_unifAt F E X.ν v t hunr] at hpow
  obtain ⟨H, hloc, hinf⟩ := GlobalTheory.HeckeBridge.exists_hchar F E σ h.base.cm X.ν (isHecke_nu h)
  have hval : val X.ν (splitPrime t) = H.val (splitPrime t) := (hloc _ _).symm
  obtain ⟨p, hp, hN, hsq⟩ := GlobalTheory.SplitFullyNorm.exists_prime_absNorm_eq_of_splitsFully F E (splitPrime t)
    (by rw [splitPrime_under]; exact hv.2)
  refine GlobalTheory.CMSplitValue.not_isOfFinOrder_val F E σ h.base.cm h.base.galois B.emb H _ (hinf _ _ (hasExp_nu h))
    (fun w => ?_) p hp _ hN hsq ?_
  · have := h.geo.kappa w
    omega
  · rw [← hval]
    exact isOfFinOrder_iff_zpow_eq_one.2 ⟨k, hk, hpow⟩

theorem goodNe : GoodNe := fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ hv =>
  ⟨nonempty_emb_of_splitsFully h.base hv.2, fun t e => nu_pow_ne_one h hv t one_ne_zero (by rw [e, zpow_one])⟩

end GlobalTheory.ThK.Dbl

end
end

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.HeckeBridge GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds
open GlobalTheory.CMVal (IsHeckeL IsCMType eulerFactor)

theorem exists_hchar_unitary (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) : IsCMExt F E σ → ∀ χ : Chr F E, IsHecke F E χ → ∃ H : Formalism.L2.Host.HChar E, H.IsUnitary ∧
      (∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ), H.loc W x = locChar χ W x) ∧
      ∀ (τ : ∀ w : InfinitePlace F, EmbOver E w) (m : InfinitePlace F → ℤ), HasExp τ χ m →
        H.HasInf (fun w => (τ w).1) m := by
  intro hcm χ hχ
  obtain ⟨Φ, j, -, hΦc, hj, hΦ⟩ := exists_tensor_adele_equiv F E σ hcm
  have hfin : ∀ x : E, finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = algebraMap E (FiniteAdeleRing (𝓞 E) E) x := fun x => by
    rw [show finAdEquiv F E ((1 : Af F) ⊗ₜ[F] x) = _ from toFinAd_tmul 1 x, map_one, one_mul]
  let u : Neutral.B1.Ideles E →* (AF F ⊗[F] E)ˣ := Units.map Φ.symm.toRingHom.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hΦc
  have ht : Continuous (Circle.toUnits : Circle →* ℂˣ) :=
    Units.continuous_iff.2 ⟨continuous_subtype_val, by
      have h : Continuous fun z : Circle => ((z⁻¹ : Circle) : ℂ) := continuous_subtype_val.comp continuous_inv
      refine h.congr fun z => ?_
      simp⟩
  have hdiag : ∀ k : Eˣ, u (Neutral.B1.diagUnits E k) = Units.map (inclR (F := F) (AF F)).toMonoidHom k := fun k =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ]
      change (algebraMap E (InfiniteAdeleRing E) k, algebraMap E (FiniteAdeleRing (𝓞 E) E) k) = _
      refine Prod.ext (hj k).symm (hfin k).symm))
  have hloc : ∀ (W : HeightOneSpectrum (𝓞 E)) (x : (W.adicCompletion E)ˣ),
      u (Neutral.B1.localIdele E W x) = locIdele F W x := fun W x =>
    Units.ext (Φ.symm_apply_eq.2 (by
      rw [hΦ, infTens_locIdele, map_one, finTens_locIdele]
      rfl))
  let H : Formalism.L2.Host.HChar E := ⟨Circle.toUnits.comp (χ.comp u), ht.comp (hχ.1.comp hu), fun k => by
    change Circle.toUnits (χ (u _)) = 1
    rw [hdiag, hχ.2, map_one]⟩
  refine ⟨H, fun x => Circle.norm_coe (χ (u x)), fun W x => ?_, fun τ m hm k => ?_⟩
  · change Circle.toUnits (χ (u _)) = Circle.toUnits (χ (locIdele F W x))
    rw [hloc]
  · set z := u (Formalism.L2.Host.infDiag k) with hz
    have hz1 : Φ (z : AF F ⊗[F] E) = (Formalism.L2.Host.infDiag k : AdeleRing (𝓞 E) E) := Φ.apply_symm_apply _
    rw [coe_infDiag, hΦ] at hz1
    have hinf : infTens F E z = (1 : Ainf F) ⊗ₜ[F] (k : E) :=
      j.injective ((congrArg Prod.fst hz1).trans (hj k).symm)
    have hfin1 : finTens F E z = 1 :=
      (finAdEquiv F E).injective ((congrArg Prod.snd hz1).trans (map_one _).symm)
    have hAt : At (evI F) ((z : AF F ⊗[F] E) - 1) := by
      intro a ha
      have ha1 : a.1 = 0 := (InfiniteAdeleRing.ringEquiv_mixedSpace F).injective (ha.trans (map_zero _).symm)
      refine tens_ext ?_ ?_
      · rw [Algebra.smul_def, map_mul, map_zero]
        change (a.1 ⊗ₜ[F] (1 : E)) * _ = 0
        rw [ha1, TensorProduct.zero_tmul, zero_mul]
      · rw [Algebra.smul_def, map_mul, map_zero, map_sub, map_one, hfin1, sub_self, mul_zero]
    have hpi : ∀ w, piInf (τ w) z = (τ w).1 k := fun w => by
      change infEmb (τ w) (compInf F E w z) = _
      rw [compInf_eq_infTens, hinf, Algebra.TensorProduct.map_tmul, map_one, infEmb_tmul, map_one, one_mul]
      rfl
    change ((χ z : Circle) : ℂ) = _
    rw [hm z hAt]
    exact Finset.prod_congr rfl fun w _ => by rw [hpi w]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isCMType_emb (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) : IsCMType fun w => (τ w).1 := by
  haveI := h.1
  haveI := h.2.1
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  have real : ∀ φ : F →+* ℂ, ComplexEmbedding.conjugate φ = φ := fun φ => IsTotallyReal.complexEmbedding_isReal φ
  have emb : ∀ φ : F →+* ℂ, (InfinitePlace.mk φ).embedding = φ := fun φ =>
    (InfinitePlace.embedding_mk_eq φ).elim id fun e => e.trans (real φ)
  intro φ
  have cj : ∀ w, (ComplexEmbedding.conjugate (τ w).1).comp (algebraMap F E) = w.embedding := fun w =>
    (congrArg ComplexEmbedding.conjugate (τ w).2).trans (real _)
  refine ⟨InfinitePlace.mk (φ.comp (algebraMap F E)), ?_, fun w hw => ?_⟩
  · set w := InfinitePlace.mk (φ.comp (algebraMap F E))
    obtain ⟨g, hg⟩ := ComplexEmbedding.exists_comp_symm_eq_of_comp_eq (k := F) (τ w).1 φ ((τ w).2.trans (emb _))
    let s : E ≃ₐ[F] E := AlgEquiv.ofBijective σ σ.bijective
    have hs : s ≠ 1 := fun e => IsTotallyComplex.complexEmbedding_not_isReal φ (RingHom.ext fun x => by
      have e1 : σ x = x := congrArg (fun y : E ≃ₐ[F] E => y x) e
      have := h.2.2.2 φ x
      rw [e1] at this
      exact this.symm)
    obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E ≃ₐ[F] E)).1 ((IsGalois.card_aut_eq_finrank F E).trans h.2.2.1)
    by_cases e : g.symm = 1
    · left; rw [← hg, e]; rfl
    · right
      rw [← hg, (hy _ e).trans (hy _ hs).symm]
      exact RingHom.ext fun x => h.2.2.2 _ x
  · rcases hw with rfl | rfl
    · rw [(τ w).2, InfinitePlace.mk_embedding]
    · rw [cj, InfinitePlace.mk_embedding]

variable {I : Type} [Fintype I]

theorem eq_charL {χ : Chr F E} {H : Formalism.L2.Host.HChar E} (hu : H.IsUnitary) (hloc : ∀ W x, H.loc W x = locChar χ W x)
    {L : ℂ → ℂ} (hL : IsHeckeL H L) {s : ℂ} (hs : 1 < s.re) : L s = charL χ (∅ : Set (Pl F)) s := by
  have e : charFam χ = heckeFam H := funext fun w => by
    have e1 : UnrAt χ w ↔ H.UnrAt w := forall₂_congr fun x _ => by rw [hloc]
    have e2 : val χ w = H.val w := (hloc _ _).symm
    by_cases hw : H.UnrAt w <;> simp [charFam, heckeFam, e1, e2, hw]
  have e0 : above E (∅ : Set (Pl F)) = ∅ := Set.eq_empty_of_forall_notMem fun _ h => h
  rw [charL, LS, e, e0]
  have h1 := (converges_heckeFam ∅ hu hs).hasProd
  simp only [locL_heckeFam] at h1
  exact (hL.2 s hs).unique ((Equiv.subtypeUnivEquiv (p := fun w => w ∉ (∅ : Set (HeightOneSpectrum (𝓞 E))))
    (fun _ => Set.notMem_empty _)).hasProd_iff.1 h1)

def LInt2 : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) om om', IsTriple B G X om om' → ∀ χ ∈ ({X.ν, X.ν⁻¹} : Set (Chr F E)),
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ (∀ s : ℂ, 1 < s.re → Λ s = charL χ (∅ : Set (Pl F)) s) ∧
      ∀ z : ℤ, -((a + a' : ℕ) : ℤ) ≤ 2 * z → Λ z ≠ 0

end GlobalTheory.ThK.Dbl

end
end
