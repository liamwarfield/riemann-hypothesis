module

public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.AeFacts
public import Development.WeilBound.ThetaLifts.EigenvalueEndgame.TowerCodimensionTwo
public import Development.WeilBound.ThetaLifts.ConeHypotheses.PureEqPureA
public import Development.WeilBound.ThetaLifts.TowerModels.PlaneHerm
public import Development.WeilBound.ThetaLifts.CartanFactorisation.IntegrableOnRight

@[expose] public section

section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.ExistsAbsGt
noncomputable section

namespace PositivityTheory.ThKEnd.Grp

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open PositivityTheory.ThKG.Tow.Levi

section Abs

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

theorem abs_conj {Γ N N₂ : Subgroup G} {γ : G} (hγ : γ ∈ Γ) (hN : ∀ u, u ∈ N₂ ↔ γ * u * γ⁻¹ ∈ N) (μ : Measure N) (𝓕 : Set N)
    [μ.IsHaarMeasure] (h2 : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) : ∃ (μ₂ : Measure N₂) (𝓕₂ : Set N₂), μ₂.IsHaarMeasure ∧
      IsFundamentalDomain (Γ.subgroupOf N₂) 𝓕₂ μ₂ ∧ μ₂ 𝓕₂ = μ 𝓕 ∧
      ∀ f : G → ℂ, ∫ u in 𝓕₂, f (γ * u.1 * γ⁻¹) ∂μ₂ = ∫ u in 𝓕, f u.1 ∂μ := by
  let φ : N ≃ₜ* N₂ :=
    { toFun := fun u => ⟨γ⁻¹ * u * γ, (hN _).2 (by simpa [mul_assoc] using u.2)⟩
      invFun := fun u => ⟨γ * u * γ⁻¹, (hN _).1 u.2⟩
      left_inv := fun u => Subtype.ext (by simp [mul_assoc])
      right_inv := fun u => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun u v => Subtype.ext (by simp [mul_assoc])
      continuous_toFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _
      continuous_invFun := ((continuous_const.mul continuous_subtype_val).mul continuous_const).subtype_mk _ }
  let ψ := φ.toHomeomorph.toMeasurableEquiv
  have mp : MeasurePreserving ψ μ (μ.map ψ) := ⟨ψ.measurable, rfl⟩
  let e : Γ.subgroupOf N ≃ Γ.subgroupOf N₂ :=
    φ.toEquiv.subtypeEquiv fun u => ⟨fun k => mul_mem (mul_mem (inv_mem hγ) (show u.1 ∈ Γ from k)) hγ, fun k => by
      have := mul_mem (mul_mem hγ (show γ⁻¹ * u.1 * γ ∈ Γ from k)) (inv_mem hγ)
      change u.1 ∈ Γ
      simpa [mul_assoc] using this⟩
  refine ⟨μ.map ψ, ψ.symm ⁻¹' 𝓕, φ.isHaarMeasure_map μ,
    h2.preimage_of_equiv mp.symm.quasiMeasurePreserving e.bijective fun g x => ?_, ?_, fun f => ?_⟩
  · change φ.symm (φ g.1 * x) = g.1 * φ.symm x
    rw [map_mul, φ.symm_apply_apply]
  · rw [ψ.map_apply, ← Set.preimage_comp, ψ.symm_comp_self, Set.preimage_id]
  · exact mp.symm.setIntegral_preimage_emb ψ.symm.measurableEmbedding (fun u : N => f u.1) 𝓕

end Abs

variable {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁}

theorem UnipGood.integrable {N : Subgroup (UA σ W.J)} (hN : UnipGood N) {μ : Measure N} {𝓕 : Set N} (hμ : μ.IsHaarMeasure)
    (h𝓕 : IsFundamentalDomain ((ratU σ W.J).subgroupOf N) 𝓕 μ) {f : UA σ W.J → ℂ} (hf : IsAut f) (h : UA σ W.J) :
    IntegrableOn (fun u : N => f (u.1 * h)) 𝓕 μ := by
  obtain ⟨C, hC, hc⟩ := hN.cov
  have c : Continuous fun u : N => f (u.1 * h) := hf.1.comp (continuous_subtype_val.mul continuous_const)
  obtain ⟨b, hb⟩ := hC.exists_bound_of_continuousOn c.continuousOn
  refine Measure.integrableOn_of_bounded (hN.fin μ 𝓕 hμ h𝓕).2.ne c.aestronglyMeasurable (M := b)
    (Filter.Eventually.of_forall fun u => ?_)
  obtain ⟨γ, h1, h2⟩ := hc u
  have := hb _ h2
  rwa [Subgroup.coe_mul, mul_assoc, hf.2 _ h1] at this

theorem ct_inv (hN : UnipGood (unip σ W H)) {f c : UA σ W.J → ℂ} (hf : IsAut f) (hc : IsCT H f c) {u : UA σ W.J}
    (hu : u ∈ unip σ W H) (h : UA σ W.J) : c (u * h) = c h := by
  obtain ⟨μ, 𝓕, h1, h2, h3⟩ := hN.ex
  have := hN.cnt
  have := hN.right μ h1
  rw [hc μ 𝓕 h1 h2 h3, hc μ 𝓕 h1 h2 h3,
    ← PositivityTheory.ThKF.L2.integral_right h2 (fun v => f (v.1 * h)) (fun γ hγ x => by rw [Subgroup.coe_mul, mul_assoc]; exact hf.2 _ hγ _) ⟨u, hu⟩]
  simp only [Subgroup.coe_mul, mul_assoc]

theorem exists_abs_gt : ∃ t : (AE F E)ˣ, 1 < (absE F E t : ℝ) := by
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨b, h2⟩ : ∃ b : w.Completion, ‖b‖ = 2 := by
    refine ⟨_, (InfinitePlace.Completion.norm_coe w ((WithAbs.equiv w.1).symm (2 : F))).trans ?_⟩
    show w (2 : F) = 2
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.apply, map_ofNat]
    norm_num
  have hne : b ≠ 0 := by
    intro h; rw [h, norm_zero] at h2; norm_num at h2
  refine ⟨GlobalTheory.Doubling.ideleAtInf F E w (Units.map (algebraMap w.Completion (w.Completion ⊗[F] E)).toMonoidHom (Units.mk0 b hne)), ?_⟩
  rw [GlobalTheory.Doubling.absE_ideleAtInf, GlobalTheory.Doubling.absEw_apply]
  change 1 < ((‖Algebra.norm w.Completion (algebraMap w.Completion (w.Completion ⊗[F] E) b)‖₊ ^ w.mult : ℝ≥0) : ℝ)
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, NNReal.coe_pow, coe_nnnorm, norm_pow, h2, ← pow_mul]
  have hn : 0 < Module.finrank F E := Module.finrank_pos
  have hm : 0 < w.mult := by unfold InfinitePlace.mult; split_ifs <;> norm_num
  exact one_lt_pow₀ (by norm_num) (Nat.mul_ne_zero hn.ne' hm.ne')

theorem ctBasic : CTBasic := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H r s hB hW hH
  have hN := unipGood hB.cm (Or.inr hW.skew) (det_ne_zero hW) hH
  refine ⟨fun f g cf cg c hf hg h1 h2 μ 𝓕 k1 k2 k3 h => ?_, fun f T T' χ χ' z z' hf hz hc l l' u hu h => ?_⟩
  · simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    rw [integral_sub (hN.integrable k1 k2 hf h) ((hN.integrable k1 k2 hg h).const_mul c), integral_const_mul,
      h1 μ 𝓕 k1 k2 k3, h2 μ 𝓕 k1 k2 k3]
  · obtain ⟨t, ht⟩ := exists_abs_gt (F := F) (E := E)
    obtain ⟨L1, L2⟩ := leviPlane F E σ hB.cm d d₁ W W₁ H hW.skew hH
    obtain ⟨m, hm⟩ := L1 t 1
    have e1 := ct_inv hN hf hc hu h
    have e2 := ct_inv hN hf hc (L2 t 1 m hm u hu) (m * h)
    rw [show m * u * m⁻¹ * (m * h) = m * (u * h) by group] at e2
    simp only [Pi.add_apply, l t m hm, l' t m hm] at e1 e2
    have ne : (χ t : ℂ) * (((absE F E t : ℝ) ^ z : ℝ) : ℂ) - (χ' t : ℂ) * (((absE F E t : ℝ) ^ z' : ℝ) : ℂ) ≠ 0 := fun k => by
      have := congrArg norm (sub_eq_zero.1 k)
      have p : (0 : ℝ) < absE F E t := zero_lt_one.trans ht
      simp only [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg p.le _)] at this
      exact hz ((Real.rpow_right_inj p ht.ne').1 this)
    have e3 : T (u * h) = T h := sub_eq_zero.1 (mul_left_cancel₀ ne (by
      linear_combination e2 - (χ' t : ℂ) * (((absE F E t : ℝ) ^ z' : ℝ) : ℂ) * e1))
    exact ⟨e3, by linear_combination e1 - e3⟩

theorem ct_conj {d₂ : ℕ} {H₂ : Plane E d d₂} {γ : UA σ W.J} (hγ : γ ∈ ratU σ W.J)
    (hN : ∀ u, u ∈ unip σ W H₂ ↔ γ * u * γ⁻¹ ∈ unip σ W H) {f c : UA σ W.J → ℂ} (hf : IsAut f) (hc : IsCT H₂ f c) :
    IsCT H f fun h => c (γ⁻¹ * h) := by
  intro μ 𝓕 h1 h2 h3 h
  obtain ⟨μ₂, 𝓕₂, k1, k2, k3, k4⟩ := abs_conj hγ hN μ 𝓕 h2
  rw [← k4 fun u => f (u * h)]
  refine (hc _ _ k1 k2 (k3.trans h3) _).trans ?_
  congr 1
  funext u
  rw [mul_assoc, mul_assoc, hf.2 _ hγ]

theorem lineMove : LineMove := by
  rintro F E _ _ _ _ _ σ B d d₁ W W₁ H r s χ z f hB hW hH hf ⟨d₂, W₂, H₂, c, hH₂, hc, hl⟩
  have sk := Or.inr (a := ∀ i j, σ (W.J j i) = W.J i j) hW.skew
  have ne : ∀ {k} {Y : Spc F E k} {P : Plane E d k}, IsPlane σ P W Y → P.x ≠ 0 := fun h h0 => by
    have e := h.xy
    rw [h0, form, zero_dotProduct] at e
    exact zero_ne_one e
  obtain ⟨g, g1, g2⟩ := wittVec F E σ hB.cm d W.J hW.skew (det_ne_zero hW) _ _ (ne hH₂) (ne hH) hH₂.xx hH.xx
  let γ : UA σ W.J := ⟨Matrix.GeneralLinearGroup.map (inclR (F := F) (AF F)) g, by
    change (incM F g.1ᵀ) * incM F W.J * (incM F g.1).map (cA σ) = _
    rw [incM_conj, ← incM_mul, ← incM_mul, g1]⟩
  have hγ : γ ∈ ratU σ W.J := ⟨g, rfl⟩
  have e1 : mat γ *ᵥ incV F H₂.x = (1 : (AE F E)ˣ).1 • incV F H.x := by
    rw [Units.val_one, one_smul, ← g2]; exact incM_mulVec _ _
  have e2 : mat γ⁻¹ *ᵥ incV F H.x = (1 : (AE F E)ˣ).1 • incV F H₂.x := by
    rw [Units.val_one, one_smul] at e1 ⊢; exact inv_vec e1
  refine ⟨_, ct_conj hγ (fun u => ?_) hf hc, fun t m hm h => ?_⟩
  · rw [mem_unip hB.cm sk hH, mem_unip hB.cm sk hH₂]
    exact ⟨fun k => k.conj e1, fun k => by simpa [mul_assoc] using k.conj e2⟩
  · obtain ⟨m₀, h₀⟩ := (leviPlane F E σ hB.cm d d₂ W W₂ H₂ hW.skew hH₂).1 t 1
    have p := ((IsLevi.par (form_yx hB.cm sk hH) hH hm).conj e2).div (IsLevi.par (form_yx hB.cm sk hH₂) hH₂ h₀)
    have := ct_inv (unipGood hB.cm sk (det_ne_zero hW) hH₂) hf hc ((mem_unip hB.cm sk hH₂).2 p) (m₀ * (γ⁻¹ * h))
    rw [hl t m₀ h₀] at this
    rw [← this]
    congr 1
    group

end PositivityTheory.ThKEnd.Grp

end
end

section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.SpanPairIff
section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.Emb2DiaMulVecIncVY
section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.EmbMMul
noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open Matrix GlobalTheory.WeilM

variable {S R d k : Type} [CommRing S] [CommRing R] [Algebra S R] [Fintype d] [DecidableEq d] [Fintype k] [DecidableEq k]

structure Dual (c : R →ₐ[S] R) (J : Matrix d d R) (X Y : Matrix d k R) : Prop where
  cc : ∀ a, c (c a) = a
  skew : (J.map c)ᵀ = -J
  xx : Xᵀ * J * X.map c = 0
  yy : Yᵀ * J * Y.map c = 0
  xy : Xᵀ * J * Y.map c = 1

def embM (c : R →ₐ[S] R) (J : Matrix d d R) (X Y : Matrix d k R) (g g' : Matrix k k R) : Matrix d d R :=
  1 + X * (g - 1) * (J * Y.map c)ᵀ - Y * (g' - 1) * (J * X.map c)ᵀ

variable {c : R →ₐ[S] R} {J : Matrix d d R} {X Y : Matrix d k R}

theorem mapc_mul {a b e : Type} [Fintype b] (A : Matrix a b R) (B : Matrix b e R) : (A * B).map c = A.map c * B.map c := by
  exact Matrix.map_mul (f := c.toRingHom)

theorem mapc_one {a : Type} [DecidableEq a] : (1 : Matrix a a R).map c = 1 := by
  exact Matrix.map_one _ (map_zero c) (map_one c)

theorem Dual.mcc (h : Dual c J X Y) {a b : Type} (A : Matrix a b R) : (A.map c).map c = A := by
  ext i j
  simp only [Matrix.map_apply]
  exact h.cc _

private theorem mapc_transpose {a b : Type} (A : Matrix a b R) : (Aᵀ.map c) = (A.map c)ᵀ := by
  ext i j
  rfl

private theorem mapc_add' {a b : Type} (A B : Matrix a b R) : (A + B).map c = A.map c + B.map c := by
  ext i j
  simp

private theorem mapc_sub' {a b : Type} (A B : Matrix a b R) : (A - B).map c = A.map c - B.map c := by
  ext i j
  simp

theorem Dual.yx (h : Dual c J X Y) : Yᵀ * J * X.map c = -1 := by
  have e : ((Xᵀ * J * Y.map c).map c)ᵀ = (1 : Matrix k k R) := by
    rw [h.xy, mapc_one, transpose_one]
  rw [mapc_mul, mapc_mul, h.mcc, transpose_mul, transpose_mul, h.skew, mapc_transpose, transpose_transpose,
    Matrix.neg_mul, Matrix.mul_neg, ← Matrix.mul_assoc] at e
  exact neg_eq_iff_eq_neg.mp e

theorem tr_mul {e : Type} (Z : Matrix d k R) (T : Matrix d e R) : (J * Z.map c)ᵀ * T = (Tᵀ * J * Z.map c)ᵀ := by
  simp only [transpose_mul, transpose_transpose, Matrix.mul_assoc]

theorem embM_mul {e : Type} (g g' : Matrix k k R) (T : Matrix d e R) :
    embM c J X Y g g' * T = T + X * (g - 1) * (Tᵀ * J * Y.map c)ᵀ - Y * (g' - 1) * (Tᵀ * J * X.map c)ᵀ := by
  simp only [embM, Matrix.sub_mul, Matrix.add_mul, Matrix.one_mul, Matrix.mul_assoc, tr_mul]

theorem Dual.embX (h : Dual c J X Y) (g g' : Matrix k k R) : embM c J X Y g g' * X = X * g := by
  rw [embM_mul, h.xy, h.xx]
  simp only [transpose_one, transpose_zero, Matrix.mul_one, Matrix.mul_zero, sub_zero, Matrix.mul_sub]
  abel

theorem Dual.embY (h : Dual c J X Y) (g g' : Matrix k k R) : embM c J X Y g g' * Y = Y * g' := by
  rw [embM_mul, h.yy, h.yx]
  simp only [transpose_zero, transpose_neg, transpose_one, Matrix.mul_zero, Matrix.mul_neg, Matrix.mul_one, add_zero,
    sub_neg_eq_add, Matrix.mul_sub]
  abel

theorem Dual.emb_mul (h : Dual c J X Y) (g g' f f' : Matrix k k R) :
    embM c J X Y g g' * embM c J X Y f f' = embM c J X Y (g * f) (g' * f') := by
  have hAX : ∀ {e : Type} (M : Matrix k e R), (J * Y.map c)ᵀ * (X * M) = M := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.xy, transpose_one, Matrix.one_mul]
  have hAY : ∀ {e : Type} (M : Matrix k e R), (J * Y.map c)ᵀ * (Y * M) = 0 := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.yy, transpose_zero, Matrix.zero_mul]
  have hBX : ∀ {e : Type} (M : Matrix k e R), (J * X.map c)ᵀ * (X * M) = 0 := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.xx, transpose_zero, Matrix.zero_mul]
  have hBY : ∀ {e : Type} (M : Matrix k e R), (J * X.map c)ᵀ * (Y * M) = -M := by
    intro e M
    rw [← Matrix.mul_assoc, tr_mul, h.yx, transpose_neg, transpose_one, Matrix.neg_mul, Matrix.one_mul]
  have hAX1 : (J * Y.map c)ᵀ * X = 1 := by rw [tr_mul, h.xy, transpose_one]
  have hAY1 : (J * Y.map c)ᵀ * Y = 0 := by rw [tr_mul, h.yy, transpose_zero]
  have hBX1 : (J * X.map c)ᵀ * X = 0 := by rw [tr_mul, h.xx, transpose_zero]
  have hBY1 : (J * X.map c)ᵀ * Y = -1 := by rw [tr_mul, h.yx, transpose_neg, transpose_one]
  simp only [embM, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.mul_assoc, hAX, hAY, hBX, hBY, hAX1, hAY1, hBX1, hBY1, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_neg,
    Matrix.neg_mul, sub_zero, zero_sub, add_zero, zero_add, sub_neg_eq_add, neg_neg]
  abel

theorem Dual.emb_tr (h : Dual c J X Y) (g f : Matrix k k R) :
    (embM c J X Y g (f.map c)ᵀ)ᵀ * J = J * (embM c J X Y f (g.map c)ᵀ).map c := by
  simp only [embM, transpose_add, transpose_sub, transpose_one, transpose_mul, transpose_transpose, mapc_add',
    mapc_sub', mapc_mul, mapc_one, mapc_transpose, h.mcc, h.skew, Matrix.mul_add, Matrix.add_mul, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
  abel

theorem star_mul (g f : GL k R) : ((((g * f)⁻¹).1).map c)ᵀ = ((g⁻¹).1.map c)ᵀ * ((f⁻¹).1.map c)ᵀ := by
  rw [_root_.mul_inv_rev, Units.val_mul, mapc_mul, transpose_mul]

theorem Dual.emb_inv (h : Dual c J X Y) (g : GL k R) :
    embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ * embM c J X Y (g⁻¹).1 ((g⁻¹⁻¹).1.map c)ᵀ = 1 := by
  rw [h.emb_mul, ← star_mul]
  simp [embM, mapc_one]

def Dual.emb (h : Dual c J X Y) : GL k R →* UG c J where
  toFun g := ⟨⟨embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ, embM c J X Y (g⁻¹).1 ((g⁻¹⁻¹).1.map c)ᵀ, h.emb_inv g,
    mul_eq_one_comm.1 (h.emb_inv g)⟩, by
      change (embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ)ᵀ * J * (embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ).map c = J
      have := mul_eq_one_comm.1 (h.emb_inv g)
      rw [inv_inv] at this
      rw [h.emb_tr, Matrix.mul_assoc, ← mapc_mul, this, mapc_one, Matrix.mul_one]⟩
  map_one' := Subtype.ext (Units.ext (by simp [embM]))
  map_mul' g f := Subtype.ext (Units.ext (by
    change embM c J X Y (g.1 * f.1) _ = embM c J X Y g.1 _ * embM c J X Y f.1 _
    rw [h.emb_mul, ← star_mul]))

theorem Dual.emb_val (h : Dual c J X Y) (g : GL k R) : (h.emb g).1.1 = embM c J X Y g.1 ((g⁻¹).1.map c)ᵀ := rfl

theorem Dual.emb_cont [TopologicalSpace R] [IsTopologicalRing R] (h : Dual c J X Y) (hc : Continuous c) : Continuous h.emb := by
  have hE : ∀ {a b : GL k R → Matrix k k R}, Continuous a → Continuous b →
      Continuous fun g => embM c J X Y (a g) (b g) := by
    intro a b ha hb
    simp only [embM]
    fun_prop
  have hv : Continuous fun g : GL k R => (g : Matrix k k R) := Units.continuous_val
  have hi : Continuous fun g : GL k R => ((g⁻¹ : GL k R) : Matrix k k R) := Units.continuous_coe_inv
  have hii : Continuous fun g : GL k R => ((g⁻¹⁻¹ : GL k R) : Matrix k k R) := by
    simpa only [inv_inv] using hv
  rw [continuous_induced_rng]
  refine Units.continuous_iff.mpr ⟨?_, ?_⟩
  · exact (hE hv ((hi.matrix_map hc).matrix_transpose)).congr fun g => (h.emb_val g).symm
  · exact (hE hi ((hii.matrix_map hc).matrix_transpose)).congr fun g => rfl

theorem embM_map {S' R' : Type} [CommRing S'] [CommRing R'] [Algebra S' R'] {c' : R' →ₐ[S'] R'} (f : R →+* R')
    (hf : ∀ a, f (c a) = c' (f a)) (g g' : Matrix k k R) :
    (embM c J X Y g g').map f = embM c' (J.map f) (X.map f) (Y.map f) (g.map f) (g'.map f) := by
  have hfc : (f : R → R') ∘ c = c' ∘ f := funext hf
  simp only [embM, Matrix.map_sub f (map_sub f), Matrix.map_add f (map_add f), Matrix.map_mul,
    Matrix.map_one f (map_zero f) (map_one f), Matrix.transpose_map, Matrix.map_map, hfc]

theorem Dual.map (h : Dual c J X Y) {S' R' : Type} [CommRing S'] [CommRing R'] [Algebra S' R'] {c' : R' →ₐ[S'] R'} (f : R →+* R')
    (hf : ∀ a, f (c a) = c' (f a)) (hc : ∀ a, c' (c' a) = a) : Dual c' (J.map f) (X.map f) (Y.map f) := by
  have hfc : (f : R → R') ∘ c = c' ∘ f := funext hf
  refine ⟨hc, ?_, ?_, ?_, ?_⟩
  · have e := congrArg (fun M => Matrix.map M f) h.skew
    simp only [Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_neg f (map_neg f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e
  · have e := congrArg (fun M => Matrix.map M f) h.xx
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_zero f (map_zero f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e
  · have e := congrArg (fun M => Matrix.map M f) h.yy
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_zero f (map_zero f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e
  · have e := congrArg (fun M => Matrix.map M f) h.xy
    simp only [Matrix.map_mul, Matrix.transpose_map, Matrix.map_map, hfc, Matrix.map_one f (map_zero f) (map_one f)] at e
    simpa only [Matrix.transpose_map, Matrix.map_map] using e

end PositivityTheory.ThKEnd.Two

end
end

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open scoped TensorProduct NNReal Matrix MatrixGroups Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEnd.Grp PositivityTheory.ThKG.Tow.Levi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {d d₁ d₂ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {W₂ : Spc F E d₂} {H : Plane E d d₁} {H₁ : Plane E d₁ d₂}

def cols {R : Type} (x y : Fin d → R) : Matrix (Fin d) (Fin 2) R := Matrix.of fun i j => ![x i, y i] j

theorem cols_vec {R : Type} [CommRing R] (x y : Fin d → R) (c : Fin 2 → R) : cols x y *ᵥ c = c 0 • x + c 1 • y := by
  ext i; simp [cols, Matrix.mulVec, dotProduct, mul_comm]

theorem cols_map (x y : Fin d → E) : (cols x y).map (inclR (F := F) (AF F)) = cols (incV F x) (incV F y) := by
  ext i j; fin_cases j <;> rfl

theorem cols_tr (J : Matrix (Fin d) (Fin d) E) (x y z : Fin d → AE F E) :
    (incM F J * (cols x y).map (cA σ))ᵀ *ᵥ z = ![fa σ J z x, fa σ J z y] := by
  ext j
  fin_cases j <;> exact dotProduct_comm _ _

theorem form_iota (hH : IsPlane σ H W W₁) (u v : Fin d₁ → E) : form σ W.J (H.ι *ᵥ u) (H.ι *ᵥ v) = form σ W₁.J u v := by
  have e : (fun i => σ ((H.ι *ᵥ v) i)) = H.ι.map σ *ᵥ fun i => σ (v i) := funext fun i => RingHom.map_mulVec σ.toRingHom H.ι v i
  rw [form, form, e, ← hH.gram, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]

theorem fa_iota2 (hH : IsPlane σ H W W₁) (u v : Fin d₁ → AE F E) : fa σ W.J (incM F H.ι *ᵥ u) (incM F H.ι *ᵥ v) = fa σ W₁.J u v := by
  have e : (fun i => cA σ ((incM F H.ι *ᵥ v) i)) = incM F (H.ι.map σ) *ᵥ fun i => cA σ (v i) :=
    incM_conj (F := F) (σ := σ) H.ι ▸ funext fun i => RingHom.map_mulVec (cA σ).toRingHom (incM F H.ι) v i
  rw [fa, fa, e, ← hH.gram, incM_mul, incM_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u]
  exact congrArg (· ⬝ᵥ _) (Matrix.vecMul_transpose _ _).symm

theorem fa_iota_y (hH : IsPlane σ H W W₁) (z : Fin d₁ → AE F E) : fa σ W.J (incM F H.ι *ᵥ z) (incV F H.y) = 0 :=
  by
    have e : H.ιᵀ *ᵥ (W.J *ᵥ fun i => σ (H.y i)) = 0 := funext fun j => by
      have := (hH.orth (Pi.single j 1)).2
      rwa [form, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, single_one_dotProduct] at this
    rw [fa, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      show (fun i => cA σ (incV F H.y i)) = incV F fun i => σ (H.y i) from rfl, incM_mulVec,
      show (incM F H.ι)ᵀ = incM F H.ιᵀ from rfl, incM_mulVec, e]
    simp [incV, dotProduct]

variable (h : IsCMExt F E σ) (hJ : ∀ i j, σ (W.J j i) = -W.J i j) (hH : IsPlane σ H W W₁) (hH₁ : IsPlane σ H₁ W₁ W₂)

include h hJ hH hH₁

theorem dual2 : Dual σ W.J (cols H.x (H.ι *ᵥ H₁.x)) (cols H.y (H.ι *ᵥ H₁.y)) := by
  have sk := form_skew (sig_sig h) hJ
  have ent : ∀ (x x' y y' : Fin d → E), (cols x x')ᵀ * W.J * (cols y y').map σ =
      !![form σ W.J x y, form σ W.J x y'; form σ W.J x' y, form σ W.J x' y'] := fun x x' y y' => by
    rw [Matrix.mul_assoc]
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  have o1 : ∀ u, form σ W.J H.x (H.ι *ᵥ u) = 0 := fun u => by rw [sk, (hH.orth u).1, map_zero, neg_zero]
  have o2 : ∀ u, form σ W.J H.y (H.ι *ᵥ u) = 0 := fun u => by rw [sk, (hH.orth u).2, map_zero, neg_zero]
  refine ⟨sig_sig h, Matrix.ext hJ, ?_, ?_, ?_⟩
  · rw [ent, hH.xx, o1, (hH.orth _).1, form_iota hH, hH₁.xx]
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  · rw [ent, hH.yy, o2, (hH.orth _).2, form_iota hH, hH₁.yy]
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  · rw [ent, hH.xy, o1, (hH.orth _).2, form_iota hH, hH₁.xy, Matrix.one_fin_two]

def emb2 : SL(2, AE F E) →* UA σ W.J :=
  ((dual2 h hJ hH hH₁).map (c' := cA σ) (inclR (F := F) (AF F)) (fun _ => rfl) (cA_cA h)).emb.comp Matrix.SpecialLinearGroup.toGL

theorem mat_emb2_eq_embM (g : SL(2, AE F E)) : mat (emb2 h hJ hH hH₁ g) = embM (cA σ) (incM F W.J) (cols (incV F H.x) (incM F H.ι *ᵥ incV F H₁.x))
    (cols (incV F H.y) (incM F H.ι *ᵥ incV F H₁.y)) g.1 ((g⁻¹).1.map (cA σ))ᵀ := by
  rw [incM_mulVec, incM_mulVec, ← cols_map, ← cols_map]; rfl

theorem continuous_SL2_embedding : Continuous (emb2 h hJ hH hH₁) :=
  (Dual.emb_cont ((dual2 h hJ hH hH₁).map (c' := cA σ) (inclR (F := F) (AF F)) (fun _ => rfl) (cA_cA h)) (IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap)).comp Matrix.SpecialLinearGroup.continuous_toGL

theorem emb2_map_inclR (g : SL(2, E)) : emb2 h hJ hH hH₁ (Matrix.SpecialLinearGroup.map (inclR (F := F) (AF F)) g) ∈ ratU σ W.J :=
  (rat_iff _).2 ⟨embM σ W.J (cols H.x (H.ι *ᵥ H₁.x)) (cols H.y (H.ι *ᵥ H₁.y)) g.1 ((g⁻¹).1.map σ)ᵀ, by
    refine Eq.trans ?_ (embM_map (c' := cA σ) (X := cols H.x (H.ι *ᵥ H₁.x)) (Y := cols H.y (H.ι *ᵥ H₁.y)) (inclR (F := F) (AF F))
      (fun _ => rfl) _ _).symm
    rw [mat_emb2_eq_embM, ← map_inv, incM_mulVec, incM_mulVec, ← cols_map, ← cols_map]
    rfl⟩

theorem emb2_mulVec_incV_x_and_complement_x (g : SL(2, AE F E)) :
    mat (emb2 h hJ hH hH₁ g) *ᵥ incV F H.x = g.1 0 0 • incV F H.x + g.1 1 0 • incV F (H.ι *ᵥ H₁.x) ∧
    mat (emb2 h hJ hH hH₁ g) *ᵥ incV F (H.ι *ᵥ H₁.x) = g.1 0 1 • incV F H.x + g.1 1 1 • incV F (H.ι *ᵥ H₁.x) := by
  have e := ((dual2 h hJ hH hH₁).map (c' := cA σ) (inclR (F := F) (AF F)) (fun _ => rfl) (cA_cA h)).embX g.1 ((g⁻¹).1.map (cA σ))ᵀ
  rw [cols_map] at e
  rw [← cols_vec _ _ fun i => g.1 i 0, ← cols_vec _ _ fun i => g.1 i 1, mat_emb2_eq_embM, incM_mulVec, incM_mulVec, ← cols_map H.y]
  exact ⟨funext fun i => congrFun (congrFun e i) 0, funext fun i => congrFun (congrFun e i) 1⟩

theorem emb2_dia_mulVec_incV_y (u : (AE F E)ˣ) : mat (emb2 h hJ hH hH₁ (dia u)) *ᵥ incV F H.y = cA σ (u⁻¹).1 • incV F H.y := by
  have e := ((dual2 h hJ hH hH₁).map (c' := cA σ) (inclR (F := F) (AF F)) (fun _ => rfl) (cA_cA h)).embY (dia u).1
    (((dia u)⁻¹).1.map (cA σ))ᵀ
  rw [cols_map H.y] at e
  rw [mat_emb2_eq_embM, incM_mulVec, incM_mulVec, ← cols_map H.x]
  refine funext fun i => (congrFun (congrFun e i) 0).trans ?_
  rw [← map_inv, dia_val]
  simp [cols, Matrix.mul_apply, mul_comm]

theorem emb2_mulVec_complement_eq (g : SL(2, AE F E)) (z : Fin d₁ → AE F E) : mat (emb2 h hJ hH hH₁ g) *ᵥ (incM F H.ι *ᵥ z) =
    incM F H.ι *ᵥ (z + ((g.1 1 1 - 1) * fa σ W₁.J z (incV F H₁.y)) • incV F H₁.x -
      ((cA σ ((g⁻¹).1 1 1) - 1) * fa σ W₁.J z (incV F H₁.x)) • incV F H₁.y) + (g.1 0 1 * fa σ W₁.J z (incV F H₁.y)) • incV F H.x -
      (cA σ ((g⁻¹).1 1 0) * fa σ W₁.J z (incV F H₁.x)) • incV F H.y := by
  rw [mat_emb2_eq_embM, embM, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec _ (_ * _),
    ← Matrix.mulVec_mulVec _ (_ * _), cols_tr, cols_tr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cols_vec, cols_vec,
    fa_iota hH, fa_iota_y hH, fa_iota2 hH, fa_iota2 hH, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add,
    Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (zero_ne_one (α := Fin 2)), sub_zero, Matrix.transpose_apply,
    Matrix.map_apply]
  abel

theorem emb2_dia_isLevi (hJ₁ : ∀ i j, σ (W₁.J j i) = -W₁.J i j) (u : (AE F E)ˣ) {m : UA σ W₁.J} (hm : IsLevi (W₁ := W₂) H₁ u⁻¹ 1 m) :
    IsLevi H u m (emb2 h hJ hH hH₁ (dia u)) := by
  have e : ∀ z, mat (emb2 h hJ hH hH₁ (dia u)) *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (z + (((u⁻¹).1 - 1) *
      fa σ W₁.J z (incV F H₁.y)) • incV F H₁.x - ((cA σ u.1 - 1) * fa σ W₁.J z (incV F H₁.x)) • incV F H₁.y) := fun z => by
    rw [emb2_mulVec_complement_eq, ← map_inv, dia_val, dia_val]; simp
  have yx : form σ W₁.J H₁.y H₁.x = -1 := by rw [form_skew (sig_sig h) hJ₁, hH₁.xy, map_one]
  refine ⟨by simpa [dia_val] using (emb2_mulVec_incV_x_and_complement_x h hJ hH hH₁ (dia u)).1, emb2_dia_mulVec_incV_y h hJ hH hH₁ u, fr_ext h hJ₁ hH₁ ?_ ?_ ?_⟩
  · refine Matrix.ext_iff_mulVec.2 fun z => ?_
    rw [Matrix.mul_assoc _ (mat m), hm.2.2, mat_one, Matrix.mul_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e,
      fa_iota hH₁, fa_iota_y hH₁]
    simp
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, hm.1, fa_inc, fa_inc, hH₁.xy, hH₁.xx]
    simp [sub_smul]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, hm.2.1, fa_inc, fa_inc, hH₁.yy, yx]
    simp [sub_smul]

end PositivityTheory.ThKEnd.Two

end
end

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open scoped TensorProduct NNReal Matrix MatrixGroups Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEnd.Grp PositivityTheory.ThKG.Tow.Levi
open GlobalTheory.Eis.Conv (halfE)

theorem uniq_sub {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] {Γ S : Subgroup G} (hS : IsClosed (S : Set G))
    (L : Lat (Γ.subgroupOf S)) {f c c' : G → ℂ} (h : IsAv (Γ.subgroupOf S) Subtype.val f c)
    (h' : IsAv (Γ.subgroupOf S) Subtype.val f c') : c = c' := by
  have : LocallyCompactSpace S := hS.isClosedEmbedding_subtypeVal.locallyCompactSpace
  have : SecondCountableTopology S := TopologicalSpace.Subtype.secondCountableTopology _
  exact L.isAv_uniq h h'

theorem first_of (G : Type) [TopologicalSpace G] [SecondCountableTopology G] : FirstCountableTopology G := inferInstance

theorem uni_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (ξ : R) :
    uni (.ofAdd (f ξ)) = Matrix.SpecialLinearGroup.map f (uni (.ofAdd ξ)) :=
  Subtype.ext (Matrix.ext fun i j => by
    fin_cases i <;> fin_cases j
    exacts [(map_one f).symm, rfl, (map_zero f).symm, (map_one f).symm])

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {d d₁ d₂ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {W₂ : Spc F E d₂} {H : Plane E d d₁} {H₁ : Plane E d₁ d₂}

theorem fa_add (J : Matrix (Fin d) (Fin d) E) (w w' z : Fin d → AE F E) (a : AE F E) :
    fa σ J (w + a • w') z = fa σ J w z + a * fa σ J w' z := by
  rw [fa, add_dotProduct, smul_dotProduct]; rfl

theorem incV_lin (x y : Fin d → E) (a b : E) :
    incV F (a • x + b • y) = inclR (F := F) (AF F) a • incV F x + inclR (F := F) (AF F) b • incV F y :=
  funext fun i => by simp [incV]

theorem span_pair_iff {x y : Fin d → E} {z : Fin d → AE F E} : z ∈ Submodule.span (AE F E) (incV F '' (Submodule.span E {x, y} : Set (Fin d → E))) ↔
    ∃ a b : AE F E, a • incV F x + b • incV F y = z := by
  rw [← Submodule.mem_span_pair]
  refine ⟨fun k => Submodule.span_le.2 ?_ k, fun k => Submodule.span_mono ?_ k⟩
  · rintro _ ⟨u, hu, rfl⟩
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hu
    exact Submodule.mem_span_pair.2 ⟨_, _, (incV_lin x y a b).symm⟩
  · rintro _ (rfl | rfl)
    exacts [⟨x, Submodule.subset_span (by simp), rfl⟩, ⟨y, Submodule.subset_span (by simp), rfl⟩]

variable (h : IsCMExt F E σ) (hJ : ∀ i j, σ (W.J j i) = -W.J i j) (hH : IsPlane σ H W W₁) (hH₁ : IsPlane σ H₁ W₁ W₂)

include h hJ hH hH₁

theorem emb2_norm (g : SL(2, E)) : ∀ u ∈ Submodule.span E {H.x, H.ι *ᵥ H₁.x}, ∃ u' ∈ Submodule.span E {H.x, H.ι *ᵥ H₁.x},
    mat (emb2 h hJ hH hH₁ (Matrix.SpecialLinearGroup.map (inclR (F := F) (AF F)) g)) *ᵥ incV F u = incV F u' := fun u hu => by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hu
  refine ⟨_, Submodule.mem_span_pair.2 ⟨a * g.1 0 0 + b * g.1 0 1, a * g.1 1 0 + b * g.1 1 1, rfl⟩, ?_⟩
  rw [incV_lin, incV_lin, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, (emb2_mulVec_incV_x_and_complement_x h hJ hH hH₁ _).1, (emb2_mulVec_incV_x_and_complement_x h hJ hH hH₁ _).2]
  simp only [map_add (f := _), map_mul, smul_add, add_smul, smul_smul]
  exact add_add_add_comm _ _ _ _

theorem mem_pair (hJ₁ : ∀ i j, σ (W₁.J j i) = -W₁.J i j) {u : UA σ W.J} {y : UA σ W₁.J} (hx : mat u *ᵥ incV F H.x = incV F H.x)
    (hy : ∀ z, ∃ a : AE F E, mat u *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat y *ᵥ z) + a • incV F H.x) :
    u ∈ unipU σ W (Submodule.span E {H.x, H.ι *ᵥ H₁.x}) ↔
      y ∈ unip σ W₁ H₁ ∧ mat u *ᵥ incV F (H.ι *ᵥ H₁.x) = incV F (H.ι *ᵥ H₁.x) := by
  have m0 : H.x ∈ Submodule.span E {H.x, H.ι *ᵥ H₁.x} := Submodule.subset_span (by simp)
  have m1 : H.ι *ᵥ H₁.x ∈ Submodule.span E {H.x, H.ι *ᵥ H₁.x} := Submodule.subset_span (by simp)
  rw [unipLine F E σ h _ _ _ _ H₁ (Or.inr hJ₁) hH₁, (unipU_eq _).choose_spec.choose_spec.2, (unipU_eq _).choose_spec.choose_spec.2]
  constructor
  · rintro ⟨k1, k2⟩
    have e1 : mat y *ᵥ incV F H₁.x = incV F H₁.x := by
      obtain ⟨a, ha⟩ := hy (incV F H₁.x)
      rw [incM_mulVec H.ι H₁.x, k1 _ m1, ← incM_mulVec] at ha
      exact (iota_inj h hJ hH (a := 0) ((congrArg _ (zero_smul _ _)).trans ((add_zero _).trans ha))).symm
    refine ⟨⟨fun v hv => ?_, fun z hz => ?_⟩, k1 _ m1⟩
    · obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
      have : incV F (a • H₁.x) = inclR (F := F) (AF F) a • incV F H₁.x := funext fun i => map_mul _ _ _
      rw [this, Matrix.mulVec_smul, e1]
    · obtain ⟨a, b, hab⟩ := span_pair_iff.1 (k2 (H.ι *ᵥ z) fun v hv => by
        obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
        refine inc_inj (F := F) ?_
        have z1 := congrArg (inclR (F := F) (AF F)) (hz _ (Submodule.mem_span_singleton_self _))
        rw [← fa_inc, map_zero] at z1
        have : ∀ w p q : Fin d → AE F E, fa σ W.J w (p + q) = fa σ W.J w p + fa σ W.J w q := fun w p q => by
          simp only [fa, Pi.add_apply, map_add (f := _)]
          rw [← dotProduct_add, ← Matrix.mulVec_add]; rfl
        rw [← fa_inc, incV_lin, this, fa_smul, fa_smul, ← incM_mulVec, ← incM_mulVec, fa_iota hH, fa_iota2 hH, z1]
        simp)
      obtain ⟨c, hc⟩ := hy (incV F z)
      rw [← incM_mulVec, ← incM_mulVec, hc] at hab
      have := iota_inj h hJ hH (z := mat y *ᵥ incV F z - incV F z) (z' := b • incV F H₁.x) (a := c) (a' := a) (by
        rw [Matrix.mulVec_sub, Matrix.mulVec_smul, add_comm (b • _), hab]; abel)
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.mem_span_singleton_self _, rfl⟩)
  · rintro ⟨k, k3⟩
    rw [← (unipU_eq _).choose_spec.choose_spec.2, ← unipLine F E σ h _ _ _ _ H₁ (Or.inr hJ₁) hH₁, mem_unip h (Or.inr hJ₁) hH₁] at k
    refine ⟨fun v hv => ?_, fun z hz => ?_⟩
    · obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hv
      rw [incV_lin, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hx, k3]
    · obtain ⟨w, a, e⟩ := exists_decomp_of_fa_incV_x_eq_zero (form_yx h (Or.inr hJ) hH) hH (w := incV F z) (by rw [fa_inc, hz _ m0, map_zero])
      have z1 : fa σ W₁.J w (incV F H₁.x) = 0 := by
        have := congrArg (inclR (F := F) (AF F)) (hz _ m1)
        rwa [← fa_inc, e, fa_add, fa_inc, form_skew (sig_sig h) hJ, (hH.orth _).1, ← incM_mulVec, fa_iota2 hH, map_zero, neg_zero,
          map_zero, mul_zero, add_zero] at this
      obtain ⟨b, hb⟩ := k.2 w z1
      obtain ⟨c, hc⟩ := hy w
      refine span_pair_iff.2 ⟨c, b, ?_⟩
      rw [e, Matrix.mulVec_add, hc, hb, Matrix.mulVec_smul, hx, Matrix.mulVec_add, Matrix.mulVec_smul, incM_mulVec]
      abel


set_option maxHeartbeats 800000 in
theorem two_orders [MeasurableSpace (Multiplicative (AE F E))] [BorelSpace (Multiplicative (AE F E))] (hd : W.J.det ≠ 0)
    (hJ₁ : ∀ i j, σ (W₁.J j i) = -W₁.J i j) {f c₀ c φ c' : UA σ W.J → ℂ} (hf : IsAut f)
    (h0 : IsCT H f c₀) (h1 : ∀ lev : UA σ W₁.J → UA σ W.J, (∀ y, IsLevi H 1 y (lev y)) →
      IsAv ((ratU σ W₁.J).subgroupOf (unip σ W₁ H₁)) (fun u => lev u.1) c₀ c)
    (hφ : IsAv ((ratU σ W.J).subgroupOf (unipU σ W (Submodule.span E {H.x, H.ι *ᵥ H₁.x}))) Subtype.val f φ)
    (hc' : IsAv ((inclR (F := F) (E := E) (AF F)).toAddMonoidHom.toMultiplicative).range ((emb2 h hJ hH hH₁).comp uni) φ c') :
    c = c' := by
  obtain ⟨-, i1, i2, i3⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J
  obtain ⟨-, j1, j2, j3⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d₁ W₁.J
  obtain ⟨k1, k2, hC, LR⟩ := ae_facts h
  have := PositivityTheory.ThKF.countable_ratU σ W.J
  have : DiscreteTopology (ratU σ W.J) := PositivityTheory.ThKF.discrete_ratU h (ε := -1) (fun i j => by simp [hJ]) hd
  have : DiscreteTopology (ratU σ W₁.J) := PositivityTheory.ThKF.discrete_ratU h (ε := -1) (fun i j => by simp [hJ₁]) hH.nondeg
  have G0 := unipGood h (Or.inr hJ) hd hH
  have G1 := unipGood h (Or.inr hJ₁) hH.nondeg hH₁
  have G2 := (unipUGood F E σ h d W (Or.inr hJ) hd (Submodule.span E {H.x, H.ι *ᵥ H₁.x})).1
  have := G1.lc
  have := G1.sc
  have : SecondCountableTopology (Multiplicative (AE F E)) := k2
  have : T2Space (Multiplicative (AE F E)) := t2AE
  obtain ⟨lev, ρ, c1, c2, v1, v2, v3, v4⟩ := levi_data h hJ hH
  have ρeq : ∀ u y, (∀ z, ∃ a : AE F E, mat u.1 *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat y *ᵥ z) + a • incV F H.x) → ρ u = y :=
    fun u y k => mat_inj (Matrix.ext_iff_mulVec.2 fun z => by
      obtain ⟨a, ha⟩ := v4 u z
      obtain ⟨b, hb⟩ := k z
      exact iota_inj h hJ hH (ha.symm.trans hb))
  let S : Subgroup (UA σ W.J) := ((unip σ W₁ H₁).comap ρ).map (stab σ W H.x).subtype
  have mS : ∀ u (hu : u ∈ stab σ W H.x), ρ ⟨u, hu⟩ ∈ unip σ W₁ H₁ → u ∈ S := fun u hu k => ⟨⟨u, hu⟩, k, rfl⟩
  have sS : S ≤ stab σ W H.x := Subgroup.map_subtype_le _
  have rS : ∀ u : S, ρ (Subgroup.inclusion sS u) ∈ unip σ W₁ H₁ := by
    rintro ⟨_, u, hu, rfl⟩
    exact hu
  have cS : IsClosed (S : Set (UA σ W.J)) := (stab_closed H.x).isClosedEmbedding_subtypeVal.isClosedMap _ (G1.closed.preimage c2)
  have cI : Continuous (Subgroup.inclusion sS) := continuous_subtype_val.subtype_mk _
  have k0 : ∀ u (hu : u ∈ stab σ W H.x), ρ ⟨u, hu⟩ = 1 ↔ u ∈ unip σ W H := fun u hu => by
    refine ⟨fun k => Subgroup.subset_closure ⟨hu, fun z => ?_⟩, fun k => ρeq _ _ fun z => ?_⟩
    · simpa only [k, mat_one, Matrix.one_mulVec] using v4 ⟨u, hu⟩ z
    · rw [mat_one, Matrix.one_mulVec]
      exact ((mem_unip h (Or.inr hJ) hH).1 k).2 _ (fa_iota hH z)
  have ls : ∀ y, lev y ∈ stab σ W H.x := fun y => (v1 y).1.trans (one_smul _ _)
  have lρ : ∀ y, ρ ⟨lev y, ls y⟩ = y := fun y => ρeq _ _ fun z =>
    ⟨0, by rw [zero_smul, add_zero, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, (v1 y).2.2]⟩
  obtain ⟨LS, st1⟩ := stage_sub (Γ := ratU σ W.J) (ΓB := (ratU σ W₁.J).subgroupOf (unip σ W₁ H₁)) cS G0.closed
    (fun u hu => mS u (((mem_unip h (Or.inr hJ) hH).1 hu).1.trans (one_smul _ _)) ((k0 _ _).2 hu ▸ one_mem _))
    (ι := lev.comp (unip σ W₁ H₁).subtype) (c1.comp continuous_subtype_val) (fun b => mS _ (ls b) ((lρ b).symm ▸ b.2))
    (π := (ρ.comp (Subgroup.inclusion sS)).codRestrict _ rS) ((c2.comp cI).subtype_mk _) (fun b => Subtype.ext (lρ b))
    (fun s => Subtype.ext_iff.trans (k0 _ _)) (fun b hb => v2 _ hb) (fun s hs => v3 _ hs) (lat_of_good G0) (lat_of_good G1)
  have A1 := st1 f c₀ c hf.1 hf.2 h0 (h1 lev v1)
  let m := emb2 h hJ hH hH₁
  have mc : Continuous m := continuous_SL2_embedding h hJ hH hH₁
  let x₁ := incV F (H.ι *ᵥ H₁.x)
  have xy : fa σ W.J (incV F H.x) (incV F H.y) = 1 := by rw [fa_inc, hH.xy, map_one]
  have x1y : fa σ W.J x₁ (incV F H.y) = 0 := by rw [fa_inc, (hH.orth _).2, map_zero]
  have act : ∀ s : S, mat s.1 *ᵥ x₁ = x₁ + fa σ W.J (mat s.1 *ᵥ x₁) (incV F H.y) • incV F H.x := fun s => by
    obtain ⟨a, ha⟩ := v4 (Subgroup.inclusion sS s) (incV F H₁.x)
    rw [((mem_unip h (Or.inr hJ₁) hH₁).1 (rS s)).1, Units.val_one, one_smul, incM_mulVec] at ha
    change mat s.1 *ᵥ x₁ = x₁ + _ at ha
    rw [ha, fa_add, x1y, xy, zero_add, mul_one]
  let π : S →* Multiplicative (AE F E) := MonoidHom.mk' (fun s => .ofAdd (fa σ W.J (mat s.1 *ᵥ x₁) (incV F H.y))) fun s t => by
    rw [← ofAdd_add, Subgroup.coe_mul, mat_mul, ← Matrix.mulVec_mulVec]
    conv_lhs => rw [act t, Matrix.mulVec_add, Matrix.mulVec_smul, sS s.2, fa_add, xy, mul_one]
  have ns : ∀ b, m (uni b) ∈ stab σ W H.x := fun b => (emb2_mulVec_incV_x_and_complement_x h hJ hH hH₁ (uni b)).1.trans (by simp [uni_val])
  have nρ : ∀ b, ρ ⟨m (uni b), ns b⟩ = 1 := fun b => ρeq _ _ fun z => ⟨b.toAdd * fa σ W₁.J z (incV F H₁.y), by
    change mat (emb2 h hJ hH hH₁ _) *ᵥ _ = _
    rw [emb2_mulVec_complement_eq, ← map_inv, uni_val, uni_val]; simp [mat_one]⟩
  have ur := uni_map (inclR (F := F) (E := E) (AF F))
  obtain ⟨-, st2⟩ := stage_sub (Γ := ratU σ W.J) (ΓB := ((inclR (F := F) (E := E) (AF F)).toAddMonoidHom.toMultiplicative).range) cS
    G2.closed (fun u hu => by
      have hx : u ∈ stab σ W H.x := ((unipU_eq _).choose_spec.choose_spec.2 u).1 hu |>.1 _ (Submodule.subset_span (by simp))
      exact mS u hx ((mem_pair h hJ hH hH₁ hJ₁ hx (v4 ⟨u, hx⟩)).1 hu).1)
    (ι := m.comp uni) (mc.comp continuous_uni) (fun b => mS _ (ns b) (nρ b ▸ one_mem _)) (π := π)
    (continuous_ofAdd.comp (((continuous_mat.comp continuous_subtype_val).matrix_mulVec continuous_const).dotProduct continuous_const))
    (fun b => by
      change Multiplicative.ofAdd (fa σ W.J (mat (emb2 h hJ hH hH₁ (uni b)) *ᵥ x₁) _) = b
      rw [(emb2_mulVec_incV_x_and_complement_x h hJ hH hH₁ _).2, add_comm, uni_val]
      simp [fa_add, xy, x1y, x₁])
    (fun s => by
      rw [mem_pair h hJ hH hH₁ hJ₁ (sS s.2) (v4 (Subgroup.inclusion sS s)), and_iff_right (rS s)]
      refine ⟨fun k => ?_, fun k => congrArg Multiplicative.ofAdd ((congrArg (fa σ W.J · _) k).trans x1y)⟩
      have := act s
      rwa [show fa σ W.J (mat s.1 *ᵥ x₁) (incV F H.y) = 0 from k, zero_smul, add_zero] at this)
    (by
      rintro _ ⟨ξ, rfl⟩
      exact (congrArg m (ur ξ.toAdd)).symm ▸ emb2_map_inclR h hJ hH hH₁ _)
    (fun s hs => by
      obtain ⟨A, hA⟩ := (rat_iff _).1 hs
      refine ⟨.ofAdd (form σ W.J (A *ᵥ (H.ι *ᵥ H₁.x)) H.y), congrArg Multiplicative.ofAdd ?_⟩
      rw [hA, incM_mulVec, fa_inc]; rfl) (lat_of_good G2) LR
  exact uniq_sub cS LS A1 (st2 f φ c' hf.1 hf.2 hφ hc')


set_option maxHeartbeats 800000 in
theorem two_kill (hd : W.J.det ≠ 0) (hJ₁ : ∀ i j, σ (W₁.J j i) = -W₁.J i j) {f c₀ c : UA σ W.J → ℂ} (hf : IsAut f) (hm : Mod f)
    (h0 : IsCT H f c₀) (h1 : ∀ lev : UA σ W₁.J → UA σ W.J, (∀ y, IsLevi H 1 y (lev y)) →
      IsAv ((ratU σ W₁.J).subgroupOf (unip σ W₁ H₁)) (fun u => lev u.1) c₀ c) {l : ℂ} (hl : ‖l‖ < 1) {a : UA σ W.J}
    (ha : a = emb2 h hJ hH hH₁ (dia (halfE F E)⁻¹)) (law : ∀ x, c (a * (a * x)) - c (a * x) = l * (c (a * x) - c x)) (x : UA σ W.J) :
    c (a * x) = c x := by
  obtain ⟨-, i1, i2, i3⟩ := GlobalTheory.UnitaryAdelicTop.lcsc_UA F E σ d W.J
  obtain ⟨k1, k2, hC, LR⟩ := ae_facts h
  obtain ⟨l1, l2, l3⟩ := sl_facts (R := AE F E)
  have := PositivityTheory.ThKF.countable_ratU σ W.J
  have : DiscreteTopology (ratU σ W.J) := PositivityTheory.ThKF.discrete_ratU h (ε := -1) (fun i j => by simp [hJ]) hd
  have G2 := (unipUGood F E σ h d W (Or.inr hJ) hd (Submodule.span E {H.x, H.ι *ᵥ H₁.x})).1
  have := G2.lc
  have := G2.sc
  letI : MeasurableSpace (Multiplicative (AE F E)) := borel _
  have : BorelSpace (Multiplicative (AE F E)) := ⟨rfl⟩
  have : SecondCountableTopology (Multiplicative (AE F E)) := k2
  have : T2Space (Multiplicative (AE F E)) := t2AE
  letI : MeasurableSpace SL(2, AE F E) := borel _
  have : BorelSpace SL(2, AE F E) := ⟨rfl⟩
  have := first_of (UA σ W.J)
  let m := emb2 h hJ hH hH₁
  have mc : Continuous m := continuous_SL2_embedding h hJ hH hH₁
  have ur := uni_map (inclR (F := F) (E := E) (AF F))
  obtain ⟨φ, hφ⟩ := (lat_of_good G2).isAv_ex (ι := Subgroup.subtype _) (f := f) fun γ hγ => hf.2 _ hγ
  have φc : Continuous φ := hφ.cont (lat_of_good G2) continuous_subtype_val hf.1 fun γ hγ => hf.2 _ hγ
  have φi : ∀ γ ∈ (Matrix.SpecialLinearGroup.map (n := Fin 2) (inclR (F := F) (E := E) (AF F))).range, ∀ x, φ (m γ * x) = φ x := by
    rintro _ ⟨g, rfl⟩
    have r := emb2_map_inclR h hJ hH hH₁ g
    have n1 := emb2_norm h hJ hH hH₁ g
    have n2 := emb2_norm h hJ hH hH₁ g⁻¹
    rw [map_inv, map_inv] at n2
    exact IsAv.conj_sub G2.closed (lat_of_good G2) hφ r (fun u => conj_unipU r n1 n2)
      (fun u hu => by simpa using conj_unipU (inv_mem r) n2 (by simpa using n1) hu) (hf.2 _ r)
  have φu : ∀ γ ∈ ((inclR (F := F) (E := E) (AF F)).toAddMonoidHom.toMultiplicative).range, ∀ x, φ ((m.comp uni) γ * x) = φ x := by
    rintro _ ⟨ξ, rfl⟩
    exact φi _ ⟨_, (ur ξ.toAdd).symm⟩
  obtain ⟨c', hc'⟩ := LR.isAv_ex φu
  obtain rfl : c = c' := two_orders h hJ hH hH₁ hd hJ₁ hf h0 h1 hφ hc'
  have cc := hc'.cont LR (mc.comp continuous_uni) φc φu
  obtain ⟨lam, _, hlam⟩ := LR.isAv_prob (H := UA σ W.J)
  obtain ⟨k, hk⟩ := (hm.av G2 hf.2 hφ).gr mc (dia (halfE F E)⁻¹) x
  have D : Dat _ uni (dia (halfE F E)⁻¹) lam l (fun g => φ (m g * x)) fun g => c (m g * x) :=
    ⟨by fun_prop, fun γ hγ g => by rw [map_mul, mul_assoc, φi γ hγ], by fun_prop,
      fun g => by simp only [hlam _ φ c hc', map_mul, mul_assoc]; rfl,
      fun g => by simpa only [map_mul, mul_assoc, ha] using law (m g * x)⟩
  simpa [ha] using kill hC continuous_uni hl D hk 1

end PositivityTheory.ThKEnd.Two

end
end

section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.SigSplitOf
section -- merged from Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.SigSplit
noncomputable section

namespace PositivityTheory.ThKEnd.Two

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

def SigMod : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ f ∈ Sig B G om om', IsModerate ht f

def SigSplit : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → 1 ≤ G.p + G.q →
    ∃ (d₁ : ℕ) (W₁ : Spc F E d₁) (H : Plane E (a + a') d₁), IsPlane σ H G.W W₁ ∧ ∀ f ∈ Sig B G om om', ∃ fa fb, Split2 W₁ H X f fa fb

end PositivityTheory.ThKEnd.Two

end
end

noncomputable section

namespace PositivityTheory.ThKEnd.Two

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG

theorem sigMod_of (hW : WeilConv) (hD : KDecay) : SigMod := by
  rintro F E _ _ _ _ _ σ B a a' G X om om' t _ ⟨Φ, hΦ, Φ', hΦ', rfl⟩
  obtain ⟨-, C, k, h1⟩ := (hW F E σ B _ _ _ _ _ _ _ _ _ _ _ _ (pairV t) (weilCondV t)).1 Φ (polData_le t.geo.hM hΦ)
  obtain ⟨C', k', h2⟩ := ((hD F E σ B a a' G X om om' t).2 Φ' hΦ'.2).2.2
  refine ⟨max C 0 + max C' 0, max k k', fun h => ?_⟩
  have o : (1 : ℝ) ≤ ht h := by exact_mod_cast one_le_heightGL F h.1
  rw [add_mul]
  refine (norm_sub_le _ _).trans (add_le_add (((norm_integral_le_integral_norm _).trans (h1 h)).trans ?_) ((h2 h).trans ?_))
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ o (le_max_left _ _)) (by positivity) (le_max_right _ _)
  · exact mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ o (le_max_right _ _)) (by positivity) (le_max_right _ _)

theorem split_sub {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {B : Base F E}
    {a a' d₁ r s : ℕ} {W : Spc F E (a + a')} {W₁ : Spc F E d₁} {H : Plane E (a + a') d₁} {X : Chars F E} (hC : CTBasic)
    (hB : B.IsGood σ) (hW : W.IsSkew σ B r s) (p : IsPlane σ H W W₁) {f g fa fb ga gb : UA σ W.J → ℂ} (hf : IsAut f) (hg : IsAut g)
    (k1 : Split2 W₁ H X f fa fb) (k2 : Split2 W₁ H X g ga gb) (y : UA σ W.J) :
    ∃ A C, Split2 W₁ H X (fun x => (f - g) (x * y)) A C := by
  have k3 := isCT_right ((hC F E σ B _ _ _ _ H _ _ hB hW p).1 _ _ _ _ 1 hf hg k1.1 k2.1) y
  refine ⟨_, _, ?_, hasLaw_right (hasLaw_sub k1.2.1 k2.2.1 1) y, hasLaw_right (hasLaw_sub k1.2.2 k2.2.2 1) y⟩
  rw [one_smul, one_smul] at k3
  convert k3 using 1
  funext x
  simp only [Pi.add_apply, Pi.sub_apply, one_smul]
  ring

theorem sigSplit_of (hS : SplitEx) (hP : Tow.PlaneSkew) (hI : Iwa) (hC : CTBasic) (hA : IAut) (hR : SigRe) : SigSplit := by
  intro F E _ _ _ _ _ σ B a a' G X om om' t hy
  have g := t.geo
  have := g.aBig
  have := g.lt
  obtain ⟨Y, W₁, H, h1, -, h2⟩ := hP F E σ B t.base (a + a') (a + a' - 2) (by omega) (by omega) G.W _ _ (by omega) hy g.hW 0 1
    one_pos (by omega)
  have t' : IsTriple B (reG G G.V G.V' Y) X om om' :=
    ⟨t.base, ⟨g.lt, g.even, g.kappa, g.eBig, g.aBig, g.hV, g.hV', h1, ⟨g.hM.rat, g.hM.vac, g.hM.std, g.hM.haar, g.hM.dom⟩,
      ⟨g.hM'.rat, g.hM'.vac, g.hM'.std, g.hM'.haar, g.hM'.dom⟩⟩, t.chars, t.weil, t.weil'⟩
  have p := (hI F E σ B _ _ _ _ H _ _ _ _ t.base h1 h2).1
  obtain ⟨h₀, hh⟩ := hR F E σ B a a' G X om om' t _ _ _ t'
  refine ⟨_, W₁, H, ⟨p.rank, p.xx, p.yy, p.xy, p.orth, p.gram, p.nondeg⟩, fun f hf => ?_⟩
  obtain ⟨Φ, hΦ, Φ', hΦ', e⟩ := hh f hf
  obtain ⟨s1, s2⟩ := hS F E σ B a a' (reG G G.V G.V' Y) X om om' t' _ W₁ H _ _ h2
  obtain ⟨⟨fa, fb⟩, k1, -⟩ := s1 Φ hΦ
  obtain ⟨⟨fa', fb'⟩, k2, -⟩ := s2 Φ' hΦ'
  obtain ⟨a1, a2⟩ := hA F E σ B a a' (reG G G.V G.V' Y) X om om' t'
  have k3 := split_sub (W := (reG G G.V G.V' Y).W) hC t.base h1 p (a1 Φ hΦ) (a2 Φ' hΦ') k1 k2 h₀⁻¹
  have e' : f = _ := funext fun y => (congrArg f (inv_mul_cancel_right y h₀).symm).trans (congrFun e (y * h₀⁻¹))
  rw [e']
  exact k3

end PositivityTheory.ThKEnd.Two

end
end

noncomputable section

namespace PositivityTheory.ThKEnd.Two

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKG PositivityTheory.ThKEnd.Grp PositivityTheory.ThKG.Tow.Levi
open GlobalTheory.Doubling (absE)
open GlobalTheory.Eis.Conv (halfE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem split_move {a a' d₁ : ℕ} {W : Spc F E (a + a')} {W₁ : Spc F E d₁} {H : Plane E (a + a') d₁} {X : Chars F E}
    {f fa fb g : UA σ W.J → ℂ} (h : Split2 W₁ H X f fa fb) (c : ℂ) (y : UA σ W.J) (e : ∀ x, c * f (x * y) = g x) :
    Split2 W₁ H X g (fun x => c * fa (x * y)) fun x => c * fb (x * y) :=
  funext e ▸ split2_smul (f := fun x => f (x * y)) ⟨isCT_right h.1 y, hasLaw_right h.2.1 y, hasLaw_right h.2.2 y⟩ c

theorem twoStep_of' (hM : SigMod) (hS : SigSplit) (hI : Iwa) (hA : IAut) : TwoStep := by
  intro F E _ _ _ _ _ σ B b a' G G₁ X om om' om₁ om₁' H H' t t₁ hC hq f hf fa hs hlow k hk f₁ hf₁ hL
  have cm := t.base.cm
  have hJ := t.geo.hW.skew
  have hJ₁ := t₁.geo.hW.skew
  have hd := det_ne_zero t.geo.hW
  obtain ⟨pl, iw⟩ := hI F E σ B _ _ _ _ H' _ _ _ _ t.base t.geo.hW hC.hH'
  obtain ⟨d₂, W₂, H₁, pl₁, sp⟩ := hS F E σ B b a' G₁ X om₁ om₁' t₁ (by have := hC.eq; omega)
  have aut := sig_isAut hA t hf
  have h0 : IsCT H' f fa := by simpa using hs.1
  obtain ⟨lev, -, -, -, v1, -⟩ := levi_data cm hJ pl
  have com : ∀ {s m} y, IsLevi (W₁ := G₁.W) H' s 1 m → lev y * m = m * lev y := fun y hm =>
    levi_uniq cm hJ pl (by simpa using levi_mul (v1 y) hm) (by simpa using levi_mul hm (v1 y))
  have low : ∀ {k f₁}, IsLow H' fa k f₁ → ∀ y z, fa (lev z * (lev y * k)) = f₁ (z * y) := fun h y z => by
    rw [h _ _ (v1 _), map_mul, mul_assoc]
  have ex : ∀ x, ∃ A C, Split2 W₂ H₁ X (fun y => fa (lev y * x)) A C := fun x => by
    obtain ⟨u, hu, s, m, y, l, κ, hκ, hm, hl, rfl⟩ := iw x
    obtain rfl := levi_uniq cm hJ pl hl (v1 y)
    obtain ⟨g, hg, hg'⟩ := hlow κ hκ
    obtain ⟨A, C, h⟩ := sp g hg
    refine ⟨_, _, split_move h ((X.α s : ℂ) * (((absE F E s : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ)) y fun z => ?_⟩
    rw [← low hg', ← hs.2.1 s m hm, ← mul_assoc m, ← com z hm, ← ct_inv (unipGood cm (Or.inr hJ) hd pl) aut h0
      ((leviPlane F E σ cm _ _ _ _ H' hJ pl).2 _ _ _ (v1 z) u hu)]
    congr 1
    group
  choose A C hAC using ex
  obtain ⟨μ, 𝓕, m1, m2, m3⟩ := (unipGood cm (Or.inr hJ₁) pl.nondeg pl₁).ex
  have val : ∀ {x A' C'}, Split2 W₂ H₁ X (fun y => fa (lev y * x)) A' C' → A x 1 + C x 1 = A' 1 + C' 1 := fun {x _ _} h =>
    ((hAC x).1 μ 𝓕 m1 m2 m3 1).trans (h.1 μ 𝓕 m1 m2 m3 1).symm
  obtain ⟨u, hu⟩ : ∃ u, u = (halfE F E)⁻¹ := ⟨_, rfl⟩
  obtain ⟨m, hm⟩ := (leviPlane F E σ cm _ _ _ W₂ H₁ hJ₁ pl₁).1 u⁻¹ 1
  obtain ⟨m₀, hm₀⟩ := (leviPlane F E σ cm _ _ _ G₁.W H' hJ pl).1 u 1
  have ea : m₀ * lev m = emb2 cm hJ pl pl₁ (dia u) :=
    levi_uniq cm hJ pl (by simpa using levi_mul hm₀ (v1 m)) (emb2_dia_isLevi cm hJ pl pl₁ hJ₁ u hm)
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = absE F E u := ⟨_, rfl⟩
  have r1 : 1 < r := by
    rw [hr, hu, map_inv, GlobalTheory.Eis.Conv.absE_halfE F E σ cm, inv_inv]
    exact_mod_cast one_lt_pow₀ (by norm_num) Fintype.card_ne_zero
  have r0 : 0 < r := one_pos.trans r1
  obtain ⟨l, hl⟩ : ∃ l : ℂ, l = (X.α u : ℂ) * ((r ^ ((a' : ℝ) / 2) : ℝ) : ℂ) * ((X.β u⁻¹ : ℂ) * ((r⁻¹ ^ ((b : ℝ) / 2) : ℝ) : ℂ)) :=
    ⟨_, rfl⟩
  have l1 : ‖l‖ < 1 := by
    have : (a' : ℝ) < b := by exact_mod_cast t₁.geo.lt
    rw [hl]
    simp only [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real]
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity), Real.inv_rpow r0.le, mul_inv_lt_iff₀ (by positivity),
      one_mul]
    exact Real.rpow_lt_rpow_of_exponent_lt r1 (by linarith)
  have step : ∀ {x A' C'}, Split2 W₂ H₁ X (fun y => fa (lev y * x)) A' C' → ∃ A'' C'',
      Split2 W₂ H₁ X (fun y => fa (lev y * (m₀ * lev m * x))) A'' C'' ∧ A'' 1 = A' 1 ∧ C'' 1 = l * C' 1 := fun {x A' C'} h => by
    refine ⟨_, _, split_move h ((X.α u : ℂ) * (((absE F E u : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ)) m fun z => ?_, ?_, ?_⟩
    · rw [← hs.2.1 u m₀ hm₀, map_mul, ← mul_assoc, ← mul_assoc, ← com z hm₀]
      simp only [mul_assoc]
    · have := h.2.1 _ m hm 1
      rw [mul_one] at this
      rw [one_mul, this, map_inv, map_inv, NNReal.coe_inv, ← hr, Real.inv_rpow r0.le, Circle.coe_inv, Complex.ofReal_inv]
      have a1 : (X.α u : ℂ) ≠ 0 := Circle.coe_ne_zero _
      have a2 : ((r ^ ((a' : ℝ) / 2) : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (by positivity)
      field_simp
    · have := h.2.2 _ m hm 1
      rw [mul_one] at this
      rw [one_mul, this, hl, map_inv (absE F E), NNReal.coe_inv, ← hr]
      ring
  have key := two_kill cm hJ pl pl₁ hd hJ₁ (c := fun x => A x 1 + C x 1) aut (hM F E σ B _ _ G X om om' t f hf) h0
    (fun lev' hv ν 𝓖 n1 n2 n3 x => by
      obtain rfl : lev' = lev := funext fun y => levi_uniq cm hJ pl (hv y) (v1 y)
      simpa using (hAC x).1 ν 𝓖 n1 n2 n3 1) l1 (hu ▸ ea) fun x => by
      obtain ⟨A₁, C₁, s1, e1, e2⟩ := step (hAC x)
      obtain ⟨A₂, C₂, s2, e3, e4⟩ := step s1
      rw [val s2, val s1, e3, e4, e1, e2]
      ring
  obtain ⟨A', C', h⟩ := sp f₁ hf₁
  have z : C' = 0 := funext fun y => by
    have s0 : Split2 W₂ H₁ X (fun z => fa (lev z * (lev y * k))) _ _ :=
      split_move h 1 y fun z => (one_mul _).trans (low hL y z).symm
    obtain ⟨A₁, C₁, s1, e1, e2⟩ := step s0
    have := key (lev y * k)
    simp only [val s1, val s0, e1, e2, one_mul, add_right_inj] at this
    have l2 : l - 1 ≠ 0 := sub_ne_zero.2 fun e => by simp [e] at l1
    exact (mul_eq_zero.1 (by linear_combination this : (l - 1) * C' y = 0)).resolve_left l2
  exact ⟨d₂, W₂, H₁, A', pl₁, by simpa [z] using h.1, h.2.1⟩

end PositivityTheory.ThKEnd.Two

end
