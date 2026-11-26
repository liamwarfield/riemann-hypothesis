module

public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueEqUnitSmoothConnectedBase
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsTwoTorsionTranslateSameLambdaBundle
public import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyNormalFormDetRatioTwoTorsionTranslate

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfTwoTorsionTranslate
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyNormalFormDetRatioTwoTorsionTranslateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyKa
open GlobalTheory.KeyEq
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.keyNormalFormDetRatio_twoTorsion_translate : Out.Laws → ThetaUnifAV → ∀ (x x' : KeyIn ℂ) (p : 𝟙_ (Over (Sp ℂ)) ⟶ x.P.A) (ν : ℂˣ) (t : ℂ), IsTrl x' x p ν → Val x t → Val x' (t * (ν : ℂ) ^ 2) := by
  first | exact @GlobalTheory.KeyEq.val_of_isTrl | exact GlobalTheory.KeyEq.val_of_isTrl | (intros; apply GlobalTheory.KeyEq.val_of_isTrl <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfPolarizedPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfPolarizedPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.KnownScale

theorem val_scale {P : Out.PolAV (Sp ℂ)} {hg rig hr th hth v hv th' hth' v' hv'} {a : ℂ} (ha : a ≠ 0)
    {N : Matrix (Fin P.g) (Fin P.g) ℂ} (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ a * LB.Sec.f th i)
    (h₂ : ∀ i, IsLieComb (N i) v (v' i)) {t : ℂ} (h : Val ⟨P, hg, rig, hr, th, hth, v, hv⟩ t) :
    Val ⟨P, hg, rig, hr, th', hth', v', hv'⟩ (N.det ^ 4 / a ^ 8 * t) := by
  obtain ⟨τ, M, p, q, c, hpq, hc, ⟨u, k₁, k₂, k₃, k₄, k₅, k₆⟩, rfl⟩ := h
  have := P.isAb.comm
  refine ⟨τ, N * M, p, q, a * c, hpq, mul_ne_zero ha hc, ⟨u, k₁, k₂, k₃, k₄, fun i z hz => ?_, fun i => ?_⟩, ?_⟩
  · refine ((congrArg (valAt' _ _) (h₁ i)).trans (valAt'_mul _ _ _ _)).trans ?_
    rw [valAt'_constFn _ _ (Over.w (u.ex z)) _ _ hz]
    refine (congrArg (a * ·) (k₅ i z hz)).trans ?_
    simp only [_root_.mul_assoc]
  · have k := GlobalTheory.UnifDifferential.isDiff_of_isLieComb P.A P.L P.g P.g u _ v _ _ hv.1 k₆ (h₂ i)
    have e : ∑ j, N i j • ((2 * Real.pi * Complex.I : ℂ)⁻¹ • M j) =
        (2 * Real.pi * Complex.I : ℂ)⁻¹ • (N * M) i := by
      simp only [smul_comm (N i _) (2 * Real.pi * Complex.I : ℂ)⁻¹]
      rw [← Finset.smul_sum, ← Matrix.vecMul_eq_sum]
      rfl
    rwa [e] at k
  · rw [Matrix.det_mul, mul_pow, mul_pow, div_mul_div_comm]

theorem det_map_cast {K K' : Type} [CommRing K] [CommRing K'] (f : K →+* K') {m n : ℕ} (e : m = n)
    (M : Matrix (Fin n) (Fin n) K) :
    (Matrix.of fun i j : Fin m => f (M (i.cast e) (j.cast e))).det = f M.det := by
  subst e
  exact (f.map_det M).symm

theorem known_change {K : Type} [Field K] {P : Out.PolAV (Sp K)} {hg rig hr th hth v hv th' hth' v' hv'} (a : Kˣ)
    (h₁ : ∀ i, LB.Sec.f th' i = constFn P.A.hom _ (a : K) * LB.Sec.f th i)
    (h : Known K ⟨P, hg, rig, hr, th, hth, v, hv⟩) : Known K ⟨P, hg, rig, hr, th', hth', v', hv'⟩ := by
  obtain ⟨t₀, ht₀⟩ := h
  have := P.isAb.comm
  choose N hN using fun i => (hv'.2 (v i) (hv.1 i)).exists
  have hdet : IsUnit (Matrix.of N).det :=
    ((GlobalTheory.LieComb.lieComb_algebra K P.A P.g v' hv'.1).2.2.2.2 (Matrix.of N) v hv' hN).1 hv
  have h₁' : ∀ i, LB.Sec.f th i = constFn P.A.hom _ ((a⁻¹ : Kˣ) : K) * LB.Sec.f th' i := fun i => by
    rw [h₁, ← _root_.mul_assoc, ← KeyPow.constFn_mul, Units.inv_mul, KeyPow.constFn_one, _root_.one_mul]
  refine ⟨((Matrix.of N).det)⁻¹ ^ 4 / (a : K) ^ 8 * t₀, fun e x hx => ?_⟩
  obtain ⟨Q, hgQ, rigQ, hrQ, s, hs, u, hu⟩ := x
  obtain ⟨eg⟩ : Nonempty (Q.g = P.g) := by
    obtain ⟨_, _, _, hg, _⟩ := hx
    exact ⟨hg⟩
  have := Q.isAb.comm
  obtain ⟨ex, -, comp, sgl, bas⟩ := GlobalTheory.LieComb.lieComb_algebra ℂ Q.A Q.g u hu.1
  let N' : Matrix (Fin Q.g) (Fin Q.g) ℂ := Matrix.of fun i j => e (Matrix.of N (i.cast eg) (j.cast eg))
  have hd : N'.det = e (Matrix.of N).det := det_map_cast e eg (Matrix.of N)
  choose u₀ hu₀ using fun i => (ex (N' i)).exists
  have hb₀ : IsLieBasis u₀ := (bas N' u₀ hu hu₀).2 (hd ▸ hdet.map e)
  choose M hM using fun i => (hb₀.2 (u i) (hu.1 i)).exists
  have hMN : Matrix.of M * N' = 1 := by
    funext i
    have k := (hu.2 (u i) (hu.1 i)).unique (comp _ (fun j => N' j) u₀ (M i) (u i) hu₀ (hM i)) (sgl i)
    rw [← Matrix.vecMul_eq_sum] at k
    refine k.trans ?_
    simpa using (smul_one_row (1 : ℂ) i).symm
  have hMd : (Matrix.of M).det = (e (Matrix.of N).det)⁻¹ := by
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← hd, ← Matrix.det_mul, hMN, Matrix.det_one]
  obtain ⟨s₀, e₀, e₁, hle⟩ := exists_sec_div Q.A.hom (a := e a) (b := e ((a⁻¹ : Kˣ) : K))
    (by rw [← map_mul, Units.mul_inv, map_one]) s
  have hs₀ : ∀ p : Sp ℂ, ∃ z : Q.A.left, Q.A.hom z = p ∧ z ∈ Out.nonzeroLocus s₀ :=
    fun p => (hs p).imp fun z hz => ⟨hz.1, hle hz.2⟩
  have hx₀ := KeyPBScale.keyPB_scale K ℂ e P hg rig hr th' hth' v' hv' th hth v hv _ (Matrix.of N) Q eg hgQ rigQ hrQ
    s hs u hu s₀ hs₀ u₀ hb₀ h₁' hN e₀ hu₀ hx
  have k := val_scale (hth' := hs) (hv' := hu) (N := Matrix.of M) ((map_ne_zero e).2 a.ne_zero) e₁ hM (ht₀ e _ hx₀)
  rw [hMd] at k
  rwa [map_mul, map_div₀, map_pow, map_pow, map_inv₀]

theorem known_of_keyPB {K : Type} [Field K] {y y' : KeyIn K} (h : KeyPB y' y (RingHom.id K)) (hy : Known K y) :
    Known K y' :=
  hy.imp fun _ ht e x hx => ht e x (keyPB_trans _ _ _ y y' x (RingHom.id K) e h hx)

theorem known_of_polPB : Out.Laws → ∀ (K : Type) [Field K] (y y' : KeyIn K) (φ : y'.P.A.left ⟶ y.P.A.left), PolPB y'.P y.P (𝟙 _) φ → Known K y → Known K y' := by
  intro hL K _ y y' φ ⟨h₁, h₂, h₃⟩ hy
  have e : spMap (RingHom.id K) = 𝟙 (Sp K) := Spec.map_id _
  obtain ⟨rig, hr, th, hth, v, hv, hz⟩ := KeyTf.exists_keyPB_on K K (RingHom.id K) y y'.P φ y'.g_pos h₂ (e ▸ h₁) h₃
  obtain ⟨a, t, ht, hta, hid⟩ := (KeyOnPol.main hL K).2 ⟨y'.P, y'.g_pos, rig, hr, th, hth, v, hv⟩
    y'.rig y'.rig_gen y'.th y'.th_ne y'.v y'.basis
  exact known_of_keyPB hid (known_change a hta (known_of_keyPB hz hy))

end GlobalTheory.KnownScale
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfPolarizedPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFrameValueKnown_of_polarizedPullback : Out.Laws → ∀ (K : Type) [Field K] (y y' : KeyIn K) (φ : y'.P.A.left ⟶ y.P.A.left), PolPB y'.P y.P (𝟙 _) φ → Known K y → Known K y' := by
  first | exact @GlobalTheory.KnownScale.known_of_polPB | exact GlobalTheory.KnownScale.known_of_polPB | (intros; apply GlobalTheory.KnownScale.known_of_polPB <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfTwoTorsionTranslate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.KnownTwist
open GlobalTheory.KeyEq (trl IsTrl)

section Calc

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {K : Type} [Fintype K]

theorem gm_map (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hz : h (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ h) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm h (r z) U a) := by
  apply Units.ext
  refine (gs_unit (r ≫ h) z U hz a).symm.trans ((gs_pull r h z U hz _).symm.trans
    ((gs_stalkMap r z _ hz _).trans (congrArg (r.stalkMap z).hom ?_)))
  refine (gs_pull (𝟙 Y) h (r z) U hz _).trans ?_
  rw [Category.id_comp]
  exact gs_unit h (r z) U hz a

theorem val_map {φ : K → (Y' ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (h : Y ⟶ Y') (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val t (r ≫ h) z J = Units.map (r.stalkMap z).hom.toMonoidHom (val t h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_map r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem pmaps_val {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (H : PMaps w φ' φ ε a t h)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (r : Z ⟶ Y') (z : Z) {I : (Z ⟶ X) → L.ι} {J : (Z ⟶ X') → L'.ι}
    (hI : Good L z I) (hJ : Good L' z J) :
    val t (r ≫ h) z I = (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  rw [val_of t (r ≫ h) z I (fun k => I ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hc])]
  exact H Z r z _ _ (fun k => hI ((r ≫ φ' k) ≫ F)) (fun k => hJ (r ≫ φ' k))

theorem exists_square {A A' B B' : Scheme.{0}} {M : LB A} {M' : LB A'} {N : LB B} {N' : LB B'} (hM : M.IsLB)
    (hM' : M'.IsLB) (hN : N.IsLB) (hN' : N'.IsLB) {F : A' ⟶ A} {G : B' ⟶ B} {φ : B ⟶ A} {φ' : B' ⟶ A'}
    (hsq : φ' ≫ F = G ≫ φ) {u : LB.Iso M' (M.pull F)} {v : LB.Iso N (M.pull φ)} {v' : LB.Iso N' (M'.pull φ')}
    (hu : PGen u) (hv : PGen v) (hv' : PGen v') :
    ∃ w : LB.Iso N' (N.pull G), PGen w ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) j i i' k, φ (G (f z)) ∈ M.U j →
      G (f z) ∈ N.U i → φ' (f z) ∈ M'.U i' → f z ∈ N'.U k →
      gw v (f ≫ G) z j i * gw w f z i k = gw u (f ≫ φ') z j i' * gw v' f z i' k := by
  obtain ⟨c, T⟩ := exists_comp hM' u v' hu hv' hM hN'
  have key : ∀ H : B' ⟶ A, φ' ≫ F = H → ∃ c : LB.Iso N' (M.pull H), PGen c ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) j i' k, H (f z) ∈ M.U j → φ' (f z) ∈ M'.U i' → f z ∈ N'.U k →
        gw c f z j k = gw u (f ≫ φ') z j i' * gw v' f z i' k := by
    rintro _ rfl
    exact ⟨c, T.pgen_comp hM' hu hv', T⟩
  obtain ⟨c', hc', T'⟩ := key _ hsq
  obtain ⟨w, S⟩ := exists_cancel hM v c' hv hc' hN hN'
  exact ⟨w, S.pgen_cancel hM hv hc', fun Z f z j i i' k a b c d =>
    (S Z f z j i k a b d).symm.trans (T' Z f z j i' k a c d)⟩

end Calc

def IsTranslate {K : Type} [CommRing K] (y' y : KeyIn K) (t : 𝟙_ (Over (Sp K)) ⟶ y.P.A) (ν : Kˣ) : Prop :=
  ∃ (e : y'.P.A ≅ y.P.A) (hg : y'.P.g = y.P.g) (w : LB.Iso y'.P.L (y.P.L.pull (e.hom ≫ trl y.P.A t).left))
    (mu : LB.Gen (LB.LinComb y.P.L (K := Fin 2) ![((𝟙 y.P.A) ^ 2).left, 𝟙 y.P.A.left] ![1, -4]))
    (rp : LB.Gen (y.P.L.pull t.left)),
    t ^ 2 = 1 ∧ IsMonHom e.hom ∧ PGen w ∧ mu.IsGen ∧ rp.IsGen ∧
    (∀ i, y'.v i ≫ e.hom = y.v (i.cast hg)) ∧
    (∀ (Z : Scheme.{0}) (r : Z ⟶ y'.P.A.left) (z : Z) j k, (e.hom ≫ trl y.P.A t).left (r z) ∈ y.P.L.U j →
      r z ∈ y'.P.L.U k → gs (r ≫ (e.hom ≫ trl y.P.A t).left) z _ (y.th.f j) =
        (gw w r z j k).val * gs r z _ (y'.th.f k)) ∧
    PMaps w (K := PUnit) (fun _ => eSec y'.P.A) (fun _ => t.left) (fun _ => 1) y'.rig rp (𝟙 _) ∧
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp K))).left) (z : Z) J, Good y.P.L z J →
      val mu (r ≫ eSec y.P.A) z J = val y.rig r z J ^ (-3 : ℤ)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp K))).left) (z : Z) J, Good y.P.L z J →
      val mu (r ≫ t.left) z J =
        gm r z ⊤ (show Γ((𝟙_ (Over (Sp K))).left, ⊤)ˣ from unitOn ν) * val y.rig r z J * val rp r z J ^ (-4 : ℤ)

section Grp

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem comp_trl {T : Over S} (p : 𝟙_ (Over S) ⟶ A) (q : T ⟶ A) : q ≫ trl A p = (toUnit T ≫ p) * q := by
  rw [trl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem eSec_trl (e : B ⟶ A) [IsMonHom e] (p : 𝟙_ (Over S) ⟶ A) : eSec B ≫ (e ≫ trl A p).left = p.left := by
  have : η[B] ≫ e ≫ trl A p = p := by
    have h1 : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [← Category.assoc, IsMonHom.one_hom, comp_trl, toUnit_unit, Category.id_comp, h1, _root_.mul_one]
  exact congrArg CommaMorphism.left this

theorem comp_sq (p : 𝟙_ (Over S) ⟶ A) (hp : p ^ 2 = 1) : p.left ≫ ((𝟙 A) ^ 2).left = eSec A := by
  have : p ≫ (𝟙 A) ^ 2 = η[A] := by
    rw [MonObj.comp_pow, Category.comp_id, hp, Hom.one_def, toUnit_unit, Category.id_comp]
  exact congrArg CommaMorphism.left this

theorem eSec_sq : eSec A ≫ ((𝟙 A) ^ 2).left = eSec A := by
  have h1 : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
  exact comp_sq η[A] (by rw [h1, one_pow])

theorem trl_trl_inv (p : 𝟙_ (Over S) ⟶ A) : trl A p⁻¹ ≫ trl A p = 𝟙 A := by
  rw [comp_trl, trl, ← _root_.mul_assoc, ← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one, _root_.one_mul]

end Grp

theorem exists_isTranslate (laws : Out.Laws) {K : Type} [Field K] (y y' : KeyIn K) (e : y'.P.A ≅ y.P.A)
    (t : 𝟙_ (Over (Sp K)) ⟶ y.P.A) [he : IsMonHom e.hom] (ht : t ^ 2 = 1)
    (hL : LBIso y'.P.L (y.P.L.pull (e.hom ≫ trl y.P.A t).left)) :
    ∃ (y₁ : KeyIn K) (ν : Kˣ), y₁.P = y'.P ∧ IsTranslate y₁ y t ν := by
  obtain ⟨w, hw⟩ := hL
  replace hw := (isGen_iff w).1 hw
  have hg : y'.P.g = y.P.g := by
    obtain ⟨z, -⟩ := y'.th_ne (default : PrimeSpectrum K)
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have := y.P.smoothDim
    have h : SmoothOfRelativeDimension (0 + y.P.g) (e.hom.left ≫ y.P.A.hom) := inferInstance
    rw [Over.w, zero_add] at h
    exact H1.dim_unique _ y'.P.smoothDim h z
  obtain ⟨mu, hmu, hv⟩ := KeyKa.exists_normalised_mulPull laws K y 2
  obtain ⟨rp, hrp⟩ := DVR.exists_gen_of_local (V := K) y.P.L y.P.isLB (K := PUnit) (fun _ => t.left) (fun _ => 1)
  obtain ⟨rig, hrig, hm⟩ := H1.exists_gen_move y.P.isLB y'.P.isLB w hw (K := PUnit) (fun _ => t.left)
    (fun _ => eSec y'.P.A) (fun _ => 1) (𝟙 _) (fun _ => (eSec_trl e.hom t).trans (Category.id_comp _).symm) rp hrp
  obtain ⟨th, hth⟩ := sec_pull_down hw y.P.isLB y'.P.isLB y.th
  have hne : ∀ s : Sp K, ∃ x : y'.P.A.left, y'.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th := by
    intro s
    obtain ⟨z, -, hz⟩ := y.th_ne s
    have hs : (trl y.P.A t⁻¹ ≫ e.inv).left ≫ (e.hom ≫ trl y.P.A t).left = 𝟙 _ := by
      rw [← Over.comp_left, Category.assoc, e.inv_hom_id_assoc, trl_trl_inv, Over.id_left]
    obtain ⟨x, rfl⟩ : ∃ x, (e.hom ≫ trl y.P.A t).left x = z := ⟨_, congrArg (fun q => q z) hs⟩
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart y'.P.isLB x
    refine ⟨x, Subsingleton.elim (α := PrimeSpectrum K) _ _, (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩⟩
    have u₁ : IsUnit (gs (e.hom ≫ trl y.P.A t).left x _ (y.th.f j)) := by
      rw [gs_stalkMap _ x _ hj]; exact u.map _
    have e := hth _ (𝟙 _) x j k hj hk
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  have hb : IsLieBasis (fun i : Fin y'.P.g => y.v (i.cast hg) ≫ e.inv) := by
    refine Chart.isLieBasis_iso e ?_
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
    have : ∀ (n : ℕ) (h : n = y.P.g), IsLieBasis (fun i : Fin n => y.v (i.cast h)) := by
      rintro _ rfl; exact y.basis
    exact this _ hg
  obtain ⟨u, hu⟩ := (((SimilUnit.IsVal.pull hmu t.left).mul (SimilUnit.IsVal.pull y.rig_gen (𝟙 _)).inv).mul
    ((SimilUnit.IsVal.pull hrp (𝟙 _)).zpow (-4)).inv).exists_unit y.P.isLB (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, comp_sq t ht, Category.comp_id,
        Category.id_comp, Fintype.prod_unique, zpow_one]
      generalize h (eSec y.P.A) = a
      generalize h t.left = b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  let ν : Kˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom u
  have hν : unitOn ν = u := Units.ext (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of K)) u.val)
  refine ⟨⟨y'.P, y'.g_pos, rig, hrig, th, hne, _, hb⟩, ν, rfl, e, hg, w, mu, rp, ht, he, hw, hmu, hrp,
    fun i => by simp, hth, hm, fun Z r z J hJ => ?_, fun Z r z J hJ => ?_⟩
  · have a := val_map y.rig r (𝟙 _) z hJ
    rw [Category.comp_id] at a
    refine (val_map mu r _ z hJ).trans ?_
    rw [a, ← map_zpow]
    exact congrArg _ (hv (r z) _ fun ψ => hJ (r ≫ ψ))
  · have a := val_map y.rig r (𝟙 _) z hJ
    have b := val_map rp r (𝟙 _) z hJ
    have c := gm_map r (𝟙 _) z ⊤ trivial u
    rw [Category.comp_id] at a b c
    refine (val_map mu r _ z hJ).trans ?_
    rw [a, hν]
    erw [b, c]
    rw [← map_zpow, ← map_mul, ← map_mul]
    have d := Units.ext ((hu (r z) _ fun ψ => hJ (r ≫ ψ)).trans (gs_unit _ _ ⊤ trivial _))
    rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul] at d
    refine congrArg _ (d.trans ?_)
    exact mul_right_comm _ _ _

section Pull

variable {S S' : Scheme.{0}} {A : Over S} {B : Over S'} [GrpObj A] [GrpObj B] {f : S' ⟶ S} {φ : B.left ⟶ A.left}

theorem sq_comm (h : IsGrpPullback B A f φ) : ((𝟙 B) ^ 2).left ≫ φ = φ ≫ ((𝟙 A) ^ 2).left := by
  have e : pushPt h.1.w ((𝟙 B) ^ 2) = pushPt h.1.w (𝟙 B) ≫ (𝟙 A) ^ 2 := by
    rw [MonObj.comp_pow, Category.comp_id]
    exact map_pow (pushHom h B) _ 2
  have e' : ((𝟙 B) ^ 2).left ≫ φ = (𝟙 B.left ≫ φ) ≫ ((𝟙 A) ^ 2).left := congrArg CommaMorphism.left e
  rwa [Category.id_comp] at e'

theorem trl_comm (h : IsGrpPullback B A f φ) {p : 𝟙_ (Over S') ⟶ B} {t : 𝟙_ (Over S) ⟶ A}
    (hp : p.left ≫ φ = f ≫ t.left) : (trl B p).left ≫ φ = φ ≫ (trl A t).left := by
  have e : pushPt h.1.w (trl B p) = pushPt h.1.w (𝟙 B) ≫ trl A t := by
    rw [comp_trl]
    refine (map_mul (pushHom h B) _ _).trans (congrArg (· * _) (Over.OverMorphism.ext ?_))
    show ((toUnit B).left ≫ p.left) ≫ φ = (toUnit (Over.mk (B.hom ≫ f))).left ≫ t.left
    rw [Category.assoc, hp]
    simp
  have e' : (trl B p).left ≫ φ = (𝟙 B.left ≫ φ) ≫ (trl A t).left := congrArg CommaMorphism.left e
  rwa [Category.id_comp] at e'

theorem exists_pt (h : IsGrpPullback B A f φ) (t : 𝟙_ (Over S) ⟶ A) (ht : t ^ 2 = 1) :
    ∃ p : 𝟙_ (Over S') ⟶ B, p.left ≫ φ = f ≫ t.left ∧ p ^ 2 = 1 := by
  have w : (f ≫ t.left) ≫ A.hom = 𝟙 S' ≫ f := by
    rw [Category.assoc, Over.w t]; simp
  let p : 𝟙_ (Over S') ⟶ B := Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ _)
  have hp : p.left ≫ φ = f ≫ t.left := h.1.lift_fst _ _ _
  refine ⟨p, hp, ?_⟩
  have inj : Function.Injective (pushHom h (𝟙_ (Over S'))) := fun a b e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left e) ((Over.w a).trans (Over.w b).symm))
  apply inj
  have e : pushHom h (𝟙_ (Over S')) p = toUnit _ ≫ t := Over.OverMorphism.ext (hp.trans (by simp))
  rw [map_pow, map_one, e, ← MonObj.comp_pow, ht, MonObj.comp_one]

end Pull

def baseMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (𝟙_ (Over (Sp R'))).left ⟶ (𝟙_ (Over (Sp R))).left := spMap f

theorem gm_spMap_unitOn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (q : (𝟙_ (Over (Sp R'))).left)
    (u : Rˣ) : gm (𝟙 _ ≫ baseMap f) q ⊤ (show Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ from unitOn u) =
      gm (𝟙 _) q ⊤ (show Γ((𝟙_ (Over (Sp R'))).left, ⊤)ˣ from unitOn (Units.map f.toMonoidHom u)) := by
  refine (gm_pull (𝟙 _) (baseMap f) q ⊤ trivial _).symm.trans (congrArg (gm (𝟙 _) q ⊤) (Units.ext ?_))
  have := congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this.symm

theorem IsTranslate.baseChange {K : Type} [CommRing K] {y' y : KeyIn K} {t : 𝟙_ (Over (Sp K)) ⟶ y.P.A} {ν : Kˣ}
    (H : IsTranslate y' y t ν) {f : K →+* ℂ} {x' x : KeyIn ℂ} (h' : KeyPB x' y' f) (h : KeyPB x y f) :
    ∃ p, IsTrl x' x p (Units.map f.toMonoidHom ν) := by
  obtain ⟨e, hg₀, w₀, mu₀, rp₀, ht, he, hw₀, hmu₀, hrp₀, hv₀, hs₀, hr₀, m₀, m₁⟩ := H
  obtain ⟨φ, hφe, v, hg, F, hc, hv, hr, hs, hF, hFe, hb⟩ := h
  obtain ⟨φ', hφe', v', hg', F', hc', hv', hr', hs', hF', hFe', hb'⟩ := h'
  obtain rfl : F = F' := KeyCancel.dualNumber_ringHom_ext (fun a => (hF a).trans (hF' a).symm) (hFe.trans hFe'.symm)
  change eSec x.P.A ≫ φ = baseMap f ≫ eSec y.P.A at hφe
  change eSec x'.P.A ≫ φ' = baseMap f ≫ eSec y'.P.A at hφe'
  replace hv := (isGen_iff v).1 hv
  replace hv' := (isGen_iff v').1 hv'
  replace hr := (maps_iff v _ (fun _ => eSec y.P.A) _ x.rig y.rig (baseMap f) _ (rigPull_le φ (baseMap f) hφe y.P.L)
    (fun _ => rfl)).1 hr
  replace hr' := (maps_iff v' _ (fun _ => eSec y'.P.A) _ x'.rig y'.rig (baseMap f) _
    (rigPull_le φ' (baseMap f) hφe' y'.P.L) (fun _ => rfl)).1 hr'
  replace hs := (KeyCancel.appLE_eq_iff_stalk v y.th x.th).1 hs
  replace hs' := (KeyCancel.appLE_eq_iff_stalk v' y'.th x'.th).1 hs'
  obtain ⟨ε, hε, hεφ⟩ := grpPullback_iso ((hc'.comp (isGrpPullback_of_iso e)).congr (Category.comp_id _) rfl) hc
  obtain ⟨p, hp, hp2⟩ := exists_pt hc t ht
  change p.left ≫ φ = baseMap f ≫ t.left at hp
  have hsq : φ' ≫ (e.hom ≫ trl y.P.A t).left = (ε.hom ≫ trl x.P.A p).left ≫ φ := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, trl_comm hc hp, ← Category.assoc, ← hεφ, Category.assoc]
  obtain ⟨w, hw, Q⟩ := exists_square y.P.isLB y'.P.isLB x.P.isLB x'.P.isLB hsq hw₀ hv hv'
  have c₁ : ∀ k : Fin 2, ![((𝟙 x.P.A) ^ 2).left, 𝟙 x.P.A.left] k ≫ φ =
      φ ≫ ![((𝟙 y.P.A) ^ 2).left, 𝟙 y.P.A.left] k := fun k => by
    fin_cases k
    · exact sq_comm hc
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨mu, hmu, pm⟩ := H1.exists_gen_move y.P.isLB x.P.isLB v hv _ _ _ φ c₁ mu₀ hmu₀
  obtain ⟨rp, hrp, pr⟩ := H1.exists_gen_move y.P.isLB x.P.isLB v hv (K := PUnit) (fun _ => t.left) (fun _ => p.left)
    (fun _ => 1) (baseMap f) (fun _ => hp) rp₀ hrp₀
  have good : ∀ q : (𝟙_ (Over (Sp ℂ))).left, ∃ I, Good y.P.L q I := fun q => by
    choose I hI using fun ψ : (𝟙_ (Over (Sp ℂ))).left ⟶ y.P.A.left => exists_chart y.P.isLB (ψ q)
    exact ⟨I, hI⟩
  refine ⟨p, ε, hg'.trans (hg₀.trans hg.symm), w, mu, rp, hp2, hε, (isGen_iff w).2 hw, hmu, hrp, fun i => ?_,
    fun z j k hj hk => ?_, fun q J J' hJ hJ' => ?_, fun q J hJ => ?_, fun q J hJ => ?_⟩
  · refine Over.OverMorphism.ext (hc.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [Over.comp_left, Category.assoc, hεφ, ← Category.assoc, hb', hb, Category.assoc, ← Over.comp_left, hv₀]
    rfl
  · obtain ⟨a, ha⟩ := exists_chart y.P.isLB (φ ((ε.hom ≫ trl x.P.A p).left z))
    obtain ⟨b, hb⟩ := exists_chart y'.P.isLB (φ' z)
    have ha' : (e.hom ≫ trl y.P.A t).left (φ' z) ∈ y.P.L.U a := (congrArg (fun g => g z ∈ y.P.L.U a) hsq).mpr ha
    have e₁ := hs _ (𝟙 _ ≫ (ε.hom ≫ trl x.P.A p).left) z a j ha hj
    have e₂ := hs₀ _ (𝟙 _ ≫ φ') z a b ha' hb
    have e₃ := hs' _ (𝟙 _) z b k hb hk
    have e₄ := Q _ (𝟙 _) z a j b k ha hj hb hk
    rw [Category.assoc, hsq, ← Category.assoc, e₁, e₃, ← _root_.mul_assoc, ← Units.val_mul, ← e₄, Units.val_mul,
      _root_.mul_assoc, Units.mul_right_inj, Category.id_comp] at e₂
    exact e₂
  · obtain ⟨I, hI⟩ := good q
    obtain ⟨b, hb⟩ := exists_chart y'.P.isLB (φ' (eSec x'.P.A q))
    have E := eSec_trl ε.hom p
    have E₀ := eSec_trl e.hom t
    have a₁ : φ (p.left q) ∈ y.P.L.U (I (p.left ≫ φ)) := hI _
    have a₂ : p.left q ∈ x.P.L.U (J (𝟙 _ ≫ p.left)) := hJ (𝟙 _ ≫ p.left)
    have a₃ : eSec x'.P.A q ∈ x'.P.L.U (J' (𝟙 _ ≫ eSec x'.P.A)) := hJ' (𝟙 _ ≫ eSec x'.P.A)
    have b₁ : eSec y'.P.A (baseMap f q) ∈ y'.P.L.U b := (congrArg (fun g => g q ∈ y'.P.L.U b) hφe').mp hb
    have b₂ : (e.hom ≫ trl y.P.A t).left (eSec y'.P.A (baseMap f q)) ∈ y.P.L.U (I (p.left ≫ φ)) :=
      (congrArg (fun g => g q ∈ y.P.L.U (I (p.left ≫ φ))) (hp.trans (congrArg (baseMap f ≫ ·) E₀.symm))).mp a₁
    have e₁ := pr _ (𝟙 _) q (fun _ => I (p.left ≫ φ)) (fun _ => J (𝟙 _ ≫ p.left)) (fun _ => a₁) (fun _ => a₂)
    have e₂ := hr₀ _ (𝟙 _ ≫ baseMap f) q (fun _ => I (p.left ≫ φ)) (fun _ => b) (fun _ => b₂) (fun _ => b₁)
    have e₃ := hr' _ (𝟙 _) q (fun _ => b) (fun _ => J' (𝟙 _ ≫ eSec x'.P.A)) (fun _ => hb) (fun _ => a₃)
    have e₄ := Q _ (eSec x'.P.A) q (I (p.left ≫ φ)) (J (𝟙 _ ≫ p.left)) b (J' (𝟙 _ ≫ eSec x'.P.A))
      ((congrArg (fun g => φ (g q) ∈ y.P.L.U (I (p.left ≫ φ))) E).mpr a₁)
      ((congrArg (fun g => g q ∈ x.P.L.U (J (𝟙 _ ≫ p.left))) E).mpr a₂) hb a₃
    rw [E, hφe'] at e₄
    simp only [Fintype.prod_unique, zpow_one] at e₁ e₂ e₃
    have e₅ : gm (𝟙 _ ≫ baseMap f) q _ (rp₀.s (fun _ => I (p.left ≫ φ))) =
      gm ((𝟙 _ ≫ baseMap f) ≫ 𝟙 _) q _ (rp₀.s (fun _ => I (p.left ≫ φ))) := by erw [Category.comp_id]
    have e₆ := e₁.symm.trans (e₅.trans (e₂.trans (congrArg _ e₃)))
    have i₁ : gw v (𝟙 _ ≫ p.left) q (I (p.left ≫ φ)) (J (𝟙 _ ≫ p.left)) =
      gw v p.left q (I (p.left ≫ φ)) (J (𝟙 _ ≫ p.left)) := congrArg (gw v · q _ _) (Category.id_comp _)
    have i₂ : gw w₀ ((𝟙 _ ≫ baseMap f) ≫ eSec y'.P.A) q (I (p.left ≫ φ)) b =
      gw w₀ (baseMap f ≫ eSec y'.P.A) q (I (p.left ≫ φ)) b :=
        congrArg (fun g => gw w₀ (g ≫ eSec y'.P.A) q _ _) (Category.id_comp _)
    have i₃ : gw v' (𝟙 _ ≫ eSec x'.P.A) q b (J' (𝟙 _ ≫ eSec x'.P.A)) =
      gw v' (eSec x'.P.A) q b (J' (𝟙 _ ≫ eSec x'.P.A)) := congrArg (gw v' · q _ _) (Category.id_comp _)
    have e₇ := (congrArg (· * _) i₁.symm).trans (e₆.trans ((congrArg₂ (fun a b => a * (b * _)) i₂ i₃).trans
      ((_root_.mul_assoc _ _ _).symm.trans ((congrArg (· * _) e₄.symm).trans (_root_.mul_assoc _ _ _)))))
    exact mul_left_cancel e₇
  · obtain ⟨I, hI⟩ := good q
    have e₁ := pmaps_val pm c₁ (eSec x.P.A) q hI hJ
    have e₂ := pmaps_val hr (fun _ => hφe) (𝟙 _) q hI hJ
    have e₃ := m₀ _ (𝟙 _ ≫ baseMap f) q I hI
    have e₄ : (𝟙 _ ≫ baseMap f : (𝟙_ (Over (Sp ℂ))).left ⟶ (𝟙_ (Over (Sp K))).left) ≫ eSec y.P.A = eSec x.P.A ≫ φ :=
      (congrArg (· ≫ eSec y.P.A) (Category.id_comp _)).trans hφe.symm
    have e₅ := e₁.symm.trans ((congrArg (val mu₀ · q I) e₄.symm).trans (e₃.trans (congrArg (· ^ (-3 : ℤ)) e₂)))
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, eSec_sq, Category.comp_id,
      Fintype.prod_unique, zpow_one] at e₅
    rw [Category.id_comp] at e₅
    generalize gw v (eSec x.P.A) q _ _ = a at e₅
    rw [eq_inv_mul_of_mul_eq e₅]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  · obtain ⟨I, hI⟩ := good q
    have e₁ := pmaps_val pm c₁ p.left q hI hJ
    have e₂ := pmaps_val hr (fun _ => hφe) (𝟙 _) q hI hJ
    have e₂' := pmaps_val pr (fun _ => hp) (𝟙 _) q hI hJ
    have e₃ := m₁ _ (𝟙 _ ≫ baseMap f) q I hI
    have e₄ : (𝟙 _ ≫ baseMap f : (𝟙_ (Over (Sp ℂ))).left ⟶ (𝟙_ (Over (Sp K))).left) ≫ t.left = p.left ≫ φ :=
      (congrArg (· ≫ t.left) (Category.id_comp _)).trans hp.symm
    have e₅ := e₁.symm.trans ((congrArg (val mu₀ · q I) e₄.symm).trans (e₃.trans (congrArg₂ (· * ·)
      (congrArg₂ (· * ·) (gm_spMap_unitOn f q ν) e₂) (congrArg (· ^ (-4 : ℤ)) e₂'))))
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, comp_sq p hp2, Category.comp_id,
      Fintype.prod_unique, zpow_one] at e₅
    rw [Category.id_comp, Category.id_comp] at e₅
    generalize gw v (eSec x.P.A) q _ _ = a at e₅
    generalize gw v p.left q _ _ = b at e₅
    rw [eq_inv_mul_of_mul_eq e₅]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module

theorem polPB_of_eq {S : Scheme.{0}} {P P' : Out.PolAV S} (h : P = P') : ∃ φ, PolPB P' P (𝟙 _) φ := by
  subst h
  have : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  exact ⟨𝟙 _, isGrpPullback_of_iso (Iso.refl P.A), rfl, isoPullId (idIso P.L) rfl,
    (isGen_iff _).2 (isoPullId_pgen (idIso_isGen P.isLB) rfl)⟩

theorem known_of_translate : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] (y y' : KeyIn K) (e : y'.P.A ≅ y.P.A) (t : 𝟙_ (Over (Sp K)) ⟶ y.P.A), IsMonHom e.hom → t ^ 2 = 1 → LBIso y'.P.L (y.P.L.pull (e.hom ≫ ((toUnit y.P.A ≫ t) * 𝟙 y.P.A)).left) → Known K y → Known K y' := by
  intro laws hU K _ y y' e t he ht hL hk
  obtain ⟨t₀, h₀⟩ := hk
  obtain ⟨y₁, ν, hP, H⟩ := exists_isTranslate laws y y' e t ht hL
  have k₁ : Known K y₁ := by
    refine ⟨t₀ * (ν : K) ^ 2, fun f x' h' => ?_⟩
    obtain ⟨x, h⟩ := exists_keyPB_ring y f
    obtain ⟨p, hp⟩ := H.baseChange h' h
    have a : KeyEq.Val x (f t₀) := h₀ f x h
    have b : f (t₀ * (ν : K) ^ 2) = f t₀ * ((Units.map f.toMonoidHom ν : ℂˣ) : ℂ) ^ 2 := by
      rw [map_mul, map_pow]; rfl
    rw [b]
    exact GlobalTheory.T.keyNormalFormDetRatio_twoTorsion_translate laws hU x x' p _ _ hp a
  obtain ⟨φ, hφ⟩ := polPB_of_eq hP
  exact GlobalTheory.T.thetaFrameValueKnown_of_polarizedPullback laws K y₁ y' φ hφ k₁

end GlobalTheory.KnownTwist
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfTwoTorsionTranslateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaFrameValueKnown_of_twoTorsion_translate : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] (y y' : KeyIn K) (e : y'.P.A ≅ y.P.A) (t : 𝟙_ (Over (Sp K)) ⟶ y.P.A), IsMonHom e.hom → t ^ 2 = 1 → LBIso y'.P.L (y.P.L.pull (e.hom ≫ ((toUnit y.P.A ≫ t) * 𝟙 y.P.A)).left) → Known K y → Known K y' := by
  first | exact @GlobalTheory.KnownTwist.known_of_translate | exact GlobalTheory.KnownTwist.known_of_translate | (intros; apply GlobalTheory.KnownTwist.known_of_translate <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

namespace GlobalTheory.KeyFam.SameLam
open GlobalTheory.ZM.SiegPull

section Prod

variable {S S' X Y : Scheme.{0}} {A : Over S} [GrpObj A]

def IsProd (A : Over S) [GrpObj A] (u v w : X ⟶ A.left) : Prop :=
  ∃ (s : X ⟶ S) (x y : Over.mk s ⟶ A), x.left = u ∧ y.left = v ∧ (x * y).left = w

theorem isProd_mul {T : Over S} (x y : T ⟶ A) : IsProd A x.left y.left (x * y).left :=
  ⟨T.hom, x, y, rfl, rfl, rfl⟩

theorem exists_isProd (u v : X ⟶ A.left) (h : u ≫ A.hom = v ≫ A.hom) : ∃ w, IsProd A u v w :=
  ⟨_, v ≫ A.hom, Over.homMk u h, Over.homMk v rfl, rfl, rfl, rfl⟩

theorem IsProd.unique {u v w u' v' w' : X ⟶ A.left} (h : IsProd A u v w) (h' : IsProd A u' v' w') (hu : u = u')
    (hv : v = v') : w = w' := by
  obtain ⟨s, x, y, rfl, rfl, rfl⟩ := h
  obtain ⟨s', x', y', rfl, rfl, rfl⟩ := h'
  exact mul_left_congr ((Over.w x).symm.trans ((congrArg (· ≫ A.hom) hu).trans (Over.w x'))) _ _ _ _ hu hv

theorem IsProd.comp {u v w : X ⟶ A.left} (h : IsProd A u v w) (g : Y ⟶ X) : IsProd A (g ≫ u) (g ≫ v) (g ≫ w) := by
  obtain ⟨s, x, y, rfl, rfl, rfl⟩ := h
  let g' : Over.mk (g ≫ s) ⟶ Over.mk s := Over.homMk g rfl
  exact ⟨g ≫ s, g' ≫ x, g' ≫ y, rfl, rfl, by rw [← MonObj.comp_mul]; rfl⟩

theorem IsProd.push {A' : Over S'} [GrpObj A'] {f : S' ⟶ S} {φ : A'.left ⟶ A.left} (hφ : IsGrpPullback A' A f φ)
    {u v w : X ⟶ A'.left} (h : IsProd A' u v w) : IsProd A (u ≫ φ) (v ≫ φ) (w ≫ φ) := by
  obtain ⟨s, x, y, rfl, rfl, rfl⟩ := h
  exact ⟨_, pushPt hφ.1.w x, pushPt hφ.1.w y, rfl, rfl, hφ.2 _ x y _ _ rfl rfl⟩

theorem isProd_transl {Q : Over S} (e : Q ⟶ A) (t : 𝟙_ (Over S) ⟶ A) :
    IsProd A (Q.hom ≫ t.left) e.left (e ≫ ((toUnit A ≫ t) * 𝟙 A)).left := by
  have h := isProd_mul (toUnit Q ≫ t) e
  have hu : (toUnit Q).left = Q.hom := (Category.comp_id _).symm.trans (Over.w (toUnit Q))
  rw [Over.comp_left, hu] at h
  rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  exact h

theorem sq_eq_one_iff (t : 𝟙_ (Over S) ⟶ A) : t ^ 2 = 1 ↔ IsProd A t.left t.left (eSec A) := by
  have h1 : (1 : 𝟙_ (Over S) ⟶ A).left = eSec A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  rw [pow_two]
  exact ⟨fun h => h1 ▸ h ▸ isProd_mul t t,
    fun h => Over.OverMorphism.ext (((isProd_mul t t).unique h rfl rfl).trans h1.symm)⟩

end Prod

theorem exists_finset_point {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {X : Scheme.{0}} (p : X ⟶ Sp K)
    [LocallyOfFiniteType p] (a : Sp Ω ⟶ X) (ha : a ≫ p = spMap (algebraMap K Ω)) :
    ∃ (s : Finset Ω) (b : Sp (IntermediateField.adjoin K (s : Set Ω)) ⟶ X),
      spMap (algebraMap (IntermediateField.adjoin K (s : Set Ω)) Ω) ≫ b = a := by
  classical
  obtain ⟨A, i, _, t, ht⟩ : ∃ (A : CommRingCat.{0}) (i : Spec A ⟶ X) (_ : IsOpenImmersion i)
      (t : Spec A), i t = a (IsLocalRing.closedPoint Ω) := by
    obtain ⟨n, t, ht⟩ := X.affineCover.exists_eq (a (IsLocalRing.closedPoint Ω))
    exact ⟨_, X.affineCover.f n, X.affineCover.map_prop n, t, ht⟩
  have hr : Set.range a ⊆ Set.range i := by
    rintro _ ⟨u, rfl⟩
    exact ⟨t, ht.trans (congrArg a (Subsingleton.elim _ _))⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift i a hr)
  have hφa : Spec.map φ ≫ i = a := by rw [hφ, IsOpenImmersion.lift_fac]
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (i ≫ p)
  have h₂ : LocallyOfFiniteType (Spec.map ψ) := by rw [hψ]; infer_instance
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at h₂
  have hc : ψ ≫ φ = CommRingCat.ofHom (algebraMap K Ω) :=
    Spec.map_injective (by rw [Spec.map_comp, hψ, ← Category.assoc, hφa, ha])
  let : Algebra K A := ψ.hom.toAlgebra
  obtain ⟨s, hs⟩ : (⊤ : Subalgebra K A).FG := (show Algebra.FiniteType K A from h₂).out
  refine ⟨s.image φ.hom, ?_⟩
  set F := IntermediateField.adjoin K ((s.image φ.hom : Finset Ω) : Set Ω) with hF
  have hm : ∀ x : A, φ.hom x ∈ F := fun x => by
    have hx : x ∈ Algebra.adjoin K (s : Set A) := hs ▸ Algebra.mem_top
    induction hx using Algebra.adjoin_induction with
    | mem x hx => exact IntermediateField.subset_adjoin _ _ (by simpa using ⟨x, hx, rfl⟩)
    | algebraMap q =>
      rw [show φ.hom (algebraMap K A q) = algebraMap K Ω q from congrArg (fun z => z.hom q) hc]
      exact F.algebraMap_mem q
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  refine ⟨Spec.map (CommRingCat.ofHom (φ.hom.codRestrict F hm)) ≫ i, ?_⟩
  rw [← hφa, ← Spec.map_comp_assoc]
  rfl

theorem polPB_of_keyPB {R R' : Type} [CommRing R] [CommRing R'] {x' : KeyIn R'} {x : KeyIn R} {f : R →+* R'}
    (h : KeyPB x' x f) : ∃ φ, PolPB x'.P x.P (spMap f) φ ∧ eSec x'.P.A ≫ φ = spMap f ≫ eSec x.P.A := by
  obtain ⟨φ, he, w, hg, F, hp, hw, -⟩ := h
  exact ⟨φ, ⟨hp, hg, w, hw⟩, he⟩

theorem known_of_keyPB {K F : Type} [Field K] [Field F] {y : KeyIn K} {y' : KeyIn F} {j : K →+* F} (h : KeyPB y' y j)
    (hk : Known K y) : ∀ (e : F →+* ℂ) (x : KeyIn ℂ), KeyPB x y' e → Val x (e (j hk.choose)) :=
  fun e x hx => hk.choose_spec (e.comp j) x (keyPB_trans _ _ _ y y' x j e h hx)

theorem known_of_point (hL : Out.Laws) (hT : ThetaUnifAV) {K F : Type} [Field K] [Field F] (j : K →+* F) (y : KeyIn K)
    (y' : KeyIn F) (φ w : y'.P.A.left ⟶ y.P.A.left) (hφ : IsGrpPullback y'.P.A y.P.A (spMap j) φ)
    (p : Sp F ⟶ y.P.A.left) (hp : p ≫ y.P.A.hom = spMap j) (h₂ : IsProd y.P.A p p (spMap j ≫ eSec y.P.A))
    (hw : IsProd y.P.A (y'.P.A.hom ≫ p) φ w) (hi : LBIso y'.P.L (y.P.L.pull w)) (hk : Known K y) : Known F y' := by
  obtain ⟨z, hz⟩ := exists_keyPB_ring y j
  obtain ⟨χ, hχ, he⟩ := polPB_of_keyPB hz
  obtain ⟨e, hm, hφe⟩ := grpPullback_iso hφ hχ.1
  let t : 𝟙_ (Over (Sp F)) ⟶ z.P.A :=
    Over.homMk (hχ.1.1.lift p (𝟙 _) (hp.trans (Category.id_comp _).symm)) (hχ.1.1.lift_snd _ _ _)
  have ht : t.left ≫ χ = p := hχ.1.1.lift_fst _ _ _
  refine GlobalTheory.T.thetaFrameValueKnown_of_twoTorsion_translate hL hT F z y' e t hm ?_ ?_ ⟨_, known_of_keyPB hz hk⟩
  · have h1 : (1 : 𝟙_ (Over (Sp F)) ⟶ z.P.A).left = eSec z.P.A := by
      rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
    rw [pow_two]
    refine Over.OverMorphism.ext (hχ.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [h1, he]
    exact ((isProd_mul t t).push hχ.1).unique h₂ ht ht
  · have hw' := ((isProd_transl e.hom t).push hχ.1).unique hw (by rw [Category.assoc, ht]) hφe
    have k := SiegPull.lbIso_pull_comp hχ.2.2 (e.hom ≫ ((toUnit z.P.A ≫ t) * 𝟙 z.P.A)).left
    rw [hw'] at k
    exact LBIso.trans y'.P.isLB (LB.isLB_pull y.P.isLB _) (LB.isLB_pull z.P.isLB _) hi k.symm

theorem epi_spMap {k Ω : Type} [Field k] [Field Ω] (σ : k →+* Ω) : Epi (spMap σ) := by
  letI := σ.toAlgebra
  haveI : Flat (spMap σ) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 inferInstance
  haveI : Surjective (spMap σ) := ⟨fun p => ⟨IsLocalRing.closedPoint Ω, Subsingleton.elim _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

theorem exists_polPB {R R' : Type} [CommRing R] [CommRing R'] (P : Out.PolAV (Sp R)) (f : R →+* R') :
    ∃ (P' : Out.PolAV (Sp R')) (φ : P'.A.left ⟶ P.A.left), PolPB P' P (spMap f) φ := by
  have h := isGrpPullback_pullback P.A (spMap f)
  let φ : ((Over.pullback (spMap f)).obj P.A).left ⟶ P.A.left := pullback.fst P.A.hom (spMap f)
  change IsGrpPullback _ _ _ φ at h
  have hL' := LB.isLB_pull P.isLB φ
  have hw := (isGen_iff _).1 (idIso_isGen hL')
  exact ⟨{ A := (Over.pullback (spMap f)).obj P.A
           isAb := Out.TLinPf.isAb_pullback (spMap f) P.A P.isAb
           g := P.g
           smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
           L := P.L.pull φ
           isLB := hL'
           rigid := PolBaseChange.rigidified_pull h P.rigid
           sym := PolBaseChange.sym_pull h P.sym
           ample := relAmple_pull h.1 P.isLB hL' hw ⊤ (isAffineOpen_top _) (fun _ => trivial) P.ample
           ktriv := kTriv_pull h P.isLB hL' hw P.ktriv }, φ, h, rfl, idIso _, idIso_isGen hL'⟩

theorem exists_point (hL : Out.Laws) {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω] (σ : K →+* Ω)
    (Q P : Out.PolAV (Sp K)) (e : P.A ≅ Q.A) [IsMonHom e.hom] (hl : LamIs P.A P.L Q.A (abelian₂ Q.A Q.L) e.hom.left) :
    ∃ (p : Sp Ω ⟶ Q.A.left) (X : Over (Sp Ω)) (ψ : X.left ⟶ P.A.left) (w : X.left ⟶ Q.A.left),
      p ≫ Q.A.hom = spMap σ ∧ IsProd Q.A p p (spMap σ ≫ eSec Q.A) ∧ IsPullback ψ X.hom P.A.hom (spMap σ) ∧
      IsProd Q.A (X.hom ≫ p) (ψ ≫ e.hom.left) w ∧ LBIso (P.L.pull ψ) (Q.L.pull w) := by
  obtain ⟨Q', χ, hχ⟩ := exists_polPB Q σ
  obtain ⟨P', ψ, hψ⟩ := exists_polPB P σ
  obtain ⟨e', hm, he'⟩ := grpPullback_iso
    ((hψ.1.comp (isGrpPullback_of_iso e)).congr (Category.comp_id _) rfl) hχ.1
  have lQ : (abelian₂ Q.A Q.L).IsLB := DVR.linComb_isLB _ Q.isLB _ _
  have hl' : LamIs P'.A P'.L Q'.A (abelian₂ Q'.A Q'.L) e'.hom.left := by
    obtain ⟨φ₂, s₂, i₂⟩ := hχ.lamIs
    obtain ⟨φ₂', s₂', i₂'⟩ := LamIs.comp P'.isLB P.isLB lQ hψ.lamIs hl
    refine ⟨_, isSquare_tensor e'.hom, ?_⟩
    have k₁ := SiegPull.lbIso_pull_comp i₂ (e'.hom ⊗ₘ e'.hom).left
    rw [isSquare_unique (isSquare_comp (isSquare_tensor e'.hom) s₂) s₂' he'] at k₁
    exact LBIso.trans (DVR.linComb_isLB _ P'.isLB _ _) (LB.isLB_pull lQ _)
      (LB.isLB_pull (DVR.linComb_isLB _ Q'.isLB _ _) _) i₂' k₁.symm
  obtain ⟨t, ht, hi⟩ := GlobalTheory.T.exists_twoTorsion_translate_same_lambdaBundle hL Ω Q' P' e' hm hl'
  refine ⟨t.left ≫ χ, P'.A, ψ, (e'.hom ≫ ((toUnit Q'.A ≫ t) * 𝟙 Q'.A)).left ≫ χ, ?_, ?_, hψ.1.1, ?_, ?_⟩
  · rw [Category.assoc, hχ.1.1.w, ← Category.assoc, Over.w t]
    exact Category.id_comp _
  · rw [← PolBaseChange.eSec_comm hχ.1]
    exact ((sq_eq_one_iff t).1 ht).push hχ.1
  · rw [← he', ← Category.assoc]
    exact (isProd_transl e'.hom t).push hχ.1
  · exact LBIso.trans (LB.isLB_pull P.isLB _) P'.isLB (LB.isLB_pull Q.isLB _) hψ.2.2.symm
      (LBIso.trans P'.isLB (LB.isLB_pull Q'.isLB _) (LB.isLB_pull Q.isLB _) hi (SiegPull.lbIso_pull_comp hχ.2.2 _))

theorem lbIso_pull_both {W Y X Z : Scheme.{0}} {L : LB X} {M : LB Z} {a : Y ⟶ X} {b : Y ⟶ Z} (j : W ⟶ Y)
    (hL : L.IsLB) (hM : M.IsLB) :
    LBIso ((L.pull a).pull j) ((M.pull b).pull j) ↔ LBIso (L.pull (j ≫ a)) (M.pull (j ≫ b)) := by
  have k₁ := SiegPull.lbIso_pull_comp (⟨idIso _, idIso_isGen (LB.isLB_pull hL a)⟩ : LBIso (L.pull a) (L.pull a)) j
  have k₂ := SiegPull.lbIso_pull_comp (⟨idIso _, idIso_isGen (LB.isLB_pull hM b)⟩ : LBIso (M.pull b) (M.pull b)) j
  have a₁ := LB.isLB_pull (LB.isLB_pull hL a) j
  have a₂ := LB.isLB_pull (LB.isLB_pull hM b) j
  have b₁ := LB.isLB_pull hL (j ≫ a)
  have b₂ := LB.isLB_pull hM (j ≫ b)
  exact ⟨fun h => LBIso.trans b₁ a₁ b₂ k₁.symm (LBIso.trans a₁ a₂ b₂ h k₂),
    fun h => LBIso.trans a₁ b₁ a₂ k₁ (LBIso.trans b₁ b₂ a₂ h k₂.symm)⟩

theorem potKnown_of_lamIs : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (y : KeyIn K) (P : Out.PolAV (Sp K)) (e : P.A ≅ y.P.A), IsMonHom e.hom → LamIs P.A P.L y.P.A (abelian₂ y.P.A y.P.L) e.hom.left → Known K y → PotKnown K P := by
  intro hL hT K _ _ y P e he hl hk
  let Ω := AlgebraicClosure K
  obtain ⟨p, X, ψ, w, hp, h₂, hψ, hw, hi⟩ := exists_point hL (algebraMap K Ω) y.P P e hl
  haveI := y.P.isAb.smooth
  haveI := P.isAb.proper
  obtain ⟨K₁, p₁, hp₁, _⟩ : ∃ (K₁ : IntermediateField K Ω) (p₁ : Sp K₁ ⟶ y.P.A.left),
      spMap (algebraMap K₁ Ω) ≫ p₁ = p ∧ FiniteDimensional K K₁ := by
    obtain ⟨s, p₁, hp₁⟩ := exists_finset_point y.P.A.hom p hp
    exact ⟨_, p₁, hp₁, IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x⟩
  haveI := epi_spMap (algebraMap K₁ Ω)
  have c₁ : spMap (algebraMap K Ω) = spMap (algebraMap K₁ Ω) ≫ spMap (algebraMap K K₁) :=
    spMap_comp (algebraMap K K₁) (algebraMap K₁ Ω)
  have q₁ : p₁ ≫ y.P.A.hom = spMap (algebraMap K K₁) := by
    rw [← cancel_epi (spMap (algebraMap K₁ Ω)), ← Category.assoc, hp₁, hp, c₁]
  have r₁ : IsProd y.P.A p₁ p₁ (spMap (algebraMap K K₁) ≫ eSec y.P.A) := by
    obtain ⟨u, hu⟩ := exists_isProd p₁ p₁ rfl
    rwa [(cancel_epi (spMap (algebraMap K₁ Ω))).1 (((hu.comp _).unique h₂ hp₁ hp₁).trans
      (by rw [c₁, Category.assoc]) : _ ≫ u = _ ≫ spMap (algebraMap K K₁) ≫ eSec y.P.A)] at hu
  let X₁ : Over (Sp K₁) := Over.mk (pullback.snd P.A.hom (spMap (algebraMap K K₁)))
  let ψ₁ : X₁.left ⟶ P.A.left := pullback.fst _ _
  have hψ₁ : IsPullback ψ₁ X₁.hom P.A.hom (spMap (algebraMap K K₁)) := IsPullback.of_hasPullback _ _
  obtain ⟨w₁, hw₁⟩ := exists_isProd (X₁.hom ≫ p₁) (ψ₁ ≫ e.hom.left)
    (by rw [Category.assoc, q₁, Category.assoc, Over.w e.hom, hψ₁.w])
  let π : X.left ⟶ X₁.left := hψ₁.lift ψ (X.hom ≫ spMap (algebraMap K₁ Ω)) (by rw [hψ.w, c₁, Category.assoc])
  have π₁ : π ≫ ψ₁ = ψ := hψ₁.lift_fst _ _ _
  have π₂ : π ≫ X₁.hom = X.hom ≫ spMap (algebraMap K₁ Ω) := hψ₁.lift_snd _ _ _
  have hπ : IsPullback π X.hom X₁.hom (spMap (algebraMap K₁ Ω)) :=
    IsPullback.of_right (by rw [π₁, ← c₁]; exact hψ) π₂ hψ₁
  have πw : π ≫ w₁ = w := (hw₁.comp π).unique hw (by rw [← Category.assoc, π₂, Category.assoc, hp₁])
    (by rw [← Category.assoc, π₁])
  haveI : IsProper X₁.hom := MorphismProperty.of_isPullback (P := @IsProper) hψ₁ inferInstance
  obtain ⟨s', hs'⟩ := lbIso_descends_to_subfield_containing_finset K₁ Ω (algebraMap K₁ Ω) X₁ X π (P.L.pull ψ₁)
    (y.P.L.pull w₁) hπ inferInstance inferInstance (LB.isLB_pull P.isLB _) (LB.isLB_pull y.P.isLB _)
    ((lbIso_pull_both π P.isLB y.P.isLB).2 (by rw [π₁, πw]; exact hi))
  let K₂ := IntermediateField.adjoin K₁ (s' : Set Ω)
  haveI : FiniteDimensional K₁ K₂ :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsIntegral.isIntegral (R := K) x).tower_top
  haveI : NumberField K₁ := NumberField.of_module_finite K K₁
  haveI : NumberField K₂ := NumberField.of_module_finite K₁ K₂
  let X₂ : Over (Sp K₂) := Over.mk (pullback.snd X₁.hom (spMap (algebraMap K₁ K₂)))
  let χ : X₂.left ⟶ X₁.left := pullback.fst _ _
  have hχ : IsPullback χ X₂.hom X₁.hom (spMap (algebraMap K₁ K₂)) := IsPullback.of_hasPullback _ _
  have i₂ := (lbIso_pull_both χ P.isLB y.P.isLB).1 (hs' K₂ (algebraMap K₁ K₂) (algebraMap K₂ Ω) rfl
    (fun x hx => ⟨⟨x, IntermediateField.subset_adjoin _ _ hx⟩, rfl⟩) X₂ χ hχ)
  refine ⟨K₂, inferInstance, inferInstance, (algebraMap K₁ K₂).comp (algebraMap K K₁), fun F _ j y' φ hφ => ?_⟩
  have c₂ : spMap (j.comp ((algebraMap K₁ K₂).comp (algebraMap K K₁))) =
      (spMap j ≫ spMap (algebraMap K₁ K₂)) ≫ spMap (algebraMap K K₁) := by
    rw [spMap_comp, spMap_comp, Category.assoc]
  let a : y'.P.A.left ⟶ X₁.left := hψ₁.lift φ (y'.P.A.hom ≫ spMap j ≫ spMap (algebraMap K₁ K₂))
    (by rw [hφ.1.1.w, c₂]; simp only [Category.assoc])
  have a₁ : a ≫ ψ₁ = φ := hψ₁.lift_fst _ _ _
  have a₂ : a ≫ X₁.hom = y'.P.A.hom ≫ spMap j ≫ spMap (algebraMap K₁ K₂) := hψ₁.lift_snd _ _ _
  let b : y'.P.A.left ⟶ X₂.left := hχ.lift a (y'.P.A.hom ≫ spMap j) (by rw [a₂, Category.assoc])
  have b₁ : b ≫ χ = a := hχ.lift_fst _ _ _
  have i₃ := (lbIso_pull_both b P.isLB y.P.isLB).1
    (LBIso.chartPull (Geo.Tor.chartPullPull _ b b rfl) (Geo.Tor.chartPullPull _ b b rfl) i₂)
  rw [← Category.assoc, ← Category.assoc, b₁, a₁] at i₃
  refine known_of_point hL hT _ y y' (φ ≫ e.hom.left) (a ≫ w₁)
    ((hφ.1.comp (isGrpPullback_of_iso e)).congr (Category.comp_id _) rfl)
    ((spMap j ≫ spMap (algebraMap K₁ K₂)) ≫ p₁) (by rw [Category.assoc, q₁, c₂]) ?_ ?_
    (LBIso.trans y'.P.isLB (LB.isLB_pull P.isLB _) (LB.isLB_pull y.P.isLB _) hφ.2.2 i₃) hk
  · rw [c₂, Category.assoc _ (spMap (algebraMap K K₁))]
    exact r₁.comp _
  · rw [← Category.assoc, ← a₂, ← a₁, Category.assoc, Category.assoc]
    exact hw₁.comp a

end GlobalTheory.KeyFam.SameLam
end

section -- merged from Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.PotentiallyKnownOfSameLambdaBundleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potentiallyKnown_of_same_lambdaBundle : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] [NumberField K] (y : KeyIn K) (P : Out.PolAV (Sp K)) (e : P.A ≅ y.P.A), IsMonHom e.hom → LamIs P.A P.L y.P.A (abelian₂ y.P.A y.P.L) e.hom.left → Known K y → PotKnown K P := by
  first | exact @GlobalTheory.KeyFam.SameLam.potKnown_of_lamIs | exact GlobalTheory.KeyFam.SameLam.potKnown_of_lamIs | (intros; apply GlobalTheory.KeyFam.SameLam.potKnown_of_lamIs <;> assumption)
end
