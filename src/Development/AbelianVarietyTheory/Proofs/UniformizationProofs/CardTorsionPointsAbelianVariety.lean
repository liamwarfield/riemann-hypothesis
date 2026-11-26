module

public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProjectiveOverRingByChartsAbelianVariety
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MumfordTowerRepWtMulAdd
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankSecPullSandwich
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.DescentPowerIsoEndomorphismAbelianPartUniformiza
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsClosedSubschemeTranslationKernel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGenericFibreIsoOfCompatibleThickenings
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsBundleIsoExtendingGeneric

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LeOfPowLePolyMulPow
namespace GlobalTheory.UU

theorem le_of_pow_le_poly_mul_pow (A B K a g : ℕ)
    (H : ∀ k, A ^ k ≤ K * B ^ k * (1 + k * a) ^ g) : A ≤ B := by
  rcases Nat.eq_zero_or_pos B with hB | hB
  · have := H 1
    simp [hB] at this
    omega
  by_contra hAB
  push Not at hAB
  have hBr : (0 : ℝ) < B := by exact_mod_cast hB
  have hr : (1 : ℝ) < (A : ℝ) / B := by
    rw [one_lt_div hBr]; exact_mod_cast hAB
  have ht := (tendsto_pow_const_div_const_pow_of_one_lt g hr).const_mul
    ((K : ℝ) * (1 + a) ^ g)
  rw [mul_zero] at ht
  have h1 : ∀ᶠ k : ℕ in Filter.atTop,
      (1 : ℝ) ≤ ((K : ℝ) * (1 + a) ^ g) * ((k : ℝ) ^ g / ((A : ℝ) / B) ^ k) := by
    filter_upwards [Filter.eventually_ge_atTop 1] with k hk
    have hk' : A ^ k ≤ K * B ^ k * ((1 + a) * k) ^ g := by
      refine (H k).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ?_ _))
      nlinarith
    have hk2 : (A : ℝ) ^ k ≤ K * (B : ℝ) ^ k * ((1 + a) * k) ^ g := by exact_mod_cast hk'
    have hA : (0 : ℝ) < A := by exact_mod_cast (hB.trans hAB)
    rw [div_pow, ← mul_div_assoc, div_div_eq_mul_div, one_le_div (by positivity)]
    refine hk2.trans (le_of_eq ?_)
    rw [mul_pow]; ring
  have := ge_of_tendsto ht h1
  linarith

theorem degree_eq_pow_of_growth :
    ∀ (h : ℕ → ℕ) (g c C a d q : ℕ), 1 ≤ c → 1 ≤ q → (∀ t t', t ≤ t' → h t ≤ h t') → (∀ t, 1 ≤ t → t ^ g ≤ c * h t ∧ h t ≤ C * t ^ g) → (∀ t, d * h t ≤ h (q * (t + a)) ∧ h (q * t) ≤ d * h (t + a)) → d = q ^ g := by
  intro h g c C a d q hc hq hm hg hd
  have h1 : 1 ≤ h 1 := by
    have := (hg 1 le_rfl).1
    rcases Nat.eq_zero_or_pos (h 1) with h0 | h0
    · simp [h0] at this
    · exact h0
  have up : ∀ k t, h (q ^ k * t) ≤ d ^ k * h (t + k * a) := by
    intro k
    induction k with
    | zero => intro t; simp
    | succ k ih =>
      intro t
      have e1 : q ^ (k + 1) * t = q ^ k * (q * t) := by ring
      rw [e1]
      refine (ih _).trans ?_
      rw [pow_succ, mul_assoc]
      refine Nat.mul_le_mul_left _ ?_
      have e2 : t + (k + 1) * a = t + k * a + a := by ring
      rw [e2]
      refine le_trans (hm _ _ ?_) (hd (t + k * a)).2
      rw [mul_add]
      exact Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hq) _
  have lo : ∀ k, d ^ k ≤ h (q ^ k * (1 + k * a)) := by
    intro k
    induction k with
    | zero => simpa using h1
    | succ k ih =>
      rw [pow_succ, mul_comm]
      refine (Nat.mul_le_mul_left d ih).trans ((hd _).1.trans (hm _ _ ?_))
      have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
      have e : q ^ (k + 1) * (1 + (k + 1) * a) = q * (q ^ k * (1 + k * a) + q ^ k * a) := by ring
      rw [e]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.le_mul_of_pos_left _ hp) _)
  apply le_antisymm
  · apply le_of_pow_le_poly_mul_pow d (q ^ g) C a g
    intro k
    have hp : 1 ≤ q ^ k * (1 + k * a) := Nat.mul_pos (Nat.pow_pos hq) (by omega)
    refine (lo k).trans ((hg _ hp).2.trans (le_of_eq ?_))
    rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k g]; ring
  · apply le_of_pow_le_poly_mul_pow (q ^ g) d (c * C) a g
    intro k
    have hp : 1 ≤ q ^ k := Nat.one_le_pow _ _ hq
    have a1 := (hg _ hp).1
    have a2 := up k 1
    rw [mul_one] at a2
    have a3 := (hg (1 + k * a) (by omega)).2
    calc (q ^ g) ^ k = (q ^ k) ^ g := by rw [← pow_mul, ← pow_mul, mul_comm]
      _ ≤ c * h (q ^ k) := a1
      _ ≤ c * (d ^ k * (C * (1 + k * a) ^ g)) :=
        Nat.mul_le_mul_left _ (a2.trans (Nat.mul_le_mul_left _ a3))
      _ = _ := by ring

end GlobalTheory.UU
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVariety
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UU.TorsionCount

theorem lbIso_pw {Y : Scheme.{0}} {A B : LB Y} (h : LBIso A B) (t : ℤ) : LBIso (AbLaw.pw A t) (AbLaw.pw B t) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => w.s p ^ t⟩, fun p q => ?_⟩
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem pw_pw {X : Scheme.{0}} (H : LB X) (a b : ℤ) : AbLaw.pw (AbLaw.pw H a) b = AbLaw.pw H (a * b) := by
  unfold AbLaw.pw
  congr 1
  funext i j
  exact (zpow_mul _ _ _).symm

def chartPullPw {X Y : Scheme.{0}} (H : LB X) (φ : Y ⟶ X) (t : ℤ) :
    ChartPull ((AbLaw.pw H t).pull φ) (AbLaw.pw (H.pull φ) t) (𝟙 Y) where
  idx j := j
  le _ _ hy := hy
  g y i j hi hj :=
    (gm_pull_g (AbLaw.pw H t) φ (𝟙 Y) y i j hi hj).trans ((map_zpow _ _ t).trans
      ((congrArg (· ^ t) (gm_pull_g H φ (𝟙 Y) y i j hi hj).symm).trans (map_zpow _ _ t).symm))

theorem nonempty_secEquiv {K : Type} [CommRing K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (φ : X ⟶ X)
    (hφ : φ ≫ f = f) {H : LB X} (hH : H.IsLB) (q : ℕ) (h : LBIso (AbLaw.pw H q) (H.pull φ)) (t : ℕ) :
    Nonempty (SecOnR f (AbLaw.pw H ((q * t : ℕ) : ℤ)) ⊤ ≃ₗ[K] SecOnR (φ ≫ f) ((AbLaw.pw H t).pull φ) ⊤) := by
  have h₁ := (lbIso_pw h t).chartPull (chartPullId _) (chartPullPw H φ t)
  rw [pw_pw, ← Nat.cast_mul] at h₁
  obtain ⟨w, hw⟩ := h₁
  rw [hφ]
  exact ⟨SecOnR.linEquiv f (SecOn.congr (isLB_pw hH _) (pull_isLB (isLB_pw hH _) φ) w hw ⊤)⟩

theorem card_torsion_points : GlobalFnsSt → RigiditySt → (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) := by
  intro hG _ k _ _ B _ g n hB hg hn
  haveI := hB.comm
  haveI := hB.smooth
  haveI := hB.proper
  haveI : GeometricallyIntegral B.hom :=
    GlobalTheory.forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ _ hB.smooth hB.geomConnected
  haveI : IsIntegral B.left := GeometricallyIntegral.isIntegral_of_subsingleton B.hom
  have hn0 : n ≠ 0 := by rintro rfl; exact hn Nat.cast_zero
  have hq : 1 ≤ n ^ 2 := Nat.one_le_iff_ne_zero.2 (pow_ne_zero _ hn0)
  have hproj := GlobalTheory.T.isProjectiveOverRingByCharts_abelian_variety k B hB
  obtain ⟨H, m, s, hH, hs, hsym⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmpleBy k B hB hproj
  obtain ⟨r, hr⟩ : ∃ r : LB.Gen (H.pull (eSec B)), r.IsGen :=
    DVR.exists_gen_of_isLB_local (V := k) _ (pull_isLB hH _)
  obtain ⟨M, hM⟩ := (GlobalTheory.T.abelianScheme_cubical_bundle_exists_and_maps hG _ B hB).1 ⟨H, r, hH, hr⟩ (GlobalTheory.AbLaw.CubeProj.exists_gen_theta_abelianVariety hG k B hB hproj H hH) hsym
  have hiso : LBIso (AbLaw.pw H ((n ^ 2 : ℕ) : ℤ)) (H.pull (𝟙 B ^ n).left) := by
    have h := GlobalTheory.T.lbIso_pw_sq_pull_pow_of_isLocalRing k B M n
    rw [hM] at h
    rw [Nat.cast_pow]
    exact h
  have hφ : (𝟙 B ^ n).left ≫ B.hom = B.hom := Over.w _
  haveI : IsFinite (𝟙 B ^ n).left :=
    GlobalTheory.T.isFinite_of_pull_veryAmple_iso_pow k _ _ B.hom _ H H m s (n ^ 2) hH hH inferInstance (by rw [hφ]; exact hs) hq hiso
  haveI : Etale (𝟙 B ^ n).left := GrpTangent.etale_id_pow B (by
    simpa using (Ne.isUnit hn).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom)
  have hcard := GlobalTheory.finrank_eq_card_kernel_points_of_etale k B hB (𝟙 B ^ n)
  have hc : Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} =
      Nat.card {y : 𝟙_ (Over (Sp k)) ⟶ B // y ≫ (𝟙 B ^ n) = 1} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun y => by rw [MonObj.comp_pow, Category.comp_id])
  rw [hc]
  obtain ⟨hfin, hmono, c, C, hc1, hgrow⟩ := GlobalTheory.VeryAmpleGrowth.finite_monotone_growth k B.left B.hom g hg H m s hH hs
  have e := nonempty_secEquiv B.hom _ hφ hH (n ^ 2) hiso
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_shift_finrank_sec_pull_bounds k B.left B.left B.hom (𝟙 B ^ n).left H m s hH hs _ hcard hfin fun t => by
    obtain ⟨e⟩ := e t
    haveI := hfin (n ^ 2 * t)
    exact Module.Finite.equiv e
  rw [pow_mul]
  refine GlobalTheory.UU.degree_eq_pow_of_growth (fun t : ℕ => Module.finrank k (SecOnR B.hom (AbLaw.pw H t) ⊤)) g c C a _ (n ^ 2) hc1 hq
    hmono hgrow fun t => ?_
  obtain ⟨e₁⟩ := e (t + a)
  obtain ⟨e₂⟩ := e t
  exact ⟨(ha t).1.trans e₁.finrank_eq.ge, e₂.finrank_eq.le.trans (ha t).2⟩

end GlobalTheory.UU.TorsionCount
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVarietyStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_torsion_points_abelianVariety : GlobalFnsSt → RigiditySt → (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) := by
  first | exact @GlobalTheory.UU.TorsionCount.card_torsion_points | exact GlobalTheory.UU.TorsionCount.card_torsion_points | (intros; apply GlobalTheory.UU.TorsionCount.card_torsion_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphism
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section
namespace GlobalTheory.UT.PullExp
open GlobalTheory.FieldBaseChange

section Uniq

theorem comb_eq_zero {R K F : Type} [CommRing R] [IsDomain R] [Field K] [Field F] [Algebra K F] [Algebra R K]
    [IsFractionRing R K] {V₀ V V' : Type} [AddCommGroup V₀] [Module R V₀] [AddCommGroup V] [Module K V]
    [AddCommGroup V'] [Module F V'] {J : Type} {P₀ : J → Type} [∀ j, AddCommGroup (P₀ j)] [∀ j, Module R (P₀ j)]
    {P P' : Type} [AddCommGroup P] [Module K P] [AddCommGroup P'] [Module F P'] (X : Submodule R (V₀ × ∀ j, P₀ j))
    (j : J) (ρ : V₀ →ₛₗ[algebraMap R K] V) (ρ' : P₀ j →ₛₗ[algebraMap R K] P)
    (a : V →ₛₗ[algebraMap K F] V') (ha : IsExtension a) (b : P →ₛₗ[algebraMap K F] P') (hb : IsExtension b)
    (hX : ∀ x ∈ X, ρ x.1 = 0 → x.2 j = 0) {T : Type} [Fintype T] (c : T → F) (x : T → V₀ × ∀ j, P₀ j)
    (hx : ∀ i, x i ∈ X) (h : ∑ i, c i • a (ρ (x i).1) = 0) : ∑ i, c i • b (ρ' ((x i).2 j)) = 0 := by
  refine hb.eq_of_coord fun ℓ Λ' hΛ' => ?_
  obtain ⟨Λ, hΛ⟩ := ha.coord ℓ
  obtain ⟨r, hr⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) (fun i => ℓ (c i))
  choose m hm using hr
  have hr : algebraMap R K r ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 (nonZeroDivisors.coe_ne_zero r)
  have e₁ : ρ (∑ i, m i • x i).1 = algebraMap R K r • Λ (∑ i, c i • a (ρ (x i).1)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum, Prod.fst_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΛ, Prod.smul_fst, map_smulₛₗ, hm, smul_smul, Algebra.smul_def]
  have e₂ : ρ' ((∑ i, m i • x i).2 j) = algebraMap R K r • Λ' (∑ i, c i • b (ρ' ((x i).2 j))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum, Prod.snd_sum, Finset.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hΛ', Prod.smul_snd, Pi.smul_apply, map_smulₛₗ, hm, smul_smul, Algebra.smul_def]
  rw [h, map_zero, smul_zero] at e₁
  rw [hX _ (Submodule.sum_mem _ fun i _ => X.smul_mem _ (hx i)) e₁, map_zero] at e₂
  rw [map_zero]
  exact (smul_eq_zero.1 e₂.symm).resolve_left hr

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem term_eq_zero [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (k : ℕ) (α : D.toPre.X)
    (x : IntSec U k × ∀ α, IntTerm D k α) (hx : x ∈ expansionPairs U k) (h : genericSec U k x.1 = 0) :
    x.2 α = 0 := by
  have := U.smooth
  have : Flat G.hom := inferInstance
  have hd := GlobalTheory.ExtUnique.spec_fractionRing R (FractionRing R)
  have : IsSchemeTheoreticallyDominant (jK R) := hd.2
  have : QuasiCompact (jK R) := hd.1
  have h₀ : ∀ j, x.1.f j = 0 := fun j => by
    refine (pullback.fst G.hom (jK R)).app_injective _ (fn_ext fun y hy => ?_)
    have hy' : y ∈ LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j :=
      mem_wchart.2 fun i => mem_wchart.1 hy i
    refine (gs_pull (𝟙 _) _ y _ hy _).trans (Eq.trans ?_ ((congrArg _ (map_zero _)).trans (gs_zero' _ y _ hy)).symm)
    exact (gs_pullFn pullback.condition _ _ (𝟙 _) y hy').symm.trans
      ((congrArg (fun s : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => pullback.fst G.hom (jK R)) (fun _ => (k : ℤ))) =>
        gs (𝟙 _) y (LB.wchart U.LG.L (fun _ : Fin 1 => pullback.fst G.hom (jK R)) j) (LB.Sec.f s j)) h).trans (gs_zero' _ y _ hy'))
  have := D.toPre.P.isAb.smooth
  have : GeometricallyConnected D.toPre.P.A.hom := D.toPre.P.isAb.geomConnected
  refine SecOver.ext _ _ ((sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
    (linComb_isLB _ D.toPre.P.isLB _ _) (x.2 α) fun e j => ?_)
  exact (GlobalTheory.ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1 (WeightPf.weightIndep R I D A G U e k x.1 x.2
    (fun j => (congrArg _ (h₀ j)).trans (map_zero _)) (hx e) α j)

theorem secLin_of_expandsG [IsNoetherianRing R] (hI : I ≤ Ideal.jacobson ⊥) (F : Type) [Field F]
    [Algebra (FractionRing R) F] (k : ℕ) (v : GroupSec U F k) (s : Fam D.toPre F k) (hs : U.ExpandsG F k v s)
    (n : ℕ) (c : Fin n → F) (σ : Fin n → IntSec U k) (f : Fin n → ∀ α : D.toPre.X, IntTerm D k α)
    (hf : ∀ i e, U.ExpandsAt e k (σ i) (f i))
    (hv : GeneratorPullback.SecLin U.LG.L (fun _ : Fin 1 => UnifPre.gFK (G := G) F) (fun _ => (k : ℤ)) v (fun _ : Fin 1 => 𝟙 G.left)
      (fun _ => (k : ℤ)) σ (UnifPre.gFK (G := G) F)
      (fun i => scal (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left (c i))) (α : D.toPre.X) :
    GeneratorPullback.SecLin D.toPre.P.L (DegPre.famφ D.toPre F α) (DegPre.famε k) (s.s α) (D.toPre.famφB α) (DegPre.famε k)
      (fun i => f i α) (DegPre.prB D.toPre F).left (fun i => scal (fst (TF (R := R) F) D.toPre.P.A).left (c i)) := by
  obtain ⟨n', c', x', hx', e₁, e₂⟩ := (expandsG_iff U F k v s).1 hs
  have d₁ := (secLin_iff U.LG.isLB v σ
    (UnifPre.gFK (G := G) F) c (fun i => extendSec U F k (genericSec U k (σ i))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (σ i) q y J) (Category.assoc _ _ _))))).1 hv
  refine (secLin_iff D.toPre.P.isLB
    (famProj D.toPre F k α s) (fun i => f i α) (DegPre.prB D.toPre F).left c
    (fun i => termPull D.toPre (FractionRing R) F k α (genericTerm D k α (f i α))) (fun i y J hJ =>
      (sval_pullOver _ _ _ _ hJ).trans ((sval_pullOver _ _ _ _ hJ).trans
        (congrArg (fun q => sval (f i α) q y J) ((Category.assoc _ _ _).trans (congrArg (𝟙 _ ≫ ·)
          (congrArg (fun q => q.left) (famMap_snd D.toPre (FractionRing R) F)))))))).2 ?_
  have : TopologicalSpace.NoetherianSpace ((Over.pullback (jK R)).obj G).left := noetherianSpace_generic U
  have H := comb_eq_zero (expansionPairs U k) α (genericSec U k) (genericTerm D k α) (extendSec U F k)
    (isExtension_pullOver (isPullback_groupBase F) U.LG.isLB _ _) (termPull D.toPre (FractionRing R) F k α)
    (isExtension_termPull D.toPre _ F k α) (term_eq_zero U hI k α) (Sum.elim c' fun i => -c i)
    (Sum.elim x' fun i => (σ i, f i)) (by rintro (i | i); exacts [hx' i, hf i]) (by
      rw [Fintype.sum_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib]
      rw [← e₁, ← d₁, add_neg_cancel])
  rw [Fintype.sum_sum_type] at H
  simp only [Sum.elim_inl, Sum.elim_inr, neg_smul, Finset.sum_neg_distrib] at H
  rw [← e₂ α] at H
  exact add_neg_eq_zero.1 H

end Uniq

section Norm
variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left}

theorem eSec_comp_one : eSec G ≫ (1 : G ⟶ G).left = eSec G :=
  congrArg (fun q => q.left) ((MonObj.comp_one (M := G) η[G]).trans (by
    show toUnit _ ≫ η[G] = η[G]
    rw [toUnit_unit, Category.id_comp]))

theorem exists_normalised (hL : L.IsLB) (a : G ⟶ G) [IsMonHom a] (k' k : ℤ)
    (β : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 _, a.left] ![k', -k])) (hβ : β.IsGen) :
    ∃ ν : LB.Gen (LB.LinComb L (K := Fin 3) ![𝟙 _, a.left, (1 : G ⟶ G).left] ![k', -k, k - k']), ν.IsGen ∧
      LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ ν (eSec G)) (LB.oneGen L) := by
  have e : (1 : G ⟶ G).left ≫ a.left = (1 : G ⟶ G).left :=
    congrArg (fun q : G ⟶ G => q.left) (MonObj.one_comp a)
  obtain ⟨ν, hν, hv⟩ := exists_gen hL (K' := Fin 3) (φ' := ![𝟙 _, a.left, (1 : G ⟶ G).left]) (ε' := ![k', -k, k - k'])
    (fun V _ h => by
      rw [Fintype.prod_sum_type, Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_three]
      show h (𝟙 _) ^ k' * h a.left ^ (-k) * (h ((1 : G ⟶ G).left ≫ 𝟙 _) ^ (-k') * h ((1 : G ⟶ G).left ≫ a.left) ^ (- -k)) =
        h (𝟙 _) ^ k' * h a.left ^ (-k) * h (1 : G ⟶ G).left ^ (k - k')
      rw [e, Category.comp_id, ← zpow_add, neg_neg, neg_add_eq_sub])
    (LB.mulGen L _ _ _ _ β (LB.invGen L _ _ (LB.pullGen L _ _ β (1 : G ⟶ G).left)))
    (mulGen_isGen _ _ _ _ _ _ _ hβ (invGen_isGen _ _ _ _ (pullGen_isGen _ _ _ _ hβ _)))
  refine ⟨ν, hν, corr_of_val hL fun y J hJ => ?_⟩
  rw [val_pull hJ, val_one, hv _ _ y J hJ, val_mul hJ, val_inv, val_pull hJ, Category.id_comp, eSec_comp_one,
    mul_inv_cancel]

end Norm

variable {R : Type} [CommRing R] [IsDomain R]

theorem normd_val_eq (hG : GlobalFnsSt) {D : DegPre R} {K : Type} [Fintype K] {φ : K → (D.P.A.left ⟶ D.P.A.left)}
    {ε : K → ℤ} {u u' : LB.Gen (LB.LinComb D.P.L φ ε)} (hu : Normd u) (hu' : Normd u') {Z : Scheme.{0}}
    (r : Z ⟶ D.P.A.left) (z : Z) (J) (hJ : Good D.P.L z J) : val u r z J = val u' r z J := by
  refine gen_unique D.P.isLB D.P.A.hom (eSec D.P.A) (Over.w η[D.P.A]) (hG _ _ D.P.isAb).2 hu.1 hu'.1
    (fun y J hJ => ?_) Z r z J hJ
  have a := val_corr hJ hu.2 (𝟙 _)
  have a' := val_corr hJ hu'.2 (𝟙 _)
  rw [val_pull hJ, Category.id_comp] at a a'
  exact a.trans a'.symm

theorem sval_comb {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k n : ℕ} {c : Fin n → F}
    {χ : D.X} {s : LB.Sec (LB.LinComb D.P.L (DegPre.famφ D F χ) (DegPre.famε k))} {f : Fin n → D.SecB k χ}
    (h : GeneratorPullback.SecLin D.P.L (DegPre.famφ D F χ) (DegPre.famε k) s (D.famφB χ) (DegPre.famε k) f (DegPre.prB D F).left
      (fun i => scal (fst (TF (R := R) F) D.P.A).left (c i))) (b : TF (R := R) F ⟶ D.P.A) (z) {J}
    (hJ : Good D.P.L z J) :
    sval s (lift (𝟙 (TF (R := R) F)) b).left z J = ∑ i, cst F z (c i) * sval (f i) b.left z J := by
  refine (GlobalTheory.BoxExpansion.secLin_val h _ z hJ).trans (Finset.sum_congr rfl fun i _ => ?_)
  have e₁ : (lift (𝟙 (TF (R := R) F)) b).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    by
    rw [← Over.comp_left, lift_fst]; rfl
  have e₂ : (lift (𝟙 (TF (R := R) F)) b).left ≫ (DegPre.prB D F).left = b.left :=
    by
    rw [← Over.comp_left, lift_snd]
  rw [e₂]
  exact congrArg (· * _) ((gs_scal _ _ z (c i)).trans (congrArg (fun q => constVal q z (c i)) e₁))

theorem main : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  intro hL R _ _ _ I hI D A G _ _ hG U F _ _ _ E hh k' k hk hk' ⟨β₀, hβ₀⟩
  have hGF := hL.1.globalFns
  have := hI.1
  have := hI.2.2.2
  have := E.homG
  obtain ⟨β, hβ, hβ'⟩ := exists_normalised U.LG.isLB E.aG k' k β₀ hβ₀
  obtain ⟨κ₀, hκ₀, hrel⟩ := GlobalTheory.T.descent_powerIso_endomorphism_abelianPart_uniformization hL R I hI D A G hG U E k' k β hβ hβ'
  refine ⟨⟨κ₀, hκ₀⟩, ?_⟩
  intro w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' s s' ⟨v, hv, n, c, σ, f, h₁, h₂, h₃⟩ ⟨v', hv', hs'⟩ htw κ hκ g g' hg w' w hw' hw₁ hww
  choose σ' f' p₁ p₂ p₃ p₄ using fun i => GlobalTheory.T.pullback_section_endomorphism_expansion R I D A G U.toUnifPre E hh k' k β hβ κ₀ hκ₀.1 hrel (σ i) (f i) (h₁ i)
  have tw := GlobalTheory.T.endU_twist_of_iso hGF R I D A G U.toUnifPre E F k' k β hβ hβ' w₀ ρ hw ψ m hm hψ hm' α hα hα' t t' v v' hv hv' htw
  have H := secLin_of_expandsG U.toUnifPre (IsAdicComplete.le_jacobson_bot I) F k' v' s' hs' n c σ' f' p₁
    ((secLin_iff_val U.LG.isLB _ _ _ _).2 fun y J hJ => by
      rw [tw y J hJ, GlobalTheory.BoxExpansion.secLin_val h₂ _ y hJ, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      have e₁ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
          (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left := by
        rw [← Over.comp_left, whiskerLeft_fst]
      have e₂ : ((TFK (R := R) F) ◁ (Over.pullback (jK R)).map E.aG).left ≫ UnifPre.gFK (G := G) F =
          UnifPre.gFK (G := G) F ≫ E.aG.left := by
        rw [UnifPre.gFK, ← Category.assoc, ← Over.comp_left, whiskerLeft_snd, Over.comp_left, Category.assoc,
          Category.assoc]
        exact congrArg (_ ≫ ·) (pullback.lift_fst _ _ _)
      rw [p₂ i _ _ y J hJ, gs_scal, gs_scal, e₁, e₂, Category.id_comp, Category.id_comp, _root_.mul_assoc])
  refine ⟨fun χ => CoefBasic.coef_eq fun z J hJ => ?_, fun b hb => CoefBasic.coef_eq fun z J hJ => ?_⟩
  · have a := CoefBasic.isCoef_coef g' hw₁ χ s z J hJ
    have e : g.b.left ≫ D.toPre.P.A.hom = (TF (R := R) F).hom := Over.w g.b
    have e' : g'.b.left = g.b.left ≫ E.aB.left := congrArg (fun q => q.left) hg.1
    rw [sval_comb (h₃ χ) _ z hJ, hg.2 χ z J hJ, ← hww z J hJ, e', normd_val_eq hGF hκ hκ₀ _ z J hJ] at a
    rw [sval_comb (H (E.h χ)) _ z hJ]
    simp only [p₃ _ χ _ _ z J hJ, e, ← _root_.mul_assoc, ← Finset.sum_mul]
    have e₃ : (rigV D.toPre (TF (R := R) F).hom z J).val ^ k' =
        (rigV D.toPre (TF (R := R) F).hom z J).val ^ k * (rigV D.toPre (TF (R := R) F).hom z J ^ ((k' : ℤ) - k)).val := by
      rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast,
        ← zpow_add, add_sub_cancel]
    rw [e₃, ← _root_.mul_assoc, a]
    simp only [Units.val_mul]
    ring
  · rw [sval_comb (H b) _ z hJ, CoefBasic.cst_eq, map_zero, zero_mul, Finset.sum_eq_zero, zero_mul, zero_mul]
    intro i _
    exact (congrArg _ ((congrArg (gs _ z _) (p₄ i b hb _)).trans (gs_zero' _ z _ (hJ.mem _ _)))).trans (mul_zero _)

end GlobalTheory.UT.PullExp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpansionPullbackSectionEndomorphismStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.expansion_pullback_section_endomorphism : LL → AllUF fun {R} _ _ {I} {D} {A} {G} _ _ U F _ _ => ∀ (E : EndU U.toUnifPre), Function.Injective E.h → ∀ (k' k : ℕ), 1 ≤ k → 1 ≤ k' → (∃ β : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 _, E.aG.left] ![(k' : ℤ), -(k : ℤ)]), β.IsGen) → (∃ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ) ∧ ∀ (w₀ : W0 U.toUnifPre) (ρ), NormW U.toUnifPre w₀ ρ → ∀ (ψ : (TFK (R := R) F ⊗ A.A) ⟶ (TFK (R := R) F ⊗ A.A)) (m : (TFK (R := R) F ⊗ A.A) ⟶ A.A) (hm : ψ ≫ snd _ _ = m), ψ ≫ fst _ _ = fst _ _ → m = snd _ _ ≫ E.aA → ∀ (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![(snd (TFK (R := R) F) A.A).left, m.left] ![(k' : ℤ), -(k : ℤ)])), α.IsGen → LB.Gen.Corr A.L _ _ _ _ (LB.pullGen A.L _ _ α (ptSecT A.A 1).left) (rigT A.A A.L ρ (TFK (R := R) F) ((k' : ℤ) - k)) → ∀ (t : SecA A F k) (t' : SecA A F k') s s', U.ExpandsF F k w₀ t s → U.ExpandsF F k' w₀ t' s' → IsTwistPull A.A A.L ψ m hm k' k α t t' → ∀ κ : LB.Gen (kapLB D.toPre E.aB k' k), Normd κ → ∀ (g g' : GtPtF D.toPre F), E.Act g g' → ∀ (w' : Frm D.toPre F k' g.b) (w : Frm D.toPre F k g'.b), w'.IsGen → w.IsGen → (∀ z J, Good D.toPre.P.L z J → val w' (𝟙 _) z J * val κ g.b.left z J = val w (𝟙 _) z J) → (∀ χ, coef s' g w' (E.h χ) = coef s g' w χ) ∧ ∀ β, β ∉ Set.range E.h → coef s' g w' β = 0 := by
  first | exact @GlobalTheory.UT.PullExp.main | exact GlobalTheory.UT.PullExp.main | (intros; apply GlobalTheory.UT.PullExp.main <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmple
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmple
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.KernelRep

theorem exists_finite_closed_kernel : GlobalFnsSt → ∀ (V : Type) [CommRing V] (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ L : LB B.left, L.IsLB → RelAmple B L → ∃ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left ∧ IsFinite H.hom ∧ (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) := by
  intro hG V _ B _ hB L hL hA
  have hP : IsProjBy B.hom := (GlobalTheory.AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral _ B L hB hL hA V
    (𝟙 _) B.left (𝟙 _) B.hom IsPullback.of_id_fst).1
  obtain ⟨hO, -, hK⟩ := GlobalTheory.UU.TrivTwist.inK_iff_trivial_twist _ B L hL
  obtain ⟨H, j, hj, hH⟩ := GlobalTheory.T.exists_closed_subscheme_translation_kernel hG V B hB hP L (pw L 0) hL hO
  have : IsCommMonObj B := hB.comm
  exact ⟨H, j, hj, GlobalTheory.AmpleStabFinite.isFinite_of_relAmple hG V B hB L (pw L 0) hL hO hA H j hj hH,
    fun T x => (hK _ rfl T x).trans (hH T x)⟩

end GlobalTheory.KernelRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteClosedSubschemeRepresentsKernelAmpleStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_closed_subscheme_represents_kernel_ample : GlobalFnsSt → ∀ (V : Type) [CommRing V] (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ L : LB B.left, L.IsLB → RelAmple B L → ∃ (H : Over (Sp V)) (j : H ⟶ B), IsClosedImmersion j.left ∧ IsFinite H.hom ∧ (∀ (T : Over (Sp V)) (x : T ⟶ B), GlobalTheory.MemKL B L x ↔ ∃ z : T ⟶ H, z ≫ j = x) := by
  first | exact @GlobalTheory.KernelRep.exists_finite_closed_kernel | exact GlobalTheory.KernelRep.exists_finite_closed_kernel | (intros; apply GlobalTheory.KernelRep.exists_finite_closed_kernel <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoUniformisationsOfIsoDegenerationData
section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoUniformisationsOfIsoDegenerationData
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem pmaps_rig_of_thick_compat {R : Type} [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {D D' : DegData R I} {A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {G G' : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']
    (U : UnifPre I D A G) (U' : UnifPre I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre)
    (j : ∀ e : ℕ, thickObj R I e G' ⟶ thickObj R I e G) (hj : ∀ e, IsMonHom (j e))
    {F : G'.left ⟶ G.left} (he : eSec G' ≫ F = eSec G)
    (wL : LB.Iso U'.LG.L (U.LG.L.pull F)) (hw : wL.IsGen)
    (H : ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G').left) (z : Z) (jM : D.toPre.P.L.ι)
      (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι),
      (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) ((U'.gt e).pG.left (r z)) ∈
        D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' →
      (fstG I e G).left ((j e).left (r z)) ∈ U.LG.L.U jL → (fstG I e G').left (r z) ∈ U'.LG.L.U jL' →
      Geo.Tor.gw hD.w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') =
        Geo.Tor.gw (U.w e) (r ≫ (j e).left) z jM (fun _ => jL) *
          Geo.Tor.gw wL (r ≫ (fstG I e G').left) z jL jL') :
    PMaps wL (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) U'.LG.rig U.LG.rig (𝟙 _) := by
  refine AbelianPartIso.pmaps_of_thickenings hI U.LG.isLB U'.LG.isLB wL hw _ _ he _ U'.LG.rigGen _ U.LG.rigGen
    fun e z p q hp hq => ?_
  have hs := Geo.Tor.specOf_id R
  have hB : eSec D'.toPre.P.A ≫ hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)) =
      eSec D.toPre.P.A := hD.he.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _))
  have hje : eSec (thickObj R I e G') ≫ (j e).left = eSec (thickObj R I e G) :=
    congrArg Over.Hom.left (hj e).one_hom
  obtain ⟨m, hm⟩ := Geo.Tor.exists_chart D.toPre.P.isLB ((UnitValue.thU R I e ≫ eSec D.toPre.P.A) z)
  obtain ⟨m', hm'⟩ := Geo.Tor.exists_chart D'.toPre.P.isLB ((UnitValue.thU R I e ≫ eSec D'.toPre.P.A) z)
  have hm₂ : (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R)))
      ((UnitValue.thU R I e ≫ eSec D'.toPre.P.A) z) ∈ D.toPre.P.L.U m :=
    (congrArg (fun g => (UnitValue.thU R I e ≫ g) z ∈ D.toPre.P.L.U m) hB).mpr hm
  have e₁ := UnitValue.wv_rig U e z m p hm hp
  have e₂ := UnitValue.wv_rig U' e z m' q hm' hq
  have e₃ := (Geo.Tor.maps_iff hD.w _ (fun _ => eSec D.toPre.P.A) _ D'.toPre.rig D.toPre.rig
    (specOf (RingHom.id R)) _ (rigPull_le _ _ hD.he D.toPre.P.L) (fun _ => rfl)).1 hD.w_rig _
    (UnitValue.thU R I e) z (fun _ => m) (fun _ => m') (fun _ => hm₂) (fun _ => hm')
  have e₄ := H e _ (eSec (thickObj R I e G')) z m m' p q
    ((congrArg (fun g => (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) (g z) ∈
      D.toPre.P.L.U m) (UnitValue.eSec_pGl U' e)).mpr hm₂)
    ((congrArg (fun g => g z ∈ D'.toPre.P.L.U m') (UnitValue.eSec_pGl U' e)).mpr hm')
    ((congrArg (fun g => g z ∈ U.LG.L.U p)
      (((congrArg (· ≫ (fstG I e G).left) hje)).trans (UnitValue.eSec_fGl (G := G) e))).mpr hp)
    ((congrArg (fun g => g z ∈ U'.LG.L.U q) (UnitValue.eSec_fGl (G := G') e)).mpr hq)
  have ht : UnitValue.thU R I e ≫ specOf (RingHom.id R) = UnitValue.thU R I e :=
    (congrArg (_ ≫ ·) hs).trans (Category.comp_id _)
  rw [UnitValue.eSec_pGl U' e, UnitValue.eSec_fGl (G := G') e, hje] at e₄
  rw [ht, Fintype.prod_unique, zpow_one] at e₃
  exact mul_left_cancel (e₁.trans (e₃.trans ((congrArg _ e₂.symm).trans ((mul_assoc _ _ _).symm.trans
    ((congrArg (· * _) e₄).trans (mul_assoc _ _ _))))))

theorem exists_iso_isPullUnif_of_isPullDeg : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ (ψ : G' ≅ G) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom ψ.hom ∧ IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left ∧ IsPullUnif (RingHom.id R) hD bc U U' := by
  intro hL hL2 R _ _ _ I hR hI D D' A A' G G' _ _ _ _ hG hG' U U' hD
  obtain ⟨j, hj⟩ := exists_thick_iso_of_isPullDeg hL.globalFns R I hR hI D D' A A' G G' hG hG' U U' hD
  obtain ⟨ΦK, wK, hK⟩ := GlobalTheory.T.exists_genericFibreIso_of_compatible_thickenings hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj
  obtain ⟨ψ, hψ⟩ := GlobalTheory.T.generic_iso_extends_semiAbelian_dvr_inducing_formal hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hK
  obtain ⟨wL, hwL, H⟩ := GlobalTheory.T.exists_bundleIso_extending_generic_alt hL hL2 R I hR hI D D' A A' G G' hG hG' U U' hD j hj ΦK wK hK ψ hψ
  obtain ⟨hm, -, hf⟩ := hψ
  have hs := Geo.Tor.specOf_id R
  obtain ⟨bc, mbc, hbc⟩ := grpPullback_iso ((isGrpPullback_of_iso ψ).congr hs.symm rfl)
    (isGrpPullback_pullback G (specOf (RingHom.id R)))
  have hbc' : bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left := hbc
  have he₀ : eSec G' ≫ ψ.hom.left = eSec G := congrArg Over.Hom.left hm.one_hom
  have he : eSec G' ≫ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) =
      specOf (RingHom.id R) ≫ eSec G :=
    (congrArg (_ ≫ ·) hbc').trans (he₀.trans ((congrArg (· ≫ _) hs).trans (Category.id_comp _)).symm)
  have hI' : I ≠ ⊤ := hI ▸ (IsLocalRing.maximalIdeal.isMaximal R).ne_top
  have hr := pmaps_rig_of_thick_compat hI' U.toUnifPre U'.toUnifPre hD (fun e => (j e).hom) (fun e => (hj e).1)
    he₀ wL hwL H
  refine ⟨ψ, bc, hm, mbc, hbc', (isPullUnif_iff_stalks R R I I _ D D' hD A A' G G' bc U U').2
    ⟨pullCongr hbc'.symm wL, (isGen_iff _).2 (pgen_pullCongr _ ((isGen_iff _).1 hwL)), he, ?_, fun e =>
      ⟨(j e).hom.left, (hf e).symm.trans (congrArg (_ ≫ ·) hbc'.symm), (hj e).2.2,
        fun Z r z jM jM' jL jL' h₁ h₂ h₃ h₄ => ?_⟩⟩⟩
  · refine (Geo.Tor.maps_iff _ _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (specOf (RingHom.id R)) _
      (rigPull_le _ _ he U.LG.L) (fun _ => rfl)).2 (pmaps_pullCongr _ ?_)
    exact (congrArg (PMaps wL (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) U'.LG.rig U.LG.rig)
      hs).mpr hr
  · rw [gw_pullCongr]
    refine H e Z r z jM jM' jL jL' h₁ h₂ ?_ h₄
    rw [hbc'] at h₃
    exact (congrArg (fun g => g (r z) ∈ U.LG.L.U jL) (hf e)).mp h₃

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoUniformisationsOfIsoDegenerationDataStatement
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_iso_uniformisations_of_iso_degeneration_data : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre), ∃ (ψ : G' ≅ G) (bc : G' ≅ (Over.pullback (specOf (RingHom.id R))).obj G), IsMonHom ψ.hom ∧ IsMonHom bc.hom ∧ bc.hom.left ≫ pullback.fst G.hom (specOf (RingHom.id R)) = ψ.hom.left ∧ IsPullUnif (RingHom.id R) hD bc U U' := by
  first | exact @GlobalTheory.exists_iso_isPullUnif_of_isPullDeg | exact GlobalTheory.exists_iso_isPullUnif_of_isPullDeg | (intros; apply GlobalTheory.exists_iso_isPullUnif_of_isPullDeg <;> assumption)
end
end
