module

public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceValuesIntegralTorsionBoundShortestVec
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemistableReductionPpavPadicField
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValuationNonnegIffSpanMultiplicationTranslates

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralBasisCombinationOfIntegralFamily
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetricLiftNormalisedPullbackThetaSmul
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetricLiftNormalisedPullbackThetaSmul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre

theorem act_normPull_smul : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th th' : SecA A F 1) (c : F), (∀ j, th.f j = liftFun A.A _ (cF R c) * th'.f j) → ∀ (s₁ σ t : SecA A F (m ^ 2)) (x : TFK (R := R) F ⟶ A.A) (θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := R) F)) (c' : F), x ^ (m ^ 2) = 1 → IsNormPull A ρ m (m ^ 2) th s₁ → SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ → IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₁ σ → ThC A ρ m th' x t c' → ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j := by
  intro hLL R _ _ _ A F _ _ ρ hρ m hm th th' c hc s₁ σ t x θ c' hx ⟨α, hα, hn, hs₁⟩ hθ hσ
    ⟨α', s₁', θ', hα', hn', hs₁', hθ', ht', _⟩
  have hLaw : Laws := hLL.1
  have hL := A.isLB
  let T := TFK (R := R) F
  have hu : IsUnit ((m ^ 2 : ℕ) : Γ(Spec (CommRingCat.of (FractionRing R)), ⊤)) := by
    let e := (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).commRingCatIsoToRingEquiv.symm
    rw [← map_natCast e]
    refine (IsUnit.mk0 _ ?_).map e
    rw [← map_natCast (algebraMap R (FractionRing R))]
    exact (map_ne_zero_iff _ (IsFractionRing.injective R (FractionRing R))).2
      (Nat.cast_ne_zero.2 (pow_ne_zero 2 hm.pos.ne'))
  obtain ⟨-, huniq⟩ := hLaw.symLift _ A (m ^ 2) hm.pow hu T x hx
  have ea := gen_unique hL (fst T A.A).left (ptSecT A.A 1).left NormTheta.ptSec_fst
    (CommPairing.surj_fst hLaw.globalFns A.isAb T) hα hα' (fun y J hJ => by
      have a := (val_corr hJ hn (𝟙 _)).trans (val_corr hJ hn' (𝟙 _)).symm
      rwa [val_pull hJ, val_pull hJ, Category.id_comp] at a)
  have eθ := huniq θ θ' hθ hθ'
  have ept : θ.pt = θ'.pt := hθ.pt_eq.trans hθ'.pt_eq.symm
  have f₁ : (mulT A.A T m).left ≫ (fst T A.A).left = (fst T A.A).left := by
    rw [← Over.comp_left, mulT, lift_fst]
  have f₂ : (translT A.A θ.pt).left ≫ (fst T A.A).left = (fst T A.A).left := by
    rw [← Over.comp_left, translT, lift_fst]
  have key : SecM.ofSec A.A σ = cF R c • SecM.ofSec A.A t := ThetaAct.sv_ext hL fun y J hJ => by
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm
    have a₁ := ThetaLin.sval_of_isTwistPull A.A hσ (𝟙 _) y hJ
    have a₂ := ThetaLin.sval_of_isTwistPull A.A hs₁ (𝟙 _ ≫ (translT A.A θ.pt).left) y hJ
    have a₃ := ThetaPtMove.sv_of_eq_mul hc ((𝟙 _ ≫ (translT A.A θ.pt).left) ≫ (mulT A.A T m).left) y hJ
    have b₁ := ThetaLin.sval_of_isTwistPull A.A ht' (𝟙 _) y hJ
    have b₂ := ThetaLin.sval_of_isTwistPull A.A hs₁' (𝟙 _ ≫ (translT A.A θ.pt).left) y hJ
    rw [← val_corr hJ eθ, ← ept, b₂, ← ea _ _ y J hJ] at b₁
    rw [Category.assoc _ (mulT A.A T m).left (fst T A.A).left, f₁, Category.assoc _ _ (fst T A.A).left, f₂] at a₃
    refine a₁.trans (Eq.trans ?_ (congrArg (_ * ·) b₁.symm))
    rw [a₂]
    refine (congrArg (fun q => _ * (_ * q)) a₃).trans ?_
    ring
  exact fun j => congrArg (fun q => q.1 j) key

end GlobalTheory.TestFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SymmetricLiftNormalisedPullbackThetaSmulStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.symmetricLift_normalisedPullback_theta_smul : LL → ∀ (R : Type) [CommRing R] [IsDomain R] [CharZero R] (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (F : Type) [Field F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))), ρ.IsGen → ∀ (m : ℕ), Odd m → ∀ (th th' : SecA A F 1) (c : F), (∀ j, th.f j = liftFun A.A _ (cF R c) * th'.f j) → ∀ (s₁ σ t : SecA A F (m ^ 2)) (x : TFK (R := R) F ⟶ A.A) (θ : ThetaGrp A.A A.L ((m ^ 2 : ℕ) : ℤ) (TFK (R := R) F)) (c' : F), x ^ (m ^ 2) = 1 → IsNormPull A ρ m (m ^ 2) th s₁ → SymLift A.A A.L ((m ^ 2 : ℕ) : ℤ) (m ^ 2) x θ → IsActOf A.A A.L ((m ^ 2 : ℕ) : ℤ) θ s₁ σ → ThC A ρ m th' x t c' → ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j := by
  first | exact @GlobalTheory.TestFibre.act_normPull_smul | exact GlobalTheory.TestFibre.act_normPull_smul | (intros; apply GlobalTheory.TestFibre.act_normPull_smul <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralBasisCombinationOfIntegralFamily
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory.TestFibre

theorem exists_nsmul_of_nsmul_eq_zero {K : Type} {r N : ℕ} (hr : 0 < r) (hN : 0 < N) (a₀ : K → ZMod (r * N))
    (h : N • a₀ = 0) : ∃ a : K → ZMod (r * N), r • a = a₀ := by
  haveI : NeZero (r * N) := ⟨(Nat.mul_pos hr hN).ne'⟩
  have key : ∀ i, ∃ b : ZMod (r * N), r • b = a₀ i := by
    intro i
    have h1 : ((N * (a₀ i).val : ℕ) : ZMod (r * N)) = 0 := by
      have := congrFun h i
      simpa [nsmul_eq_mul] using this
    rw [ZMod.natCast_eq_zero_iff, _root_.mul_comm N] at h1
    obtain ⟨d, hd⟩ := Nat.dvd_of_mul_dvd_mul_right hN h1
    refine ⟨(d : ZMod (r * N)), ?_⟩
    rw [nsmul_eq_mul, ← Nat.cast_mul, ← hd, ZMod.natCast_zmod_val]
  choose a ha using key
  exact ⟨a, funext ha⟩

theorem exists_span_translates_of_eq_sq (h : Laws) (h₂ : Laws2) {V : Type} [CommRing V] [IsDomain V]
    [IsDiscreteValuationRing V] [CharZero V] (hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V) {ϖ : V}
    (hϖ : Irreducible ϖ) {D : DegData V (IsLocalRing.maximalIdeal V)} {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) {A : PolAV (Spec (CommRingCat.of (FractionRing V)))} {G : Over (Spec (CommRingCat.of V))}
    [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif (IsLocalRing.maximalIdeal V) D A G)
    (w₀ : W0 U.toUnifPre) (rig : LB.Gen (A.L.pull (eSec A.A))) (hw : NormW U.toUnifPre w₀ rig)
    (th th' : SecA A F 1) (ϑ : Fam D.toPre F 1) (hϑ : U.ExpandsF F 1 w₀ th' ϑ) (hP : Prim D Q v ϑ) (c : F)
    (hth : ∀ j, th.f j = liftFun A.A _ (cF V c) * th'.f j) (m : ℕ) (hm : Odd m) (hu : IsUnit (m : V)) (h3 : 3 ≤ m)
    (N : ℕ) (hN : N = m ^ 2) (Φ : Fam D.toPre F N) (hΦ : NuGe D Q F v N Φ 0) :
    ∃ (n : ℕ) (a : Fin n → F) (z : Fin n → (TFK (R := V) F ⟶ A.A)) (t : Fin n → SecA A F N)
      (r : Fin n → Fam D.toPre F N),
      (∀ i, 0 ≤ v (a i) ∧ z i ^ N = 1 ∧ U.ExpandsF F N w₀ (t i) (r i) ∧
        ∀ (s₁ σ : SecA A F N) (θ : ThetaGrp A.A A.L (N : ℤ) (TFK (R := V) F)), IsNormPull A rig m N th s₁ →
          SymLift A.A A.L (N : ℤ) N (z i) θ → IsActOf A.A A.L (N : ℤ) θ s₁ σ →
          ∀ j, σ.f j = liftFun A.A _ (cF V c) * (t i).f j) ∧ Φ = ∑ i, a i • r i := by
  subst hN
  obtain ⟨hL, h1, h2, h3', h4⟩ := laws_all h h₂
  obtain ⟨n, a, z, t, c', r, H, hs⟩ :=
    (GlobalTheory.T.valuation_nonneg_iff_span_multiplicationTranslates hL h1 h2 h3' h4 V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ rig hw th' ϑ hϑ hP m hm hu h3 Φ).1 hΦ
  refine ⟨n, a, z, t, r, fun i => ?_, hs⟩
  obtain ⟨ha, hz, hT, hE⟩ := H i
  exact ⟨ha, hz, hE, fun s₁ σ θ hs₁ hθ hσ =>
    GlobalTheory.T.symmetricLift_normalisedPullback_theta_smul hL V A F rig hw.2.1 m hm th th' c hth s₁ σ (t i) (z i) θ (c' i) hz hs₁ hθ hσ hT⟩

theorem IsComb.of_eq_mul {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} {J : Type} [Fintype J] {s : J → SecA A F k} {b : J → F}
    {σ t : SecA A F k} (hσ : IsComb A s b σ) {c : F} (hc : c ≠ 0)
    (ht : ∀ j, σ.f j = liftFun A.A _ (cF R c) * t.f j) : IsComb A s (fun l => c⁻¹ * b l) t := by
  intro j
  have hmul : ∀ x y : F, (liftFun A.A _ (cF R (x * y)) : Γ((TFK (R := R) F ⊗ A.A).left, (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U j)) = liftFun A.A _ (cF R x) * liftFun A.A _ (cF R y) := by
    intro x y
    simp only [liftFun, cF, map_mul]
  have hone : (liftFun A.A _ (cF R (1 : F)) : Γ((TFK (R := R) F ⊗ A.A).left, (LPow A.A A.L (k : ℤ) (TFK (R := R) F)).U j)) = 1 := by
    simp only [liftFun, cF, map_one]
  have h1 : t.f j = liftFun A.A _ (cF R c⁻¹) * σ.f j := by
    rw [ht j, ← _root_.mul_assoc, ← hmul, inv_mul_cancel₀ hc, hone, _root_.one_mul]
  rw [h1, hσ j, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by rw [hmul, _root_.mul_assoc]

theorem exists_isComb_expands_of_nuGe_zero : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → c ≠ 0 → ∀ Φ : Fam u.D.toPre (PadicAlgCl p) S.N, NuGe u.D Q (PadicAlgCl p) v S.N Φ 0 → ∃ (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N), (∀ j, ‖c * b j‖ ≤ 1) ∧ IsComb u.A s b σ ∧ u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ := by
  intro h h₂ _ o Ω _ _ _ _ S ρ p _ y₀ u l hy x rig e th s hx hs ϖ Q v lam hϖ hv hNorm w₀ th' ϑ c hw hϑ hP hth hc Φ hΦ
  obtain ⟨hchar, hun, hadm, -⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hy
  obtain ⟨hadd, -, hbij, -⟩ := (GlobalTheory.T.uniformisedModel_torsionPoints_group_pairing h o Ω S ρ p y₀ u).2 x hx
  obtain ⟨-, -, -, -, hpull, hact⟩ := hs
  obtain ⟨-, hQ, -, hle, -⟩ := hNorm
  have hN0 : 0 < S.N := lt_of_lt_of_le (by norm_num) S.N_ge
  have hn3 : 3 ≤ ρ.n := by
    have h2 := ρ.n_prime.two_le
    obtain ⟨d, hd⟩ := ρ.n_odd
    omega
  have hm3 : 3 ≤ ρ.n ^ ρ.k :=
    hn3.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
  have hmu : IsUnit ((ρ.n ^ ρ.k : ℕ) : u.V) := by
    rw [Nat.cast_pow]; exact hun.pow _
  obtain ⟨n, a, z, t, r, H, hΦs⟩ := exists_span_translates_of_eq_sq h h₂ u.complete hϖ hQ hv u.semi u.U w₀ rig hw
    th th' ϑ hϑ hP c hth (ρ.n ^ ρ.k) ρ.n_odd.pow hmu hm3 S.N ρ.N_eq Φ hΦ
  have hx0 : x 0 = 1 := by
    have := hadd 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have hxs : ∀ (k : ℕ) (b : S.Gam), x (k • b) = x b ^ k := by
    intro k b
    induction k with
    | zero => rw [zero_nsmul, hx0, pow_zero]
    | succ k ih => rw [succ_nsmul, hadd, ih, pow_succ]
  have hpt : ∀ i, ∃ g : S.Gam, x (S.r • g) = z i := by
    intro i
    obtain ⟨a₀, ha₀, -⟩ := hbij (z i) (by rw [_root_.mul_comm S.r, pow_mul, (H i).2.1, one_pow])
    obtain ⟨a₁, -, hu₁⟩ := hbij 1 (one_pow _)
    have h0 : S.N • a₀ = 0 :=
      (hu₁ _ (by show x _ = 1; rw [hxs, ha₀, (H i).2.1])).trans (hu₁ 0 hx0).symm
    obtain ⟨g, hg⟩ := exists_nsmul_of_nsmul_eq_zero S.r_pos hN0 a₀ h0
    exact ⟨g, by rw [← ha₀, ← hg]⟩
  choose g hg using hpt
  have ht : ∀ i, IsComb u.A s (fun j => c⁻¹ * y₀ (algebraMap o S.R (S.ρ (g i) j ρ.i₀))) (t i) := by
    intro i
    obtain ⟨θ, hθ, hθa⟩ := hact (g i)
    obtain ⟨σ, hσ, -⟩ := (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s (fun _ => 0)).2.2.2.1 θ (s ρ.i₀)
    rw [hg] at hθ
    exact IsComb.of_eq_mul (hθa _ _ hσ) hc ((H i).2.2.2 _ σ θ hpull hθ hσ)
  obtain ⟨σ, hσ⟩ := (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N (Fin n) t a).1
  refine ⟨_, σ, fun j => ?_,
    (GlobalTheory.T.fibreSection_linearComb_exists_unique_thetaAction u.V u.A (PadicAlgCl p) S.N S.J s (fun _ => 0)).2.2.2.2 (Fin n) _ t a σ ht hσ, ?_⟩
  · rw [Finset.mul_sum]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => ?_
    rw [← _root_.mul_assoc, mul_inv_cancel_left₀ hc, norm_mul]
    have h1 : ‖a i‖ ≤ 1 := by
      have := (hle (a i) 0).1 (by simpa using (H i).1)
      simpa using this
    exact mul_le_one₀ (hy _) (norm_nonneg _) h1
  · rw [hΦs]
    exact (GlobalTheory.T.isFibreSectionLinearComb_iff_expansion_sum (laws_all h h₂).1 u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p) S.N hN0 w₀ hw.1
      (Fin n) t r a σ fun i => (H i).2.2.1).1 hσ

end GlobalTheory.TestFibre
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralBasisCombinationOfIntegralFamilyStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_integral_basis_combination_of_integral_family : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)) (rig : LB.Gen (u.A.L.pull (eSec u.A.A))) (e : ∀ a, FrameAt u.A (x a)) (th : SecA u.A (PadicAlgCl p) 1) (s : S.J → SecA u.A (PadicAlgCl p) S.N), PtsOver u x → SecsOver u x rig e th s → ∀ (ϖ : u.V) (Q : u.D.toPre.X → ℤ) (v : AddValuation (PadicAlgCl p) (WithTop ℚ)) (lam : ℝ), Irreducible ϖ → ValOver ϖ (PadicAlgCl p) v → NormIs u l ϖ Q v lam → ∀ (w₀ : W0 u.U.toUnifPre) (th' : SecA u.A (PadicAlgCl p) 1) (ϑ : Fam u.D.toPre (PadicAlgCl p) 1) (c : PadicAlgCl p), NormW u.U.toUnifPre w₀ rig → u.U.ExpandsF (PadicAlgCl p) 1 w₀ th' ϑ → Prim u.D Q v ϑ → (∀ j, th.f j = liftFun u.A.A _ (cF u.V c) * th'.f j) → c ≠ 0 → ∀ Φ : Fam u.D.toPre (PadicAlgCl p) S.N, NuGe u.D Q (PadicAlgCl p) v S.N Φ 0 → ∃ (b : S.J → PadicAlgCl p) (σ : SecA u.A (PadicAlgCl p) S.N), (∀ j, ‖c * b j‖ ≤ 1) ∧ IsComb u.A s b σ ∧ u.U.ExpandsF (PadicAlgCl p) S.N w₀ σ Φ := by
  first | exact @GlobalTheory.TestFibre.exists_isComb_expands_of_nuGe_zero | exact GlobalTheory.TestFibre.exists_isComb_expands_of_nuGe_zero | (intros; apply GlobalTheory.TestFibre.exists_isComb_expands_of_nuGe_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemTestSectionsOnGeometricFibre
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemTestSectionsOnGeometricFibre
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section

namespace GlobalTheory.TestFibre

open GlobalTheory.ThetaPtMove GlobalTheory.ConstFam

theorem exists_secsOver : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∃ rig e th s, SecsOver u x rig e th s := by
  intro _ o Ω _ _ _ _ S ρ p _ y₀ u x hx
  obtain ⟨w, hw⟩ := u.lb
  have hp := u.cart
  have hL₀ := ρ.P.isLB
  have hL₁ := u.A.isLB
  have := u.A.isAb.comm
  have := ρ.P.isAb.comm
  let τ : (TFK (R := u.V) (PadicAlgCl p)).left ⟶ (baseOver (Sp S.R)).left := spMap y₀
  have hτ : τ ≫ (baseOver (Sp S.R)).hom = (TFK (R := u.V) (PadicAlgCl p)).hom ≫ spMap u.yK := by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Spec.map_comp _ _))
    exact congrArg (fun q => spMap q) u.fac.symm
  have hx' : ∀ a, (x a).left ≫ u.φ = τ ≫ (ρ.pt a).left := hx
  obtain ⟨rig, hrig, Hr⟩ := exists_gen_through (K := PUnit) (φ' := fun _ => eSec u.A.A) (φ := fun _ => eSec ρ.P.A)
    (ε := fun _ => 1) (h := spMap u.yK) hw hL₀ hL₁ (fun _ => PolBaseChange.eSec_comm hp) ρ.rig ρ.rig_gen
  choose e he He using fun a => exists_gen_through (φ' := fun _ : Fin 1 => (x a).left) (h := τ) hw hL₀ hL₁
    (fun _ => hx' a) (ρ.fr a) (ρ.fr_tors a).2.1
  have hfr : ∀ a, IsTorsFrame u.A rig (S.r * S.N) (x a) (e a) := fun a =>
    FrameMove.isTorsFrame_move hp hw
      (fun Z r z J J' hJ hJ' =>
        (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _))))
      (hx' a) (ρ.fr_tors a) (he a) (fun z J J' hJ hJ' => by
        have := He a _ (𝟙 _) z J J' hJ hJ'
        rwa [Fin.prod_univ_one, zpow_one, Category.id_comp, Category.id_comp] at this)
  obtain ⟨th, hth⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ ρ.th₁
  choose s hs using fun i => exists_secRel hp τ hτ hw hL₀ hL₁ (ρ.s i)
  obtain ⟨α, hα, vα⟩ := exists_genThrough₂ hp τ hτ hw hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) ρ.α ρ.α_gen
  have hpow : ∀ (n : ℕ) a, ρ.pt (n • a) = ρ.pt a ^ n := fun n a => by
    induction n with
    | zero =>
      have h := ρ.pt_add 0 0
      rw [add_zero] at h
      rw [zero_smul, pow_zero]
      exact left_eq_mul.1 h
    | succ n ih => rw [succ_nsmul, ρ.pt_add, ih, pow_succ]
  have hN : ∀ a, x (S.r • a) ^ S.N = 1 := fun a => FrameMove.pow_eq_one_of hp (hx' _) (by
    rw [hpow, ← pow_mul]
    exact (ρ.fr_tors a).1)
  refine ⟨rig, e, th, s, hrig, hfr, fun a z J hJ => ?_, fun i a z J hJ => ?_,
    ⟨α, hα, ThetaGeom.norm_move hp τ hτ hL₀ hL₁ Hr vα ρ.α_norm,
      isTwistPull_move hp τ hτ hL₀ hL₁ (psi_pow hp τ hτ (ρ.n ^ ρ.k)) hα vα hth (hs ρ.i₀) ρ.s_zero⟩, fun a => ?_⟩
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx' a).symm (He a) hth (ρ.th_val a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    rw [ThetaGeom.val_powFrame, Nat.cast_one, zpow_one]
    exact q
  · have h := isValueAt_move hp τ hτ hL₀ hL₁ (hx' a).symm (ThetaGeom.genThrough_pow τ (He a) S.N) (hs i)
      (ρ.ev_val i a)
    have q := sv_of_isValueAt h (𝟙 _) z hJ
    rw [Category.id_comp, spMap_appTop_fn] at q
    exact q
  · obtain ⟨θ, hθ, H⟩ := ClassWeight.symLift_act_move hp τ hτ hw hL₀ hL₁ (hx' _).symm (hN a) (ρ.U_sym a)
      (fun l i => fn (algebraMap o S.R (S.ρ a l i))) (fun l i => cF u.V (y₀ (algebraMap o S.R (S.ρ a l i))))
      (fun l i => spMap_appTop_fn y₀ _) hs (ρ.U_act a)
    exact ⟨θ, hθ, fun i σ h => (ThetaGeom.comb_iff _ _ _).2 (H i σ h)⟩

end GlobalTheory.TestFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsThetaSystemTestSectionsOnGeometricFibreStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaSystem_test_sections_on_geometric_fibre : Laws → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (x : S.Gam → (TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A)), PtsOver u x → ∃ rig e th s, SecsOver u x rig e th s := by
  first | exact @GlobalTheory.TestFibre.exists_secsOver | exact GlobalTheory.TestFibre.exists_secsOver | (intros; apply GlobalTheory.TestFibre.exists_secsOver <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemSumCharacterOrthogonalEqZero
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemSumCharacterOrthogonalEqZero
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory

theorem thetaSys_sum_perp_char_eq_zero :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (ζ : F), IsPrimitiveRoot ζ ((S.r * S.N) ^ 2) → ∀ (H : AddSubgroup S.Gam) [Fintype (S.perp H)] (a : S.Gam), a ∉ H → ∑ t : S.perp H, ζ ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) = 0 := by
  intro o Ω _ _ _ _ S F _ ζ hζ H _ a ha
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have hω : IsPrimitiveRoot (ζ ^ (S.r * S.N)) (S.r * S.N) :=
    hζ.pow (NeZero.pos _) (by ring)
  let χ : AddChar (ZMod (S.r * S.N)) F := AddChar.zmodChar _ hω.pow_eq_one
  have hχ : ∀ b, χ b = 1 → b = 0 := fun b hb =>
    ((AddChar.zmodChar_primitive_of_primitive_root _ hω).zmod_char_eq_one_iff _ b).mp hb
  let f : S.perp H →+ ZMod (S.r * S.N) :=
    { toFun := fun t => eStd S.g _ (t : S.Gam) a
      map_zero' := by simp [eStd]
      map_add' := fun x y => by
        simp only [eStd, AddSubgroup.coe_add, Pi.add_apply, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring }
  have hne : χ.compAddMonoidHom f ≠ 1 := by
    intro h
    apply ha
    rw [← (thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1 H]
    intro t ht
    have h1 : f ⟨t, ht⟩ = 0 := hχ _ (DFunLike.congr_fun h ⟨t, ht⟩)
    have h2 : eStd S.g _ t a = 0 := h1
    rw [ThetaProj.eStd_swap, h2, neg_zero]
  have h0 : ∑ t : S.perp H, χ (f t) = 0 := AddChar.sum_eq_zero_of_ne_one hne
  rw [← h0]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [pow_mul]
  rfl

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemSumCharacterOrthogonalEqZeroStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_sum_character_orthogonal_eq_zero : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (ζ : F), IsPrimitiveRoot ζ ((S.r * S.N) ^ 2) → ∀ (H : AddSubgroup S.Gam) [Fintype (S.perp H)] (a : S.Gam), a ∉ H → ∑ t : S.perp H, ζ ^ (S.r * S.N * (eStd S.g _ (t : S.Gam) a).val) = 0 := by
  first | exact @GlobalTheory.thetaSys_sum_perp_char_eq_zero | exact GlobalTheory.thetaSys_sum_perp_char_eq_zero | (intros; apply GlobalTheory.thetaSys_sum_perp_char_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValLeOfValuedSumAgainstCharactersStatement
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsValLeOfValuedSumAgainstCharacters
open GlobalTheory.UT

namespace GlobalTheory.TestFibre

theorem exists_val_le_of_sumV_characters : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X T : Type) [Fintype T] (χ : T → X → F) (cf : X → F) (ζ w : T → F) (α : X) (q : ℚ), (∀ t, SumV v (fun β => χ t β * cf β) (ζ t * w t)) → (∀ t, v (ζ t) = 0) → (∀ t β, v (χ t β) = 0) → v ((Fintype.card T : ℕ) : F) = 0 → v (cf α) = (q : WithTop ℚ) → (∀ β, β ≠ α → ∑ t, (χ t α)⁻¹ * χ t β = 0 ∨ (q : WithTop ℚ) < v (cf β)) → ∃ t, v (w t) ≤ (q : WithTop ℚ) := by
  classical
  intro F _ v X T _ χ cf ζ w α q hS hζ hχ hT hα hβ
  by_contra hcon
  have hw : ∀ t, (q : WithTop ℚ) < v (w t) := fun t => lt_of_not_ge fun h => hcon ⟨t, h⟩
  have hq : (q : WithTop ℚ) ≠ ⊤ := WithTop.coe_ne_top
  have hne : ∀ t, χ t α ≠ 0 := fun t h => by
    have h1 := hχ t α
    rw [h, v.map_zero] at h1
    exact WithTop.top_ne_zero h1
  have hinv : ∀ t, v (χ t α)⁻¹ = 0 := fun t => by
    have h1 : v ((χ t α)⁻¹ * χ t α) = 0 := by rw [inv_mul_cancel₀ (hne t), v.map_one]
    rwa [v.map_mul, hχ t α, add_zero] at h1
  choose S hS' using fun t => hS t (q + 1)
  set U : Finset X := insert α (Finset.univ.biUnion S) with hU
  have hαU : α ∈ U := Finset.mem_insert_self _ _
  have hSU : ∀ t, S t ⊆ U := fun t x hx =>
    Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨t, Finset.mem_univ _, hx⟩)
  have hq1 : (q : WithTop ℚ) < ((q + 1 : ℚ) : WithTop ℚ) := WithTop.coe_lt_coe.2 (by linarith)
  have hA : (q : WithTop ℚ) < v (∑ t, (χ t α)⁻¹ * (ζ t * w t)) :=
    v.map_lt_sum hq fun t _ => by
      rw [v.map_mul, v.map_mul, hinv, hζ, zero_add, zero_add]; exact hw t
  have hB : (q : WithTop ℚ) < v (∑ t, (χ t α)⁻¹ * (ζ t * w t - ∑ β ∈ U, χ t β * cf β)) :=
    v.map_lt_sum hq fun t _ => by
      rw [v.map_mul, hinv, zero_add]; exact hq1.trans_le (hS' t U (hSU t))
  have hC : (q : WithTop ℚ) < v (∑ β ∈ U.erase α, (∑ t, (χ t α)⁻¹ * χ t β) * cf β) :=
    v.map_lt_sum hq fun β hb => by
      rcases hβ β (Finset.ne_of_mem_erase hb) with h | h
      · rw [h, zero_mul, v.map_zero]; exact WithTop.coe_lt_top q
      · rw [v.map_mul]
        have h0 : (0 : WithTop ℚ) ≤ v (∑ t, (χ t α)⁻¹ * χ t β) :=
          v.map_le_sum fun t _ => by rw [v.map_mul, hinv, hχ, add_zero]
        exact h.trans_le (le_add_of_nonneg_left h0)
  have e1 : ∑ t, (χ t α)⁻¹ * χ t α = ((Fintype.card T : ℕ) : F) := by
    rw [Finset.sum_congr rfl fun t _ => inv_mul_cancel₀ (hne t)]
    simp
  have e2 : ∑ t, (χ t α)⁻¹ * (∑ β ∈ U, χ t β * cf β) = ∑ β ∈ U, (∑ t, (χ t α)⁻¹ * χ t β) * cf β := by
    simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
    exact Finset.sum_comm
  have e : ((Fintype.card T : ℕ) : F) * cf α =
      (∑ t, (χ t α)⁻¹ * (ζ t * w t)) +
        (-(∑ t, (χ t α)⁻¹ * (ζ t * w t - ∑ β ∈ U, χ t β * cf β)) +
          -(∑ β ∈ U.erase α, (∑ t, (χ t α)⁻¹ * χ t β) * cf β)) := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [e2, ← Finset.add_sum_erase U _ hαU, e1]
    ring
  have hfin : (q : WithTop ℚ) < v (((Fintype.card T : ℕ) : F) * cf α) := by
    rw [e]
    exact v.map_lt_add hA (v.map_lt_add (by rwa [v.map_neg]) (by rwa [v.map_neg]))
  rw [v.map_mul, hT, zero_add, hα] at hfin
  exact lt_irrefl _ hfin

end GlobalTheory.TestFibre
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_val_le_of_valuedSum_against_characters : ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (X T : Type) [Fintype T] (χ : T → X → F) (cf : X → F) (ζ w : T → F) (α : X) (q : ℚ), (∀ t, SumV v (fun β => χ t β * cf β) (ζ t * w t)) → (∀ t, v (ζ t) = 0) → (∀ t β, v (χ t β) = 0) → v ((Fintype.card T : ℕ) : F) = 0 → v (cf α) = (q : WithTop ℚ) → (∀ β, β ≠ α → ∑ t, (χ t α)⁻¹ * χ t β = 0 ∨ (q : WithTop ℚ) < v (cf β)) → ∃ t, v (w t) ≤ (q : WithTop ℚ) := by
  first | exact @GlobalTheory.TestFibre.exists_val_le_of_sumV_characters | exact GlobalTheory.TestFibre.exists_val_le_of_sumV_characters | (intros; apply GlobalTheory.TestFibre.exists_val_le_of_sumV_characters <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemWeightProjectorFixesEigenvector
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemWeightProjectorFixesEigenvector
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

noncomputable section
namespace GlobalTheory.TestFibre

theorem proj_fixes_eigen : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (y : o →+* F) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N), S.IsoFree T → ∀ (b E : S.J → F), (∀ t : T, ∑ j, (∑ i, y (S.ρ t j i) * b i) * E j = y S.ζN ^ (c t).val * ∑ j, b j * E j) → ∑ i, b i * ∑ j, y (S.proj T c j i) * E j = ∑ j, b j * E j := by
  intro o Ω _ _ _ S F _ y T c hT b E h
  have := Fintype.ofFinite T
  have h1 : ∀ t : T, y (GlobalGen.chi S (c t)) * y S.ζN ^ (c t).val = 1 := fun t => by
    have h2 := GlobalGen.chi_add S (c t) (-(c t))
    rw [add_neg_cancel, GlobalGen.chi_zero] at h2
    rw [← map_pow, ← map_one y, h2, map_mul, GlobalGen.chi.eq_1 S (-(c t)), neg_neg]
  have h3 : y (Ring.inverse (Nat.card T : o)) * (Fintype.card T : F) = 1 := by
    rw [← Nat.card_eq_fintype_card, ← map_natCast y, ← map_mul,
      Ring.inverse_mul_cancel _ (GlobalGen.isUnit_card hT), map_one]
  have h4 : ∑ i, b i * ∑ j, y (S.proj T c j i) * E j =
      y (Ring.inverse (Nat.card T : o)) * ∑ t : T, y (GlobalGen.chi S (c t)) *
        ∑ j, (∑ i, y (S.ρ t j i) * b i) * E j := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [GlobalGen.proj_eq, Matrix.smul_apply, Matrix.sum_apply, smul_eq_mul, map_mul, map_sum,
      Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    conv_rhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h4]
  simp only [h, ← _root_.mul_assoc, h1, _root_.one_mul]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← _root_.mul_assoc, h3, _root_.one_mul]

end GlobalTheory.TestFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemWeightProjectorFixesEigenvectorStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_weightProjector_fixes_eigenvector : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (F : Type) [Field F] (y : o →+* F) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N), S.IsoFree T → ∀ (b E : S.J → F), (∀ t : T, ∑ j, (∑ i, y (S.ρ t j i) * b i) * E j = y S.ζN ^ (c t).val * ∑ j, b j * E j) → ∑ i, b i * ∑ j, y (S.proj T c j i) * E j = ∑ j, b j * E j := by
  first | exact @GlobalTheory.TestFibre.proj_fixes_eigen | exact GlobalTheory.TestFibre.proj_fixes_eigen | (intros; apply GlobalTheory.TestFibre.proj_fixes_eigen <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemExistsRootOfUnitySumNormAttained
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemExistsRootOfUnitySumNormAttained
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre

namespace GlobalTheory

theorem thetaSys_exists_norm_FF_eq :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (B : ℝ), (∀ (t : T) i, ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ ≤ B) → (∃ (t : T) (i : S.J), B ≤ ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖) → ∃ (k : _) (hk : S.FF T c k ∈ S.R), ‖y₀ ⟨S.FF T c k, hk⟩‖ = B := by
  intro o Ω _ _ _ hA S p _ y₀ hy T c B hle ⟨t, i, hge⟩
  have hN := S.N_ge
  have hr := S.r_pos
  have hrN : 2 ≤ S.r * S.N := le_trans hN (Nat.le_mul_of_pos_left _ hr)
  have hn : 1 < (S.r * S.N) ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
  have : Fact (1 < (S.r * S.N) ^ 2) := ⟨hn⟩
  have : IsDomain o := hA.inj.isDomain _
  have : NeZero (S.r * S.N) := ⟨by omega⟩
  have := Fintype.ofFinite T
  have hmem := (thetaSys_FF_mem_finite_perp_proj o Ω S).1 T c
  set E : T → PadicAlgCl p := fun s =>
    ∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev s j, S.ev_mem s j⟩ with hE
  have hval : ∀ k : T → ZMod ((S.r * S.N) ^ 2), y₀ ⟨S.FF T c (i, k), hmem _⟩
      = ∑ s, y₀ (algebraMap o S.R S.ζ) ^ (k s).val * E s := fun k => by
    have : (⟨S.FF T c (i, k), hmem _⟩ : S.R) = ∑ s : T, algebraMap o S.R S.ζ ^ (k s).val *
        ∑ j, algebraMap o S.R (S.proj T c j i) * ⟨S.ev s j, S.ev_mem s j⟩ := by
      apply Subtype.ext
      simp [ThetaSys.FF, finsum_eq_sum_of_fintype]
    rw [this]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [hE, map_sum]
  have hB : ‖E t‖ = B := le_antisymm (hle t i) hge
  have hB0 : 0 ≤ B := hB ▸ norm_nonneg _
  have h0 : ‖∑ s, E s‖ ≤ B :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB0 fun s _ => hle s i
  rcases h0.eq_or_lt with h0 | h0
  · refine ⟨(i, 0), hmem _, ?_⟩
    rw [hval]
    simpa using h0
  · have hu : IsUnit (1 - S.ζ) := by
      obtain ⟨m, hm⟩ : ∃ m, (S.r * S.N) ^ 2 = m + 1 + 1 := ⟨(S.r * S.N) ^ 2 - 2, by omega⟩
      have hp := S.prim
      rw [hm] at hp
      have h1 := hp.prod_one_sub_pow_eq_order
      have h2 : IsUnit ((((S.r * S.N) ^ 2 : ℕ)) : o) := by
        rw [Nat.cast_pow]; exact S.unit.pow _
      rw [hm, Nat.cast_succ, ← h1, Finset.prod_range_succ'] at h2
      simpa using isUnit_of_mul_isUnit_right h2
    have hone : ‖1 - y₀ (algebraMap o S.R S.ζ)‖ = 1 := by
      obtain ⟨v, hv⟩ := hu.exists_right_inv
      have h1 := hy (1 - S.ζ)
      have h2 := hy v
      have h3 : ‖y₀ (algebraMap o S.R (1 - S.ζ))‖ * ‖y₀ (algebraMap o S.R v)‖ = 1 := by
        rw [← norm_mul, ← map_mul, ← map_mul, hv, map_one, map_one, norm_one]
      rw [map_sub, map_sub, map_one, map_one] at h1 h3
      refine le_antisymm h1 ?_
      calc (1 : ℝ) = _ := h3.symm
        _ ≤ _ := mul_le_of_le_one_right (norm_nonneg _) h2
    refine ⟨(i, Pi.single t 1), hmem _, ?_⟩
    have hs : ∑ s, y₀ (algebraMap o S.R S.ζ) ^ ((Pi.single t 1 : T → ZMod ((S.r * S.N) ^ 2)) s).val * E s
        = ∑ s, E s + -((1 - y₀ (algebraMap o S.R S.ζ)) * E t) := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t),
        ← Finset.add_sum_erase _ E (Finset.mem_univ t),
        Finset.sum_congr rfl (g := E) fun s hs => by
          rw [Pi.single_eq_of_ne (Finset.ne_of_mem_erase hs), ZMod.val_zero, pow_zero,
            _root_.one_mul]]
      rw [Pi.single_eq_same, ZMod.val_one, pow_one]
      ring
    have hn' : ‖-((1 - y₀ (algebraMap o S.R S.ζ)) * E t)‖ = B := by
      rw [norm_neg, norm_mul, hone, _root_.one_mul, hB]
    rw [hval, hs, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [hn']; exact h0.ne),
      hn', max_eq_right h0.le]

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemExistsRootOfUnitySumNormAttainedStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TestFibre
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thetaSystem_exists_rootOfUnity_sum_norm_attained : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (B : ℝ), (∀ (t : T) i, ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ ≤ B) → (∃ (t : T) (i : S.J), B ≤ ‖∑ j, y₀ (algebraMap o S.R (S.proj T c j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖) → ∃ (k : _) (hk : S.FF T c k ∈ S.R), ‖y₀ ⟨S.FF T c k, hk⟩‖ = B := by
  first | exact @GlobalTheory.thetaSys_exists_norm_FF_eq | exact GlobalTheory.thetaSys_exists_norm_FF_eq | (intros; apply GlobalTheory.thetaSys_exists_norm_FF_eq <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormTorsionSumShortestVectorEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.UT
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TestFibre

theorem val_lt_of_shortest {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) {n r : ℕ}
    (hn : 1 ≤ n) (hr : 2 ≤ r) (z : D.toPre.X) (hz : ∀ m, Q z ≤ Q (z + n • m)) (m : D.toPre.X)
    (hm : (n * r) • m ≠ 0) : Q z < Q (z + (n * r) • m) := by
  let B : D.toPre.X →+ D.toPre.X →+ ℤ := AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => QForm.bOf D.toPre Q a b)
    (fun b b' => by
      rw [QForm.bOf_comm D (Q := Q) a, QForm.bOf_add_left hϖ D hQ, QForm.bOf_comm D (Q := Q) b,
        QForm.bOf_comm D (Q := Q) b']))
    (fun a a' => AddMonoidHom.ext fun b => QForm.bOf_add_left hϖ D hQ a a' b)
  refine shortest_vector_strict_of_mul _ Q B (fun a b => ?_) (fun a => ?_) (fun a ha => QForm.Q_pos hϖ D hQ ha)
    n r hn hr z hz m hm
  · show _ = Q a + Q b + QForm.bOf D.toPre Q a b
    rw [QForm.bOf]; ring
  · show _ = QForm.bOf D.toPre Q a a
    have h := QForm.bOf_add_left hϖ D hQ a (-a) a
    simp only [QForm.bOf, add_neg_cancel, neg_add_cancel, zero_add, QForm.Q_neg hϖ D hQ, QForm.Q_zero hϖ D hQ] at h ⊢
    linarith

theorem exists_origin (hLL : LL) (hT : TwistBCSpanStatement) (hVR : TWM.VRatioGtStatement) (hTW : TWStatement)
    (hUU : UUStatement) {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hc : IsAdicComplete (IsLocalRing.maximalIdeal V) V) (hadm : AdmBase V (IsLocalRing.maximalIdeal V))
    {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q)
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] {v : AddValuation F (WithTop ℚ)}
    (hv : ValOver ϖ F v) (k : ℕ) : ∃ (g : GtPtF D.toPre F) (w : Frm D.toPre F k g.b), g.IsZero ∧ FrmOne w ∧
      GtV hϖ hv g (fun _ => 0) ∧ GenV hϖ hv w 0 := by
  obtain ⟨-, -, h₁, -, h₂⟩ := gt_onto_divisible_kernel hLL V _ hadm D F
  obtain ⟨g, hg, -⟩ := h₁ 1
  obtain ⟨w, hw⟩ := (CoefBasic.coef_basic V D.toPre F k g).2.1 hg.1
  obtain ⟨⟨l, hl, hu⟩, -, h₃, h₄, -⟩ := CoefVal.main hLL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv g
  have hadd : g.IsAdd g g := (h₂ 1 1 g g g hg hg).2 (by rwa [_root_.mul_one])
  have e : l + l = l := hu (l + l) (h₄ g g l l hadd hl hl)
  have e₀ : l = 0 := by simpa using e
  refine ⟨g, w, (isZero_iff g).2 ⟨hg.1, fun χ y J hJ => Units.ext ?_⟩, hw, ?_, h₃ k w hw hg.1⟩
  · refine (hg.2 χ y J hJ).trans ?_
    rw [CoefBasic.cst_eq]
    exact map_one _
  · rw [e₀] at hl
    exact hl


set_option maxHeartbeats 1000000 in
theorem exists_norm_FF_eq : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∃ (k : _) (hk : S.FF _ (l.wt α) k ∈ S.R), ‖y₀ ⟨S.FF _ (l.wt α) k, hk⟩‖ = S.delta y₀ * Real.exp (-(l.q α / S.N))) := by
  intro hL hL2 hU o Ω _ _ _ _ S ρ p _ y₀ u l hint α hα
  obtain ⟨hLL, hT, hVR, hTW, hUU⟩ := laws_all hL hL2
  obtain ⟨hch, -, hadm, hN', hζ, ϖ, Q, v, lam, hϖ, hv, hnorm⟩ := GlobalTheory.T.uniformisedModel_valuation_data o Ω S ρ p y₀ u l hint
  obtain ⟨⟨x, hx⟩, -⟩ := GlobalTheory.T.uniformisedModel_torsionPoints_group_pairing hL o Ω S ρ p y₀ u
  obtain ⟨rig, e, th, s, hs⟩ := GlobalTheory.T.exists_thetaSystem_test_sections_on_geometric_fibre hL o Ω S ρ p y₀ u x hx
  have hle : S.perp l.yy.ker ≤ l.yy.ker :=
    l.isoFree.1.trans ((thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1 _).le
  refine GlobalTheory.T.thetaSystem_exists_rootOfUnity_sum_norm_attained o Ω S p y₀ hint _ (l.wt α) _
    (fun t i => GlobalTheory.T.weightSpace_values_integralTorsion_bound_shortestVector hL hL2 hU o Ω S ρ p y₀ u l hint α hα t (hle t.2) i) ?_
  obtain ⟨w₀, hw₀⟩ := (EvalZero.value_at_origin hLL u.V _ hadm u.D u.A u.G u.semi u.U (PadicAlgCl p)).2.1 rig hs.1
  obtain ⟨th', ϑ, hϑ, hprim, hgen⟩ := exists_prim_generator hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hnorm.2.1
    (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ hw₀.1
  obtain ⟨c₀, hc₀⟩ := hgen th
  obtain ⟨c, rfl⟩ : ∃ c : PadicAlgCl p, cF u.V c = c₀ :=
    ⟨(Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).hom.hom c₀,
      (Scheme.ΓSpecIso (CommRingCat.of (PadicAlgCl p))).hom_inv_id_apply c₀⟩
  have hδ : S.delta y₀ ≤ ‖c‖ := ciSup_le
    (GlobalTheory.T.norm_thetaConstant_le_primitiveGenerator_scale hL hL2 hU o Ω S ρ p y₀ u l hint x rig e th s hx hs ϖ Q v lam hϖ hv hnorm w₀ th' ϑ c hw₀ hϑ hprim hc₀)
  by_cases hc : c = 0
  · rw [hc, norm_zero] at hδ
    exact ⟨0, ρ.i₀, (mul_nonpos_of_nonpos_of_nonneg hδ (Real.exp_pos _).le).trans (norm_nonneg _)⟩
  obtain ⟨hlam, hQ, hq, hge, heq⟩ := id hnorm
  have hN0 : 1 ≤ S.N := le_trans (by norm_num) S.N_ge
  have hrN : 1 ≤ S.r * S.N := Nat.mul_pos S.r_pos hN0
  have hN4 : 4 ≤ S.N := by
    have : 2 ≤ ρ.n ^ ρ.k := ρ.n_prime.two_le.trans (Nat.le_self_pow (by have := ρ.two_le; omega) _)
    rw [ρ.N_eq]; nlinarith
  have hr2 : 2 ≤ S.r := by
    obtain ⟨j, hj, hr⟩ := ρ.r_eq
    rw [hr]
    exact ρ.n_prime.two_le.trans (Nat.le_self_pow (by omega) _)
  haveI : NeZero (S.r * S.N) := ⟨by omega⟩
  haveI : Fintype (S.perp l.yy.ker) := Fintype.ofFinite _
  obtain ⟨g, w₁, hg, hw₁, hgv, hwv⟩ := exists_origin hLL hT hVR hTW hUU u.complete hadm hϖ u.D hQ hv S.N
  obtain ⟨Φ, hΦ, hsupp, hval⟩ := CoefUnit.exists_fam_coef_val hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
    (PadicAlgCl p) v hv S.N hN4 g w₁ _ 0 hw₁.1 hgv hwv α
  obtain ⟨b, σ, hb, hσ, hσΦ⟩ := GlobalTheory.T.exists_integral_basis_combination_of_integral_family hL hL2 hU o Ω S ρ p y₀ u l hint x rig e th s hx hs ϖ Q v lam hϖ hv hnorm
    w₀ th' ϑ c hw₀ hϑ hprim hc₀ hc Φ hΦ
  choose τ q hqy hτ hqx hτv using GlobalTheory.T.thetaSystem_orthogonal_labels_are_torus_points hL hL2 hU o Ω S ρ p y₀ u l hint x hx
  have key : ∀ t : S.perp l.yy.ker, ∃ ζ : PadicAlgCl p, v ζ = 0 ∧
      SumV v (fun β => (τ t (Multiplicative.ofAdd β)).val * coef Φ g w₁ β)
        (ζ * ∑ j, b j * y₀ ⟨S.ev t j, S.ev_mem t j⟩) := fun t => by
    obtain ⟨ζ, hζ, H⟩ := WeightValue.value_at_formal_torsion hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ
      (PadicAlgCl p) v hv u.A u.G u.semi u.U w₀ rig hw₀ (S.r * S.N) S.N hrN hN0 (q t) (x t) (hqy t) (hqx t) (e t)
      (hs.2.1 t)
    exact ⟨ζ, hζ, (H σ Φ _ hσΦ ((GlobalTheory.T.isFibreSectionValueInFrame_linear_unique_exists hL u.V u.A (PadicAlgCl p) S.N (x t) (e t)).1 S.J s b _ σ hσ
      fun i => hs.2.2.2.1 i t)).2 _ (hτ t) g w₁ hg hw₁⟩
  choose ζ hζv hsum using key
  have v1 : ∀ z : PadicAlgCl p, ‖z‖ = 1 → v z = 0 := fun z hz => (heq z 0).2 (by simpa using hz)
  have hζ1 : ‖y₀ (algebraMap o S.R S.ζ)‖ = 1 :=
    (pow_eq_one_iff_of_nonneg (norm_nonneg _) (pow_ne_zero 2 (NeZero.ne (S.r * S.N)))).1
      (by rw [← norm_pow, hζ.pow_eq_one, norm_one])
  obtain ⟨t, ht⟩ := GlobalTheory.T.exists_val_le_of_valuedSum_against_characters (PadicAlgCl p) v u.D.toPre.X (S.perp l.yy.ker)
    (fun t β => (τ t (Multiplicative.ofAdd β)).val) (coef Φ g w₁) ζ _ α ((Q α : ℚ) / S.N) hsum hζv
    (fun t β => by
      obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk β)
      exact v1 _ (by rw [hτv t a β ha, norm_pow, hζ1, one_pow]))
    (by
      obtain ⟨d, ⟨E⟩⟩ := l.isoFree.2
      refine v1 _ ?_
      rw [Fintype.card_congr E.toEquiv, Fintype.card_fun, ZMod.card, Nat.cast_pow, norm_pow, hN', one_pow])
    (by simpa using hval)
    (fun β hβ => by
      obtain ⟨a, ha⟩ := l.yy_onto (QuotientAddGroup.mk (β - α))
      by_cases hk : a ∈ l.yy.ker
      · right
        rw [AddMonoidHom.mem_ker, ha, QuotientAddGroup.eq_zero_iff] at hk
        obtain ⟨m, hm⟩ := hk
        have hm' : (S.N * S.r) • m = β - α := by rw [Nat.mul_comm]; exact hm
        have hlt := val_lt_of_shortest hϖ u.D hQ hN0 hr2 α (fun m => by
          have := hα m
          rw [hq, hq] at this
          exact_mod_cast le_of_mul_le_mul_left this hlam) m (by rw [hm']; exact sub_ne_zero.2 hβ)
        rw [hm', add_sub_cancel] at hlt
        refine lt_of_lt_of_le (WithTop.coe_lt_coe.2 ?_)
          ((((CoefVal.main hLL hT hVR hTW hUU u.V u.complete ϖ hϖ u.D Q hQ (PadicAlgCl p) v hv g).2.2.2.2.2.2
            S.N hN0 w₁ Φ hw₁.1).2 _ 0 0 hgv hwv hΦ β))
        have : (0 : ℚ) < S.N := by exact_mod_cast hN0
        simp only [zero_add, add_zero]
        exact div_lt_div_of_pos_right (by exact_mod_cast hlt) this
      · left
        refine Eq.trans (Finset.sum_congr rfl fun t _ => ?_) (GlobalTheory.T.thetaSystem_sum_character_orthogonal_eq_zero o Ω S _ _ hζ l.yy.ker a hk)
        rw [← hτv t a _ ha, ofAdd_sub, map_div, Units.val_div_eq_div_val, div_eq_inv_mul])
  rw [← GlobalTheory.T.thetaSystem_weightProjector_fixes_eigenvector o Ω S (PadicAlgCl p) (y₀.comp (algebraMap o S.R)) _ (l.wt α) l.isoFree b _
    (fun t' => GlobalTheory.T.torusOperator_eigen_of_expansion_single_class hL hL2 hU o Ω S ρ p y₀ u l hint x rig e th s hx hs w₀ hw₀.1 α b σ Φ hσ hσΦ hsupp t' t)] at ht
  have hE : Real.exp (-(l.q α / S.N)) = Real.exp (-(lam * (((Q α : ℚ) / S.N : ℚ) : ℝ))) := by
    rw [hq]; push_cast; ring_nf
  obtain ⟨i, -, hi⟩ := (Finset.le_sup'_iff Finset.univ_nonempty).1
    (Finset.univ_nonempty.norm_sum_le_sup'_norm
      (fun i => b i * ∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt α) j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩))
  refine ⟨t, i, ?_⟩
  have hw : Real.exp (-(l.q α / S.N)) ≤
      ‖∑ i, b i * ∑ j, y₀ (algebraMap o S.R (S.proj _ (l.wt α) j i)) * y₀ ⟨S.ev t j, S.ev_mem t j⟩‖ := by
    rw [hE]
    by_contra hlt
    have hlt := not_le.1 hlt
    exact hlt.ne ((heq _ _).1 (le_antisymm ht ((hge _ _).2 hlt.le)))
  have hbi := hb i
  rw [norm_mul] at hi hbi
  calc _ ≤ ‖c‖ * (‖b i‖ * _) := mul_le_mul hδ (hw.trans hi) (Real.exp_pos _).le (norm_nonneg _)
    _ = (‖c‖ * ‖b i‖) * _ := (_root_.mul_assoc _ _ _).symm
    _ ≤ 1 * _ := mul_le_mul_of_nonneg_right hbi (norm_nonneg _)
    _ = _ := _root_.one_mul _

end GlobalTheory.TestFibre
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormTorsionSumShortestVectorEqStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_norm_torsionSum_shortestVector_eq : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → (∀ α : u.D.toPre.X, (∀ v₀, l.q α ≤ l.q (α + S.N • v₀)) → ∃ (k : _) (hk : S.FF _ (l.wt α) k ∈ S.R), ‖y₀ ⟨S.FF _ (l.wt α) k, hk⟩‖ = S.delta y₀ * Real.exp (-(l.q α / S.N))) := by
  first | exact @GlobalTheory.TestFibre.exists_norm_FF_eq | exact GlobalTheory.TestFibre.exists_norm_FF_eq | (intros; apply GlobalTheory.TestFibre.exists_norm_FF_eq <;> assumption)
end
