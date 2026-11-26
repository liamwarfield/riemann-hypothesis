module

public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLaws
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.GaugeThirdDifferenceSymmetryIntegralExponentials

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSymmetricLiftOddOrderLocalRing
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSymmetricLiftOddOrderLocalRing
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymLiftConst
open GlobalTheory.SymLiftOdd

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S} {k : ℤ}

private theorem surjective_appTop_of_section_surjective {Y Z W : Scheme.{0}} (p : Y ⟶ W) (q : Z ⟶ W) (σ : Y ⟶ Z) (r : Z ⟶ Y)
    (hσr : σ ≫ r = 𝟙 Y) (hσq : σ ≫ q = p) (hq : Function.Surjective q.appTop.hom) :
    Function.Surjective p.appTop.hom := by
  intro f
  obtain ⟨s, hs⟩ := hq (r.appTop.hom f)
  refine ⟨s, ?_⟩
  have e1 : p.appTop.hom s = σ.appTop.hom (q.appTop.hom s) := by
    subst hσq; simp <;> rfl
  have e2 : σ.appTop.hom (r.appTop.hom f) = (σ ≫ r).appTop.hom f := by
    simp <;> rfl
  rw [e1, hs, e2, hσr]
  simp

private theorem hom_baseOver_subsingleton {X : Over S} (f g : X ⟶ baseOver S) : f = g := by
  have hf : f.left ≫ 𝟙 S = X.hom := Over.w f
  have hg : g.left ≫ 𝟙 S = X.hom := Over.w g
  have hf' : f.left = X.hom := by simpa using hf
  have hg' : g.left = X.hom := by simpa using hg
  exact Over.OverMorphism.ext (hf'.trans hg'.symm)


omit [GrpObj A] in
theorem surj_fst_base (h : Function.Surjective (A ⊗ A).hom.appTop.hom) :
    Function.Surjective (fst (baseOver S) A).left.appTop.hom := by
  let g : A ⊗ A ⟶ baseOver S := Over.homMk (A ⊗ A).hom (by simp [baseOver])
  refine surjective_appTop_of_section_surjective (fst (baseOver S) A).left (A ⊗ A).hom
    (lift (snd (baseOver S) A) (snd (baseOver S) A)).left (lift g (snd A A)).left ?_ ?_ h
  · rw [← Over.comp_left, ← Over.id_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext
    · exact hom_baseOver_subsingleton _ _
    · simp
  · have h1 : (fst (baseOver S) A).left ≫ 𝟙 S = (baseOver S ⊗ A).hom := Over.w _
    have h1' : (fst (baseOver S) A).left = (baseOver S ⊗ A).hom := by simpa using h1
    rw [h1']
    exact Over.w _

theorem exists_constT (hs : Function.Surjective (fst T A).left.appTop.hom) (hL : L.IsLB) {K : Type} [Fintype K]
    {φ : K → ((T ⊗ A).left ⟶ A.left)} {ε : K → ℤ}
    (hF : ∀ (U : Type) [CommGroup U] (h : ((T ⊗ A).left ⟶ A.left) → U), ∏ k, h (φ k) ^ ε k = 1)
    {u : LB.Gen (LB.LinComb L φ ε)} (hu : u.IsGen) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (m : T ⊗ A ⟶ A) (y : (T ⊗ A).left) (J), Good L y J →
      val u (lift (fst T A) m).left y J = gm (fst T A).left y ⊤ a := by
  have he : (lift (𝟙 T) (1 : T ⟶ A)).left ≫ (fst T A).left = 𝟙 T.left := by
    rw [← Over.comp_left, lift_fst, Over.id_left]
  obtain ⟨a, ha⟩ := GlobalTheory.SymLiftOdd.exists_const hL (fst T A).left (lift (𝟙 T) (1 : T ⟶ A)).left he hs hF hu
  refine ⟨a, fun m y J hJ => ?_⟩
  rw [ha _ _ y J hJ, ← Over.comp_left, lift_fst]

variable [IsCommMonObj A]

theorem exists_symConst (hs : Function.Surjective (fst T A).left.appTop.hom) (hL : L.IsLB) (θ : ThetaGrp A L k T)
    {nu : LB.Gen (negLB A L k T)} (hnu : nu.IsGen) :
    ∃ a : Γ(T.left, ⊤)ˣ, ∀ (m : T ⊗ A ⟶ A) (y : (T ⊗ A).left) (J), Good L y J →
      val (symGen A L k θ nu) (lift (fst T A) m).left y J = gm (fst T A).left y ⊤ a := by
  refine GlobalTheory.SymLiftConst.exists_constT hs hL ?_ (GlobalTheory.SymLiftOdd.symGen_isGen θ hnu)
  intro U _ h
  have hb : (translT A θ.pt⁻¹).left ≫ (translPt A θ.pt).left = (snd T A).left := by
    rw [← Over.comp_left, translT_eq, lift_translPt, comp_inv', mul_inv_cancel_left]
  have hc : (negT A T).left ≫ (snd T A).left = (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
    rw [← Over.comp_left, negT_eq, lift_snd]
    rfl
  have hd : (negT A T).left ≫ (translPt A θ.pt).left =
      (translT A θ.pt⁻¹).left ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left := by
    rw [← Over.comp_left, ← Over.comp_left, negT_eq, translT_eq, lift_translPt, ← Category.assoc, lift_snd, comp_inv']
    rw [show ∀ f : T ⊗ A ⟶ A, f ≫ (GrpObj.inv : A ⟶ A) = f⁻¹ from fun _ => rfl]
    rw [mul_inv_rev, inv_inv, mul_comm]
  simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, neg_neg, hb, hc, hd]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_one, neg_smul]
  abel

private theorem mul_pow_eq_one_and_mul_sq_eq_one_of_odd {U : Type} [CommGroup U] (a b c : U) (n : ℕ) (hn : Odd n) (h : a ^ n = b ^ 2)
    (hc : c = a ^ ((n - 1) / 2) * b⁻¹) : b * c ^ n = 1 ∧ a * c ^ 2 = 1 := by
  obtain ⟨m, rfl⟩ := hn
  have hm : (2 * m + 1 - 1) / 2 = m := by omega
  rw [hm] at hc
  subst hc
  constructor
  · have e : (a ^ m) ^ (2 * m + 1) = b ^ (2 * m) := by
      rw [← pow_mul, mul_comm, pow_mul, h, ← pow_mul]
    rw [mul_pow, e, inv_pow]
    group
  · rw [mul_pow, inv_pow, ← _root_.mul_assoc, ← pow_mul, ← pow_succ', show m * 2 + 1 = 2 * m + 1 by ring, h,
      mul_inv_cancel]

theorem exists_symLift (hs : Function.Surjective (fst T A).left.appTop.hom) (hL : L.IsLB) {n : ℕ} (hn : Odd n)
    {x : T ⟶ A} (hx : x ^ n = 1) (θ : ThetaGrp A L k T) (hθ : θ.pt = x) {nu : LB.Gen (negLB A L k T)}
    (hnu : nu.IsGen) : ∃ θ' : ThetaGrp A L k T, SymLift A L k n x θ' := by
  obtain ⟨α, hα⟩ := GlobalTheory.SymLiftConst.exists_symConst hs hL θ hnu
  have hx' : θ.pt ^ n = 1 := by rw [hθ]; exact hx
  obtain ⟨β, hβ⟩ := GlobalTheory.SymLiftConst.exists_constT hs hL (fun U _ h => form_pow hx' U h) (powGen_isGen θ n)
  have key : ∀ y J, Good L y J → gm (fst T A).left y ⊤ α ^ n = gm (fst T A).left y ⊤ β ^ 2 := by
    intro y J hJ
    refine defect_pow (fun m => thetaVal θ y J m) (fun m => negVal nu y J m) (fst T A ≫ x) n ?_ _ _ ?_ ?_
    · rw [← comp_pow', hx]
      simp
    · intro m
      exact (val_symGen θ nu hθ hJ m).symm.trans (hα m y J hJ)
    · have e := (val_powGen θ n hθ hJ 1).symm.trans (hβ 1 y J hJ)
      simpa only [_root_.mul_one] using e
  obtain ⟨θ', hpt, hsc⟩ := exists_scale hL θ (α ^ ((n - 1) / 2) * β⁻¹)
  have hpt' : θ'.pt = x := hpt.trans hθ
  have hc : ∀ y, gm (fst T A).left y ⊤ (α ^ ((n - 1) / 2) * β⁻¹) =
      gm (fst T A).left y ⊤ α ^ ((n - 1) / 2) * (gm (fst T A).left y ⊤ β)⁻¹ := by
    intro y
    rw [map_mul, map_pow, map_inv]
  refine ⟨θ', ⟨hpt', ?_, ?_⟩⟩
  · apply corr_of_val hL
    intro y J hJ
    rw [val_one, id_eq_lift, val_powGen θ' n hpt' hJ]
    simp only [hsc y J hJ]
    rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range,
      ← val_powGen θ n hθ hJ (snd T A), hβ _ y J hJ]
    exact (mul_pow_eq_one_and_mul_sq_eq_one_of_odd _ _ _ n hn (key y J hJ) (hc y)).1
  · refine ⟨nu, hnu, corr_of_val hL fun y J hJ => ?_⟩
    rw [val_one, id_eq_lift, val_symGen θ' nu hpt' hJ]
    simp only [hsc y J hJ]
    have e1 := (val_symGen θ nu hθ hJ (snd T A)).symm.trans (hα _ y J hJ)
    have e2 := (mul_pow_eq_one_and_mul_sq_eq_one_of_odd _ _ _ n hn (key y J hJ) (hc y)).2
    refine Eq.trans ?_ e2
    rw [← e1]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    abel

theorem exists_gen_neg (L : RigLB A) (h : L.IsSymmetric) (k : ℤ) (T : Over S) :
    ∃ nu : LB.Gen (negLB A L.L k T), nu.IsGen := by
  obtain ⟨s, hs, -⟩ := GlobalTheory.SymmetricBundle.gen_of_isSymmetric L h
  have hs1 := ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen L.L _ _ s hs (snd T A).left
  obtain ⟨s2, hs2⟩ := GlobalTheory.exists_gen_zsmul _ hs1 (-k)
  unfold negLB
  refine (exists_gen (K' := Fin 2) L.isLB (φ' := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
    (ε' := ![k, -k]) ?_ s2 hs2).elim fun nu hnu => ⟨nu, hnu.1⟩
  intro U _ hh
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Over.comp_left,
    _root_.mul_one, mul_neg, neg_neg]
  simp only [Category.comp_id]
  exact _root_.mul_comm _ _

theorem exists_symLift_local : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (k : ℕ), Odd k → ∀ a : baseOver (Sp V) ⟶ t.G, a ^ k = 1 → ∃ U : ThetaGrp t.G t.PP.L (k : ℤ) (baseOver (Sp V)), SymLift t.G t.PP.L (k : ℤ) k a U := by
  intro E _ _ _ H V _ _ t hsurj k hk a ha
  obtain ⟨θ, hθ⟩ := GlobalTheory.TorsionThetaLocal.exists_theta_of_pow_eq_one (Sp V) t.G t.PP t.cub V (𝟙 (Sp V)) k a ha
  obtain ⟨nu, hnu⟩ := exists_gen_neg t.PP t.sym (k : ℤ) (baseOver (Sp V))
  exact GlobalTheory.SymLiftConst.exists_symLift (surj_fst_base hsurj) t.PP.isLB hk ha θ hθ hnu

end GlobalTheory.SymLiftConst
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsSymmetricLiftOddOrderLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_symmetric_lift_odd_order_localRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (V : Type) [CommRing V] [IsLocalRing V] (t : SAB H (Sp V)), Function.Surjective (t.G ⊗ t.G).hom.appTop.hom → ∀ (k : ℕ), Odd k → ∀ a : baseOver (Sp V) ⟶ t.G, a ^ k = 1 → ∃ U : ThetaGrp t.G t.PP.L (k : ℤ) (baseOver (Sp V)), SymLift t.G t.PP.L (k : ℤ) k a U := by
  first | exact @GlobalTheory.SymLiftConst.exists_symLift_local | exact GlobalTheory.SymLiftConst.exists_symLift_local | (intros; apply GlobalTheory.SymLiftConst.exists_symLift_local <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowSpanXLeSpanFormalModuleMatrix
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowSpanXLeSpanFormalModuleMatrix
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceInt

theorem map_mem_span_of_constantCoeff_eq_zero {σ R S : Type} [Finite σ] [CommRing R] [CommRing S]
    (ψ : MvPowerSeries σ R →+* S) (g : MvPowerSeries σ R) (hg : MvPowerSeries.constantCoeff g = 0) :
    ψ g ∈ Ideal.span (Set.range fun j => ψ (MvPowerSeries.X j)) := by
  have h3 : g ∈ Ideal.span (Set.range (MvPowerSeries.X : σ → MvPowerSeries σ R)) := by
    rw [← germIdeal_eq_span]
    exact hg
  have h4 := Ideal.mem_map_of_mem ψ h3
  rwa [Ideal.map_span, ← Set.range_comp] at h4

theorem exists_pow_span_X_le_span_matV : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p p' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → p' * p = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin n × Fin d → PS (ResidueField V) n d)) ^ M ≤ Ideal.span (Set.range fun s : Fin n × Fin d => MvPowerSeries.map (residue V) (matV B p (fun j => pt V (n := n) d j) s.1 s.2)) := by
  intro V _ _ _ _ _ d O _ _ B hB n p p' N hN hp
  obtain ⟨M, hM⟩ := hB N hN
  have hpt0 : ∀ (b : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt V (n := n) d b i) = 0 := by
    intro b i; simp [pt]
  have hpt : ∀ (b : Fin n) (i : Fin d), MvPowerSeries.constantCoeff (pt V (n := n) d b i) ∈ maximalIdeal V := by
    intro b i; rw [hpt0]; exact zero_mem _
  obtain ⟨-, hmul, -, hsm, -, -, -⟩ := GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p' p (fun j => pt V d j) (fun j => pt V d j) hpt hpt
  obtain ⟨hy, -, -, -, -, -, -⟩ := GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p p (fun j => pt V d j) (fun j => pt V d j) hpt hpt
  set y : Fin n → Pt V n d := matV B p (fun j => pt V d j) with hydef
  obtain ⟨-, -, -, -, hev, h0, -⟩ := GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws V d O B n n p' p y y hy hy
  obtain ⟨⟨ψ, hψX, hψ⟩, -⟩ := evC_spec V (Fin n × Fin d) (Fin n × Fin d) Unit
    (fun s => y s.1 s.2) (fun s => hy s.1 s.2)

  have hA : ∀ (b : Fin n) (i : Fin d), compV (B.A.act (N : O)) (pt V (n := n) d b) i ∈
      Ideal.span (Set.range fun s : Fin n × Fin d => y s.1 s.2) := by
    intro b i
    have e1 : compV (B.A.act (N : O)) (pt V (n := n) d b) i = matV B p' y b i := by
      rw [← hmul, hp, hsm]
    rw [e1, ← hev, evV, hψ]
    have := map_mem_span_of_constantCoeff_eq_zero ψ.toRingHom _ (h0 b i)
    simpa [hψX] using this
  refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (Submodule.fg_span (Set.finite_range _))
  rw [Ideal.span_le]
  rintro _ ⟨⟨b, i⟩, rfl⟩
  let a : Fin 1 × Fin d → PS V n d := fun q => (![pt V (n := n) d b] : Fin 1 → Pt V n d) q.1 q.2
  have ha : ∀ q, a q = MvPowerSeries.X (b, q.2) := by
    rintro ⟨q1, q2⟩
    obtain rfl : q1 = 0 := Subsingleton.elim _ _
    rfl
  have ha0 : ∀ q, MvPowerSeries.constantCoeff (a q) = 0 := by
    intro q; rw [ha]; simp
  obtain ⟨-, -, hs, -⟩ := evC_spec V (Fin 1 × Fin d) (Fin n × Fin d) Unit a
    (fun q => by rw [ha0]; exact zero_mem _)
  have hS : MvPowerSeries.HasSubst a := MvPowerSeries.hasSubst_of_constantCoeff_zero ha0
  have hS' : MvPowerSeries.HasSubst (fun q => MvPowerSeries.map (residue V) (a q)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => by rw [ha]; simp)
  let θ : PS (ResidueField V) 1 d →ₐ[ResidueField V] PS (ResidueField V) n d := MvPowerSeries.substAlgHom hS'
  have hθ : ∀ f : PS V 1 d, θ (MvPowerSeries.map (residue V) f) = MvPowerSeries.map (residue V) (evC a f) := by
    intro f
    rw [hs ha0, MvPowerSeries.map_subst hS]
    simp only [θ, MvPowerSeries.coe_substAlgHom]
  have hX : θ (MvPowerSeries.X (0, i)) = MvPowerSeries.X (b, i) := by
    simp only [θ, MvPowerSeries.coe_substAlgHom]
    rw [MvPowerSeries.subst_X hS', ha]
    simp
  have h1 := Ideal.mem_map_of_mem θ (hM (Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self (0, i))) M))
  rw [map_pow, hX] at h1
  refine ⟨M, ?_⟩
  refine SetLike.le_def.1 ?_ h1
  rw [Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  have h2 := Ideal.mem_map_of_mem (MvPowerSeries.map (σ := Fin n × Fin d) (residue V)) (hA b j)
  rw [Ideal.map_span, ← Set.range_comp] at h2
  rw [SetLike.mem_coe, hθ]
  exact h2

end GlobalTheory.PlaceInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowSpanXLeSpanFormalModuleMatrixStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_pow_span_X_le_span_formalModuleMatrix : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O), FinHt B → ∀ (n : ℕ) (p p' : Matrix (Fin n) (Fin n) O) (N : ℕ), 1 ≤ N → p' * p = (N : O) • (1 : Matrix (Fin n) (Fin n) O) → ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin n × Fin d → PS (ResidueField V) n d)) ^ M ≤ Ideal.span (Set.range fun s : Fin n × Fin d => MvPowerSeries.map (residue V) (matV B p (fun j => pt V (n := n) d j) s.1 s.2)) := by
  first | exact @GlobalTheory.PlaceInt.exists_pow_span_X_le_span_matV | exact GlobalTheory.PlaceInt.exists_pow_span_X_le_span_matV | (intros; apply GlobalTheory.PlaceInt.exists_pow_span_X_le_span_matV <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantSectionEqLimitChartPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantSectionEqLimitChartPoint
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit

namespace GlobalTheory.TransUnit

theorem ptOf_const_left : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (G : Over (Sp V)) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (X : limO V d 1 ⟶ G), IsLimit x X → ∀ (α : Fin d → V) (hα : Small α) (aV : Sp V ⟶ G.left), (∀ m : ℕ, ∃ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] V ⧸ maximalIdeal V ^ (m + 1), (∀ p, ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (α p.2)) ∧ spMap (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))) ≫ aV = spMap (ψ : Jet V (Fin 1 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (x m).left) → ∀ n : ℕ, (ptOf X (Sm.const B α hα : Sm B n)).left = spMap (algebraMap V (PS V n d)) ≫ aV := by
  intro V _ _ _ _ _ d O _ _ B G x X hX α hα aV ha n
  let χ : PS V 1 d →ₐ[V] V :=
    GlobalTheory.mvEvalAdic V (maximalIdeal V) (fun p : Fin 1 × Fin d => α p.2) (fun p => hα p.2)
  have hχ : ∀ p, χ (MvPowerSeries.X p) = α p.2 := fun p => GlobalTheory.mvEvalAdic_X _ _ _ p
  have h1 : evA ![(Sm.const B α hα : Sm B n)] = (Algebra.ofId V (PS V n d)).comp χ := by
    refine AlgHom.ext fun f => (evA_apply _ f).trans ?_
    refine evC_eq_algHom _ (fun p : Fin 1 × Fin d => ((![(Sm.const B α hα : Sm B n)] : Fin 1 → Sm B n) p.1).2 p.2)
      _ (fun p => ?_) f
    obtain ⟨i, j⟩ := p
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rw [AlgHom.comp_apply, hχ]
    rfl
  have h2 : spMap (χ : PS V 1 d →+* V) ≫ X.left = aV := by
    refine GlobalTheory.hom_ext_of_isHausdorff (maximalIdeal V) fun m => ?_
    obtain ⟨ψ, hψ, e⟩ := ha m
    have hj : ∀ p : Fin 1 × Fin d, jetA (V := V) (Fin 1 × Fin d) m (MvPowerSeries.X p) =
        Ideal.Quotient.mk _ (MvPolynomial.X p) := fun p => by
      first
      | exact (mk_psTrunc m _ (MvPowerSeries.constantCoeff_X p)).trans (Chart.pj_X m p)
      | exact FBIdSy.mk_psTrunc_X m p
      | exact (mk_psTrunc m _ (MvPowerSeries.constantCoeff_X p)).symm.trans (Chart.pj_X m p)
    have k : ψ.comp (jetA (Fin 1 × Fin d) m) = (Ideal.Quotient.mkₐ V (maximalIdeal V ^ (m + 1))).comp χ := by
      have hv : ∀ p, (ψ.comp (jetA (Fin 1 × Fin d) m)) (MvPowerSeries.X p) = Ideal.Quotient.mk _ (α p.2) :=
        fun p => by rw [AlgHom.comp_apply, hj, hψ]
      have hv' : ∀ p, ((Ideal.Quotient.mkₐ V (maximalIdeal V ^ (m + 1))).comp χ) (MvPowerSeries.X p) =
          Ideal.Quotient.mk _ (α p.2) := fun p => by rw [AlgHom.comp_apply, hχ]; rfl
      refine AlgHom.ext fun f => ?_
      have := GlobalTheory.algHom_sub_mem_pow _ _
        (J := (maximalIdeal V).map (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))))
        (fun p => hv p ▸ Ideal.mem_map_of_mem _ (hα p.2)) (fun p => hv' p ▸ Ideal.mem_map_of_mem _ (hα p.2))
        (n := m + 1) (fun p => by rw [hv, hv', sub_self]; exact zero_mem _) f
      rw [← Ideal.map_pow, Ideal.map_quotient_self, Ideal.mem_bot, sub_eq_zero] at this
      exact this
    have k2 := GlobalTheory.PlaceFormPt.spMap_homAt (jetA (Fin 1 × Fin d) m) ψ X.left
    rw [k] at k2
    have k3 : (x m).left = (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetA (Fin 1 × Fin d) m)).left ≫ X.left :=
      (congrArg (fun q => q.left) (hX m)).symm
    refine Eq.trans ?_ (k2.symm.trans ((congrArg (_ ≫ ·) k3.symm).trans e.symm))
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ X.left) (Spec.map_comp _ _).symm)
  rw [← h2, ptOf, h1]
  exact (congrArg (· ≫ X.left) (Spec.map_comp (CommRingCat.ofHom (χ : PS V 1 d →+* V))
    (CommRingCat.ofHom (algebraMap V (PS V n d))))).trans (Category.assoc _ _ _)

end GlobalTheory.TransUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ConstantSectionEqLimitChartPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constantSection_eq_limitChart_point : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (G : Over (Sp V)) (x : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ G) (X : limO V d 1 ⟶ G), IsLimit x X → ∀ (α : Fin d → V) (hα : Small α) (aV : Sp V ⟶ G.left), (∀ m : ℕ, ∃ ψ : Jet V (Fin 1 × Fin d) m →ₐ[V] V ⧸ maximalIdeal V ^ (m + 1), (∀ p, ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (α p.2)) ∧ spMap (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))) ≫ aV = spMap (ψ : Jet V (Fin 1 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (x m).left) → ∀ n : ℕ, (ptOf X (Sm.const B α hα : Sm B n)).left = spMap (algebraMap V (PS V n d)) ≫ aV := by
  first | exact @GlobalTheory.TransUnit.ptOf_const_left | exact GlobalTheory.TransUnit.ptOf_const_left | (intros; apply GlobalTheory.TransUnit.ptOf_const_left <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvalIotaSeriesEqQuadraticInversionPartials
section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvalIotaSeriesEqQuadraticInversionPartials
set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
open ReciprocityTheory.ChartRestriction.G.TB.WickVanishing GlobalTheory.PlaceInt.ThetaInt

namespace GlobalTheory.TransUnit.IotaLaw

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V]
  {d : ℕ} {O : Type} [CommRing O] [StarRing O] {B : FB V d O} {n : ℕ}

theorem evA_three (x y z : Sm B n) (hx : GP x.1) (hy : GP y.1) (hz : GP z.1) (f : PS V 3 d) :
    evA ![x, y, z] f = ev ![x.1, y.1, z.1] f := by
  rw [evA_eq_ev]
  · congr 1
    funext j
    fin_cases j <;> rfl
  · intro j i
    fin_cases j
    exacts [hx i, hy i, hz i]

theorem mul_val_of (x y : Sm B n) (hx : GP x.1) (hy : GP y.1) : (x * y).1 = addOf B.G.F x.1 y.1 := by
  rw [Sm.mul_val]
  funext i
  show evV ![x.1, y.1] (B.G.F i) = ev ![x.1, y.1] (B.G.F i)
  rw [← smallPointsSubstitutionAlgHom_two_points, evA_eq_ev]
  · congr 1
    funext j
    fin_cases j <;> rfl
  · intro j k
    fin_cases j
    exacts [hx k, hy k]

theorem compV_of (φ : Pt V 1 d) (x : Sm B n) (hx : GP x.1) : compV φ x.1 = comp1 φ x.1 := by
  funext i
  show evV ![x.1] (φ i) = ev ![x.1] (φ i)
  rw [← smallPointsSubstitutionAlgHom_single_point, evA_eq_ev]
  · congr 1
    funext j
    fin_cases j
    rfl
  · intro j k
    fin_cases j
    exact hx k

theorem constantCoeff_act_eq_zero (o : O) (x : Sm B n) (hx : GP x.1) : GP (Sm.act B o x).1 := by
  rw [Sm.act_val, compV_of _ x hx]
  exact gp_comp1 _ _ (fun i => B.A.const o i) hx

theorem constantCoeff_inv_eq_zero (x : Sm B n) (hx : GP x.1) : GP (x⁻¹).1 := by
  rw [Sm.inv_val, ← Sm.act_val]
  exact constantCoeff_act_eq_zero (-1) x hx

variable (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] {h : PS K 2 d}

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] [Algebra ℚ K] in
theorem mp_zero : mp K (0 : Pt V n d) = 0 := by
  funext i
  simp [mp]

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one (hh : B.IsCanonGauge K h) (a : Pt K n d) (ha : GP a) : ev ![0, a] h = 0 := by
  obtain ⟨h1, h2, -, -, -, -⟩ := hh
  have hv : ∀ j, GP (![a] j) := single_point_zero_constant ha
  have hw : ∀ j, GP (![(0 : Pt K 1 d), pt K (n := 1) d 0] j) := pair_points_zero_constant gp_zero₂ (gp_pt 0)
  have e := gt_ev_ev' ![a] _ hv hw h
  rw [h1, eval_pair_points, evP_zero _ hv, evP_pt _ hv] at e
  simp only [Matrix.cons_val_zero] at e
  rw [← e, gt_ev_zero _ hv]

omit [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] in
theorem canonicalGauge_eval_zero_right (hh : B.IsCanonGauge K h) (a : Pt K n d) (ha : GP a) : ev ![a, 0] h = 0 := by
  obtain ⟨h1, h2, -, -, -, -⟩ := hh
  have hv : ∀ j, GP (![a] j) := single_point_zero_constant ha
  have hw : ∀ j, GP (![pt K (n := 1) d 0, (0 : Pt K 1 d)] j) := pair_points_zero_constant (gp_pt 0) gp_zero₂
  have e := gt_ev_ev' ![a] _ hv hw h
  rw [h2, eval_pair_points, evP_zero _ hv, evP_pt _ hv] at e
  simp only [Matrix.cons_val_zero] at e
  rw [← e, gt_ev_zero _ hv]

theorem canonicalGauge_first_partial_law_in_field (hh : B.IsCanonGauge K h) (x y z : Sm B n) (hx : GP x.1) (hy : GP y.1) (hz : GP z.1) :
    FB.toK K (evA ![x, y, z] B.ph1) = FB.expS K (ev ![mp K x.1, mp K z.1] h + ev ![mp K y.1, mp K z.1] h
      - ev ![mp K (x * y).1, mp K z.1] h) := by
  have hc : MvPowerSeries.constantCoeff h = 0 := cc_gauge (K := K) (B := B) hh
  obtain ⟨-, -, h3, h4, -, -⟩ := hh
  have hF : ∀ i, MvPowerSeries.constantCoeff (B.FK K i) = 0 := cc_FK (K := K) (B := B)
  have p0 : GP (pt K (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt K (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt K (n := 3) d 2) := gp_pt 2
  have pa : GP (addOf (B.FK K) (pt K (n := 3) d 0) (pt K d 1)) := gp_addOf _ hF _ _ p0 p1
  have hX : ∀ j, GP (![mp K x.1, mp K y.1, mp K z.1] j) := triple_points_zero_constant (constantCoeff_baseChange_eq_zero K hx) (constantCoeff_baseChange_eq_zero K hy) (constantCoeff_baseChange_eq_zero K hz)
  have hv : (fun j => mp K (![x.1, y.1, z.1] j)) = ![mp K x.1, mp K y.1, mp K z.1] := by
    funext j
    fin_cases j <;> rfl
  rw [evA_three x y z hx hy hz, toK_ev K _ (triple_points_zero_constant hx hy hz), h3, hv]
  rw [gt_ev_expS _ hX]
  · congr 1
    rw [gt_ev_sub _ hX, gt_ev_add _ hX, gt_ev_ev' _ _ hX (pair_points_zero_constant p0 p2), gt_ev_ev' _ _ hX (pair_points_zero_constant p1 p2),
      gt_ev_ev' _ _ hX (pair_points_zero_constant pa p2), eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hX _ _ _ p0 p1,
      evP_pt _ hX, evP_pt _ hX, evP_pt _ hX, mul_val_of x y hx hy, mp_addOf K B.G _ _ hx hy]
    rfl
  · rw [map_sub, map_add (f := _), gt_const_ev_eq _ (pair_points_zero_constant p0 p2), gt_const_ev_eq _ (pair_points_zero_constant p1 p2),
      gt_const_ev_eq _ (pair_points_zero_constant pa p2), hc]
    simp

theorem canonicalGauge_second_partial_law_in_field (hh : B.IsCanonGauge K h) (x y z : Sm B n) (hx : GP x.1) (hy : GP y.1) (hz : GP z.1) :
    FB.toK K (evA ![x, y, z] B.ph2) = FB.expS K (ev ![mp K x.1, mp K y.1] h + ev ![mp K x.1, mp K z.1] h
      - ev ![mp K x.1, mp K (y * z).1] h) := by
  have hc : MvPowerSeries.constantCoeff h = 0 := cc_gauge (K := K) (B := B) hh
  obtain ⟨-, -, h3, h4, -, -⟩ := hh
  have hF : ∀ i, MvPowerSeries.constantCoeff (B.FK K i) = 0 := cc_FK (K := K) (B := B)
  have p0 : GP (pt K (n := 3) d 0) := gp_pt 0
  have p1 : GP (pt K (n := 3) d 1) := gp_pt 1
  have p2 : GP (pt K (n := 3) d 2) := gp_pt 2
  have pa : GP (addOf (B.FK K) (pt K (n := 3) d 1) (pt K d 2)) := gp_addOf _ hF _ _ p1 p2
  have hX : ∀ j, GP (![mp K x.1, mp K y.1, mp K z.1] j) := triple_points_zero_constant (constantCoeff_baseChange_eq_zero K hx) (constantCoeff_baseChange_eq_zero K hy) (constantCoeff_baseChange_eq_zero K hz)
  have hv : (fun j => mp K (![x.1, y.1, z.1] j)) = ![mp K x.1, mp K y.1, mp K z.1] := by
    funext j
    fin_cases j <;> rfl
  rw [evA_three x y z hx hy hz, toK_ev K _ (triple_points_zero_constant hx hy hz), h4, hv]
  rw [gt_ev_expS _ hX]
  · congr 1
    rw [gt_ev_sub _ hX, gt_ev_add _ hX, gt_ev_ev' _ _ hX (pair_points_zero_constant p0 p1), gt_ev_ev' _ _ hX (pair_points_zero_constant p0 p2),
      gt_ev_ev' _ _ hX (pair_points_zero_constant p0 pa), eval_pair_points, eval_pair_points, eval_pair_points, evP_addOf _ hX _ _ _ p1 p2,
      evP_pt _ hX, evP_pt _ hX, evP_pt _ hX, mul_val_of y z hy hz, mp_addOf K B.G _ _ hy hz]
    rfl
  · rw [map_sub, map_add (f := _), gt_const_ev_eq _ (pair_points_zero_constant p0 p1), gt_const_ev_eq _ (pair_points_zero_constant p0 p2),
      gt_const_ev_eq _ (pair_points_zero_constant p0 pa), hc]
    simp

private theorem eq_of_toK_eq_of_injective (hi : Function.Injective (algebraMap V K)) {m : ℕ} (a b : PS V m d)
    (hab : FB.toK K a = FB.toK K b) : a = b := by
  unfold FB.toK at hab
  refine MvPowerSeries.ext fun k => ?_
  have e := congrArg (MvPowerSeries.coeff k) hab
  rw [MvPowerSeries.coeff_map, MvPowerSeries.coeff_map] at e
  exact hi e

theorem iota_gen (hi : Function.Injective (algebraMap V K)) (hh : B.IsCanonGauge K h) (w0 : O)
    (p₁ p₂ : (PS V 3 d)ˣ) (e₁ : p₁.val = B.ph1) (e₂ : p₂.val = B.ph2) (jo : PS V 1 d) (hj : IsIota B K h w0 jo) :
    jo = (quadN (u3 p₁) (u3 p₂) (Sm.act B w0) (Sm.gen B (0 : Fin 1))).val := by
  unfold IsIota at hj
  set g : Sm B 1 := Sm.gen B 0 with hgdef
  have hg : GP g.1 := gp_pt 0
  have hgi : GP (g⁻¹).1 := constantCoeff_inv_eq_zero g hg
  have hwg : GP (Sm.act B w0 g).1 := constantCoeff_act_eq_zero w0 g hg
  have hwgi : GP ((Sm.act B w0 g)⁻¹).1 := constantCoeff_inv_eq_zero _ hwg
  have hc : MvPowerSeries.constantCoeff h = 0 := cc_gauge (K := K) (B := B) hh
  have c2 : ∀ a b : Pt K 1 d, GP a → GP b → MvPowerSeries.constantCoeff (ev ![a, b] h) = 0 := fun a b ha hb => by
    rw [gt_const_ev_eq _ (pair_points_zero_constant ha hb), hc]
  have hL1 : B.hL K h w0 = ev ![mp K g.1, mp K (Sm.act B w0 g).1] h := by
    have e := ev_hL K B h w0 g.1 hg
    rw [Sm.act_val, compV_of _ g hg, ← e, show mp K g.1 = pt K (n := 1) d 0 from mp_pt K 0, gt_ev_pt_self]
  have ha : mp K (g⁻¹).1 = B.actK K (-1) := by
    rw [Sm.inv_val, compV_of _ g hg]
    show mp K (comp1 (B.A.act (-1)) (pt V (n := 1) d 0)) = _
    rw [gt_comp1_pt_right]
    rfl
  have hL2 : ev ![B.actK K (-1)] (B.hL K h w0) = ev ![mp K (g⁻¹).1, mp K ((Sm.act B w0 g)⁻¹).1] h := by
    rw [← ha, ev_hL K B h w0 (g⁻¹).1 hgi, ← map_inv (Sm.act B w0) g, Sm.act_val, compV_of _ _ hgi]
  have key : jo * (u3 p₁ g g⁻¹ (Sm.act B w0 g)).val = (u3 p₂ g⁻¹ (Sm.act B w0 g) (Sm.act B w0 g)⁻¹).val := by
    apply eq_of_toK_eq_of_injective K hi
    have hm : ∀ a b : PS V 1 d, FB.toK K (a * b) = FB.toK K a * FB.toK K b := fun a b => by
      unfold FB.toK
      exact map_mul _ _ _
    rw [hm, hj]
    unfold u3
    rw [evU_val, evU_val, e₁, e₂, canonicalGauge_first_partial_law_in_field K hh g g⁻¹ _ hg hgi hwg, canonicalGauge_second_partial_law_in_field K hh g⁻¹ _ _ hgi hwg hwgi,
      mul_inv_cancel, mul_inv_cancel, Sm.one_val, mp_zero K, ev_zero_zero_gp_eq_one_of_ev_zero_pt_pt_eq_one K hh _ (constantCoeff_baseChange_eq_zero K hwg),
      canonicalGauge_eval_zero_right K hh _ (constantCoeff_baseChange_eq_zero K hgi), hL2, hL1]
    have cA := c2 _ _ (constantCoeff_baseChange_eq_zero K hgi) (constantCoeff_baseChange_eq_zero K hwgi)
    have cB := c2 _ _ (constantCoeff_baseChange_eq_zero K hg) (constantCoeff_baseChange_eq_zero K hwg)
    have cQ := c2 _ _ (constantCoeff_baseChange_eq_zero K hgi) (constantCoeff_baseChange_eq_zero K hwg)
    rw [← gt_expS_add]
    · congr 1
      ring
    · simp [cA, cB]
    · simp [cB, cQ]
  unfold quadN
  rw [div_eq_mul_inv, Units.val_mul, ← key, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

end GlobalTheory.TransUnit.IotaLaw

namespace GlobalTheory.TransUnit

theorem evA_iota_eq_quadN : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (p₁ p₂ : (PS V 3 d)ˣ), p₁.val = B.ph1 → p₂.val = B.ph2 → ∀ jo : PS V 1 d, IsIota B K h w0 jo → ∀ (n : ℕ) (x : Sm B n), evA ![x] jo = (quadN (u3 p₁) (u3 p₂) (Sm.act B w0) x).val := by
  intro V _ _ _ _ _ d O _ _ B K _ _ _ _ h w0 hh p₁ p₂ e₁ e₂ jo hj n x
  rw [IotaLaw.iota_gen K (IsFractionRing.injective V K) hh w0 p₁ p₂ e₁ e₂ jo hj, ← evU_val,
    ← quadN_map (Sm.sub ![x]) (evU ![x]) (fun y => (Sm.sub_act ![x] w0 y).symm) (fun a b c => unitSeriesValueThreePoints_substitution ![x] p₁ a b c)
      (fun a b c => unitSeriesValueThreePoints_substitution ![x] p₂ a b c) (Sm.gen B 0), Sm.sub_gen]
  rfl

end GlobalTheory.TransUnit
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvalIotaSeriesEqQuadraticInversionPartialsStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eval_iotaSeries_eq_quadratic_inversion_partials : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (p₁ p₂ : (PS V 3 d)ˣ), p₁.val = B.ph1 → p₂.val = B.ph2 → ∀ jo : PS V 1 d, IsIota B K h w0 jo → ∀ (n : ℕ) (x : Sm B n), evA ![x] jo = (quadN (u3 p₁) (u3 p₂) (Sm.act B w0) x).val := by
  first | exact @GlobalTheory.TransUnit.evA_iota_eq_quadN | exact GlobalTheory.TransUnit.evA_iota_eq_quadN | (intros; apply GlobalTheory.TransUnit.evA_iota_eq_quadN <;> assumption)
end
end
