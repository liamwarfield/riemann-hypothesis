module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeCocycleClassIndependent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.CompatH
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.IsUnitWitt
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.DividedPowerReduction.IsFirstChernThickening

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrame
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrame
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

theorem taylor_alg {K A B : Type} [CommRing K] [CommRing A] [Algebra K A] [CommRing B] [Algebra K B] {d : ℕ}
    (t : Fin d → A)
    (hf : (MvPolynomial.eval₂Hom (algebraMap K A) t : MvPolynomial (Fin d) K →+* A).FormallyUnramified)
    (D : Fin d → Derivation K A A) (hD : ∀ k j, D k (t j) = if k = j then 1 else 0)
    (N P : Ideal B) (hNP : N * N ≤ P) (a b : A →ₐ[K] B) (hab : ∀ x, a x - b x ∈ N) (x : A) :
    a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) ∈ P := by
  classical
  let f : MvPolynomial (Fin d) K →+* A := MvPolynomial.eval₂Hom (algebraMap K A) t
  let π : B →+* B ⧸ P := Ideal.Quotient.mk P
  let e : Fin d → B := fun k => a (t k) - b (t k)
  have he : ∀ k, e k ∈ N := fun k => hab _
  let S : A → B := fun x => ∑ k, e k * b (D k x)
  have hS : ∀ x, S x ∈ N := fun x => Ideal.sum_mem _ fun k _ => N.mul_mem_right _ (he k)
  have hSadd : ∀ x y, S (x + y) = S x + S y := fun x y => by
    simp only [S, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have hSmul : ∀ x y, S (x * y) = b x * S y + b y * S x := fun x y => by
    simp only [S, Derivation.leibniz, smul_eq_mul, map_add (f := _), map_mul, mul_add, Finset.sum_add_distrib,
      Finset.mul_sum]
    congr 1 <;> exact Finset.sum_congr rfl fun k _ => by ring
  have hSone : S 1 = 0 := by simp [S]
  have hSzero : S 0 = 0 := by simp [S]
  let c : A →+* B ⧸ P :=
    { toFun := fun x => π (b x + S x)
      map_one' := by simp [hSone]
      map_zero' := by simp [hSzero]
      map_add' := fun x y => by
        rw [hSadd, map_add b, ← map_add π]
        congr 1
        ring
      map_mul' := fun x y => by
        rw [← map_mul π]
        refine Ideal.Quotient.eq.2 ?_
        have h := hNP (Ideal.mul_mem_mul (hS x) (hS y))
        have e2 : b (x * y) + S (x * y) - (b x + S x) * (b y + S y) = -(S x * S y) := by
          rw [hSmul, map_mul]
          ring
        rw [e2]
        exact P.neg_mem h }
  have hc : ∀ x, c x = π (b x + S x) := fun _ => rfl
  have hcf : c.comp f = π.comp ((a : A →+* B).comp f) := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) fun i => ?_
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_C, hc]
      have : S (algebraMap K A r) = 0 := by simp [S]
      simp [this]
    · simp only [RingHom.comp_apply, f, MvPolynomial.eval₂Hom_X', hc]
      have : S (t i) = e i := by simp [S, hD, e]
      rw [this]
      simp [e]
  letI algA : Algebra (MvPolynomial (Fin d) K) A := f.toAlgebra
  letI algC : Algebra (MvPolynomial (Fin d) K) (B ⧸ P) := (π.comp ((a : A →+* B).comp f)).toAlgebra
  haveI : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) A := hf
  let g₁ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := π.comp (a : A →+* B), commutes' := fun _ => rfl }
  let g₂ : A →ₐ[MvPolynomial (Fin d) K] B ⧸ P :=
    { toRingHom := c, commutes' := fun p => RingHom.congr_fun hcf p }
  have hnil : IsNilpotent (N.map π) := by
    refine ⟨2, ?_⟩
    rw [pow_two, ← Ideal.map_mul, Ideal.zero_eq_bot]
    refine le_bot_iff.1 ((Ideal.map_mono hNP).trans ?_)
    rw [Ideal.map_quotient_self]
  have hg : g₁ = g₂ := by
    refine Algebra.FormallyUnramified.ext (N.map π) hnil fun y => ?_
    refine Ideal.Quotient.eq.2 ?_
    have : g₁ y - g₂ y = π (a y - (b y + S y)) := by
      rw [map_sub]
      rfl
    rw [this]
    refine Ideal.mem_map_of_mem π ?_
    have e3 : a y - (b y + S y) = (a y - b y) - S y := by ring
    rw [e3]
    exact N.sub_mem (hab y) (hS y)
  have h1 : π (a x) = π (b x + S x) := DFunLike.congr_fun hg x
  have h2 := Ideal.Quotient.eq.1 h1
  have e4 : a x - (b x + S x) = a x - b x - ∑ k, (a (t k) - b (t k)) * b (D k x) := by
    simp only [S, e]
    ring
  rwa [e4] at h2

theorem taylor_loc : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε →
    letI := (strV q W).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, W) Γ(X, W)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    Taylor (sFil (KS q s {W})) E (fun k x => ε (D k (ε.symm x))) := by
  intro K _ _ X q W d c s E ε h
  letI := (strV q W).toAlgebra
  intro D hD
  obtain ⟨-, -, h3, h4, h5⟩ := h
  intro T u v x
  obtain ⟨y, rfl⟩ := ε.surjective x
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {W})
  have hcomm : ∀ (w : E.D ⟶ T) (r : K), ((sP (KS q s {W})).A.map w).hom (ε (algebraMap K Γ(X, W) r)) =
      algebraMap K ((sP (KS q s {W})).A.obj T) r := fun w r => by
    have e : ε (algebraMap K Γ(X, W) r) = algebraMap K _ r := h3 r
    rw [e]
    exact AlgHom.commutes _ r
  let ev' : (E.D ⟶ T) → (Γ(X, W) →ₐ[K] (sP (KS q s {W})).A.obj T) := fun w =>
    { toRingHom := RingHom.comp (AlgHom.toRingHom ((sP (KS q s {W})).A.map w).hom) ε.toRingHom
      commutes' := hcomm w }
  have hNP : (sFil (KS q s {W}) 1).S T * (sFil (KS q s {W}) 1).S T ≤ (sFil (KS q s {W}) 2).S T :=
    Ideal.mul_le.2 fun a ha b hb => hF.mul 1 1 T ha hb
  have hab : ∀ g, ev' u g - ev' v g ∈ (sFil (KS q s {W}) 1).S T := fun g => by
    rw [hF.one T]
    have e := (h4 T u g).symm.trans (h4 T v g)
    exact Ideal.Quotient.eq.1 e
  have hf : (MvPolynomial.eval₂Hom (algebraMap K Γ(X, W)) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).FormallyUnramified :=
    by
      have he := c.etale
      letI := (MvPolynomial.eval₂Hom (strV q W) c.t : MvPolynomial (Fin d) K →+* Γ(X, W)).toAlgebra
      haveI : Algebra.Etale (MvPolynomial (Fin d) K) Γ(X, W) := he
      exact (inferInstance : Algebra.FormallyUnramified (MvPolynomial (Fin d) K) Γ(X, W))
  have key := taylor_alg c.t hf D hD _ _ hNP (ev' u) (ev' v) hab y
  have e : ∀ k, E.τ k v u = ev' u (c.t k) - ev' v (c.t k) := fun k => h5 k v u
  simp only [ε.symm_apply_apply, e]
  exact key

end GlobalTheory.CompanionTheory.ConeLocal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TaylorOfLocalFrameStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.taylor_of_local_frame : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (s : ℕ) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D), IsLoc q s c.t E ε →
    letI := (strV q W).toAlgebra
    ∀ (D : Fin d → Derivation K Γ(X, W) Γ(X, W)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    Taylor (sFil (KS q s {W})) E (fun k x => ε (D k (ε.symm x))) := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.taylor_loc | exact GlobalTheory.CompanionTheory.ConeLocal.taylor_loc | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.taylor_loc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormSumRepresentativeLift
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormSumRepresentativeLift
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section Collapse
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {d : ℕ}

theorem form_sum_zsmul (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {m : ℕ} (I : Fin m → Fin d)
    {ι : Type} [Fintype ι] (a : ι → ℤ) (w : ι → Φ.A.obj E.D) (u : ComposableArrows C m) :
    E.form σ I (∑ i, a i • w i) u = ∑ i, a i • E.form σ I (w i) u := by
  unfold Frame.form
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul, mul_smul_comm]

theorem form_zsmul (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) {m : ℕ} (I : Fin m → Fin d)
    (a : ℤ) (w : Φ.A.obj E.D) (u : ComposableArrows C m) :
    E.form σ I (a • w) u = a • E.form σ I w u := by
  unfold Frame.form
  rw [map_zsmul, mul_smul_comm]

theorem sgn_eq_zero_of_not_injective {m : ℕ} (I : Idx m d) {J : Fin m → Fin d} (h : ¬ Function.Injective J) :
    sgn I J = 0 := by
  refine Finset.sum_eq_zero fun π _ => if_neg ?_
  intro e
  exact h (e ▸ I.2.injective.comp π.injective)

theorem exists_increasing {m : ℕ} {J : Fin m → Fin d} (h : Function.Injective J) :
    ∃ (I : Idx m d) (π : Equiv.Perm (Fin m)), J = I.1 ∘ π := by
  refine ⟨⟨J ∘ Tuple.sort J, (Tuple.monotone_sort J).strictMono_of_injective
    (h.comp (Tuple.sort J).injective)⟩, (Tuple.sort J)⁻¹, ?_⟩
  funext k
  simp

theorem sgn_comp_self {m : ℕ} (I : Idx m d) (π : Equiv.Perm (Fin m)) :
    sgn I (I.1 ∘ π) = (Equiv.Perm.sign π : ℤ) := by
  unfold sgn
  rw [Finset.sum_eq_single π]
  · simp
  · intro b _ hb
    refine if_neg fun e => hb ?_
    exact (Equiv.ext fun k => I.2.injective (congrFun e k)).symm
  · simp

theorem sgn_comp_of_ne {m : ℕ} {I I' : Idx m d} (π : Equiv.Perm (Fin m)) (h : I' ≠ I) :
    sgn I' (I.1 ∘ π) = 0 := by
  refine Finset.sum_eq_zero fun π' _ => if_neg fun e => h (Subtype.ext ?_)
  refine (StrictMono.range_inj I'.2 I.2).1 ?_
  have e' := congrArg Set.range e
  rw [π.surjective.range_comp, π'.surjective.range_comp] at e'
  exact e'.symm

theorem rep_finset_sum {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ} {ι : Type} (t : Finset ι)
    {z : ι → ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c : ι → CH.H (sq a b) j}
    (h : ∀ i, CrystallineSemistableComparison.Pb.Rep a b (z i) (c i)) :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => ∑ i ∈ t, z i s) (∑ i ∈ t, c i) := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact rep_zero fun s => Ideal.zero_mem _
  | insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact rep_add (h i) ih

theorem rep_collapse_one {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T)
    (hc : E.GrConst Fil) (m : ℕ) (r : ℤ) (hr : r = m) (J : Fin m → Fin d) (w : Φ.A.obj E.D)
    (c : CH.H (gr Fil r) m) (h : CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (E.form σ J w) c) :
    CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (sgn I J • w) u) c := by
  have hw : w ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := by
    rw [hF.top _ (by simp)]
    trivial
  have hr0 : r = (m : ℤ) + ((0 : ℕ) : ℤ) := by simpa using hr
  by_cases hJ : Function.Injective J
  · obtain ⟨I, π, rfl⟩ := exists_increasing hJ
    obtain ⟨c₀, h₀⟩ := GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc m 0 r hr0 I.1 w hw
    have h₁ := (GlobalTheory.CompanionTheory.AltForm.form_alternating hF E σ hc m 0 r hr0 I.1 w hw c₀ h₀).2.1 π
    obtain rfl := rep_unique h h₁
    have h₂ := GlobalTheory.CompanionTheory.AltForm.Rep.zsmul (Equiv.Perm.sign π : ℤ) h₀
    refine rep_congr h₂ fun u => ?_
    rw [Finset.sum_eq_single I, sgn_comp_self, form_zsmul, Pi.smul_apply, sub_self]
    · exact Ideal.zero_mem _
    · intro I' _ hI'
      rw [sgn_comp_of_ne π hI', zero_smul]
      unfold Frame.form
      simp
    · simp
  · obtain rfl := (GlobalTheory.CompanionTheory.AltForm.form_alternating hF E σ hc m 0 r hr0 J w hw c h).1 hJ
    refine rep_zero fun u => ?_
    rw [Finset.sum_eq_zero]
    · exact Ideal.zero_mem _
    · intro I _
      rw [sgn_eq_zero_of_not_injective I hJ, zero_smul]
      unfold Frame.form
      simp

theorem rep_collapse : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (m : ℕ) (r : ℤ), r = m → ∀ {ι : Type} [Fintype ι] (J : ι → Fin m → Fin d) (w : ι → Φ.A.obj E.D) (x : CH.H (gr Fil r) m),
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ i, E.form σ (J i) (w i) u) x →
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (∑ i, sgn I (J i) • w i) u) x := by
  intro R _ C _ Φ Fil d hF E σ hc m r hr ι _ J w x h
  have hw : ∀ i, w i ∈ (Fil ((0 : ℕ) : ℤ)).S E.D := fun i => by
    rw [hF.top _ (by simp)]
    trivial
  have hr0 : r = (m : ℤ) + ((0 : ℕ) : ℤ) := by simpa using hr
  choose c hcl using fun i => GlobalTheory.CompanionTheory.CocProd.rep_form hF E σ hc m 0 r hr0 (J i) (w i) (hw i)
  obtain rfl := rep_unique h (rep_finset_sum Finset.univ hcl)
  have h₂ := rep_finset_sum Finset.univ fun i => rep_collapse_one hF E σ hc m r hr (J i) (w i) (c i) (hcl i)
  refine rep_congr h₂ fun u => ?_
  rw [Finset.sum_comm]
  have e : ∀ I : Idx m d, E.form σ I.1 (∑ i, sgn I (J i) • w i) u = ∑ i, E.form σ I.1 (sgn I (J i) • w i) u := by
    intro I
    rw [form_sum_zsmul]
    exact Finset.sum_congr rfl fun i _ => (form_zsmul E σ I.1 _ _ u).symm
  simp only [e, sub_self]
  exact Ideal.zero_mem _

end Collapse

end GlobalTheory.CompanionTheory.ConeLocal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormSumRepresentativeLiftStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.form_sum_representative_lift : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A} {d : ℕ} (hF : IsFil Φ Fil) (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (hc : E.GrConst Fil)
    (m : ℕ) (r : ℤ), r = m → ∀ {ι : Type} [Fintype ι] (J : ι → Fin m → Fin d) (w : ι → Φ.A.obj E.D) (x : CH.H (gr Fil r) m),
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ i, E.form σ (J i) (w i) u) x →
      CrystallineSemistableComparison.Pb.Rep (Fil r) (Fil (r + 1)) (fun u => ∑ I : Idx m d, E.form σ I.1 (∑ i, sgn I (J i) • w i) u) x := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.rep_collapse | exact GlobalTheory.CompanionTheory.ConeLocal.rep_collapse | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.rep_collapse <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEq
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEq
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal.DlogApprox

theorem alg_core {B : Type} [CommRing B] (J F : Ideal B) (hJF : ∀ a ∈ J, ∀ b ∈ J, a * b ∈ F)
    {H H0 D Y0 I0 W : B} (hH : H ∈ J) (hH0 : H0 ∈ J) (hD : D ∈ J) (hI : Y0 * I0 = 1)
    (hW : W * ((1 + H0) * Y0) = 1) :
    (1 + H) * (Y0 + D) * W - 1 - (D * I0 + H - H0) ∈ F := by
  set C := W * Y0 with hCdef
  have hC : C * (1 + H0) = 1 := by rw [hCdef]; linear_combination hW
  have hWC : W = C * I0 := by rw [hCdef]; linear_combination (-W) * hI
  set A := H + D * I0 + H * (D * I0) with hA
  have hAJ : A ∈ J := J.add_mem (J.add_mem hH (J.mul_mem_right _ hD)) (J.mul_mem_left _ (J.mul_mem_right _ hD))
  have e : (1 + H) * (Y0 + D) * W - 1 - (D * I0 + H - H0) =
      (C * H0) * H0 - (A * C) * H0 + H * (D * I0) := by
    rw [hWC, hA]
    linear_combination (1 + H) * C * hI + (1 - H0 + (H + D * I0 + H * (D * I0))) * hC
  rw [e]
  exact F.add_mem (F.sub_mem (hJF _ (J.mul_mem_left _ hH0) _ hH0) (hJF _ (J.mul_mem_right _ hAJ) _ hH0))
    (hJF _ hH _ (J.mul_mem_right _ hD))

theorem plogK_sub_mem {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (F : Ideal B) {s : ℕ} (hs : 1 ≤ s)
    {x : B} (hx : x ∈ J) (h : ∀ k, 2 ≤ k → δ.dpow k x ∈ F) : plogK δ s x - x ∈ F := by
  obtain ⟨n, rfl⟩ : ∃ n, s = n + 1 := ⟨s - 1, by omega⟩
  unfold plogK
  rw [Finset.sum_range_succ']
  have e : (-1 : B) ^ 0 * ((Nat.factorial 0 : ℕ) : B) * δ.dpow (0 + 1) x = x := by
    simp [δ.dpow_one hx]
  rw [e, add_sub_cancel_right]
  exact F.sum_mem fun k _ => F.mul_mem_left _ (h _ (by omega))

section Fr
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem form_one {d : ℕ} (E : Frame Φ d) (σ : ∀ T : C, E.D ⟶ T) (i : Fin d) (x : Φ.A.obj E.D)
    (u : ComposableArrows C 1) :
    E.form σ ![i] x u = E.a σ i (u.map (homOfLE (Fin.zero_le (Fin.last 1)))) * (Φ.A.map (σ _)).hom x := by
  unfold Frame.form
  rw [Fin.prod_univ_one]
  congr 1
  have e : ∀ (h : (Fin.succ (0 : Fin 1)) ⟶ Fin.last 1) (z : Φ.A.obj (u.obj (Fin.last 1))),
      (Φ.A.map (u.map h)).hom z = z := by
    intro h z
    have : h = 𝟙 (Fin.last 1) := Subsingleton.elim _ _
    have e2 : u.map h = 𝟙 (u.obj (Fin.last 1)) := (congrArg u.map this).trans (u.map_id _)
    have e3 : Φ.A.map (u.map h) = 𝟙 (Φ.A.obj (u.obj (Fin.last 1))) := (congrArg Φ.A.map e2).trans (Φ.A.map_id _)
    rw [e3]
    rfl
  exact e _ _

theorem mul2 {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) (T : C) : ∀ a ∈ Φ.J.S T, ∀ b ∈ Φ.J.S T, a * b ∈ (Fil 2).S T := by
  intro a ha b hb
  have h1 : ∀ z ∈ Φ.J.S T, z ∈ (Fil ((1 : ℕ) : ℤ)).S T := fun z hz => by
    rw [Nat.cast_one, hF.one]; exact hz
  exact hF.mul 1 1 T (h1 a ha) (h1 b hb)

theorem const1 {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} {E : Frame Φ d} (hc : E.GrConst Fil) {T : C}
    (a b : E.D ⟶ T) (x : Φ.A.obj E.D) : (Φ.A.map a).hom x - (Φ.A.map b).hom x ∈ Φ.J.S T := by
  have h := hc 0 a b (x := x) (by rw [Nat.cast_zero, hF.top 0 le_rfl E.D]; trivial)
  rw [Nat.cast_zero, zero_add, hF.one] at h
  exact h

theorem frame_core {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) (ht : Taylor Fil E p) (σ : ∀ T : C, E.D ⟶ T)
    (G : Φ.A.obj E.D) (hG : IsUnit G) {T T' : C} (φ : T ⟶ T') {H H0 W : Φ.A.obj T'}
    (hH : H ∈ Φ.J.S T') (hH0 : H0 ∈ Φ.J.S T')
    (hW : W * ((1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G) = 1) :
    (1 + H) * (Φ.A.map (σ T')).hom G * W - 1 -
      (∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) + (H - H0)) ∈ (Fil 2).S T' := by
  set v := (Φ.A.map (σ T ≫ φ)).hom with hv
  set w := (Φ.A.map (σ T')).hom with hw
  have hI : v G * v (Ring.inverse G) = 1 := by
    rw [← map_mul, Ring.mul_inverse_cancel _ hG, map_one]
  have hD : w G - v G ∈ Φ.J.S T' := const1 hF hc _ _ G
  have h1 := alg_core (Φ.J.S T') ((Fil 2).S T') (mul2 hF T') hH hH0 hD hI hW
  have h2 := ((Fil 2).S T').mul_mem_left (v (Ring.inverse G)) (ht T' (σ T') (σ T ≫ φ) G)
  have h3 : ∑ i, E.a σ i φ * (v (Ring.inverse G * p i G) - w (Ring.inverse G * p i G)) ∈ (Fil 2).S T' :=
    ((Fil 2).S T').sum_mem fun i _ => mul2 hF T' _ (E.mem i _ _) _ (const1 hF hc _ _ _)
  have h4 : ∑ i, E.a σ i φ * (v (Ring.inverse G * p i G) - w (Ring.inverse G * p i G)) =
      v (Ring.inverse G) * ∑ i, E.a σ i φ * v (p i G) - ∑ i, E.a σ i φ * w (Ring.inverse G * p i G) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul v]
    ring
  have h5 : (∑ k, E.τ k (σ T ≫ φ) (σ T') * v (p k G)) = ∑ i, E.a σ i φ * v (p i G) := rfl
  rw [h4] at h3
  change v (Ring.inverse G) * (w G - v G - ∑ k, E.τ k (σ T ≫ φ) (σ T') * v (p k G)) ∈ _ at h2
  rw [h5] at h2
  have e : (1 + H) * w G * W - 1 - (∑ i, E.a σ i φ * w (Ring.inverse G * p i G) + (H - H0)) =
      ((1 + H) * (v G + (w G - v G)) * W - 1 - ((w G - v G) * v (Ring.inverse G) + H - H0)) +
      v (Ring.inverse G) * (w G - v G - ∑ i, E.a σ i φ * v (p i G)) +
      (v (Ring.inverse G) * (∑ i, E.a σ i φ * v (p i G)) - ∑ i, E.a σ i φ * w (Ring.inverse G * p i G)) := by
    ring
  rw [e]
  exact ((Fil 2).S T').add_mem (((Fil 2).S T').add_mem h1 h2) h3

end Fr

section Fr2
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

theorem frame_main {Fil : ℤ → IdF Φ.A} (hF : IsFil Φ Fil) {d : ℕ} (E : Frame Φ d) (hc : E.GrConst Fil)
    (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) (ht : Taylor Fil E p) (σ : ∀ T : C, E.D ⟶ T)
    (G : Φ.A.obj E.D) (hG : IsUnit G) (gh : ∀ T, Φ.A.obj T)
    (hg : ∀ T, gh T - (Φ.A.map (σ T)).hom G ∈ Φ.J.S T)
    (hun : ∀ T, ∀ x ∈ Φ.J.S T, IsUnit (1 + x)) :
    (∀ T, gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 ∈ Φ.J.S T) ∧
    ∀ {T T' : C} (φ : T ⟶ T'),
      (gh T' * Ring.inverse ((Φ.A.map φ).hom (gh T)) - 1 ∈ Φ.J.S T') ∧
      gh T' * Ring.inverse ((Φ.A.map φ).hom (gh T)) - 1 -
        (∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) +
          ((gh T' * Ring.inverse ((Φ.A.map (σ T')).hom G) - 1) -
            (Φ.A.map φ).hom (gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1))) ∈ (Fil 2).S T' := by
  have hy : ∀ T, IsUnit ((Φ.A.map (σ T)).hom G) := fun T => hG.map (Φ.A.map (σ T)).hom
  have hyi : ∀ T, (Φ.A.map (σ T)).hom G * Ring.inverse ((Φ.A.map (σ T)).hom G) = 1 :=
    fun T => Ring.mul_inverse_cancel _ (hy T)
  have hh : ∀ T, gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 ∈ Φ.J.S T := by
    intro T
    have e : gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 =
        (gh T - (Φ.A.map (σ T)).hom G) * Ring.inverse ((Φ.A.map (σ T)).hom G) := by
      linear_combination hyi T
    rw [e]
    exact (Φ.J.S T).mul_mem_right _ (hg T)
  refine ⟨hh, ?_⟩
  intro T T' φ
  set H := gh T' * Ring.inverse ((Φ.A.map (σ T')).hom G) - 1 with hHd
  set h0 := gh T * Ring.inverse ((Φ.A.map (σ T)).hom G) - 1 with hh0
  set H0 := (Φ.A.map φ).hom h0 with hH0d
  have hHm : H ∈ Φ.J.S T' := hh T'
  have hH0m : H0 ∈ Φ.J.S T' := Φ.J.map_mem φ (hh T)
  have e1 : gh T = (1 + h0) * (Φ.A.map (σ T)).hom G := by
    rw [hh0]; linear_combination (-gh T) * hyi T
  have e2 : gh T' = (1 + H) * (Φ.A.map (σ T')).hom G := by
    rw [hHd]; linear_combination (-gh T') * hyi T'
  have hU : IsUnit (gh T) := by
    rw [e1]; exact (hun T _ (hh T)).mul (hy T)
  have e3 : (Φ.A.map φ).hom (gh T) = (1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G := by
    rw [e1, map_mul, map_add (f := _), map_one, Φ.A.map_comp]
    rfl
  have hW : Ring.inverse ((Φ.A.map φ).hom (gh T)) * ((1 + H0) * (Φ.A.map (σ T ≫ φ)).hom G) = 1 := by
    rw [← e3]
    exact Ring.inverse_mul_cancel _ (hU.map (Φ.A.map φ).hom)
  have key := frame_core hF E hc p ht σ G hG φ hHm hH0m hW
  rw [← e2] at key
  refine ⟨?_, key⟩
  have hle : (Fil 2).S T' ≤ Φ.J.S T' := by
    rw [← hF.one]; exact hF.anti (by norm_num) T'
  have hs : ∑ i, E.a σ i φ * (Φ.A.map (σ T')).hom (Ring.inverse G * p i G) + (H - H0) ∈ Φ.J.S T' :=
    (Φ.J.S T').add_mem ((Φ.J.S T').sum_mem fun i _ => (Φ.J.S T').mul_mem_right
      ((Φ.A.map (σ T')).hom (Ring.inverse G * p i G)) (E.mem i (σ T ≫ φ) (σ T'))) ((Φ.J.S T').sub_mem hHm hH0m)
  have h6 := (Φ.J.S T').add_mem (hle key) hs
  rw [sub_add_cancel] at h6
  exact h6

end Fr2

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ), 2 ≤ s → ∀ {V V' : X.Opens} (hVV : V ≤ V') {d : ℕ} (t : Fin d → Γ(X, V)) (E : Frame (sP (KS q s {V})) d)
    (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s t E ε →
    ∀ (p : Fin d → (sP (KS q s {V})).A.obj E.D → (sP (KS q s {V})).A.obj E.D), Taylor (sFil (KS q s {V})) E p →
    ∀ (σ : ∀ T, E.D ⟶ T) (g : Γ(X, V')), IsUnit g → ∀ (ĝ : ∀ T : (KS q s {V'}).FullSubcategory, T.obj.B),
      (∀ T, Ideal.Quotient.mk T.obj.J (ĝ T) = ev T.obj (ks_in q s V' _ T.property) g) →
      ∃ h : ∀ T, (sP (KS q s {V})).A.obj T, (∀ T, h T ∈ (sP (KS q s {V})).J.S T) ∧ ∀ u : ComposableArrows (KS q s {V}).FullSubcategory 1,
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from resQ (ks_le q s hVV) (dlogC (KS q s {V'}) s ĝ) u) -
          (∑ i, E.form σ ![i] (Ring.inverse (ε (rs hVV g)) * p i (ε (rs hVV g))) u +
            (h (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h (u.obj 0)))) ∈
          (sFil (KS q s {V}) 2).S _ := by
  intro K _ _ X q s hs V V' hVV d t E ε hL p ht σ g hg ĝ hĝ
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil (KS q s {V})
  obtain ⟨hc, -, -, h4, -⟩ := hL
  have hG : IsUnit (ε (rs hVV g)) := (hg.map (rs hVV)).map ε
  let gh : ∀ T : (KS q s {V}).FullSubcategory, (sP (KS q s {V})).A.obj T :=
    fun T => ĝ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T)
  have hgl : ∀ T, gh T - ((sP (KS q s {V})).A.map (σ T)).hom (ε (rs hVV g)) ∈ (sP (KS q s {V})).J.S T := by
    intro T
    have a1 := hĝ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T)
    have a2 := h4 T (σ T) (rs hVV g)
    have a3 := GlobalTheory.CompanionTheory.GrForm.ev_res hVV T.obj (ks_in q s V' _ ((ObjectProperty.ιOfLE (ks_le q s hVV)).obj T).property)
      (ks_in q s V _ T.property) g
    exact Ideal.Quotient.eq.1 (a1.trans (a3.symm.trans a2))
  have hun : ∀ T, ∀ x ∈ (sP (KS q s {V})).J.S T, IsUnit (1 + x) := by
    intro T x hx
    have hn : IsNilpotent (show T.obj.B from x) := by
      obtain ⟨n, hn⟩ := GlobalTheory.CompanionTheory.ConeZcls.J_nil T.obj
      refine ⟨n, ?_⟩
      have h1 : (show T.obj.B from x) ^ n ∈ T.obj.J ^ n := Ideal.pow_mem_pow hx n
      rw [hn] at h1
      simpa using h1
    exact hn.isUnit_one_add
  obtain ⟨m1, m2⟩ := frame_main hF E hc p ht σ (ε (rs hVV g)) hG gh hgl hun
  refine ⟨fun T => gh T * Ring.inverse (((sP (KS q s {V})).A.map (σ T)).hom (ε (rs hVV g))) - 1, m1, fun u => ?_⟩
  obtain ⟨b1, b2⟩ := m2 (u.map (homOfLE (Fin.zero_le (Fin.last 1))))
  have b3 := plogK_sub_mem (u.obj (Fin.last 1)).obj.δ
    (show Ideal (u.obj (Fin.last 1)).obj.B from (sFil (KS q s {V}) 2).S (u.obj (Fin.last 1)))
    (s := s) (by omega) b1 (fun k hk => hF.anti (by exact_mod_cast hk) _ (hF.dp_mem k _ b1))
  have b4 := ((sFil (KS q s {V}) 2).S (u.obj (Fin.last 1))).add_mem b3 b2
  rw [sub_add_sub_cancel] at b4
  simp only [form_one]
  exact b4

end GlobalTheory.CompanionTheory.ConeLocal.DlogApprox
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalFrameTaylorClassEqStatement
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb GlobalTheory.CompanionTheory.ConeLocal
open GlobalTheory.CatH (face toLast)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_frame_taylor_class_eq : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (s : ℕ), 2 ≤ s → ∀ {V V' : X.Opens} (hVV : V ≤ V') {d : ℕ} (t : Fin d → Γ(X, V)) (E : Frame (sP (KS q s {V})) d)
    (ε : Γ(X, V) ≃+* (sP (KS q s {V})).A.obj E.D), IsLoc q s t E ε →
    ∀ (p : Fin d → (sP (KS q s {V})).A.obj E.D → (sP (KS q s {V})).A.obj E.D), Taylor (sFil (KS q s {V})) E p →
    ∀ (σ : ∀ T, E.D ⟶ T) (g : Γ(X, V')), IsUnit g → ∀ (ĝ : ∀ T : (KS q s {V'}).FullSubcategory, T.obj.B),
      (∀ T, Ideal.Quotient.mk T.obj.J (ĝ T) = ev T.obj (ks_in q s V' _ T.property) g) →
      ∃ h : ∀ T, (sP (KS q s {V})).A.obj T, (∀ T, h T ∈ (sP (KS q s {V})).J.S T) ∧ ∀ u : ComposableArrows (KS q s {V}).FullSubcategory 1,
        (show (sP (KS q s {V})).A.obj (u.obj (Fin.last 1)) from resQ (ks_le q s hVV) (dlogC (KS q s {V'}) s ĝ) u) -
          (∑ i, E.form σ ![i] (Ring.inverse (ε (rs hVV g)) * p i (ε (rs hVV g))) u +
            (h (u.obj (Fin.last 1)) - ((sP (KS q s {V})).A.map (u.map (homOfLE (Fin.zero_le (Fin.last 1))))).hom (h (u.obj 0)))) ∈
          (sFil (KS q s {V}) 2).S _ := by
  first | exact @GlobalTheory.CompanionTheory.ConeLocal.DlogApprox.main | exact GlobalTheory.CompanionTheory.ConeLocal.DlogApprox.main | (intros; apply GlobalTheory.CompanionTheory.ConeLocal.DlogApprox.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianPlaneStrongApprox
noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published
open scoped TensorProduct Quaternion

namespace GlobalTheory.CompanionTheory.PlaneSA

section Places

variable (F : Type) [Field F] [NumberField F]

abbrev Pl : Type := InfinitePlace F ⊕ HeightOneSpectrum (𝓞 F)

variable {F}


end Places

section Quat

variable {F : Type} [Field F]

variable {d β : F} {R : Type} [CommRing R] [Algebra F R]

section Top

variable [TopologicalSpace R]

end Top

end Quat

section QuatAlg

variable {F : Type} [Field F] {d β : F} {R : Type} [CommRing R] [Algebra F R]

end QuatAlg

section Adelic

variable {F : Type} [Field F] [NumberField F] {d β : F}

end Adelic

section Two

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

end Two

end GlobalTheory.CompanionTheory.PlaneSA
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwAcrFromBase
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.BetaGal

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem dd_twAcr (k : Bool) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) :
    IsDPMorphism (DD k (tw σ A) n) (DD k A n) (twAcr σ A n) := by
  cases k
  exacts [dp_twAcr A σ n, dpP_twAcr A σ n]

theorem twAcr_fromBase (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (r : (base l).Acr n) :
    twAcr σ A n (mapAcr (tw σ A).fromBase n r) = mapAcr A.fromBase n (galBase σ n r) := by
  have e : (tw σ A).fromBase = baseTw σ ≫ twMap σ A.fromBase := (fromBase_comp _ (twMap σ A.fromBase)).symm
  rw [e, mapAcr_comp, twAcr_mapAcr]
  rfl

theorem uJ_tw (k : Bool) (σ : Gal(PadicAlgCl l/K)) (A : PAlg l) (n : ℕ) (h) (x : (tw σ A).U) :
    Ideal.quotientMap (JJ k A n) (twAcr σ A n) h (uJ k (tw σ A) n x) = uJ k A n (twU σ A x) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotientMap (JJ k A n) (twAcr σ A n) h (uJ k (tw σ A) n ((tw σ A).th w)) = uJ k A n (twU σ A ((tw σ A).th w))
  rw [uJ_th, twU_th, uJ_th, Ideal.quotientMap_mk]
  exact congrArg (Ideal.Quotient.mk _) ((pdOk_twId σ A).acr_toAcr n w)

theorem map3 (P : CommRingCat.{0} ⥤ Type) {A B C D : Type} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
    (f : A →+* B) (g : B →+* C) (h : C →+* D) (e : A →+* D) (he : ∀ x, h (g (f x)) = e x) (y : P.obj (CommRingCat.of A)) :
    P.map (CommRingCat.ofHom h) (P.map (CommRingCat.ofHom g) (P.map (CommRingCat.ofHom f) y)) = P.map (CommRingCat.ofHom e) y := by
  have e' : CommRingCat.ofHom f ≫ CommRingCat.ofHom g ≫ CommRingCat.ofHom h = CommRingCat.ofHom e :=
    CommRingCat.hom_ext (RingHom.ext he)
  rw [← e', Functor.map_comp_apply, Functor.map_comp_apply]

variable {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) (σ : Gal(PadicAlgCl l/K))
  (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n : ℕ)

def etaGal (T : El (F.pt κ)) :
    (gT F κ k n).obj ((elTw σ (ptTw F κ σ hσ)).obj T) ⟶ (SH.galM F κ σ hσ k n).obj ((gT F κ k n).obj T) :=
  crHom (twAcr σ T.1.obj n) (twAcr_fromBase σ T.1.obj n) (dd_twAcr k σ T.1.obj n) fun h =>
    map3 F.Pt (twUEquiv σ T.1.obj).symm.toRingHom (uJ k (tw σ T.1.obj) n) (Ideal.quotientMap _ (twAcr σ T.1.obj n) h)
      (uJ k T.1.obj n) (fun x => (uJ_tw k σ T.1.obj n h _).trans
        (congrArg (uJ k T.1.obj n) ((twUEquiv σ T.1.obj).apply_symm_apply x))) T.2.1

theorem β_gal : ∀ {l : ℕ} [Fact l.Prime], ∀ {O : Type} [CommRing O] (F : Fn O) (κ : O →+* OC l) {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ x, galOC σ (κ x) = κ x) (k : Bool) (n j : ℕ) (x : Hc F κ k n j), β F κ k n j (galHc F κ σ hσ k n j x) = (galMor σ (ptTw F κ σ hσ) n).pull j (β F κ k n j x) := by
  intro l _ O _ F κ K σ hσ k n j x
  have h1 := pull_pull (ACris.galCris σ) (galMorC F κ σ hσ k n) (βMor F κ k n) j x
  have h2 := pull_pull (ACris.galCris σ) (βMor F κ k n) (galMor σ (ptTw F κ σ hσ) n) j x
  refine h1.trans (Eq.trans ?_ h2.symm)
  exact (cr_pull_eq ((βMor F κ k n).comp (σ'' := ACris.galCris σ) (galMor σ (ptTw F κ σ hσ) n))
    ((galMorC F κ σ hσ k n).comp (σ'' := ACris.galCris σ) (βMor F κ k n)) (etaGal F κ σ hσ k n)
    (fun f x => twAcr_mapAcr σ f.1.hom n x) (fun _ _ => rfl) j x).symm

end GlobalTheory.CompanionTheory.BetaGal
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitsPullbackEmptyProductOne
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry DividedPowers GroundTheory.PAdicHodge GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.PAlg CrystallineSemistableComparison.B

noncomputable section

namespace GlobalTheory.CompanionTheory.BetaPull

universe u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ w₁ w₂ w₃ w₄

theorem pull_square {R : Type} [CommRing R]
    {C₁ : Type u₁} [Category.{v₁} C₁] {C₂ : Type u₂} [Category.{v₂} C₂]
    {C₃ : Type u₃} [Category.{v₃} C₃] {C₄ : Type u₄} [Category.{v₄} C₄]
    {F₁ : C₁ ⥤ ModuleCat.{w₁} R} {F₂ : C₂ ⥤ ModuleCat.{w₂} R} {F₃ : C₃ ⥤ ModuleCat.{w₃} R}
    {F₄ : C₄ ⥤ ModuleCat.{w₄} R}
    (m : CH.Mor F₁ F₂ (RingHom.id R)) (b : CH.Mor F₂ F₃ (RingHom.id R))
    (b' : CH.Mor F₁ F₄ (RingHom.id R)) (q : CH.Mor F₄ F₃ (RingHom.id R))
    (η : b.G ⋙ m.G ⟶ q.G ⋙ b'.G)
    (hτ : ∀ T x, q.τ T (b'.τ (q.G.obj T) ((F₁.map (η.app T)).hom x)) = b.τ T (m.τ (b.G.obj T) x))
    (n : ℕ) (x : CH.H F₁ n) : b.pull n (m.pull n x) = q.pull n (b'.pull n x) := by
  rw [← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) m b n x).1,
    ← (CrystallineSemistableComparison.P.pull_comp (σ'' := RingHom.id R) b' q n x).1]
  exact CrystallineSemistableComparison.P.prism (m.comp b) (b'.comp q) η hτ n x

theorem pt_nat {P P' : CommRingCat.{0} ⥤ Type} (a : P ⟶ P') {B C : CommRingCat.{0}} (f : B ⟶ C)
    (g : C ⟶ C) (hg : g = 𝟙 C) (y : P.obj B) :
    P'.map g (a.app C (P.map f y)) = P'.map f (a.app B y) := by
  subst hg
  rw [P'.map_id]
  exact ConcreteCategory.congr_hom (a.naturality f) y

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l)
  (u : Fn.Map F F') (k : Bool) (n : ℕ)

theorem units_pullback_empty_product_one {B B' : Type} [CommRing B] [CommRing B'] (i : B' →+* B) (a : B'ˣ) (ha : a = 1)
    (e : Empty → Bˣ) : (1 : Bˣ) =
      (∏ j, e j) * Units.map (RingHom.id B).toMonoidHom ((1 : Bˣ) ^ 1 * (Units.map i.toMonoidHom a)⁻¹) := by
  subst ha
  change (1 : Bˣ) = (1 : Bˣ) * Units.map (RingHom.id B).toMonoidHom ((1 : Bˣ) ^ 1 * (Units.map i.toMonoidHom 1)⁻¹)
  simp

def cmpHom (T : El (F.pt κ)) :
    (gT F κ k n ⋙ (pullMorC κ u k n).G).obj T ⟶ ((pullMor (u.pt κ) n).G ⋙ (βMor F' κ k n).G).obj T where
  φ := RingHom.id _
  u := fun j => j.elim
  comm _ := rfl
  dp := (DPMorphism.id _).isDPMorphism
  hle := fun _ h => h
  pt := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
    · exact pt_nat u.u (CommRingCat.ofHom (uJ k T.1.obj n))
        (CommRingCat.ofHom (Ideal.quotientMap _ (RingHom.id _) fun _ h => h))
        (CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))) T.2.1
  hx := fun j => j.elim
  hs := units_pullback_empty_product_one _ _ rfl _
  hv := fun j => j.elim

def cmpNat : gT F κ k n ⋙ (pullMorC κ u k n).G ⟶ (pullMor (u.pt κ) n).G ⋙ (βMor F' κ k n).G where
  app T := cmpHom κ u k n T
  naturality T T' f := Thick.Hom.ext rfl (funext fun j => j.elim)

theorem beta_pull {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] {F F' : Fn O} (κ : O →+* OC l)
    (u : Fn.Map F F') (k : Bool) (n j : ℕ) (x : Hc F' κ k n j) :
    β F κ k n j (pullHc κ u k n j x) = (pullMor (u.pt κ) n).pull j (β F' κ k n j x) :=
  pull_square (pullMorC κ u k n) (βMor F κ k n) (βMor F' κ k n) (pullMor (u.pt κ) n)
    (cmpNat κ u k n) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.BetaPull
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullUnitClass
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.SiteCup

theorem pull_unit_class {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {σ : R →+* R'} (A : C ⥤ CommAlgCat.{0} R) (A' : C' ⥤ CommAlgCat.{0} R')
    (m : CH.Mor (CH.modF A) (CH.modF A') σ)
    (h : ∀ T : C', m.τ T (1 : A.obj (m.G.obj T)) = (1 : A'.obj T)) :
    m.pull 0 (CH.oneH A) = CH.oneH A' := by
  unfold CH.Mor.pull CH.oneH
  generalize_proofs p1 p2
  rw [CrystallineSemistableComparison.P.mapH_cls]
  · congr 1
    funext s
    exact h _
  · convert p2 using 2
    funext s
    exact h _

theorem smor_cup : ∀ {R R' : Type} [CommRing R] [CommRing R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C}
    {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ), (∀ {i j k : ℕ} (h : i + j = k) x y,
      m.o.pull k ((CH.mulP Φ.A).cup h x y) = (CH.mulP Φ'.A).cup h (m.o.pull i x) (m.o.pull j y)) ∧
    m.o.pull 0 (CH.oneH Φ.A) = CH.oneH Φ'.A := by
  intro R R' _ _ C C' _ _ Φ Φ' σ m
  refine ⟨?_, pull_unit_class _ _ m.o (fun T => RingHom.map_one (m.ρ T))⟩
  intro i j k h x y
  have hz : ∀ n (c : (CH.cx (CH.modF Φ.A)).X n), c ∈ (CH.cx (CH.modF Φ.A)).Z n →
      m.o.hom.f n c ∈ (CH.cx (CH.modF Φ'.A)).Z n := by
    intro n c hc
    refine LinearMap.mem_ker.mpr ?_
    rw [m.o.hom.comm, LinearMap.mem_ker.mp hc, map_zero]
  have ex := CrystallineSemistableComparison.Auxff.cls_out _ x
  generalize Quotient.out x = z at ex
  subst ex
  have ey := CrystallineSemistableComparison.Auxff.cls_out _ y
  generalize Quotient.out y = w at ey
  subst ey
  obtain ⟨a, ha⟩ := z
  obtain ⟨b, hb⟩ := w
  have cup_cls {R : Type} [CommRing R] {C : Type 1} [Category.{0} C]
      {F₁ F₂ F₃ : C ⥤ ModuleCat.{0} R} (P : CH.Pairing F₁ F₂ F₃)
      {p q n : ℕ} (h : p + q = n) (a : CH.Cn F₁ p) (b : CH.Cn F₂ q) ha hb :
      ∃ hc, P.cup h ((CH.cx F₁).cls a ha) ((CH.cx F₂).cls b hb) =
        (CH.cx F₃).cls (P.cupC h a b) hc := by
    have ce (x : CH.H F₁ p) (y : CH.H F₂ q) :
        P.cup h x y = (CrystallineSemistableComparison.Auxff.toCx P).cup h x y := by
      unfold CH.Pairing.cup CxPairing.cup
      split_ifs with hz
      · rfl
      · exact absurd ((CrystallineSemistableComparison.Auxff.toCx P).leib h _ _ |>.trans (by
          rw [show CH.d F₁ p (Quotient.out x).1 = 0 from (Quotient.out x).2,
            show CH.d F₂ q (Quotient.out y).1 = 0 from (Quotient.out y).2]; simp)) hz
    exact ⟨CrystallineSemistableComparison.Auxff.closed (CrystallineSemistableComparison.Auxff.toCx P) h a b ha hb,
      (ce _ _).trans
        (CrystallineSemistableComparison.P.cxcup_cls (CrystallineSemistableComparison.Auxff.toCx P) h a b ha hb _)⟩
  obtain ⟨hc, e⟩ := cup_cls (CH.mulP Φ.A) h a b ha hb
  obtain ⟨hc', e'⟩ := cup_cls (CH.mulP Φ'.A) h _ _ (hz _ _ ha) (hz _ _ hb)
  rw [e]
  unfold CH.Mor.pull
  rw [CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ ha), CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hb), e',
    CrystallineSemistableComparison.P.mapH_cls _ _ _ _ (hz _ _ hc)]
  congr 1
  funext s
  simp [CH.Mor.hom, CH.Mor.pullC, CH.mulP, CH.Pairing.cupC, SMor.o, CH.term, CH.modF]
  congr 1 <;> exact m.nat _ _

end GlobalTheory.CompanionTheory.SiteCup
end
