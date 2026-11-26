module

public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTranslateJetNeZero
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HermFormDiagonalEq
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsTorusOfSelfD
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.CoeffEqZeroOfOrthonormal
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelOneThetaEqSmulOfSelfDualLattice
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LevelStructureProperties
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.RiemannThetaLevelOneNeZero

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaIdealLatticeEqSumLevelTranslates
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaIdealLatticeEqSumLevelTranslates
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict.ThetaEig

theorem mem_of_eigen_mem {A W : Type} [AddCommGroup A] [AddCommGroup W] [Module ℂ W] (N : AddSubgroup A)
    [Finite (A ⧸ N)] (S : A → W →ₗ[ℂ] W) (hS : ∀ u v f, S u (S v f) = S (u + v) f)
    (H : AddSubgroup (AddChar (A ⧸ N) ℂ)) (hH : ∀ q ≠ 0, ∃ ψ ∈ H, ψ q ≠ 1)
    (f : W) (hf : ∀ u ∈ N, S u f = f) (U V : Submodule ℂ W) (hU : ∀ u, S u f ∈ U)
    (hV : ∀ ψ ∈ H, ∀ h ∈ U, (∀ u : A, S u h = ψ (u : A ⧸ N) • h) → h ∈ V) : f ∈ V := by
  haveI := Fintype.ofFinite (A ⧸ N)
  haveI := Fintype.ofFinite H
  let T : A ⧸ N → W := fun q => S q.out f
  have hT : ∀ u : A, T (u : A ⧸ N) = S u f := by
    intro u
    obtain ⟨m, hm⟩ := QuotientAddGroup.mk_out_eq_add N u
    simp only [T, hm]
    rw [← hS, hf _ m.2]
  have hST : ∀ (u : A) q, S u (T q) = T ((u : A ⧸ N) + q) := by
    intro u q
    obtain ⟨v, rfl⟩ := QuotientAddGroup.mk_surjective q
    rw [← QuotientAddGroup.mk_add, hT, hT, hS]
  have h1 : ∀ ψ : H, ∑ q, ψ.1 (-q) • T q ∈ V := by
    intro ψ
    refine hV ψ ψ.2 _ (U.sum_mem fun q _ => U.smul_mem _ (hU _)) fun u => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Fintype.sum_equiv (Equiv.addLeft (u : A ⧸ N)) _ _ fun q => ?_
    rw [map_smul, hST, smul_smul, ← AddChar.map_add_eq_mul]
    simp
  have h2 : ∀ q : A ⧸ N, q ≠ 0 → ∑ ψ : H, ψ.1 (-q) = 0 := by
    intro q hq
    obtain ⟨ψ, hψ, hne⟩ := hH (-q) (neg_ne_zero.2 hq)
    let ev : AddChar H ℂ :=
      { toFun := fun ψ => ψ.1 (-q)
        map_zero_eq_one' := by simp
        map_add_eq_mul' := fun a b => by simp }
    refine (AddChar.sum_eq_zero_iff_ne_zero (ψ := ev)).2 fun h => hne ?_
    exact DFunLike.congr_fun h ⟨ψ, hψ⟩
  have h3 : ∑ ψ : H, ∑ q, ψ.1 (-q) • T q = (Fintype.card H : ℂ) • f := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul]
    rw [Finset.sum_eq_single 0 (fun q _ hq => by rw [h2 q hq, zero_smul]) (by simp)]
    have := hT 0
    rw [hf 0 N.zero_mem, QuotientAddGroup.mk_zero] at this
    simp [this]
  have h4 : (Fintype.card H : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [← V.smul_mem_iff h4, ← h3]
  exact V.sum_mem fun ψ _ => h1 ψ

theorem mem_span_prod {Z J : Type} (φ : J → Z → ℂ) (Y : Set J) (hY : Y.Finite) : ∀ (n : ℕ)
    (F : (Fin n → Z) → ℂ), (∀ b z, (fun t => F (Function.update z b t)) ∈ Submodule.span ℂ (φ '' Y)) →
    F ∈ Submodule.span ℂ ((fun (y : Fin n → J) (z : Fin n → Z) => ∏ b, φ (y b) (z b)) '' {y | ∀ b, y b ∈ Y}) := by
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (φ '' Y)) := FiniteDimensional.span_of_finite ℂ (hY.image φ)
  intro n
  induction n with
  | zero =>
    intro F _
    have : F = F default • fun z : Fin 0 → Z => ∏ b, φ ((default : Fin 0 → J) b) (z b) := by
      funext z
      simp [Subsingleton.elim z default]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨default, fun b => b.elim0, rfl⟩)
  | succ n ih =>
    intro F hF
    obtain ⟨m, h, k, hhk, hF'⟩ := ThetaAddition.exists_sum_mul (Submodule.span ℂ (φ '' Y)) _
      (fun t (z : Fin n → Z) => F (Fin.cons t z))
      (fun z => by
        rcases isEmpty_or_nonempty Z with hZ | ⟨⟨t⟩⟩
        · rw [Subsingleton.elim (fun t => F (Fin.cons t z)) 0]; exact Submodule.zero_mem _
        · simpa only [Fin.update_cons_zero] using hF 0 (Fin.cons t z))
      (fun t => ih _ fun b z => by simpa only [Fin.cons_update] using hF b.succ (Fin.cons t z))
    have : F = ∑ i, fun z : Fin (n + 1) → Z => h i (z 0) * k i (Fin.tail z) := by
      funext z
      rw [Finset.sum_apply, ← hF', Fin.cons_self_tail]
    rw [this]
    refine Submodule.sum_mem _ fun i _ => ?_
    obtain ⟨h1, h2⟩ := hhk i
    generalize h i = a at h1
    generalize k i = c at h2
    induction h1, h2 using Submodule.span_induction₂ with
    | mem_mem a c ha hc =>
      obtain ⟨j, hj, rfl⟩ := ha
      obtain ⟨y, hy, rfl⟩ := hc
      refine Submodule.subset_span ⟨Fin.cons j y, fun b => Fin.cases hj hy b, ?_⟩
      funext z
      simp [Fin.prod_univ_succ, Fin.tail]
    | zero_left c _ => simp only [Pi.zero_apply, zero_mul]; exact Submodule.zero_mem _
    | zero_right c _ => simp only [Pi.zero_apply, mul_zero]; exact Submodule.zero_mem _
    | add_left a a' c _ _ _ h1 h2 => simp only [Pi.add_apply, add_mul]; exact Submodule.add_mem _ h1 h2
    | add_right a c c' _ _ _ h1 h2 => simp only [Pi.add_apply, mul_add]; exact Submodule.add_mem _ h1 h2
    | smul_left t a c _ _ h1 =>
      simp only [Pi.smul_apply, smul_mul_assoc]; exact Submodule.smul_mem _ t h1
    | smul_right t a c _ _ h1 =>
      simp only [Pi.smul_apply, mul_smul_comm]; exact Submodule.smul_mem _ t h1

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r}

theorem thetaSignExpEF_add_selfDual_lattice {L : Lt E r} (hL : SelfD X L) {w : E} (hw : IsIntegral ℤ w) (hw1 : w + cc w = 1)
    {u v : Fin r → E} (hu : u ∈ L) (hv : v ∈ L) :
    eps1 X w (u + v) = eps1 X w u * eps1 X w v * cexp (-(Real.pi * I * ((EF X u v : ℚ) : ℂ))) := by
  have h := (TensLat.epsW_semichar (Base.stdL_mem_Vset 1 1) hL hw hw1 (y := fun _ => u)
    ((TensLat.mem_tens_stdL L _).2 fun _ => hu)).2 (fun _ => v) ((TensLat.mem_tens_stdL L _).2 fun _ => hv)
  simp only [epsW, Finset.univ_unique, Finset.sum_singleton] at h
  exact h

theorem EF_zero_left (u : Fin r → E) : EF X 0 u = 0 := by
  rw [TensLat.EF_eq_bilin, map_zero, LinearMap.zero_apply]

theorem EF_zero_right (u : Fin r → E) : EF X u 0 = 0 := by
  rw [TensLat.EF_eq_bilin, map_zero]

theorem EF_int_of_mem {L : Lt E r} (hL : SelfD X L) {𝔐 : Ideal (𝓞 E)} {M : ℕ} (hM : M ≠ 0)
    (h𝔐 : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) {y u : Fin r → E} (hy : (M : E) • y ∈ 𝔐 • L)
    (hu : u ∈ 𝔐 • L) : ∃ k : ℤ, EF X y u = k := by
  have hM' : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  refine Submodule.smul_induction_on hu (fun a ha l hl => ?_) ?_
  · have h1 : Lev.bar a • ((M : E) • y) ∈ (Ideal.span {(M : 𝓞 E)}) • L := by
      rw [← h𝔐, mul_comm, Submodule.mul_smul]
      exact Submodule.smul_mem_smul (Lev.mem_conjI.2 (by rwa [Lev.bar_bar])) hy
    rw [Submodule.ideal_span_singleton_smul] at h1
    obtain ⟨l', hl', e⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 h1
    have h2 : Lev.bar a • y = l' := by
      refine smul_right_injective _ hM' ?_
      change (M : E) • (Lev.bar a • y) = (M : E) • l'
      rw [smul_comm, ← e, Lev.O_smul]
      simp
    have h3 := Lev.EF_smul (X := X) (Lev.bar a) y l
    rw [Lev.bar_bar, h2] at h3
    rw [← h3]
    exact (hL.2 l').1 hl' l hl
  · rintro u v ⟨k, hk⟩ ⟨k', hk'⟩
    exact ⟨k + k', by rw [Lev.EF_add_right, hk, hk', Int.cast_add]⟩

theorem mem_of_EF_int {L : Lt E r} (hL : SelfD X L) {𝔐 : Ideal (𝓞 E)} {M : ℕ} (hM : M ≠ 0)
    (h𝔐 : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) {u : Fin r → E}
    (h : ∀ y : Fin r → E, (M : E) • y ∈ 𝔐 • L → ∃ k : ℤ, EF X y u = k) : u ∈ 𝔐 • L := by
  have hM' : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM
  have h1 : ∀ b ∈ conjI 𝔐, b • ((M : E)⁻¹ • u) ∈ L := by
    intro b hb
    refine (hL.2 _).2 fun l hl => ?_
    obtain ⟨k, hk⟩ := h ((M : E)⁻¹ • (Lev.bar b • l)) (by
      rw [smul_inv_smul₀ hM']
      exact Submodule.smul_mem_smul (Lev.mem_conjI.1 hb) hl)
    rw [Lev.EF_smulE, Lev.EF_smul, Lev.bar_bar] at hk
    refine ⟨-k, ?_⟩
    rw [TensLat.EF_swap, Int.cast_neg, ← hk]
    simp [cc]
  have h2 : ∀ c ∈ 𝔐 * conjI 𝔐, c • ((M : E)⁻¹ • u) ∈ 𝔐 • L := by
    intro c hc
    refine Submodule.mul_induction_on hc (fun a ha b hb => ?_) fun a b ha hb => ?_
    · rw [mul_smul]
      exact Submodule.smul_mem_smul ha (h1 b hb)
    · rw [add_smul]
      exact add_mem ha hb
  have h3 := h2 M (h𝔐 ▸ Ideal.mem_span_singleton_self _)
  rw [Lev.O_smul] at h3
  simpa [smul_smul, hM'] using h3

variable (X) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (x : Frame X.Ψ r)

noncomputable def fockL (a : Fin g → ℂ) : ((Fin g → ℂ) → ℂ) →ₗ[ℂ] ((Fin g → ℂ) → ℂ) where
  toFun := fock X bas idx x 1 a
  map_add' f f' := by funext z; simp only [fock, Pi.add_apply, mul_add]
  map_smul' c f := by funext z; simp only [fock, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

theorem pv_add (u v : Fin r → E) : pv X idx x (u + v) = pv X idx x u + pv X idx x v := by
  unfold pv; rw [per_add]; rfl

theorem pv_zero : pv X idx x 0 = 0 := by
  unfold pv; rw [per_zero]; rfl

variable {X bas idx x}

theorem fockL_fockL (hs : IsSympl X bas) (hd : x ∈ X.dom) (u v : Fin r → E) (f : (Fin g → ℂ) → ℂ) :
    fockL X bas idx x (pv X idx x u) (fockL X bas idx x (pv X idx x v) f) =
      cexp (-(Real.pi * I * ((EF X u v : ℚ) : ℂ))) • fockL X bas idx x (pv X idx x (u + v)) f := by
  have h := (fock_laws E r X g bas idx 0 hs Even.zero x hd 1 f).1 (pv X idx x u) (pv X idx x v)
  rw [(hx_laws E r X g bas idx 0 hs Even.zero x hd).2.2.1, ← pv_add] at h
  simp only [Nat.cast_one, _root_.one_mul, ofReal_ratCast] at h
  exact h

theorem exists_span_one (hs : IsSympl X bas) (hd : x ∈ X.dom) {w : E} (hw : IsIntegral ℤ w)
    (hw1 : w + cc w = 1) {L : Lt E r} (hL : SelfD X L) {𝔐 : Ideal (𝓞 E)} {M : ℕ} (hM : M ≠ 0)
    (h𝔐 : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) {θ : (Fin g → ℂ) → ℂ} (hθ : IsTheta1 X bas idx w x L θ)
    (h0 : θ ≠ 0) : ∃ Y : Set (Fin r → E), Y.Finite ∧ (∀ y ∈ Y, (M : E) • y ∈ 𝔐 • L) ∧
      ∀ f, IsTheta1 X bas idx w x (𝔐 • L) f →
        f ∈ Submodule.span ℂ ((fun y => fock X bas idx x 1 (pv X idx x y) θ) '' Y) := by
  let N : AddSubgroup L := (𝔐 • L).toAddSubgroup.comap L.subtype.toAddMonoidHom
  have hN : ∀ u : L, u ∈ N ↔ (u : Fin r → E) ∈ 𝔐 • L := fun _ => Iff.rfl
  haveI : Finite (L ⧸ N) := by
    haveI : Module.Finite (𝓞 E) L := .of_fg hL.1
    haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
    haveI : AddGroup.FG L := Module.Finite.iff_addGroup_fg.1 inferInstance
    refine AddCommGroup.finite_of_fg_isAddTorsion _ fun q => ?_
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨M, Nat.pos_of_ne_zero hM, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, hN]
    have : (M : 𝓞 E) ∈ 𝔐 := Ideal.mul_le_left (h𝔐 ▸ Ideal.mem_span_singleton_self (M : 𝓞 E))
    simpa [Nat.cast_smul_eq_nsmul] using Submodule.smul_mem_smul this u.2
  let e : (Fin r → E) → (Fin r → E) → ℂ := fun y u => cexp (2 * Real.pi * I * ((EF X y u : ℚ) : ℂ))
  have he1 : ∀ y u, e y u = 1 ↔ ∃ k : ℤ, EF X y u = k := by
    intro y u
    rw [Complex.exp_eq_one_iff]
    refine exists_congr fun k => ?_
    rw [mul_comm, mul_left_inj' Complex.two_pi_I_ne_zero]
    exact_mod_cast Iff.rfl
  have hel : ∀ y y' u, e (y + y') u = e y u * e y' u := by
    intro y y' u
    simp only [e, Lev.EF_add_left, Rat.cast_add, mul_add, Complex.exp_add]
  have her : ∀ y u u', e y (u + u') = e y u * e y u' := by
    intro y u u'
    simp only [e, Lev.EF_add_right, Rat.cast_add, mul_add, Complex.exp_add]
  have hen : ∀ y u, e (-y) u = e y (-u) := by
    intro y u
    simp only [e, TensLat.EF_eq_bilin, map_neg, LinearMap.neg_apply]
  let H : AddSubgroup (AddChar (L ⧸ N) ℂ) :=
    { carrier := {ψ | ∃ y : Fin r → E, (M : E) • y ∈ 𝔐 • L ∧ ∀ u : L, ψ (u : L ⧸ N) = e y u}
      zero_mem' := ⟨0, by simp, fun u => by simp [e, EF_zero_left]⟩
      add_mem' := by
        rintro ψ ψ' ⟨y, hy, h⟩ ⟨y', hy', h'⟩
        exact ⟨y + y', by rw [smul_add]; exact add_mem hy hy', fun u => by
          rw [AddChar.add_apply, h, h', hel]⟩
      neg_mem' := by
        rintro ψ ⟨y, hy, h⟩
        exact ⟨-y, by rw [smul_neg]; exact neg_mem hy, fun u => by
          rw [AddChar.neg_apply, ← QuotientAddGroup.mk_neg, h, hen]; rfl⟩ }
  have hH : ∀ q ≠ 0, ∃ ψ ∈ H, ψ q ≠ 1 := by
    intro q hq
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective q
    by_contra hcon
    push Not at hcon
    refine hq ((QuotientAddGroup.eq_zero_iff _).2 (mem_of_EF_int hL hM h𝔐 fun y hy => ?_))
    let χ : L →+ Additive ℂ :=
      { toFun := fun u => Additive.ofMul (e y u)
        map_zero' := by simp [e, EF_zero_right]
        map_add' := fun a b => by rw [Submodule.coe_add, her, ofMul_mul] }
    have hχ : N ≤ χ.ker := fun a ha =>
      congrArg Additive.ofMul ((he1 y a).2 (EF_int_of_mem hL hM h𝔐 hy ha))
    exact (he1 y u).1
      (hcon (AddChar.toAddMonoidHomEquiv.symm (QuotientAddGroup.lift N χ hχ)) ⟨y, hy, fun _ => rfl⟩)
  choose yy hyy hyy' using fun ψ : H => ψ.2
  refine ⟨Set.range yy, Set.finite_range _, by rintro _ ⟨ψ, rfl⟩; exact hyy ψ, fun f hf => ?_⟩
  let U : Submodule ℂ ((Fin g → ℂ) → ℂ) :=
    { carrier := {f | Differentiable ℂ f}
      zero_mem' := differentiable_const 0
      add_mem' := fun h h' => h.add h'
      smul_mem' := fun c _ h => h.const_smul c }
  have hdiff := fun f => (fock_laws E r X g bas idx 0 hs Even.zero x hd 1 f).2.2.2.1
  refine mem_of_eigen_mem N (fun u : L => eps1 X w u • fockL X bas idx x (pv X idx x u)) (fun u v f => ?_) H hH
    f (fun u hu => hf.2 u hu) U _ (fun u => U.smul_mem _ (hdiff f hf.1 _)) fun ψ hψ h hU hh => ?_
  · obtain ⟨k, hk⟩ := (hL.2 u).1 u.2 v v.2
    simp only [LinearMap.smul_apply, map_smul, fockL_fockL hs hd, smul_smul, Submodule.coe_add,
      thetaSignExpEF_add_selfDual_lattice hL hw hw1 u.2 v.2]
    congr 1
    ring
  · set y := yy ⟨ψ, hψ⟩
    have h1 : IsTheta1 X bas idx w x L (fockL X bas idx x (pv X idx x (-y)) h) := by
      refine ⟨hdiff h hU _, fun u hu => ?_⟩
      have h2 := congrArg (fockL X bas idx x (pv X idx x (-y))) (hh ⟨u, hu⟩)
      rw [hyy' ⟨ψ, hψ⟩, LinearMap.smul_apply, map_smul, map_smul, fockL_fockL hs hd, add_comm] at h2
      change eps1 X w u • fockL X bas idx x (pv X idx x u) _ = _
      refine smul_right_injective _ (show e y u ≠ 0 from Complex.exp_ne_zero _) ?_
      simp only []
      rw [← h2, fockL_fockL hs hd, smul_comm (e y u), smul_smul (e y u), ← Complex.exp_add]
      have e1 : EF X u (-y) = -EF X y u * -1 := by
        rw [← TensLat.EF_swap]; simp only [TensLat.EF_eq_bilin, map_neg, mul_neg, _root_.mul_one]
      have e2 : EF X (-y) u = -EF X y u := by simp only [TensLat.EF_eq_bilin, map_neg, LinearMap.neg_apply]
      rw [e1, e2]
      congr 3
      push_cast
      ring
    obtain ⟨a, ha⟩ := ThetaOne.exists_eq_smul_of_isTheta1 E r X g bas idx 0 hs Even.zero w hw hw1 L hL x hd
      _ θ h1 hθ h0
    have h3 := congrArg (fockL X bas idx x (pv X idx x y)) ha
    have h4 : EF X y (-y) = 0 := by
      have := TensLat.EF_swap X y y
      simp only [TensLat.EF_eq_bilin, map_neg] at this ⊢
      linarith
    have h5 : fockL X bas idx x 0 h = h := (fock_laws E r X g bas idx 0 hs Even.zero x hd 1 h).2.1
    rw [fockL_fockL hs hd, h4, add_neg_cancel, pv_zero, h5, map_smul] at h3
    simp only [Rat.cast_zero, mul_zero, neg_zero, Complex.exp_zero, one_smul] at h3
    rw [h3]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨y, ⟨_, rfl⟩, rfl⟩)

theorem theta_eq_sum_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ F : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ F → (∀ u : Matrix (Fin n) (Fin r) E, (∀ b, u b ∈ 𝔐 • L) → ∀ z, F z = epsW X (w : E) u * cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (u b)) (pv X idx x (u b)))) * F (fun b => z b + pv X idx x (u b))) → ∃ (s : Finset (Matrix (Fin n) (Fin r) E)) (cf : Matrix (Fin n) (Fin r) E → ℂ), (∀ y ∈ s, ∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ z, F z = ∑ y ∈ s, cf y * (κ * thA X bas idx (heisG X bas y v) x z) := by
  intro E _ _ _ r X g q0 _ bas idx n hs hn w hw L hL x hd _ t _ _ 𝔐 M hM h𝔐 v hv θ κ hθ hmean hκ F hF hlaw
  have h0 : θ ≠ 0 := by
    rintro rfl
    obtain ⟨_, _, -, -, h⟩ := hmean
    simp at h
  obtain ⟨Y, hY, hYM, hspan⟩ := exists_span_one hs hd w.2 hw hL hM.pos.ne' h𝔐 hθ h0
  have h1 := mem_span_prod (fun y => fock X bas idx x 1 (pv X idx x y) θ) Y hY n F fun b z => by
    refine hspan _ ⟨hF.comp (fun s => (hasFDerivAt_update z s).differentiableAt), fun u hu => ?_⟩
    funext s
    have h := hlaw (Pi.single b u) (fun b' => by
      rcases eq_or_ne b' b with rfl | hb
      · simpa using hu
      · simp [Pi.single_eq_of_ne hb]) (Function.update z b s)
    rw [h]
    simp only [Pi.smul_apply, smul_eq_mul, fock, epsW, eps1]
    rw [Finset.sum_eq_single b, Finset.sum_eq_single b]
    · simp only [Pi.single_eq_same, Function.update_self, Nat.cast_one, _root_.one_mul, _root_.mul_assoc]
      congr 3
      funext b'
      rcases eq_or_ne b' b with rfl | hb
      · simp
      · simp [Pi.single_eq_of_ne hb, pv_zero, hb]
    · intro b' _ hb
      simp [Pi.single_eq_of_ne hb, pv_zero, fock_hx_zero_right]
    · simp
    · intro b' _ hb
      simp [Pi.single_eq_of_ne hb, EF_zero_left]
    · simp
  obtain ⟨l, hl, e⟩ := (Finsupp.mem_span_image_iff_linearCombination ℂ).1 h1
  refine ⟨l.support, l, fun y hy b => hYM _ (hl hy b), fun z => ?_⟩
  rw [← e, Finsupp.linearCombination_apply, Finsupp.sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Pi.smul_apply, smul_eq_mul,
    (fock_laws E r X g bas idx n hs hn x hd 1 θ).2.2.2.2 (fun _ => θ) κ v hv.1 hκ y z]

end GlobalTheory.Dict.ThetaEig
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ThetaIdealLatticeEqSumLevelTranslatesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_ideal_lattice_eq_sum_level_translates : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ F : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ F → (∀ u : Matrix (Fin n) (Fin r) E, (∀ b, u b ∈ 𝔐 • L) → ∀ z, F z = epsW X (w : E) u * cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (u b)) (pv X idx x (u b)))) * F (fun b => z b + pv X idx x (u b))) → ∃ (s : Finset (Matrix (Fin n) (Fin r) E)) (cf : Matrix (Fin n) (Fin r) E → ℂ), (∀ y ∈ s, ∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ z, F z = ∑ y ∈ s, cf y * (κ * thA X bas idx (heisG X bas y v) x z) := by
  first | exact @GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates | exact GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates | (intros; apply GlobalTheory.Dict.ThetaEig.theta_eq_sum_translates <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaSublatticeJetNeZero
section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaSublatticeJetNeZero
namespace GlobalTheory.Dict.SubJet

noncomputable section

section General

open Complex ReciprocityTheory.ChartRestriction.G.I2
open scoped Classical

theorem exists_poly_scale {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (P : MvPolynomial σ ℂ) {s : ℂ}
    (hs : s ≠ 0) : ∃ P' : MvPolynomial σ ℂ, P'.support = P.support ∧
      ∀ (u : σ → W) (F : W → ℂ) (x : W), ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun l => s • u l) F x = ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P' u F x := by
  let P' : MvPolynomial σ ℂ := ∑ m ∈ P.support,
    MvPolynomial.monomial m (s ^ Multiset.card (Finsupp.toMultiset m) * P.coeff m)
  have hc : ∀ m, P'.coeff m = s ^ Multiset.card (Finsupp.toMultiset m) * P.coeff m := by
    intro m
    simp only [P', MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial, Finset.sum_ite_eq']
    split_ifs with h
    · rfl
    · rw [MvPolynomial.notMem_support_iff.1 h, mul_zero]
  have hsup : P'.support = P.support := by
    ext m
    simp only [MvPolynomial.mem_support_iff, hc, ne_eq, mul_eq_zero, pow_ne_zero _ hs, false_or]
  refine ⟨P', hsup, fun u F x => ?_⟩
  unfold ReciprocityTheory.ChartRestriction.G.I2.polyDeriv
  rw [hsup]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [ContinuousMultilinearMap.map_smul_univ _ (fun _ => s), Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, smul_eq_mul, hc]
  ring

theorem exists_jet_of_periods {ι A : Type} [Fintype ι] [AddCommGroup A] (p : A →+ EuclideanSpace ℂ ι)
    (hp : Function.Injective p) (b : Module.Basis (Fin (2 * Fintype.card ι)) ℝ (EuclideanSpace ℂ ι))
    (hb : ∀ y, y ∈ lat b ↔ ∃ a, p a = y) (hint : ∀ a a', ∃ k : ℤ, (Hf (p a) (p a')).im = k)
    (hperf : ∀ φ : A →+ ℤ, ∃ a, ∀ a', (φ a' : ℝ) = (Hf (p a) (p a')).im) (Q : A → ℝ)
    (hQ : ∀ a a', ∃ k : ℤ, Q (a + a') = Q a + Q a' - (Hf (p a) (p a')).im + 2 * k)
    (q : ℕ) (P : MvPolynomial ι ℂ) (hP : P ≠ 0) (hq : 3 * P.totalDegree + 2 ≤ q) {s : ℂ} (hs : s ≠ 0) :
    ∃ G : EuclideanSpace ℂ ι → ℂ, Differentiable ℂ G ∧
      (∀ a v, G (v + p a) = cexp (Real.pi * I * (q * Q a : ℝ)) *
        cexp (q * Real.pi * Hf v (p a) + q * Real.pi * Hf (p a) (p a) / 2) * G v) ∧
      ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (fun i => s • EuclideanSpace.single i 1) G 0 ≠ 0 := by
  let Y : GT ι :=
    { b := b
      integral := fun x y hx hy => by
        obtain ⟨a, rfl⟩ := (hb x).1 hx
        obtain ⟨a', rfl⟩ := (hb y).1 hy
        exact hint a a'
      perfect := fun φ => by
        obtain ⟨a, ha⟩ := hperf (φ.comp (p.codRestrict (lat b) fun a => (hb _).2 ⟨a, rfl⟩))
        refine ⟨p a, (hb _).2 ⟨a, rfl⟩, ?_⟩
        rintro ⟨y, hy⟩
        obtain ⟨a', rfl⟩ := (hb y).1 hy
        exact ha a'
      ka := fun y => cexp (Real.pi * I * Q (Function.invFun p y))
      ka_abs := fun x _ => by
        rw [Complex.norm_exp]
        simp }
  have hka : ∀ a, Y.ka (p a) = cexp (Real.pi * I * Q a) := fun a => by
    simp only [Y, Function.leftInverse_invFun hp a]
  have hC : FPw.Coc Y 1 := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := (hb x).1 hx
    obtain ⟨a', rfl⟩ := (hb y).1 hy
    obtain ⟨k, hk⟩ := hQ a a'
    rw [← map_add (f := _), hka, hka, hka, hk, ← Complex.exp_add, ← Complex.exp_add,
      Complex.exp_eq_exp_iff_exists_int]
    refine ⟨k, ?_⟩
    push_cast
    ring
  obtain ⟨θ, hθ, h0⟩ := GlobalTheory.ThetaExist.exists_sec_ne_zero Y hC
  obtain ⟨P', hsup, hP'⟩ := exists_poly_scale (W := EuclideanSpace ℂ ι) P hs
  have hne : P' ≠ 0 := by
    rwa [Ne, ← MvPolynomial.support_eq_empty, hsup, MvPolynomial.support_eq_empty]
  have hdeg : P'.totalDegree ≤ P.totalDegree := by
    unfold MvPolynomial.totalDegree
    rw [hsup]
  obtain ⟨G, hG, hlaw, hG0⟩ := exists_section_jet_ne_zero Y θ hθ h0 _ q hq P' hne hdeg
  refine ⟨G, hG, fun a v => ?_, by rw [hP']; exact hG0⟩
  rw [hlaw (p a) ((hb _).2 ⟨a, rfl⟩) v, hka, ← Complex.exp_nat_mul]
  congr 3
  push_cast
  ring

def colEquiv {K : Type} [Fintype K] {n g : ℕ} (e : K ≃ Fin n × Fin g) (s : ℂ) (hs : s ≠ 0) :
    (Fin n → Fin g → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ K where
  toFun z := WithLp.toLp 2 fun i => s * z (e i).1 (e i).2
  invFun y k j := s⁻¹ * y (e.symm (k, j))
  map_add' z z' := by ext i; simp [mul_add]
  map_smul' c z := by ext i; simp [mul_left_comm]
  left_inv z := by funext k j; simp [hs]
  right_inv y := by ext i; simp [hs]

theorem colEquiv_apply {K : Type} [Fintype K] {n g : ℕ} (e : K ≃ Fin n × Fin g) (s : ℂ) (hs : s ≠ 0)
    (z : Fin n → Fin g → ℂ) (i : K) : colEquiv e s hs z i = s * z (e i).1 (e i).2 := rfl

theorem exists_basis_cols {K κ : Type} [Fintype K] [Fintype κ] {n g : ℕ}
    (Φ : (Fin n → Fin g → ℂ) ≃ₗ[ℂ] EuclideanSpace ℂ K) (b₀ : Module.Basis κ ℝ (Fin g → ℂ)) :
    ∃ b : Module.Basis (Fin (2 * Fintype.card K)) ℝ (EuclideanSpace ℂ K),
      ∀ z, Φ z ∈ lat b ↔ ∀ k, z k ∈ Submodule.span ℤ (Set.range b₀) := by
  let b₁ := (Pi.basis fun _ : Fin n => b₀).map (Φ.restrictScalars ℝ)
  have hcard : Fintype.card (Σ _ : Fin n, κ) = Fintype.card (Fin (2 * Fintype.card K)) := by
    rw [← Module.finrank_eq_card_basis b₁, finrank_real_of_complex]
    simp
  refine ⟨b₁.reindex (Fintype.equivOfCardEq hcard), fun z => ?_⟩
  rw [lat, Module.Basis.range_reindex]
  simp only [Module.Basis.mem_span_iff_repr_mem, b₁, Module.Basis.map_repr, Sigma.forall]
  simp

end General

section Arith

open NumberField ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr GlobalTheory.SW GlobalTheory.SW.TensLat

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g : ℕ} {X : Data E r} {L : Lt E r}
  {𝔐 : Ideal (𝓞 E)} {M : ℕ}

theorem EF_add_left (u u' v : Fin r → E) : EF X (u + u') v = EF X u v + EF X u' v := by
  simp only [EF_eq_bilin, map_add (f := _), LinearMap.add_apply]

theorem EF_add_right (u v v' : Fin r → E) : EF X u (v + v') = EF X u v + EF X u v' := by
  simp only [EF_eq_bilin, map_add (f := _)]

theorem EF_ratSmul_left (c : ℚ) (u v : Fin r → E) : EF X ((c : E) • u) v = c * EF X u v := by
  rw [Rat.cast_smul_eq_qsmul, EF_eq_bilin, EF_eq_bilin, map_smul, LinearMap.smul_apply, smul_eq_mul]

theorem EF_mem_mul (hL : SelfD X L) (hM : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) {u v : Fin r → E}
    (hu : u ∈ 𝔐 • L) (hv : v ∈ 𝔐 • L) : ∃ k : ℤ, EF X u v = M * k := by
  refine Submodule.smul_induction_on hu (fun a ha x hx => ?_) ?_
  · refine Submodule.smul_induction_on hv (fun b hb y hy => ?_) ?_
    · let b' : 𝓞 E := ⟨cc (b : E), Base.isIntegral_cc b.isIntegral_coe⟩
      have h1 : a * b' ∈ Ideal.span {(M : 𝓞 E)} :=
        hM ▸ Ideal.mul_mem_mul ha (Ideal.subset_span ⟨b, hb, rfl⟩)
      obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 h1
      have hc' : (c : E) * M = a * cc (b : E) := by
        have := congrArg (algebraMap (𝓞 E) E) hc
        rw [map_mul, map_mul, map_natCast] at this
        exact this
      obtain ⟨k, hk⟩ := (hL.2 _).1 (L.smul_mem c hx) y hy
      refine ⟨k, ?_⟩
      have h2 : EF X (cc (b : E) • (a : E) • x) y = EF X ((a : E) • x) ((b : E) • y) := by
        rw [EF_smul]
        simp [cc]
      change EF X ((a : E) • x) ((b : E) • y) = _
      rw [← h2, ← hk, ← EF_ratSmul_left, smul_smul, mul_comm, ← hc']
      congr 1
      change _ = _ • (c : E) • x
      rw [smul_smul, mul_comm, Rat.cast_natCast]
    · rintro y y' ⟨k, hk⟩ ⟨k', hk'⟩
      exact ⟨k + k', by rw [EF_add_right, hk, hk']; push_cast; ring⟩
  · rintro y y' ⟨k, hk⟩ ⟨k', hk'⟩
    exact ⟨k + k', by rw [EF_add_left, hk, hk']; push_cast; ring⟩

theorem mem_of_EF_mem_mul (hL : SelfD X L) (hM0 : M ≠ 0) (hM : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)})
    {u : Fin r → E} (hu : ∀ v ∈ 𝔐 • L, ∃ k : ℤ, EF X u v = M * k) : u ∈ 𝔐 • L := by
  have hQ : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM0
  have h1 : ∀ c ∈ conjI 𝔐, c • (((M : ℚ)⁻¹ : ℚ) : E) • u ∈ L := by
    intro c hc
    induction hc using Submodule.span_induction with
    | mem c hc =>
      obtain ⟨b, hb, hcb⟩ := hc
      refine (hL.2 _).2 fun y hy => ?_
      obtain ⟨k, hk⟩ := hu _ (Submodule.smul_mem_smul hb hy)
      refine ⟨k, ?_⟩
      change EF X ((c : E) • _) y = _
      change EF X u ((b : E) • y) = _ at hk
      have h3 : cc (cc (b : E)) = b := by simp [cc]
      rw [EF_smul, EF_ratSmul_left, hcb, h3, hk, inv_mul_cancel_left₀ hQ]
    | zero => rw [zero_smul]; exact L.zero_mem
    | add a b _ _ ha hb => rw [add_smul]; exact L.add_mem ha hb
    | smul a b _ hb => rw [smul_assoc]; exact L.smul_mem a hb
  have h2 : ∀ z ∈ 𝔐 * conjI 𝔐, z • (((M : ℚ)⁻¹ : ℚ) : E) • u ∈ 𝔐 • L := by
    intro z hz
    refine Submodule.mul_induction_on hz (fun a ha c hc => ?_) fun a b ha hb => ?_
    · rw [mul_smul]
      exact Submodule.smul_mem_smul ha (h1 c hc)
    · rw [add_smul]
      exact Submodule.add_mem _ ha hb
  have h3 := h2 M (hM ▸ Ideal.mem_span_singleton_self _)
  have hE : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM0
  rwa [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E, Rat.cast_inv, Rat.cast_natCast,
    smul_inv_smul₀ hE] at h3

theorem exists_EF_eq {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (hs : IsSympl X bas) (hL : SelfD X L) (hM0 : M ≠ 0)
    (hM : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) (φ : (𝔐 • L : Lt E r) →+ ℤ) :
    ∃ u ∈ 𝔐 • L, ∀ v : (𝔐 • L : Lt E r), EF X u v = M * φ v := by
  obtain ⟨F, hF⟩ := (Module.Baer.of_divisible ℚ).extension_property_addMonoidHom
    (𝔐 • L : Lt E r).subtype.toAddMonoidHom (𝔐 • L : Lt E r).injective_subtype
    ((AddMonoidHom.mulLeft (M : ℚ)).comp ((Int.castAddHom ℚ).comp φ))
  let u := (LinearMap.BilinForm.toDual _ (SelfTorus.nondeg hs)).symm F.toRatLinearMap
  have hu (v : (𝔐 • L : Lt E r)) : EF X u v = M * φ v :=
    (LinearMap.BilinForm.apply_toDual_symm_apply (hB := SelfTorus.nondeg hs) F.toRatLinearMap v).trans
      (DFunLike.congr_fun hF v)
  exact ⟨u, mem_of_EF_mem_mul hL hM0 hM fun y hy => ⟨_, hu ⟨y, hy⟩⟩, hu⟩

theorem EF_quad {w : E} (hw : w + cc w = 1) (u v : Fin r → E) :
    EF X (u + v) (w • (u + v)) = EF X u (w • u) + EF X v (w • v) - EF X u v + 2 * EF X u (w • v) := by
  have h2 : EF X v (w • u) = -EF X u (cc w • v) := by rw [EF_swap, EF_smul]
  have h3 : EF X u (w • v) + EF X u (cc w • v) = EF X u v := by
    rw [← EF_add_right, ← add_smul, hw, one_smul]
  simp only [smul_add, EF_add_left, EF_add_right]
  linarith

theorem exists_basis_smul {κ : Type} [Fintype κ] (pl : (Fin r → E) →+ (Fin g → ℂ))
    (b₀ : Module.Basis κ ℝ (Fin g → ℂ))
    (hb₀ : ∀ z, z ∈ Submodule.span ℤ (Set.range b₀) ↔ ∃ u ∈ L, z = pl u) (hM0 : M ≠ 0)
    (hM : 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)}) :
    ∃ b₁ : Module.Basis κ ℝ (Fin g → ℂ), ∀ z, z ∈ Submodule.span ℤ (Set.range b₁) ↔ ∃ u ∈ 𝔐 • L, z = pl u := by
  have hle : Ideal.span {(M : 𝓞 E)} ≤ 𝔐 := by
    rw [← hM]
    exact Ideal.mul_le.2 fun a ha b _ => 𝔐.mul_mem_right b ha
  have hMm : (M : 𝓞 E) ∈ 𝔐 := (Ideal.span_singleton_le_iff_mem _).1 hle
  let N : Submodule ℤ (Fin g → ℂ) := ((𝔐 • L : Lt E r).toAddSubgroup.map pl).toIntSubmodule
  have hN : ∀ z, z ∈ N ↔ ∃ u ∈ 𝔐 • L, z = pl u := fun z =>
    ⟨fun ⟨u, hu, h⟩ => ⟨u, hu, h.symm⟩, fun ⟨u, hu, h⟩ => ⟨u, hu, h.symm⟩⟩
  obtain ⟨b₁, hb₁⟩ := TensorLat.exists_basis_span_eq_of_commensurable b₀ N (M := M) (by omega)
    (fun z hz => by
      obtain ⟨u, hu, rfl⟩ := (hb₀ z).1 hz
      refine (hN _).2 ⟨M • u, ?_, by rw [map_nsmul]⟩
      rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      exact Submodule.smul_mem_smul hMm hu)
    (fun z hz => by
      obtain ⟨u, hu, rfl⟩ := (hN z).1 hz
      exact (hb₀ _).2 ⟨M • u, nsmul_mem (Submodule.smul_le_right hu) M, by rw [map_nsmul]⟩)
  exact ⟨b₁, fun z => by rw [hb₁, hN]⟩

end Arith

end

end GlobalTheory.Dict.SubJet

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict


open GlobalTheory.Dict.SubJet in
theorem GlobalTheory.Dict.exists_theta_sublattice_jet_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), P ≠ 0 → 3 * P.totalDegree + 2 ≤ M → ∃ F : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ F ∧ (∀ u : Matrix (Fin n) (Fin r) E, (∀ b, u b ∈ 𝔐 • L) → ∀ z, F z = epsW X (w : E) u * cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (u b)) (pv X idx x (u b)))) * F (fun b => z b + pv X idx x (u b))) ∧ I2.polyDeriv P (letterDir X hr idx) F 0 ≠ 0 := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn w hw L hL x hxd ho t ht hc 𝔐 M _ hM P hP hdeg
  have hM0 : M ≠ 0 := by omega
  have hMR : (M : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hM0
  obtain ⟨-, -, him, -, -, hinj, -⟩ := hx_laws E r X g bas idx n hs hn x hxd
  obtain ⟨hdiag, -⟩ := hx_ortho E r X g bas idx hs x hxd ho
  obtain ⟨T, ψ, -, -, -, hT, -⟩ := exists_torus_of_selfD E r X g bas idx hs w hw L hL x hxd ho t ht hc
  let pl : (Fin r → E) →+ (Fin g → ℂ) := AddMonoidHom.mk' (pv X idx x) fun u v => by
    simp only [pv, per_add]
    rfl
  have hpl : ∀ u, pl u = pv X idx x u := fun _ => rfl
  have hb₀ : ∀ z, z ∈ Submodule.span ℤ (Set.range (T.b.map (ψ.symm.restrictScalars ℝ))) ↔
      ∃ u ∈ L, z = pl u := by
    intro z
    have h1 : z ∈ Submodule.span ℤ (Set.range (T.b.map (ψ.symm.restrictScalars ℝ))) ↔ ψ z ∈ T.L := by
      simp only [Module.Basis.mem_span_iff_repr_mem, Module.Basis.map_repr]
      rfl
    rw [h1, hT]
    simp only [ψ.injective.eq_iff, hpl]
  obtain ⟨b₁, hb₁⟩ := exists_basis_smul pl _ hb₀ hM0 hM
  let s : ℂ := (Real.sqrt (t / M) : ℝ)
  have htM : 0 < t / M := by positivity
  have hs0 : s ≠ 0 := ofReal_ne_zero.2 (Real.sqrt_pos.2 htM).ne'
  have hss : (M : ℂ) * (s * s) = t := by
    simp only [s]
    rw [← ofReal_mul, Real.mul_self_sqrt htM.le]
    push_cast
    field_simp
  let e : Harm.Var X.Ψ q0 X.p0 (Fin n) ≃ Fin n × Fin g :=
    ((Equiv.prodAssoc _ _ _).symm.trans (Equiv.prodComm _ _)).trans
      (Equiv.prodCongr (Equiv.refl _) ((rowOf X hr).trans idx.symm))
  let Φ := colEquiv e s hs0
  have hH : ∀ z z', (M : ℂ) * I2.Hf (Φ z) (Φ z') = ∑ b, hx X bas idx x (z b) (z' b) := by
    intro z z'
    simp only [hdiag, hc]
    rw [I2.Hf, Finset.mul_sum, ← Finset.sum_product', Finset.univ_product_univ]
    refine Fintype.sum_equiv e _ _ fun i => ?_
    rw [colEquiv_apply, colEquiv_apply, map_mul, conj_ofReal, ← hss]
    ring
  obtain ⟨b, hb⟩ := exists_basis_cols Φ b₁
  let p : (Fin n → (𝔐 • L : Lt E r)) →+ EuclideanSpace ℂ (Harm.Var X.Ψ q0 X.p0 (Fin n)) :=
    AddMonoidHom.mk' (fun a => Φ fun k => pl (a k)) fun a a' => by
      rw [← map_add (f := _)]
      congr 1
      funext k
      exact map_add pl _ _
  have hp : ∀ a, p a = Φ fun k => pv X idx x (a k) := fun _ => rfl
  have hI : ∀ a a', (I2.Hf (p a) (p a')).im = ((∑ k, EF X (a k) (a' k) : ℚ) : ℝ) / M := by
    intro a a'
    have h := congrArg Complex.im (hH (fun k => pv X idx x (a k)) fun k => pv X idx x (a' k))
    rw [← ofReal_natCast, im_ofReal_mul, im_sum] at h
    simp only [him] at h
    rw [hp, hp, eq_div_iff hMR, mul_comm, h, Rat.cast_sum]
  have hZ : ∀ u v : Fin n → Fin r → E, (∀ k, u k ∈ 𝔐 • L) → (∀ k, v k ∈ 𝔐 • L) →
      ∃ m : ℤ, ∑ k, EF X (u k) (v k) = M * m := by
    intro u v hu hv
    choose m hm using fun k => EF_mem_mul hL hM (hu k) (hv k)
    exact ⟨∑ k, m k, by simp only [hm, Int.cast_sum, Finset.mul_sum]⟩
  obtain ⟨G, hG, hlaw, hG0⟩ := exists_jet_of_periods p
    (fun a a' h => funext fun k => Subtype.ext (hinj (congrFun (Φ.injective h) k))) b
    (fun y => by
      obtain ⟨z, rfl⟩ := Φ.surjective y
      simp only [hb, hb₁]
      constructor
      · intro h
        choose u hu hu' using h
        exact ⟨fun k => ⟨u k, hu k⟩, congrArg Φ (funext fun k => (hu' k).symm)⟩
      · rintro ⟨a, ha⟩ k
        exact ⟨a k, (a k).2, (congrFun (Φ.injective ha) k).symm⟩)
    (fun a a' => by
      obtain ⟨m, hm⟩ := hZ _ _ (fun k => (a k).2) fun k => (a' k).2
      refine ⟨m, ?_⟩
      rw [hI, hm]
      push_cast
      field_simp)
    (fun φ => by
      choose u hu hu' using fun k => exists_EF_eq hs hL hM0 hM
        (φ.comp (AddMonoidHom.single (fun _ : Fin n => (𝔐 • L : Lt E r)) k))
      refine ⟨fun k => ⟨u k, hu k⟩, fun a' => ?_⟩
      rw [hI]
      simp only [hu']
      set_option synthInstance.maxHeartbeats 100000 in
        conv_lhs => rw [← Finset.univ_sum_single a', map_sum]
      rw [← Finset.mul_sum]
      push_cast
      field_simp
      rfl)
    (fun a => ((∑ k, EF X (a k) ((w : E) • (a k : Fin r → E)) : ℚ) : ℝ) / M)
    (fun a a' => by
      obtain ⟨m, hm⟩ := hZ _ (fun k => (w : E) • (a' k : Fin r → E)) (fun k => (a k).2)
        fun k => Submodule.smul_mem _ w (a' k).2
      refine ⟨m, ?_⟩
      simp only [hI, Pi.add_apply, Submodule.coe_add, EF_quad hw, Finset.sum_add_distrib,
        Finset.sum_sub_distrib, ← Finset.mul_sum, hm]
      push_cast
      field_simp)
    M P hP hdeg hs0
  refine ⟨G ∘ Φ.toContinuousLinearEquiv, hG.comp Φ.toContinuousLinearEquiv.differentiable, fun u hu z => ?_, ?_⟩
  · have h := hlaw (fun k => ⟨u k, hu k⟩) (Φ z)
    rw [hp, ← map_add (f := _), mul_div_cancel₀ _ hMR, mul_comm (M : ℂ), _root_.mul_assoc (Real.pi : ℂ) M,
      _root_.mul_assoc (Real.pi : ℂ) M, hH, hH] at h
    simp only at h
    obtain ⟨m, hm⟩ := hZ u (fun k => (w : E) • u k) hu fun k => Submodule.smul_mem _ w (hu k)
    have hadd : ∑ k, hx X bas idx x (z k + (1 / 2 : ℂ) • pv X idx x (u k)) (pv X idx x (u k)) =
        ∑ k, hx X bas idx x (z k) (pv X idx x (u k)) +
          1 / 2 * ∑ k, hx X bas idx x (pv X idx x (u k)) (pv X idx x (u k)) := by
      simp only [hdiag, Finset.mul_sum, ← Finset.sum_add_distrib, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    change G (Φ z) = _ * G (Φ (z + fun k => pv X idx x (u k)))
    rw [h, hadd, epsW, hm, ← _root_.mul_assoc, ← Complex.exp_add, ← Complex.exp_add, ← Complex.exp_add]
    refine (_root_.one_mul _).symm.trans (congrArg (· * G (Φ z)) ?_)
    refine (Complex.exp_int_mul_two_pi_mul_I (M * m)).symm.trans ?_
    congr 1
    push_cast
    ring
  · rw [Jet.polyDeriv_comp_equiv, map_zero]
    convert hG0 using 2
    funext l
    ext i
    change s * (Pi.single (e l).1 (Pi.single (e l).2 1) : Fin n → Fin g → ℂ) (e i).1 (e i).2 = _
    by_cases h : i = l
    · simp [h]
    · have h' : e i ≠ e l := fun h0 => h (e.injective h0)
      by_cases h1 : (e i).1 = (e l).1
      · have h2 : (e i).2 ≠ (e l).2 := fun h2 => h' (Prod.ext h1 h2)
        simp [h, h1, h2]
      · simp [h, h1]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsThetaSublatticeJetNeZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_theta_sublattice_jet_ne_zero_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), P ≠ 0 → 3 * P.totalDegree + 2 ≤ M → ∃ F : (Fin n → Fin g → ℂ) → ℂ, Differentiable ℂ F ∧ (∀ u : Matrix (Fin n) (Fin r) E, (∀ b, u b ∈ 𝔐 • L) → ∀ z, F z = epsW X (w : E) u * cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (u b)) (pv X idx x (u b)))) * F (fun b => z b + pv X idx x (u b))) ∧ I2.polyDeriv P (letterDir X hr idx) F 0 ≠ 0 := by
  first | exact @GlobalTheory.Dict.exists_theta_sublattice_jet_ne_zero | exact GlobalTheory.Dict.exists_theta_sublattice_jet_ne_zero | (intros; apply GlobalTheory.Dict.exists_theta_sublattice_jet_ne_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevelTranslateJetNeZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.Dict

theorem polyDeriv_const_mul_entire {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [FiniteDimensional ℂ W]
    (P : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {G : W → ℂ} (hG : Differentiable ℂ G) (x : W) :
    I2.polyDeriv P u (fun z => c * G z) x = c * I2.polyDeriv P u G x := by
  have := I2.polyDeriv_sum P u (Finset.univ : Finset Unit) (fun _ => c) (fun _ => G)
    (fun _ _ k => I2.contDiff_of_differentiable_fd hG k) x
  simpa using this

theorem polyDeriv_const_mul_of_entire {σ W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W]
    [FiniteDimensional ℂ W] (P : MvPolynomial σ ℂ) (u : σ → W) (c : ℂ) {T : W → ℂ}
    (hG : Differentiable ℂ fun z => c * T z) (x : W) :
    I2.polyDeriv P u (fun z => c * T z) x = c * I2.polyDeriv P u T x := by
  by_cases hc : c = 0
  · have := polyDeriv_const_mul_entire P u 0 hG x
    simpa [hc] using this
  · have h : T = fun z => c⁻¹ * (c * T z) := by
      funext z; field_simp
    conv_rhs => rw [h]
    rw [polyDeriv_const_mul_entire P u c⁻¹ hG x]
    field_simp

theorem exists_level_translate_jet_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), P ≠ 0 → 3 * P.totalDegree + 2 ≤ M → ∃ y : Matrix (Fin n) (Fin r) E, (∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ y' : Matrix (Fin n) (Fin r) E, (∀ b, y' b - y b ∈ L) → κ * thP X hr bas idx (heisG X bas y' v) P x ≠ 0 := by
  intro E _ _ _ r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 v hv θ κ hθ hm hκ P hP hdeg
  obtain ⟨F, hF, hFa, hFP⟩ := GlobalTheory.T.exists_theta_sublattice_jet_ne_zero_alt E r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 P hP hdeg
  obtain ⟨s, cf, hs', hsum⟩ := GlobalTheory.T.theta_ideal_lattice_eq_sum_level_translates E r X g q0 hr bas idx n hs hn w hw L hL x hd ho t ht hc 𝔐 M hM h𝔐 v hv
    θ κ hθ hm hκ F hF hFa
  obtain ⟨hcomp, -, -, hdiff, hprod⟩ := fock_laws E r X g bas idx n hs hn x hd 1 θ
  have hprod' := hprod (fun _ => θ) κ v hv.1 hκ
  have hent : ∀ y : Matrix (Fin n) (Fin r) E,
      Differentiable ℂ fun z => κ * thA X bas idx (heisG X bas y v) x z := by
    intro y
    have : (fun z => κ * thA X bas idx (heisG X bas y v) x z) =
        fun z : Fin n → Fin g → ℂ => ∏ b, fock X bas idx x 1 (pv X idx x (y b)) θ (z b) :=
      funext fun z => (hprod' y z).symm
    rw [this]
    have hb : ∀ b, Differentiable ℂ fun z : Fin n → Fin g → ℂ =>
        fock X bas idx x 1 (pv X idx x (y b)) θ (z b) := fun b =>
      (hdiff hθ.1 (pv X idx x (y b))).comp (f := fun z : Fin n → Fin g → ℂ => z b) (differentiable_apply b)
    exact fun z => (HasFDerivAt.finsetProd (u := Finset.univ) fun b _ => (hb b z).hasFDerivAt).differentiableAt
  have hFe : F = fun z => ∑ y ∈ s, cf y * (κ * thA X bas idx (heisG X bas y v) x z) := funext hsum
  rw [hFe, I2.polyDeriv_sum P _ s cf (fun y z => κ * thA X bas idx (heisG X bas y v) x z)
    (fun y _ k => I2.contDiff_of_differentiable_fd (hent y) k)] at hFP
  obtain ⟨y, hy, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero hFP
  refine ⟨y, hs' y hy, fun y' hy' => ?_⟩
  have hne' := right_ne_zero_of_mul hne
  have hrow : ∀ b, ∃ c : ℂ, fock X bas idx x 1 (pv X idx x (y b)) θ =
      c • fock X bas idx x 1 (pv X idx x (y' b)) θ := by
    intro b
    have h1 := hθ.2 _ (hy' b)
    have h2 := hcomp (pv X idx x (y b)) (pv X idx x (y' b - y b))
    have h3 : pv X idx x (y b) + pv X idx x (y' b - y b) = pv X idx x (y' b) := by
      funext j
      have := congrFun (per_add X x (y b) (y' b - y b)) (idx j)
      rw [add_sub_cancel] at this
      exact this.symm
    rw [h3] at h2
    have h4 : ∀ (e : ℂ) (a : Fin g → ℂ) (φ : (Fin g → ℂ) → ℂ),
        fock X bas idx x 1 a (e • φ) = e • fock X bas idx x 1 a φ := by
      intro e a φ
      funext z
      simp only [fock, Pi.smul_apply, smul_eq_mul]
      ring
    exact ⟨_, by conv_lhs => rw [← h1, h4, h2, smul_smul]⟩
  choose c hcc using hrow
  have hfun : (fun z => κ * thA X bas idx (heisG X bas y v) x z) =
      fun z => (∏ b, c b) * (κ * thA X bas idx (heisG X bas y' v) x z) := by
    funext z
    rw [← hprod' y z, ← hprod' y' z, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun b _ => by rw [hcc b]; rfl
  rw [hfun, polyDeriv_const_mul_entire P _ _ (hent y'), polyDeriv_const_mul_of_entire P _ _ (hent y')] at hne'
  exact right_ne_zero_of_mul hne'

end GlobalTheory.Dict
end

section -- merged from Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsLevelTranslateJetNeZeroStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_level_translate_jet_ne_zero_alt : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (g q0 : ℕ) (hr : X.p0 + q0 = r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (n : ℕ), IsSympl X bas → Even n → ∀ w : 𝓞 E, (w : E) + cc (w : E) = 1 → ∀ L : Lt E r, SelfD X L → ∀ x ∈ X.dom, X.IsOrtho x → ∀ t : ℝ, 0 < t → (∀ τ, X.c τ = t) → ∀ (𝔐 : Ideal (𝓞 E)) (M : ℕ), Odd M → 𝔐 * conjI 𝔐 = Ideal.span {(M : 𝓞 E)} → ∀ v : TF n g, IsVac X bas (w : E) (tens (stdL E n) L) v → ∀ (θ : (Fin g → ℂ) → ℂ) (κ : ℂ), IsTheta1 X bas idx (w : E) x L θ → MeanOne X bas idx x L θ → (∀ z : Fin n → Fin g → ℂ, ∏ b, θ (z b) = κ * thA X bas idx v x z) → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), P ≠ 0 → 3 * P.totalDegree + 2 ≤ M → ∃ y : Matrix (Fin n) (Fin r) E, (∀ b, (M : E) • y b ∈ 𝔐 • L) ∧ ∀ y' : Matrix (Fin n) (Fin r) E, (∀ b, y' b - y b ∈ L) → κ * thP X hr bas idx (heisG X bas y' v) P x ≠ 0 := by
  first | exact @GlobalTheory.Dict.exists_level_translate_jet_ne_zero | exact GlobalTheory.Dict.exists_level_translate_jet_ne_zero | (intros; apply GlobalTheory.Dict.exists_level_translate_jet_ne_zero <;> assumption)
end
