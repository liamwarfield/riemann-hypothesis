module

public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.FiniteCuspidalOfIsCuspidal
public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.MemOfTameGeneratorFrobenius
public import Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ConjTorusSubApply

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.LabFinite
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

theorem lab_finite (K : Type) [Field K] [Finite K] (n : ℕ) : (Lab K n).Finite := by
  have h : Finite (Polynomial.degreeLT K (n + 1)) :=
    Finite.of_equiv _ (Polynomial.degreeLTEquiv K (n + 1)).symm.toEquiv
  refine Set.Finite.subset (Set.toFinite ((Polynomial.degreeLT K (n + 1) : Submodule K K[X]) : Set K[X])) fun P hP => ?_
  refine Polynomial.mem_degreeLT.2 (lt_of_le_of_lt Polynomial.degree_le_natDegree ?_)
  rw [hP.2.2.2]
  exact_mod_cast Nat.lt_succ_self n

end PositivityTheory.Rg.DzCount

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ExistsMaximalStableAvoiding
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

section Quot

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def subRep4 (π : Representation ℂ G V) (U : Submodule ℂ V) (hU : ∀ g, ∀ v ∈ U, π g v ∈ U) :
    Representation ℂ G U where
  toFun g := (π g).restrict (fun v hv => hU g v hv)
  map_one' := LinearMap.ext fun v => Subtype.ext (by
    show π 1 (v : V) = v
    rw [map_one]; rfl)
  map_mul' g h := LinearMap.ext fun v => Subtype.ext (by
    show π (g * h) (v : V) = π g (π h v)
    rw [map_mul]; rfl)

def quotRep4 (π : Representation ℂ G V) (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, π g v ∈ M) :
    Representation ℂ G (V ⧸ M) where
  toFun g := M.mapQ M (π g) (fun v hv => hM g v hv)
  map_one' := LinearMap.ext fun x => Submodule.Quotient.induction_on M x fun v => by
    show Submodule.Quotient.mk (π 1 v) = Submodule.Quotient.mk v
    rw [map_one]; rfl
  map_mul' g h := LinearMap.ext fun x => Submodule.Quotient.induction_on M x fun v => by
    show Submodule.Quotient.mk (π (g * h) v) = Submodule.Quotient.mk (π g (π h v))
    rw [map_mul]; rfl

theorem quotRep4_mk (π : Representation ℂ G V) (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, π g v ∈ M) (g : G) (v : V) :
    quotRep4 π M hM g (Submodule.Quotient.mk v) = Submodule.Quotient.mk (π g v) := rfl

theorem exists_maximal_stable_avoiding (π : Representation ℂ G V) (x₀ : V) (hx₀ : x₀ ≠ 0) :
    ∃ M : Submodule ℂ V, (∀ g, ∀ v ∈ M, π g v ∈ M) ∧ x₀ ∉ M ∧
      ∀ N : Submodule ℂ V, (∀ g, ∀ v ∈ N, π g v ∈ N) → x₀ ∉ N → M ≤ N → N = M := by
  let S : Set (Submodule ℂ V) := {N | (∀ g, ∀ v ∈ N, π g v ∈ N) ∧ x₀ ∉ N}
  have hbot : (⊥ : Submodule ℂ V) ∈ S := ⟨fun g v hv => by
    rw [(Submodule.mem_bot ℂ).1 hv, map_zero]; exact Submodule.zero_mem _, fun h => hx₀ ((Submodule.mem_bot ℂ).1 h)⟩
  obtain ⟨M, -, hMS, hMmax⟩ := zorn_le_nonempty₀ S (fun c hcS hc y hy => by
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨fun g v hv => ?_, fun h => ?_⟩, fun z hz => le_sSup hz⟩
    · obtain ⟨N, hN, hvN⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hv
      exact le_sSup hN ((hcS hN).1 g v hvN)
    · obtain ⟨N, hN, hxN⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 h
      exact (hcS hN).2 hxN) ⊥ hbot
  exact ⟨M, hMS.1, hMS.2, fun N hN hxN hMN => le_antisymm (hMmax ⟨hN, hxN⟩ hMN) hMN⟩

theorem quotRep4_irr (π : Representation ℂ G V) (M : Submodule ℂ V) (hM : ∀ g, ∀ v ∈ M, π g v ∈ M) (x₀ : V)
    (hgen : ∀ N : Submodule ℂ V, (∀ g, ∀ v ∈ N, π g v ∈ N) → x₀ ∈ N → N = ⊤) (hx₀ : x₀ ∉ M)
    (hmax : ∀ N : Submodule ℂ V, (∀ g, ∀ v ∈ N, π g v ∈ N) → x₀ ∉ N → M ≤ N → N = M) :
    (quotRep4 π M hM).IsIrreducible := by
  have hne : (Submodule.Quotient.mk x₀ : V ⧸ M) ≠ 0 := by
    rwa [Ne, Submodule.Quotient.mk_eq_zero]
  refine { toNontrivial := ⟨⊥, ⊤, fun h => hne ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · have h1 : (Submodule.Quotient.mk x₀ : V ⧸ M) ∈ (⊤ : Subrepresentation (quotRep4 π M hM)).toSubmodule :=
      Submodule.mem_top
    rw [← h] at h1
    exact (Submodule.mem_bot ℂ).1 h1
  · let N : Submodule ℂ V := S.toSubmodule.comap M.mkQ
    have hNst : ∀ g, ∀ v ∈ N, π g v ∈ N := fun g v hv => by
      show Submodule.Quotient.mk (π g v) ∈ S.toSubmodule
      rw [← quotRep4_mk π M hM]
      exact S.apply_mem_toSubmodule g hv
    by_cases hx : x₀ ∈ N
    · right
      have hN := hgen N hNst hx
      refine Subrepresentation.ext (eq_top_iff.2 fun q _ => ?_)
      induction q using Submodule.Quotient.induction_on with
      | H v =>
        have : v ∈ N := by rw [hN]; exact Submodule.mem_top
        exact this
    · left
      have hMN : M ≤ N := fun v hv => by
        show Submodule.Quotient.mk v ∈ S.toSubmodule
        rw [(Submodule.Quotient.mk_eq_zero M).2 hv]
        exact Submodule.zero_mem _
      have hN := hmax N hNst hx hMN
      refine Subrepresentation.ext (eq_bot_iff.2 fun q hq => ?_)
      induction q using Submodule.Quotient.induction_on with
      | H v =>
        have : v ∈ N := hq
        rw [hN] at this
        exact (Submodule.mem_bot ℂ).2 ((Submodule.Quotient.mk_eq_zero M).2 this)

end Quot

theorem val_unif4 {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ϖ : kˣ}
    (hϖ : ord k ϖ = 1) : valuation k (ϖ : k) = uniformizer k := by
  obtain ⟨π₀, hπ₀⟩ := exists_uniformizer k
  have h1 : ord k π₀ = 1 := ord_eq_one hπ₀
  have h0 : ord k π₀⁻¹ = -1 := by
    have := ord_mul k π₀ π₀⁻¹
    rw [mul_inv_cancel, ord_eq_zero (by simp), h1] at this
    omega
  have h2 : ord k (ϖ * π₀⁻¹) = 0 := by rw [ord_mul, h0, hϖ]; norm_num
  have h3 := ord_eq_zero_iff.1 h2
  rw [Units.val_mul, Units.val_inv_eq_inv_val, map_mul, map_inv₀] at h3
  have hne : valuation k (π₀ : k) ≠ 0 := by simp
  rw [mul_inv_eq_one₀ hne] at h3
  rw [h3, hπ₀]

theorem st4 : St4 := by
  intro k W _ _ _ _ _ _ _ n hn τ hτ ϖ hϖ c
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  obtain ⟨ω₀, hω₀⟩ := exists_hasCentralChar hτ
  obtain ⟨ω, hω, hωc⟩ := exists_isTameLift ω₀ (val_unif4 hϖ) c
  have hE : ExtendsCentral ω τ := hω.extendsCentral hω₀
  obtain ⟨w₀, hw₀⟩ : ∃ w₀ : W, w₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    haveI := hτ
    exact (bot_ne_top : (⊥ : Subrepresentation τ) ≠ ⊤) (Subrepresentation.ext (Submodule.ext fun w => by
      rw [hcon w]; exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩))
  let π₀ := depthZero τ ω hE
  let cn := canon τ ω hE
  have hcn : ∀ (g : KO k (Fin n)) (w : W), cn (τ (redK k (Fin n) g) w) = π₀ g (cn w) := fun g w => by
    rw [← extZK_KO τ ω hE, (canon τ ω hE).isIntertwining]; rfl
  let x₀ := cn w₀
  have hx₀ : x₀ ≠ 0 := fun h => hw₀ (canon_injective τ ω hE (h.trans (map_zero _).symm))
  let U : Submodule ℂ (DepthZeroSp τ ω hE) := Submodule.span ℂ (Set.range fun g => π₀ g x₀)
  have hU : ∀ g, ∀ v ∈ U, π₀ g v ∈ U := fun g v hv => by
    have hle : U ≤ U.comap (π₀ g) := Submodule.span_le.2 (by
      rintro _ ⟨h, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp only [map_mul, Module.End.mul_apply]⟩)
    exact hle hv
  have hx₀U : x₀ ∈ U := Submodule.subset_span ⟨1, by simp only [map_one, Module.End.one_apply]⟩
  have hcnU : ∀ w, cn w ∈ U := by
    let S : Subrepresentation τ := ⟨U.comap cn.toLinearMap, fun g v hv => by
      obtain ⟨g', rfl⟩ := redK_surjective g
      show cn _ ∈ U
      rw [hcn]
      exact hU g' _ hv⟩
    have hS : S = ⊤ := by
      refine (hτ.eq_bot_or_eq_top S).resolve_left fun h => hw₀ ?_
      have : w₀ ∈ S.toSubmodule := hx₀U
      rw [h] at this
      exact (Submodule.mem_bot ℂ).1 this
    intro w
    have : w ∈ S.toSubmodule := by rw [hS]; exact Submodule.mem_top
    exact this
  let π₁ := subRep4 π₀ U hU
  let x₁ : U := ⟨x₀, hx₀U⟩
  have hx₁ : x₁ ≠ 0 := fun h => hx₀ (congrArg Subtype.val h)
  have hgen : ∀ N : Submodule ℂ U, (∀ g, ∀ v ∈ N, π₁ g v ∈ N) → x₁ ∈ N → N = ⊤ := by
    intro N hN hxN
    have hle : U ≤ N.map U.subtype := Submodule.span_le.2 (by
      rintro _ ⟨g, rfl⟩
      exact ⟨π₁ g x₁, hN g x₁ hxN, rfl⟩)
    refine eq_top_iff.2 fun u _ => ?_
    obtain ⟨u', hu', he⟩ := hle u.2
    rwa [show u' = u from Subtype.ext he] at hu'
  obtain ⟨M, hM, hx₁M, hMmax⟩ := exists_maximal_stable_avoiding π₁ x₁ hx₁
  let ρQ := quotRep4 π₁ M hM
  have hirr : ρQ.IsIrreducible := quotRep4_irr π₁ M hM x₁ hgen hx₁M hMmax
  have hsm : IsSmooth ρQ := by
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H u =>
      let H : Subgroup (GL (Fin n) k) :=
        { carrier := {g | ρQ g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u}
          one_mem' := by simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply]
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at ha hb ⊢
            rw [hb, ha]
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_setOf_eq] at ha ⊢
            conv_lhs => rw [← ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
      have hopen : IsOpen {g : GL (Fin n) k | π₀ g (u : DepthZeroSp τ ω hE) = u} := isSmooth_depthZero τ ω hE u
      have hsub : {g : GL (Fin n) k | π₀ g (u : DepthZeroSp τ ω hE) = u} ⊆ (H : Set (GL (Fin n) k)) := fun g hg => by
        show ρQ g (Submodule.Quotient.mk u) = Submodule.Quotient.mk u
        rw [quotRep4_mk]
        congr 1
        exact Subtype.ext hg
      exact Subgroup.isOpen_of_mem_nhds H (g := 1)
        (Filter.mem_of_superset (hopen.mem_nhds (by simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply])) hsub)
  let jU : W →ₗ[ℂ] U := LinearMap.codRestrict U cn.toLinearMap hcnU
  let j : W →ₗ[ℂ] (U ⧸ M) := M.mkQ.comp jU
  have hj : ∀ (g : KO k (Fin n)) (v : W), j (τ (redK k (Fin n) g) v) = ρQ g (j v) := fun g v => by
    show Submodule.Quotient.mk (jU (τ (redK k (Fin n) g) v)) = Submodule.Quotient.mk (π₁ g (jU v))
    congr 1
    exact Subtype.ext (hcn g v)
  have hjinj : Function.Injective j := by
    let K : Subrepresentation τ := ⟨LinearMap.ker j, fun g v hv => by
      obtain ⟨g', rfl⟩ := redK_surjective g
      rw [LinearMap.mem_ker] at hv ⊢
      rw [hj, hv, map_zero]⟩
    have hK : K = ⊥ := by
      refine (hτ.eq_bot_or_eq_top K).resolve_right fun h => ?_
      have : w₀ ∈ K.toSubmodule := by rw [h]; exact Submodule.mem_top
      have h2 : j w₀ = 0 := LinearMap.mem_ker.1 this
      apply hx₁M
      exact (Submodule.Quotient.mk_eq_zero M).1 h2
    have : LinearMap.ker j = ⊥ := congrArg Subrepresentation.toSubmodule hK
    exact LinearMap.ker_eq_bot.1 this
  refine ⟨⟨U ⧸ M, ρQ, hsm, hirr⟩, ω, j, ?_, hωc, hjinj, hj⟩
  intro z q
  induction q using Submodule.Quotient.induction_on with
  | H u =>
    show ρQ (GeneralLinearGroup.scalar (Fin n) z) (Submodule.Quotient.mk u) = (ω z : ℂ) • Submodule.Quotient.mk u
    rw [quotRep4_mk, ← Submodule.Quotient.mk_smul]
    congr 1
    exact Subtype.ext (hasCentralChar_depthZero τ ω hE z u)

end PositivityTheory.Rg.DzCount

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.LeviInductionForms
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

namespace PositivityTheory.Rg.DzCount

namespace LeviInductionForms

theorem pow_eq_pow_iff_mod {M : Type*} [CommMonoid M] {ζ : M} {N : ℕ} (h : IsPrimitiveRoot ζ N)
    (hN : 0 < N) (a b : ℕ) : ζ ^ a = ζ ^ b ↔ a % N = b % N := by
  have e : ∀ c, ζ ^ c = ζ ^ (c % N) := fun c => by
    conv_lhs => rw [← Nat.mod_add_div c N]
    rw [pow_add, pow_mul, h.pow_eq_one, one_pow, mul_one]
  rw [e a, e b]
  exact ⟨fun H => h.pow_inj (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) H, fun H => by rw [H]⟩

theorem natDegree_minpoly_eq {K F : Type*} [Field K] [Finite K] [Field F] [Algebra K F] (n : ℕ)
    (hn : 0 < n) (w : F) (hw : IsIntegral K w) (h1 : w ^ (Nat.card K) ^ n = w)
    (h2 : ∀ d, 0 < d → d < n → w ^ (Nat.card K) ^ d ≠ w) : (minpoly K w).natDegree = n := by
  have hirr := minpoly.irreducible hw
  have hdvd : minpoly K w ∣ (X ^ (Nat.card K) ^ n - X : K[X]) := by
    apply minpoly.dvd
    simp [h1]
  have hd : (minpoly K w).natDegree ∣ n := hirr.natDegree_dvd_of_dvd_X_pow_card_pow_sub_X hdvd
  have hpos : 0 < (minpoly K w).natDegree := minpoly.natDegree_pos hw
  have hself : w ^ (Nat.card K) ^ (minpoly K w).natDegree = w := by
    obtain ⟨r, hr⟩ := (hirr.natDegree_dvd_iff_dvd_X_pow_card_pow_sub_X).1 (dvd_refl _)
    have h3 : Polynomial.aeval w (X ^ (Nat.card K) ^ (minpoly K w).natDegree - X : K[X]) = 0 := by
      rw [hr, map_mul, minpoly.aeval, zero_mul]
    simpa [sub_eq_zero] using h3
  by_contra hne
  exact h2 _ hpos (lt_of_le_of_ne (Nat.le_of_dvd hn hd) hne) hself

theorem exists_eq_pow_of_aeval {K F : Type*} [Field K] [Fintype K] [Field F] [Algebra K F] (n : ℕ)
    (hn : 0 < n) (w w' : F) (hw : IsIntegral K w) (h1 : w ^ (Nat.card K) ^ n = w)
    (h2 : ∀ d, 0 < d → d < n → w ^ (Nat.card K) ^ d ≠ w)
    (hP : Polynomial.aeval w' (minpoly K w) = 0) : ∃ i : ℕ, w' = w ^ (Nat.card K) ^ i := by
  classical
  have hq : Fintype.card K = Nat.card K := Nat.card_eq_fintype_card.symm
  have hφ : ∀ (i : ℕ) (x : F), (FiniteField.frobeniusAlgHom K F ^ i) x = x ^ (Nat.card K) ^ i := by
    intro i
    induction i with
    | zero => intro x; simp
    | succ i ih =>
      intro x
      rw [pow_succ, AlgHom.mul_apply, ih]
      show (x ^ Fintype.card K) ^ (Nat.card K) ^ i = _
      rw [hq, ← pow_mul, ← pow_succ']
  have hroot : ∀ i : ℕ, Polynomial.aeval (w ^ (Nat.card K) ^ i) (minpoly K w) = 0 := by
    intro i
    rw [← hφ, Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  have hpw : ∀ a b : ℕ, (w ^ (Nat.card K) ^ a) ^ (Nat.card K) ^ b = w ^ (Nat.card K) ^ (a + b) := by
    intro a b
    rw [← pow_mul, ← pow_add]
  have hlt : ∀ i j : ℕ, i < j → j < n → w ^ (Nat.card K) ^ i ≠ w ^ (Nat.card K) ^ j := by
    intro i j hij hjn H
    have H2 := congrArg (fun x : F => x ^ (Nat.card K) ^ (n - j)) H
    simp only [hpw] at H2
    have e : j + (n - j) = n := by omega
    rw [e, h1] at H2
    exact h2 (i + (n - j)) (by omega) (by omega) H2
  have hinj : Set.InjOn (fun i : ℕ => w ^ (Nat.card K) ^ i) (Finset.range n : Set ℕ) := by
    intro i hi j hj H
    simp only [Finset.mem_coe, Finset.mem_range, Finset.coe_range, Set.mem_Iio] at hi hj
    rcases lt_trichotomy i j with h | h | h
    · exact absurd H (hlt i j h hj)
    · exact h
    · exact absurd H.symm (hlt j i h hi)
  by_contra hno
  push_neg at hno
  set S := (Finset.range n).image (fun i : ℕ => w ^ (Nat.card K) ^ i) with hS
  have hcardS : S.card = n := by
    rw [hS, Finset.card_image_of_injOn hinj, Finset.card_range]
  have hw'S : w' ∉ S := by
    rw [hS, Finset.mem_image]
    rintro ⟨i, -, hi⟩
    exact hno i hi.symm
  have hP0 : minpoly K w ≠ 0 := minpoly.ne_zero hw
  have hmap0 : (minpoly K w).map (algebraMap K F) ≠ 0 := Polynomial.map_ne_zero hP0
  have hsub : (insert w' S).val ⊆ ((minpoly K w).map (algebraMap K F)).roots := by
    intro x hx
    rw [Finset.mem_val, Finset.mem_insert] at hx
    rw [Polynomial.mem_roots hmap0, Polynomial.IsRoot.def, Polynomial.eval_map,
      ← Polynomial.aeval_def]
    rcases hx with rfl | hx
    · exact hP
    · rw [hS, Finset.mem_image] at hx
      obtain ⟨i, -, rfl⟩ := hx
      exact hroot i
  have hcard := Polynomial.card_le_degree_of_subset_roots hsub
  rw [Finset.card_insert_of_notMem hw'S, hcardS, Polynomial.natDegree_map,
    natDegree_minpoly_eq n hn w hw h1 h2] at hcard
  omega

end LeviInductionForms

open LeviInductionForms in
theorem st3a : St3a := by
  unfold St3a
  intro K _ _ n hn
  classical
  letI : Fintype K := Fintype.ofFinite K
  have hq1 : 1 < Nat.card K := Finite.one_lt_card
  have hqn : 1 < Nat.card K ^ n := Nat.one_lt_pow hn.ne' hq1
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = Nat.card K ^ n - 1 := ⟨_, rfl⟩
  have hNq : Nat.card K ^ n = N + 1 := by omega
  have hNpos : 0 < N := by omega
  haveI : NeZero N := ⟨hNpos.ne'⟩
  haveI : NeZero ((N : ℕ) : K) := ⟨by
    have hc : ((Nat.card K : ℕ) : K) = 0 := by
      rw [Nat.card_eq_fintype_card]; exact FiniteField.cast_card_eq_zero K
    have h4 : ((Nat.card K ^ n : ℕ) : K) = (N : K) + 1 := by
      rw [hNq, Nat.cast_add, Nat.cast_one]
    rw [Nat.cast_pow, hc, zero_pow hn.ne'] at h4
    intro h0
    rw [h0, zero_add] at h4
    exact zero_ne_one h4⟩
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (AlgebraicClosure K) N
  obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, IsPrimitiveRoot ζ N := ⟨_, Complex.isPrimitiveRoot_exp N hNpos.ne'⟩
  have htr : ∀ a b : ℕ, ζ ^ a = ζ ^ b ↔ ω ^ a = ω ^ b := by
    intro a b
    rw [pow_eq_pow_iff_mod hζ hNpos, pow_eq_pow_iff_mod hω hNpos]
  let jOf : ℂ → ℕ := fun z => if h : ∃ j : ℕ, ζ ^ j = z then h.choose else 0
  have hj : ∀ z : ℂ, ExactPer (Nat.card K) n z → ζ ^ jOf z = z := by
    intro z hz
    unfold ExactPer at hz
    obtain ⟨hz0, hz1, -⟩ := hz
    have hzN : z ^ N = 1 := by
      rw [hNq, pow_succ'] at hz1
      exact mul_right_injective₀ hz0 (hz1.trans (mul_one z).symm)
    have hex : ∃ j : ℕ, ζ ^ j = z := by
      obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hzN
      exact ⟨i, hi⟩
    simp only [jOf, dif_pos hex]
    exact hex.choose_spec
  have hint : ∀ x : AlgebraicClosure K, IsIntegral K x := fun x => Algebra.IsIntegral.isIntegral x
  have hper : ∀ (j m : ℕ), (ζ ^ j) ^ (Nat.card K) ^ m = ζ ^ j ↔
      (ω ^ j) ^ (Nat.card K) ^ m = ω ^ j := by
    intro j m
    rw [← pow_mul, ← pow_mul]
    exact htr _ _
  have hω0 : ω ≠ 0 := hω.ne_zero hNpos.ne'
  refine ⟨fun z => minpoly K (ω ^ jOf z), ?_, ?_⟩
  · intro z hz
    have hzj := hj z hz
    unfold ExactPer at hz
    obtain ⟨-, hz1, hz2⟩ := hz
    rw [← hzj] at hz1 hz2
    have hw1 : (ω ^ jOf z) ^ (Nat.card K) ^ n = ω ^ jOf z := (hper _ _).1 hz1
    have hw2 : ∀ d, 0 < d → d < n → (ω ^ jOf z) ^ (Nat.card K) ^ d ≠ ω ^ jOf z :=
      fun d hd hdn H => hz2 d hd hdn ((hper _ _).2 H)
    have hw := hint (ω ^ jOf z)
    show (minpoly K (ω ^ jOf z)).Monic ∧ Irreducible (minpoly K (ω ^ jOf z)) ∧
      minpoly K (ω ^ jOf z) ≠ X ∧ (minpoly K (ω ^ jOf z)).natDegree = n
    refine ⟨minpoly.monic hw, minpoly.irreducible hw, ?_, natDegree_minpoly_eq n hn _ hw hw1 hw2⟩
    intro hX
    have h0 := minpoly.aeval K (ω ^ jOf z)
    rw [hX, Polynomial.aeval_X] at h0
    exact pow_ne_zero _ hω0 h0
  · intro z z' hz hz' hlab
    have hzj := hj z hz
    have hzj' := hj z' hz'
    unfold ExactPer at hz
    obtain ⟨-, hz1, hz2⟩ := hz
    rw [← hzj] at hz1 hz2
    have hw1 : (ω ^ jOf z) ^ (Nat.card K) ^ n = ω ^ jOf z := (hper _ _).1 hz1
    have hw2 : ∀ d, 0 < d → d < n → (ω ^ jOf z) ^ (Nat.card K) ^ d ≠ ω ^ jOf z :=
      fun d hd hdn H => hz2 d hd hdn ((hper _ _).2 H)
    have hw := hint (ω ^ jOf z)
    have hP : Polynomial.aeval (ω ^ jOf z') (minpoly K (ω ^ jOf z)) = 0 := by
      have hlab' : minpoly K (ω ^ jOf z) = minpoly K (ω ^ jOf z') := hlab
      rw [hlab']
      exact minpoly.aeval K _
    obtain ⟨i, hi⟩ := exists_eq_pow_of_aeval n hn _ _ hw hw1 hw2 hP
    refine ⟨i, ?_⟩
    rw [← hzj', ← hzj, ← pow_mul, htr, pow_mul]
    exact hi

end PositivityTheory.Rg.DzCount

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.HasCentralCharOfEquiv
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace CentralCharacterTransfer

theorem equiv_apply {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (g : G) (v : V) :
    φ (ρ g v) = σ g (φ v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ φ.toIntertwiningMap g v

theorem mem_fixed_iff {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    {H : Subgroup G} {v : V} : v ∈ fixed ρ H ↔ ∀ h ∈ H, ρ h v = v := by
  change (∀ h : H, ρ h v = ((1 : H →* ℂˣ) h : ℂ) • v) ↔ _
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  constructor
  · intro hv h hh
    exact hv ⟨h, hh⟩
  · intro hv h
    exact hv h h.2

theorem map_fixed {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (H : Subgroup G) :
    (fixed ρ H).map φ.toLinearEquiv.toLinearMap = fixed σ H := by
  ext w
  simp only [Submodule.mem_map, mem_fixed_iff]
  constructor
  · rintro ⟨v, hv, rfl⟩ h hh
    change σ h (φ v) = φ v
    rw [← equiv_apply, hv h hh]
  · intro hw
    have e2 : φ (φ.toLinearEquiv.symm w) = w := φ.toLinearEquiv.apply_symm_apply w
    refine ⟨φ.toLinearEquiv.symm w, fun h hh => ?_, e2⟩
    apply φ.toLinearEquiv.injective
    change φ _ = φ _
    rw [equiv_apply, e2, hw h hh]

theorem hasCentralChar_of_equiv {k V W : Type} [Field k] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {n : ℕ} {π : Representation ℂ (GL (Fin n) k) V} {σ : Representation ℂ (GL (Fin n) k) W} (φ : π.Equiv σ)
    {ω : kˣ →* ℂˣ} (h : HasCentralChar π ω) : HasCentralChar σ ω := by
  intro z w
  have e2 : φ (φ.toLinearEquiv.symm w) = w := φ.toLinearEquiv.apply_symm_apply w
  rw [← e2, ← equiv_apply, h z]
  exact φ.toLinearEquiv.map_smul _ _

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem transfer {W W' V V' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] {n : ℕ}
    {τ : Representation ℂ (GL (Fin n) 𝓀[k]) W} {τ' : Representation ℂ (GL (Fin n) 𝓀[k]) W'}
    {π : Representation ℂ (GL (Fin n) k) V} {π' : Representation ℂ (GL (Fin n) k) V'}
    {j : W →ₗ[ℂ] V} {j' : W' →ₗ[ℂ] V'} (hj : IsTypeMap τ π j) (hj' : IsTypeMap τ' π' j')
    (hf : fixed π (KOne k (Fin n)) = LinearMap.range j) (hf' : fixed π' (KOne k (Fin n)) = LinearMap.range j')
    (φ : π.Equiv π') : ∃ e : W ≃ₗ[ℂ] W', ∀ g v, e (τ g v) = τ' g (e v) := by
  have hm := map_fixed φ (KOne k (Fin n))
  rw [hf, hf'] at hm
  let e : W ≃ₗ[ℂ] W' := (LinearEquiv.ofInjective j hj.1).trans
    ((φ.toLinearEquiv.submoduleMap (LinearMap.range j)).trans
      ((LinearEquiv.ofEq _ _ hm).trans (LinearEquiv.ofInjective j' hj'.1).symm))
  have key : ∀ w, j' (e w) = φ (j w) := by
    intro w
    have h1 := congrArg Subtype.val ((LinearEquiv.ofInjective j' hj'.1).apply_symm_apply
      ((LinearEquiv.ofEq _ _ hm) ((φ.toLinearEquiv.submoduleMap _) ((LinearEquiv.ofInjective j hj.1) w))))
    rw [LinearEquiv.ofInjective_apply] at h1
    exact h1
  refine ⟨e, fun g v => ?_⟩
  obtain ⟨g', rfl⟩ := GlobalTheory.LocGL.redK_surjective g
  apply hj'.1
  rw [key, hj.2, hj'.2, key]
  exact equiv_apply φ _ _

end CentralCharacterTransfer

open CentralCharacterTransfer in
theorem st8a : St4 → St5 → St6 → St7 → St8a := by
  classical
  intro h4 h5 h6 h7 k _ _ _ _ n hn ϖ hϖ c
  obtain ⟨τ, hτ, hinj⟩ := h7 𝓀[k] n hn
  have hdata : ∀ P ∈ Lab 𝓀[k] n, ∃ (π : IrrRep (GL (Fin n) k)) (ω : kˣ →* ℂˣ) (j : (τ P).V →ₗ[ℂ] π.V),
      HasCentralChar π.ρ ω ∧ ω ϖ = c ∧ IsTypeMap (τ P).ρ π.ρ j :=
    fun P hP => h4 k (τ P).V n hn (τ P).ρ (hτ P hP).1 ϖ hϖ c
  choose π ω j hω hc hj using hdata
  have hirr : (1 : Representation ℂ (GL (Fin n) k) ℂ).IsIrreducible := by
    refine { exists_pair_ne := ⟨⊥, ⊤, fun h => ?_⟩, eq_bot_or_eq_top := fun s => ?_ }
    · exact bot_ne_top (α := Submodule ℂ ℂ) (congrArg Subrepresentation.toSubmodule h)
    · rcases Ideal.eq_bot_or_top s.toSubmodule with h | h
      · exact Or.inl (Subrepresentation.toSubmodule_injective h)
      · exact Or.inr (Subrepresentation.toSubmodule_injective h)
  let d : IrrRep (GL (Fin n) k) := ⟨ℂ, 1, fun v => by simp, hirr⟩
  let F : 𝓀[k][X] → IrrGL (k := k) := fun P =>
    if hP : P ∈ Lab 𝓀[k] n then ⟨n, Quotient.mk _ (π P hP)⟩ else ⟨n, Quotient.mk _ d⟩
  have hF : ∀ P (hP : P ∈ Lab 𝓀[k] n), F P = ⟨n, Quotient.mk _ (π P hP)⟩ := by
    intro P hP
    simp only [F, dif_pos hP]
  have hfix : ∀ P (hP : P ∈ Lab 𝓀[k] n),
      fixed (π P hP).ρ (KOne k (Fin n)) = LinearMap.range (j P hP) := by
    intro P hP
    haveI := GlobalTheory.SmGL.nontrivial_of_irreducible (hτ P hP).1
    exact h6 k (τ P).V n (τ P).ρ (hτ P hP).2 (π P hP) (ω P hP) (hω P hP) (j P hP) (hj P hP)
  refine ⟨F, fun P hP => ?_, fun P hP P' hP' hPP => ?_⟩
  · haveI := GlobalTheory.SmGL.nontrivial_of_irreducible (hτ P hP).1
    rw [hF P hP]
    obtain ⟨ψ⟩ : Nonempty ((π P hP).ρ.Equiv
        (IrrCl.rep (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))).ρ) :=
      Quotient.exact (Quotient.out_eq (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))).symm
    set π₀ := IrrCl.rep (Quotient.mk _ (π P hP) : IrrCl (GL (Fin n) k))
    let j₀ : (τ P).V →ₗ[ℂ] π₀.V := ψ.toLinearEquiv.toLinearMap ∘ₗ j P hP
    have hj₀ : IsTypeMap (τ P).ρ π₀.ρ j₀ := by
      refine ⟨ψ.toLinearEquiv.injective.comp (hj P hP).1, fun g v => ?_⟩
      change ψ (j P hP _) = π₀.ρ g (ψ (j P hP v))
      rw [(hj P hP).2, equiv_apply]
    have hcc := GlobalTheory.LocGL.hasCentralChar_of_equiv ψ (hω P hP)
    refine ⟨rfl, ⟨hn, h5 k (τ P).V n (τ P).ρ (hτ P hP).2 π₀ j₀ hj₀⟩, ?_, ω P hP, hcc, hc P hP⟩
    change fixed π₀.ρ (KOne k (Fin n)) ≠ ⊥
    rw [h6 k (τ P).V n (τ P).ρ (hτ P hP).2 π₀ (ω P hP) hcc j₀ hj₀]
    obtain ⟨w, hw⟩ := exists_ne (0 : (τ P).V)
    intro hb
    apply hw
    apply hj₀.1
    rw [map_zero]
    have hm : j₀ w ∈ LinearMap.range j₀ := LinearMap.mem_range_self j₀ w
    rw [hb] at hm
    exact (Submodule.mem_bot ℂ).1 hm
  · rw [hF P hP, hF P' hP'] at hPP
    have hq := eq_of_heq (Sigma.mk.inj_iff.1 hPP).2
    obtain ⟨φ⟩ : Nonempty ((π P hP).ρ.Equiv (π P' hP').ρ) := Quotient.exact hq
    obtain ⟨e, he⟩ := transfer (hj P hP) (hj P' hP') (hfix P hP) (hfix P' hP') φ
    exact hinj P hP P' hP' ⟨e, he⟩

end PositivityTheory.Rg.DzCount

end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.GaloisPermutationReps.SubquotientEquivalence.ExistsLiftUnipotentRadical
noncomputable section

open NumberField IsDedekindDomain ValuativeRel Matrix Polynomial
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.DzCount

namespace L5

section Entries

variable {R : Type} [CommRing R] {s N : ℕ} {d : Fin s → ℕ} {e : (Σ a, Fin (d a)) ≃ Fin N}

theorem mem_unipotent_radical_iff_alt {u : GL (Fin N) R} :
    u ∈ unipRad R e ↔
      ∀ i j, ¬ blk e i < blk e j → (u : Matrix (Fin N) (Fin N) R) i j = (1 : Matrix (Fin N) (Fin N) R) i j := by
  rw [mem_unipRad, mem_parab]
  constructor
  · rintro ⟨hP, hD⟩ i j hij
    rcases lt_or_eq_of_le (not_lt.1 hij) with h | h
    · rw [hP i j h, Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ h
    · obtain ⟨⟨a, p⟩, rfl⟩ := e.surjective i
      obtain ⟨⟨b, q⟩, rfl⟩ := e.surjective j
      simp only [blk_apply] at h
      subst h
      rw [hD, Matrix.one_apply, Matrix.one_apply]
      simp [e.apply_eq_iff_eq]
  · intro h
    refine ⟨fun i j hij => ?_, fun a p q => ?_⟩
    · rw [h i j (not_lt.2 hij.le), Matrix.one_apply_ne]
      rintro rfl
      exact lt_irrefl _ hij
    · rw [h _ _ (by simp), Matrix.one_apply, Matrix.one_apply]
      simp [e.apply_eq_iff_eq]

theorem exists_block_lt_of_ne_bot (h : unipRad R e ≠ ⊥) : ∃ i j, blk e i < blk e j := by
  by_contra hc
  push Not at hc
  apply h
  rw [eq_bot_iff]
  intro u hu
  rw [Subgroup.mem_bot]
  refine Units.ext (Matrix.ext fun i j => ?_)
  rw [Units.val_one]
  exact (mem_unipotent_radical_iff_alt.1 hu) i j (not_lt.2 (hc i j))

theorem unipotent_radical_ne_bot {K : Type} [Field K] (h : ∃ i j, blk e i < blk e j) : unipRad K e ≠ ⊥ := by
  obtain ⟨i, j, hij⟩ := h
  have hne : i ≠ j := by
    rintro rfl
    exact lt_irrefl _ hij
  let t : GL (Fin N) K := Matrix.GeneralLinearGroup.mkOfDetNeZero (Matrix.transvection i j 1)
    (by rw [Matrix.det_transvection_of_ne _ _ hne]; exact one_ne_zero)
  have ht : t ∈ unipRad K e := by
    rw [mem_unipotent_radical_iff_alt]
    intro a b hab
    show (1 + Matrix.single i j (1 : K)) a b = _
    rw [Matrix.add_apply, Matrix.single_apply, ite_eq_right, add_zero]
    rintro ⟨rfl, rfl⟩
    exact hab hij
  intro hb
  rw [hb, Subgroup.mem_bot] at ht
  have h1 := congrArg (fun x : GL (Fin N) K => (x : Matrix (Fin N) (Fin N) K) i j) ht
  simp only [t, Matrix.GeneralLinearGroup.mkOfDetNeZero, Units.val_one] at h1
  change (1 + Matrix.single i j (1 : K)) i j = (1 : Matrix (Fin N) (Fin N) K) i j at h1
  rw [Matrix.add_apply, Matrix.single_apply_same, Matrix.one_apply_ne hne, zero_add] at h1
  exact one_ne_zero h1

end Entries

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {s N : ℕ} {d : Fin s → ℕ} {e : (Σ a, Fin (d a)) ≃ Fin N}

theorem exists_lift_unipotent_radical (u : GL (Fin N) 𝓀[k]) (hu : u ∈ unipRad 𝓀[k] e) :
    ∃ g : KO k (Fin N), redK k (Fin N) g = u ∧ (g : GL (Fin N) k) ∈ unipRad k e := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : 𝓀[k] → 𝒪[k], ∀ x, IsLocalRing.residue 𝒪[k] (r x) = x :=
    ⟨Function.surjInv IsLocalRing.residue_surjective, Function.surjInv_eq IsLocalRing.residue_surjective⟩
  let M : Matrix (Fin N) (Fin N) 𝒪[k] := fun a b =>
    if blk e a < blk e b then r ((u : Matrix (Fin N) (Fin N) 𝓀[k]) a b)
    else (1 : Matrix (Fin N) (Fin N) 𝒪[k]) a b
  have hM : ∀ a b, ¬ blk e a < blk e b → M a b = (1 : Matrix (Fin N) (Fin N) 𝒪[k]) a b := fun a b h => by
    simp only [M, ite_eq_right h]
  have hT : M.BlockTriangular (blk e) := fun a b hab => by
    rw [hM a b (not_lt.2 hab.le), Matrix.one_apply_ne]
    rintro rfl
    exact lt_irrefl _ hab
  have hdet : M.det = 1 := by
    rw [hT.det_fintype]
    refine Finset.prod_eq_one fun c _ => ?_
    have : M.toSquareBlock (blk e) c = 1 := by
      refine Matrix.ext fun ⟨x, hx⟩ ⟨y, hy⟩ => ?_
      show M x y = _
      rw [hM x y (by rw [hx, hy]; exact lt_irrefl _), Matrix.one_apply, Matrix.one_apply]
      simp [Subtype.ext_iff]
    rw [this, Matrix.det_one]
  have hU : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).2 (by rw [hdet]; exact isUnit_one)
  let g : GL (Fin N) k := Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) hU.unit
  have hgK : g ∈ KO k (Fin N) := MonoidHom.mem_range.2 ⟨hU.unit, rfl⟩
  refine ⟨⟨g, hgK⟩, ?_, ?_⟩
  · refine Units.ext (Matrix.ext fun a b => ?_)
    rw [redK_apply]
    show IsLocalRing.residue 𝒪[k] (M a b) = _
    by_cases h : blk e a < blk e b
    · simp only [M, ite_eq_left h, hr]
    · rw [hM a b h, (mem_unipotent_radical_iff_alt.1 hu) a b h, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
  · rw [mem_unipotent_radical_iff_alt]
    intro a b h
    show algebraMap 𝒪[k] k (M a b) = _
    rw [hM a b h, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem lift_mem_twisted_kernel {W V : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (GL (Fin N) 𝓀[k]) W) (ρ : Representation ℂ (GL (Fin N) k) V) (j : W →ₗ[ℂ] V)
    (hj : ∀ (g : KO k (Fin N)) (v : W), j (τ (redK k (Fin N) g) v) = ρ (g : GL (Fin N) k) (j v))
    (hCF : ∀ v : W, (∀ u ∈ unipRad 𝓀[k] e, τ u v = v) → v = 0) (x : W) :
    j x ∈ twKer ρ (unipRad k e) 1 := by
  classical
  have : Finite (GL (Fin N) 𝓀[k]) :=
    Finite.of_injective (fun g : GL (Fin N) 𝓀[k] => fun i j => (g : Matrix (Fin N) (Fin N) 𝓀[k]) i j)
      (fun a b h => Units.ext (Matrix.ext fun i j => congrFun (congrFun h i) j))
  let _ : Fintype (unipRad 𝓀[k] e) := Fintype.ofFinite _
  let y : W := ∑ u : unipRad 𝓀[k] e, τ u x
  have hy : y = 0 := by
    apply hCF
    intro u hu
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [y, map_sum]
    rw [show (∑ v : unipRad 𝓀[k] e, τ u (τ v x)) =
        ∑ v : unipRad 𝓀[k] e, τ ((⟨u, hu⟩ * v : unipRad 𝓀[k] e) : GL (Fin N) 𝓀[k]) x from
      Finset.sum_congr rfl fun v _ => by rw [Subgroup.coe_mul, map_mul, mul_apply_eq_comp]]
    exact Fintype.sum_equiv (Equiv.mulLeft (⟨u, hu⟩ : unipRad 𝓀[k] e)) _ _ fun v => rfl
  choose lf hlf using fun u : unipRad 𝓀[k] e => exists_lift_unipotent_radical (e := e) u.1 u.2
  have hsum : ∑ u : unipRad 𝓀[k] e, (j x - ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x)) ∈
      twKer ρ (unipRad k e) 1 := by
    refine Submodule.sum_mem _ fun u _ => ?_
    have : ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x) - j x ∈ twKer ρ (unipRad k e) 1 :=
      Submodule.subset_span ⟨⟨_, (hlf u).2⟩, j x, by simp⟩
    rw [← neg_sub]
    exact neg_mem this
  have h2 : ∑ u : unipRad 𝓀[k] e, (j x - ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x)) =
      (Fintype.card (unipRad 𝓀[k] e) : ℂ) • j x := by
    rw [Finset.sum_sub_distrib]
    have : ∑ u : unipRad 𝓀[k] e, ρ ((lf u : KO k (Fin N)) : GL (Fin N) k) (j x) = j y := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [y, map_sum]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [← hj, (hlf u).1]
    rw [this, hy, map_zero, sub_zero, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  rw [h2] at hsum
  have hc : (Fintype.card (unipRad 𝓀[k] e) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have := (twKer ρ (unipRad k e) 1).smul_mem (Fintype.card (unipRad 𝓀[k] e) : ℂ)⁻¹ hsum
  rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this

end Local

end L5


open L5 in
theorem st5 : St5 := by
  intro k W _ _ _ _ _ _ _ n τ hτ π j hj
  refine ⟨π.smooth, fun s d e hne => ?_⟩
  have hCF := hτ s d e (unipotent_radical_ne_bot (exists_block_lt_of_ne_bot hne))
  let S : Submodule ℂ π.V := Submodule.span ℂ {v | ∃ h x, v = π.ρ h (j x)}
  have hSst : ∀ h v, v ∈ S → π.ρ h v ∈ S := by
    intro h v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
      obtain ⟨h', x, rfl⟩ := hv
      exact Submodule.subset_span ⟨h * h', x, by rw [map_mul, mul_apply_eq_comp]⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hS0 : S ≠ ⊥ := by
    obtain ⟨x, hx⟩ := exists_ne (0 : W)
    intro hb
    have hm : j x ∈ S := Submodule.subset_span ⟨1, x, by simp⟩
    rw [hb, Submodule.mem_bot] at hm
    exact hx (hj.1 (hm.trans (map_zero j).symm))
  have hST : S ≤ twKer π.ρ (unipRad k e) 1 := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, x, rfl⟩
    obtain ⟨p, w, hw, rfl⟩ := GlobalTheory.SmGL.MultiIrr.exists_parab_mul e h
    rw [map_mul, mul_apply_eq_comp,
      show π.ρ w (j x) = j (τ (redK k (Fin n) ⟨w, hw⟩) x) from (hj.2 ⟨w, hw⟩ x).symm]
    exact twKer_le_comap π.ρ _ p (parab_le_normalizer k e p.2) (lift_mem_twisted_kernel τ π.ρ j hj.2 hCF _)
  have htop : S = ⊤ := by
    let S' : Subrepresentation π.ρ := ⟨S, fun x v hv => hSst x v hv⟩
    rcases π.irr.eq_bot_or_eq_top S' with h | h
    · exact absurd (congrArg Subrepresentation.toSubmodule h) hS0
    · exact congrArg Subrepresentation.toSubmodule h
  rw [htop, top_le_iff] at hST
  show Subsingleton (_ ⧸ twKer π.ρ (unipRad k e) 1)
  rw [Submodule.Quotient.subsingleton_iff]
  exact hST

end PositivityTheory.Rg.DzCount

end
end

namespace PositivityTheory.Rg.DzCount

theorem depth_zero_intermediate_holds : St3 := st3 st1a st1b st2 st3a

theorem depth_zero_count_holds : St8a := st8a st4 st5 B.st6 st7

end PositivityTheory.Rg.DzCount
