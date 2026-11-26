module

public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsChOfTors

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalSeriesJacobianChainRuleLinearPart
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalSeriesJacobianChainRuleLinearPart
set_option autoImplicit false
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem hs {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (h : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => h q.1 q.2)

private theorem sub_sub' {R : Type} [CommRing R] {m n k d e f : ℕ} (a : Fin m → Fin d → PS R n e)
    (b : Fin n → Fin e → PS R k f) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0)
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) (u : PS R m d) :
    sub b (sub a u) = sub (fun i j => sub b (a i j)) u :=
  MvPowerSeries.subst_comp_subst_apply (hs a ha) (hs b hb) u

private theorem sub_X {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (q : Fin m × Fin d) :
    sub a (MvPowerSeries.X q) = a q.1 q.2 :=
  MvPowerSeries.subst_X (hs a ha) q

private theorem sub_mul' {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (u v : PS R m d) :
    sub a (u * v) = sub a u * sub a v :=
  MvPowerSeries.subst_mul (hs a ha) u v

private theorem const_sub {R : Type} [CommRing R] {m n d e : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (u : PS R m d) :
    MvPowerSeries.constantCoeff (sub a u) = MvPowerSeries.constantCoeff u := by
  obtain ⟨-, -, h3, -, -, h6⟩ := nv_calculus R R (RingHom.id R) n e 0 (fun _ _ => IsNilpotent.zero)
  obtain ⟨-, -, -, -, -, h6'⟩ := nv_calculus R R (RingHom.id R) m d 0 (fun _ _ => IsNilpotent.zero)
  have h6 := h6 (by simp)
  have h6' := h6' (by simp)
  have h := h3 m d a u ha
  have e0 : (fun i j => nv (RingHom.id R) (a i j) 0) = 0 := by
    funext i j
    rw [h6, ha]; simp
  rw [e0, h6, h6'] at h
  simpa using h

private theorem coeff_sub {R : Type} [CommRing R] {d e : ℕ} (φ : Fin e → PS R 1 d)
    (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) (u : PS R 1 e) (k : Fin d) :
    dl (sub ![φ] u) k = ∑ i, lin φ i k * dl u i := by
  classical
  have hφ' : ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → _) i j) = 0 := by
    intro i j; fin_cases i; exact hφ j
  let s : R →+* TrivSqZeroExt R R := algebraMap R _
  let a : Fin 1 → Fin d → TrivSqZeroExt R R := fun _ j => TrivSqZeroExt.inr (if j = k then 1 else 0)
  let b : Fin 1 → Fin e → TrivSqZeroExt R R := fun _ j => TrivSqZeroExt.inr (lin φ j k)
  have hn : ∀ x : R, IsNilpotent (TrivSqZeroExt.inr x : TrivSqZeroExt R R) := fun x =>
    ⟨2, by rw [pow_two, TrivSqZeroExt.inr_mul_inr]⟩
  obtain ⟨-, -, h3, -, -, h6⟩ := nv_calculus R _ s 1 d a (fun _ _ => hn _)
  obtain ⟨-, -, -, -, -, h6'⟩ := nv_calculus R _ s 1 e b (fun _ _ => hn _)
  have h6 := h6 (fun _ _ _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have h6' := h6' (fun _ _ _ _ => TrivSqZeroExt.inr_mul_inr _ _ _)
  have h := h3 1 e ![φ] u hφ'
  have e0 : (fun i j => nv s ((![φ] : Fin 1 → _) i j) a) = b := by
    funext i j
    fin_cases i
    rw [h6, hφ']
    ext
    · have hf : ∀ (t : Finset (Fin 1 × Fin d)) (g : Fin 1 × Fin d → TrivSqZeroExt R R),
          (∑ q ∈ t, g q).fst = ∑ q ∈ t, (g q).fst := fun t g =>
        map_sum (TrivSqZeroExt.fstHom R R R) g t
      simp [s, a, b, hf, apply_ite TrivSqZeroExt.fst]
    · simp [s, a, b, TrivSqZeroExt.snd_sum, Fintype.sum_prod_type, lin, TrivSqZeroExt.algebraMap_eq_inl]
  rw [e0, h6, h6'] at h
  have h2 := congrArg TrivSqZeroExt.snd h
  simpa [s, a, b, TrivSqZeroExt.snd_sum, Fintype.sum_prod_type, TrivSqZeroExt.algebraMap_eq_inl, dl,
    mul_comm] using h2

theorem chain_rule_lin : ∀ (R : Type) [CommRing R] (d e : ℕ) (φ : Fin e → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∀ u : PS R 1 e, dl (sub ![φ] u) = (lin φ)ᵀ *ᵥ dl u ∧ MvPowerSeries.constantCoeff (sub ![φ] u) = MvPowerSeries.constantCoeff u) ∧ (∀ (m : ℕ) (ψ : Fin m → PS R 1 e), lin (fun j => sub ![φ] (ψ j)) = lin ψ * lin φ) ∧ ∀ (F : FGLaw R d) (F' : FGLaw R e), IsHomF F.F F'.F φ → ∀ u, IsCh F'.F u → IsCh F.F (sub ![φ] u) := by
  intro R _ d e φ hφ
  have one : ∀ {n f g : ℕ} (x : Fin g → PS R n f), (∀ j, MvPowerSeries.constantCoeff (x j) = 0) →
      ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![x] : Fin 1 → _) i j) = 0 := by
    intro n f g x hx i j; fin_cases i; exact hx j
  have two : ∀ {n f g : ℕ} (x y : Fin g → PS R n f), (∀ j, MvPowerSeries.constantCoeff (x j) = 0) →
      (∀ j, MvPowerSeries.constantCoeff (y j) = 0) →
      ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff ((![x, y] : Fin 2 → _) i j) = 0 := by
    intro n f g x y hx hy i j; fin_cases i
    · exact hx j
    · exact hy j
  have hφ' := one φ hφ
  refine ⟨fun u => ⟨?_, const_sub _ hφ' u⟩, fun m ψ => ?_, fun F F' hF u hu => ⟨?_, ?_⟩⟩
  · funext k
    rw [coeff_sub φ hφ u k]
    rfl
  · ext j k
    have := coeff_sub φ hφ (ψ j) k
    rw [Matrix.mul_apply]
    refine this.trans (Finset.sum_congr rfl fun i _ => mul_comm _ _)
  · rw [const_sub _ hφ' u, hu.1]
  · have hpt : ∀ (f : ℕ) (i : Fin 2) j, MvPowerSeries.constantCoeff (pt R (n := 2) f i j) = 0 :=
      fun f i j => MvPowerSeries.constantCoeff_X _
    have hid : ∀ (f : ℕ) (G : Fin f → PS R 2 f), addOf G (pt R (n := 2) f 0) (pt R (n := 2) f 1) = G := by
      intro f G
      funext i
      have : (fun p : Fin 2 × Fin f => (![pt R (n := 2) f 0, pt R (n := 2) f 1] : Fin 2 → _) p.1 p.2)
          = MvPowerSeries.X := by
        funext ⟨p, q⟩
        fin_cases p <;> rfl
      simp only [addOf, ev]
      rw [this, MvPowerSeries.subst_self]
      rfl
    have hu2 := hu.2
    rw [hid] at hu2 ⊢
    set x : Fin e → PS R 2 d := fun i => sub ![pt R (n := 2) d 0] (φ i) with hx
    set y : Fin e → PS R 2 d := fun i => sub ![pt R (n := 2) d 1] (φ i) with hy
    have hx0 : ∀ j, MvPowerSeries.constantCoeff (x j) = 0 := fun j => by
      rw [hx]; dsimp only; rw [const_sub _ (one _ (hpt d 0)), hφ]
    have hy0 : ∀ j, MvPowerSeries.constantCoeff (y j) = 0 := fun j => by
      rw [hy]; dsimp only; rw [const_sub _ (one _ (hpt d 1)), hφ]
    have hxy := two x y hx0 hy0
    have h : sub ![x, y] (sub ![F'.F] u) =
        sub ![x, y] (sub ![pt R (n := 2) e 0] u * sub ![pt R (n := 2) e 1] u) := congrArg _ hu2
    rw [sub_mul' _ hxy, sub_sub' _ _ (one _ F'.const) hxy, sub_sub' _ _ (one _ (hpt e 0)) hxy,
      sub_sub' _ _ (one _ (hpt e 1)) hxy] at h
    change sub ![F.F] (sub ![φ] u) =
      sub ![pt R (n := 2) d 0] (sub ![φ] u) * sub ![pt R (n := 2) d 1] (sub ![φ] u)
    rw [sub_sub' _ _ hφ' (one _ F.const), sub_sub' _ _ hφ' (one _ (hpt d 0)),
      sub_sub' _ _ hφ' (one _ (hpt d 1))]
    have e1 : (fun i j => sub ![F.F] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![F'.F] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact hF.2 j
    have e2 : (fun i j => sub ![pt R (n := 2) d 0] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![pt R (n := 2) e 0] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact (sub_X _ hxy (0, j)).symm
    have e3 : (fun i j => sub ![pt R (n := 2) d 1] ((![φ] : Fin 1 → _) i j)) =
        fun i j => sub ![x, y] ((![pt R (n := 2) e 1] : Fin 1 → _) i j) := by
      funext i j; fin_cases i; exact (sub_X _ hxy (1, j)).symm
    rw [e1, e2, e3]
    exact h

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.FormalSeriesJacobianChainRuleLinearPartStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalSeriesJacobian_chain_rule_linearPart : ∀ (R : Type) [CommRing R] (d e : ℕ) (φ : Fin e → PS R 1 d), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → (∀ u : PS R 1 e, dl (sub ![φ] u) = (lin φ)ᵀ *ᵥ dl u ∧ MvPowerSeries.constantCoeff (sub ![φ] u) = MvPowerSeries.constantCoeff u) ∧ (∀ (m : ℕ) (ψ : Fin m → PS R 1 e), lin (fun j => sub ![φ] (ψ j)) = lin ψ * lin φ) ∧ ∀ (F : FGLaw R d) (F' : FGLaw R e), IsHomF F.F F'.F φ → ∀ u, IsCh F'.F u → IsCh F.F (sub ![φ] u) := by
  first | exact @GlobalTheory.ChF.chain_rule_lin | exact GlobalTheory.ChF.chain_rule_lin | (intros; apply GlobalTheory.ChF.chain_rule_lin <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GmLawCharsMul
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ChF
open MvPowerSeries

private lemma gm_hs {R : Type} [CommRing R] {m n d : ℕ} (a : Fin m → Pt R n d)
    (h : ∀ j i, constantCoeff (a j i) = 0) :
    HasSubst (fun p : Fin m × Fin d => a p.1 p.2) :=
  hasSubst_of_constantCoeff_zero (fun p => h p.1 p.2)

private lemma ev_gm {R : Type} [CommRing R] {n r : ℕ} (a b : Pt R n r)
    (ha : ∀ i, constantCoeff (a i) = 0) (hb : ∀ i, constantCoeff (b i) = 0) (i : Fin r) :
    ev ![a, b] (gmF R r i) = a i + b i + a i * b i := by
  have h := gm_hs (m := 2) ![a, b] (by
    intro j i
    fin_cases j
    · exact ha i
    · exact hb i)
  unfold ev gmF
  rw [subst_add h, subst_add h, subst_mul h, subst_X h, subst_X h]
  rfl

private lemma ev_ch {R : Type} [CommRing R] {n r : ℕ} (a : Pt R n r)
    (ha : ∀ i, constantCoeff (a i) = 0) (i : Fin r) :
    ev ![a] (1 + X ((0 : Fin 1), i) : PS R 1 r) = 1 + a i := by
  have h := gm_hs (m := 1) ![a] (by
    intro j i
    fin_cases j
    exact ha i)
  have h1 := ev_one ![a]
  unfold ev at h1 ⊢
  rw [subst_add h, h1, subst_X h]
  rfl

private lemma gm_const {R : Type} [CommRing R] {r : ℕ} (i : Fin r) :
    constantCoeff (gmF R r i) = 0 := by
  simp [gmF]

private lemma pt_const {R : Type} [CommRing R] {n r : ℕ} (j : Fin n) (i : Fin r) :
    constantCoeff (pt R r j i) = 0 := by
  simp [pt]

private def gmLaw (R : Type) [CommRing R] (r : ℕ) : FGLaw R r where
  F := gmF R r
  const := gm_const
  unit i := by
    rw [ev_gm _ _ (by simp) (pt_const _)]
    simp [pt]
  comm i := by
    rw [ev_gm _ _ (pt_const _) (pt_const _)]
    simp only [pt, gmF]
    ring
  assoc i := by
    have h : ∀ (j k : Fin 3) (l : Fin r), constantCoeff (ev (n := 3) ![pt R r j, pt R r k] (gmF R r l)) = 0 := by
      intro j k l
      rw [ev_gm _ _ (pt_const _) (pt_const _)]
      simp [pt]
    rw [ev_gm _ _ (h _ _) (pt_const _), ev_gm _ _ (pt_const _) (h _ _),
      ev_gm _ _ (pt_const _) (pt_const _), ev_gm _ _ (pt_const _) (pt_const _)]
    ring

private lemma mulF_gm (R : Type) [CommRing R] (r : ℕ) (N : ℕ) :
    ∀ i : Fin r, mulF (gmF R r) N i = (1 + X ((0 : Fin 1), i)) ^ N - 1 := by
  induction N with
  | zero => intro i; simp [mulF]
  | succ N ih =>
    intro i
    simp only [mulF, addOf]
    rw [ev_gm _ _ (by intro l; rw [ih]; simp) (pt_const _), ih]
    simp only [pt]
    ring

theorem gmLaw_chars_mul : ∀ (R : Type) [CommRing R] (r : ℕ), (∃ Gl : FGLaw R r, Gl.F = gmF R r) ∧ (∀ i : Fin r, IsCh (gmF R r) (1 + MvPowerSeries.X ((0 : Fin 1), i)) ∧ dl (1 + MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 r) = Pi.single i 1) ∧ ∀ (N : ℕ) (i : Fin r), mulF (gmF R r) N i = (1 + MvPowerSeries.X ((0 : Fin 1), i)) ^ N - 1 := by
  intro R _ r
  refine ⟨⟨gmLaw R r, rfl⟩, fun i => ⟨⟨by simp, ?_⟩, ?_⟩, mulF_gm R r⟩
  · have hA : addOf (gmF R r) (pt R (n := 2) r 0) (pt R (n := 2) r 1) = gmF R r := by
      funext l
      unfold addOf
      rw [ev_gm _ _ (pt_const _) (pt_const _)]
      rfl
    rw [hA, ev_ch _ gm_const, ev_ch _ (pt_const _), ev_ch _ (pt_const _)]
    simp only [pt, gmF]
    ring
  · classical
    funext j
    simp only [dl, map_add (f := _), coeff_one, coeff_X, Finsupp.single_eq_zero, one_ne_zero, if_false, zero_add,
      Finsupp.single_left_inj (one_ne_zero : (1 : ℕ) ≠ 0), Prod.mk.injEq, true_and, Pi.single_apply]

end GlobalTheory.ChF
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalTorusCharacterLiftToLaw
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MultiplicativeFormalGroupLawPowerPTorsionFiniteF
section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MultiplicativeFormalGroupLawPowerPTorsionFiniteF
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF GlobalTheory.ChF

namespace GlobalTheory.ChF

private theorem coeff_eq_zero_of_roots {O : Type} [CommRing O] [IsDomain O] {σ : Type} [Fintype σ]
    [DecidableEq σ] {N : ℕ} {ζ : O} (hζ : IsPrimitiveRoot ζ N) (c : (σ → Fin N) → O)
    (h : ∀ b : σ → ℕ, ∑ a : σ → Fin N, c a * ∏ i, (ζ ^ b i) ^ (a i : ℕ) = 0) : ∀ a, c a = 0 := by
  let χ : (σ → Fin N) → (Multiplicative (σ → ℕ) →* O) := fun a =>
    { toFun := fun b => ∏ i, (ζ ^ (Multiplicative.toAdd b) i) ^ (a i : ℕ)
      map_one' := by simp
      map_mul' := fun b b' => by
        simp [pow_add, mul_pow, Finset.prod_mul_distrib] }
  have hinj : Function.Injective χ := by
    intro a a' haa
    funext j
    have h1 := DFunLike.congr_fun haa (Multiplicative.ofAdd (Pi.single j 1))
    have key : ∀ e : σ → Fin N, χ e (Multiplicative.ofAdd (Pi.single j 1)) = ζ ^ (e j : ℕ) := by
      intro e
      show ∏ i, (ζ ^ (Pi.single j 1 : σ → ℕ) i) ^ (e i : ℕ) = _
      rw [Finset.prod_eq_single j]
      · simp
      · intro i _ hij
        simp [Pi.single_eq_of_ne hij]
      · simp
    rw [key, key] at h1
    exact Fin.ext (hζ.pow_inj (a j).2 (a' j).2 h1)
  have hli := (linearIndependent_monoidHom (Multiplicative (σ → ℕ)) O).comp χ hinj
  rw [Fintype.linearIndependent_iff] at hli
  apply hli c
  funext b
  have := h (Multiplicative.toAdd b)
  simpa [Finset.sum_apply, χ] using this

private theorem map_coe_mem_span {O Q : Type} [CommRing O] [CommRing Q] [Algebra O Q] {σ : Type}
    [Fintype σ] [DecidableEq σ] {N : ℕ} (hN : 0 < N) (ψ : MvPowerSeries σ O →ₐ[O] Q)
    (hy : ∀ i, (1 + ψ (MvPowerSeries.X i)) ^ N = 1) (P : MvPolynomial σ O) :
    ψ (P : MvPowerSeries σ O) ∈ Submodule.span O
      (Set.range fun a : σ → Fin N => ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (a i : ℕ)) := by
  set S := Submodule.span O
      (Set.range fun a : σ → Fin N => ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (a i : ℕ)) with hS
  have hmon : ∀ e : σ → ℕ, ∏ i, (1 + ψ (MvPowerSeries.X i)) ^ (e i) ∈ S := by
    intro e
    apply Submodule.subset_span
    refine ⟨fun i => ⟨e i % N, Nat.mod_lt _ hN⟩, ?_⟩
    refine Finset.prod_congr rfl fun i _ => ?_
    exact (pow_eq_pow_mod (e i) (hy i)).symm
  have hmul : ∀ j, ∀ q ∈ S, q * (1 + ψ (MvPowerSeries.X j)) ∈ S := by
    intro j q hq
    induction hq using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      have := hmon (fun i => (a i : ℕ) + (Pi.single j 1 : σ → ℕ) i)
      simp only [pow_add, Finset.prod_mul_distrib] at this
      rwa [Finset.prod_eq_single j (f := fun i =>
        (1 + ψ (MvPowerSeries.X i)) ^ (Pi.single j 1 : σ → ℕ) i)
        (fun i _ hij => by simp [Pi.single_eq_of_ne hij]) (by simp), Pi.single_eq_same, pow_one] at this
    | zero => simp
    | add x y _ _ hx hy => rw [add_mul]; exact S.add_mem hx hy
    | smul a x _ hx => rw [smul_mul_assoc]; exact S.smul_mem a hx
  induction P using MvPolynomial.induction_on with
  | C a =>
    have h1 : (1 : Q) ∈ S := by simpa using hmon 0
    have : ψ ((MvPolynomial.C a : MvPolynomial σ O) : MvPowerSeries σ O) = a • (1 : Q) := by
      rw [MvPolynomial.coe_C, ← Algebra.algebraMap_eq_smul_one]
      exact ψ.commutes a
    rw [this]
    exact S.smul_mem a h1
  | add f g hf hg => rw [MvPolynomial.coe_add, map_add (f := _)]; exact S.add_mem hf hg
  | mul_X f j hf =>
    rw [MvPolynomial.coe_mul, MvPolynomial.coe_X, map_mul]
    have := S.sub_mem (hmul j _ hf) hf
    convert this using 1
    ring

private theorem exists_pow_eq {A : Type} [CommRing A] {p : ℕ} (hp : p.Prime) (k : ℕ) (x : A) :
    ∃ s : A, x ^ p ^ k = ((1 + x) ^ p ^ k - 1) + (p : A) * s := by
  obtain ⟨s, hs⟩ := exists_add_pow_prime_pow_eq hp (1 : A) x k
  refine ⟨-(x * s), ?_⟩
  rw [hs]
  ring

private theorem exists_primitiveRoot_integers {C : Type} [Field C] [IsAlgClosed C] [CharZero C]
    {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) {N : ℕ}
    (hN : 0 < N) : ∃ ζ : O, IsPrimitiveRoot ζ N := by
  haveI : NeZero N := ⟨hN.ne'⟩
  obtain ⟨z, hz⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot C N
  have hvz : v z ≤ 1 := by
    have : v z ^ N = 1 := by rw [← map_pow, hz.pow_eq_one, map_one]
    exact ((pow_eq_one_iff_of_nonneg zero_le hN.ne').1 this).le
  obtain ⟨ζ, rfl⟩ := hv.exists_of_le_one hvz
  exact ⟨ζ, hz.of_map_of_injective hv.hom_inj⟩

theorem fh_gmF : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O →
    ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (r : ℕ), FH p (gmF O r) := by
  intro p hp C _ _ _ v O _ _ hv _ hc r k
  classical
  haveI : IsDomain O := hv.hom_inj.isDomain _
  have hN : 0 < p ^ k := pow_pos hp.out.pos k
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_integers hv hN
  have hmul := (gmLaw_chars_mul O r).2.2 (p ^ k)
  set I : Ideal (PS O 1 r) := Ideal.span (Set.range (mulF (gmF O r) (p ^ k))) with hI
  have hrel : ∀ i : Fin 1 × Fin r, (1 + MvPowerSeries.X i : PS O 1 r) ^ p ^ k - 1 ∈ I := by
    rintro ⟨i0, i⟩
    obtain rfl : i0 = 0 := Subsingleton.elim _ _
    exact Ideal.subset_span ⟨i, hmul i⟩

  obtain ⟨M, hM⟩ : ∃ M : ℕ, Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin r → PS O 1 r)) ^ M ≤
      I ⊔ Ideal.map (MvPowerSeries.C : O →+* PS O 1 r) (Ideal.span {(p : O)}) := by
    apply Ideal.exists_pow_le_of_le_radical_of_fg _ (Submodule.fg_span (Set.finite_range _))
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    obtain ⟨s, hs⟩ := exists_pow_eq hp.out k (MvPowerSeries.X i : PS O 1 r)
    refine ⟨p ^ k, ?_⟩
    rw [hs]
    refine Ideal.add_mem _ (Ideal.mem_sup_left (hrel i)) (Ideal.mem_sup_right (Ideal.mul_mem_right _ _ ?_))
    rw [← map_natCast (MvPowerSeries.C : O →+* PS O 1 r) p]
    exact Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton_self _)
  let π : PS O 1 r →ₐ[O] (PS O 1 r ⧸ I) := Ideal.Quotient.mkₐ O I
  let m : (Fin 1 × Fin r → Fin (p ^ k)) → (PS O 1 r ⧸ I) :=
    fun a => ∏ i, (1 + π (MvPowerSeries.X i)) ^ (a i : ℕ)
  have hspan : ∀ q : PS O 1 r ⧸ I, q ∈ Submodule.span O (Set.range m) := by
    intro q
    obtain ⟨g, rfl⟩ := Ideal.Quotient.mk_surjective q
    obtain ⟨P, -, hP⟩ := GlobalTheory.CompleteBaseChange.exists_polynomial_totalDegree_le_sub_mem O
      (Ideal.span {(p : O)}) (Submodule.fg_span (Set.finite_singleton _)) hc (Fin 1 × Fin r) (Fin r)
      (mulF (gmF O r) (p ^ k)) M hM g
    rw [Ideal.Quotient.eq.2 hP]
    refine map_coe_mem_span hN π (fun i => ?_) P
    have h0 : π ((1 + MvPowerSeries.X i : PS O 1 r) ^ p ^ k - 1) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (hrel i)
    rw [map_sub, map_pow, map_add (f := _), map_one] at h0
    exact sub_eq_zero.1 h0

  have hpt : ∀ b : Fin 1 × Fin r → ℕ, ∃ φ : (PS O 1 r ⧸ I) →ₐ[O] O,
      ∀ i, φ (π (MvPowerSeries.X i)) = ζ ^ b i - 1 := by
    intro b
    have hone : ∀ i, (1 + (ζ ^ b i - 1)) ^ p ^ k - 1 = 0 := by
      intro i
      rw [add_sub_cancel, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow, sub_self]
    obtain ⟨ψ, hψ⟩ := (GlobalTheory.mvPowerSeries_eval_of_pow_mem O (Ideal.span {(p : O)}) (Fin 1 × Fin r)
      (fun i => ζ ^ b i - 1) (fun i => by
        obtain ⟨s, hs⟩ := exists_pow_eq hp.out k (ζ ^ b i - 1)
        refine ⟨p ^ k, ?_⟩
        rw [hs, hone, zero_add]
        exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))).1 hc O
    have hker : I ≤ RingHom.ker ψ := by
      rw [hI, Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      show ψ _ = 0
      rw [hmul, map_sub, map_pow, map_add (f := _), map_one, hψ]
      exact hone _
    exact ⟨Ideal.Quotient.liftₐ I ψ (fun a ha => hker ha), fun i => hψ i⟩
  have hsep : ∀ c : (Fin 1 × Fin r → Fin (p ^ k)) → O,
      (∀ φ : (PS O 1 r ⧸ I) →ₐ[O] O, φ (∑ a, c a • m a) = 0) → ∀ a, c a = 0 := by
    intro c hcφ
    refine coeff_eq_zero_of_roots hζ c fun b => ?_
    obtain ⟨φ, hφ⟩ := hpt b
    have := hcφ φ
    set_option synthInstance.maxHeartbeats 100000 in
      simpa only [map_sum, map_smul, m, map_prod, map_pow, map_add (f := _), map_one, hφ, add_sub_cancel,
      smul_eq_mul] using this
  have hli : LinearIndependent O m := by
    rw [Fintype.linearIndependent_iff]
    intro c h0
    exact hsep c fun φ => by rw [h0, map_zero]
  let B := Module.Basis.mk hli (fun q _ => hspan q)
  refine ⟨Module.Free.of_basis B, Module.Finite.of_basis B, fun q hq => ?_⟩
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 (hspan q)
  simp [hsep c hq]

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.MultiplicativeFormalGroupLawPowerPTorsionFiniteFStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.multiplicativeFormalGroupLawPower_pTorsion_finiteFree : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (r : ℕ), FH p (gmF O r) := by
  first | exact @GlobalTheory.ChF.fh_gmF | exact GlobalTheory.ChF.fh_gmF | (intros; apply GlobalTheory.ChF.fh_gmF <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.SubSurjectiveOfLinLeftInverse
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem isAdicComplete_germIdeal (R κ : Type) [CommRing R] [Finite κ] :
    IsAdicComplete (germIdeal κ R) (MvPowerSeries κ R) := by
  have h := (mem_sup_span_X_pow_iff_and_isAdicComplete R ⊥ κ).2 inferInstance
  rwa [Ideal.map_bot, bot_sup_eq, ← germIdeal_eq_span] at h

private theorem eq_zero_or_single {κ : Type} {e : κ →₀ ℕ} (he : e.degree < 2) :
    e = 0 ∨ ∃ k, e = Finsupp.single k 1 := by
  classical
  by_cases h0 : e = 0
  · exact Or.inl h0
  · right
    obtain ⟨k, hk⟩ := Finsupp.ne_iff.1 h0
    have hle : Finsupp.single k 1 ≤ e := by
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.2 hk
    obtain ⟨c, hc⟩ := exists_add_of_le hle
    have hd : e.degree = 1 + c.degree := by rw [hc, map_add (f := _), Finsupp.degree_single]
    have : c = 0 := (Finsupp.degree_eq_zero_iff c).1 (by omega)
    exact ⟨k, by rw [hc, this, add_zero]⟩

theorem sub_surjective_of_lin_leftInverse : ∀ (R : Type) [CommRing R] (d r : ℕ) (φ : Fin d → PS R 1 r) (A' : Matrix (Fin r) (Fin d) R), (∀ j, MvPowerSeries.constantCoeff (φ j) = 0) → A' * lin φ = 1 → Function.Surjective (fun f : PS R 1 d => sub ![φ] f) := by
  intro R _ d r φ A' h0 hA
  classical
  set a : Fin 1 × Fin d → PS R 1 r := fun q => (![φ] : Fin 1 → Fin d → PS R 1 r) q.1 q.2 with ha
  have ha' : ∀ q : Fin 1 × Fin d, a q = φ q.2 := by
    rintro ⟨i, j⟩
    fin_cases i
    rfl
  have hs : MvPowerSeries.HasSubst a :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => by rw [ha', h0]
  let f : PS R 1 d →+* PS R 1 r := (MvPowerSeries.substAlgHom (R := R) hs).toRingHom
  have hf : ∀ u, f u = sub ![φ] u := fun u => by
    change MvPowerSeries.substAlgHom hs u = MvPowerSeries.subst a u
    rw [MvPowerSeries.coe_substAlgHom]
  have hfX : ∀ q, f (MvPowerSeries.X q) = φ q.2 := fun q => by
    change MvPowerSeries.substAlgHom hs _ = _
    rw [MvPowerSeries.substAlgHom_X, ha']
  have hC1 := isAdicComplete_germIdeal R (Fin 1 × Fin d)
  have hC2 := isAdicComplete_germIdeal R (Fin 1 × Fin r)
  have hmap : (germIdeal (Fin 1 × Fin d) R).map f = germIdeal (Fin 1 × Fin r) R := by
    apply le_antisymm
    · rw [germIdeal_eq_span, Ideal.map_span, Ideal.span_le]
      rintro _ ⟨_, ⟨q, rfl⟩, rfl⟩
      rw [hfX]
      exact RingHom.mem_ker.2 (h0 _)
    · refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := germIdeal (Fin 1 × Fin r) R) ?_
        (IsAdicComplete.le_jacobson_bot _) ?_
      · rw [germIdeal_eq_span]
        exact Submodule.fg_span (Set.finite_range _)
      · rw [smul_eq_mul, ← pow_two]
        conv_lhs => rw [germIdeal_eq_span]
        rw [Ideal.span_le]
        rintro _ ⟨⟨i0, i⟩, rfl⟩
        obtain rfl : i0 = 0 := Subsingleton.elim _ _
        have h1 : ∑ j, A' i j • φ j ∈ (germIdeal (Fin 1 × Fin d) R).map f := by
          refine Ideal.sum_mem _ fun j _ => Submodule.smul_of_tower_mem _ _ ?_
          rw [← hfX (0, j)]
          exact Ideal.mem_map_of_mem _ (X_mem_germIdeal _)
        have h2 : (MvPowerSeries.X ((0 : Fin 1), i) : PS R 1 r) - ∑ j, A' i j • φ j ∈
            germIdeal (Fin 1 × Fin r) R ^ 2 := by
          refine mem_germIdeal_pow_iff.2 fun e he => ?_
          rcases eq_zero_or_single he with rfl | ⟨⟨k0, k⟩, rfl⟩
          · simp [h0]
          · obtain rfl : k0 = 0 := Subsingleton.elim _ _
            have h3 := congrFun (congrFun hA i) k
            rw [Matrix.mul_apply, Matrix.one_apply] at h3
            simp only [lin, Matrix.of_apply] at h3
            set_option synthInstance.maxHeartbeats 100000 in
              rw [map_sub, map_sum]
            simp only [map_smul, smul_eq_mul]
            rw [h3, MvPowerSeries.coeff_X]
            simp [Finsupp.single_left_inj, eq_comm]
        have h4 := Submodule.add_mem_sup h1 h2
        rwa [add_sub_cancel] at h4
  have hsurj : Function.Surjective f := by
    have : IsHausdorff ((germIdeal (Fin 1 × Fin d) R).map f) (PS R 1 r) := by
      rw [hmap]
      exact hC2.toIsHausdorff
    refine surjective_of_mk_map_comp_surjective (I := germIdeal (Fin 1 × Fin d) R) f fun y => ?_
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨MvPowerSeries.C (MvPowerSeries.constantCoeff y), ?_⟩
    have h5 : f (MvPowerSeries.C (MvPowerSeries.constantCoeff y)) =
        MvPowerSeries.C (MvPowerSeries.constantCoeff y) :=
      (MvPowerSeries.substAlgHom (R := R) hs).commutes _
    rw [RingHom.comp_apply, h5, Ideal.Quotient.eq, hmap]
    exact RingHom.mem_ker.2 (by simp)
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨x, (hf x).symm.trans hx⟩

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsAddUnitOfPow
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CharExt

private theorem isAddUnit_of_pow {M : Type} [AddCommMonoid M] {p : ℕ} (hp : p ≠ 0) {a : M}
    (h : ∃ k, p ^ k • a = 0) : IsAddUnit a := by
  obtain ⟨k, hk⟩ := h
  have h1 : p ^ k = (p ^ k - 1) + 1 := by
    have : 0 < p ^ k := Nat.pos_of_ne_zero (pow_ne_zero _ hp)
    omega
  rw [h1, add_nsmul, one_nsmul, add_comm] at hk
  exact ⟨⟨a, (p ^ k - 1) • a, hk, by rw [add_comm]; exact hk⟩, rfl⟩

private theorem extend_group {A B : Type} [AddCommGroup A] [AddCommGroup B] (j : A →+ B)
    (hj : Function.Injective j) (C : Type) [Field C] [IsAlgClosed C]
    (χ : A →+ Additive Cˣ) : ∃ κ : B →+ Additive Cˣ, ∀ a, κ (j a) = χ a := by
  classical
  have hsurj : ∀ n : ℕ, n ≠ 0 → ∀ x : Additive Cˣ, ∃ y : Additive Cˣ, n • y = x := by
    intro n hn x
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((Additive.toMul x : Cˣ) : C)
      (Nat.pos_of_ne_zero hn)
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_pow hn] at hz
      exact (Additive.toMul x : Cˣ).ne_zero hz.symm
    refine ⟨Additive.ofMul (Units.mk0 z hz0), ?_⟩
    apply Additive.toMul.injective
    ext
    simpa using hz
  letI : DivisibleBy (Additive Cˣ) ℕ :=
    divisibleByOfSMulRightSurj (Additive Cˣ) ℕ (fun {n} hn x => hsurj n hn x)
  letI : DivisibleBy (Additive Cˣ) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨κ, hκ⟩ := (Module.Baer.of_divisible (Additive Cˣ)).extension_property_addMonoidHom
    j hj χ
  exact ⟨κ, fun a => DFunLike.congr_fun hκ a⟩

theorem exists_extension : ∀ (M M' : Type) [AddCommMonoid M] [AddCommMonoid M'] (j : M' →+ M), Function.Injective j → ∀ (C : Type) [Field C] [IsAlgClosed C] (p : ℕ), p ≠ 0 → ∀ χ : M' → Cˣ, (∀ a b, χ (a + b) = χ a * χ b) → ∃ κ : M → Cˣ, (∀ a b, (∃ k, p ^ k • a = 0) → (∃ k, p ^ k • b = 0) → κ (a + b) = κ a * κ b) ∧ κ 0 = 1 ∧ ∀ a, (∃ k, p ^ k • a = 0) → κ (j a) = χ a := by
  intro M M' _ _ j hj C _ _ p hp χ hχ
  classical
  let χ' : AddUnits M' →+ Additive Cˣ := AddMonoidHom.mk' (fun u => Additive.ofMul (χ u.val))
    (fun a b => by rw [AddUnits.val_add, hχ]; rfl)
  have hj' : Function.Injective (AddUnits.map j) := by
    intro a b hab
    ext
    exact hj (congrArg AddUnits.val hab)
  obtain ⟨κ, hκ⟩ := extend_group (AddUnits.map j) hj' C χ'
  have key : ∀ u : AddUnits M,
      (if h : IsAddUnit u.val then Additive.toMul (κ h.addUnit) else 1) = Additive.toMul (κ u) := by
    intro u
    rw [dite_eq_left u.isAddUnit]
    congr 2
    ext
    exact IsAddUnit.addUnit_spec _
  refine ⟨fun a => if h : IsAddUnit a then Additive.toMul (κ h.addUnit) else 1, ?_, ?_, ?_⟩
  · intro a b ha hb
    obtain ⟨u, rfl⟩ := isAddUnit_of_pow hp ha
    obtain ⟨v, rfl⟩ := isAddUnit_of_pow hp hb
    have h3 := key (u + v)
    have h1 := key u
    have h2 := key v
    beta_reduce
    rw [h1, h2]
    refine Eq.trans h3 ?_
    rw [map_add (f := _)]; rfl
  · have := key 0
    refine Eq.trans this ?_
    rw [map_zero]; rfl
  · intro a ha
    obtain ⟨u, rfl⟩ := isAddUnit_of_pow hp ha
    have h1 := key (AddUnits.map j u)
    refine Eq.trans h1 ?_
    rw [hκ]; rfl

end GlobalTheory.CharExt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalTorusCharacterLiftToLaw
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF.Lift

section Subst
variable {R : Type} [CommRing R] {m n d e : ℕ}

private theorem hasSub (a : Fin m → Fin d → PS R n e) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) :
    MvPowerSeries.HasSubst (fun q : Fin m × Fin d => a q.1 q.2) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (fun q => ha q.1 q.2)

private noncomputable def subA (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) : PS R m d →ₐ[R] PS R n e :=
  MvPowerSeries.substAlgHom (hasSub a ha)

private theorem subA_apply (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d) : subA a ha f = sub a f := by
  unfold subA sub
  rw [MvPowerSeries.coe_substAlgHom]

private theorem sub_sub {n' e' : ℕ} (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (b : Fin n → Fin e → PS R n' e')
    (hb : ∀ i j, MvPowerSeries.constantCoeff (b i j) = 0) (f : PS R m d) :
    sub b (sub a f) = sub (fun i j => sub b (a i j)) f := by
  unfold sub
  rw [MvPowerSeries.subst_comp_subst_apply (hasSub a ha) (hasSub b hb)]

private theorem sub_X (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (i : Fin m) (j : Fin d) :
    sub a (MvPowerSeries.X (i, j)) = a i j := by
  unfold sub
  rw [MvPowerSeries.subst_X (hasSub a ha)]

private theorem const_sub (a : Fin m → Fin d → PS R n e)
    (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) = 0) (f : PS R m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (sub a f) = 0 :=
  MvPowerSeries.constantCoeff_subst_eq_zero (hasSub a ha) (fun q => ha q.1 q.2) hf

private theorem ev_eq_sub (a : Fin m → Pt R n d) (f : PS R m d) : ev a f = sub a f := rfl

private theorem addOf_pt (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  unfold addOf ev
  have h : (fun q : Fin 2 × Fin d => (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) q.1 q.2) =
      MvPowerSeries.X := by
    funext ⟨a, b⟩
    fin_cases a <;> rfl
  rw [h, MvPowerSeries.subst_self]
  rfl

private theorem const_one (φ : Fin d → PS R n e) (hφ : ∀ j, MvPowerSeries.constantCoeff (φ j) = 0) :
    ∀ (i : Fin 1) j, MvPowerSeries.constantCoeff ((![φ] : Fin 1 → Fin d → PS R n e) i j) = 0 := by
  intro i j
  fin_cases i
  exact hφ j

private theorem const_pt (k : Fin n) : ∀ j, MvPowerSeries.constantCoeff (pt R d k j) = 0 := by
  intro j
  simp [pt]

private theorem isSum_comp (F : Fin d → PS R 2 d) (hF : ∀ j, MvPowerSeries.constantCoeff (F j) = 0)
    (F' : Fin e → PS R 2 e) (hF' : ∀ j, MvPowerSeries.constantCoeff (F' j) = 0)
    (J : Fin e → PS R 1 d) (hJ : IsHomF F F' J) (φ φ' ψ : PS R 1 d →ₐ[R] R) (h : IsSum F φ φ' ψ) :
    IsSum F' (φ.comp (subA ![J] (const_one J hJ.1))) (φ'.comp (subA ![J] (const_one J hJ.1)))
      (ψ.comp (subA ![J] (const_one J hJ.1))) := by
  obtain ⟨Φ, h0, h1, h2⟩ := h
  have hb : ∀ (i : Fin 2) j, MvPowerSeries.constantCoeff
      ((![fun i => ev (n := 2) ![pt R d 0] (J i), fun i => ev (n := 2) ![pt R d 1] (J i)] :
        Fin 2 → Fin e → PS R 2 d) i j) = 0 := by
    intro i j
    fin_cases i
    · exact const_sub _ (const_one _ (const_pt 0)) _ (hJ.1 j)
    · exact const_sub _ (const_one _ (const_pt 1)) _ (hJ.1 j)
  refine ⟨Φ.comp (subA _ hb), fun f => ?_, fun f => ?_, fun f => ?_⟩
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h0, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ (const_pt 0)) _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ (const_pt 0))]
    congr 2
    funext i j
    fin_cases i
    exact sub_X _ hb 0 j
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h1, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ (const_pt 1)) _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ (const_pt 1))]
    congr 2
    funext i j
    fin_cases i
    exact sub_X _ hb 1 j
  · simp only [AlgHom.comp_apply, subA_apply]
    rw [← h2, ev_eq_sub _ f, ev_eq_sub _ (sub _ f), sub_sub _ (const_one _ hF') _ hb,
      sub_sub _ (const_one J hJ.1) _ (const_one _ hF)]
    congr 2
    funext i j
    fin_cases i
    exact (hJ.2 j).symm

private theorem isCh_sum (F : Fin d → PS R 2 d) (u : PS R 1 d) (hu : IsCh F u) (φ φ' ψ : PS R 1 d →ₐ[R] R)
    (h : IsSum F φ φ' ψ) : ψ u = φ u * φ' u := by
  obtain ⟨Φ, h0, h1, h2⟩ := h
  have h3 := hu.2
  rw [addOf_pt] at h3
  rw [← h2, ← h0, ← h1, h3, map_mul]

end Subst

theorem exists_char_lift : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d r : ℕ) (F : FGLaw O d), FH p F.F → ∀ (J : Fin d → PS O 1 r) (A' : Matrix (Fin r) (Fin d) O), IsHomF (gmF O r) F.F J → A' * lin J = 1 → ∀ i : Fin r, ∃ u : PS O 1 d, IsCh F.F u ∧ (lin J)ᵀ *ᵥ dl u = Pi.single i 1 := by
  intro p _ C _ _ _ v O _ _ hv _ _ d r F hFH J A' hJ hA i
  obtain ⟨⟨Gl, hGl⟩, hch, -⟩ := GlobalTheory.ChF.gmLaw_chars_mul O r
  obtain ⟨hchi, hdl⟩ := hch i
  have hFHG : FH p Gl.F := hGl ▸ GlobalTheory.T.multiplicativeFormalGroupLawPower_pTorsion_finiteFree p C v O hv r
  rw [← hGl] at hJ hchi
  obtain ⟨instF, hsF, h0F, hkF⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  obtain ⟨instG, hsG, h0G, hkG⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv r Gl
  obtain ⟨hchain, -, -⟩ := GlobalTheory.ChF.chain_rule_lin O r d J hJ.1
  have hsurj := GlobalTheory.ChF.sub_surjective_of_lin_leftInverse O d r J A' hJ.1 hA
  let j : (PS O 1 r →ₐ[O] O) →+ (PS O 1 d →ₐ[O] O) :=
    { toFun := fun φ => φ.comp (subA ![J] (const_one J hJ.1))
      map_zero' := by
        refine AlgHom.ext fun f => ?_
        rw [AlgHom.comp_apply, subA_apply, h0F, h0G, (hchain f).2]
      map_add' := fun φ φ' =>
        (hsF _ _ _).1 (isSum_comp Gl.F Gl.const F.F F.const J hJ φ φ' _ ((hsG _ _ _).2 rfl)) }
  have hj : ∀ φ f, j φ f = φ (sub ![J] f) := fun φ f => by
    show φ (subA ![J] (const_one J hJ.1) f) = _
    rw [subA_apply]
  have hinj : Function.Injective j := by
    intro φ φ' h
    refine AlgHom.ext fun g => ?_
    obtain ⟨f, rfl⟩ := hsurj g
    rw [← hj, ← hj, h]
  have hunit : IsUnit (1 + MvPowerSeries.X ((0 : Fin 1), i) : PS O 1 r) := by
    rw [MvPowerSeries.isUnit_iff_constantCoeff, hchi.1]
    exact isUnit_one
  let χ : (PS O 1 r →ₐ[O] O) → Cˣ := fun φ => ((hunit.map φ).map (algebraMap O C)).unit
  have hχ : ∀ φ, (χ φ : C) = algebraMap O C (φ (1 + MvPowerSeries.X ((0 : Fin 1), i))) := fun φ => rfl
  have hχm : ∀ a b, χ (a + b) = χ a * χ b := by
    intro a b
    apply Units.ext
    rw [Units.val_mul, hχ, hχ, hχ, isCh_sum Gl.F _ hchi a b _ ((hsG _ _ _).2 rfl), map_mul]
  obtain ⟨κ, hκm, hκ0, hκj⟩ := GlobalTheory.CharExt.exists_extension _ _ j hinj C p (Fact.out : p.Prime).ne_zero χ hχm
  obtain ⟨u, hu, huκ⟩ := GlobalTheory.T.exists_isCh_eq_character_on_torsion p C v O hv d F hFH (fun φ => (κ φ : C))
    (by
      rintro φ φ' ψ ⟨k, hk⟩ ⟨k', hk'⟩ hs
      rw [(hsF _ _ _).1 hs, hκm φ φ' ⟨k, (hkF _ _).2 hk⟩ ⟨k', (hkF _ _).2 hk'⟩, Units.val_mul])
    (by
      intro φ hφ
      have : φ = 0 := AlgHom.ext fun f => by rw [hφ, h0F]
      show (κ φ : C) = 1
      rw [this, hκ0, Units.val_one])
  refine ⟨u, hu, ?_⟩
  have heq : sub ![J] u - (1 + MvPowerSeries.X ((0 : Fin 1), i)) = 0 := by
    apply (GlobalTheory.T.formalGroup_series_separated_by_torsion p C v O hv r Gl hFHG).2
    rintro φ ⟨k, hk⟩
    have h1 : p ^ k • φ = 0 := (hkG _ _).2 hk
    have h2 : p ^ k • j φ = 0 := by rw [← map_nsmul, h1, map_zero]
    have h3 := huκ (j φ) ⟨k, (hkF _ _).1 h2⟩
    rw [map_sub, sub_eq_zero]
    apply hv.hom_inj
    rw [← hj, h3, ← hχ, ← hκj φ ⟨k, h1⟩]
  rw [← (hchain u).1, sub_eq_zero.1 heq, hdl]

end GlobalTheory.ChF.Lift
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFormalTorusCharacterLiftToLawStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_formalTorus_character_lift_to_law : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d r : ℕ) (F : FGLaw O d), FH p F.F → ∀ (J : Fin d → PS O 1 r) (A' : Matrix (Fin r) (Fin d) O), IsHomF (gmF O r) F.F J → A' * lin J = 1 → ∀ i : Fin r, ∃ u : PS O 1 d, IsCh F.F u ∧ (lin J)ᵀ *ᵥ dl u = Pi.single i 1 := by
  first | exact @GlobalTheory.ChF.Lift.exists_char_lift | exact GlobalTheory.ChF.Lift.exists_char_lift | (intros; apply GlobalTheory.ChF.Lift.exists_char_lift <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLinearDataOfSplitFormalGroupExtension
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

theorem exists_linDat_of_extSer : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (d g r : ℕ) (F : FGLaw O d) (FB : FGLaw O g) (J : Fin d → PS O 1 r) (Q : Fin g → PS O 1 d), ExtSer F.F FB.F J Q → FH p F.F → ∀ (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (αB : OE → Fin g → PS O 1 g), (∀ a, lin Q * ρG a = lin (αB a) * lin Q) → (∀ a, ρG a * lin J = lin J * (N a).map (Int.castRingHom O)) → (∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (αB a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ ∀ i, ∃ u : PS O 1 g, IsCh FB.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (B : Matrix (Fin g) (Fin d) O) (m : ℕ) (u : Fin m → PS O 1 d), (∀ k, IsCh F.F (u k)) ∧ LinDat H (lin J) B ρG N (fun k => dl (u k)) := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ d g r F FB J Q hE hFH ρG N αB hB hA ⟨cp, hU, H, S, hP, hPL, hS, hα, hu⟩
  classical
  obtain ⟨h0, A', B', hA', hB', hAB⟩ := hE.exact
  have hdet : IsUnit S.det := (Matrix.isUnit_iff_isUnit_det S).1 hS
  have hS1 : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S hdet
  have hS2 : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S hdet
  choose u1 hu1 hu1' using hu
  choose u2 hu2 hu2' using GlobalTheory.T.exists_formalTorus_character_lift_to_law p C v O hv d r F hFH J A' hE.homI hA'
  obtain ⟨hc1, -, hc3⟩ := GlobalTheory.T.formalSeriesJacobian_chain_rule_linearPart O d g Q hE.homQ.1
  let w : (Fin g ⊕ Fin g) ⊕ Fin r → PS O 1 d := Sum.elim (fun i => sub ![Q] (u1 i)) u2
  let e := Fintype.equivFin ((Fin g ⊕ Fin g) ⊕ Fin r)
  refine ⟨cp, hU, H, S⁻¹ * lin Q, _, fun k => w (e.symm k), ?_, ⟨hP, hPL⟩, ⟨?_, A', B' * S, hA', ?_, ?_⟩,
    ?_, hA, ?_, ?_⟩
  · intro k
    show IsCh F.F (w (e.symm k))
    rcases e.symm k with i | i
    · exact hc3 F FB hE.homQ _ (hu1 i)
    · exact hu2 i
  · rw [Matrix.mul_assoc, h0, Matrix.mul_zero]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (lin Q), hB', Matrix.one_mul, hS1]
  · rw [Matrix.mul_assoc B', ← Matrix.mul_assoc S, hS2, Matrix.one_mul, hAB]
  · intro a
    have h : S⁻¹ * lin (αB a) = H.ρL (1 ⊗ₜ[ℤ] a) * S⁻¹ := by
      calc S⁻¹ * lin (αB a) = S⁻¹ * (lin (αB a) * S) * S⁻¹ := by
            rw [Matrix.mul_assoc, Matrix.mul_assoc, hS2, Matrix.mul_one]
        _ = _ := by rw [hα a, ← Matrix.mul_assoc, hS1, Matrix.one_mul]
    rw [Matrix.mul_assoc, hB a, ← Matrix.mul_assoc, h, Matrix.mul_assoc]
  · intro i
    refine ⟨e (Sum.inl i), ?_⟩
    simp only [Equiv.symm_apply_apply, w, Sum.elim_inl]
    rw [(hc1 _).1, ← hu1' i, Matrix.mulVec_mulVec, ← Matrix.transpose_mul, ← Matrix.mul_assoc, hS2,
      Matrix.one_mul]
  · intro i
    refine ⟨e (Sum.inr i), ?_⟩
    simp only [Equiv.symm_apply_apply, w, Sum.elim_inr]
    exact hu2' i

end GlobalTheory.ChF
end

section -- merged from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLinearDataOfSplitFormalGroupExtensionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_linearData_of_split_formalGroup_extension : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [StarRing OE] (d g r : ℕ) (F : FGLaw O d) (FB : FGLaw O g) (J : Fin d → PS O 1 r) (Q : Fin g → PS O 1 d), ExtSer F.F FB.F J Q → FH p F.F → ∀ (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (αB : OE → Fin g → PS O 1 g), (∀ a, lin Q * ρG a = lin (αB a) * lin Q) → (∀ a, ρG a * lin J = lin J * (N a).map (Int.castRingHom O)) → (∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (S : Matrix (Fin g) (Fin g) O), H.P = 0 ∧ H.PL = 0 ∧ IsUnit S ∧ (∀ a : OE, lin (αB a) * S = S * H.ρL (1 ⊗ₜ[ℤ] a)) ∧ ∀ i, ∃ u : PS O 1 g, IsCh FB.F u ∧ Sᵀ *ᵥ dl u = fun l => H.Ht l i) → ∃ (cp : O) (_ : HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (B : Matrix (Fin g) (Fin d) O) (m : ℕ) (u : Fin m → PS O 1 d), (∀ k, IsCh F.F (u k)) ∧ LinDat H (lin J) B ρG N (fun k => dl (u k)) := by
  first | exact @GlobalTheory.ChF.exists_linDat_of_extSer | exact GlobalTheory.ChF.exists_linDat_of_extSer | (intros; apply GlobalTheory.ChF.exists_linDat_of_extSer <;> assumption)
end
