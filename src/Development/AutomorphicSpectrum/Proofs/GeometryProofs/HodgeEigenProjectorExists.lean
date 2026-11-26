module

public import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.FlagLabelBasesExist

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorDenominator
section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorDenominator
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sandwich

open NumberField Polynomial GlobalTheory.CompanionTheory.Ar

variable {E : Type} [Field E] [NumberField E]

theorem exists_uniform_factor (w : 𝓞 E) :
    ∃ x : 𝓞 E, x ≠ 0 ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (ρ w - scal V σ w) * T = 0 ∧ ∀ v, ρ w v = σ w • v → T v = σ x • v := by
  obtain ⟨f, -, hroot, hder⟩ := exists_sep_poly w
  have key : ∀ p : ℤ[X], eval₂ (Int.castRingHom (𝓞 E)) w p = aeval w p := fun p => by
    rw [aeval_def, algebraMap_int_eq]
  have hF : (f.map (Int.castRingHom (𝓞 E))).IsRoot w := by
    rw [IsRoot, eval_map, key]
    exact hroot
  set g := f.map (Int.castRingHom (𝓞 E)) /ₘ (X - C w) with hg
  have hfac : (X - C w) * g = f.map (Int.castRingHom (𝓞 E)) :=
    (mul_divByMonic_eq_iff_isRoot).2 hF
  refine ⟨g.eval w, ?_, ?_⟩
  · have hd : (derivative (f.map (Int.castRingHom (𝓞 E)))).eval w = g.eval w := by
      rw [← hfac, derivative_mul]
      simp
    rw [← hd, derivative_map, eval_map, key]
    exact hder
  · intro Ω _ V _ _ ρ σ
    refine ⟨eval₂ (scal V σ) (ρ w) g, eval₂_mem_opRing ρ σ w g, ?_, ?_⟩
    · have hcomm : ∀ k, Commute (scal V σ (g.coeff k)) (ρ w) :=
        fun k => commute_scal σ (g.coeff k) (ρ w)
      have h1 : ρ w - scal V σ w = eval₂ (scal V σ) (ρ w) (X - C w) := by
        simp [eval₂_sub]
      rw [h1, ← eval₂_mul_noncomm _ _ hcomm, hfac, eval₂_map]
      have hc : (scal V σ).comp (Int.castRingHom (𝓞 E)) = ρ.comp (Int.castRingHom (𝓞 E)) :=
        RingHom.ext_int _ _
      rw [hc, ← hom_eval₂, key, hroot, map_zero]
    · intro v hv
      exact eval₂_apply_of_eigen ρ σ w hv g

private theorem mem_eigSp_iff_geometry {Ω : Type} [Field Ω] {V : Type} [AddCommGroup V] [Module Ω V]
    (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω) (v : V) :
    v ∈ eigSp ρ σ ↔ ∀ a, ρ a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem exists_uniform_product (W : Finset (𝓞 E)) :
    ∃ x : 𝓞 E, x ≠ 0 ∧ ∀ (Ω : Type) [Field Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (∀ w ∈ W, (ρ w - scal V σ w) * T = 0) ∧ ∀ v ∈ eigSp ρ σ, T v = σ x • v := by
  classical
  induction W using Finset.induction_on with
  | empty =>
    refine ⟨1, one_ne_zero, ?_⟩
    intro Ω _ V _ _ ρ σ
    exact ⟨1, (opRing ρ σ).one_mem, by simp, fun v _ => by simp⟩
  | @insert a W' ha ih =>
    obtain ⟨x', hx', hT'⟩ := ih
    obtain ⟨xa, hxa, hTa⟩ := exists_uniform_factor a
    refine ⟨xa * x', mul_ne_zero hxa hx', ?_⟩
    intro Ω _ V _ _ ρ σ
    obtain ⟨T', hT'm, hT'k, hT'e⟩ := hT' Ω V ρ σ
    obtain ⟨Ta, hTam, hTak, hTae⟩ := hTa Ω V ρ σ
    refine ⟨Ta * T', (opRing ρ σ).mul_mem hTam hT'm, ?_, ?_⟩
    · intro w hw
      rcases Finset.mem_insert.1 hw with rfl | hw'
      · rw [← mul_assoc, hTak, zero_mul]
      · have hc : Commute (ρ w - scal V σ w) Ta :=
          (commute_opRing hTam w).symm.sub_left (commute_scal σ w Ta)
        rw [← mul_assoc, hc.eq, mul_assoc, hT'k w hw', mul_zero]
    · intro v hv
      have hva : ρ a v = σ a • v := (mem_eigSp_iff_geometry ρ σ v).1 hv a
      change Ta (T' v) = _
      rw [hT'e v hv, map_smul, hTae v hva, smul_smul, map_mul, mul_comm (σ xa)]

theorem exists_eigen_op_uniform : ∀ (E : Type) [Field E] [NumberField E], ∃ D : ℕ, 0 < D ∧
    ∀ (Ω : Type) [Field Ω] [CharZero Ω] (V : Type) [AddCommGroup V] [Module Ω V]
      (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω),
      ∃ T ∈ opRing ρ σ, (∀ v, T v ∈ eigSp ρ σ) ∧ ∀ v ∈ eigSp ρ σ, T v = (D : Ω) • v := by
  intro E _ _
  obtain ⟨S, hS⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 E)).FG)
  obtain ⟨x, hx, hT⟩ := exists_uniform_product S
  have hint : IsIntegral ℤ x := Algebra.IsIntegral.isIntegral x
  have hbot := Ideal.comap_ne_bot_of_integral_mem hx (Ideal.mem_span_singleton_self x) hint
  obtain ⟨c, hcmem, hc0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hbot
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, algebraMap_int_eq, eq_intCast] at hcmem
  obtain ⟨y0, hy0⟩ := hcmem
  obtain ⟨n, hn0, y, hy⟩ : ∃ n : ℕ, 0 < n ∧ ∃ y : 𝓞 E, x * y = (n : 𝓞 E) := by
    rcases Int.natAbs_eq c with h | h
    · refine ⟨c.natAbs, Int.natAbs_pos.2 hc0, y0, ?_⟩
      rw [← hy0]
      conv_lhs => rw [h]
      simp
    · refine ⟨c.natAbs, Int.natAbs_pos.2 hc0, -y0, ?_⟩
      rw [mul_neg, ← hy0]
      conv_lhs => rw [h]
      simp
  refine ⟨n, hn0, ?_⟩
  intro Ω _ _ V _ _ ρ σ
  obtain ⟨T, hTm, hTk, hTe⟩ := hT Ω V ρ σ
  have hall : ∀ v, ∀ a : 𝓞 E, ρ a (T v) = σ a • T v := by
    intro v a
    have ha : a ∈ Submodule.span ℤ (S : Set (𝓞 E)) := by
      rw [hS]
      trivial
    induction ha using Submodule.span_induction with
    | mem w hw =>
      have h := congrArg (fun U : Module.End Ω V => U v) (hTk w hw)
      change (ρ w - scal V σ w) (T v) = 0 at h
      rw [LinearMap.sub_apply, scal_apply, sub_eq_zero] at h
      exact h
    | zero => simp
    | add a b _ _ iha ihb =>
      rw [map_add (f := _), map_add (f := _), LinearMap.add_apply, iha, ihb, add_smul]
    | smul m a _ ih =>
      rw [map_zsmul, map_zsmul, LinearMap.smul_apply, ih, smul_assoc]
  have hs : scal V σ y ∈ opRing ρ σ := by
    simpa using eval₂_mem_opRing ρ σ 0 (C y)
  refine ⟨scal V σ y * T, (opRing ρ σ).mul_mem hs hTm, ?_, ?_⟩
  · intro v
    change scal V σ y (T v) ∈ eigSp ρ σ
    rw [scal_apply]
    exact Submodule.smul_mem _ _ ((mem_eigSp_iff_geometry ρ σ (T v)).2 (hall v))
  · intro v hv
    change scal V σ y (T v) = _
    rw [scal_apply, hTe v hv, smul_smul, ← map_mul, mul_comm y x, hy, map_natCast]

end GlobalTheory.CompanionTheory.Ar.Sandwich
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorDenominatorStatement
open NumberField GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_projector_denominator : ∀ (E : Type) [Field E] [NumberField E], ∃ D : ℕ, 0 < D ∧ ∀ (Ω : Type) [Field Ω] [CharZero Ω] (V : Type) [AddCommGroup V] [Module Ω V] (ρ : 𝓞 E →+* Module.End Ω V) (σ : 𝓞 E →+* Ω), ∃ T ∈ Sandwich.opRing ρ σ, (∀ v, T v ∈ eigSp ρ σ) ∧ ∀ v ∈ eigSp ρ σ, T v = (D : Ω) • v := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform | exact GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform | (intros; apply GlobalTheory.CompanionTheory.Ar.Sandwich.exists_eigen_op_uniform <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeEigenProjectorExists
noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert

namespace GlobalTheory.CompanionTheory.Ar.OrVert

section Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l} {Y : Model Xo c (algebraMap (𝓞 c.F) c.F)} {S : Finset ℕ} {Ω : Type} [Field Ω]
  {K : Type} [Fintype K] {J : K → Type} [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} (𝔐 : HodgeCpt Y S y)

theorem V_eq_HT (s : CMType H ⊕ CMType H) {q : Cpt 𝔐.ξ} {p : ℕ} (hp : p ∈ S) (hq : InFibre 𝔐.ξ p q) :
    𝔐.V s q = 𝔐.HT p s q :=
  Lat.patch_of_unique S _ _ hp hq fun p' hp' h' => by
    by_contra hne
    exact Lat.not_inFibre_of_coprime q ((Nat.coprime_primes (𝔐.S_prime _ hp) (𝔐.S_prime _ hp')).2 (Ne.symm hne)) hq h'

theorem dR_le_V (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) : 𝔐.dR s q ≤ 𝔐.V s q := by
  by_cases h : ∃ p ∈ S, InFibre 𝔐.ξ p q
  · obtain ⟨p, hp, hq⟩ := h
    rw [V_eq_HT 𝔐 s hp hq]
    have hd : 𝔐.dR s q ≤ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s) q :=
      𝔐.M.eigLat_le_htDual _ _ _ _ q
    rcases s with τ | τ
    · intro e he
      refine Submodule.subset_span ⟨he.2, fun d _ => ?_⟩
      exact Submodule.smul_mem _ (⟨_, Sandwich.emb_mem 𝔐 _ q d⟩ : regAt 𝔐.ξ q) (hd he)
    · exact hd
  · exact (Lat.patch_of_not S _ _ fun p hp hf => h ⟨p, hp, hf⟩).ge

theorem V_le_lat_of_not (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) (h : ∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) :
    𝔐.V s q ≤ 𝔐.M.lat q := by
  have e : 𝔐.V s q = 𝔐.dR s q := Lat.patch_of_not S _ _ h
  rw [e]
  exact fun _ he => he.1

theorem smul_V_mem_lat (s : CMType H ⊕ CMType H) (q : Cpt 𝔐.ξ) {p : ℕ} (hp : p ∈ S) (hq : InFibre 𝔐.ξ p q) {κ : Ω}
    (hκ : HT.Sandwich 𝔐 p κ) (D₂ : ℕ) (hD : (D₂ : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E)) {e : 𝔐.Li} (he : e ∈ 𝔐.V s q) :
    ((D₂ : Ω) * κ) • e ∈ 𝔐.M.lat q := by
  obtain ⟨hκr, -, -, hS⟩ := hκ q hq
  have hdual : ∀ s' : CMType H ⊕ CMType H, ∀ e ∈ 𝔐.M.htDual 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb s') q,
      κ • e ∈ 𝔐.M.lat q := fun s' e he => ((hS s').2 e he).1
  rw [V_eq_HT 𝔐 s hp hq] at he
  rcases s with τ | τ
  · change e ∈ 𝔐.M.htW 𝔐.t.PP.L (p ^ 𝔐.R p) 𝔐.ρ (𝔐.emb (.inl τ)) (differentIdeal ℤ (𝓞 E)) q at he
    induction he using Submodule.span_induction with
    | mem x hx =>
      have h1 := hdual _ _ (hx.2 _ hD)
      rw [map_natCast, smul_smul, mul_comm] at h1
      exact h1
    | zero => simp
    | add a b _ _ ha hb =>
      rw [smul_add]
      exact add_mem ha hb
    | smul t a _ ha =>
      have : ((D₂ : Ω) * κ) • t • a = t • (((D₂ : Ω) * κ) • a) := by
        rw [show t • a = (t : Ω) • a from rfl, show t • (((D₂ : Ω) * κ) • a) = (t : Ω) • (((D₂ : Ω) * κ) • a) from rfl,
          smul_comm]
      rw [this]
      exact Submodule.smul_mem _ t ha
  · have h1 := hdual _ _ he
    rw [mul_smul]
    exact Submodule.smul_mem _ (⟨_, natCast_mem _ D₂⟩ : regAt 𝔐.ξ q) h1

end Loc

theorem hodge_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ Dn : ℕ, 0 < Dn ∧ ∀ (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H), ∃ T : Module.End Ω 𝔐.Li, (∀ v ∈ eigSp 𝔐.ρ (𝔐.emb s), T v = (Dn : Ω) • v) ∧ ∀ q : Cpt 𝔐.ξ, (∀ e ∈ 𝔐.M.lat q, T e ∈ 𝔐.V s q) ∧ ((∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) → ∀ e ∈ 𝔐.V s q, (Dn : Ω) • e ∈ 𝔐.M.lat q) ∧ ∀ p ∈ S, InFibre 𝔐.ξ p q → ∀ κ : Ω, HT.Sandwich 𝔐 p κ → ∀ e ∈ 𝔐.V s q, ((Dn : Ω) * κ) • e ∈ 𝔐.M.lat q := by
  intro E _ _ _
  obtain ⟨D₁, hD₁, hop⟩ := GlobalTheory.T.eigen_projector_denominator E
  have hdiff : differentIdeal ℤ (𝓞 E) ≠ ⊥ := differentIdeal_ne_bot
  have hD₂ : 0 < Ideal.absNorm (differentIdeal ℤ (𝓞 E)) :=
    Nat.pos_of_ne_zero (by rwa [Ne, Ideal.absNorm_eq_zero_iff])
  have hmem : ((Ideal.absNorm (differentIdeal ℤ (𝓞 E)) : ℕ) : 𝓞 E) ∈ differentIdeal ℤ (𝓞 E) := Ideal.absNorm_mem _
  generalize Ideal.absNorm (differentIdeal ℤ (𝓞 E)) = D₂ at hD₂ hmem
  refine ⟨D₁ * D₂, Nat.mul_pos hD₁ hD₂, ?_⟩
  intro H D l Xo c Y S Ω _ K _ J _ y 𝔐 s
  haveI := Sandwich.charZero_of_hodgeCpt 𝔐
  obtain ⟨T₁, hT₁, hTe, hTD⟩ := hop Ω 𝔐.Li 𝔐.ρ (𝔐.emb s)
  have hreg : ∀ (q : Cpt 𝔐.ξ) (n : ℕ) {e : 𝔐.Li}, e ∈ 𝔐.M.lat q → (n : Ω) • e ∈ 𝔐.M.lat q := fun q n _ he =>
    Submodule.smul_mem _ (⟨_, natCast_mem _ n⟩ : regAt 𝔐.ξ q) he
  refine ⟨(D₂ : Ω) • T₁, fun v hv => ?_, fun q => ⟨fun e he => ?_, fun h e he => ?_, fun p hp hq κ hκ e he => ?_⟩⟩
  · rw [LinearMap.smul_apply, hTD v hv, smul_smul]
    push_cast
    rw [mul_comm]
  · have hst : T₁ e ∈ 𝔐.M.lat q :=
      Sandwich.opRing_stable (𝔐.M.lat q).toAddSubgroup (fun a e he => Sandwich.lat_act 𝔐 q a e he)
        (fun a e he => (𝔐.M.lat q).smul_mem ⟨_, Sandwich.emb_mem 𝔐 s q a⟩ he) hT₁ e he
    exact dR_le_V 𝔐 s q ⟨hreg q D₂ hst, (eigSp 𝔐.ρ (𝔐.emb s)).smul_mem _ (hTe e)⟩
  · exact hreg q _ (V_le_lat_of_not 𝔐 s q h he)
  · have h1 := hreg q D₁ (smul_V_mem_lat 𝔐 s q hp hq hκ D₂ hmem he)
    rw [smul_smul] at h1
    have e1 : ((D₁ * D₂ : ℕ) : Ω) * κ = (D₁ : Ω) * ((D₂ : Ω) * κ) := by
      push_cast
      ring
    rw [e1]
    exact h1

end GlobalTheory.CompanionTheory.Ar.OrVert
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeEigenProjectorExistsStatement
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.OrVert
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_eigen_projector_exists : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], ∃ Dn : ℕ, 0 < Dn ∧ ∀ (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y) (s : CMType H ⊕ CMType H), ∃ T : Module.End Ω 𝔐.Li, (∀ v ∈ eigSp 𝔐.ρ (𝔐.emb s), T v = (Dn : Ω) • v) ∧ ∀ q : Cpt 𝔐.ξ, (∀ e ∈ 𝔐.M.lat q, T e ∈ 𝔐.V s q) ∧ ((∀ p ∈ S, ¬ InFibre 𝔐.ξ p q) → ∀ e ∈ 𝔐.V s q, (Dn : Ω) • e ∈ 𝔐.M.lat q) ∧ ∀ p ∈ S, InFibre 𝔐.ξ p q → ∀ κ : Ω, HT.Sandwich 𝔐 p κ → ∀ e ∈ 𝔐.V s q, ((Dn : Ω) * κ) • e ∈ 𝔐.M.lat q := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrVert.hodge_loc | exact GlobalTheory.CompanionTheory.Ar.OrVert.hodge_loc | (intros; apply GlobalTheory.CompanionTheory.Ar.OrVert.hodge_loc <;> assumption)
end
