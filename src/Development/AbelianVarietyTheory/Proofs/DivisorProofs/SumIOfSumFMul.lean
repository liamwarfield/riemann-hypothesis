module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalSectionDivisorPullbackGeneric
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartValueIsIntegralOfIntegralAtPoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegPBOfFiniteEtaleCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernDensityPullbackWeightInLiftedChart
public import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumIOfSumFMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.TwistSum₂

theorem sumI_of_sumF_mul {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V] {Ix : Type}
    (y : Ix → V) (v : V) (d : FractionRing V) (hd : d ≠ 0)
    (h : SumF (maximalIdeal V) (FractionRing V) (fun i => algebraMap V (FractionRing V) (y i) * d)
      (algebraMap V (FractionRing V) v * d)) :
    SumI (maximalIdeal V) y v := by
  classical
  have hsm : ∀ (r : V) (x : FractionRing V), r • x = algebraMap V (FractionRing V) r * x := Algebra.smul_def
  have hmod : (Module.compHom (FractionRing V) (algebraMap V (FractionRing V)) : Module V (FractionRing V)) =
      Algebra.toModule := Module.ext' _ _ fun r x => (Algebra.smul_def r x).symm
  unfold SumF at h
  rw [hmod] at h
  obtain ⟨N, hN, -, -, hS⟩ := h
  let P : Submodule V (FractionRing V) := N ⊔ Submodule.span V {d}
  haveI : Module.Finite V P := Module.Finite.iff_fg.mpr (hN.sup (Submodule.fg_span_singleton d))
  let L : Submodule V P := (Submodule.span V {d}).comap P.subtype
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul (maximalIdeal V) L
  refine ⟨⊤, Module.Finite.fg_top, Submodule.mem_top, fun _ => Submodule.mem_top, fun n => ?_⟩
  obtain ⟨S, hS⟩ := hS (n + k)
  refine ⟨S, fun T hT => ?_⟩
  set w : V := v - ∑ i ∈ T, y i with hw
  have e : algebraMap V (FractionRing V) w * d =
      algebraMap V (FractionRing V) v * d - ∑ i ∈ T, algebraMap V (FractionRing V) (y i) * d := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hw, map_sub, map_sum, sub_mul, Finset.sum_mul]
  have h1 : algebraMap V (FractionRing V) w * d ∈ maximalIdeal V ^ (n + k) • N := e ▸ hS T hT
  have hwP : algebraMap V (FractionRing V) w * d ∈ P :=
    Submodule.mem_sup_right (by rw [← hsm]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d))
  let p : P := ⟨_, hwP⟩
  have hp1 : p ∈ maximalIdeal V ^ (n + k) • (⊤ : Submodule V P) :=
    (Submodule.mem_smul_top_iff _ P p).2 (Submodule.smul_mono le_rfl le_sup_left h1)
  have hp2 : p ∈ L := by
    show algebraMap V (FractionRing V) w * d ∈ Submodule.span V {d}
    rw [← hsm]; exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self d)
  have hp3 : p ∈ maximalIdeal V ^ n • L := by
    have := (hk (n + k) (Nat.le_add_left _ _)).le ⟨hp1, hp2⟩
    rw [Nat.add_sub_cancel] at this
    exact Submodule.smul_mono le_rfl inf_le_right this
  have hp4 : algebraMap V (FractionRing V) w * d ∈ maximalIdeal V ^ n • Submodule.span V {d} := by
    have := Submodule.mem_map_of_mem (f := P.subtype) hp3
    rw [Submodule.map_smul''] at this
    exact Submodule.smul_mono le_rfl (Submodule.map_comap_le _ _) this
  obtain ⟨u, hu, hud⟩ := Submodule.mem_smul_span_singleton.1 hp4
  rw [hsm] at hud
  have hwu : w = u := IsFractionRing.injective V (FractionRing V) (mul_right_cancel₀ hd hud).symm
  rw [hwu]
  simpa using Submodule.smul_mem_smul hu (Submodule.mem_top : (1 : V) ∈ (⊤ : Submodule V V))

end GlobalTheory.Poinc.TwistSum₂

namespace GlobalTheory.Poinc.TwistSum₂

open GlobalTheory.Poinc.Sep

variable {g n : ℕ} {F : SFam g n (zetaAway n)} {W : Matrix (Fin 8) (Fin 8) ℤ} {Z : Scheme.{0}} {i : F.X ⟶ Z}

theorem val_stalkHom (X₁ : Setup F W i) (z₁ : X₁.M.Z) {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V]
    (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) [IsLocalHom ev] (a : X₁.M.Z.presheaf.stalk z₁) :
    X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (X₁.M.stalkHom z₁ a) =
      algebraMap V (FractionRing V) (ev a) := by
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have h : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) ⤳ z₁ := specializes_of_eq hc
  have e := RatModel.val_spMap_comp (algebraMap V (FractionRing V)) (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) h
    (X₁.M.stalkEquiv z₁ a)
  rw [RatModel.coe_stalkEquiv] at e
  refine e.trans (congrArg _ ?_)
  have hψ : Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) ≫
      X₁.M.Z.fromSpecStalk z₁ = spMap ev ≫ X₁.M.Z.fromSpecStalk z₁ := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  have heq : spMap ev = Spec.map (X₁.M.Z.presheaf.stalkSpecializes h ≫
      Scheme.stalkClosedPointTo (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁)) := by
    rw [← cancel_mono (X₁.M.Z.fromSpecStalk z₁), hψ]
  have hφψ := Spec.map_injective heq
  simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
    RingEquiv.symm_apply_apply]
  exact (congrArg (fun φ => φ.hom a) hφψ).symm

theorem twistSum_of_sumF : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)), ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ) (x₀ : X₁.S.Gam) (C : Type) (lab : C → X₁.S.Gam) (T : (Fin 8 → X) → C → V) (sg : ℤˣ) (c : C) (τ : X₁.S.Gam) (χ : Multiplicative 𝔪.D.toPre.X →* (FractionRing V)ˣ) (e : ℕ), 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ ≠ 0 → (∀ mu, ∃ a : X₁.S.Gam, 𝔪.YY a mu) → (∀ a mu, 𝔪.YY a mu → ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N * (((sg : ℤˣ) : ℤ) • eStd X₁.S.g _ τ a).val)))) → SumF (maximalIdeal V) (FractionRing V) (fun mu : Fin 8 → X => ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) * (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩)) (𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩) → TwistSum X₁ z₁ act x₀ 𝔪 lab T sg c τ e := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x₀ C lab T sg c τ χ e hθ hY hχ hS
  intro zt h hzt hh wt hwt
  haveI : IsNoetherianRing V := 𝔪.cn.1
  haveI : IsLocalHom ev := 𝔪.loc
  have hc : (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint V) = z₁ := by
    refine (Scheme.Hom.comp_apply _ _ _).trans
      (Eq.trans (congrArg (X₁.M.Z.fromSpecStalk z₁) ?_) (Scheme.fromSpecStalk_closedPoint (x := z₁)))
    exact comap_closedPoint ev
  have hsp : ∀ w, (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) w ⤳
      (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) :=
    RatModel.specializes_of_range_eq (RatModel.range_eq_singleton (M := X₁.M) (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (IsLocalRing.closedPoint (FractionRing V)))
  have hgen : (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V)) ⤳ z₁ := by
    have h1 : (jK V) (closedPoint (FractionRing V)) ⤳ closedPoint V := IsLocalRing.specializes_closedPoint _
    have h2 := h1.map (spMap ev ≫ X₁.M.Z.fromSpecStalk z₁).continuous
    rw [hc] at h2
    exact h2
  have hO : ∀ s, X₁.M.stalkHom z₁ s ∈
      X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := fun s =>
    RatModel.O_le_of_specializes hgen (X₁.M.stalkEquiv z₁ s).2
  have hR : ∀ a ∈ X₁.S.R, a ∈ X₁.M.O ((jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (closedPoint (FractionRing V))) := 𝔪.reg
  have hyK : ∀ (a : X₁.Ω₁) (ha : a ∈ X₁.S.R), 𝔪.yK ⟨a, ha⟩ = X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) a :=
    fun a ha => 𝔪.yK_eq ⟨a, ha⟩
  have hyA : ∀ b : X₁.o₁, 𝔪.yK (algebraMap X₁.o₁ X₁.S.R b) =
      X₁.M.val (jK V ≫ spMap ev ≫ X₁.M.Z.fromSpecStalk z₁) (algebraMap X₁.o₁ X₁.Ω₁ b) := fun b => by
    rw [𝔪.yK_eq, Subalgebra.coe_algebraMap]
  have hzt' : algebraMap V (FractionRing V) (ev zt) = 𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ (X₁.S.r * X₁.S.N))) := by
    rw [← val_stalkHom X₁ z₁ ev, hzt, hyA]
  have hth0 : X₁.S.th x₀ ≠ 0 := by
    intro h0
    apply hθ
    rw [hyK, h0, RatModel.val_zero]
  have hh' : algebraMap V (FractionRing V) (ev h) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ =
      𝔪.yK (algebraMap X₁.o₁ X₁.S.R (X₁.S.ζ ^ e)) * 𝔪.yK ⟨X₁.S.th (lab c + τ), X₁.S.th_mem (lab c + τ)⟩ := by
    rw [← val_stalkHom X₁ z₁ ev, hyA, hyK, hyK, ← RatModel.val_mul hsp (hO h) (hR _ (X₁.S.th_mem x₀)),
      ← RatModel.val_mul hsp (hR _ (Subalgebra.algebraMap_mem _ _)) (hR _ (X₁.S.th_mem _)), hh,
      div_mul_cancel₀ _ hth0]
  have hterm : ∀ mu : Fin 8 → X, ((χ (Multiplicative.ofAdd (𝔪.e₈ mu)) : (FractionRing V)ˣ) : FractionRing V) *
      (algebraMap V (FractionRing V) (T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩) =
      algebraMap V (FractionRing V) (ev zt ^ (wt mu).val * T mu c) * 𝔪.yK ⟨X₁.S.th x₀, X₁.S.th_mem x₀⟩ := by
    intro mu
    obtain ⟨a, ha⟩ := hY mu
    rw [hχ a mu ha, ← hwt a mu ha, pow_mul, map_pow, map_pow, ← hzt', map_mul, map_pow]
    ring
  refine TwistSum₂.sumI_of_sumF_mul _ _ _ hθ ?_
  convert hS using 1
  · funext mu
    exact (hterm mu).symm

end GlobalTheory.Poinc.TwistSum₂
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDual
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimAddDualCotangentDimLeHeight
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimAddDualCotangentDimLeHeight
set_option autoImplicit false
noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField WithConv
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.PerfdLat
open Coalgebra Bialgebra
open GlobalTheory.DeRham (spOver spOver_comp)
attribute [local instance] Over.cartesianMonoidalCategory


open GlobalTheory.PDivGroup.CotDim in
theorem GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero (p : ℕ) [Fact p.Prime]
    (k : Type) [Field k] (hp : (p : k) = 0) (Γ : PDivGroup p k) :
    Module.finrank k (Cot k (Γ.A 1)) + Module.finrank k (Cot k (Γ.dual.A 1)) ≤ Γ.height := by
  letI : CharP k p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 hp
  have hdimD := finrank_level_one Γ.dual
  have hmulP : Function.Injective (Γ.mulP 1) := fun a b e => by
    refine CartierDual.eq_of_forall_apply (R := k) fun φ => ?_
    obtain ⟨ψ, rfl⟩ := Γ.dual_mulP_surjective 1 φ
    change ψ.ofConv (Γ.mulP 1 a) = ψ.ofConv (Γ.mulP 1 b)
    rw [e]

  have hord := finrank_eq_ker_mul_range k (Γ.dual.A 1) _ ((PDivGroup.relFrob hp Γ.dual).app 1)
  have hcot (G : PDivGroup p k) :
      p ^ Module.finrank k (Cot k (G.A 1)) ≤
        Module.finrank k (G.A 1 ⧸ kerIdeal ((PDivGroup.relFrob hp G).app 1)) :=
    (FrobKerOrder.pow_finrank_cot_le (p := p) (k := k) (H := G.A 1)).trans
      (quot_finrank_le (GlobalTheory.T.relativeFrobeniusKernelIdeal_le_frobeniusKernelIdeal p k hp G 1))

  have hker : LinearMap.ker ((PDivGroup.verschiebung hp Γ).app 1 :
        Γ.A 1 →ₐ[k] (PDivGroup.frobTwist hp Γ).A 1).toLinearMap ≤
      (kerIdeal ((PDivGroup.relFrob hp Γ).app 1)).restrictScalars k := by
    intro a ha
    have h := GlobalTheory.T.mulP_mem_kerIdeal_comp_relFrob_of_verschiebung_eq_zero p k hp Γ a ha
    rw [kerIdeal_comp] at h
    change a ∈ kerIdeal ((PDivGroup.relFrob hp Γ).app 1)
    rw [← GlobalTheory.T.comap_map_eq_self_of_injective_finiteHopf k _ _ (Γ.mulP 1) hmulP
      (kerIdeal ((PDivGroup.relFrob hp Γ).app 1))]
    exact h
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p k hp Γ
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((PDivGroup.relFrob hp Γ).app 1)).restrictScalars k)
  rw [(Submodule.Quotient.restrictScalarsEquiv k (kerIdeal ((PDivGroup.relFrob hp Γ).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have hrD : Module.finrank k (Γ.A 1 ⧸ kerIdeal ((PDivGroup.relFrob hp Γ).app 1)) ≤
      Module.finrank k (LinearMap.range ((PDivGroup.relFrob hp Γ.dual).app 1 :
        (PDivGroup.frobTwist hp Γ.dual).A 1 →ₐ[k] Γ.dual.A 1).toLinearMap) := by omega
  apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1
  change _ ≤ p ^ Γ.dual.height
  rw [pow_add, mul_comm, ← hdimD, hord]
  exact Nat.mul_le_mul (hcot Γ.dual) ((hcot Γ).trans hrD)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CotangentDimAddDualCotangentDimLeHeightStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cotangent_dim_add_dual_cotangent_dim_le_height : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) ≤ G.height := by
  first | exact @GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero | exact GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero | (intros; apply GlobalTheory.PDivGroup.finrank_cot_add_finrank_cot_dual_le_of_cast_eq_zero <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeCotangentDimAddDualCotangentDim
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeCotangentDimAddDualCotangentDim
set_option autoImplicit false
noncomputable section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

theorem GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual (p : ℕ) [Fact p.Prime] (K : Type)
    [Field K] (h : (p : K) = 0) (G : PDivGroup p K) :
    G.height ≤ Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) := by
  haveI : CharP K p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 h
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hdimD : Module.finrank K (G.dual.A 1) = p ^ G.dual.height := by
    obtain ⟨q⟩ : Nonempty (PrimeSpectrum K) := inferInstance
    have e := G.dual.rank_eq 1 q
    rw [Module.rankAtStalk_eq_finrank_of_free] at e
    simpa using e
  have hhD : G.dual.height = G.height := by simp
  have hord := finrank_eq_ker_mul_range K (G.dual.A 1) _ ((relFrob h G.dual).app 1)
  have hD : Module.finrank K (G.dual.A 1 ⧸ kerIdeal ((relFrob h G.dual).app 1)) ≤
      p ^ Module.finrank K (Cot K (G.dual.A 1)) := by
    rw [← GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius p K h G.dual 1]
    exact GlobalTheory.T.finrank_frobenius_kernel_hopf_le_pow_cotangent p K (G.dual.A 1)
  have hA : Module.finrank K (G.A 1 ⧸ kerIdeal ((relFrob h G).app 1)) ≤
      p ^ Module.finrank K (Cot K (G.A 1)) := by
    rw [← GlobalTheory.T.frobeniusKernelIdeal_eq_kernel_relativeFrobenius p K h G 1]
    exact GlobalTheory.T.finrank_frobenius_kernel_hopf_le_pow_cotangent p K (G.A 1)
  have hker : (kerIdeal ((relFrob h G).app 1)).restrictScalars K ≤
      LinearMap.ker ((verschiebung h G).app 1 :
        G.A 1 →ₐ[K] (frobTwist h G).A 1).toLinearMap := fun a ha =>
    GlobalTheory.T.app_one_eq_zero_of_kernel_ideal_of_comp_eq_prime_smul p K G (frobTwist h G) (relFrob h G) (verschiebung h G)
      (verschiebung_comp_relFrob h G) a ha
  have hV := GlobalTheory.T.finrank_frobeniusDual_add_finrank_ker_verschiebung p K h G
  have hq := Submodule.finrank_quotient_add_finrank
    ((kerIdeal ((relFrob h G).app 1)).restrictScalars K)
  rw [(Submodule.Quotient.restrictScalarsEquiv K (kerIdeal ((relFrob h G).app 1))).finrank_eq] at hq
  have hmono := Submodule.finrank_mono hker
  have hr : Module.finrank K (LinearMap.range ((relFrob h G.dual).app 1 :
        (frobTwist h G.dual).A 1 →ₐ[K] G.dual.A 1).toLinearMap) ≤
      p ^ Module.finrank K (Cot K (G.A 1)) := by omega
  have key : p ^ G.height ≤
      p ^ (Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1))) := by
    rw [pow_add, mul_comm, ← hhD, ← hdimD, hord]
    exact Nat.mul_le_mul hD hr
  exact (Nat.pow_le_pow_iff_right hp2).1 key
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeightLeCotangentDimAddDualCotangentDimStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.height_le_cotangent_dim_add_dual_cotangent_dim : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), G.height ≤ Module.finrank K (Cot K (G.A 1)) + Module.finrank K (Cot K (G.dual.A 1)) := by
  first | exact @GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual | exact GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual | (intros; apply GlobalTheory.PDivGroup.height_le_finrank_cot_add_finrank_cot_dual <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDual
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup

namespace GlobalTheory.PDivGroup

theorem finite_omega_of_eq_zero {p : ℕ} {K : Type} [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) : Module.Finite K G.omega := by
  haveI : Module.Finite K (Cot K (G.A 1)) :=
    Module.Finite.of_surjective (AugCot.d (counitAlgHom K (G.A 1))) (AugCot.d_surjective _)
  exact Module.Finite.equiv (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).symm

theorem finrank_rigExt_omega (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0)
    (G : PDivGroup p K) :
    Module.Finite K G.omega ∧ Module.Finite K ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) ∧ Module.finrank K ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) = G.height ∧
      Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
  have h1 := finite_omega_of_eq_zero h G
  have h2 := finite_omega_of_eq_zero h G.dual
  have e1 : Module.finrank K G.omega = Module.finrank K (Cot K (G.A 1)) :=
    (LinearEquiv.ofBijective _ (G.omegaLevel_one_bijective h)).finrank_eq
  have e2 : Module.finrank K G.dual.omega = Module.finrank K (Cot K (G.dual.A 1)) :=
    (LinearEquiv.ofBijective _ (G.dual.omegaLevel_one_bijective h)).finrank_eq
  have hsum : Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
    rw [e1, e2]
    exact le_antisymm (GlobalTheory.T.cotangent_dim_add_dual_cotangent_dim_le_height p K h G) (GlobalTheory.T.height_le_cotangent_dim_add_dual_cotangent_dim p K h G)

  have hr := (G.rigToLie h).rank_range_add_rank_ker
  rw [LinearMap.range_eq_top.2 (G.rigToLie_surjective h), rank_top,
    LinearMap.exact_iff.1 (G.exact_rigOfOmega_rigToLie h),
    (LinearEquiv.ofInjective _ (G.rigOfOmega_injective_of_eq_zero h)).rank_eq.symm] at hr
  have hfin : Module.Finite K G.RigExt := by
    haveI : Module.Free K G.RigExt := Module.Free.of_divisionRing K _
    rw [← Module.rank_lt_aleph0_iff, ← hr]
    exact Cardinal.add_lt_aleph0 (Module.rank_lt_aleph0 K _) (Module.rank_lt_aleph0 K _)
  refine ⟨h1, hfin, ?_, hsum⟩
  have e := (G.rigToLie h).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.2 (G.rigToLie_surjective h), finrank_top,
    LinearMap.exact_iff.1 (G.exact_rigOfOmega_rigToLie h),
    LinearMap.finrank_range_of_inj (G.rigOfOmega_injective_of_eq_zero h)] at e
  change Module.finrank K G.RigExt = G.height
  rw [← e, ← hsum, add_comm, Subspace.dual_finrank_eq]

end GlobalTheory.PDivGroup
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankRigidExtensionsEqHeightAndDimAddDualStatement
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_rigidExtensions_eq_height_and_dim_add_dual : ∀ (p : ℕ) [Fact p.Prime] (K : Type) [Field K] (h : (p : K) = 0) (G : PDivGroup p K), Module.Finite K G.omega ∧ Module.Finite K ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) ∧ Module.finrank K ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n)))))) = G.height ∧ Module.finrank K G.omega + Module.finrank K G.dual.omega = G.height := by
  first | exact @GlobalTheory.PDivGroup.finrank_rigExt_omega | exact GlobalTheory.PDivGroup.finrank_rigExt_omega | (intros; apply GlobalTheory.PDivGroup.finrank_rigExt_omega <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneous
set_option autoImplicit false

noncomputable section

open Set MeasureTheory
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ENNReal
open GlobalTheory.CxForm GlobalTheory.ChartGlue

namespace GlobalTheory.LineForm.TopInt

variable {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n)

theorem loc_add (α β : A.Fld) (i : A.ι) (v : V n) : A.loc (α + β) i v = A.loc α i v + A.loc β i v := by
  unfold HolAtlas.loc; split_ifs
  · rfl
  · exact (add_zero 0).symm

theorem loc_smul (c : ℂ) (α : A.Fld) (i : A.ι) (v : V n) : A.loc (c • α) i v = c • A.loc α i v := by
  unfold HolAtlas.loc; split_ifs
  · rfl
  · exact (smul_zero c).symm

theorem dens_add (x y : Alt n) : dens (x + y) = dens x + dens y := by
  simp only [dens, map_add (f := _), Finsupp.add_apply, add_div]

theorem dens_smul (c : ℂ) (x : Alt n) : dens (c • x) = c * dens x := by
  simp only [dens, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_div_assoc]

theorem reDens_add (α β : A.Fld) (i : A.ι) (v : V n) :
    A.reDens (α + β) i v = A.reDens α i v + A.reDens β i v := by
  simp only [HolAtlas.reDens, loc_add, dens_add, Complex.add_re]

theorem reDens_smul (t : ℝ) (α : A.Fld) (i : A.ι) (v : V n) :
    A.reDens ((t : ℂ) • α) i v = t * A.reDens α i v := by
  simp only [HolAtlas.reDens, loc_smul, dens_smul, Complex.re_ofReal_mul]

variable [MeasurableSpace M]

def G (r : A.ι → V n → ℝ) : Measure M := glueMeas A.e fun i y => ENNReal.ofReal (r i (A.e i y))

def Good (r : A.ι → V n → ℝ) : Prop :=
  (∀ i, ContinuousOn (r i) (A.e i).target) ∧
  ∀ i j y, y ∈ (A.e i).source → y ∈ (A.e j).source →
    r i (A.e i y) = ‖ChartGlue.transDet (A.e i) (A.e j) y‖ ^ 2 * r j (A.e j y)

theorem part_eq (γ : A.Fld) (ε : ℤˣ) (r : A.ι → V n → ℝ) (h : ∀ i v, ((ε : ℤ) : ℝ) * A.reDens γ i v = r i v) :
    A.part γ ε = G A r := by
  simp only [HolAtlas.part, G]
  congr 1
  funext i y
  rw [← h]
  rfl

theorem good_lin {α : A.Fld} (hα : A.IsForm α) (c : ℝ) : Good A fun i v => c * A.reDens α i v :=
  ⟨fun i => continuousOn_const.mul (A.continuousOn_reDens hα i),
    fun i j y hi hj => by simp only [A.reDens_compat hα i j y hi hj]; ring⟩

theorem isJacobianCompatibleDensity_linearCombination_realDensity {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) (c d : ℝ) :
    Good A fun i v => c * A.reDens α i v + d * A.reDens β i v :=
  ⟨fun i => (continuousOn_const.mul (A.continuousOn_reDens hα i)).add
      (continuousOn_const.mul (A.continuousOn_reDens hβ i)),
    fun i j y hi hj => by simp only [A.reDens_compat hα i j y hi hj, A.reDens_compat hβ i j y hi hj]; ring⟩

theorem glueMeas_mono [BorelSpace M] {ρ ρ' : A.ι → M → ℝ≥0∞} (h : ∀ i y, ρ i y ≤ ρ' i y) :
    glueMeas A.e ρ ≤ glueMeas A.e ρ' := by
  unfold glueMeas
  exact iSup_mono fun i => Measure.le_iff.2 fun S hS => by
    rw [chartMeas_apply _ _ hS, chartMeas_apply _ _ hS]
    exact lintegral_mono fun v => h i _

variable [BorelSpace M] [SecondCountableTopology M]

theorem aem {r : A.ι → V n → ℝ} (hr : Good A r) (i : A.ι) (S : Set M) :
    AEMeasurable (fun v => ENNReal.ofReal (r i (A.e i ((A.e i).symm v))))
      (volume.restrict ((A.e i).target ∩ (A.e i).symm ⁻¹' S)) :=
  (HolAtlas.aemeasurable_ofReal_chart (A.e i) (r i) (hr.1 i)).mono_measure
    (Measure.restrict_mono (inter_subset_inter_right _ (preimage_mono (subset_univ S))) le_rfl)

theorem G_add {r₁ r₂ : A.ι → V n → ℝ} (h₁ : Good A r₁) (h₂ : Good A r₂) :
    glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y))) = G A r₁ + G A r₂ := by
  ext S hS
  rw [Measure.add_apply]
  exact glueMeas_add_of_compat_on A.e A.holo A.cover hS _ _
    (fun i j y _ hi hj => A.ofReal_compat r₁ h₁.2 i j y hi hj)
    (fun i j y _ hi hj => A.ofReal_compat r₂ h₂.2 i j y hi hj) (fun i => aem A h₁ i S)

theorem holAtlasGluedDensityMeasure_add_three {r₁ r₂ r₃ : A.ι → V n → ℝ} (h₁ : Good A r₁) (h₂ : Good A r₂) (h₃ : Good A r₃) :
    glueMeas A.e (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)) +
      ENNReal.ofReal (r₃ i (A.e i y))) = G A r₁ + G A r₂ + G A r₃ := by
  ext S hS
  have c₁ := A.ofReal_compat r₁ h₁.2
  have c₂ := A.ofReal_compat r₂ h₂.2
  have c₃ := A.ofReal_compat r₃ h₃.2
  rw [Measure.add_apply, Measure.add_apply,
    glueMeas_add_of_compat_on A.e A.holo A.cover hS
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y)) + ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i y => ENNReal.ofReal (r₃ i (A.e i y)))
      (fun i j y _ hi hj => by rw [c₁ i j y hi hj, c₂ i j y hi hj, mul_add])
      (fun i j y _ hi hj => c₃ i j y hi hj)
      (fun i => (aem A h₁ i S).add (aem A h₂ i S)),
    glueMeas_add_of_compat_on A.e A.holo A.cover hS
      (fun i y => ENNReal.ofReal (r₁ i (A.e i y))) (fun i y => ENNReal.ofReal (r₂ i (A.e i y)))
      (fun i j y _ hi hj => c₁ i j y hi hj) (fun i j y _ hi hj => c₂ i j y hi hj)
      (fun i => aem A h₁ i S)]
  rfl

theorem G_smul {r : A.ι → V n → ℝ} (h : Good A r) {c : ℝ} (hc : 0 ≤ c) :
    G A (fun i v => c * r i v) = ENNReal.ofReal c • G A r := by
  have hc' : Good A (fun i v => c * r i v) :=
    ⟨fun i => continuousOn_const.mul (h.1 i), fun i j y hi hj => by simp only [h.2 i j y hi hj]; ring⟩
  refine ext_of_cover (fun i => (A.e i).source) (fun i => (A.e i).open_source) A.cover fun i S hS hSi => ?_
  rw [Measure.smul_apply, G, G, glueMeas_apply _ _ A.holo (fun i j y hi hj => A.ofReal_compat (fun i v => c * r i v) hc'.2 i j y hi hj) i hS hSi,
    glueMeas_apply _ _ A.holo (fun i j y hi hj => A.ofReal_compat _ h.2 i j y hi hj) i hS hSi,
    chartMeas_apply_of_subset _ _ hS hSi, chartMeas_apply_of_subset _ _ hS hSi, smul_eq_mul,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_congr fun v => ?_
  rw [ENNReal.ofReal_mul hc]

theorem part_finite [CompactSpace M] {α : A.Fld} (hα : A.IsForm α) (ε : ℤˣ) : IsFiniteMeasure (A.part α ε) := by
  have h := good_lin A hα ((ε : ℤ) : ℝ)
  have e : A.part α ε = G A (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) := part_eq A α ε _ fun _ _ => rfl
  have fin : G A (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) univ ≠ ∞ :=
    GlobalTheory.T.glueMeas_univ_ne_infty_of_continuousOn A.e A.cover A.holo (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) h.1 h.2
  refine ⟨?_⟩
  rw [e]
  exact lt_top_iff_ne_top.2 fin

theorem part_add_le {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) (ε : ℤˣ) :
    A.part (α + β) ε ≤ A.part α ε + A.part β ε := by
  rw [part_eq A (α + β) ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v + ((ε : ℤ) : ℝ) * A.reDens β i v)
      fun i v => by rw [reDens_add, mul_add],
    part_eq A α ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    part_eq A β ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens β i v) fun _ _ => rfl,
    ← G_add A (good_lin A hα _) (good_lin A hβ _)]
  exact glueMeas_mono A fun i y => ENNReal.ofReal_add_le

theorem part_balance {α β : A.Fld} (hα : A.IsForm α) (hβ : A.IsForm β) :
    A.part (α + β) 1 + A.part α (-1) + A.part β (-1) = A.part (α + β) (-1) + A.part α 1 + A.part β 1 := by
  rw [part_eq A (α + β) 1 (fun i v => 1 * A.reDens α i v + 1 * A.reDens β i v)
      fun i v => by simp [reDens_add],
    part_eq A α (-1) (fun i v => (-1) * A.reDens α i v + 0 * A.reDens β i v) fun i v => by simp,
    part_eq A β (-1) (fun i v => 0 * A.reDens α i v + (-1) * A.reDens β i v) fun i v => by simp,
    part_eq A (α + β) (-1) (fun i v => (-1) * A.reDens α i v + (-1) * A.reDens β i v)
      fun i v => by simp [reDens_add]; ring,
    part_eq A α 1 (fun i v => 1 * A.reDens α i v + 0 * A.reDens β i v) fun i v => by simp,
    part_eq A β 1 (fun i v => 0 * A.reDens α i v + 1 * A.reDens β i v) fun i v => by simp,
    ← holAtlasGluedDensityMeasure_add_three A (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _),
    ← holAtlasGluedDensityMeasure_add_three A (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _) (isJacobianCompatibleDensity_linearCombination_realDensity A hα hβ _ _)]
  congr 1
  funext i y
  have := HolAtlas.ofReal_posNeg (A.reDens α i (A.e i y)) (-A.reDens β i (A.e i y))
  convert this using 3 <;> ring_nf

theorem part_smul_nonneg {α : A.Fld} (hα : A.IsForm α) {t : ℝ} (ht : 0 ≤ t) (ε : ℤˣ) :
    A.part ((t : ℂ) • α) ε = ENNReal.ofReal t • A.part α ε := by
  rw [part_eq A ((t : ℂ) • α) ε (fun i v => t * (((ε : ℤ) : ℝ) * A.reDens α i v))
      fun i v => by rw [reDens_smul]; ring,
    part_eq A α ε (fun i v => ((ε : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    G_smul A (good_lin A hα _) ht]

theorem part_smul_nonpos {α : A.Fld} (hα : A.IsForm α) {t : ℝ} (ht : t ≤ 0) (ε : ℤˣ) :
    A.part ((t : ℂ) • α) ε = ENNReal.ofReal (-t) • A.part α (-ε) := by
  rw [part_eq A ((t : ℂ) • α) ε (fun i v => (-t) * ((((-ε : ℤˣ) : ℤ) : ℝ) * A.reDens α i v))
      fun i v => by rw [reDens_smul, Units.val_neg, Int.cast_neg]; ring,
    part_eq A α (-ε) (fun i v => (((-ε : ℤˣ) : ℤ) : ℝ) * A.reDens α i v) fun _ _ => rfl,
    G_smul A (good_lin A hα _) (neg_nonneg.2 ht)]

theorem part_congr {α β : A.Fld} (h : ∀ x, dens (α x) = dens (β x)) (ε : ℤˣ) : A.part α ε = A.part β ε := by
  simp only [HolAtlas.part]
  congr 1
  funext i y
  congr 3
  unfold HolAtlas.loc
  split_ifs
  · exact h _
  · rfl

end GlobalTheory.LineForm.TopInt

namespace GlobalTheory.LineForm

open GlobalTheory.LineForm.TopInt

theorem wInt_props : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    (∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, IsFiniteMeasure (A.part α ε)) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), A.IsForm α → A.IsForm β → (∀ ε : ℤˣ, Integrable g (A.part α ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part β ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part (α + β) ε)) ∧ wInt A g (α + β) = wInt A g α + wInt A g β) ∧
    (∀ (g : M → ℝ) (t : ℝ) (α : A.Fld), A.IsForm α → wInt A g ((t : ℂ) • α) = t * wInt A g α) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), (∀ x, dens (α x) = dens (β x)) → wInt A g α = wInt A g β) := by
  intro M _ _ _ _ _ _ n A
  refine ⟨fun α hα ε => part_finite A hα ε, fun g α β hα hβ ga gb => ?_, fun g t α hα => ?_,
    fun g α β h => by simp only [wInt, part_congr A h]⟩
  · have gs : ∀ ε : ℤˣ, Integrable g (A.part (α + β) ε) := fun ε =>
      ((ga ε).add_measure (gb ε)).mono_measure (part_add_le A hα hβ ε)
    refine ⟨gs, ?_⟩
    have key := congrArg (fun μ : Measure M => ∫ y, g y ∂μ) (part_balance A hα hβ)
    rw [integral_add_measure (((gs 1).add_measure (ga (-1)))) (gb (-1)),
      integral_add_measure (gs 1) (ga (-1)),
      integral_add_measure (((gs (-1)).add_measure (ga 1))) (gb 1),
      integral_add_measure (gs (-1)) (ga 1)] at key
    simp only [wInt]
    linarith
  · rcases le_total 0 t with ht | ht
    · simp only [wInt, part_smul_nonneg A hα ht, integral_smul_measure, ENNReal.toReal_ofReal ht, smul_eq_mul]
      ring
    · simp only [wInt, part_smul_nonpos A hα ht, integral_smul_measure, ENNReal.toReal_ofReal (neg_nonneg.2 ht),
        smul_eq_mul, neg_neg]
      ring

end GlobalTheory.LineForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasTopFormIntegralFiniteAdditiveHomogeneousStatement
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_topFormIntegral_finite_additive_homogeneous : ∀ (M : Type) [TopologicalSpace M] [T2Space M] [SecondCountableTopology M] [CompactSpace M] [MeasurableSpace M] [BorelSpace M] (n : ℕ) (A : HolAtlas M n),
    (∀ α : A.Fld, A.IsForm α → ∀ ε : ℤˣ, IsFiniteMeasure (A.part α ε)) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), A.IsForm α → A.IsForm β → (∀ ε : ℤˣ, Integrable g (A.part α ε)) → (∀ ε : ℤˣ, Integrable g (A.part β ε)) →
      (∀ ε : ℤˣ, Integrable g (A.part (α + β) ε)) ∧ wInt A g (α + β) = wInt A g α + wInt A g β) ∧
    (∀ (g : M → ℝ) (t : ℝ) (α : A.Fld), A.IsForm α → wInt A g ((t : ℂ) • α) = t * wInt A g α) ∧
    (∀ (g : M → ℝ) (α β : A.Fld), (∀ x, dens (α x) = dens (β x)) → wInt A g α = wInt A g β) := by
  exact @GlobalTheory.LineForm.wInt_props
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUnique
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUnique
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT.MapUniq

open GlobalTheory.UPel.HT.MapComp

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_auto {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o' : Obj b N s'} {o : Obj b N s}
    {f : S' ⟶ S} (m m' : ObjMap o' o f) : ∃ a : ObjMap o' o' (𝟙 S'), a.φ ≫ m'.φ = m.φ := by
  have w : m.φ ≫ o.A.hom = o'.A.hom ≫ f := m.cart.1.w
  set ψ := m'.cart.1.lift m.φ o'.A.hom w
  have hψ : ψ ≫ m'.φ = m.φ := m'.cart.1.lift_fst _ _ _
  have hψ₀ : ψ ≫ o'.A.hom = o'.A.hom := m'.cart.1.lift_snd _ _ _
  have hψ' : ψ ≫ o'.A.hom = o'.A.hom ≫ 𝟙 S' := by rw [Category.comp_id]; exact hψ₀
  have n : IsGrpPullback o'.A o.A (𝟙 S' ≫ f) (ψ ≫ m'.φ) := by rw [hψ, Category.id_comp]; exact m.cart
  obtain ⟨ψ₂, sq⟩ := exists_isSquare hψ'
  have e : m.φ₂ = ψ₂ ≫ m'.φ₂ := isSquare_unique m.sq (hψ ▸ isSquare_comp sq m'.sq)
  have hact : ∀ c, (o'.act.act c).left ≫ ψ = ψ ≫ (o'.act.act c).left := by
    intro c
    apply m'.cart.1.hom_ext
    · rw [Category.assoc, hψ, m.act, Category.assoc, m'.act, ← Category.assoc, hψ]
    · rw [Category.assoc, hψ₀, Over.w, Category.assoc, Over.w, hψ₀]
  have heta : ∀ y, (o'.eta y).left ≫ ψ = 𝟙 S' ≫ (o'.eta y).left := by
    intro y
    apply m'.cart.1.hom_ext
    · rw [Category.assoc, hψ, m.eta, Category.id_comp, m'.eta]
    · rw [Category.assoc, hψ₀, Category.id_comp]
  exact ⟨{ φ := ψ
           φ₂ := ψ₂
           cart := m'.cart.cancel n hψ'
           sq := sq
           act := hact
           pol := LBIso.trans o'.isLB (pull_isLB o.isLB _) (pull_isLB o'.isLB _) m.pol
             (LBIso.symm (lbIso_pull_comp m'.pol ψ₂ e))
           eta := heta }, hψ⟩

theorem objMap_φ_unique : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R)
    (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o' : Obj b N s')
    (o : Obj b N s) (f : S' ⟶ S) (m m' : ObjMap o' o f), m.φ = m'.φ := by
  intro p _ D R _ b N hN hNp S S' s s' o' o f m m'
  obtain ⟨a, ha⟩ := exists_auto m m'
  have h1 := GlobalTheory.UPel.HT.Rigid.eq_id p D R b N hN hNp S' s' o' a
  rw [← ha, h1, Category.id_comp]

end GlobalTheory.UPel.HT.MapUniq
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackAbelianMapUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S S' : Scheme.{0}) (s : S ⟶ Sp R) (s' : S' ⟶ Sp R) (o' : Obj b N s') (o : Obj b N s) (f : S' ⟶ S) (m m' : ObjMap o' o f), m.φ = m'.φ := by
  first | exact @GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique | exact GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique | (intros; apply GlobalTheory.UPel.HT.MapUniq.objMap_φ_unique <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section

namespace GlobalTheory.Poinc.TorsRatio

variable {V : Type} [CommRing V] [IsDomain V]

def cstK (z : (TFK (R := V) (FractionRing V)).left) :
    FractionRing V →+* (TFK (R := V) (FractionRing V)).left.presheaf.stalk z :=
  ((TFK (R := V) (FractionRing V)).left.presheaf.germ ⊤ z trivial).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv.hom

theorem cst_eq_cstK (z : (TFK (R := V) (FractionRing V)).left) (a : FractionRing V) :
    GlobalTheory.UT.cst (R := V) (FractionRing V) z a = cstK z a :=
  gs_eq (𝟙 _) z ⊤ trivial _

theorem pt_eq (z z' : (TFK (R := V) (FractionRing V)).left) : z = z' :=
  Subsingleton.elim (α := PrimeSpectrum (FractionRing V)) z z'

theorem cstK_surj (z : (TFK (R := V) (FractionRing V)).left) : Function.Surjective (cstK (V := V) z) := by
  intro a
  obtain ⟨U, hU, s, rfl⟩ := (TFK (R := V) (FractionRing V)).left.presheaf.germ_exist a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => pt_eq z y ▸ hU
  obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (FractionRing V))).inv).2 s
  exact ⟨x, congrArg ((TFK (R := V) (FractionRing V)).left.presheaf.germ ⊤ z trivial).hom hx⟩

theorem frame_ratio {A : PolAV (Sp (FractionRing V))} {x : TFK (R := V) (FractionRing V) ⟶ A.A} {e e' : FrAt x}
    (he : e.IsGen) (he' : e'.IsGen) : ∃ l : FractionRing V, l ≠ 0 ∧ ∀ z J, Good A.L z J →
      (Geo.Tor.val e' (𝟙 _) z J).val = cstK z l * (Geo.Tor.val e (𝟙 _) z J).val := by
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J' hJ' using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ' : Good A.L z J' := hJ'
  obtain ⟨l, hl⟩ := cstK_surj z (Geo.Tor.val e' (𝟙 _) z J' * (Geo.Tor.val e (𝟙 _) z J')⁻¹).val
  refine ⟨l, fun h => ?_, fun z' J hJ => ?_⟩
  · rw [h, map_zero] at hl
    exact Units.ne_zero _ hl.symm
  · obtain rfl := pt_eq z z'
    have t₁ : Geo.Tor.val e (𝟙 _) z J = _ * Geo.Tor.val e (𝟙 _) z J' :=
      gen_trans he (𝟙 _) z (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    have t₂ : Geo.Tor.val e' (𝟙 _) z J = _ * Geo.Tor.val e' (𝟙 _) z J' :=
      gen_trans he' (𝟙 _) z (hJ.mem _ (𝟙 _)) (hJ'.mem _ (𝟙 _))
    rw [hl, t₁, t₂, ← Units.val_mul]
    congr 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel

end GlobalTheory.Poinc.TorsRatio

namespace GlobalTheory.Poinc.TorsRatio

theorem valAt_torsFrame_ratio : ∀ (V : Type) [CommRing V] [IsDomain V] (A : PolAV (Sp (FractionRing V)))
    (ρA : LB.Gen (A.L.pull (eSec A.A))), ρA.IsGen → ∀ (N : ℕ), 1 ≤ N →
    ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e e' : FrAt x), IsTorsFrame A ρA N x e → IsTorsFrame A ρA N x e' →
    ∀ (th : SecA A (FractionRing V) 1) (c : FractionRing V), ValAt th x e c →
      ∃ u : FractionRing V, u ^ (N ^ 2) = 1 ∧ ValAt th x e' (u * c) := by
  intro V _ _ A ρA _ N _ x e e' H H' th c hv
  obtain ⟨-, he, α, hα, nα, cα⟩ := H
  obtain ⟨-, he', α', hα', nα', cα'⟩ := H'
  obtain ⟨l, hl0, hl⟩ := frame_ratio he he'

  have hp : Function.Surjective A.A.hom.appTop.hom := (GlobalTheory.globalFns_holds _ _ A.isAb).2
  have hαα : ∀ (Z : Scheme.{0}) (r : Z ⟶ A.A.left) (z : Z) J, Good A.L z J →
      Geo.Tor.val α r z J = Geo.Tor.val α' r z J :=
    gen_unique A.isLB A.A.hom (eSec A.A) (Over.w η[A.A]) hp hα hα' (fun w I hI => by
      have a := val_corr hI nα (𝟙 _)
      have b := val_corr hI nα' (𝟙 _)
      rw [val_pull hI, Category.id_comp] at a b
      exact a.trans b.symm)
  let z : (TFK (R := V) (FractionRing V)).left := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V))
  choose J hJ using fun χ : (TFK (R := V) (FractionRing V)).left ⟶ A.A.left => Geo.Tor.exists_chart A.isLB (χ z)
  replace hJ : Good A.L z J := hJ
  have q : Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) = Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := by
    have a := val_corr hJ cα (𝟙 _)
    have b := val_corr hJ cα' (𝟙 _)
    have p₁ : Geo.Tor.val (powFrame A.A A.L x e ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    have p₂ : Geo.Tor.val (powFrame A.A A.L x e' ((N : ℤ) ^ 2)) (𝟙 _) z J =
      Geo.Tor.val e' (𝟙 _) z J ^ ((N : ℤ) ^ 2) := map_zpow _ _ _
    rw [val_mul hJ, val_pull hJ] at a b
    rw [← p₁, ← p₂, a, b, hαα _ _ z J hJ]
  have hlN : l ^ (N ^ 2) = 1 := by
    have q' := congrArg Units.val q
    rw [show ((N : ℤ) ^ 2) = ((N ^ 2 : ℕ) : ℤ) by push_cast; ring, zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, hl z J hJ, mul_pow, ← map_pow] at q'
    have hu : IsUnit ((Geo.Tor.val e (𝟙 _) z J).val ^ (N ^ 2)) := (Units.isUnit _).pow _
    have h1 : cstK z (l ^ (N ^ 2)) = cstK z 1 := by
      rw [map_one]
      exact hu.mul_left_inj.1 (by rw [_root_.one_mul]; exact q'.symm)
    exact (cstK z).injective h1
  refine ⟨l⁻¹, by rw [inv_pow, hlN, inv_one], fun z' J' hJ' => ?_⟩
  rw [hv z' J' hJ']
  have r₁ : Geo.Tor.val (powFrame A.A A.L x e ((1 : ℕ) : ℤ)) (𝟙 _) z' J' = Geo.Tor.val e (𝟙 _) z' J' ^ ((1 : ℕ) : ℤ) :=
    map_zpow _ _ _
  have r₂ : Geo.Tor.val (powFrame A.A A.L x e' ((1 : ℕ) : ℤ)) (𝟙 _) z' J' =
      Geo.Tor.val e' (𝟙 _) z' J' ^ ((1 : ℕ) : ℤ) := map_zpow _ _ _
  rw [r₁, r₂, Nat.cast_one, zpow_one, zpow_one, hl z' J' hJ']
  simp only [id, cst_eq_cstK]
  rw [← _root_.mul_assoc, ← map_mul, mul_comm l⁻¹ c, inv_mul_cancel_right₀ hl0]

end GlobalTheory.Poinc.TorsRatio
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorsionFramesSectionValuesRatioRootOfUnityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torsionFrames_sectionValues_ratio_rootOfUnity : ∀ (V : Type) [CommRing V] [IsDomain V] (A : PolAV (Sp (FractionRing V))) (ρA : LB.Gen (A.L.pull (eSec A.A))), ρA.IsGen → ∀ (N : ℕ), 1 ≤ N → ∀ (x : TFK (R := V) (FractionRing V) ⟶ A.A) (e e' : FrAt x), IsTorsFrame A ρA N x e → IsTorsFrame A ρA N x e' → ∀ (th : SecA A (FractionRing V) 1) (c : FractionRing V), ValAt th x e c → ∃ u : FractionRing V, u ^ (N ^ 2) = 1 ∧ ValAt th x e' (u * c) := by
  first | exact @GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio | exact GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio | (intros; apply GlobalTheory.Poinc.TorsRatio.valAt_torsFrame_ratio <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernPartCombinationPower
set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxForm GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.Cartier GlobalTheory.CovTest GlobalTheory.LineForm
open GlobalTheory.Points GlobalTheory.HermFrame
open scoped Classical

namespace GlobalTheory.ChernTop

variable {n : ℕ}

def rowForm (a : Fin n) : (Fin n → ℂ) →ₗ[ℂ] Ev n := Fintype.linearCombination ℂ fun b => sym (a, b)

def matForm (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Ev n where
  toFun H := kappa • ∑ a, rowForm a (H a)
  map_add' H H' := by
    rw [← smul_add, ← Finset.sum_add_distrib]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_add _ _ _)
  map_smul' c H := by
    rw [RingHom.id_apply, smul_comm, Finset.smul_sum (r := c)]
    exact congrArg _ (Finset.sum_congr rfl fun a _ => map_smul (rowForm a) c (H a))

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ} {σ : k →+* ℂ}

variable {c : AlgChart p σ D} {y : CxPts p σ}

end GlobalTheory.ChernTop
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidificationMatchingFramesTorsionFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidificationMatchingFramesTorsionFrames
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

noncomputable section
open Classical

namespace GlobalTheory.Poinc.IntTerm

theorem exists_rig_torsFrame_of_match : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∃ ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A)), ρA.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  intro g n F W Z i X₁ z₁ act V _ _ _ ev X _ m t δ 𝔪 x fr hx hfr
  have gp := 𝔪.cart
  have hw := 𝔪.wl_gen
  obtain ⟨rig', hrig', Hr⟩ := GlobalTheory.ConstFam.exists_gen_through (K := PUnit) (φ' := fun _ => eSec 𝔪.A.A)
    (φ := fun _ => eSec X₁.ρ.P.A) (ε := fun _ => 1) (h := spMap 𝔪.yK) hw X₁.ρ.P.isLB 𝔪.A.isLB
    (fun _ => PolBaseChange.eSec_comm gp) X₁.ρ.rig X₁.ρ.rig_gen
  have hr : ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over _)).left) (z : Z) J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' →
      GlobalTheory.FrameMove.rval X₁.ρ.rig (r ≫ spMap 𝔪.yK) z J = GlobalTheory.ConstFam.wVal 𝔪.wl z J J' (r ≫ eSec 𝔪.A.A) * GlobalTheory.FrameMove.rval rig' r z J' :=
    fun Z r z J J' hJ hJ' =>
      (Hr Z r z J J' hJ hJ').trans (congrArg (· * _) ((Fintype.prod_unique _).trans (zpow_one _)))
  refine ⟨rig', hrig', fun a => ?_⟩
  exact GlobalTheory.FrameMove.isTorsFrame_move gp hw hr (hx a) (X₁.ρ.fr_tors a) (hfr a).1
    (fun z J J' hJ hJ' => ((hfr a).2 z J J' hJ hJ').symm)

end GlobalTheory.Poinc.IntTerm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRigidificationMatchingFramesTorsionFramesStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_rigidification_matchingFrames_torsionFrames : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (act : Matrix (Fin 8) (Fin 8) ℤ → (X₁.ρ.P.A ⟶ X₁.ρ.P.A)) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ev : X₁.M.Z.presheaf.stalk z₁ →+* V) (X : Type) [AddCommGroup X] (m : ℕ) (t : Fin m → V) (δ : Fin m → LinearMap.BilinForm ℤ X) (𝔪 : UMem X₁ z₁ act V ev X t δ), ∀ (x : X₁.S.Gam → (TFK (R := V) (FractionRing V) ⟶ 𝔪.A.A)) (fr : ∀ a, FrAt (x a)), (∀ a, (x a).left ≫ 𝔪.φ = spMap 𝔪.yK ≫ (X₁.ρ.pt a).left) → (∀ a, (fr a).IsGen ∧ ∀ z J J', Good X₁.ρ.P.L z J → Good 𝔪.A.L z J' → Geo.Tor.gw 𝔪.wl (x a).left z (J ((x a).left ≫ 𝔪.φ)) (J' (x a).left) * val (fr a) (𝟙 _) z J' = val (X₁.ρ.fr a) (show (TFK (R := V) (FractionRing V)).left ⟶ (baseOver (Sp X₁.S.R)).left from spMap 𝔪.yK) z J) → ∃ ρA : LB.Gen (𝔪.A.L.pull (eSec 𝔪.A.A)), ρA.IsGen ∧ ∀ a, IsTorsFrame 𝔪.A ρA (X₁.S.r * X₁.S.N) (x a) (fr a) := by
  first | exact @GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match | exact GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match | (intros; apply GlobalTheory.Poinc.IntTerm.exists_rig_torsFrame_of_match <;> assumption)
end
end
