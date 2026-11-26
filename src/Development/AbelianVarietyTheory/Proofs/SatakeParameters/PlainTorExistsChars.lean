module

public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsMidLevIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSolvableCmExtensionSplitPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.PlainTorExistsChars
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open Polynomial hiding funext
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RoadU.PlainChars

theorem exists_fin_enum {S : Type*} (t : Multiset S) {n : ℕ} (hn : Multiset.card t = n) :
    ∃ ξ : Fin n → S, Finset.univ.val.map ξ = t := by
  subst hn
  refine ⟨fun j => t.toList.get (Fin.cast (by simp) j), ?_⟩
  rw [Fin.univ_val_map]
  conv_rhs => rw [← Multiset.coe_toList t]
  congr 1
  apply List.ext_get (by simp)
  intro i h1 h2
  simp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem exists_eq_ofChar (x : IrrGL (k := k)) (hx : x.1 = 1) : ∃ θ hθ, x = IrrGL.ofChar θ hθ := by
  obtain ⟨n, c⟩ := x
  obtain rfl : n = 1 := hx
  obtain ⟨θ, hθ, ⟨e⟩⟩ := RankLeOne.exists_equiv_detRep k (Fin 1) _ c.rep.ρ c.rep.smooth c.rep.irr
  exact ⟨θ, hθ, congrArg (Sigma.mk 1) (c.cl_rep.symm.trans (IrrRep.cl_eq_iff.2 ⟨e⟩))⟩

end GlobalTheory.RoadU.PlainChars

theorem GlobalTheory.RoadU.plainTor_exists_chars : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)), PlainTor x → ∃ (ξ : Fin x.1 → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)), HasSupport x.rep (chars ξ hξ) ∧ Unlinked (chars ξ hξ) := by
  intro k _ _ _ _ _ x ⟨s, hs, h1, hu⟩
  let S := {χ : kˣ →* ℂˣ // IsSmoothChar χ}
  let F : S → IrrGL (k := k) := fun χ => IrrGL.ofChar χ.1 χ.2
  obtain ⟨t, rfl⟩ : ∃ t : Multiset S, t.map F = s :=
    haveI : CanLift (IrrGL (k := k)) S F fun y => ∃ χ, F χ = y := ⟨fun _ hy => hy⟩
    (Multiset.canLift F (fun y => ∃ χ, F χ = y)).prf s fun y hy => by
      obtain ⟨χ, hχ, e⟩ := PlainChars.exists_eq_ofChar y (h1 y hy)
      exact ⟨⟨χ, hχ⟩, e.symm⟩
  have hcard : Multiset.card t = x.1 := by
    have h2 := hs.sum_fst
    rw [Multiset.map_map] at h2
    have h3 : t.map (Sigma.fst ∘ F) = Multiset.replicate (Multiset.card t) 1 :=
      Multiset.eq_replicate.2 ⟨by simp, fun b hb => by
        obtain ⟨χ, -, rfl⟩ := Multiset.mem_map.1 hb
        rfl⟩
    rw [h3, Multiset.sum_replicate, smul_eq_mul, mul_one, Fintype.card_fin] at h2
    exact h2
  obtain ⟨ξ, hξ⟩ := PlainChars.exists_fin_enum t hcard
  have hc : chars (fun j => (ξ j).1) (fun j => (ξ j).2) = t.map F := by
    rw [← hξ, Multiset.map_map]
    rfl
  exact ⟨fun j => (ξ j).1, fun j => (ξ j).2, hc ▸ hs, hc ▸ hu⟩
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatWDCharPolChars
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open Polynomial hiding funext
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.SatChar

variable {Ω : Type} [Field Ω] {E : Type} [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω]
  {w : HeightOneSpectrum (𝓞 E)} {A : ValuationSubring Ω}

theorem charPol_satWD (h : IsPlaceOver A w) (n : ℕ) (B : Multiset ℂˣ) (g : Weil h) :
    (satWD h n B).charPol g = (B.map fun b : ℂˣ =>
      X - C ((((normV w : ℕ) : ℂ) ^ (((((1 : ℝ) - n) / 2 : ℝ)) : ℂ)) ^ deg g * ((b : ℂ)⁻¹) ^ deg g)).prod := by
  classical
  have hs : ∀ {ι : Type} (c : ℂ) (d : ι → ℂ), c • WeilDeligne.diagEnd d = WeilDeligne.diagEnd (fun i => c * d i) := fun c d =>
    LinearMap.ext fun v => funext fun i => by simp [WeilDeligne.diagEnd_apply, mul_assoc]
  rw [satWD, WD.lpUnr, WD.lpTw_mk, WD.charPol_mk, WDRep.tw_ρ, WDRep.diag_ρ, hs, charpoly_diagEnd,
    ← Finset.prod_map_val]
  rw [Multiset.map_univ (B.map fun b : ℂˣ => ((b⁻¹ : ℂˣ) : ℂ))
    (fun z : ℂ => X - C ((((normV w : ℕ) : ℂ) ^ ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) ^ deg g * ((WD.unitOf z : ℂˣ) : ℂ) ^ deg g)),
    Multiset.map_map]
  refine congrArg _ (Multiset.map_congr rfl fun b _ => ?_)
  simp only [Function.comp_apply]
  rw [WD.coe_unitOf (by simp), Units.val_inv_eq_inv_val]

def ordHom (w : HeightOneSpectrum (𝓞 E)) : (w.adicCompletion E)ˣ →* Multiplicative ℤ :=
  MonoidHom.mk' (fun x => Multiplicative.ofAdd (ord (w.adicCompletion E) x)) fun x y => by
    rw [ord_mul, ofAdd_add]

theorem unram_art {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a)
    (χ : (w.adicCompletion E)ˣ →* ℂˣ) (hχ : ∀ x : (w.adicCompletion E)ˣ, Valued.v (x : w.adicCompletion E) = 1 → χ x = 1)
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ)) (g : Weil h) :
    χ (a g) = χ ϖ ^ (-deg g) := by
  have h1 : ord (w.adicCompletion E) ϖ = 1 := by
    rw [SphCompletion.ord_completion, hϖ, WithZero.log_exp]; simp
  have h2 : ord (w.adicCompletion E) (a g * ϖ ^ deg g) = 0 := by
    have := congrArg Multiplicative.toAdd (map_mul (ordHom w) (a g) (ϖ ^ deg g))
    rw [map_zpow] at this
    simp only [ordHom, MonoidHom.mk'_apply, toAdd_ofAdd, toAdd_mul, toAdd_zpow, smul_eq_mul] at this
    rw [this, ha.ord_eq, h1]; ring
  have h3 : Valued.v ((a g * ϖ ^ deg g : (w.adicCompletion E)ˣ) : w.adicCompletion E) = 1 := by
    rw [SphCompletion.ord_completion, neg_eq_zero] at h2
    have h0 : Valued.v ((a g * ϖ ^ deg g : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≠ 0 :=
      (Valuation.ne_zero_iff _).2 (Units.ne_zero _)
    rw [← WithZero.exp_log h0, h2, WithZero.exp_zero]
  have h4 : a g = (a g * ϖ ^ deg g) * ϖ ^ (-deg g) := by
    rw [mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, mul_one]
  rw [h4, map_mul, hχ _ h3, one_mul, map_zpow]

theorem absPow_art {h : IsPlaceOver A w} {a : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h a) (s : ℝ)
    (g : Weil h) :
    (absPow (w.adicCompletion E) (s : ℂ) (a g) : ℂ) = (((normV w : ℕ) : ℂ) ^ (s : ℂ)) ^ deg g := by
  have hq : (0 : ℝ) < ((normV w : ℕ) : ℝ) := by
    have := GlobalTheory.WeilDeligne.one_lt_normV w
    exact_mod_cast (zero_lt_one.trans this)
  rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, ha.ord_eq, neg_neg, resCard_eq_normV]
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_cpow hq.le, ← Complex.ofReal_zpow,
    ← Complex.ofReal_cpow (zpow_pos hq _).le]
  congr 1
  rw [← Real.rpow_intCast, ← Real.rpow_intCast, ← Real.rpow_mul hq.le, ← Real.rpow_mul hq.le, mul_comm]

theorem satWD_charPol_chars : ∀ (Ω : Type) [Field Ω] (E : Type) [Field E] [NumberField E] [Algebra E Ω] [IsAlgClosure E Ω] (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω) (h : IsPlaceOver A w), ∀ (n : ℕ) (ξ ξ' : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)), (∀ j, ξ' j = ξ j * absPow (w.adicCompletion E) ((((1 : ℝ) - n) / 2 : ℝ) : ℂ)) → (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) → ∀ ϖ : (w.adicCompletion E)ˣ, Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) → ∀ a : Weil h →* (w.adicCompletion E)ˣ, IsLocalArtin h a → ∀ g : Weil h, (satWD h n (Finset.univ.val.map fun j => ξ j ϖ)).charPol g = ∏ j, (X - C ((ξ' j (a g) : ℂˣ) : ℂ)) := by
  intro Ω _ E _ _ _ _ w A h n ξ ξ' hξ' hun ϖ hϖ a ha g
  rw [charPol_satWD, Multiset.map_map, Finset.prod_map_val]
  refine Finset.prod_congr rfl fun j _ => ?_
  simp only [Function.comp_apply]
  rw [hξ' j, MonoidHom.mul_apply, Units.val_mul, unram_art ha (ξ j) (hun j) ϖ hϖ g, absPow_art ha]
  congr 2
  rw [Units.val_zpow_eq_zpow_val, zpow_neg, inv_zpow, mul_comm]

end GlobalTheory.SatChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharacters
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharacters
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open Polynomial hiding funext
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.TwistSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nu_nu_neg (x : IrrGL (k := k)) (s : ℂ) : (x.nu s).nu (-s) = x := by
  rw [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]

theorem nu_injective (s : ℂ) : Function.Injective fun x : IrrGL (k := k) => x.nu s := fun x y h => by
  have := congrArg (fun z : IrrGL (k := k) => z.nu (-s)) h
  simpa only [nu_nu_neg] using this

theorem chars_eq_map_nu {n : ℕ} (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j))
    (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ) (h : ∀ j, ξ' j = ξ j * absPow k s) :
    chars ξ' hξ' = (chars ξ hξ).map fun y => y.nu s := by
  unfold chars
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, IrrGL.nu, IrrGL.tw_ofChar]
  exact IrrGL.ofChar_inj.2 (h j)

theorem unlinked_map_nu (m : Multiset (IrrGL (k := k))) (s : ℂ) :
    Unlinked (m.map fun y => y.nu s) ↔ Unlinked m := by
  constructor
  · intro h y hy z hz e
    refine h (y.nu s) (Multiset.mem_map_of_mem _ hy) (z.nu s) (Multiset.mem_map_of_mem _ hz) ?_
    rw [e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]
  · intro h y' hy' z' hz' e
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hy'
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hz'
    refine h y hy z hz (nu_injective s ?_)
    simp only
    rw [e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]

theorem supp_nu_chars : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (n : ℕ) (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ), (∀ j, ξ' j = ξ j * absPow k s) → (HasSupport x.rep (chars ξ hξ) ↔ HasSupport (x.nu s).rep (chars ξ' hξ')) ∧ (Unlinked (chars ξ hξ) ↔ Unlinked (chars ξ' hξ')) := by
  intro k _ _ _ _ _ x n ξ ξ' hξ hξ' s h
  rw [chars_eq_map_nu ξ ξ' hξ hξ' s h, unlinked_map_nu]
  refine ⟨⟨fun H => SupportRing.hasSupport_nu H s, fun H => ?_⟩, Iff.rfl⟩
  have H' := SupportRing.hasSupport_nu H (-s)
  rw [nu_nu_neg, Multiset.map_map] at H'
  simpa only [Function.comp_def, nu_nu_neg, Multiset.map_id'] using H'

end GlobalTheory.RoadU.TwistSupp
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupercuspidalSupportTwistNuCharactersStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open Polynomial hiding funext
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.supercuspidalSupport_twist_nu_characters : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL (k := k)) (n : ℕ) (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ), (∀ j, ξ' j = ξ j * absPow k s) → (HasSupport x.rep (chars ξ hξ) ↔ HasSupport (x.nu s).rep (chars ξ' hξ')) ∧ (Unlinked (chars ξ hξ) ↔ Unlinked (chars ξ' hξ')) := by
  first | (exact @GlobalTheory.RoadU.TwistSupp.supp_nu_chars) | (exact GlobalTheory.RoadU.TwistSupp.supp_nu_chars) | (intros; apply GlobalTheory.RoadU.TwistSupp.supp_nu_chars  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemLatBack
noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Apx

variable {D : D7} {X : Fields} (s : Seam D X)

def apxAt {N : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (n : ℕ)
    (k : GL (Fin N) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Sp X.E N ≃ₗ[X.E] Sp X.E N :=
  Classical.epsilon fun g : Sp X.E N ≃ₗ[X.E] Sp X.E N => NearAt (seamP s P) n k (seamGL s g)

def seamVec (n : ℕ) :
    Sp X.E n →ₛₗ[(RingOfIntegers.mapRingEquiv s.iE : 𝓞 X.E →+* 𝓞 D.host.E)] (Fin n → D.host.E) where
  toFun x l := s.iE (x l)
  map_add' x y := by
    funext l
    simp
  map_smul' r x := by
    funext l
    simp only [Pi.smul_apply, Algebra.smul_def, map_mul]
    rfl

def latBack {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Submodule (𝓞 X.E) (Sp X.E n) :=
  L.comap (seamVec s n)

theorem mem_latBack {n : ℕ} (L : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (y : Sp X.E n) :
    y ∈ latBack s L ↔ (fun l => s.iE (y l)) ∈ L := Iff.rfl

end Apx

section Ad

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (a : 𝓞 D.host.E)

def latAdX (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)) :=
  latBack t.seam (latCo D.sp (gramN D i hi) (A.crd i hi) a x ((St i hi).K β).lev.Lb)




end Ad

end GlobalTheory.TwU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAt
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAt
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct
open Matrix

namespace GlobalTheory.RatInt

theorem mem_range_of_iA_mem {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (a : E) (ha : iA F E a ∈ Formalism.L2.Herm.intAf F E) : a ∈ (algebraMap (𝓞 E) E).range := by
  let Λ : Submodule (𝓞 E) (Fin 1 → E) := Submodule.span (𝓞 E) {fun _ => 1}
  have h1 : (fun _ => 1 : Fin 1 → E) ∈ Λ := Submodule.subset_span rfl
  have hfin : Module.Finite (𝓞 E) Λ := Module.Finite.span_of_finite _ (Set.finite_singleton _)
  have hspan : Submodule.span E (Λ : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have : x = x 0 • (fun _ => 1 : Fin 1 → E) := by
      funext i
      rw [Subsingleton.elim i 0]; simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have hmem : (fun _ => a : Fin 1 → E) ∈ Formalism.UG.CS.globLat (F := F) 1 Λ := by
    show ((1⁻¹ : GL (Fin 1) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin 1) (Fin 1) _) *ᵥ
      (fun _ => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a) ∈
      latS (F := F) (FiniteAdeleRing (𝓞 F) F)
        (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ
    rw [inv_one, Units.val_one, Matrix.one_mulVec]
    have h2 : (fun _ => inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (1 : E)) ∈
        latS (F := F) (FiniteAdeleRing (𝓞 F) F)
          (tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) Λ :=
      Submodule.subset_span ⟨_, h1, rfl⟩
    have h3 := Submodule.smul_mem _ (⟨_, ha⟩ : tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)) h2
    convert h3 using 1
    funext i
    show _ = inclE (F := F) (FiniteAdeleRing (𝓞 F) F) a * inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (1 : E)
    rw [map_one, mul_one]
  rw [Formalism.UG.P.global_lattice_one_holds F E (Fin 1) Λ hfin hspan] at hmem
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
  refine ⟨c, ?_⟩
  have := congrFun hc 0
  simpa [Algebra.smul_def] using this

theorem intAt_of_intAtA : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (x : E), IntAtA (F := F) P (iA F E x) → IntAt P x := by
  intro F E _ _ _ _ _ P x ⟨s, hs, hm⟩
  rw [← map_mul] at hm
  obtain ⟨r, hr⟩ := mem_range_of_iA_mem (F := F) _ hm
  exact ⟨r, s, hs, hr.symm⟩

end GlobalTheory.RatInt
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAtStatement
open NumberField IsDedekindDomain Formalism.UG Formalism.L2.Col
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralAt_of_adelic_integralAt : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (P : HeightOneSpectrum (𝓞 E)) (x : E), IntAtA (F := F) P (iA F E x) → IntAt P x := by
  first | exact @GlobalTheory.RatInt.intAt_of_intAtA | exact GlobalTheory.RatInt.intAt_of_intAtA | (intros; apply GlobalTheory.RatInt.intAt_of_intAtA <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLPrincipalCongruenceOfColsCong
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLPrincipalCongruenceOfColsCong
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

namespace GlobalTheory.CongOne

open GlobalTheory.TopStep GlobalTheory.BlockDecompositionK1

theorem mem_glint_prinCong_of_cols {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E))
    {n : ℕ} (D : ℕ) (k : Sp E n ≃ₗ[E] Sp E n) (hD : 1 ≤ D)
    (h : ∀ s l, IntAt P (((qOf P : E) ^ D)⁻¹ * (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l))) :
    ∃ hk : k ∈ GLint E n P, (⟨k, hk⟩ : GLint E n P) ∈ GlobalTheory.TopStep.prinCong n P D := by
  classical
  have hq : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hqD : ((qOf P : E) ^ D) ≠ 0 := pow_ne_zero _ hq
  have hsingle : ∀ s l, IntAt P ((Pi.single s (1 : E) : Sp E n) l) := fun s l =>
    mem_stdAt.1 (single_mem_stdAt (P := P) s) l
  have hent : ∀ l s, IntAt P (k (Pi.single s (1 : E)) l) := fun l s => by
    have e : k (Pi.single s (1 : E)) l = (qOf P : E) ^ D * (((qOf P : E) ^ D)⁻¹ *
        (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l)) + (Pi.single s (1 : E) : Sp E n) l := by
      field_simp
      ring
    rw [e]
    exact ((intAt_pow (intAt_nat (qOf P)) D).mul (h s l)).add (hsingle s l)
  let A : Matrix (Fin n) (Fin n) E := Matrix.of fun l s => k (Pi.single s (1 : E)) l
  have hA : ∀ l s, IntAt P (A l s) := hent
  have hAx : ∀ x, A.mulVec x = k x := fun x => by
    funext l
    refine Eq.trans ?_ (apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l).symm
    show ∑ s, A l s * x s = _
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [mul_comm]
    rfl
  have hred : A.map (redP P) = 1 := by
    ext l s
    rw [Matrix.map_apply]
    have h0 : redP P (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l) = 0 := by
      obtain ⟨c, rfl⟩ : ∃ c, D = c + 1 := ⟨D - 1, by omega⟩
      exact reduction_eq_zero_of_integral_absNorm_pow_inv_mul (h s l)
    rw [reduction_sub (hent l s) (hsingle s l), sub_eq_zero] at h0
    show redP P (k (Pi.single s (1 : E)) l) = _
    rw [h0, Matrix.one_apply, Pi.single_apply]
    split_ifs
    · exact reduction_one₂
    · exact reduction_zero
  have hdet : IsUnit (redP P A.det) := by
    rw [(det_int hA).2, hred, Matrix.det_one]
    exact isUnit_one
  obtain ⟨j, hj⟩ := exists_glint_of_matrix A hA hdet
  have hjk : j.1 = k := LinearEquiv.ext fun x => (hj x).trans (hAx x)
  have hk : k ∈ GLint E n P := hjk ▸ j.2
  refine ⟨hk, fun x hx => ?_⟩
  refine mem_stdAt.2 fun l => ?_
  have e1 := apply_eq_sum (k : Sp E n →ₗ[E] Sp E n) x l
  have e2 := apply_eq_sum (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l
  have e : (((qOf P : E) ^ D)⁻¹ • (k x - x)) l = ∑ s, x s * (((qOf P : E) ^ D)⁻¹ *
      (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l)) := by
    rw [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
    change ((qOf P : E) ^ D)⁻¹ * ((k : Sp E n →ₗ[E] Sp E n) x l - (LinearMap.id : Sp E n →ₗ[E] Sp E n) x l) = _
    rw [e1, e2, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [LinearMap.id_apply, LinearEquiv.coe_coe]
    ring
  rw [e]
  exact intAt_sum _ fun s _ => (mem_stdAt.1 hx s).mul (h s l)

end GlobalTheory.CongOne
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLPrincipalCongruenceOfColsCongStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_integralGL_principalCongruence_of_cols_cong : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (P : HeightOneSpectrum (𝓞 E)) {n : ℕ} (D : ℕ) (k : Sp E n ≃ₗ[E] Sp E n), 1 ≤ D → (∀ s l, IntAt P (((qOf P : E) ^ D)⁻¹ * (k (Pi.single s (1 : E)) l - (Pi.single s (1 : E) : Sp E n) l))) → ∃ hk : k ∈ GLint E n P, (⟨k, hk⟩ : GLint E n P) ∈ GlobalTheory.TopStep.prinCong n P D := by
  first | exact @GlobalTheory.CongOne.mem_glint_prinCong_of_cols | exact GlobalTheory.CongOne.mem_glint_prinCong_of_cols | (intros; apply GlobalTheory.CongOne.mem_glint_prinCong_of_cols <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

noncomputable section

namespace GlobalTheory.LamRowCong

open GlobalTheory.TopStep

section Gen

variable {E K : Type} [Field E] [NumberField E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem unitV_det_eq_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {t : ℕ} (A : Matrix (Fin t) (Fin t) E)
    (hA : ∀ s s', IntAt P (A s s')) (h1 : A.map (redP P) = 1) : LocE.unitV χ A.det = 1 := by
  have hd : redP P A.det = 1 := by rw [(det_int hA).2, h1, Matrix.det_one]
  have hu : IsUnit (redP P A.det) := hd ▸ isUnit_one
  unfold LocE.unitV
  rw [dite_eq_left hu]
  have : hu.unit = 1 := Units.ext (by simp [hd])
  rw [this, map_one, Units.val_one]

theorem sum_red_zero (M : ℕ → ℕ → E) {B : ℕ}
    (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (a b : ℕ → ℕ) (n : ℕ) (hab : ∀ i < n, a i < B ∧ b i < B ∧ a i ≠ b i) :
    IntAt P (∑ i ∈ Finset.range n, M (a i) (b i)) ∧ redP P (∑ i ∈ Finset.range n, M (a i) (b i)) = 0 := by
  have hI : ∀ i ∈ Finset.range n, IntAt P (M (a i) (b i)) := fun i hi => by
    have h := hab i (Finset.mem_range.1 hi)
    exact (hM _ _ h.1 h.2.1).1
  refine ⟨intAt_sum _ hI, ?_⟩
  rw [reduction_sum₂ _ hI]
  refine Finset.sum_eq_zero fun i hi => ?_
  have h := hab i (Finset.mem_range.1 hi)
  rw [(hM _ _ h.1 h.2.1).2, if_neg h.2.2]

theorem prod_blocks_eq_one (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E) {B r t j : ℕ}
    (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hrj : r + j * t ≤ B) :
    ∏ i ∈ Finset.range j, LocE.unitV (χ i) (Matrix.det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1))) = 1 := by
  refine Finset.prod_eq_one fun i hi => ?_
  have hij : i + 1 ≤ j := Finset.mem_range.1 hi
  have h2 : i * t + t ≤ j * t := by
    have := Nat.mul_le_mul_right t hij
    rwa [Nat.add_mul, one_mul] at this
  have hb : ∀ s : Fin t, r + i * t + s.1 < B := fun s => by
    have := s.2
    omega
  refine unitV_det_eq_one _ _ (fun s s' => (hM _ _ (hb s) (hb s')).1) ?_
  ext s s'
  rw [Matrix.map_apply, Matrix.of_apply, (hM _ _ (hb s) (hb s')).2, Matrix.one_apply]
  by_cases h : s = s'
  · rw [if_pos h, if_pos (by rw [h])]
  · rw [if_neg h, if_neg (fun h' => h (Fin.ext (by omega)))]

theorem lamGv_eq_one (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E)
    {B r t j : ℕ} (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hr : r ≤ B) (hrj : r + j * t ≤ B) : LocE.lamGv ψ₀ χ r t j M = 1 := by
  unfold LocE.lamGv
  rw [(sum_red_zero M hM (fun i => i) (fun i => i + 1) (r - 1) fun i hi => ⟨by omega, by omega, by omega⟩).2,
    AddChar.map_zero_eq_one, one_mul]
  exact prod_blocks_eq_one χ M hM hrj

theorem lamGvS_eq_one (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (M : ℕ → ℕ → E)
    {B k₀ r t j : ℕ} (hM : ∀ p p', p < B → p' < B → IntAt P (M p p') ∧ redP P (M p p') = if p = p' then 1 else 0)
    (hk : k₀ ≤ r) (hr : r ≤ B) (hrj : r + j * t ≤ B) : LocE.lamGvS ψ₀ χ k₀ r t j M = 1 := by
  unfold LocE.lamGvS
  have h1 := sum_red_zero M hM (fun i => i) (fun i => i + 1) (k₀ - 1) fun i hi => ⟨by omega, by omega, by omega⟩
  have h2 := sum_red_zero M hM (fun i => k₀ + i) (fun i => k₀ + i + 1) (r - k₀ - 1)
    fun i hi => ⟨by omega, by omega, by omega⟩
  rw [reduction_add h1.1 h2.1, h1.2, h2.2, add_zero, AddChar.map_zero_eq_one, one_mul]
  exact prod_blocks_eq_one χ M hM hrj

end Gen

section Ent

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem fIdx_lt {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) : LocE.fIdx k₀ c n p < n + c := by
  unfold LocE.fIdx
  split_ifs <;> omega

theorem fIdx_inj {k₀ c n p p' : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hp' : p' < n + c)
    (h : LocE.fIdx k₀ c n p = LocE.fIdx k₀ c n p') : p = p' := by
  unfold LocE.fIdx at h
  split_ifs at h <;> omega

theorem entB_one_add_q {k₀ n c : ℕ} (hk : k₀ ≤ n) (ex : ℕ → ℕ) (y : HomE E (n + c) (n + c))
    (hy : ∀ x ∈ LocE.lamY P (qOf P) n c ex, y x ∈ LocE.lamY P (qOf P) n c ex) {p p' : ℕ}
    (hp : p < n + c) (hp' : p' < n + c) :
    IntAt P (LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p') ∧
      redP P (LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p') =
        if p = p' then 1 else 0 := by
  have hQ0 : ((qOf P : ℕ) : E) ≠ 0 := qOf_ne_zero
  have hfl : LocE.fIdx k₀ c n p < n + c := fIdx_lt hk hp
  have hfl' : LocE.fIdx k₀ c n p' < n + c := fIdx_lt hk hp'
  have hb : IntAt P ((((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p))⁻¹ *
      (((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p') *
        y (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨_, hfl⟩)) := by
    have h1 := hy _ (GlobalTheory.CongLevel.bvec_mem P (qOf P) hQ0 (n + c) (LocE.scE n ex) (LocE.fIdx k₀ c n p'))
    have h2 := (GlobalTheory.CongLevel.mem_sclLat P (qOf P) (n + c) _ _).1 h1 ⟨_, hfl⟩
    rw [map_smul, Pi.smul_apply, smul_eq_mul] at h2
    exact h2
  have key : LocE.entB (qOf P) k₀ c n c n ex ex (LinearMap.id + ((qOf P : ℕ) : E) • y) p p' =
      (if p = p' then 1 else 0) + ((qOf P : ℕ) : E) * ((((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p))⁻¹ *
      (((qOf P : ℕ) : E) ^ LocE.scE n ex (LocE.fIdx k₀ c n p') *
        y (Loc.eN E (n + c) (LocE.fIdx k₀ c n p')) ⟨_, hfl⟩)) := by
    unfold LocE.entB Loc.atN
    rw [dite_eq_left hfl, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smul_apply, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul]
    by_cases hpp : p = p'
    · subst hpp
      have : Loc.eN E (n + c) (LocE.fIdx k₀ c n p) ⟨_, hfl⟩ = 1 := by simp [Loc.eN]
      rw [this, if_pos rfl, sub_self, zpow_zero, mul_one]
      have h0 := zpow_ne_zero (LocE.scE n ex (LocE.fIdx k₀ c n p)) hQ0
      field_simp
    · have hff : LocE.fIdx k₀ c n p ≠ LocE.fIdx k₀ c n p' := fun h => hpp (fIdx_inj hk hp hp' h)
      have : Loc.eN E (n + c) (LocE.fIdx k₀ c n p') ⟨_, hfl⟩ = 0 := by simp [Loc.eN, hff]
      rw [this, if_neg hpp, zero_add, zero_add, zpow_sub₀ hQ0]
      have h0 := zpow_ne_zero (LocE.scE n ex (LocE.fIdx k₀ c n p)) hQ0
      field_simp
  have hd : IntAt P (if p = p' then (1 : E) else 0) := by
    split_ifs
    · exact intAt_one
    · exact intAt_zero
  have hqb := (intAt_nat (P := P) (qOf P)).mul hb
  rw [key]
  refine ⟨hd.add hqb, ?_⟩
  rw [reduction_add hd hqb, reduction_mul (intAt_nat _) hb, reduction_absNorm_eq_zero, zero_mul, add_zero]
  split_ifs
  · exact reduction_one₂
  · exact reduction_zero

end Ent

theorem lamRow_one_add_q : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  intro X Pr R Ch S mu sharp j P hP y hy
  have hm := R.two_le_m
  have hk : R.k ≤ R.N j := by unfold Ranks.N; omega
  have hkr : R.k ≤ R.r := by unfold Ranks.r; omega
  have hNj : R.N j = R.k + j * R.t + j := by unfold Ranks.N; ring
  have hr : R.r ≤ R.N j + cOf R j := by
    rw [hNj]
    unfold Ranks.r cOf
    generalize j * R.t = u
    omega
  have hrj : R.r + j * R.t ≤ R.N j + cOf R j := by
    rw [hNj]
    unfold Ranks.r cOf
    generalize j * R.t = u
    omega
  have hy' : ∀ x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1),
      y x ∈ LocE.lamY P (qOf P) (R.N j) (cOf R j) (fun i => i + 1) := by
    intro x hx
    have h := hy x (by unfold lamYat; rw [if_pos hP]; exact hx)
    unfold lamYat at h
    rw [if_pos hP] at h
    exact h
  have hM := fun p p' (hp : p < R.N j + cOf R j) (hp' : p' < R.N j + cOf R j) =>
    entB_one_add_q (k₀ := R.k) hk (fun i => i + 1) y hy' hp hp'
  unfold lamRow
  rw [if_pos hP]
  cases sharp
  · simp only [Bool.false_eq_true, if_false]
    unfold LocE.lamGB
    exact lamGv_eq_one _ _ _ hM hr hrj
  · simp only [if_true]
    unfold LocE.lamGBS
    exact lamGvS_eq_one _ _ _ hM hkr hr hrj

end GlobalTheory.LamRowCong
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RowCharacterIdAddQSmulLatticePreservingEqOneStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rowCharacter_id_add_q_smul_latticePreserving_eq_one : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (sharp : Bool) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∈ Pr.vGs → ∀ y : HomE X.E (R.N j + cOf R j) (R.N j + cOf R j), (∀ x ∈ lamYat (Pr := Pr) (R := R) j P, y x ∈ lamYat (Pr := Pr) (R := R) j P) → lamRow Ch mu sharp j P (LinearMap.id + (qOf P : X.E) • y) = 1 := by
  first | exact @GlobalTheory.LamRowCong.lamRow_one_add_q | exact GlobalTheory.LamRowCong.lamRow_one_add_q | (intros; apply GlobalTheory.LamRowCong.lamRow_one_add_q <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldPointLiftsGenericFibre
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open Polynomial hiding funext
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem GlobalTheory.SatSupp.hasSupport_of_hasSatGL : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ), 1 ≤ n → ∀ (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (B : Multiset ℂˣ), GlobalTheory.LFun.HasSatGL w σ.ρ B → ∃ (ξ : Fin n → ((w.adicCompletion E)ˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (ϖ : (w.adicCompletion E)ˣ), HasSupport (IrrGL.of σ.ρ σ.smooth σ.irred).rep (chars ξ hξ) ∧ (∀ j (x : (w.adicCompletion E)ˣ), Valued.v (x : w.adicCompletion E) = 1 → ξ j x = 1) ∧ Valued.v (ϖ : w.adicCompletion E) = WithZero.exp (-1 : ℤ) ∧ B = Finset.univ.val.map fun j => ξ j ϖ := by
  intro E _ _ n _ w σ B hB
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_ringHom (algebraMap E (w.adicCompletion E)).injective
  obtain ⟨α, hαB, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  have hϖ : Valued.v ((GroundTheory.Global.uniformizerUnit w : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
      WithZero.exp (-1 : ℤ) := by
    simpa using GroundTheory.Global.valued_uniformizerUnit_zpow w 1
  refine ⟨fun j => GlobalTheory.SmGL.unrChar _ (α j),
    fun j => GlobalTheory.SmGL.isSmoothChar_of_isUnram (GlobalTheory.SmGL.isUnram_unrChar _ (α j)),
    GroundTheory.Global.uniformizerUnit w, ?_, ?_, hϖ, ?_⟩
  · let π : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion E)) := ⟨σ.V, σ.ρ, σ.smooth, σ.irred⟩
    exact (GlobalTheory.LocLanglands.hasSupport_of_isSubquotient_prinSeries _ n _ _ π hα.2.2).of_equiv
      (IrrGL.equivOf σ.ρ σ.smooth σ.irred)
  · intro j x hx
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hx]
    simp
  · rw [← hαB]
    congr 1
    funext j
    rw [GlobalTheory.SmGL.unrChar_apply, GlobalTheory.SmGL.SphCompletion.ord_completion, hϖ]
    simp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsOverVUnder
noncomputable section

namespace GlobalTheory.TwU

open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG _root_.Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat
open Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section MidDatum

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
  (A : AdData t u μ St) (a : 𝓞 D.host.E)

def mvN (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) : Submodule (𝓞 t.X.E) (Sp t.X.E (D.R.N i)) :=
  Submodule.span (𝓞 t.X.E) ((fun (y : Fin (D.R.N i) → D.host.E) (l : Fin (D.R.N i)) => t.seam.iE.symm (y l)) ''
    (latCo D.sp (gramN D i hi) (A.crd i hi) a x.1 ((St i hi).K β).lev.Lb : Set (Fin (D.R.N i) → D.host.E)))

def vUnder (P : HeightOneSpectrum (𝓞 t.X.E)) : HeightOneSpectrum (𝓞 D.host.F) :=
  HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P)

theorem isOver_vUnder (P : HeightOneSpectrum (𝓞 t.X.E)) : IsOver (vUnder (t := t) P) (seamP t.seam P) := by
  unfold IsOver vUnder
  rw [HeightOneSpectrum.under_asIdeal]

def vecAt {n : ℕ} (g : GL (Fin n) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : Sp t.X.E n) : Fin n → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F :=
  fun l => prV (E := D.host.E) v (pullV (F := D.host.F) g (fun b => t.seam.iE (w b)) l)

def iotaSel (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (P : t.Pr.vT (t.word u)) (v : HeightOneSpectrum (𝓞 D.host.F))
    (h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal := by
  classical
  exact if hι : ∃ ι : ((St i hi).K β).lev.fM v h →+ 𝓞 t.X.E ⧸ P.1.asIdeal,
      ∀ c, (St i hi).chOf c = β → FunMoved t.seam ((St i hi).K β).lev P v h ι (A.mov i hi c) (A.pt i hi c).deco.1
    then hι.choose else 0

def InDom (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N i)) : Prop :=
  vecAt (t := t) (ratA D.host.F (A.crd i hi) * x.1) (vUnder (t := t) P.1) w ∈
    latS (F := D.host.F) ((vUnder (t := t) P.1).adicCompletion D.host.F) (intV D.host.E (vUnder (t := t) P.1))
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) ((St i hi).K β).lev.Lb))

def mvG (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch)
    (x : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N i)) :
    𝓞 t.X.E ⧸ P.1.asIdeal := by
  classical
  exact if h : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ (vUnder (t := t) P.1).asIdeal then
    (if hz : InDom A i hi β x P w then
      iotaSel A i hi β P (vUnder (t := t) P.1) h (((St i hi).K β).lev.fT (vUnder (t := t) P.1) h ⟨_, hz⟩) else 0)
    else 0

end MidDatum

end GlobalTheory.TwU

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOne
section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOne
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open Polynomial hiding funext
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

open Matrix GlobalTheory.IsoPull

namespace GlobalTheory.DegOneChar

section Char

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']

theorem detChar_map (i : k ≃+* k') (χ : kˣ →* ℂˣ) (g : GL (Fin 1) k') :
    detChar (Fin 1) χ (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g) =
      detChar (Fin 1) (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) g := by
  simp only [detChar_apply, MonoidHom.comp_apply]
  congr 1
  ext
  simp [RingHom.map_det]

theorem trGL_ofChar (i : k ≃+* k') (hi' : Continuous i.symm) (χ : kˣ →* ℂˣ) (hχ : IsSmoothChar χ)
    (h' : IsSmoothChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom))) :
    GlobalTheory.SuppIne.trGL i hi' (IrrGL.ofChar χ hχ) = IrrGL.ofChar (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) h' := by
  unfold GlobalTheory.SuppIne.trGL
  change _ = IrrGL.of (IrrRep.det (Fin 1) _ h').ρ (IrrRep.det (Fin 1) _ h').smooth (IrrRep.det (Fin 1) _ h').irr
  refine IrrGL.of_eq_of.2 ⟨?_⟩
  let E := (equivRep (IrrRep.det (Fin 1) χ hχ)).symm
  refine GlobalTheory.LocGL.equivOfBijective ⟨E.toLinearEquiv.toLinearMap, fun g => LinearMap.ext fun x => ?_⟩ E.toLinearEquiv.bijective
  have h1 := LinearMap.congr_fun (E.isIntertwining' (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g)) x
  change E.toLinearEquiv ((IrrRep.det (Fin 1) χ hχ).cl.rep.ρ _ x) = _
  refine h1.trans ?_
  change ((detChar (Fin 1) χ (GeneralLinearGroup.map (n := Fin 1) i.symm.toRingHom g) : ℂˣ) : ℂ) • E.toLinearEquiv x =
    ((detChar (Fin 1) (χ.comp (Units.map i.symm.toRingHom.toMonoidHom)) (g : GL (Fin 1) k') : ℂˣ) : ℂ) • E.toLinearEquiv x
  exact congrArg (fun z : ℂˣ => (z : ℂ) • E.toLinearEquiv x) (detChar_map i χ g)

end Char

section Norm

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]

theorem adicCompletionMap_eq (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) (z : v.adicCompletion K) :
    GroundTheory.Global.adicCompletionMap v u z = cLoc hO z :=
  congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := K) v).equalizer
    (GroundTheory.Global.continuous_adicCompletionMap v u) (continuous_cLoc hO)
    (funext fun x => (GroundTheory.Global.adicCompletionMap_algebraMap v u x).trans
      (by rw [Function.comp_apply, cLoc_algebraMap hO x, he]))) z

theorem normU_apply (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) (y : (u.adicCompletion M)ˣ) :
    ((GlobalTheory.BCChar.normU v u y : (v.adicCompletion K)ˣ) : v.adicCompletion K) = (locEquiv hO).symm y := by
  letI : Algebra (v.adicCompletion K) (u.adicCompletion M) := (GroundTheory.Global.adicCompletionMap v u).toAlgebra
  have hf : ∀ z, algebraMap (v.adicCompletion K) (u.adicCompletion M) z = locEquiv hO z :=
    adicCompletionMap_eq e he hO
  have hb : Function.Bijective (algebraMap (v.adicCompletion K) (u.adicCompletion M)) := by
    have : ⇑(algebraMap (v.adicCompletion K) (u.adicCompletion M)) = locEquiv hO := funext hf
    rw [this]
    exact (locEquiv hO).bijective
  have h1 : Module.finrank (v.adicCompletion K) (u.adicCompletion M) = 1 :=
    Algebra.finrank_eq_one_iff_bijective_algebraMap.2 hb
  obtain ⟨z, hz⟩ := hb.2 (y : u.adicCompletion M)
  change Algebra.norm (v.adicCompletion K) (y : u.adicCompletion M) = _
  rw [← hz, Algebra.norm_algebraMap, h1, pow_one, hf, RingEquiv.symm_apply_apply]

theorem normU_eq (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) {v : HeightOneSpectrum (𝓞 K)}
    {u : HeightOneSpectrum (𝓞 M)} [u.asIdeal.LiesOver v.asIdeal] (hO : Over e v u) :
    GlobalTheory.BCChar.normU v u = Units.map (locEquiv hO).symm.toRingHom.toMonoidHom :=
  MonoidHom.ext fun y => Units.ext (normU_apply e he hO y)

theorem over_of_liesOver (e : K ≃+* M) (he : ∀ x, e x = algebraMap K M x) (v : HeightOneSpectrum (𝓞 K))
    (u : HeightOneSpectrum (𝓞 M)) [h : u.asIdeal.LiesOver v.asIdeal] : Over e v u := fun x => by
  have hx : RingOfIntegers.mapRingEquiv e x = algebraMap (𝓞 K) (𝓞 M) x := RingOfIntegers.ext (he x)
  rw [hx, h.over, Ideal.under_def, Ideal.mem_comap]

end Norm

section Lift

theorem ofChar_congr {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {χ ψ : kˣ →* ℂˣ} (h : χ = ψ) (hχ : IsSmoothChar χ) (hψ : IsSmoothChar ψ) : IrrGL.ofChar χ hχ = IrrGL.ofChar ψ hψ := by
  subst h
  rfl

variable {K M : Type} [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M]
  [Algebra K M]

theorem charLift_of_isLift (h1 : Module.finrank K M = 1) {a : ℕ} {π : CuspSub K a} {P : CuspSub M a}
    (hP : IsLift π P) : CharLift π P := by
  refine ⟨hP, fun v u _ τ T hτ hT ξ hξ hs => ?_⟩
  let e : K ≃+* M := RingEquiv.ofBijective (algebraMap K M) (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1)
  have he : ∀ x, e x = algebraMap K M x := fun _ => rfl
  have hO : Over e v u := over_of_liesOver e he v u
  let i := locEquiv hO
  have hi : Continuous i := continuous_cLoc hO
  have hi' : Continuous i.symm := continuous_cLoc hO.symm
  obtain ⟨E, hE⟩ := hP.loc v u i hi (fun x => cLoc_algebraMap hO x) τ T hτ hT
  have hg : ∀ g : GL (Fin a) (u.adicCompletion M),
      GeneralLinearGroup.map i.toRingHom (GeneralLinearGroup.map i.symm.toRingHom g) = g := fun g =>
    Units.ext (Matrix.ext fun _ _ => i.apply_symm_apply _)
  let φ : Representation.Equiv (τ.ρ.comp (GeneralLinearGroup.map (n := Fin a) i.symm.toRingHom)) T.ρ :=
    GlobalTheory.LocGL.equivOfBijective ⟨E.toLinearMap, fun g => LinearMap.ext fun x => by
      rw [LinearMap.comp_apply, LinearMap.comp_apply]
      change E (τ.ρ (GeneralLinearGroup.map i.symm.toRingHom g) x) = T.ρ g (E x)
      rw [hE, hg]⟩ E.bijective
  have hs2 := (GlobalTheory.SuppIne.hasSupport_comp i hi hi' hs).of_equiv φ
  have hN := normU_eq e he hO
  have hc : (chars ξ hξ).map (GlobalTheory.SuppIne.trGL i hi') =
      chars (fun j => (ξ j).comp (GlobalTheory.BCChar.normU v u)) fun j => GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j) := by
    unfold chars
    rw [Multiset.map_map]
    refine Multiset.map_congr rfl fun j _ => ?_
    have hj : IsSmoothChar ((ξ j).comp (Units.map i.symm.toRingHom.toMonoidHom)) := by
      have := GlobalTheory.BCChar.isSmoothChar_comp_normU v u (hξ j)
      rwa [hN] at this
    rw [Function.comp_apply, trGL_ofChar i hi' (ξ j) (hξ j) hj]
    exact ofChar_congr (by rw [hN]) _ _
  rw [← hc]
  exact hs2

end Lift

theorem exists_charLift : ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a, ∃ P : CuspSub M a, CharLift π P := by
  intro K M _ _ _ _ _ _ _ h1 a _ π
  obtain ⟨P, hP⟩ := GlobalTheory.DegOneLift.isLift K M h1 a π
  exact ⟨P, charLift_of_isLift h1 hP⟩

end GlobalTheory.DegOneChar
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCharacterSupportBaseChangeLiftDegreeOneStatement
open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open Neutral.B1 hiding G Dec IsPlaceOver
open Polynomial hiding funext
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_characterSupportBaseChangeLift_degreeOne : ∀ (K M : Type) [Field K] [NumberField K] [_root_.NumberField.IsTotallyComplex K] [Field M] [NumberField M] [_root_.NumberField.IsTotallyComplex M] [Algebra K M], Module.finrank K M = 1 → ∀ (a : ℕ), 1 ≤ a → ∀ π : CuspSub K a, ∃ P : CuspSub M a, CharLift π P := by
  first | (exact @GlobalTheory.DegOneChar.exists_charLift) | (exact GlobalTheory.DegOneChar.exists_charLift) | (intros; apply GlobalTheory.DegOneChar.exists_charLift  <;> assumption)
end
end
