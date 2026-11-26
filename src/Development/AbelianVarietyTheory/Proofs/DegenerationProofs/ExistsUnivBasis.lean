module

public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SpanEqTopOfFunctionals
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsRosatiGen
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBimultiplicativeOfSecondQuotConst
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMulIsIntegralChart
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIsoMorphismRestrictOfLocalDominantSections
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.OverPointsExtOfInjective
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.WeilIsGrpPullbackIff

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnivBasis
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
noncomputable section
namespace GlobalTheory.ThetaReal

def UnivBasis {S : Scheme.{0}} (P : PolAV S) (n : ℤ) {T₀ : Over S} {κ : Type} (b : κ → SecM P.A P.L n T₀) : Prop :=
  ∀ (T : Over S) [IsAffine T.left] (h : T ⟶ T₀), ∃ c : Module.Basis κ Γ(T.left, ⊤) (SecM P.A P.L n T),
    ∀ i, c i = VVRank.pullM P.A P.L n h (b i)

theorem exists_univBasis (h : SecBaseChangeAnySt) {S : Scheme.{0}} (P : PolAV S) (n : ℕ) (hn : 1 ≤ n) (p : S) :
    ∃ V : S.Opens, p ∈ V ∧ ∃ b : Fin (n ^ P.g) → SecM P.A P.L n (overRes (T := baseOver S) V), UnivBasis P n b := by
  obtain ⟨V, hV, b, hb⟩ := h S P n hn p
  exact ⟨V, hV, fun i => SecM.ofSec P.A (b i), fun T _ h => VVRank.exists_basis P n b hb T h⟩

end GlobalTheory.ThetaReal
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.TestBasis

open FreeNear

theorem exists_eStd_eq_linear (g n : ℕ) (f : (Fin g ⊕ Fin g → ZMod n) →ₗ[ZMod n] ZMod n) :
    ∃ b, ∀ y, eStd g n b y = f y := by
  refine ⟨Sum.elim (fun i => f (Pi.single (.inr i) 1)) (fun i => -f (Pi.single (.inl i) 1)),
    fun y => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [← Finset.univ_sum_single y, map_sum, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, f (Pi.single j (y j)) = y j * f (Pi.single j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h, h]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem perp_perp (H : AddSubgroup S.Gam) : S.perp (S.perp H) = H := by
  refine le_antisymm (fun x hx => ?_) fun x hx y hy => ?_
  · by_contra hxH
    let H' : Submodule (ZMod (S.r * S.N)) S.Gam := AddSubgroup.toZModSubmodule _ H
    obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := S.r * S.N) (q := H'.mkQ x)
      (fun h0 => hxH ((Submodule.Quotient.mk_eq_zero H').mp h0))
    obtain ⟨b, hb⟩ := exists_eStd_eq_linear _ _ (f ∘ₗ H'.mkQ)
    have hb' : b ∈ S.perp H := fun y hy => by
      rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply,
        (Submodule.Quotient.mk_eq_zero H').mpr hy, map_zero]
    have h1 : eStd S.g _ x b = 0 := hx b hb'
    rw [Weights.eStd_swap, neg_eq_zero, hb] at h1
    exact hf h1
  · rw [Weights.eStd_swap, hy x hx, neg_zero]

variable {S} {p : ℕ} [Fact p.Prime] {y₀ : S.R →+* PadicAlgCl p} (τ : S.Test p y₀)

theorem exists_nsmul_of_wt_eq_zero [ArithBase o Ω] (α : τ.X) (h : τ.wt α = 0) : ∃ v, α = S.N • v := by
  choose w hw using fun x => QuotientAddGroup.mk_surjective (τ.yy x)
  have h1 := ((test_weights o Ω S p y₀ τ).2 _ τ.isoFree le_rfl w (fun x => (hw x).symm) τ.yy.ker
    (by rw [perp_perp, AddSubgroup.closure_eq]) α).1 (fun t h₂ _ => by rw [h]; rfl)
  have h2 : AddSubgroup.closure (w '' τ.yy.ker ∪ Set.range fun v₀ : τ.X => S.N • v₀) ≤
      (nsmulAddMonoidHom S.N : τ.X →+ τ.X).range := by
    rw [AddSubgroup.closure_le]
    rintro _ (⟨x, hx, rfl⟩ | ⟨v, rfl⟩)
    · have h3 := hw x
      rw [AddMonoidHom.mem_ker.1 hx, QuotientAddGroup.eq_zero_iff] at h3
      obtain ⟨u, hu⟩ := h3
      exact ⟨S.r • u, by rw [← hu]; exact (mul_nsmul u S.r S.N).symm⟩
    · exact ⟨v, rfl⟩
  obtain ⟨v, hv⟩ := h2 h1
  exact ⟨v, hv.symm⟩

theorem q_le_of_wt_eq [ArithBase o Ω] {α β : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀))
    (h : τ.wt β = τ.wt α) : τ.q α ≤ τ.q β := by
  obtain ⟨v, hv⟩ := exists_nsmul_of_wt_eq_zero τ (β - α) (by rw [map_sub, h, sub_self])
  have := hα v
  rwa [← hv, add_sub_cancel] at this

theorem exists_norm_eq_exp {α : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) :
    ∃ l : PadicAlgCl p, ‖l‖ = Real.exp (τ.q α / S.N) := by
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  obtain ⟨x, hx⟩ := τ.δ_max.1
  refine ⟨y₀ ⟨S.th x, S.th_mem x⟩ / y₀ ⟨_, hk⟩, ?_⟩
  have hx' : ‖y₀ ⟨S.th x, S.th_mem x⟩‖ = τ.δ := hx
  rw [norm_div, hx', h, Real.exp_neg]
  have := τ.δ_pos.ne'
  have := (Real.exp_pos (τ.q α / S.N)).ne'
  field_simp

theorem exists_proj_ne_zero {α : τ.X} (hα : ∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) :
    ∃ j i, y₀ (algebraMap o S.R (S.proj _ (τ.wt α) j i)) ≠ 0 := by
  by_contra! h0
  obtain ⟨k, hk, h⟩ := τ.eq α hα
  have := Fintype.ofFinite (S.perp τ.yy.ker)
  have h1 : (⟨_, hk⟩ : S.R) = ∑ t : S.perp τ.yy.ker, algebraMap o S.R (S.ζ ^ (k.2 t).val) *
      ∑ j, algebraMap o S.R (S.proj _ (τ.wt α) j k.1) * ⟨S.ev t j, S.ev_mem t j⟩ := by
    apply Subtype.ext
    simp only [ThetaSys.FF, finsum_eq_sum_of_fintype, AddSubmonoidClass.coe_finsetSum, MulMemClass.coe_mul]
    rfl
  rw [h1] at h
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_mul, h0, zero_mul, Finset.sum_const_zero, mul_zero, norm_zero] at h
  exact (mul_pos τ.δ_pos (Real.exp_pos _)).ne h

end GlobalTheory.ZH.TestBasis

namespace GlobalTheory.ZH


open FreeNear TestBasis in
theorem exists_adapted_basis_testLattice : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∃ (B : Matrix S.J S.J (PadicAlgCl p)) (l : S.J → PadicAlgCl p) (α : S.J → τ.X), (∀ i j, ‖B i j‖ ≤ 1) ∧ ‖B.det‖ = 1 ∧ (∀ i v₀, τ.q (α i) ≤ τ.q (α i + S.N • v₀)) ∧ (∀ i, ‖l i‖ = Real.exp (τ.q (α i) / S.N)) ∧ (∀ c, ∃ i, τ.wt (α i) = c) ∧ (∀ i, ((S.proj _ (τ.wt (α i))).map fun a => y₀ (algebraMap o S.R a)).mulVec (B i) = B i) ∧ τ.E = Submodule.span (OO p) (Set.range fun i j => l i * B i j) := by
  intro o Ω _ _ _ hA S p _ y₀ τ hint
  have : IsDomain o := hA.inj.isDomain
  have := finite_char S (S.perp τ.yy.ker)
  have := Fintype.ofFinite (S.perp τ.yy.ker →+ ZMod S.N)
  obtain ⟨hmul, hsum⟩ := proj_orthogonal S _ τ.isoFree
  let φ : o →+* OO p := (y₀.comp (algebraMap o S.R)).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hint a)
  obtain ⟨κ, col, hdet, hspan⟩ := exists_basis_adapted_to_idempotents (OO p) S.J
    (S.perp τ.yy.ker →+ ZMod S.N) (fun c => φ.mapMatrix (S.proj _ c))
    (fun c c' => by
      rw [← map_mul, hmul]
      split_ifs <;> simp)
    (by rw [← map_sum, hsum, map_one])
  choose a ha hwa using (test_weights o Ω S p y₀ τ).1
  choose f hf using fun c => exists_norm_eq_exp τ (ha c)
  refine ⟨Matrix.of fun i j => y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i))), fun i => f (κ i),
    fun i => a (κ i), fun i j => hint _, ?_, fun i => ha _, fun i => hf _, fun c => ?_, fun i => ?_, ?_⟩
  · have h1 : (((Matrix.of fun i j => φ.mapMatrix (S.proj _ (κ i)) j (col i)).det : OO p) : PadicAlgCl p) =
        (Matrix.of fun i j => y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i)))).det :=
      RingHom.map_det (OO p).subtype _
    rw [← h1]
    exact le_antisymm ((mem_OO_iff _).1 (Subtype.prop _))
      (not_lt.1 fun h => (not_isUnit_OO_iff _).2 h hdet)
  · by_contra! h
    obtain ⟨j, i, hji⟩ := exists_proj_ne_zero τ (ha c)
    rw [hwa] at hji
    have h1 := (hspan c).le (Submodule.subset_span ⟨i, rfl⟩)
    have h2 : {v : S.J → OO p | ∃ i, κ i = c ∧ v = fun j => φ.mapMatrix (S.proj _ c) j (col i)} = ∅ :=
      Set.eq_empty_of_forall_notMem fun _ ⟨i, hi, _⟩ => h i ((hwa _).trans hi)
    rw [h2, Submodule.span_empty, Submodule.mem_bot] at h1
    exact hji (congrArg Subtype.val (congrFun h1 j))
  · rw [hwa]
    funext j
    have h1 := congrArg (fun a => y₀ (algebraMap o S.R a)) (congrFun (congrFun (hmul (κ i) (κ i)) j) (col i))
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [if_true, Matrix.mul_apply, map_sum, map_mul] at h1
    exact h1
  · refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
    · rintro _ ⟨α, l, i, hα, hl, rfl⟩
      generalize hc : τ.wt α = c
      have h1 : ∀ w ∈ Submodule.span (OO p) {v : S.J → OO p | ∃ i, κ i = c ∧
          v = fun j => φ.mapMatrix (S.proj _ c) j (col i)},
          (fun j => f c * (w j : PadicAlgCl p)) ∈ Submodule.span (OO p) (Set.range fun i j =>
            f (κ i) * y₀ (algebraMap o S.R (S.proj _ (κ i) j (col i)))) := by
        intro w hw
        induction hw using Submodule.span_induction with
        | mem _ h' =>
          obtain ⟨i', rfl, rfl⟩ := h'
          exact Submodule.subset_span ⟨i', rfl⟩
        | zero =>
          have : (fun j => f c * (((0 : S.J → OO p) j : OO p) : PadicAlgCl p)) = 0 := funext fun j => by simp
          rw [this]
          exact Submodule.zero_mem _
        | add a a' _ _ ha ha' =>
          convert Submodule.add_mem _ ha ha' using 1
          funext j
          simp [mul_add]
        | smul s a _ ha =>
          convert Submodule.smul_mem _ s ha using 1
          funext j
          change f c * ((s : PadicAlgCl p) * a j) = (s : PadicAlgCl p) * (f c * a j)
          ring
      have h2 := h1 _ ((hspan c).le (Submodule.subset_span ⟨i, rfl⟩))
      have hpos : 0 < ‖f c‖ := hf c ▸ Real.exp_pos _
      have h0 : f c ≠ 0 := norm_pos_iff.1 hpos
      have hq : l / f c ∈ OO p := by
        rw [mem_OO_iff, norm_div, div_le_one hpos, hf]
        refine hl.trans (Real.exp_le_exp.2 (div_le_div_of_nonneg_right ?_ (Nat.cast_nonneg _)))
        exact q_le_of_wt_eq τ hα ((hwa c).trans hc.symm)
      have h3 : (fun j => l * y₀ (algebraMap o S.R (S.proj _ c j i))) =
          (⟨_, hq⟩ : OO p) • fun j => f c * y₀ (algebraMap o S.R (S.proj _ c j i)) := by
        funext j
        change _ = l / f c * (f c * y₀ (algebraMap o S.R (S.proj _ c j i)))
        rw [← _root_.mul_assoc, div_mul_cancel₀ _ h0]
      rw [h3]
      exact Submodule.smul_mem _ _ h2
    · rintro _ ⟨i, rfl⟩
      exact ⟨a (κ i), f (κ i), col i, ha _, (hf _).le, by rw [hwa]; rfl⟩

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsionImports
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {p : ℕ} [Fact p.Prime]
  {y₀ : S.R →+* PadicAlgCl p}

def Extends (u : ρ.UTest p y₀) (a : S.Gam) (h : baseOver (Sp u.V) ⟶ u.G) : Prop :=
  ∃ x : Sp (FractionRing u.V) ⟶ pullback u.G.hom (jK u.V), x ≫ pullback.fst _ _ = jK u.V ≫ h.left ∧
    x ≫ pullback.snd _ _ = 𝟙 _ ∧ x ≫ u.U.gen.hom.left ≫ u.φ = spMap u.yK ≫ (ρ.pt a).left

theorem integral_iff (u : ρ.UTest p y₀) (a : S.Gam) : u.Integral a ↔ ∃ h, Extends u a h :=
  ⟨fun ⟨h, x, e, H⟩ => ⟨Over.homMk h e, x, H⟩, fun ⟨h, x, H⟩ => ⟨h.left, x, Over.w h, H⟩⟩

end GlobalTheory.UnitTheta
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreeOrthogonalSupportAndSupISpecializes
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

namespace ThetaSys

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω)

theorem supI_subset_of_specializes {ξ z : M.Z} (h : ξ ⤳ z) : S.supI M z ⊆ S.supI M ξ :=
  fun _ hx => ⟨hx.1, fun j => M.O_le_of_specializes h (hx.2 j)⟩

theorem exists_isClosed_supI_eq [JacobsonSpace M.Z] (ξ : M.Z) (W : M.Z.Opens) (hξ : ξ ∈ W) :
    ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have hV : IsOpen ((W : Set M.Z) ∩ ⋂ a ∈ S.supI M ξ, {z | M.Div S.th a z}) :=
    W.isOpen.inter ((Set.toFinite _).isOpen_biInter fun a _ => M.isOpen_setOf_div _ _)
  obtain ⟨x, ⟨⟨hxW, hxI⟩, hxc⟩, hx⟩ := nonempty_inter_closedPoints
    (Z := ((W : Set M.Z) ∩ ⋂ a ∈ S.supI M ξ, {z | M.Div S.th a z}) ∩ closure {ξ})
    ⟨ξ, ⟨hξ, Set.mem_iInter₂.mpr fun _ ha => ha⟩, subset_closure rfl⟩
    (hV.isLocallyClosed.inter isClosed_closure.isLocallyClosed)
  have hs : ξ ⤳ x := specializes_iff_mem_closure.mpr hxc
  exact ⟨x, hxW, hx, hs, (S.supI_subset_of_specializes M hs).antisymm
    fun a ha => Set.mem_iInter₂.mp hxI a ha⟩

theorem Over₀.supI_eq {S : ThetaSys o Ω} {M : RatModel o Ω} {U₀ : M.Z.Opens} (h : S.Over₀ M U₀)
    {ξ : M.Z} (hξ : ξ ∈ U₀) : S.supI M ξ = {x | S.th x ≠ 0} := by
  ext x
  refine ⟨fun hx => hx.1, fun hx => ⟨hx, fun j => ?_⟩⟩
  have h1 : S.th j / S.th x ∈ M.ringOn U₀ := by
    rw [div_eq_mul_inv]
    exact mul_mem (h.le (S.th_mem j)) (h.th_unit x hx)
  exact (Algebra.mem_iInf.mp (Algebra.mem_iInf.mp h1 ξ) hξ :)

end ThetaSys

theorem isoFree_TT_and_supI_specializes :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens), S.Over₀ M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) := by
  intro o Ω _ _ _ _ S M U₀ hO ⟨hL, hJ⟩ hT hS
  have hpp := (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.1
  refine ⟨fun ξ => ⟨?_, hpp _⟩, fun ξ z h => S.supI_subset_of_specializes M h, fun ξ hξ => ?_,
    fun ξ W hξ => S.exists_isClosed_supI_eq M ξ W hξ⟩
  · obtain ⟨x, -, hx, -, he⟩ := S.exists_isClosed_supI_eq M ξ ⊤ trivial
    obtain ⟨p, hp, y, hy⟩ := (hL U₀ le_rfl hO.ne x hx).1
    obtain ⟨y₀, hy₀, -, ⟨τ⟩⟩ := hT x p y hy
    have h1 : S.HH M ξ = τ.yy.ker := by
      rw [← (hS x p y y₀ τ hy hy₀).2, ThetaSys.HH, ThetaSys.HH, he]
    rw [ThetaSys.TT, h1]
    exact τ.isoFree
  · have h1 : S.perp ⊥ = ⊤ := by
      refine top_unique fun a _ h hh => ?_
      rw [AddSubgroup.mem_bot.mp hh]
      simp [eStd]
    rw [ThetaSys.TT, ThetaSys.HH, hO.supI_eq hξ, S.supp, ← h1, hpp]

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormLtOneOfIrreducible
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.ZH.PsiForm

open ReciprocityTheory.ChartRestriction.G.DVR

variable {V : Type} [CommRing V] [IsDomain V]

theorem hasVal_valF {ϖ : V} [IsDiscreteValuationRing V] {X : Scheme.{0}} (L : LB X)
    (x : Spec (CommRingCat.of V) ⟶ X) (x' : Spec (CommRingCat.of (FractionRing V)) ⟶ X) (hx : x' = jK V ≫ x)
    (ε : ℤ) (t : LB.Gen (LB.LinComb L (K := PUnit) (fun _ => x') (fun _ => ε))) {n : ℤ}
    (hn : GenHasVal ϖ L (fun _ => x) (fun _ => x') (fun _ => hx) (fun _ => ε) t n)
    (j : PUnit → L.ι) (hj : ⊤ ≤ x ⁻¹ᵁ L.U (j PUnit.unit)) :
    HasVal ϖ (valF (𝟙 (Sp (FractionRing V))) _ (t.s j).val) n := by
  subst hx
  have htop : LB.wchart L (fun _ : PUnit => x) j = ⊤ :=
    eq_top_iff.2 fun y hy => Set.mem_iInter.2 fun _ => hj hy
  have hK : (⊤ : (Spec (CommRingCat.of (FractionRing V))).Opens) ≤ LB.wchart L (fun _ : PUnit => jK V ≫ x) j :=
    fun y _ => by
      have hy : (jK V).base y ∈ LB.wchart L (fun _ : PUnit => x) j := by rw [htop]; trivial
      exact Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  obtain ⟨c, hc, eV, hce⟩ := genHasVal_top L (fun _ : PUnit => x) (fun _ => ε) t hn j htop hK
  have e : valF (𝟙 (Sp (FractionRing V))) _ (t.s j).val = c * algebraMap V (FractionRing V) (eV : V) := by
    rw [← hce]
    exact (dif_pos hK).trans rfl
  rw [e]
  exact hasVal_mul_unit hc eV

variable {F : Type} [NormedField F] [Algebra (FractionRing V) F]
  (hle : ∀ x : FractionRing V, ‖algebraMap _ F x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V)))

omit [IsDomain V] in
include hle in
theorem norm_unit (w : Vˣ) : ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w : V))‖ = 1 := by
  have h1 := (hle _).2 ⟨(w : V), rfl⟩
  have h2 := (hle _).2 ⟨((w⁻¹ : Vˣ) : V), rfl⟩
  have h3 : ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) (w : V))‖ *
      ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V))‖ = 1 := by
    rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
  refine le_antisymm h1 ?_
  calc (1 : ℝ) = _ := h3.symm
    _ ≤ _ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
    _ = _ := mul_one _

theorem norm_pos_of_irreducible {ϖ : V} (hϖ : Irreducible ϖ) :
    0 < ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ :=
  norm_pos_iff.2 ((map_ne_zero _).2 ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero))

include hle in
theorem norm_lt_one_of_irreducible {ϖ : V} (hϖ : Irreducible ϖ) :
    ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ < 1 := by
  by_contra h
  have h0 : algebraMap V (FractionRing V) ϖ ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).2 hϖ.ne_zero
  obtain ⟨w, hw⟩ := (hle (algebraMap V (FractionRing V) ϖ)⁻¹).1 (by
    rw [map_inv₀, norm_inv]
    exact inv_le_one_of_one_le₀ (not_lt.1 h))
  refine hϖ.not_isUnit (IsUnit.of_mul_eq_one w (IsFractionRing.injective V (FractionRing V) ?_))
  rw [map_mul, hw, mul_inv_cancel₀ h0, map_one]

include hle in
theorem norm_of_hasVal {ϖ : V} (hϖ : Irreducible ϖ) {c : FractionRing V} {n : ℤ} (hc : HasVal ϖ c n) :
    ‖algebraMap (FractionRing V) F c‖ =
      Real.exp (-(-Real.log ‖algebraMap (FractionRing V) F (algebraMap V (FractionRing V) ϖ)‖ * n)) := by
  obtain ⟨w, rfl⟩ := hc
  rw [map_mul, norm_mul, norm_unit hle, _root_.mul_one, map_zpow₀, norm_zpow, neg_mul, neg_neg,
    ← Real.rpow_def_of_pos (norm_pos_of_irreducible hϖ), Real.rpow_intCast]

theorem tendsto_val [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) :
    Filter.Tendsto Q Filter.cofinite Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b => Filter.eventually_cofinite.2 ((D.psi_tendsto b.toNat).subset fun χ hχ hin => hχ ?_)
  exact (Int.self_le_toNat b).trans (genHasVal_ge_of_in hϖ D.toPre.P.L D.toPre.P.isLB (D.toPre.c χ).left (D.toPre.xK χ)
    (QForm.ptK_eq D.toPre χ) (-1) (D.toPre.psi χ) b.toNat hin (hQ χ))

theorem exists_quadraticMap [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ)
    (D : DegData V (IsLocalRing.maximalIdeal V)) {Q : D.toPre.X → ℤ} (hQ : QForm.IsQ D.toPre ϖ Q) (a : ℝ) :
    ∃ q : QuadraticMap ℤ D.toPre.X ℝ, ∀ χ, q χ = a * Q χ := by
  have h0 := QForm.Q_zero hϖ D hQ
  have hd : HasConstSecondDiff fun χ => a * (Q χ : ℝ) := by
    refine (hasConstSecondDiff_iff _).2 fun b m ν => ?_
    have h := QForm.bOf_add_left hϖ D hQ b m ν
    simp only [QForm.bOf] at h
    have h' : Q (b + m + ν) - Q (b + m) - Q (b + ν) + Q b = Q (m + ν) - Q m - Q ν + Q 0 := by rw [h0]; linarith
    have h'' := congrArg (fun z : ℤ => a * (z : ℝ)) h'
    push_cast at h''
    linarith
  refine ⟨hd.quadraticMap fun χ => by rw [QForm.Q_neg hϖ D hQ], fun χ => ?_⟩
  change a * (Q χ : ℝ) - a * (Q 0 : ℝ) = a * (Q χ : ℝ)
  simp [h0]

theorem main : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀), ∃ q : QuadraticMap ℤ u.D.toPre.X ℝ, Filter.Tendsto q Filter.cofinite Filter.atTop ∧ ∀ χ, u.PsiNorm χ (Real.exp (-q χ)) := by
  intro o Ω _ _ _ _ S ρ p _ y₀ u
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible u.V
  choose Q hQ using QForm.exists_QVal hϖ u.D
  obtain ⟨q, hq⟩ := exists_quadraticMap hϖ u.D hQ
    (-Real.log ‖algebraMap (FractionRing u.V) (PadicAlgCl p) (algebraMap u.V (FractionRing u.V) ϖ)‖)
  refine ⟨q, ?_, fun χ j hj => ?_⟩
  · refine Filter.Tendsto.congr (fun χ => (hq χ).symm) (Filter.Tendsto.const_mul_atTop ?_ ?_)
    · exact neg_pos.2 (Real.log_neg (norm_pos_of_irreducible hϖ) (norm_lt_one_of_irreducible u.norm_le hϖ))
    · exact tendsto_intCast_atTop_atTop.comp (tendsto_val hϖ u.D hQ)
  · rw [hq]
    exact norm_of_hasVal u.norm_le hϖ (hasVal_valF u.D.toPre.P.L _ _ (QForm.ptK_eq u.D.toPre χ) (-1) _ (hQ χ) j hj)

end GlobalTheory.ZH.PsiForm
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaSystemNormWeightSumLeExpOfTest
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ThetaBound

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem proj_mul_proj (T T' : AddSubgroup S.Gam) (h : T' ≤ T) (hT : T ≤ S.perp T)
    (hT' : S.IsoFree T') (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N)
    (hc : ∀ t : T', c' t = c (AddSubgroup.inclusion h t)) :
    S.proj T' c' * S.proj T c = S.proj T c := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have := Fintype.ofFinite T
  have := Fintype.ofFinite T'
  obtain ⟨d, ⟨e⟩⟩ := hT'.2
  have hζ : IsPrimitiveRoot S.ζN S.N := S.prim.pow (NeZero.pos _) (by ring)
  let χ : AddChar (ZMod S.N) o := AddChar.zmodChar S.N hζ.pow_eq_one
  have hu : IsUnit (Nat.card T' : o) := by
    rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
    exact S.unit.pow _
  have h1 : S.proj T c = Ring.inverse (Nat.card T : o) • ∑ t : T, χ (-c t) • S.ρ t := by
    rw [← finsum_eq_sum_of_fintype]; rfl
  have h2 : S.proj T' c' = Ring.inverse (Nat.card T' : o) • ∑ t : T', χ (-c' t) • S.ρ t := by
    rw [← finsum_eq_sum_of_fintype]; rfl
  have h3 : ∀ u : T', (χ (-c' u) • S.ρ u) * ∑ t : T, χ (-c t) • S.ρ t
      = ∑ t : T, χ (-c t) • S.ρ t := fun u => by
    conv_rhs => rw [← Equiv.sum_comp (Equiv.addLeft (AddSubgroup.inclusion h u))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_mul_smul_comm, ← AddChar.map_add_eq_mul, S.ρ_add _ _ (by
      rw [hT (h u.2) t t.2, smul_zero]), hc]
    simp only [Equiv.coe_addLeft, map_add (f := _), neg_add]
    rfl
  have h4 : ∀ u : T', (χ (-c' u) • S.ρ u) * S.proj T c = S.proj T c := fun u => by
    rw [h1, mul_smul_comm, h3]
  rw [h2, smul_mul_assoc, Finset.sum_mul]
  simp_rw [h4]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card, ← Nat.cast_smul_eq_nsmul o,
    smul_smul, Ring.inverse_mul_cancel _ hu, one_smul]

theorem norm_FF_le {p : ℕ} [Fact p.Prime] (y : S.R →+* PadicAlgCl p)
    (hy : ∀ a : o, ‖y (algebraMap o S.R a)‖ ≤ 1) (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N)
    (k : _) (hk : S.FF T c k ∈ S.R) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ t : T, ‖∑ j, y (algebraMap o S.R (S.proj T c j k.1)) * y ⟨S.ev t j, S.ev_mem _ j⟩‖ ≤ B) :
    ‖y ⟨S.FF T c k, hk⟩‖ ≤ B := by
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have := Fintype.ofFinite T
  have h1 : (⟨S.FF T c k, hk⟩ : S.R) = ∑ t : T, algebraMap o S.R (S.ζ ^ (k.2 t).val) *
      ∑ j, algebraMap o S.R (S.proj T c j k.1) * ⟨S.ev t j, S.ev_mem _ j⟩ := by
    apply Subtype.ext
    simp only [ThetaSys.FF, finsum_eq_sum_of_fintype, AddSubmonoidClass.coe_finsetSum,
      MulMemClass.coe_mul, SubalgebraClass.coe_algebraMap]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [h1, map_sum]
  refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg hB fun t _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_mul, norm_mul, map_sum]
  simp_rw [map_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hy _)).trans (h t)

end GlobalTheory.ThetaBound

namespace GlobalTheory

open ThetaBound

theorem thetaSys_norm_FF_le_exp :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω), (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) := by
  intro o Ω _ _ _ hA S H p _ y τ hy T c k hk hT
  obtain ⟨-, -, hperp, href⟩ := thetaSys_FF_mem_finite_perp_proj o Ω S
  have hpos : ∀ α : τ.X, 0 ≤ τ.δ * Real.exp (-(τ.q α / S.N)) := fun α =>
    mul_nonneg τ.δ_pos.le (Real.exp_pos _).le
  refine ⟨fun h1 h2 α hα hc => ?_, fun h1 => ?_⟩
  · refine norm_FF_le S y hy T c k hk (hpos α) fun t => ?_
    rw [← proj_mul_proj S T _ h1 hT.1 τ.isoFree c (τ.wt α) fun u => (hc u (h1 u.2) u.2).symm]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [Matrix.mul_apply, map_sum, map_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos α) fun l _ => ?_
    simp_rw [mul_right_comm _ (y (algebraMap o S.R (S.proj T c l k.1)))]
    rw [← Finset.sum_mul, norm_mul]
    exact (mul_le_of_le_one_right (norm_nonneg _) (hy _)).trans (τ.le α hα t (h2 t.2) l)
  · have hN := S.N_ge
    have hr := S.r_pos
    have : NeZero S.N := ⟨by omega⟩
    have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
    choose a ha hwa using (H p y τ).1
    obtain ⟨d, ⟨e⟩⟩ := hT.2
    obtain ⟨π, hπ⟩ := ThetaProj.exists_retraction T e
    have hfin : Finite (S.perp τ.yy.ker →+ ZMod S.N) := DFunLike.finite _
    set s := {c' : S.perp τ.yy.ker →+ ZMod S.N | c'.comp (AddSubgroup.inclusion h1) = c} with hs
    have hne : s.Nonempty := ⟨(c.comp π).comp (AddSubgroup.subtype _), by
      ext t
      exact congrArg c (hπ t)⟩
    obtain ⟨c₀, hc₀, hmax⟩ := Set.exists_max_image s
      (fun c' => τ.δ * Real.exp (-(τ.q (a c') / S.N))) (Set.toFinite _) hne
    refine ⟨a c₀, ha c₀, fun t h₁ h₂ => ?_, ?_⟩
    · rw [hwa, ← show _ = c from hc₀]
      rfl
    · refine norm_FF_le S y hy T c k hk (hpos _) fun t => ?_
      rw [href _ T h1 τ.isoFree hT c, finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [Matrix.sum_apply, map_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (hpos _) fun c' hc' => ?_
      have ht : (t : S.Gam) ∈ τ.yy.ker := by
        rw [← hperp τ.yy.ker]
        exact τ.isoFree.1 (h1 t.2)
      have := τ.le (a c') (ha c') t ht k.1
      rw [hwa] at this
      exact this.trans (hmax c' ((Set.Finite.mem_toFinset _).mp hc'))

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdmissibleAffineModelDividingTuple
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH

theorem finite_over_subfield_of_le {Ω : Type} [Field Ω] {K L : Subfield Ω} (h : K ≤ L)
    (hK : Module.Finite K Ω) : Module.Finite L Ω := by
  letI : Algebra K L := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower K L Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  exact Module.Finite.of_restrictScalars_finite K L Ω

theorem exists_normal_proj_hasDiv_family (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω]
    (J : Type) [Fintype J] (t : J → Ω) (ht : ∃ i, t i ≠ 0)
    (hfin : Module.Finite
      (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j, x = t j / t i})) Ω)
    (B : Type) [Finite B] (JJ : B → Type) [∀ b, Finite (JJ b)] (tt : ∀ b, JJ b → Ω)
    (htt : ∀ b, ∃ k, tt b k ≠ 0) :
    ∃ M : RatModel o Ω, IsNormalScheme M.Z ∧ IsProjOver M.s ∧ M.HasDiv t ∧ ∀ b, M.HasDiv (tt b) := by
  haveI := ArithBase.ded (o := o) (Ω := Ω)
  haveI := ArithBase.char (o := o) (Ω := Ω)
  letI : Fintype B := Fintype.ofFinite B
  letI : Fintype (∀ b, JJ b) := Fintype.ofFinite _
  choose q₀ hq₀ using htt
  have hP : (∏ b, tt b (q₀ b)) ≠ 0 := Finset.prod_ne_zero_iff.2 fun b _ => hq₀ b
  obtain ⟨i₀, hi₀⟩ := ht
  obtain ⟨M, hM, hp⟩ := GlobalTheory.ZH.exists_isNm_isProjOver o Ω (ArithBase.inj (o := o) (Ω := Ω))
    (J × ∀ b, JJ b) (fun q => t q.1 * ∏ b, tt b (q.2 b)) ⟨(i₀, q₀), mul_ne_zero hi₀ hP⟩
    (finite_over_subfield_of_le (Subfield.closure_mono (Set.union_subset_union_right _ (by
      rintro _ ⟨i, j, rfl⟩
      exact ⟨(i, q₀), (j, q₀), (mul_div_mul_right _ _ hP).symm⟩))) hfin)
  have h := GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M J t
  have h2 : M.HasDiv t ∧ M.HasDiv (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) := by
    refine ⟨fun z => ?_, fun z => ?_⟩
    · obtain ⟨⟨i, q⟩, hi⟩ := hM.1 z
      exact ⟨i, ((h.2.1 _ (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) i q z).1 hi).1⟩
    · obtain ⟨⟨i, q⟩, hi⟩ := hM.1 z
      exact ⟨q, ((h.2.1 _ (fun q : ∀ b, JJ b => ∏ b, tt b (q b)) i q z).1 hi).2⟩
  exact ⟨M, (GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M _ _).1 hM, hp, h2.1, (h.2.2 B JJ tt).1 h2.2⟩

theorem exists_admissible_affine_model_dividing_tuple : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (J₀ : Type) [Fintype J₀] (t₀ : J₀ → Ω), (∃ i, t₀ i ≠ 0) → Module.Finite (Subfield.closure (Set.range (algebraMap o Ω) ∪ {x | ∃ i j : S.Gam × J₀, x = S.th j.1 * t₀ j.2 / (S.th i.1 * t₀ i.2)})) Ω → ∃ (M : RatModel o Ω) (U₀ : M.Z.Opens), S.admitted M U₀ ∧ IsAffineOpen U₀ ∧ M.HasDiv t₀ := by
  intro o Ω _ _ _ _ S J₀ _ t₀ ht₀ hfin
  have hN : S.N ≠ 0 := by have := S.N_ge; omega
  have hr : S.r ≠ 0 := by have := S.r_pos; omega
  haveI : NeZero S.N := ⟨hN⟩
  haveI : NeZero (S.r * S.N) := ⟨mul_ne_zero hr hN⟩
  haveI : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (mul_ne_zero hr hN)⟩
  haveI : Finite (AddSubgroup S.Gam) := Finite.of_injective _ SetLike.coe_injective
  haveI : ∀ T : AddSubgroup S.Gam, Finite (T →+ ZMod S.N) := fun T =>
    Finite.of_injective _ DFunLike.coe_injective
  obtain ⟨x₀, hx₀⟩ := S.th_ne
  obtain ⟨i₀, hi₀⟩ := ht₀
  obtain ⟨M, hn, hp, hd, hF⟩ := exists_normal_proj_hasDiv_family o Ω (S.Gam × J₀)
    (fun q => S.th q.1 * t₀ q.2) ⟨(x₀, i₀), mul_ne_zero hx₀ hi₀⟩ hfin
    {b : Σ T : AddSubgroup S.Gam, T →+ ZMod S.N // S.FF b.1 b.2 ≠ 0}
    (fun b => S.J × (b.1.1 → ZMod ((S.r * S.N) ^ 2))) (fun b => S.FF b.1.1 b.1.2)
    (fun b => Function.ne_iff.1 b.2)
  have h := GlobalTheory.ZH.isNm_normal_and_div_prod o Ω M _ S.th
  have hth : M.HasDiv S.th := fun z => by
    obtain ⟨⟨x, i⟩, hi⟩ := hd z
    exact ⟨x, ((h.2.1 _ t₀ x i z).1 hi).1⟩
  have ht : M.HasDiv t₀ := fun z => by
    obtain ⟨⟨x, i⟩, hi⟩ := hd z
    exact ⟨i, ((h.2.1 _ t₀ x i z).1 hi).2⟩
  have hA : ((fun x : Ω => x⁻¹) '' (Set.range S.th ∪ {x : Ω | ∃ T c k, x = S.FF T c k})).Finite :=
    ((Set.finite_range _).union (GlobalTheory.thetaSys_FF_mem_finite_perp_proj o Ω S).2.1).image _
  obtain ⟨U₀, a, -, hne, haff, -, -, hR, hsub⟩ := GlobalTheory.ZH.exists_affineOpen_ringOn_eq_adjoin_inv o Ω M S.R _
    S.fg S.frac hA ⊤ ⟨genericPoint M.Z, trivial⟩
  refine ⟨M, U₀, ⟨⟨fun x => ⟨hn.1 x, hn.2 x⟩, hp, hth, hne, fun x hx => ?_, fun x _ => hsub ⟨_, Or.inl ⟨x, rfl⟩, rfl⟩,
    fun T c k _ _ => hsub ⟨_, Or.inr ⟨T, c, k, rfl⟩, rfl⟩⟩, fun T c _ h0 => hF ⟨⟨T, c⟩, h0⟩⟩, haff, ht⟩
  rw [hR]
  exact Algebra.subset_adjoin (Set.mem_insert_of_mem _ hx)

end GlobalTheory.ZH
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSumDivThetaConstDotProductMem
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ZH.DualSection

theorem proj_mul_proj_eq_zero {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] [hA : ArithBase o Ω]
    (S : ThetaSys o Ω) {T T' : AddSubgroup S.Gam} (h : T' ≤ T) (hT : S.IsoFree T) (hT' : S.IsoFree T')
    (c : T →+ ZMod S.N) (c' : T' →+ ZMod S.N) (hc : c.comp (AddSubgroup.inclusion h) ≠ c') :
    S.proj T c * S.proj T' c' = 0 := by
  haveI : IsDomain o := hA.inj.isDomain
  haveI := FreeNear.finite_char S T
  haveI := Fintype.ofFinite (T →+ ZMod S.N)
  rw [(thetaSys_FF_mem_finite_perp_proj o Ω S).2.2.2 T T' h hT hT' c',
    finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.mul_sum]
  refine Finset.sum_eq_zero fun c'' hc'' => ?_
  rw [(FreeNear.proj_orthogonal S T hT).1, if_neg]
  rintro rfl
  rw [Set.Finite.mem_toFinset] at hc''
  exact hc hc''

theorem mul_dotProduct_mem_of_mem_span {o Ω J : Type} [CommRing o] [Field Ω] [Algebra o Ω] [Fintype J]
    (O : Subalgebra o Ω) (a : Ω) (u : J → Ω) (V : Set (J → Ω)) (hV : ∀ v ∈ V, a * (u ⬝ᵥ v) ∈ O) :
    ∀ v ∈ Submodule.span O V, a * (u ⬝ᵥ v) ∈ O := by
  intro v hv
  induction hv using Submodule.span_induction with
  | mem _ h' => exact hV _ h'
  | zero => simp
  | add x y _ _ hx hy => rw [dotProduct_add, mul_add]; exact add_mem hx hy
  | smul s x _ hx =>
    rw [dotProduct_smul, Subalgebra.smul_def, smul_eq_mul, mul_left_comm]
    exact mul_mem s.2 hx

theorem ff_div_th_mul_dotProduct_mem : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ → ((∀ U₁ : M.Z.Opens, U₁ ≤ U₀ → (U₁ : Set M.Z).Nonempty → ∀ z : M.Z, IsClosed ({z} : Set M.Z) → (∃ (p : ℕ) (_ : Fact p.Prime) (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y) ∧ ∀ φ ∈ M.ringOn U₁, (∀ (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₁ z y → ‖M.val (gPt p ≫ y) φ‖ ≤ 1) → φ ∈ M.O z) ∧ JacobsonSpace M.Z) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z), M.Cen U₀ z y → ∃ y₀ : S.R →+* PadicAlgCl p, S.At M y y₀ ∧ (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) ∧ Nonempty (S.Test p y₀)) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → (∀ x, x ∈ S.supI M z ↔ ‖M.val (gPt p ≫ y) (S.th x)‖ = τ.δ) ∧ S.HH M z = τ.yy.ker) → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ c : S.perp τ.yy.ker →+ ZMod S.N, ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ τ.wt α = c) ∧ ∀ (T : AddSubgroup S.Gam), S.IsoFree T → T ≤ S.perp τ.yy.ker → ∀ (w : S.Gam → τ.X), (∀ x, τ.yy x = QuotientAddGroup.mk (w x)) → ∀ (I : Set S.Gam), AddSubgroup.closure I = S.perp T → ∀ α : τ.X, (∀ (t : S.Gam) (h₂ : t ∈ S.perp τ.yy.ker), t ∈ T → τ.wt α ⟨t, h₂⟩ = 0) ↔ α ∈ AddSubgroup.closure (w '' I ∪ Set.range fun v₀ : τ.X => S.N • v₀)) → (∀ (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → ∀ (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) (hk : S.FF T c k ∈ S.R), S.IsoFree T → (S.perp τ.yy.ker ≤ T → T ≤ τ.yy.ker → ∀ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N))) ∧ (T ≤ S.perp τ.yy.ker → ∃ α : τ.X, (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) ∧ (∀ (t : S.Gam) (h₁ : t ∈ T) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) ∧ ‖y₀ ⟨S.FF T c k, hk⟩‖ ≤ τ.δ * Real.exp (-(τ.q α / S.N)))) → (∀ (z : M.Z) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (τ : S.Test p y₀), M.Cen U₀ z y → S.At M y y₀ → ∀ (c : S.TT M z →+ ZMod S.N) (k : _) (α : τ.X), M.Div (S.FF (S.TT M z) c) k z → (∀ v₀, τ.q α ≤ τ.q (α + S.N • v₀)) → (∀ (t : S.Gam) (h₁ : t ∈ S.TT M z) (h₂ : t ∈ S.perp τ.yy.ker), c ⟨t, h₁⟩ = τ.wt α ⟨t, h₂⟩) → ‖M.val (gPt p ≫ y) (S.FF (S.TT M z) c k)‖ = τ.δ * Real.exp (-(τ.q α / S.N))) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → ∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N) (k : _) (i : S.J) (z : M.Z), S.supI M ξ ⊆ S.supI M z → ∀ x₀ ∈ S.supI M z, ∀ v ∈ EE.E z, S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ v) ∈ M.O z := by
  intro o Ω _ _ _ _ S M U₀ EE hAdm hLL hT hS hG hW hB hE _ hEE ξ c k i
  have hO := hAdm.1
  have key : ∀ z : M.Z, IsClosed ({z} : Set M.Z) → S.supI M ξ ⊆ S.supI M z → ∀ x₀ ∈ S.supI M z, ∀ v ∈ EE.E z,
      S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ v) ∈ M.O z := by
    intro z hz hI x₀ hx₀
    have hH : S.HH M ξ ≤ S.HH M z := AddSubgroup.closure_mono hI
    have hTT : S.TT M z ≤ S.TT M ξ := FirstIneq.perp_anti_of_le S hH
    rw [hEE z hz]
    refine mul_dotProduct_mem_of_mem_span _ _ _ _ ?_
    rintro _ ⟨c₁, k₁, x₁, i₁, hd, -, rfl⟩
    have e : S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ
        fun j => S.th x₁ / S.FF _ c₁ k₁ * algebraMap o Ω (S.proj _ c₁ j i₁)) =
        S.FF _ c k / S.FF _ c₁ k₁ * (S.th x₁ / S.th x₀) *
          algebraMap o Ω ((S.proj _ c * S.proj _ c₁) i i₁) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [dotProduct, Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    by_cases hc : c.comp (AddSubgroup.inclusion hTT) = c₁
    swap
    · rw [proj_mul_proj_eq_zero S hTT (hG.1 ξ).1 (hG.1 z).1 c c₁ hc]
      simp
    refine mul_mem (mul_mem ?_ (hx₀.2 x₁)) (Subalgebra.algebraMap_mem _ _)
    have hf : S.FF _ c k ∈ M.ringOn U₀ := hO.le (FirstIneq.ff_mem_ring S _ c k)
    have hf' : S.FF _ c₁ k₁ ∈ M.ringOn U₀ := hO.le (FirstIneq.ff_mem_ring S _ c₁ k₁)
    have hi : (S.FF _ c₁ k₁)⁻¹ ∈ M.ringOn U₀ := hO.FF_unit _ c₁ k₁ (hG.1 z).1 hd.1
    refine (hLL.1 U₀ le_rfl hO.ne z hz).2 _ ?_ ?_
    · rw [div_eq_mul_inv]
      exact mul_mem hf hi
    intro p _ y hy
    obtain ⟨y₀, hAt, hint, ⟨τ⟩⟩ := hT z p y hy
    have hker : S.HH M z = τ.yy.ker := (hS z p y y₀ τ hy hAt).2
    have hperp : S.perp τ.yy.ker = S.TT M z := by rw [← hker]; rfl
    obtain ⟨α, hα, hwt⟩ := (hW p y₀ τ).1 (c₁.comp (AddSubgroup.inclusion hperp.le))
    have h1 := (hB p y₀ τ hint (S.TT M ξ) c k (FirstIneq.ff_mem_ring S _ c k) (hG.1 ξ).1).1
      (hperp.le.trans hTT) (((hG.1 ξ).1.1.trans (hG.1 ξ).2.le).trans (hH.trans hker.le)) α hα
      (fun t h₁ h₂ => by rw [hwt, ← hc]; rfl)
    have h2 := hE z p y y₀ τ hy hAt c₁ k₁ α hd hα (fun t h₁ h₂ => by rw [hwt]; rfl)
    rw [hAt, ← h2] at h1
    set yg := gPt p ≫ y with hyg
    have w : Sp (PadicAlgCl p) := IsLocalRing.closedPoint (PadicAlgCl p)
    have hw : yg w ∈ (U₀ : Set M.Z) := hy.2 ⟨w, rfl⟩
    have hsp := RatModel.specializes_of_range_eq (RatModel.range_eq_singleton yg w)
    have e1 : M.val yg (S.FF _ c₁ k₁) * M.val yg (S.FF _ c₁ k₁)⁻¹ = 1 := by
      rw [← RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf') (RatModel.ringOn_le_O hw hi),
        mul_inv_cancel₀ hd.1, RatModel.val_one]
    rw [div_eq_mul_inv, RatModel.val_mul hsp (RatModel.ringOn_le_O hw hf) (RatModel.ringOn_le_O hw hi),
      norm_mul, ← norm_one (α := PadicAlgCl p), ← e1, norm_mul]
    exact mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
  intro z hI x₀ hx₀
  obtain ⟨U, b, hzU, -, hb⟩ := EE.loc z
  obtain ⟨x, hxU, hxc, hzx, hIx⟩ := hG.2.2.2 z U hzU
  rw [hb z hzU]
  refine mul_dotProduct_mem_of_mem_span _ _ _ _ fun v hv => RatModel.O_le_of_specializes hzx ?_
  refine key x hxc (hIx ▸ hI) x₀ (hIx ▸ hx₀) v ?_
  rw [hb x hxU]
  exact Submodule.subset_span hv

end GlobalTheory.ZH.DualSection
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLevelStructureOfGenericOfFibrewiseIndep
section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLevelStructureOfGenericOfFibrewiseIndep
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SpreadLevel

theorem appTop_unitOn {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (u : Rˣ) (u₀ : Kˣ)
    (h : f u = u₀) : Units.map (spMap f).appTop.hom.toMonoidHom (unitOn u) = unitOn u₀ := by
  apply Units.ext
  have := congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  rw [h] at this
  exact this.symm

theorem appTop_injective {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (hf : Function.Injective f) :
    Function.Injective (spMap f).appTop.hom := by
  have e := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  intro a b hab
  have ha := congrArg (fun q => q.hom a) e
  have hb := congrArg (fun q => q.hom b) e
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at ha hb
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  apply hf
  exact ha.symm.trans ((congrArg _ hab).trans hb)

theorem linComb_pow {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {T : Over S} {n : ℕ}
    (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) (M : ℕ) (h : ∀ i, y i ^ M = 1) : linComb y a ^ M = 1 := by
  unfold linComb
  rw [List.prod_ofFn, ← Finset.prod_pow]
  exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]

theorem stdSymp_cast {g g' : ℕ} (h : g = g') (i j : Fin (2 * g)) (i' j' : Fin (2 * g')) (hi : (i' : ℕ) = i)
    (hj : (j' : ℕ) = j) : stdSymp g' i' j' = stdSymp g i j := by
  subst h
  rw [Fin.ext hi, Fin.ext hj]

end SpreadLevel


open SpreadLevel in
theorem level_of_generic_of_indep : Laws → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (P : PolAV (Sp R)) (P₀ : PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A (spMap (algebraMap R K)) φ → LBIso P₀.L (P.L.pull φ) → P.g = P₀.g → ∀ (M : ℕ) (ze : Rˣ) (ze₀ : Kˣ), IsUnit (M : R) → algebraMap R K ze = ze₀ → ∀ (lev₀ : Out.Level P₀ M (unitOn ze₀)) (y : Fin (2 * P.g) → (baseOver (Sp R) ⟶ P.A)), (∀ (i₀ : Fin (2 * P₀.g)) (i : Fin (2 * P.g)), (i₀ : ℕ) = i → (lev₀.pt i₀).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R) (c c' : Fin (2 * P.g) → Fin M), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c' i : ℕ)) → c = c') → ∃ lev : Out.Level P M (unitOn ze), lev.pt = y := by
  intro hL R K _ _ _ _ _ _ P P₀ φ hp hw hg M ze ze₀ hM hze lev₀ y hy hind
  obtain ⟨w, hw⟩ := hw
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  have hu := appTop_unitOn (algebraMap R K) ze ze₀ hze
  have hΓ : Function.Injective (Units.map (spMap (algebraMap R K)).appTop.hom.toMonoidHom) :=
    Units.map_injective (appTop_injective _ hinj)
  have := P.isAb.comm
  have := P.isAb.proper
  let cs : Fin (2 * P.g) → Fin (2 * P₀.g) := Fin.cast (by rw [hg])
  have hy' : ∀ i, spMap (algebraMap R K) ≫ (y i).left = (lev₀.pt (cs i)).left ≫ φ := fun i => (hy (cs i) i rfl).symm
  let U : Over.mk ((baseOver (Sp K)).hom ≫ spMap (algebraMap R K)) ⟶ baseOver (Sp R) :=
    Over.homMk (spMap (algebraMap R K)) (by simp)
  have tor : ∀ i, y i ^ M = 1 := fun i => by
    have e : U ≫ y i = pushHom hp (baseOver (Sp K)) (lev₀.pt (cs i)) := Over.OverMorphism.ext (hy' i)
    have e₁ : U ≫ (y i ^ M) = U ≫ 1 := by
      rw [MonObj.comp_pow, MonObj.comp_one, e]
      exact (map_pow (pushHom hp _) _ M).symm.trans ((congrArg _ (lev₀.torsion _)).trans (map_one _))
    exact over_points_ext_of_injective _ P.A R K _ hinj _ _ _ (congrArg (fun q => q.left) e₁)
  refine ⟨⟨y, ?_, tor, hind, ?_, ?_⟩, rfl⟩
  · have := lev₀.prim
    rw [← hu] at this
    exact this.of_map_of_injective hΓ
  · intro F _ _ s x hx
    have hF : (M : F) ≠ 0 := by
      have := hM.map (Spec.preimage s).hom
      rw [map_natCast] at this
      exact this.ne_zero
    have hM0 : 1 ≤ M := Nat.pos_of_ne_zero (by rintro rfl; exact hF Nat.cast_zero)
    have hc := (hL.mulN _ P M hM0).2.2.2.2 F s hF
    let Φ : (Fin (2 * P.g) → Fin M) → {x : Over.mk s ⟶ P.A // x ^ M = 1} := fun c =>
      ⟨linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)),
        linComb_pow _ _ M fun i => by rw [← MonObj.comp_pow, tor, MonObj.comp_one]⟩
    have hΦ : Function.Injective Φ := fun c c' h => hind F s c c' (congrArg Subtype.val h)
    have : Finite {x : Over.mk s ⟶ P.A // x ^ M = 1} :=
      Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
    have hb := hΦ.bijective_of_nat_card_le (by rw [hc]; simp)
    obtain ⟨c, h⟩ := hb.2 ⟨x, hx⟩
    exact ⟨c, congrArg Subtype.val h⟩
  · intro i j
    obtain ⟨c, hc, -⟩ := (hL.weil _ P M (baseOver (Sp R))).1 (y i) (y j) (tor i) (tor j)
    obtain ⟨r, hr, ⟨cu⟩⟩ := PolAV_exists_cubical hL.cube P₀
    have := P₀.isAb.comm
    have h₁ := WeilCube.weilIs_pull (c := cu) hL.globalFns P₀.isAb P.isLB hp w hw (T := baseOver (Sp K))
      (T₀ := baseOver (Sp R)) (spMap (algebraMap R K)) (by simp) (lev₀.torsion (cs i)) (lev₀.torsion (cs j))
      (hy' i) (hy' j) hc
    have h₂ := ((hL.weil _ P₀ M (baseOver (Sp K))).1 _ _ (lev₀.torsion (cs i)) (lev₀.torsion (cs j))).unique h₁
      (lev₀.pairing _ _)
    rw [stdSymp_cast hg i j (cs i) (cs j) rfl rfl, ← hu] at h₂
    have h₃ : c = unitOn ze ^ stdSymp P.g i j := hΓ (h₂.trans (map_zpow _ _ _).symm)
    exact h₃ ▸ hc

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsLevelStructureOfGenericOfFibrewiseIndepStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isLevelStructure_of_generic_of_fibrewise_indep : Laws → ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (P : PolAV (Sp R)) (P₀ : PolAV (Sp K)) (φ : P₀.A.left ⟶ P.A.left), IsGrpPullback P₀.A P.A (spMap (algebraMap R K)) φ → LBIso P₀.L (P.L.pull φ) → P.g = P₀.g → ∀ (M : ℕ) (ze : Rˣ) (ze₀ : Kˣ), IsUnit (M : R) → algebraMap R K ze = ze₀ → ∀ (lev₀ : Out.Level P₀ M (unitOn ze₀)) (y : Fin (2 * P.g) → (baseOver (Sp R) ⟶ P.A)), (∀ (i₀ : Fin (2 * P₀.g)) (i : Fin (2 * P.g)), (i₀ : ℕ) = i → (lev₀.pt i₀).left ≫ φ = spMap (algebraMap R K) ≫ (y i).left) → (∀ (F : Type) [Field F] [IsAlgClosed F] (s : Spec (CommRingCat.of F) ⟶ Sp R) (c c' : Fin (2 * P.g) → Fin M), linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c i : ℕ)) = linComb (fun i => (Over.homMk s (by simp) : Over.mk s ⟶ baseOver (Sp R)) ≫ y i) (fun i => (c' i : ℕ)) → c = c') → ∃ lev : Out.Level P M (unitOn ze), lev.pt = y := by
  first | exact @GlobalTheory.level_of_generic_of_indep | exact GlobalTheory.level_of_generic_of_indep | (intros; apply GlobalTheory.level_of_generic_of_indep <;> assumption)
end
end
