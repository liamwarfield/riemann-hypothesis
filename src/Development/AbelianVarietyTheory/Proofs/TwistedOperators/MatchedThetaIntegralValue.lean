module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLatticeForMatchedFrames
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormBottom
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowLatticesGoodPositionLargeDepth

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.SmallConst

theorem kerSmall_rat_mid {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) (B : Frames G)
    (ρ : RealMatch W) (t : T) (i j : Fin D.R.m) (Θ : TotT G (routeBig t i j)) (Θ' : TotT G (routeSmall t i j))
    (hΘ : IsMatched B t ρ i j Θ Θ') (g : GA D (G.V (.grid i (j + 1)))) (g₁ : GA D (G.V (.grid (i + 1) j))) :
    ∀ γ ∈ GQ (G.V (.grid i j)), ∀ u, kerSmall W Θ' g g₁ (γ * u) = kerSmall W Θ' g g₁ u := by
  intro γ hγ u
  have hm := W.om_is (.mu t i j) ⟨i.2.le, j.2⟩
  have hc := W.om_is (.chi (i : ℕ) j) ⟨i.2, j.2.le⟩
  unfold kerSmall
  refine Finsupp.sum_congr fun d hd => ?_
  obtain ⟨h2, h1⟩ := GlobalTheory.SmallRoute.theta_of_matched hΘ hd
  congr 1
  congr 1
  · show thetaKO (W.om (.mu t i j)) (γ * u) g d.1.2 = thetaKO (W.om (.mu t i j)) u g d.1.2
    unfold thetaKO
    have e : ((γ * u, g) : GA D (G.pS (.mu t i j)) × GA D (G.pT (.mu t i j))) = (γ, 1) * (u, g) := by simp
    rw [e, map_mul]
    exact hm.om_aut γ hγ 1 (one_mem _) _ (hm.om_pres _ _ h1)
  · show thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) (γ * u) d.2 = thetaKO (W.om (.chi (i : ℕ) j)) (negGA _ g₁) u d.2
    unfold thetaKO
    have e : ((negGA _ g₁, γ * u) : GA D (G.pS (.chi (i : ℕ) j)) × GA D (G.pT (.chi (i : ℕ) j))) =
        (1, γ) * (negGA _ g₁, u) := by simp
    rw [e, map_mul]
    exact hc.om_aut 1 (one_mem _) γ hγ _ (hc.om_pres _ _ h2)

theorem setIntegral_mul_right {D : D7} (V : HSp D) (ν : Measure (GA D V)) [hH : ν.IsHaarMeasure] (fd : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) fd ν) (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (hint : IntegrableOn F fd ν) (k : GA D V) :
    IntegrableOn (fun u => F (u * k)) fd ν ∧ ∫ u in fd, F (u * k) ∂ν = ∫ u in fd, F u ∂ν := by
  haveI := GlobalTheory.AdelicPointsUnimod.isMulRightInvariant_of_isHaarMeasure D V ν hH
  have hmp : MeasurePreserving (fun x : GA D V => x * k⁻¹) ν ν := measurePreserving_mul_right ν k⁻¹
  have ht : IsFundamentalDomain (GQ V) ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν :=
    hfd.preimage_of_equiv hmp.quasiMeasurePreserving (e := id) Function.bijective_id
      (fun g x => by simp [Subgroup.smul_def, mul_assoc])
  have hinv : ∀ (g : GQ V) (x : GA D V), F (g • x) = F x := fun g x => hF g g.2 x
  have hmp2 : MeasurePreserving (fun x : GA D V => x * k) ν ν := measurePreserving_mul_right ν k
  have hpre : (fun x : GA D V => x * k) ⁻¹' ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) = fd := by
    ext x; simp
  have hemb : MeasurableEmbedding (fun x : GA D V => x * k) := (MeasurableEquiv.mulRight k).measurableEmbedding
  have h1 : IntegrableOn F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd) ν := (hfd.integrableOn_iff ht hinv).1 hint
  have e1 : ∫ u in fd, F (u * k) ∂ν = ∫ u in (fun x : GA D V => x * k⁻¹) ⁻¹' fd, F u ∂ν := by
    have := hmp2.setIntegral_preimage_emb hemb F ((fun x : GA D V => x * k⁻¹) ⁻¹' fd)
    rw [hpre] at this
    exact this
  refine ⟨?_, ?_⟩
  · rw [← hpre]
    exact (hmp2.integrableOn_comp_preimage hemb).2 h1
  · rw [e1]; exact (hfd.setIntegral_eq ht hinv).symm

theorem translates_left_inv {D : D7} {V : HSp D} (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (w : GA D V →₀ ℂ) : ∀ γ ∈ GQ V, ∀ u, translates w F (γ * u) = translates w F u := by
  intro γ hγ u
  unfold translates
  refine Finsupp.sum_congr fun k _ => ?_
  rw [mul_assoc, hF γ hγ]

theorem integral_translates {D : D7} (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] (fd : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) fd ν) (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (hint : IntegrableOn F fd ν) (w : GA D V →₀ ℂ) :
    IntegrableOn (translates w F) fd ν ∧ ∫ u in fd, translates w F u ∂ν = zdeg w * ∫ u in fd, F u ∂ν := by
  have h := fun k => setIntegral_mul_right V ν fd hfd F hF hint k
  have e : translates w F = fun u => ∑ k ∈ w.support, w k * F (u * k) := by
    funext u; rfl
  rw [e]
  refine ⟨integrable_finsetSum _ fun k _ => (h k).1.const_mul _, ?_⟩
  rw [integral_finsetSum _ fun k _ => (h k).1.const_mul _]
  simp only [integral_const_mul, (h _).2]
  rw [zdeg, Finsupp.sum, Finset.sum_mul]

theorem translates_comm {H : Type} [Monoid H] (F : H → ℂ) (a b : H →₀ ℂ)
    (hab : ∀ x ∈ a.support, ∀ y ∈ b.support, x * y = y * x) :
    translates a (translates b F) = translates b (translates a F) := by
  funext u
  simp only [translates, Finsupp.sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y hy => Finset.sum_congr rfl fun x hx => ?_
  rw [mul_assoc, mul_assoc, hab x hx y hy]; ring

theorem zdeg_mul_integral_comm {D : D7} (V : HSp D) (ν : Measure (GA D V)) [ν.IsHaarMeasure] (fd : Set (GA D V))
    (hfd : IsFundamentalDomain (GQ V) fd ν) (F : GA D V → ℂ) (hF : ∀ γ ∈ GQ V, ∀ u, F (γ * u) = F u)
    (a b : GA D V →₀ ℂ) (hab : ∀ x ∈ a.support, ∀ y ∈ b.support, x * y = y * x)
    (ha : IntegrableOn (translates a F) fd ν) (hb : IntegrableOn (translates b F) fd ν) :
    zdeg a * ∫ u in fd, translates b F u ∂ν = zdeg b * ∫ u in fd, translates a F u ∂ν := by
  rw [← (integral_translates V ν fd hfd _ (translates_left_inv F hF b) hb a).2,
    ← (integral_translates V ν fd hfd _ (translates_left_inv F hF a) ha b).2, translates_comm F a b hab]

end GlobalTheory.SmallConst

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.CastMulUnitaryAdelicGroupOfEq
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBottomLevelLeFormLevelLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBottomLevelLeFormLevelLargeDepth
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowLevel

theorem finE_cast_mem {D : D7} (X Y : LSp D) (e : X = Y) (K : Subgroup (GL (Fin X.sp.rank) (Lev.EAf D)))
    (K' : Subgroup (GL (Fin Y.sp.rank) (Lev.EAf D))) (h : HEq K K') (g : GA D X.sp) (hg : Lev.finE X.sp g ∈ K) :
    Lev.finE Y.sp (cast (congrArg (fun Z : LSp D => GA D Z.sp) e) g) ∈ K' := by
  subst e
  cases h
  exact hg

theorem toXf_mem_of_is {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} (W : G.Weil) {U : Set T}
    (S : GridChoice W U) {μ₀ : T} (hL : L.Is μ₀) (t : T) (k : FinPt G (.grid 0 D.R.m))
    (hk : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _)) :
    toXf k ∈ (levEnv D.sp.X' L.βX (L.datXt t)).J := by

  have hU : finG (G.V (.grid 0 D.R.m)) k ∈ S.levRow t 0 (Nat.zero_le _) ⊓ UA D.sp.cm (G.V (.grid 0 D.R.m)).gram :=
    ⟨hk, GlobalTheory.LevSplit.finE_mem_UA _ _⟩
  have hX := finE_cast_mem (columnBlock L D.R.m) ⟨D.sp.X', L.ΛX⟩ (colY_m L) _ _
    (GlobalTheory.T.gridRowLevel_zero_inf_unitary_eq_datumLevel W S hL t (Nat.zero_le _)) k.1 hU
  exact hX

theorem levRow_zero_le : Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J := by
  refine ⟨0, fun ε CF _ => ⟨0, ?_⟩⟩
  intro D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch _ _
  exact fun t k hk => toXf_mem_of_is ch.W ch.S.toGridChoice hS.core.lev t k hk

end GlobalTheory.FirstRowLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridBottomLevelLeFormLevelLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridBottomLevel_le_formLevel_largeDepth : Big fun {D} {_Γ} _ _ {_Pl0} {T} {_A} {_Ks} _ _ _ {R} ch =>
    ∀ (t : T) (k : FinPt ch.G (.grid 0 D.R.m)), finG (ch.G.V (.grid 0 D.R.m)) k ∈ ch.S.levRow t 0 (Nat.zero_le _) →
      toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J := by
  first | exact @GlobalTheory.FirstRowLevel.levRow_zero_le | exact GlobalTheory.FirstRowLevel.levRow_zero_le | (intros; apply GlobalTheory.FirstRowLevel.levRow_zero_le <;> assumption)
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

namespace GlobalTheory.FirstRowLaw

section Gen
variable {Gg Γg : Type} [Group Gg] [Group Γg] {Wg : Type} [NormedAddCommGroup Wg] [InnerProductSpace ℂ Wg]

theorem adForms_law (ι : Γg →* Gg) (ρ : Γg →* Module.End ℂ Wg) (J : Subgroup Gg) (χ : J →* ℂˣ) {F : Gg → Wg}
    (hF : F ∈ Bridge.AdForms ι ρ J χ) (h : Gg) (k : J) : F (h * k) = (χ k : ℂ) • F h := by
  have e := hF 1 h k
  rwa [map_one, one_mul, map_one, Module.End.one_apply] at e

end Gen

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {sc : Consts}
  {G : GridData R.toLevCh sc} {W : G.Weil} {U : Set T}

theorem cast_mul_unitaryAdelicGroup_of_eq {X Y : LSp D} (h : X = Y) (a b : GA D X.sp) :
    cast (congrArg (fun X : LSp D => GA D X.sp) h) (a * b) =
      cast (congrArg (fun X : LSp D => GA D X.sp) h) a * cast (congrArg (fun X : LSp D => GA D X.sp) h) b := by
  subst h; rfl

theorem toXf_mul (y k : FinPt G (.grid 0 D.R.m)) : toXf (y * k) = toXf y * toXf k := by
  unfold toXf
  rw [← map_mul, Subgroup.coe_mul]
  exact congrArg _ (cast_mul_unitaryAdelicGroup_of_eq (colY_m R.toLevCh) _ _)

theorem formC_apply (S : SumChoice W U) (t : T) (u : (R.HX t).H) (y : FinPt G (.grid 0 D.R.m)) :
    S.formC t u y = S.co ((R.HX t).e u (toXf y)) := rfl

theorem formC_mul (S : SumChoice W U) (hHX : R.models_HX) (t : T) (u : (R.HX t).H) (y k : FinPt G (.grid 0 D.R.m))
    (hk : toXf k ∈ (levEnv D.sp.X' R.βX (R.datXt t)).J) :
    S.formC t u (y * k) = (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • S.formC t u y := by
  have h : ∀ F, F ∈ LinearMap.range (R.HX t).e → F ∈ Bridge.AdForms (Bridge.ratF D.sp.X') R.cX.coef.ρ
      (levEnv D.sp.X' R.βX (R.datXt t)).J (levEnv D.sp.X' R.βX (R.datXt t)).χ := fun F hF => (hHX t).2.1 ▸ hF
  have e : (R.HX t).e u (toXf y * toXf k) =
      (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • (R.HX t).e u (toXf y) :=
    adForms_law (Bridge.ratF D.sp.X') _ _ _ (h _ (LinearMap.mem_range_self (R.HX t).e u)) (toXf y) ⟨toXf k, hk⟩
  calc S.formC t u (y * k) = S.co ((R.HX t).e u (toXf (y * k))) := formC_apply S t u (y * k)
    _ = S.co ((R.HX t).e u (toXf y * toXf k)) := congrArg (fun z => S.co ((R.HX t).e u z)) (toXf_mul y k)
    _ = S.co ((((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • (R.HX t).e u (toXf y)) := congrArg S.co e
    _ = (((levEnv D.sp.X' R.βX (R.datXt t)).χ ⟨toXf k, hk⟩ : ℂˣ) : ℂ) • S.co ((R.HX t).e u (toXf y)) := S.co.map_smul _ _
    _ = _ := congrArg _ (formC_apply S t u y).symm

end GlobalTheory.FirstRowLaw

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaAreRealDatumLargeDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaAreRealDatumLargeDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
open scoped TensorProduct
namespace GlobalTheory.VacRealPf

variable {D : D7}

theorem mem_GfC_of_idemSum {e : AE D} {Q : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e Q) {V : HSp D} {g : GA D V}
    (hs : SuppAt e V g) : g ∈ GfC V := by
  have h0 : infPart D (e + cA D e) = 0 := by
    have h1 := GlobalTheory.FinRestComm.infPart_of_idemSum he
    rw [RingHom.map_add (f := _), h1, GlobalTheory.AdjointPair.infPart_zero e h1, add_zero]
  show g ∈ (infHom V).ker
  rw [MonoidHom.mem_ker]
  apply Units.ext
  ext i j
  have h1 := congrArg (infPart D) (hs i j)
  rw [map_mul, h0, zero_mul] at h1
  have e : (infHom V g).1 i j = infPart D (mt V g i j) := rfl
  change (infHom V g).1 i j = (1 : GL (Fin V.rank) (Ainf D.host.F ⊗[D.host.F] D.host.E)).1 i j
  rw [e, Units.val_one]
  have h2 : infPart D ((mt V g - 1) i j) = infPart D (mt V g i j) - (1 : Matrix (Fin V.rank) (Fin V.rank) _) i j := by
    rw [Matrix.sub_apply, RingHom.map_sub]
    by_cases hij : i = j
    · subst hij; rw [Matrix.one_apply_eq, Matrix.one_apply_eq, RingHom.map_one]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne hij, RingHom.map_zero]
  rw [h2] at h1
  exact sub_eq_zero.1 h1.symm

theorem moves_one (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) : GlobalTheory.FinPl.Moves S 1 L L P := by
  intro y _
  rw [show mt S 1 = 1 from rfl, Matrix.one_mulVec]

theorem mem_idx {j : ℕ} : j ∈ idx D ↔ 1 ≤ j ∧ j + 2 ≤ D.R.m := by
  have := D.R.two_le_m
  simp only [idx, List.mem_range'_1]
  omega

section
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type} {A : FamIn D.what₂.LL Γ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (ch : Choice R)

theorem base_fin {t : T} {b : Pts ch.G} (hb : IsBase t ch.S.B b) (j : ℕ) : b j ∈ GfC _ := by
  by_cases h0 : j = 0
  · subst h0
    obtain ⟨e, he, hs, -⟩ := hb.1
    exact mem_GfC_of_idemSum he hs
  · by_cases hj : j ∈ idx D
    · obtain ⟨δ, -, hδ⟩ := hb.2.1 j hj
      exact hδ.1
    · rw [hb.2.2 j h0 hj]; exact one_mem _

theorem sd_grid (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (ch.G.Λ (.grid D.R.m j)) :=
  (ch.G.isV (X := .grid D.R.m j) ⟨le_rfl, hj⟩ fun i e => by
    have := D.R.two_le_m
    injection e with e1
    omega).sd

theorem sd_top (j : ℕ) (hj : j ≤ D.R.m) : IsSelfDualC _ (ch.G.Λ (.top j)) :=
  (ch.G.isV (X := .top j) hj fun i e => by cases e).sd

theorem fock_vac (t : T) (j : ℕ) (hj : j < D.R.m) (P : PolDown ch.G) {M : GlobalTheory.FinPl.Lat (ch.G.V (.grid D.R.m j))}
    {M' : GlobalTheory.FinPl.Lat (ch.G.V (.grid D.R.m (j + 1)))} (hM : IsSelfDualC _ M) (hM' : IsSelfDualC _ M')
    {g : GA D (ch.G.V (.grid D.R.m j))} {h : GA D (ch.G.V (.grid D.R.m (j + 1)))} (hg : g ∈ GfC _) (hh : h ∈ GfC _)
    (mg : GlobalTheory.FinPl.Moves _ g (ch.G.Λ (.grid D.R.m j)) M fun _ => True)
    (mh : GlobalTheory.FinPl.Moves _ h (ch.G.Λ (.grid D.R.m (j + 1))) M' fun _ => True)
    {x : GA D (ch.G.V (.grid D.R.m j))} {y : GA D (ch.G.V (.grid D.R.m (j + 1)))} (hx : x ∈ GinfC _) (hy : y ∈ GinfC _) :
    GlobalTheory.FinPl.Vac ch.W.ψ (ch.G.V (.grid D.R.m j)) (ch.G.V (.grid D.R.m (j + 1))) M M' (fun _ => True)
      (ch.W.om (.mu t D.R.m j) (x * g, y * h) (fockD ch.W t (fun j => ch.rm.vT D.R.m j) P ⟨j, hj⟩)) :=
  (GlobalTheory.StepMove.gen (ch.W.om_is (.mu t D.R.m j) ⟨le_rfl, hj⟩) (sd_grid ch j hj.le) hM (sd_grid ch (j + 1) hj) hM' hg hh mg mh _ _
    (ch.rm.vT_is t D.R.m j le_rfl hj)).1 _ x hx y hy

theorem real_of {ψ : AddChar (AF D.host.F) ℂ} {X S X' : HSp D} {LA : GlobalTheory.FinPl.Lat X} {LS : GlobalTheory.FinPl.Lat S}
    {LA' : GlobalTheory.FinPl.Lat X'} {C : WO X S → WO S X' → ℂ} (h : IsBiTheta ψ X S X' C)
    (h' : GlobalTheory.FinPl.BiVacAt ψ LA LS LA' (fun _ => True) C) :
    IsBiVac ψ X S X' (LA : Set _) (LS : Set _) (LA' : Set _) C ∧ IsBiSmooth C :=
  ⟨⟨h.cont, h'.1, h'.2⟩, h.smooth⟩

theorem vac_cast {V : HSp D} {LV : GlobalTheory.FinPl.Lat V} {n n' : ℕ} (h : n = n') {f : WO V (ch.G.V (.grid D.R.m n)) → ℂ}
    (hf : GlobalTheory.FinPl.Vac ch.W.ψ V _ LV (ch.G.Λ (.grid D.R.m n)) (fun _ => True) f) :
    GlobalTheory.FinPl.Vac ch.W.ψ V _ LV (ch.G.Λ (.grid D.R.m n')) (fun _ => True) (castSch ch.G h f) := by
  subst h
  exact hf

theorem orth_cast {LZ : GlobalTheory.FinPl.Lat (pLine D)} {v : GlobalTheory.FinPl.Pl D}
    (hor : GlobalTheory.FinPl.OrthAt (topOrth ch.G) (ch.G.Λ (.top D.R.m)) (ch.G.Λ (.grid D.R.m D.R.m)) LZ v) {n : ℕ} (h : D.R.m = n) :
    GlobalTheory.FinPl.OrthAt (topOrthAt ch.G h) (ch.G.Λ (.top n)) (ch.G.Λ (.grid D.R.m D.R.m)) LZ v := by
  subst h
  exact hor

theorem vacReal_of_shape (hsh : ShapeAt ch) : VacReal ch := by
  obtain ⟨N, N₀, LL, LZ, hmv, hLZ, hor, hall⟩ := hsh
  intro t M hM b hb P p hp j hje hjm
  have hm2 := D.R.two_le_m
  obtain ⟨a, ha⟩ := D.R.m_even
  obtain ⟨c, hc⟩ := hje
  have hψ : IsStdChar D ch.W.ψ (-1) := ch.W.ψ_std
  obtain ⟨x₀⟩ := GlobalTheory.SeeSaw.VacShape.nonempty_pl D
  have hFV := GlobalTheory.T.flatMapPreservesVacuum_proof D ch.W.ψ (fun _ => True)
  have hbf := base_fin ch hb
  have hpi : ∀ k, p k ∈ GinfC _ := hp.1
  unfold conAt
  by_cases h0 : j + 2 * 0 + 2 = D.R.m
  · rw [dite_eq_left h0]
    have hb1 : b (j + 1) = 1 := hb.2.2 (j + 1) (by omega) fun h => by
      have := (mem_idx.1 h).2
      omega
    have hs := hall t M hM j 0 h0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have hg0 := (hs x₀).2.2.1
    have hmv1 := hmv t b hb (j + 1) (by omega)
    rw [hb1] at hmv1
    have v₁ := fock_vac ch t j (by omega) P (M := N j) (M' := N (j + 1)) hg0.sdV hg0.sdW (hbf j) (one_mem _)
      (hmv t b hb j (by omega)) hmv1 (hpi j) (one_mem _)
    rw [one_mul] at v₁
    have v₂ := fock_vac ch t (j + 1) (by omega) P (M := N (j + 1)) (M' := ch.G.Λ (.grid D.R.m (j + 1 + 1))) hg0.sdW
      (sd_grid ch _ (by omega)) (one_mem _) (one_mem _) hmv1 (moves_one _ _ _) (one_mem _) (one_mem _)
    rw [one_mul, one_mul, Prod.mk_one_one, map_one, Module.End.one_apply] at v₂
    have v₃ := vac_cast ch (show j + 1 + 1 = D.R.m by omega) v₂
    have f₁ := hFV.1 0 _ _ (lastAt ch.G ch.W t hM j h0 (GlobalTheory.Unf.Inhab.nonempty_volN _).some).s (N j) (N₀ j) (N (j + 1))
      (ch.G.Λ (.top (j + 1))) (fun x _ => (hs x).2.2.1) _ v₁
    have f₂ := hFV.2.2 _ _ _ (rowJac ch.G (j + 1) (by omega) 0 (by omega)) (N (j + 1)) (ch.G.Λ (.top (j + 1)))
      (ch.G.Λ (.grid D.R.m D.R.m)) hg0.sdW hg0.sdW₀ (sd_grid ch _ le_rfl) (fun x _ => (hs x).2.2.1.monoW) _ v₃
    refine real_of ?_ ?_
    · exact GlobalTheory.LastBiTheta.isBiTheta_lastBi D _ hψ _ _ _ _ _ _ _ _ _ _ GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram _ _ f₁.1 f₂.1
    · exact GlobalTheory.T.lastSeeSawDatum_of_vacua_is_vacuum_both D _ hψ _ _ _ _ _ _ _ _ _ _ rfl rfl GlobalTheory.RowChain.LastSeeSawStep.lastTau_gram (fun _ => True) (N₀ j)
        (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.G.Λ (.top (j + 1 + 1))) (ch.G.Λ (.grid D.R.m D.R.m)) hg0.sdV₀
        (sd_top ch _ (by omega)) hg0.sdW₀ (sd_top ch _ (by omega)) (sd_grid ch _ le_rfl)
        (fun x _ => ⟨(hs x).2.2.1.tame, LL j, LZ, (hs x).1, hLZ, (hs x).2.1, orth_cast ch (hor x) _, (hs x).2.2.2.2.1 rfl⟩)
        _ _ f₁ f₂
  · have h1 : j + 2 * ((D.R.m - 4 - j) / 2 + 1) + 2 = D.R.m := by omega
    rw [dite_eq_right h0]
    erw [dite_eq_left h1]
    have hs := hall t M hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have hs' := hall t M hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some
    have had := fun x => (hs' x).2.2.2.1 (j + 1) rfl (by omega)
    have hg0 := (hs x₀).2.2.1
    have hg1 := had x₀
    have v₁ := fock_vac ch t j (by omega) P (M := N j) (M' := N (j + 1)) hg0.sdV hg0.sdW (hbf j) (hbf (j + 1))
      (hmv t b hb j (by omega)) (hmv t b hb (j + 1) (by omega)) (hpi j) (hpi (j + 1))
    have v₂ := fock_vac ch t (j + 1) (by omega) P (M := N (j + 1)) (M' := N (j + 1 + 1)) hg0.sdW hg1.sdW (hbf (j + 1))
      (hbf (j + 1 + 1)) (hmv t b hb (j + 1) (by omega)) (hmv t b hb (j + 1 + 1) (by omega)) (hpi (j + 1)) (hpi (j + 1 + 1))
    have f₁ := hFV.1 _ (besAt ch.G hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega)) (stepAt ch.G ch.W t hM j (by omega) (besDecAt ch.G j _ h1)
      (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))) (N j) (N₀ j) (N (j + 1))
      (ch.G.Λ (.top (j + 1))) (fun x _ => (hs x).2.2.1) _ v₁
    have f₂ := hFV.2.1 _ (jacAt ch.G hM (j + 1) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besAt ch.G hM (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some) (stepAt ch.G ch.W t hM (j + 1) (by omega)
      (rowJac ch.G (j + 1) (by omega) ((D.R.m - 4 - j) / 2 + 1) (by omega))
      (besDecAt ch.G (j + 1 + 1) ((D.R.m - 4 - j) / 2) (by omega))) (N (j + 1)) (ch.G.Λ (.top (j + 1))) (N (j + 1 + 1))
      (N₀ (j + 1 + 1)) (fun x _ => had x) _ v₂
    have hCC := GlobalTheory.T.besselThetaContraction_extendByZero_vacuum_smooth D _ hψ _ _ _ _
      (linkAt hM j _ h1 (GlobalTheory.Unf.Inhab.nonempty_volN _).some (by omega) (GlobalTheory.Unf.Inhab.nonempty_volN _).some)
      (ch.G.V (.top (j + 1))) ((GlobalTheory.Unf.Inhab.nonempty_volM D _ _).some) _ _ f₁.1 f₂.1
    exact real_of hCC.1 (hCC.2.2 (fun _ => True) (ch.G.Λ (.top j)) (ch.G.Λ (.top (j + 1))) (ch.G.Λ (.top (j + 1 + 1)))
      (N₀ j) (N₀ (j + 1 + 1)) (sd_top ch _ (by omega)) hg0.sdW₀ (sd_top ch _ (by omega)) hg0.sdV₀ hg1.sdW₀
      (fun x _ => ⟨⟨_, (hs x).2.1⟩, ⟨_, (hs' x).2.1⟩⟩) f₁ f₂)

end

theorem vacReal : Big fun ch => VacReal ch := by
  refine GlobalTheory.RowReal.big_mono ?_ GlobalTheory.T.lastRowLatticesGoodPosition_large_depth
  intro D Γ _ _ Pl0 T A Ks _ _ _ R ch hsh
  exact vacReal_of_shape ch hsh

end GlobalTheory.VacRealPf
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldedVacuaAreRealDatumLargeDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unfoldedVacuaAreRealDatum_largeDepth : Big fun ch => VacReal ch := by
  first | exact @GlobalTheory.VacRealPf.vacReal | exact GlobalTheory.VacRealPf.vacReal | (intros; apply GlobalTheory.VacRealPf.vacReal <;> assumption)
end
end
