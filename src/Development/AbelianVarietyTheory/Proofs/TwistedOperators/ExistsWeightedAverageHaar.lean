module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TypePlacesDatumMoveToFullRank
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridRowLocalEqCompletedHomLattice
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaKernelAlgebraicExpansion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenCompactLevelThetaKernelSource
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomDeepPointsFixLatticeStdFirst
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomDeepPointsFixLatticeStdFirst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.StdFstFix

variable {D : D7}

theorem isHalf_actO {S T : HSp D} {e : AE D} (g : GA D S) (h : GA D T) {x : WO S T} (hx : IsHalf e x) :
    IsHalf e (actO S T g h x) := by
  have hx' : e • (x : Matrix (Fin T.rank) (Fin S.rank) (AE D)) = x := Matrix.ext fun i j => hx i j
  have e1 : e • actO S T g h x = actO S T g h x := by
    unfold actO
    conv_rhs => rw [← hx']
    rw [Matrix.mul_smul, Matrix.smul_mul]
  intro i j
  exact congrFun (congrFun e1 i) j

theorem actO_nsmul {S T : HSp D} (g : GA D S) (h : GA D T) (k : ℕ) (x : WO S T) :
    actO S T g h (k • x) = k • actO S T g h x := by
  unfold actO
  rw [Matrix.mul_smul, Matrix.smul_mul]

theorem finCong_of_mem_GinfC {V : HSp D} (N : ℕ) {k : GA D V} (hk : k ∈ GinfC V) : GlobalTheory.Member.FinCong V N k := by
  have h1 : finHom V k = finHom V 1 := by rw [map_one]; exact hk
  have := GlobalTheory.Member.PrincLevel.finCong_one V N
  unfold GlobalTheory.Member.FinCong at this ⊢
  rw [h1]
  exact this

end GlobalTheory.StdFstFix

namespace GlobalTheory.StdFstFix


set_option maxHeartbeats 2000000 in
theorem stdFst_fixed : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧ ∀ k ∈ U, k ∈ GfC A →
      (∀ u, u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔ actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k) 1 u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)) ∧
      ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β
          (actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k)⁻¹ 1⁻¹ x) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β x := by
  intro D T L sc G W i j A A' WW X hX t
  classical
  have hI := hX.is
  have hν : Continuous (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
      (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) := (hI.weil' t).hecT.1
  have he := hI.idem t
  have hinf := GlobalTheory.PlaceDatum.infPart_idemSum he
  have hsdS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := isSelfDualC_neg' hI.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hI.rigW.1
  obtain ⟨M, hM, hB⟩ := GlobalTheory.PlaceDatum.exists_den_frMapO (S := GlobalTheory.Grid.neg A) hsdS.1.fg hsdT.1.fg X.rA.β X.rW.β
  obtain ⟨K, hK, hC⟩ := GlobalTheory.PlaceDatum.exists_nsmul_of_frMapO (S := GlobalTheory.Grid.neg A)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hsdS)
    (Formalism.IndefR.Fin.PDA.selfDual_isFullLattice _ _ hsdT) X.rA.β X.rW.β
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D _ hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ X.ideal (locPl G) t :=
    ⟨_, Nat.pos_of_ne_zero fun h => GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t (Ideal.absNorm_eq_zero_iff.1 h),
      Ideal.absNorm_mem _⟩
  obtain ⟨c, hc, hcS⟩ : ∃ c : ℕ, 0 < c ∧ ∀ P ∈ locPl G t, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal := by
    refine ⟨∏ P ∈ locPl G t, Ideal.absNorm P.asIdeal, Finset.prod_pos fun P _ =>
      Nat.pos_of_ne_zero fun h => P.ne_bot (Ideal.absNorm_eq_zero_iff.1 h), fun P hP => ?_⟩
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun P : Pl D.host.E => Ideal.absNorm P.asIdeal) hP
    rw [hm, Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ (Ideal.absNorm_mem P.asIdeal)
  obtain ⟨m, hm⟩ := GlobalTheory.VacTranslate.exists_finCong_mod (GlobalTheory.Grid.neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT
    (K * (n₀ * (n * c) * M)) (Nat.mul_pos hK (Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) hM))

  have key : ∀ g ∈ GfC (GlobalTheory.Grid.neg A), GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial g → ∀ x : WO A WW,
      (IsHalf (X.e t) x ∧ IsIntM (frMapO A WW X.rA.β X.rW.β x) ∧
        ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t) (frMapO A WW X.rA.β X.rW.β x i j)) →
      GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
                   (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β
                   (actO (GlobalTheory.Grid.neg A) WW g 1 x) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) /
          (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β x := by
    intro g hg hgc x hx
    obtain ⟨l, hl', e1⟩ := hm g hg hgc (K • x) (hC x (GlobalTheory.PlaceDatum.infPart_of_half hinf hx.1) hx.2.1)
    have e2 : actO (GlobalTheory.Grid.neg A) WW g 1 x = x + (n₀ * (n * c) * M) • l := by
      have e3 : K • actO (GlobalTheory.Grid.neg A) WW g 1 x = K • (x + (n₀ * (n * c) * M) • l) := by
        rw [← actO_nsmul, e1, smul_add, smul_smul]
      rw [← GlobalTheory.PlaceModel.inv_smul_nsmul (GlobalTheory.Grid.neg A) WW hK (actO (GlobalTheory.Grid.neg A) WW g 1 x), e3,
        GlobalTheory.PlaceModel.inv_smul_nsmul (GlobalTheory.Grid.neg A) WW hK]
    refine StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.stdFst_shift he hnI hl hcS A WW X.rA.β X.rW.β
      (W := fun i j => (M : Lev.EAf D) * frMapO A WW X.rA.β X.rW.β l i j)
      ⟨fun _ => hx.1, fun _ => isHalf_actO g 1 hx.1⟩ (fun i j => hB l hl' i j) fun i j => ?_
    rw [e2, GlobalTheory.PlaceDatum.frMapO_add]
    push_cast
    ring
  refine ⟨(GlobalTheory.VacFixTarget.congGroup (GlobalTheory.Grid.neg A) m.factorial).comap (GlobalTheory.Grid.ofSgn true A).symm.toMonoidHom,
    (GlobalTheory.Grid.continuous_ofSgn_symm true A).isOpen_preimage _
      (GlobalTheory.VacFixTarget.isOpen_congGroup (GlobalTheory.Grid.neg A) m.factorial_pos), fun k hk => ?_, fun k hkU hkf => ?_⟩
  · show GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial ((GlobalTheory.Grid.ofSgn true A).symm k)
    refine finCong_of_mem_GinfC _ ?_
    rw [GlobalTheory.SgnIdent.mem_GinfC_sgn, MulEquiv.apply_symm_apply]
    exact hk
  · have hκf : (GlobalTheory.Grid.ofSgn true A).symm k ∈ GfC (GlobalTheory.Grid.neg A) := by
      rw [GlobalTheory.SgnIdent.mem_GfC_sgn, MulEquiv.apply_symm_apply]
      exact hkf
    have hκc : GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial ((GlobalTheory.Grid.ofSgn true A).symm k) := hkU
    refine ⟨fun u => ⟨fun hu => ?_, fun hu => ?_⟩, fun x => ?_⟩
    · obtain ⟨l, hl', e⟩ := hm _ hκf hκc u hu
      rw [e]
      exact add_mem hu (nsmul_mem hl' _)
    · obtain ⟨l, hl', e⟩ := hm _ (inv_mem hκf) (GlobalTheory.Member.PrincLevel.finCong_inv hκc) _ hu
      have e' := GlobalTheory.WeilVacMove.actO_inv_actO ((GlobalTheory.Grid.ofSgn true A).symm k) (1 : GA D WW) u
      rw [inv_one] at e'
      rw [e'] at e
      rw [e]
      exact add_mem hu (nsmul_mem hl' _)
    · rw [inv_one]
      set g := ((GlobalTheory.Grid.ofSgn true A).symm k)⁻¹ with hgdef
      have hg : g ∈ GfC (GlobalTheory.Grid.neg A) := inv_mem hκf
      have hgc : GlobalTheory.Member.FinCong (GlobalTheory.Grid.neg A) m.factorial g := GlobalTheory.Member.PrincLevel.finCong_inv hκc
      by_cases hx : IsHalf (X.e t) x ∧ IsIntM (frMapO A WW X.rA.β X.rW.β x) ∧
          ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t) (frMapO A WW X.rA.β X.rW.β x i j)
      · exact key g hg hgc x hx
      · by_cases hx' : IsHalf (X.e t) (actO (GlobalTheory.Grid.neg A) WW g 1 x) ∧
            IsIntM (frMapO A WW X.rA.β X.rW.β (actO (GlobalTheory.Grid.neg A) WW g 1 x)) ∧
            ∀ i j, A.rank ≤ i.1 → GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.InId (X.ideal (locPl G) t)
              (frMapO A WW X.rA.β X.rW.β (actO (GlobalTheory.Grid.neg A) WW g 1 x) i j)
        · have h2 := key g⁻¹ (inv_mem hg) (GlobalTheory.Member.PrincLevel.finCong_inv hgc) _ hx'
          have e' := GlobalTheory.WeilVacMove.actO_inv_actO g (1 : GA D WW) x
          rw [inv_one] at e'
          rw [e'] at h2
          exact h2.symm
        · unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst
          rw [if_neg hx, if_neg hx']

end GlobalTheory.StdFstFix
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DefiniteBottomDeepPointsFixLatticeStdFirstStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.definiteBottom_deepPoints_fix_lattice_stdFirst : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧ ∀ k ∈ U, k ∈ GfC A →
      (∀ u, u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔ actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k) 1 u ∈ (latO (GlobalTheory.Grid.neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True)) ∧
      ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β
          (actO (GlobalTheory.Grid.neg A) WW ((GlobalTheory.Grid.ofSgn true A).symm k)⁻¹ 1⁻¹ x) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle.stdFst (L.mu t (j + 1) * L.eta ^ (rankV D i j % 2) / (G.ch.chi (D.R.m - i) * L.eta ^ (rankV D i j % 2))) (X.e t) (X.ideal (locPl G) t) A WW X.rA.β X.rW.β x := by
  first | exact @GlobalTheory.StdFstFix.stdFst_fixed | exact GlobalTheory.StdFstFix.stdFst_fixed | (intros; apply GlobalTheory.StdFstFix.stdFst_fixed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenCompactLevelThetaKernelSource
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped Topology

noncomputable section

namespace GlobalTheory.SrcLevel

theorem ker_finE {D : D7} (V : HSp D) {k : GA D V} (hk : Lev.finE V k = 1) : k ∈ GinfC V := by
  show finHom V k = 1
  have hinj : Function.Injective (Lev.swapAE D) :=
    (Algebra.TensorProduct.comm D.host.F (Af D.host.F) D.host.E).injective
  have h1 : Formalism.UG.bc (Lev.swapAE D) (finHom V k) = 1 := hk
  apply Units.ext
  have h2 := congrArg Units.val h1
  change Matrix.map (finHom V k).val (Lev.swapAE D) = 1 at h2
  refine Matrix.map_injective hinj ?_
  beta_reduce
  rw [h2, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem level_of_open {D : D7} (V : HSp D) (U : Subgroup (GA D V)) (hUo : IsOpen (U : Set (GA D V)))
    (hinf : GinfC V ≤ U) :
    ∃ K : Subgroup (GL (Fin V.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel V K ∧ ∀ k ∈ Lev.levA V K, k ∈ U := by
  obtain ⟨ho, hc⟩ := GlobalTheory.FunObj.congLev_open_compact V (GlobalTheory.AdelicU.SelfDual.isLattice_frameLat V) (𝔪 := ⊤) top_ne_bot
  set K₀ := congLev D.sp.cm V.gram (GlobalTheory.AdelicU.frameLat V) ⊤ with hK₀
  have hmem : ∀ k ∈ Lev.levA V (K₀ ⊓ U.map (Lev.finE V)), k ∈ U := by
    intro k hk
    obtain ⟨-, hkK⟩ := Lev.mem_levA.1 hk
    obtain ⟨k', hk'U, e⟩ := Subgroup.mem_map.1 hkK.2
    have h1 : k'⁻¹ * k ∈ GinfC V := ker_finE V (by rw [map_mul, map_inv, e, inv_mul_cancel])
    have h2 := U.mul_mem hk'U (hinf h1)
    rwa [mul_inv_cancel_left] at h2
  have hopen : IsOpen (((K₀ ⊓ U.map (Lev.finE V)).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := by
    rw [Subgroup.comap_inf, Subgroup.coe_inf]
    exact ho.inter (Subgroup.isOpen_mono (Subgroup.le_comap_map _ _) hUo)
  refine ⟨K₀ ⊓ U.map (Lev.finE V), ⟨hopen, ?_⟩, hmem⟩
  have hcl : IsClosed ((Lev.levA V (K₀ ⊓ U.map (Lev.finE V)) : Subgroup (GA D V)) : Set (GA D V)) := by
    have e : ((Lev.levA V (K₀ ⊓ U.map (Lev.finE V)) : Subgroup (GA D V)) : Set (GA D V)) =
        (GfC V : Set (GA D V)) ∩ (((K₀ ⊓ U.map (Lev.finE V)).comap (Lev.finE V) : Subgroup (GA D V)) : Set (GA D V)) := rfl
    rw [e]
    exact (GlobalTheory.Ker.CongTop.isClosed_GfC V).inter (Subgroup.isClosed_of_isOpen _ hopen)
  refine hc.of_isClosed_subset hcl fun k hk => ?_
  obtain ⟨h1, h2⟩ := Lev.mem_levA.1 hk
  exact Lev.mem_levA.2 ⟨h1, h2.1⟩

theorem dat_fix : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D A), IsOpen (U : Set (GA D A)) ∧ GinfC A ≤ U ∧
      ∀ k ∈ U, k ∈ GfC A → X.ω t (k, 1) X.vac = X.vac → X.ω t (k, 1) (X.f t) = X.f t := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U, hUo, hUinf, hU⟩ := GlobalTheory.T.definiteBottom_deepPoints_fix_lattice_stdFirst hX t
  refine ⟨U, hUo, hUinf, fun k hkU hkf hv => ?_⟩
  obtain ⟨hΛ, hΦ⟩ := hU k hkU hkf
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
  have e1 : ∀ F, (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm k, 1) F = X.ω t (k, 1) F := by
    intro F
    simp [GlobalTheory.Grid.WRep.toSgn]
  have hsdS : IsSelfDualC (GlobalTheory.Grid.neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hmv := GlobalTheory.TypeMove.isThetaAt_move hW hsdS hsdT (GlobalTheory.PlaceDatum.idemSum_mul_self (hX.is.idem t))
    (GlobalTheory.PlaceDatum.infPart_idemSum (hX.is.idem t)) hΛ hX.is.isVac.2.theta (by rw [e1]; exact hv) (hX.is.fst t)
  have hf := hX.is.fst t
  obtain ⟨⟨T₀, hT₀⟩, hall⟩ := hmv
  obtain ⟨-, hall'⟩ := hf
  rw [← e1, hall T₀ hT₀, hall' T₀ hT₀]
  congr 1
  funext x
  exact hΦ x

theorem exists_level_ker : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ K : Subgroup (GL (Fin A.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A K ∧
      ∀ (P : PolF D WW.rank A.rank) (h : GA D WW), ∀ k ∈ Lev.levA A K, ∀ g,
        X.ker W.ψ W.θ t P h (g * k) = X.ker W.ψ W.θ t P h g := by
  intro D T L sc G W i j A A' WW X hX t
  obtain ⟨U₁, hU₁o, hU₁inf, hU₁⟩ := GlobalTheory.T.exists_open_fixing_negative_vacuum_definite_bottom hX t
  obtain ⟨U₂, hU₂o, hU₂inf, hU₂⟩ := dat_fix hX t
  obtain ⟨K, hK, hKU⟩ := level_of_open A (U₁ ⊓ U₂) (hU₁o.inter hU₂o) (le_inf hU₁inf hU₂inf)
  refine ⟨K, hK, fun P h k hk g => ?_⟩
  have hkf : k ∈ GfC A := (Lev.mem_levA.1 hk).1
  have hkU := hKU k hk
  have hv := hU₁ k hkU.1 hkf
  have hf := hU₂ k hkU.2 hkf hv
  have hW : IsWeilDatumO W.ψ (GlobalTheory.Grid.neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
  have hθ := hX.is.isVac.2.inf
  have hft : IsThetaFunO W.ψ (GlobalTheory.Grid.neg A) WW (X.f t) :=
    GlobalTheory.JointHarm.isThetaFunO_of_isThetaAt hX.is.isVac.1 hθ (hX.is.fst t) hX.is.isVac.2.theta
  have hκ : (GlobalTheory.Grid.ofSgn true A).symm k ∈ GfC (GlobalTheory.Grid.neg A) :=
    (GlobalTheory.SgnIdent.mem_GfC_sgn true A _).2 (by rw [MulEquiv.apply_symm_apply]; exact hkf)
  have e1 : ∀ F, (X.ω t).toSgn true ((GlobalTheory.Grid.ofSgn true A).symm k, 1) F = X.ω t (k, 1) F := by
    intro F
    simp [GlobalTheory.Grid.WRep.toSgn]
  have key : X.ω t (k, 1) (pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) =
      pureTensorO W.ψ W.θ (GlobalTheory.Grid.neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P := by
    rw [← e1, GlobalTheory.OrientedHeis.om_fin_pureTensorO _ _ _ _ _ _ hW _ hθ _ hκ 1 (one_mem _) _ _ _ _ _ P hft, e1, hf]
  show X.ω t (g * k, h) _ 0 = X.ω t (g, h) _ 0
  have e : ((g * k, h) : GA D A × GA D WW) = (g, h) * (k, 1) := by simp
  rw [e, map_mul, Module.End.mul_apply, key]

end GlobalTheory.SrcLevel

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenCompactLevelThetaKernelSourceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_openCompactLevel_thetaKernel_source : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ K : Subgroup (GL (Fin A.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A K ∧
      ∀ (P : PolF D WW.rank A.rank) (h : GA D WW), ∀ k ∈ Lev.levA A K, ∀ g,
        X.ker W.ψ W.θ t P h (g * k) = X.ker W.ψ W.θ t P h g := by
  first | exact @GlobalTheory.SrcLevel.exists_level_ker | exact GlobalTheory.SrcLevel.exists_level_ker | (intros; apply GlobalTheory.SrcLevel.exists_level_ker <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section
open scoped ComplexOrder
open GlobalTheory.ClassRegroup GlobalTheory.DefiniteClassAvg GlobalTheory.DefiniteClassReal
open GlobalTheory.Grid (neg sgn ofSgn)

namespace GlobalTheory.RowTest.BottomClassSumNeg

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem theta (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A.rank) :
    IsThetaFunO W.ψ (neg A) WW (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) :=
  GlobalTheory.Chain.InnerSteps.theta_pureTensorO (S := neg A) (T := WW) hX.is.isVac.1 hX.is.isVac.2.inf (fun τ => -X.rA.s τ) X.rA.B X.rW.s X.rW.B
    (GlobalTheory.ConstRatio.theta_f hX.is t).1 P

theorem ker_eq (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) (g : GA D A) :
    X.ker W.ψ W.θ t P h g = thetaKO ((X.ω t).toSgn true) ((ofSgn true A).symm g) h
      (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) P) := by
  show thetaKO (X.ω t) g h _ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm g), h) _ 0
  rw [MulEquiv.apply_symm_apply]
  rfl

theorem ker_left (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) :
    ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t P h (γ * g) = X.ker W.ψ W.θ t P h g := by
  intro γ hγ g
  have hK := GlobalTheory.thetaKO_rat_left_and_eigen_right W.ψ (neg A) WW _ _ _ (hX.is.weil t) _ (theta hX t P)
  rw [ker_eq, ker_eq, map_mul]
  have := hK.1 _ ((GlobalTheory.SgnIdent.mem_GQ_sgn true A _).2 (by rwa [MulEquiv.apply_symm_apply])) 1 (one_mem _)
    ((ofSgn true A).symm g) h
  rwa [one_mul] at this

theorem ker_cont (hX : IsBottomTri W i j X) (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW) (x : GA D A) :
    Continuous fun k : GinfC A => X.ker W.ψ W.θ t P h (x * k) := by
  have hW := hX.is.weil t
  have hF := theta hX t P
  simp_rw [ker_eq]
  exact (hW.om_cont _ hF 0).comp (((GlobalTheory.Grid.continuous_ofSgn_symm true A).comp
    (continuous_const.mul continuous_subtype_val)).prodMk continuous_const)

end GlobalTheory.RowTest.BottomClassSumNeg

namespace GlobalTheory.RowTest.BottomClassSumNeg

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {i j : Fin D.R.m}
    {A A' WW : HSp D} {X : Tri T A A' WW}

theorem level_all [Finite T] (t₀ : T) (hX : IsBottomTri W i j X) :
    ∃ K : Subgroup (GL (Fin A.rank) (Lev.EAf D)), GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral.IsOpenCompactLevel A K ∧
      ∀ (t : T) (P : PolF D WW.rank A.rank) (h : GA D WW), ∀ k ∈ Lev.levA A K, ∀ g,
        X.ker W.ψ W.θ t P h (g * k) = X.ker W.ψ W.θ t P h g := by
  choose K hK hinv using GlobalTheory.T.exists_openCompactLevel_thetaKernel_source hX
  refine ⟨⨅ t, K t, ⟨?_, ?_⟩, fun t P h k hk g => hinv t P h k ?_ g⟩
  · have e : (((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) =
        ⋂ t, (((K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) := by
      ext x; simp [Subgroup.mem_iInf]
    rw [e]
    exact isOpen_iInter_of_finite fun t => (hK t).1
  · have hcl : IsClosed ((((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A))) := by
      have e : (((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) =
          ⋂ t, (((K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) := by
        ext x; simp [Subgroup.mem_iInf]
      rw [e]
      exact isClosed_iInter fun t => Subgroup.isClosed_of_isOpen _ (hK t).1
    have e2 : ((Lev.levA A (⨅ t, K t) : Subgroup (GA D A)) : Set (GA D A)) =
        (Lev.levA A (K t₀) : Set (GA D A)) ∩ (((⨅ t, K t).comap (Lev.finE A) : Subgroup (GA D A)) : Set (GA D A)) := by
      ext x
      simp only [SetLike.mem_coe, Set.mem_inter_iff, Lev.mem_levA, Subgroup.mem_comap]
      exact ⟨fun ⟨h1, h2⟩ => ⟨⟨h1, (Subgroup.mem_iInf.1 h2) t₀⟩, h2⟩, fun ⟨⟨h1, _⟩, h2⟩ => ⟨h1, h2⟩⟩
    rw [e2]
    exact (hK t₀).2.inter_right hcl
  · obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact Lev.mem_levA.2 ⟨hk1, (Subgroup.mem_iInf.1 hk2) t⟩

end GlobalTheory.RowTest.BottomClassSumNeg

end
