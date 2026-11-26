module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VecOfEqIntertwiner
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumOKEx
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteHeisenbergTranslateSelfDualVacuumFockJets

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GivenLevelInner
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.LastVertexInv GlobalTheory.LastVertexMove
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LastRowLat

open GlobalTheory.FinPl (Moves Lat)
open Matrix

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}


variable (G) in
theorem givenLevel_inner (t : T) (w : Pl D.host.E) : ∀ X : ℕ × ℕ, 1 ≤ X.1 → 1 ≤ X.2 →
    givenLevel G t w X = GlobalTheory.SplitWeil.KO (Kw w) _
  | (_ + 1, _ + 1), _, _ => rfl
  | (0, _), h, _ => absurd h (by omega)
  | (_ + 1, 0), _, h => absurd h (by omega)

theorem inBasis_KO {n n' : ℕ} (h : n' = n) (β x : GL (Fin n) (Lev.EAf D)) (w : Pl D.host.E)
    (K : Subgroup (GL (Fin n') (Kw w))) (hK : K = GlobalTheory.SplitWeil.KO (Kw w) (Fin n')) (hx : inBasis h β w x ∈ K) :
    inBasis rfl β w x ∈ GlobalTheory.SplitWeil.KO (Kw w) (Fin n) := by
  subst h; subst hK; exact hx

theorem isFrame_grid (S : GridChoice W U) : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsFrame (S.B.β i D.R.m) (G.Λ (.grid i D.R.m))
  | 0, h, _ => absurd h (by omega)
  | i + 1, _, hi => S.B.isFrame (i + 1) D.R.m (by omega) hi le_rfl

theorem isSelfDual_grid : ∀ {i : ℕ}, 1 ≤ i → i ≤ D.R.m → IsSelfDualC (G.V (.grid i D.R.m)) (G.Λ (.grid i D.R.m))
  | 0, h, _ => absurd h (by omega)
  | i + 1, _, hi => (G.sp.V_is (i + 1) D.R.m (by omega) hi le_rfl).sd

theorem levRow_mem_St (S : GridChoice W U) (t : T) (k : FinPt G (.grid D.R.m D.R.m))
    (hk : finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl) :
    finG (G.V (.grid D.R.m D.R.m)) k ∈ St (S.B.β D.R.m D.R.m) := by
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hfr := isFrame_grid S hm le_rfl
  have hsd := isSelfDual_grid (G := G) hm le_rfl
  have hU : finG (G.V (.grid D.R.m D.R.m)) k ∈ UA D.sp.cm (G.V (.grid D.R.m D.R.m)).gram := GlobalTheory.LevSplit.finE_mem_UA _ _
  obtain ⟨h1, h2⟩ := Subgroup.mem_inf.1 hk
  have hP : ∀ w0 ∈ locPl G t, inBasis rfl (S.B.β D.R.m D.R.m) w0 (finG (G.V (.grid D.R.m D.R.m)) k) ∈ GlobalTheory.SplitWeil.KO (Kw w0) _ := fun w0 hw0 =>
    inBasis_KO _ _ _ _ _ (givenLevel_inner G t w0 (D.R.m, D.R.m) hm hm) (Subgroup.mem_iInf.1 h1 ⟨w0, hw0⟩)
  refine GlobalTheory.Adopt.mem_latticeStabilizer_of_local_integral_inBasis _ _ fun w => ?_
  by_cases hw : ∃ w0 ∈ locPl G t, w.under (𝓞 D.host.F) = w0.under (𝓞 D.host.F)
  · obtain ⟨w0, hw0, e⟩ := hw
    rcases GlobalTheory.GoodPrimes.eq_or_conj_of_under_eq e with rfl | rfl
    · exact hP w hw0
    · exact GlobalTheory.T.unitaryInBasis_integral_at_conjugatePlace _ _ _ hfr (GlobalTheory.AdIsom.dualL_eq hsd) _ hU w0 (hP w0 hw0)
  · push_neg at hw
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h2 w) hw

theorem hat_stab_of_St {n : ℕ} (Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (β M : GL (Fin n) (Lev.EAf D))
    (hβ : IsFrame β Λ) (hM : M ∈ St β) (z : Fin n → Lev.EAf D) :
    z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ M.val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := by
  refine ⟨GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β M hβ hM z, fun h => ?_⟩
  have e : (M⁻¹).val *ᵥ (M.val *ᵥ z) = z := by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  rw [← e]
  exact GlobalTheory.LatStab.mulVec_mem_of_mem_St Λ β M⁻¹ hβ (inv_mem hM) _ h

theorem hat_stab_conj (V : HSp D) (u k : GA D V) (Λ M : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hu : ∀ v, v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔ (Lev.finE V u).val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (hk : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V k).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ)
    (v : Fin V.rank → Lev.EAf D) :
    v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M ↔
      (Lev.finE V (u⁻¹ * k * u)).val *ᵥ v ∈ Formalism.L2.Herm.hatL (F := D.host.F) M := by
  have e : (Lev.finE V u).val *ᵥ ((Lev.finE V (u⁻¹ * k * u)).val *ᵥ v) =
      (Lev.finE V k).val *ᵥ ((Lev.finE V u).val *ᵥ v) := by
    rw [map_mul, map_mul, map_inv, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Units.val_mul, ← Units.val_mul]
    congr 2
    group
  refine (hu v).trans ((hk _).trans ?_)
  rw [← e]
  exact (hu _).symm

theorem moves_of_hat (V : HSp D) (g : GA D V) (Λ : Lat V)
    (h : ∀ z, z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔ (Lev.finE V g).val *ᵥ z ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ) :
    Moves V g Λ Λ (fun _ => True) := by
  intro y hy
  have hy' : ∀ i, (Formalism.L2.Theta.mt V g *ᵥ y) i ∈ GlobalTheory.FinPl.idAt D (fun _ => True) :=
    GlobalTheory.Core.Mi.FrameMove.mulVec_mem_ideal _ hy
  constructor
  · intro h1
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy' ?_
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat]
    exact (h _).1 (GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ y h1)
  · intro h1
    refine GlobalTheory.HatLatV.mem_latV_of_hatL D V Λ _ _ hy ?_
    have h2 := GlobalTheory.LatVHat.latV_mem_hatL D V Λ _ _ h1
    rw [GlobalTheory.Core.Mi.FrameMove.finE_mulVec_hat] at h2
    exact (h _).2 h2

theorem moves_neg (V : HSp D) (g : GA D V) (Λ : Lat V) {P : GlobalTheory.FinPl.Pl D → Prop} (h : Moves V g Λ Λ P) :
    Moves (negSp V) (negGA V g) Λ Λ P := h

theorem moves_cast (S : GridChoice W U) : ∀ (i : ℕ) (e : D.R.m = i) (g : FinPt G (.grid D.R.m D.R.m)),
    Moves (G.V (.grid D.R.m D.R.m)) g.1 (colLat (S.N.fr (.grid D.R.m D.R.m))) (colLat (S.N.fr (.grid D.R.m D.R.m)))
      (fun _ => True) →
    Moves (G.V (.grid i D.R.m)) (e ▸ g : FinPt G (.grid i D.R.m)).1 (colLat (S.N.fr (.grid i D.R.m)))
      (colLat (S.N.fr (.grid i D.R.m))) (fun _ => True) := by
  rintro i rfl g h
  exact h

end GlobalTheory.LastRowLat

namespace GlobalTheory.LastRowLat

open GlobalTheory.FinPl (Moves Lat)
open Matrix

theorem rowPt_mem_stdLat : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T} (S : GridChoice W U) {t : T}, t ∈ U → ∀ k : FinPt G (.grid D.R.m D.R.m),
    finG (G.V (.grid D.R.m D.R.m)) k ∈ S.levRow t D.R.m le_rfl →
    ∀ x : WO (G.pS (.chi (lastIx D) D.R.m : Pair T)) (G.pT (.chi (lastIx D) D.R.m : Pair T)),
    actO _ _ (rowPt S k).1⁻¹ (rowPt S k).2⁻¹ x ∈ stdLat S (.chi (lastIx D) D.R.m) ↔ x ∈ stdLat S (.chi (lastIx D) D.R.m) := by
  intro D T L sc G W U S t _ k hk x
  have hm : 1 ≤ D.R.m := by have := D.R.two_le_m; omega
  have hX : DefNode D.R.m (.grid D.R.m D.R.m) := ⟨le_rfl, rfl⟩
  have hk' := hat_stab_of_St _ _ _ (isFrame_grid S hm le_rfl) (levRow_mem_St S t k hk)
  have hg := hat_stab_conj (G.V (.grid D.R.m D.R.m)) (S.N.u (.grid D.R.m D.R.m)).1 k.1 _ _
    (S.N.u_lat _ hX) hk'
  have mv : Moves (G.V (.grid D.R.m D.R.m)) ((S.N.u (.grid D.R.m D.R.m))⁻¹ * k * S.N.u (.grid D.R.m D.R.m)).1
      (colLat (S.N.fr (.grid D.R.m D.R.m))) (colLat (S.N.fr (.grid D.R.m D.R.m))) (fun _ => True) :=
    moves_of_hat _ _ _ hg
  have mv2 := moves_cast S _ (lastIx_succ D) _ mv
  have mvS : Moves (G.pS (.chi (lastIx D) D.R.m : Pair T)) (rowPt S k).1⁻¹ (S.N.latS (.chi (lastIx D) D.R.m))
      (S.N.latS (.chi (lastIx D) D.R.m)) (fun _ => True) :=
    GlobalTheory.VacMove.moves_inv (moves_neg _ _ _ mv2)
  have mvT : Moves (G.pT (.chi (lastIx D) D.R.m : Pair T)) (rowPt S k).2⁻¹ (S.N.latT (.chi (lastIx D) D.R.m))
      (S.N.latT (.chi (lastIx D) D.R.m)) (fun _ => True) := by
    have e2 : (rowPt S k).2 = 1 := rfl
    rw [e2, inv_one]
    intro y _
    rw [GlobalTheory.VacMove.mt_one₀, Matrix.one_mulVec]
  have hl := (lastIx D).2
  have sdS : IsSelfDualC (G.pS (.chi (lastIx D) D.R.m : Pair T)) (S.N.latS (.chi (lastIx D) D.R.m)) :=
    isSelfDualC_neg (OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ ⟨by omega, rfl⟩))
  have sdT : IsSelfDualC (G.pT (.chi (lastIx D) D.R.m : Pair T)) (S.N.latT (.chi (lastIx D) D.R.m)) :=
    OrthoFrame.isSelfDualC_colLat_of_orthonormal _ _ (S.N.fr_on _ ⟨by omega, rfl⟩)
  exact (GlobalTheory.VacMove.mem_latO_iff_actO sdS sdS sdT sdT mvS mvT x).symm

end GlobalTheory.LastRowLat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingSeesawVacuumDefiniteBottom
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingSeesawVacuumDefiniteBottom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open scoped Topology

noncomputable section

namespace GlobalTheory.VacFixTarget

theorem om_pow_eq_snd {D : D7} {S V : HSp D} (om : GA D S × GA D V →* Module.End ℂ (WO S V → ℂ)) (k : GA D V)
    (f : WO S V → ℂ) (c : ℂ) (hc : om (1, k) f = c • f) : ∀ m : ℕ, om (1, k ^ m) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, Prod.mk_one_one, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    have e : (((1 : GA D S), k ^ (m + 1)) : GA D S × GA D V) = (1, k ^ m) * (1, k) := by
      rw [pow_succ, Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]

def congGroup {D : D7} (V : HSp D) (N : ℕ) : Subgroup (GA D V) where
  carrier := {k | GlobalTheory.Member.FinCong V N k}
  one_mem' := GlobalTheory.Member.PrincLevel.finCong_one V N
  mul_mem' := fun ha hb => GlobalTheory.Member.PrincLevel.finCong_mul ha hb
  inv_mem' := fun ha => GlobalTheory.Member.PrincLevel.finCong_inv ha

theorem isOpen_congGroup {D : D7} (V : HSp D) {N : ℕ} (hN : 0 < N) : IsOpen (congGroup V N : Set (GA D V)) :=
  Subgroup.isOpen_of_mem_nhds _ (g := 1) (GlobalTheory.Member.PrincLevel.finCong_mem_nhds V hN)

end GlobalTheory.VacFixTarget

namespace GlobalTheory.VacFixTarget

open _root_.Formalism.L2.Fam.ThC (fixSig)

theorem isThetaFunO_fixSig {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {f : WO S T → ℂ}
    (h : IsThetaFunO ψ S T f) : IsThetaFunO ψ (fixSig S) (fixSig T) f :=
  ⟨h.quasi, h.level, h.cont, h.smooth⟩

theorem isVacO_fixSig {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (h : IsVacO ψ θ S T sS sT LS LT f) : IsVacO ψ θ (fixSig S) (fixSig T) sS sT LS LT f :=
  ⟨h.1, h.2.inf, isThetaFunO_fixSig h.2.theta, h.2.lat, h.2.fock, h.2.norm⟩

end GlobalTheory.VacFixTarget

namespace GlobalTheory.VacFixTarget

open GlobalTheory.Grid (neg)


set_option maxHeartbeats 1000000 in
theorem exists_open_fix_vac_target : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac := by
  intro D T L sc G W i j A A' WW X hX t
  have hW : IsWeilDatumO W.ψ (neg A) WW _ _ ((X.ω t).toSgn true) := hX.is.weil t
  have hvac : IsVacO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.Λ X.rW.Λ X.vac := hX.is.isVac
  have hθ : IsInfFam W.θ := hvac.2.inf
  have hsdS : IsSelfDualC (neg A) X.rA.Λ := GlobalTheory.RowTest.isSelfDualC_neg' hX.is.rigA.1
  have hsdT : IsSelfDualC WW X.rW.Λ := hX.is.rigW.1
  have hcS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ =>
    GlobalTheory.Grid.isCartanInv_sgn true A τ (hX.is.rigA.2.2 τ).1
  have hcT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hX.is.rigW.2.2 τ).1
  have hone : ∀ κ : GA D WW, (X.ω t).toSgn true (1, κ) = X.ω t (1, κ) := fun κ => by
    simp [GlobalTheory.Grid.WRep.toSgn]
  have hev := (GlobalTheory.LatNhds.eventually_actO D (neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT
    (GlobalTheory.LatFinGen.latO_finitely_generated D (neg A) WW X.rA.Λ X.rW.Λ hsdS hsdT)).1
  have hpair : Filter.Tendsto (fun x : GA D WW => (((1 : GA D (neg A)), x) : GA D (neg A) × GA D WW)) (𝓝 1) (𝓝 1) := by
    have := ((continuous_const.prodMk continuous_id :
      Continuous fun x : GA D WW => (((1 : GA D (neg A)), x) : GA D (neg A) × GA D WW))).tendsto 1
    exact this
  have hev' := hpair.eventually hev
  obtain ⟨n₁, hn₁⟩ : ∃ n : ℕ, ∀ x ∈ GfC WW, GlobalTheory.Member.FinCong WW n.factorial x →
      ∀ u ∈ (latO (neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True),
        actO (neg A) WW 1 x u ∈
          (latO (neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) := by
    by_contra hne
    push_neg at hne
    choose k hk hkc u hu hu' using hne
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong hk hkc
    obtain ⟨n, hn⟩ := (ht.eventually hev').exists
    exact hu' n (hn _ (hu n))
  have hscal : ∀ k ∈ GfC WW, GlobalTheory.Member.FinCong WW n₁.factorial k →
      ∃ c : ℂ, ‖c‖ = 1 ∧ (X.ω t).toSgn true (1, k) X.vac = c • X.vac := by
    intro k hk hc
    have hΛ : ∀ u : WO (neg A) WW, u ∈ (latO (neg A) WW (X.rA.Λ : Set (Fin A.rank → D.host.E))
        (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True) ↔ ∃ u₀ ∈ (latO (neg A) WW
        (X.rA.Λ : Set (Fin A.rank → D.host.E)) (X.rW.Λ : Set (Fin WW.rank → D.host.E)) fun _ => True),
        u = actO (neg A) WW 1 k u₀ := by
      intro u
      constructor
      · intro hu
        refine ⟨actO (neg A) WW 1 k⁻¹ u, hn₁ k⁻¹ (inv_mem hk) (GlobalTheory.Member.PrincLevel.finCong_inv hc) u hu, ?_⟩
        have := GlobalTheory.WeilVacMove.actO_inv_actO (1 : GA D (neg A)) k⁻¹ u
        rw [inv_inv, inv_one] at this
        exact this.symm
      · rintro ⟨u₀, hu₀, rfl⟩
        exact hn₁ k hk hc u₀ hu₀
    have hvac' := GlobalTheory.WeilVacMove.isVacO_om D W.ψ W.θ (neg A) WW _ _ ((X.ω t).toSgn true) hW hθ
      (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ) X.rW.s X.rW.s _ _ _ _ 1 k
      (fun τ => GlobalTheory.SmoothVac.comm_compAt_one (neg A) W.θ τ (-X.rA.s τ))
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC W.θ WW hk τ, Matrix.one_mul, Matrix.mul_one]) hΛ X.vac hvac
    exact GlobalTheory.VacUnique.vacUniqueO D W.ψ W.θ hvac.1 hθ (Formalism.L2.Fam.ThC.fixSig (neg A)) (Formalism.L2.Fam.ThC.fixSig WW)
      (fun τ => -X.rA.s τ) X.rW.s (Formalism.L2.Fam.ThC.fixSig_ok _) (Formalism.L2.Fam.ThC.fixSig_ok _) hcS hcT X.rA.Λ X.rW.Λ
      hsdS hsdT X.vac _ (isVacO_fixSig hvac) (isVacO_fixSig hvac')
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hvac
  have hcont : Continuous fun k : GA D WW => (X.ω t).toSgn true (1, k) X.vac w₀ :=
    (hW.om_cont _ hvac.2.theta w₀).comp (continuous_const.prodMk continuous_id)
  have key : ∃ n : ℕ, ∀ k ∈ GfC WW, GlobalTheory.Member.FinCong WW (n₁.factorial * n.factorial) k →
      (X.ω t).toSgn true (1, k) X.vac = X.vac := by
    by_contra hne
    push_neg at hne
    choose k hk hkc hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, (X.ω t).toSgn true (1, k n ^ m) X.vac = c • X.vac ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, -, hc⟩ := hscal (k n) (hk n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      push_neg at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (om_pow_eq_snd _ (k n) _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup WW (n₁.factorial * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup WW (n₁.factorial * n.factorial) from ⟨hk n, hkc n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have h2 := (hcont.tendsto 1).comp ht
    have e1 : (X.ω t).toSgn true ((1 : GA D (neg A)), (1 : GA D WW)) X.vac w₀ = X.vac w₀ := by
      show (X.ω t).toSgn true 1 X.vac w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖X.vac w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    rw [hmc n, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := hc n
    push_neg at this
    nlinarith [norm_nonneg (X.vac w₀)]
  obtain ⟨n, hn⟩ := key
  refine ⟨congGroup WW (n₁.factorial * n.factorial),
    isOpen_congGroup WW (Nat.mul_pos n₁.factorial_pos n.factorial_pos), fun κ hU hκ => ?_⟩
  rw [← hone]
  exact hn κ hκ hU

end GlobalTheory.VacFixTarget
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpenFixingSeesawVacuumDefiniteBottomStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_open_fixing_seesaw_vacuum_definite_bottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X → ∀ t : T,
    ∃ U : Subgroup (GA D WW), IsOpen (U : Set (GA D WW)) ∧ ∀ κ ∈ U, κ ∈ GfC WW → X.ω t (1, κ) X.vac = X.vac := by
  first | exact @GlobalTheory.VacFixTarget.exists_open_fix_vac_target | exact GlobalTheory.VacFixTarget.exists_open_fix_vac_target | (intros; apply GlobalTheory.VacFixTarget.exists_open_fix_vac_target <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomTriangleMonomialSupportFinite
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

open scoped ComplexOrder

namespace GlobalTheory.BottomDeg

open GlobalTheory.Grid (neg sgn ofSgn)

variable {D : D7}


open Classical in
theorem pureTensorO_scal_pm {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ)
    {S T : HSp D} (sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (BS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ) (BT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hs : ∀ τ, sS τ = 1 ∨ sS τ = -1) (ht : ∀ τ, sT τ = 1 ∨ sT τ = -1)
    (f : WO S T → ℂ) (hf : IsThetaFunO ψ S T f) (ζ : D.what₂.Tau → ℂ) (hζ : ∀ τ, ‖ζ τ‖ = 1)
    (α : FVar D T.rank S.rank →₀ ℕ) :
    pureTensorO ψ θ S T sS sT (fun τ => ζ τ • BS τ) BT f (MvPolynomial.monomial α 1) =
      (∏ τ, (if (sS τ = 1 ↔ sT τ = 1) then (ζ τ)⁻¹ else ζ τ) ^ (∑ v ∈ α.support with v.1 = τ, α v)) •
        pureTensorO ψ θ S T sS sT BS BT f (MvPolynomial.monomial α 1) := by
  have hz : ∀ τ, ζ τ ≠ 0 := fun τ h => by simpa [h] using hζ τ
  let μ : D.what₂.Tau → ℂ := fun τ => if (sS τ = 1 ↔ sT τ = 1) then (ζ τ)⁻¹ else ζ τ
  have key : ∀ (i : FVar D T.rank S.rank) g, IsThetaFunO ψ S T g →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) (fun τ => ζ τ • BS τ) BT i g =
      μ i.1 • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i g := by
    rintro ⟨ρ, a, j⟩ g hg
    simp only [aPlusAll, μ]
    rw [GlobalTheory.FockScal.unitMap_smul _ _ (hz ρ),
      GlobalTheory.FockSubst.aPlus_dir_smul hψ hθ ρ _ _ hg _ _ (GlobalTheory.FockScal.cplxO_pm (hs ρ) (ht ρ) a j _)]
    congr 1
    rw [map_inv₀, ← Complex.inv_eq_conj (hζ ρ), inv_inv]
    simp only [decide_eq_true_eq]
  have hA : ∀ i f, IsThetaFunO ψ S T f →
      IsThetaFunO ψ S T (aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i f) :=
    fun _ _ h => GlobalTheory.FockSubst.aPlus_th hψ hθ _ _ _ h
  have Asm : ∀ i (a : ℂ) f, IsThetaFunO ψ S T f →
      aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i (a • f) =
      a • aPlusAll (heisO ψ S T) θ (fun τ => cplxO (sS τ) (sT τ)) BS BT i f :=
    fun _ a _ h => GlobalTheory.FockSubst.aPlus_smul hψ hθ _ _ _ a h
  unfold pureTensorO
  exact GlobalTheory.FockScal.pure_scal (P := IsThetaFunO ψ S T) (fun v : FVar D T.rank S.rank => v.1) μ
    (fun a _ => GlobalTheory.OrientedHeis.theta_smul a) hA Asm key hf α


open Classical in
theorem scalar_exists {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW} (hX : IsBottomTri W i j X) (t : T) (τ₀ : D.what₂.Tau) :
    ∃ C w : ℂ, (w = Complex.exp Complex.I ∨ w = (Complex.exp Complex.I)⁻¹) ∧
      ∀ (k : FVar D WW.rank A.rank →₀ ℕ) (h : GA D WW),
        X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h =
          (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) * X.I W.ψ W.θ t (MvPolynomial.monomial k 1) h := by
  classical
  have hI := hX.is
  have hθ : IsInfFam W.θ := hI.isVac.2.inf
  have hψ : IsStdChar D W.ψ (-1) := hI.isVac.1
  set om' := (X.ω t).toSgn true with hom'
  have hom := hI.weil t
  have hsA : ∀ τ, X.rA.s τ = 1 := fun τ => (hX.std.2.2 τ).1
  have hsW : ∀ τ, X.rW.s τ = 1 := fun τ => (hX.stdW.2.2 τ).1
  have he : ‖Complex.exp Complex.I‖ = 1 := by simpa using Complex.norm_exp_ofReal_mul_I 1
  obtain ⟨z', hz', -, h1, h2⟩ := GlobalTheory.CentralUnit.exists_central_of_norm_one D W.θ hθ (neg A) τ₀ (Complex.exp Complex.I) he
  set ζ : D.what₂.Tau → ℂ := fun τ => if τ = τ₀ then Complex.exp Complex.I else 1 with hζdef
  have hζ : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt (neg A) z') = ζ τ • (1 : Matrix (Fin (neg A).rank) (Fin (neg A).rank) ℂ) := by
    intro τ
    by_cases hτ : τ = τ₀
    · subst hτ
      simp only [hζdef, if_pos rfl, h1]
    · simp only [hζdef, if_neg hτ, h2 τ hτ, one_smul]
  have hζn : ∀ τ, ‖ζ τ‖ = 1 := fun τ => by
    by_cases hτ : τ = τ₀
    · simp only [hζdef, if_pos hτ, he]
    · simp only [hζdef, if_neg hτ, norm_one]
  have hf : IsThetaFunO W.ψ (neg A) WW (X.f t) := (GlobalTheory.ConstRatio.theta_f hI t).1
  have ho := GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum (hI.idem t)
  have hfock : ∀ τ, IsFockVacAt (heisO W.ψ (neg A) WW) W.θ τ (cplxO (-X.rA.s τ) (X.rW.s τ)) (X.f t) := fun τ =>
    GlobalTheory.DatumFock.isFockVacAt_of_isThetaAt hψ.1.1 hθ ho.infPart_eq ho.conj.infPart_eq (hI.fst t)
      hI.isVac.2.theta hf (hI.isVac.2.fock τ)
  have cS : ∀ τ, IsCartanInv (gramAt D (neg A) τ) (-X.rA.s τ) := fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1
  have cT : ∀ τ, IsCartanInv (gramAt D WW τ) (X.rW.s τ) := fun τ => (hI.rigW.2.2 τ).1
  have hdet : ∀ τ, (gramAt D (neg A) τ).det ≠ 0 := fun τ h0 => by
    have := (cS τ).2.2.det_pos.ne'
    rw [Matrix.det_mul, h0, zero_mul] at this
    exact this rfl
  obtain ⟨r, hr, -⟩ := GlobalTheory.VacuumCharacter.exists_root hθ (neg A) hdet z' hz'
  have hy1 : IsDetRoot WW 1 1 := by
    show _ = _
    rw [Units.val_one, RingHom.map_one, mul_one]
    exact (Matrix.det_one).symm
  obtain ⟨η, hη⟩ := GlobalTheory.WeilParts.exists_isEtaTilde_unramified D
  have one : ∀ τ, compAt W.θ τ (Formalism.L2.Theta.mt WW 1) = 1 := fun τ => GlobalTheory.PointAtPlaceHom.infMat_one WW _
  obtain ⟨C, hC⟩ : ∃ C : ℂ, om' (z', 1) (X.f t) = C • X.f t :=
    ⟨_, GlobalTheory.WeilVacChar.vacuum_character D W.ψ hψ (neg A) WW W.θ hθ _ _ om' η hη hom (fun τ => -X.rA.s τ) X.rW.s cS cT
      z' hz' 1 (one_mem _) (fun τ => by rw [hζ τ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [one, one_mul, mul_one]) r 1 hr hy1 (X.f t) hf hfock⟩

  have hop : ∀ k : FVar D WW.rank A.rank →₀ ℕ, _ := fun k =>
    GlobalTheory.OrientedHeis.om_pureTensorO D W.ψ W.θ (neg A) WW _ _ om' hom hθ (fun τ => -X.rA.s τ) (fun τ => -X.rA.s τ)
      X.rA.B (fun τ => ζ τ • X.rA.B τ) X.rW.s X.rW.s X.rW.B X.rW.B z' 1
      (fun τ => by rw [hζ τ, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [one, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [hζ τ, Matrix.smul_mul, Matrix.one_mul])
      (fun τ => by rw [one, Matrix.one_mul]) (X.f t) hf (MvPolynomial.monomial k 1)
  set w : ℂ := if (-X.rA.s τ₀ = 1 ↔ X.rW.s τ₀ = 1) then (Complex.exp Complex.I)⁻¹ else Complex.exp Complex.I with hw
  have hscal : ∀ k : FVar D WW.rank A.rank →₀ ℕ,
      om' (z', 1) (pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t)
        (MvPolynomial.monomial k 1)) =
        (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) •
          pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (MvPolynomial.monomial k 1) := by
    intro k
    rw [(hop k).2, hC, GlobalTheory.FiniteFock.pureTensorO_smul,
      pureTensorO_scal_pm (S := neg A) (T := WW) hψ hθ (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (fun τ => Or.inr (by rw [hsA])) (fun τ => Or.inl (hsW τ)) (X.f t) hf ζ hζn k,
      smul_smul]
    congr 2
    rw [Finset.prod_eq_single τ₀]
    · simp only [hζdef, if_pos rfl, hw]
    · intro ρ _ hρ
      simp only [hζdef, if_neg hρ, inv_one, ite_self, one_pow]
    · simp
  refine ⟨C, w, by rw [hw]; split_ifs; exacts [Or.inr rfl, Or.inl rfl], fun k h => ?_⟩
  set φ := pureTensorO W.ψ W.θ (neg A) WW (fun τ => -X.rA.s τ) X.rW.s X.rA.B X.rW.B (X.f t) (MvPolynomial.monomial k 1)
    with hφ
  have hK := GlobalTheory.thetaKO_rat_left_and_eigen_right W.ψ (neg A) WW _ _ om' hom φ (hop k).1
  have hker : ∀ g : GA D A, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g = thetaKO om' ((ofSgn true A).symm g) h φ :=
    fun g => by
      show thetaKO (X.ω t) g h φ = (X.ω t) ((ofSgn true A) ((ofSgn true A).symm g), h) φ 0
      rw [MulEquiv.apply_symm_apply]
      rfl
  have hleft : ∀ γ ∈ GQ A, ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (γ * g) =
      X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g := by
    intro γ hγ g
    rw [hker, hker, map_mul]
    have := hK.1 _ ((GlobalTheory.SgnIdent.mem_GQ_sgn true A _).2 (by rwa [MulEquiv.apply_symm_apply])) 1 (one_mem _)
      ((ofSgn true A).symm g) h
    rwa [one_mul] at this
  have hright : ∀ g, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (g * ofSgn true A z') =
      (C * w ^ (∑ v ∈ k.support with v.1 = τ₀, k v)) * X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g := by
    intro g
    rw [hker, hker, map_mul, MulEquiv.symm_apply_apply]
    have := hK.2 z' 1 _ (hscal k) ((ofSgn true A).symm g) h
    rwa [mul_one] at this
  show ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g ∂X.m =
    _ * ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h g ∂X.m
  calc _ = ∫ g in X.fd, X.ker W.ψ W.θ t (MvPolynomial.monomial k 1) h (g * ofSgn true A z') ∂X.m :=
        (GlobalTheory.ChainOnto.setIntegral_fd_mul_right D A X.m X.fd hI.meas.1 hI.meas.2 _ hleft (ofSgn true A z')).symm
    _ = _ := by
        simp_rw [hright]
        exact integral_const_mul _ _

end GlobalTheory.BottomDeg

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalFormPhase
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfLe
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun

noncomputable section

namespace GlobalTheory.PhaseField

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice _root_.Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links _root_.Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.SplitFlip GlobalTheory.SplitWeil ValuativeRel MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

theorem exists_field_roots {n : ℕ} (hn : 0 < n) : ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧
    ∀ z : ℂ, z ^ n = 1 → z ∈ Set.range (algebraMap M ℂ) := by
  classical
  set S : Set ℂ := {z | z ^ n = 1} with hSdef
  have hS : S = ((Polynomial.nthRoots n (1 : ℂ)).toFinset : Set ℂ) := by
    ext z; simp [S, Polynomial.mem_nthRoots hn]
  haveI : Finite S := by rw [hS]; infer_instance
  have hint : ∀ z ∈ S, IsIntegral ℚ z := fun z hz =>
    ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C _ hn.ne', by
      simp [Polynomial.eval₂_sub, show z ^ n = 1 from hz]⟩
  exact ⟨IntermediateField.adjoin ℚ S, IntermediateField.finiteDimensional_adjoin hint,
    fun z hz => ⟨⟨z, IntermediateField.subset_adjoin ℚ S hz⟩, rfl⟩⟩

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem val_resCard_le {ϖ : kˣ} (hϖ : IsUnif ϖ) : valuation k ((Nat.card 𝓀[k] : ℕ) : k) ≤ valuation k (ϖ : k) := by
  classical
  letI := Fintype.ofFinite 𝓀[k]
  have h0 : IsLocalRing.residue 𝒪[k] ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) = 0 := by
    rw [map_natCast, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero _
  have hmem : ((Nat.card 𝓀[k] : ℕ) : 𝒪[k]) ∈ IsLocalRing.maximalIdeal 𝒪[k] :=
    (IsLocalRing.residue_eq_zero_iff _).1 h0
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one] at hmem
  rw [hϖ, le_uniformizer_iff]
  simpa using hmem

theorem exists_pow_eq_one_of_le {ψ : AddChar k Circle} {ϖ : kˣ} (hψ : HasConductor ψ 1) (hϖ : IsUnif ϖ) (N : ℕ) :
    ∃ n : ℕ, 0 < n ∧ ∀ z : k, valuation k z ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) → ((ψ z : Circle) : ℂ) ^ n = 1 := by
  have hq : 0 < Nat.card 𝓀[k] := Nat.card_pos
  refine ⟨Nat.card 𝓀[k] ^ N, pow_pos hq N, fun z hz => ?_⟩
  have h1 : valuation k (((Nat.card 𝓀[k] ^ N : ℕ) : k) * z) ≤ 1 := by
    rw [map_mul, Nat.cast_pow, map_pow]
    calc valuation k ((Nat.card 𝓀[k] : ℕ) : k) ^ N * valuation k z
        ≤ valuation k (ϖ : k) ^ N * valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) :=
          mul_le_mul' (pow_le_pow_left₀ zero_le' (val_resCard_le hϖ) N) hz
      _ = 1 := by
          rw [Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, map_inv₀, map_pow]
          exact mul_inv_cancel₀ (pow_ne_zero _ (by simp))
  have h2 : ψ (((Nat.card 𝓀[k] ^ N : ℕ) : k) * z) = 1 :=
    (hψ 1).2 le_rfl _ (by simpa using h1)
  rw [← nsmul_eq_mul, AddChar.map_nsmul_eq_pow] at h2
  rw [← Circle.coe_pow, h2, Circle.coe_one]

end Local


open GlobalTheory.RootEx Matrix in
theorem phase_bounded {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (G : Grid k) (hs : 1 ≤ G.s) (ψ : AddChar k Circle) (ν : Measure k)
    [ν.IsAddHaarMeasure] (ϖ : kˣ) (e : ℕ) (T : G.Args → ℂ) (keep : Bool) (g : G.VertexGroup) (hm : 2 ≤ G.m)
    (hϖ : IsUnif ϖ) (hψ : HasConductor ψ 1) (hT : G.IsTensor ϖ e (oppositePath G.m) T) :
    ∃ N : ℕ, ∀ (x : ColArgs G) (y : RowArgs G) (v : Vars G), flatTensor hs ψ ν (moved G keep g T) x y ≠ 0 →
      moved G keep g T (fill hs x y v) ≠ 0 → valuation k (phase x v) ≤ valuation k (((ϖ ^ N)⁻¹ : kˣ) : k) := by
  classical
  obtain ⟨n1, hsupp⟩ := FlatSupp.flatTensor_support G hs ψ ν ϖ e T keep g hϖ hT
  obtain ⟨n2, hlast⟩ := FlatLast.flatTensor_lastRow_bounded G hs ψ ν ϖ e T keep g hm hϖ hψ hT
  choose N hN using fun b : Edge =>
    FlatSupp.exists_bound_conj hϖ (Assignment.one.read (g b.tgt)) (Assignment.one.read (g b.src))
  set K := max n1 (max n2 ((oppositePath G.m).toFinset.sup N)) with hK
  set c := valuation k (((ϖ ^ K)⁻¹ : kˣ) : k) with hc
  have hc1 : 1 ≤ c := by
    have := FlatSupp.val_inv_pow_mono hϖ (Nat.zero_le K)
    rwa [show valuation k (((ϖ ^ 0)⁻¹ : kˣ) : k) = 1 by simp] at this
  have hcc : valuation k (((ϖ ^ (K + K))⁻¹ : kˣ) : k) = c * c := by
    rw [hc, FlatSupp.val_inv_pow, FlatSupp.val_inv_pow, pow_add, mul_inv]
  refine ⟨K + K, fun x y v hF hM => ?_⟩
  rw [hcc]
  have hT0 : T (G.moveArgs .one g (fill hs x y v)) ≠ 0 := by
    intro h0
    apply hM
    simp [moved, Grid.pathAct, h0]
  have key : ∀ b ∈ oppositePath G.m, ∀ r s, valuation k (fill hs x y v b r s) ≤ c := by
    intro b hb r s
    refine le_trans (hN b _ (fun r s => ?_) r s) (FlatSupp.val_inv_pow_mono hϖ
      ((Finset.le_sup (f := N) (List.mem_toFinset.2 hb)).trans ((le_max_right _ _).trans (le_max_right _ _))))
    have hm' : (G.moveArgs .one g (fill hs x y v)) b ∈ matLat _ (GlobalTheory.SplitFlip.stdLat k _) := by
      by_contra h
      exact hT0 (hT.2.1 _ b hb h)
    exact mem_matLat_stdLat.1 hm' r s
  have hstep : ∀ (j : Fin (G.m - 1)) p q, valuation k (stepPt (x j) (v j) p q) ≤ c := by
    intro j p q
    have hmem : Edge.theta G.m j ∈ oppositePath G.m := by simp [oppositePath]; omega
    have hj' : (j : ℕ) < G.m - 1 := j.2
    have h := key _ hmem
      (frame (a := topRank G j) (b := G.rank (G.m, j)) (c := G.m - 2 - j + 1) (by have := topRank_add hs j; omega) q)
      (frame (a := topRank G (j + 1)) (b := G.rank (G.m, j + 1)) (c := G.m - 2 - j)
        (by have := topRank_add hs (j + 1); omega) p)
    rw [fill_theta, transpose_apply, downMap, dite_eq_left hj'] at h
    simpa [reindex_apply, submatrix_apply, Equiv.symm_apply_apply] using h
  have hx : ∀ j, j < G.m → ∀ r s, valuation k (x j r s) ≤ c := by
    intro j hj r s
    by_cases hr : j + 1 = G.m ∧ r = topLast G (j + 1)
    · obtain ⟨h1, rfl⟩ := hr
      obtain rfl : j = G.m - 1 := by omega
      exact (hlast x y hF s).trans (FlatSupp.val_inv_pow_mono hϖ ((le_max_left _ _).trans (le_max_right _ _)))
    · exact ((hsupp x y hF).1 j hj r s fun h h' => hr ⟨h, h'⟩).trans (FlatSupp.val_inv_pow_mono hϖ (le_max_left _ _))
  have hcol : ∀ j r, valuation k (colVar x v j r) ≤ c := fun j r => hstep j _ _
  have hrow : ∀ (j : Fin (G.m - 1)) r, valuation k (rowVar x v (j + 1) r) ≤ c := by
    intro j r
    unfold rowVar
    split_ifs with h
    · refine Valuation.map_sum_le _ fun l _ => ?_
      split_ifs
      · exact hstep ⟨_, h⟩ _ _
      · simp
    · exact hx _ (by omega) _ _
  have hch : ∀ j : Fin (G.m - 1), valuation k (ch (stepPt (x j) (v j))) ≤ c := fun j =>
    Valuation.map_sum_le _ fun i _ => hstep j _ _
  unfold phase
  refine Valuation.map_sum_le _ fun j _ => ?_
  refine Valuation.map_add_le _ ((hch j).trans (le_mul_of_one_le_right' hc1)) ?_
  split_ifs
  · refine Valuation.map_sum_le _ fun r _ => ?_
    rw [map_mul]
    exact mul_le_mul' (hrow j r) (hcol j r)
  · simp

theorem phases_core {D : D7} {T : Type} [Finite T] {L : LevCh D T} {sc : Consts} {μ₀ : T} (hL : L.Is μ₀) {G : GridData L sc}
    {W : G.Weil} {U : Set T} (S : GridChoice W U) (hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q))
    (hc : ∀ t, ∀ P ∈ L.Q t, ((Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ ∀ t Φ, ∀ β ∈ S.supp t Φ, PhasesIn (algebraMap M ℂ) S t Φ β := by
  classical
  have hm : 2 ≤ D.R.m := D.R.two_le_m
  have hloc : ∀ t Φ (β : CosFam G t) (w : locPl G t), ∃ n : ℕ, 0 < n ∧ ∀ x y e, (S.term t Φ β w).datum x y ≠ 0 →
      moved (locGrid G t w) (keepAt G w) ((repsAt G t w).elt (β w)) (Tflip W S.B t Φ w) (fill one_le_sLen x y e) ≠ 0 →
      ((psiAt W w.1 (phase x e) : Circle) : ℂ) ^ n = 1 := by
    intro t Φ β w
    have hg := (Good.locGrid_isGood hL G W t hde (hc t)).1 w.1 w.2
    have h00 := hg.square 0 (by change 0 < D.R.m; omega) 0 (by change 0 < D.R.m; omega)
    haveI := (isUnitVol_unitVol w.1).1
    obtain ⟨N, hN⟩ := phase_bounded (locGrid G t w.1) one_le_sLen (psiAt W w.1) (unitVol w.1) (unifAt w.1) (depthAt G w.1)
      (Tflip W S.B t Φ w.1) (keepAt G w.1) ((repsAt G t w.1).elt (β w)) hm h00.unif h00.cond
      (isTensor_Tflip hL W S.B t Φ hde (hc t) w.2)
    obtain ⟨n, hn, hpow⟩ := exists_pow_eq_one_of_le h00.cond h00.unif N
    exact ⟨n, hn, fun x y e h1 h2 => hpow _ (hN x y e h1 h2)⟩
  choose nf hnf hpow using hloc
  haveI : ∀ t Φ, Finite (S.supp t Φ) := fun t Φ => ((S.sumOK_flat_fin_ex hL t Φ hde (hc t)).2.1).to_subtype
  haveI : Finite G.Datum := G.finite_datum (GlobalTheory.DiagLiftFix.isLattice_of_isFrame (hL.βY 0 (by omega)).choose_spec.1).fg
  letI : Fintype (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t) := Fintype.ofFinite _
  set n := ∏ i : (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t), nf i.1 i.2.1 i.2.2.1.1 i.2.2.2 with hn
  have hn0 : 0 < n := Finset.prod_pos fun i _ => hnf _ _ _ _
  obtain ⟨M, hM, hMr⟩ := exists_field_roots hn0
  refine ⟨M, hM, fun t Φ β hβ w x y e h1 h2 => hMr _ ?_⟩
  obtain ⟨c, hc'⟩ : nf t Φ β w ∣ n :=
    Finset.dvd_prod_of_mem (fun i : (Σ t : T, Σ Φ : G.Datum, (S.supp t Φ) × locPl G t) => nf i.1 i.2.1 i.2.2.1.1 i.2.2.2)
      (Finset.mem_univ ⟨t, Φ, ⟨β, hβ⟩, w⟩)
  rw [hc', pow_mul, hpow t Φ β w x y e h1 h2, one_pow]

end GlobalTheory.PhaseField

namespace GlobalTheory.BigTop.Fun

end GlobalTheory.BigTop.Fun
end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx

namespace GlobalTheory.RowEx

theorem nfPhase_of_sumOKK : SumOKK → NFPhase := by
  intro _
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs _ => ?_⟩⟩
  exact (letI := hS.fin; GlobalTheory.PhaseField.phases_core hS.core.lev ch.S.toGridChoice (GlobalTheory.RowClaim.Test.pde_ne_q hS) hIs.guard)

end GlobalTheory.RowEx

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeMemUnitary
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
noncomputable section

open scoped Matrix

namespace GlobalTheory.RealColAct

variable {D : D7}

theorem gramAt_of_gram_one {V : HSp D} (hV : HSpace.gram V = 1) (τ : D.what₂.Tau) : gramAt D V τ = 1 := by
  unfold gramAt
  rw [hV]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem compAt_mem_unitary {θ : InfFam D} (hθ : IsInfFam θ) {V : HSp D} (hV : HSpace.gram V = 1) (g : GA D V)
    (τ : D.what₂.Tau) : compAt θ τ (Formalism.L2.Theta.mt V g) ∈ Matrix.unitaryGroup (Fin V.rank) ℂ := by
  have h := GlobalTheory.StdUnn.CartanMove.compAt_isom hθ V g τ
  rw [gramAt_of_gram_one hV, Matrix.mul_one] at h
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  exact h

theorem transpose_mem_unitary {n : ℕ} {K : Matrix (Fin n) (Fin n) ℂ} (hK : K ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Kᵀ ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  have h2 : K * star K = 1 := Matrix.mem_unitaryGroup_iff.1 hK
  rw [Matrix.mem_unitaryGroup_iff']
  have e : star Kᵀ = (star K)ᵀ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.star_eq_conjTranspose]; rfl
  rw [e, ← Matrix.transpose_mul, h2, Matrix.transpose_one]

def realCol (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) :
    GinfC V →* (D.what₂.Tau → Matrix.unitaryGroup (Fin V.rank) ℂ) where
  toFun g τ := ⟨(compAt θ τ (Formalism.L2.Theta.mt V ((g : GA D V)⁻¹)))ᵀ,
    transpose_mem_unitary (compAt_mem_unitary hθ hV _ τ)⟩
  map_one' := by
    funext τ
    apply Subtype.ext
    simp only [OneMemClass.coe_one, inv_one, GlobalTheory.StdUnn.CartanMove.compAt_mt_one, Matrix.transpose_one, Pi.one_apply]
  map_mul' g h := by
    funext τ
    apply Subtype.ext
    simp only [Subgroup.coe_mul, mul_inv_rev, GlobalTheory.StdUnn.CartanMove.compAt_mt_mul, Matrix.transpose_mul, Pi.mul_apply]
    rfl

theorem realCol_apply (θ : InfFam D) (hθ : IsInfFam θ) (V : HSp D) (hV : HSpace.gram V = 1) (g : GinfC V) (τ : D.what₂.Tau) :
    (realCol θ hθ V hV g τ : Matrix (Fin V.rank) (Fin V.rank) ℂ) = (compAt θ τ (Formalism.L2.Theta.mt V ((g : GA D V)⁻¹)))ᵀ := rfl

end GlobalTheory.RealColAct
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFlipStageIsTensorPlaceDepth
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFlipStageIsTensorPlaceDepth
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.FlipRun

theorem canFlip_of_append {γ : List GlobalTheory.SplitFlip.Edge} {l l' : List (ℕ × ℕ)} (h : GlobalTheory.SplitFlip.CanFlip γ (l ++ l')) :
    GlobalTheory.SplitFlip.CanFlip γ l := by
  induction l generalizing γ with
  | nil => exact .nil _
  | cons x l ih =>
    cases h with
    | cons hp h' => exact .cons hp (ih h')

theorem isTensor_flips_take : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (Φ : ch.G.Datum), ∀ w ∈ locPl ch.G t, ∀ k, k ≤ D.R.m ^ 2 → (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w) ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).path ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).tensor := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch hch _ => ?_⟩⟩
  intro t Φ w hw k _
  have hL := s.core.lev
  have hde : Nat.Coprime D.host.pde (D.host.QS * D.host.q) ∧ Nat.Coprime D.host.pde' (D.host.QS * D.host.q) := by
    obtain ⟨⟨P, -, -⟩, -⟩ := s.size
    have key : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q) := fun p hp hpp =>
      UpperTheory.Ram.Fun.coprime_QSq_of_splitK D.host hpp (P.level_split p hp)
    exact ⟨key _ D.host.pde_level.1 D.host.pde_prime, key _ D.host.pde_level.2 D.host.pde'_prime⟩
  have hg := (Good.locGrid_isGood hL ch.G ch.W t hde (hch.guard t)).1 w hw
  have hadm := GivenAdm.givenStage_isAdmissible hL ch.S.B t Φ hw
  have hm : 0 < D.R.m := by have := D.R.two_le_m; omega
  have h00 := hg.square 0 hm 0 hm
  have hν : ∀ x ∈ flipOrder D.R.m, GlobalTheory.SplitFlip.CondLE (unifAt w) (depthAt ch.G w) ((locGrid ch.G t w).nu x.1 x.2) := by
    intro x hx
    simp only [flipOrder, List.mem_flatMap, List.mem_map, List.mem_range] at hx
    obtain ⟨i, hi, j, hj, rfl⟩ := hx
    rw [← GlobalTheory.SplitFlip.Grid.alpha_div_beta]
    exact (hg.square i hi j hj).condν
  have hcan : GlobalTheory.SplitFlip.CanFlip (GlobalTheory.SplitFlip.givenPath D.R.m) ((flipOrder D.R.m).take k) := by
    have h := (canFlip_flipOrder D.R.m).1
    rw [← List.take_append_drop k (flipOrder D.R.m)] at h
    exact canFlip_of_append h
  exact isTensor_flips h00.unif h00.cond h00.one_le ((flipOrder D.R.m).take k) (givenStage t w ch.S.B Φ)
    (fun x hx => hν x (List.mem_of_mem_take hx)) hcan (fun X => GivenAdm.givenLevel_open hL hw X) hadm.tensor

end GlobalTheory.FlipRun

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFlipStageIsTensorPlaceDepthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localFlipStage_isTensor_placeDepth : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ _ ch => ∀ (t : T) (Φ : ch.G.Datum), ∀ w ∈ locPl ch.G t, ∀ k, k ≤ D.R.m ^ 2 → (locGrid ch.G t w).IsTensor (unifAt w) (depthAt ch.G w) ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).path ((givenStage t w ch.S.B Φ).flips .one (psiAt ch.W w) (unifAt w) (depthAt ch.G w) ((flipOrder D.R.m).take k)).tensor := by
  first | exact @GlobalTheory.FlipRun.isTensor_flips_take | exact GlobalTheory.FlipRun.isTensor_flips_take | (intros; apply GlobalTheory.FlipRun.isTensor_flips_take <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrameGramUnitaryIdentity
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.FinTransJet

theorem inV_stdL_eq_colLat {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E) :
    GlobalTheory.MovedDict.inV B (Formalism.MainNotions.StandardLatticesGL3.stdL D n) = (Formalism.L2.DIV.colLat B : Set (Fin n → D.host.E)) := by
  have hc := GlobalTheory.ColStd.colLat_comap_eq_stdLat B
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    have hy' : y ∈ Formalism.L2.Pj.stdLat D.host.E n := hy
    rw [← hc] at hy'
    exact hy'
  · intro hx
    refine ⟨(B⁻¹ : GL (Fin n) D.host.E).1.mulVec x, ?_, ?_⟩
    · show _ ∈ Formalism.L2.Pj.stdLat D.host.E n
      rw [← hc, Submodule.mem_comap]
      simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]
      exact hx
    · simp only [Matrix.mulVec_mulVec]
      rw [show (B.1 * (B⁻¹).1) = 1 from B.mul_inv, Matrix.one_mulVec]

end GlobalTheory.FinTransJet

namespace GlobalTheory.FinTransJet

end GlobalTheory.FinTransJet
end
end
