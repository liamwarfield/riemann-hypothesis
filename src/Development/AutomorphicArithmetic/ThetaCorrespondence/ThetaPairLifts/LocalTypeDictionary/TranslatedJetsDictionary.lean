module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RowGrpEq
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.SplittingOfMovedKappaTwist
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsRationalMoveOfJets
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SelfDualFullLatticeShared

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumVectorCorrespondence
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedMovedVacuumKappa
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedKappaRationalOfArithmetic
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsUniqueMovedKappaJet
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedVacuumRootExistsAlgebraic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedVacRoot
private theorem mem_algebraic_of_root_of_unity {c : ℂ} {m : ℕ} (hm : 0 < m) (h : c ^ m = 1) : c ∈ Qbar :=
  mem_algebraicClosure_iff'.2 (IsIntegral.of_pow hm (h ▸ isIntegral_one))
private theorem norm_root_of_unity_eq_one {K : Type} [NormedField K] (σ : Qbar →+* K) {c : ℂ} {m : ℕ} (hm : 0 < m) (h : c ^ m = 1)
    (hc : c ∈ Qbar) : ‖σ ⟨c, hc⟩‖ = 1 := by
  have e : (⟨c, hc⟩ : Qbar) ^ m = 1 := Subtype.ext h
  have e' : ‖σ ⟨c, hc⟩‖ ^ m = 1 := by rw [← norm_pow, ← map_pow, e, map_one, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm.ne').1 e'
private theorem isOpen_principal_level_subgroup {D : D7} (T : HSp D) {N : ℕ} (hN : 0 < N) :
    IsOpen (((GlobalTheory.Member.PrincLevel.levelGroup T N).subgroupOf (GfC T) : Subgroup (GfC T)) : Set (GfC T)) := by
  let F : GfC T → Formalism.IndefR.Bridge.Gf T := fun x => (finHom T).rangeRestrict x.1
  have hG : Continuous fun x : GfC T => (finHom T x.1 : GL (Fin T.rank) (Formalism.L2.Herm.Af D.host.F ⊗[D.host.F] D.host.E)) := by
    refine Units.continuous_iff.2 ⟨(GlobalTheory.Member.continuous_finHom_val D T).comp continuous_subtype_val, ?_⟩
    have h := ((GlobalTheory.Member.continuous_finHom_val D T).comp continuous_inv).comp
      (continuous_subtype_val (p := fun x => x ∈ GfC T))
    refine h.congr fun x => ?_
    simp [Function.comp_def, map_inv]
  have hF : Continuous F := hG.subtype_mk _
  have e : (((GlobalTheory.Member.PrincLevel.levelGroup T N).subgroupOf (GfC T) : Subgroup (GfC T)) : Set (GfC T)) =
      F ⁻¹' (((GlobalTheory.Member.PrincLevel.levelGroup T N).map (finHom T).rangeRestrict : Subgroup (Formalism.IndefR.Bridge.Gf T)) :
        Set (Formalism.IndefR.Bridge.Gf T)) := by
    ext x
    simp only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Set.mem_preimage]
    constructor
    · intro hx
      exact Subgroup.mem_map.2 ⟨x.1, hx, rfl⟩
    · intro hx
      obtain ⟨k', hk', e⟩ := Subgroup.mem_map.1 hx
      have e' : finHom T k' = finHom T x.1 := congrArg Subtype.val e
      refine ⟨x.2, ?_⟩
      have hc := hk'.2
      unfold GlobalTheory.Member.FinCong at hc ⊢
      rw [← e']
      exact hc
  rw [e]
  exact (GlobalTheory.SmoothVac.isOpen_map_levelGroup T hN).preimage hF
private theorem exists_pow_mem_open_subgroup {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (H K U : Subgroup G)
    (hKH : K ≤ H) (hK : IsCompact (K : Set G)) (hU : IsOpen ((U.subgroupOf H : Subgroup H) : Set H)) {k : G} (hk : k ∈ K) :
    ∃ m : ℕ, 0 < m ∧ k ^ m ∈ U := by
  haveI : CompactSpace K := isCompact_iff_compactSpace.1 hK
  have ho : IsOpen ((U.subgroupOf K : Subgroup K) : Set K) := by
    have hc : Continuous (Subgroup.inclusion hKH) := continuous_inclusion hKH
    exact hU.preimage hc
  haveI := Subgroup.quotient_finite_of_isOpen _ ho
  obtain ⟨m, hm, -, h⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (H := U.subgroupOf K) Subgroup.index_ne_zero_of_finite ⟨k, hk⟩
  exact ⟨m, hm, h⟩
private theorem selfDual_full {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : IsSelfDualC V Λ) : Submodule.IsFullLattice D.host.E Λ := _root_.DedupShared.selfDual_isFullLattice V Λ hΛ

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
private theorem exists_pow_mem_principal_level {D : D7} (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E))
    (hΛ : Submodule.IsFullLattice D.host.E Λ) {k : GA D V} (hk : k ∈ GfC V)
    (hfix : Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE V k) Λ = Λ) {N : ℕ} (hN : 0 < N) :
    ∃ m : ℕ, 0 < m ∧ k ^ m ∈ GlobalTheory.Member.PrincLevel.levelGroup V N := by
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ Λ hΛ
  have key := Formalism.UG.P.span_recovery_of_integral_adelic_approx Formalism.UG.P.integral_adele_approximation_holds D.host.F D.host.E (Fin V.rank) Λ
    (Module.Finite.iff_fg.2 hΛ.fg) hΛ.span_eq_top (Formalism.IndefR.Lev.finE V k)
  rw [hfix] at key
  have key' : ∀ u, u ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ ↔
      Matrix.mulVec ((Formalism.IndefR.Lev.finE V k)⁻¹).1 u ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ := key
  have hst : Formalism.IndefR.Lev.finE V k ∈ Formalism.L2.DIV.St β := by
    refine (GlobalTheory.LevSplit.mem_St_iff β Λ hβ _).2 ⟨fun y hy => (key' _).2 ?_, fun y hy => (key' y).1 hy⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    exact hy
  exact exists_pow_mem_open_subgroup (GfC V) (Formalism.IndefR.Lev.levA V (Formalism.L2.DIV.St β)) _ inf_le_left
    (GlobalTheory.AscInh.stab_compact_open V β).1 (isOpen_principal_level_subgroup V hN) ⟨hk, hst⟩
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
private theorem exists_root_of_unity_factor {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) {k : GA D S} {k' : GA D T} (hk : k ∈ GfC S) (hk' : k' ∈ GfC T)
    (h1 : Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE S k) ΛS = ΛS)
    (h2 : Formalism.UG.CS.globLat (Formalism.IndefR.Lev.finE T k') ΛT = ΛT)
    (hf' : IsVacO ψ θ S T sS sT ΛS ΛT (om (k, k') f)) :
    ∃ (c : ℂ) (m : ℕ), 0 < m ∧ c ^ m = 1 ∧ om (k, k') f = c • f := by
  obtain ⟨c, hc⟩ := GlobalTheory.LevelVac.vac_eq_smul hS hT hΛS hΛT hf hf'
  obtain ⟨α, hα⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ ΛS (selfDual_full S ΛS hΛS)
  obtain ⟨β, hβ⟩ := GlobalTheory.latticeFrame.exists_frame D.host.F D.host.E _ ΛT (selfDual_full T ΛT hΛT)
  obtain ⟨N, hN, hfix⟩ := GlobalTheory.LevelVac.exists_level_fix hW hS hT hΛS hΛT hα hβ hf
  obtain ⟨a, ha, hka⟩ := exists_pow_mem_principal_level S ΛS (selfDual_full S ΛS hΛS) hk h1 hN
  obtain ⟨b, hb, hkb⟩ := exists_pow_mem_principal_level T ΛT (selfDual_full T ΛT hΛT) hk' h2 hN
  have e1 : k ^ (a * b) ∈ GlobalTheory.Member.PrincLevel.levelGroup S N := by
    rw [pow_mul]; exact pow_mem hka b
  have e2 : k' ^ (a * b) ∈ GlobalTheory.Member.PrincLevel.levelGroup T N := by
    rw [pow_mul']; exact pow_mem hkb a
  have e3 := hfix _ e1.1 _ e2.1 e1.2 e2.2
  have e4 : om (k ^ (a * b), k' ^ (a * b)) f = c ^ (a * b) • f := GlobalTheory.LevelVac.om_pow_eq om (k, k') f c hc (a * b)
  obtain ⟨w, hw⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hf
  refine ⟨c, a * b, mul_pos ha hb, ?_, hc⟩
  have e5 := congrFun (e4.symm.trans e3) w
  rw [Pi.smul_apply, smul_eq_mul] at e5
  exact mul_right_cancel₀ hw (e5.trans (one_mul _).symm)
private theorem inverse_image_standard_lattice {D : D7} {n : ℕ} (B : GL (Fin n) D.host.E) :
    inV B (stdL D n) = (colLat B : Set (Fin n → D.host.E)) := by
  ext y
  simp only [inV, Set.mem_image, SetLike.mem_coe]
  unfold colLat
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : ∀ i, ∃ c : 𝓞 D.host.E, algebraMap _ D.host.E c = z i := fun i =>
      Submodule.mem_one.1 (hz i (Set.mem_univ i))
    choose c hc using hz'
    refine ⟨c, funext fun a => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, hc, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rintro ⟨c, rfl⟩
    refine ⟨fun j => algebraMap _ D.host.E (c j), fun i _ => Submodule.mem_one.2 ⟨c i, rfl⟩, funext fun a => ?_⟩
    simp only [Finset.sum_apply, Pi.smul_apply, Algebra.smul_def, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem movedVacuum_root_exists_algebraic (hP : _root_.GlobalTheory.FunPr.ThetaLocalInputs) (hI : ∀ D, GlobalTheory.NormSum.Inp D) {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R) (hch : ch.Is) (p : Pair T) (hp : DefPair D.R.m p) (x : FinPt ch.G p.small) (y : FinPt ch.G p.big)
    (hx : GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x = stdL D _)
    (hy : GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y = stdL D _) :
    ∃ (c : ℂ) (m : ℕ), 0 < m ∧ c ^ m = 1 ∧
      ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small))
        ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p) = c • ch.S.Z.vac p := by
  have hn := DefPair.nodes hp
  obtain ⟨h1, h2⟩ := DefPair.nodes hp
  have hom := ch.W.om_is p (by cases p <;> simp only [DefPair, DefNode] at hp hn <;> simp only [Pair.InRange, Node.InRange] <;> omega)
  have negMem : ∀ (V : HSp D) {g : Formalism.L2.Theta.GA D V}, g ∈ GfC V → negGA V g ∈ GfC (negSp V) := by
    intro V g hg
    have e : matHom (negSp V) (negGA V g) = matHom V g := Units.ext (mt_negGA V g)
    simp only [GfC, MonoidHom.mem_ker, infHom, MonoidHom.comp_apply] at hg ⊢
    rw [e]
    exact hg
  have hvac := _root_.GlobalTheory.MovedDict.moved_vacuum_isVacuumIntegral hP hI ch hch p hp x y
  have hv := ch.S.Z.vac_is p hp
  have gx := GlobalTheory.MovedHomLat.movedLat_eq ch.S.toGridChoice _ h1 x
  have gy := GlobalTheory.MovedHomLat.movedLat_eq ch.S.toGridChoice _ h2 y
  have ix : inV (ch.S.N.fr p.small) (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) = (colLat (ch.S.N.fr p.small) : Set _) := by
    rw [hx, inverse_image_standard_lattice]
  have iy : inV (ch.S.N.fr p.big) (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) = (colLat (ch.S.N.fr p.big) : Set _) := by
    rw [hy, inverse_image_standard_lattice]
  have fx := SetLike.coe_injective (gx.symm.trans ix)
  have fy := SetLike.coe_injective (gy.symm.trans iy)
  cases p with
  | chi i j =>
    rw [show inV (frS ch.S.N (.chi i j)) (srcLat ch.S.toGridChoice (.chi i j) x y) = _ from iy,
      show inV (frT ch.S.N (.chi i j)) (tgtLat ch.S.toGridChoice (.chi i j) x y) = _ from ix] at hvac
    exact exists_root_of_unity_factor hom (fun τ => isCartanInv_neg (ch.W.cart_is _ h2.inRange τ)) (fun τ => ch.W.cart_is _ h1.inRange τ)
      (isSelfDualC_neg (ch.S.N.selfDual h2)) (ch.S.N.selfDual h1) hv (negMem _ (y * ch.S.N.u _).2) (x * ch.S.N.u _).2
      fy fx hvac
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    rw [show inV (frS ch.S.N (.top t j)) (srcLat ch.S.toGridChoice (.top t j) x y) = _ from ix,
      show inV (frT ch.S.N (.top t j)) (tgtLat ch.S.toGridChoice (.top t j) x y) = _ from iy] at hvac
    exact exists_root_of_unity_factor hom (fun τ => ch.W.cart_is _ h1.inRange τ) (fun τ => ch.W.cart_is _ h2.inRange τ)
      (ch.S.N.selfDual h1) (ch.S.N.selfDual h2) hv (x * ch.S.N.u _).2 (y * ch.S.N.u _).2
      fx fy hvac
end GlobalTheory.MovedVacRoot
end
open GlobalTheory.MovedVacRoot in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moved_vacuum_has_algebraic_root : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x = stdL D _ → GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y = stdL D _ →
    ∃ κ : ℂ, Mod1All κ ∧ (∀ (q : ℕ) [Fact q.Prime], GlobalTheory.MovedKappaEx.UnitAt q κ) ∧ GlobalTheory.MovedKappaEx.JetKap ch p x y κ := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y hx hy
  obtain ⟨c, m, hm, h1, hc⟩ := _root_.GlobalTheory.MovedVacRoot.movedVacuum_root_exists_algebraic hP hI ch hch p hp x y hx hy
  have h2 : (opp p c) ^ m = 1 := by rw [← map_pow, h1, map_one]
  have h3 := mem_algebraic_of_root_of_unity hm h2
  refine ⟨opp p c, ⟨h3, fun σ => norm_root_of_unity_eq_one σ hm h2 h3⟩, fun q _ lam => ?_, fun k => ?_⟩
  · rw [lamC, dite_eq_left h3]
    exact norm_root_of_unity_eq_one lam hm h2 h3
  · have hs : srcLat ch.S.toGridChoice p x y = stdL D _ := by
      cases p
      exacts [hy, hx, hy, hx]
    have ht : tgtLat ch.S.toGridChoice p x y = stdL D _ := by
      cases p
      exacts [hx, hy, hx, hy]
    have hoo : opp p (opp p c) = c := by
      cases p <;> simp [opp]
    have he0 := ch.S.Z.e0_is p hp
    have hK : KLat D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) (ch.G.pS p).rank (ch.G.pT p).rank) :=
      Or.inr ⟨_, _, GlobalTheory.NormSum.VacInt.sd_std D _, GlobalTheory.NormSum.VacInt.sd_std D _, rfl⟩
    obtain ⟨-, -, hself, -⟩ := GlobalTheory.ThetaTriple.klat_triples D D.host.ccK ch.S.Z.δ ch.S.Z.crv (ch.G.pS p).rank (ch.G.pT p).rank
    have hI0 : Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
        (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (srcLat ch.S.toGridChoice p x y) (tgtLat ch.S.toGridChoice p x y))
        (ch.S.Z.e0 p) = ch.S.Z.e0 p := by
      rw [hs, ht]
      exact hself _ hK _ he0.1
    have hd : Differentiable ℂ (ch.S.Z.e0 p) := he0.1.1
    have h0 := ch.S.Z.kernelNorm_constant_spec p hp k
    rw [hI0, GlobalTheory.MovedKappa.applyAt0_const_mul D _ hd, hc]
    unfold fockIn at h0 ⊢
    rw [Formalism.IndefR.Eqv.KerDiag.pureTensorO_smul, Pi.smul_apply, h0, smul_eq_mul]
    simp only [map_mul, hoo]
    ring
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsMovedKappaDecomposition
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedKappaDec
theorem exists_movedKappa_decomposition : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (X : Node), DefNode D.R.m X → ∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime) → ∀ x : FinPt ch.G X,
    ∃ r s x₀ : FinPt ch.G X, GlobalTheory.MovedKappaEx.RatFin _ r ∧ s ∈ GlobalTheory.MovedKappaEx.splitOff _ Q ∧
      GlobalTheory.SumSize.latAt ch.S.toGridChoice X x₀ = stdL D _ ∧ (∀ q ∈ Q, EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice X (s * x₀)) (stdL D _)) ∧ x = r * s * x₀ := by
  intro _ _ D Γ _ _ Pl0 T A Ks _ _ _ R ch _ X hX Q hQ x
  obtain ⟨r, s, k, hr, hs, hk, e⟩ := GlobalTheory.RatSplitLat.exists_rat_split_lat (ch.G.V X) (ch.S.N.fr X) (∏ q ∈ Q, q)
    (Finset.prod_pos fun q hq => (hQ q hq).pos) (x * ch.S.N.u X)
  have hs' := GlobalTheory.MovedKappaEx.mem_splitOff_of_suppSplit _ Q s hs
  have hB := GlobalTheory.LatStdStab.latAt_mul_inv_eq_stdL ch.S.toGridChoice X hX k hk
  refine ⟨r, s, k * (ch.S.N.u X)⁻¹, hr, hs', hB, fun q hq => ?_, ?_⟩
  · have key : ∀ s' ∈ GlobalTheory.MovedKappaEx.splitOff (ch.G.V X) Q, ∀ y : FinPt ch.G X,
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice X (s' * y)) (GlobalTheory.SumSize.latAt ch.S.toGridChoice X y) := by
      intro s' hs'
      induction hs' using Subgroup.closure_induction with
      | mem g hg =>
        obtain ⟨e, he, hoff, hsupp⟩ := hg
        exact fun y => GlobalTheory.MovedSplitEq.eqAt_latAt_mul ch.S.toGridChoice X hX q (hQ q hq) e he (hoff q hq) g y hsupp
      | one => exact fun y => by rw [one_mul]; exact eqAt_refl q _
      | mul a b _ _ ha hb => exact fun y => by rw [mul_assoc]; exact eqAt_trans (ha (b * y)) (hb y)
      | inv a _ ha =>
        intro y
        have := ha (a⁻¹ * y)
        rw [mul_inv_cancel_left] at this
        exact eqAt_symm this
    have := key s hs' (k * (ch.S.N.u X)⁻¹)
    rw [hB] at this
    exact this
  · rw [← mul_assoc, ← e, mul_inv_cancel_right]
end GlobalTheory.MovedKappaDec
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedKappa_decomposition_exists : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (X : Node), DefNode D.R.m X → ∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime) → ∀ x : FinPt ch.G X,
    ∃ r s x₀ : FinPt ch.G X, GlobalTheory.MovedKappaEx.RatFin _ r ∧ s ∈ GlobalTheory.MovedKappaEx.splitOff _ Q ∧
      GlobalTheory.SumSize.latAt ch.S.toGridChoice X x₀ = stdL D _ ∧ (∀ q ∈ Q, EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice X (s * x₀)) (stdL D _)) ∧ x = r * s * x₀ := by
  first | exact @_root_.GlobalTheory.MovedKappaDec.exists_movedKappa_decomposition | exact _root_.GlobalTheory.MovedKappaDec.exists_movedKappa_decomposition | (intros; apply _root_.GlobalTheory.MovedKappaDec.exists_movedKappa_decomposition <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedKappaEx
theorem jet_kappa_unique : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big) (κ κ' : ℂ),
    JetKap ch p x y κ → JetKap ch p x y κ' → κ = κ' := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y κ κ' h1 h2
  set F := Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) with hFdef
  have hF : Differentiable ℂ F :=
    _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hPr hInp ch hIs p hp x y
  obtain ⟨hsd, hsd'⟩ := _root_.GlobalTheory.MovedSD.moved_series_decomposition hPr hInp ch hIs p hp x y
  have hF0 : F ≠ 0 := selfDualLattice_intertwiner_baseVector_ne_zero ch.S.Z.crv ch.S.Z.pt0 (ch.S.Z.e0_is p hp) hsd hsd'
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D hF hF0
  have e := (h1 α).symm.trans (h2 α)
  rw [applyAt0_monomial', applyAt0_monomial', GlobalTheory.ProdThetaConj.taylor_const_mul hF,
    GlobalTheory.ProdThetaConj.taylor_const_mul hF] at e
  have e' := (opp p).injective (mul_left_cancel₀ (ch.S.Z.c0 p).ne_zero e)
  have hP : (α.prod fun v e => period ch.S.Z.δ v.1 ^ e) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero (GlobalTheory.TwoTorsionPt.delta_ne ch.S.Z.crv) v.1)
  have hfac : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have e'' := mul_left_cancel₀ (mul_ne_zero hP hfac) (by simpa only [mul_assoc] using e')
  exact mul_right_cancel₀ hα e''
end GlobalTheory.MovedKappaEx
namespace GlobalTheory.MovedKappaEx
theorem exists_moved_kappa : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ₀ : ℂ, Mod1All κ₀ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ₀‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ₀ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y
  obtain ⟨hns, hnb⟩ := hp.nodes
  have chain : ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime) →
      (∀ q ∈ Q, EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) ∧
        EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _)) →
      ∃ κ, Mod1All κ ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) ∧ JetKap ch p x y κ := by
    intro Q hQ hQx
    obtain ⟨r, s, x₀, hr, hs, hx₀, hsx, rfl⟩ := _root_.GlobalTheory.T.movedKappa_decomposition_exists hPr hInp ch hIs _ hns Q hQ x
    obtain ⟨r', s', y₀, hr', hs', hy₀, hsy, rfl⟩ := _root_.GlobalTheory.T.movedKappa_decomposition_exists hPr hInp ch hIs _ hnb Q hQ y
    obtain ⟨κ₀, hm₀, hu₀, hj₀⟩ := _root_.GlobalTheory.T.moved_vacuum_has_algebraic_root hPr hInp ch hIs p hp x₀ y₀ hx₀ hy₀
    have stepS : ∀ g ∈ splitOff (ch.G.V p.small) Q, ∀ (x' : FinPt ch.G p.small) (κ : ℂ), JetKap ch p x' y₀ κ → Mod1All κ →
        (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
        ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (g * x') y₀ κ' := by
      have gen : ∀ g : FinPt ch.G p.small, (∃ e, IsSplitIdem D e ∧ (∀ q ∈ Q, OffPrime e q) ∧
          SuppAt e _ (g : GA D (ch.G.V p.small))) → ∀ (x' : FinPt ch.G p.small) (κ : ℂ), JetKap ch p x' y₀ κ → Mod1All κ →
          (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
          ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (g * x') y₀ κ' := by
        rintro g ⟨e, he, hoff, hsupp⟩ x' κ hj hm hu
        obtain ⟨c, hc, hcu, hjc⟩ := _root_.GlobalTheory.T.splitting_of_moved_kappa_twist hPr hInp ch hIs p hp x' y₀ κ hj e he g 1 hsupp
          (by rw [OneMemClass.coe_one]; exact GlobalTheory.LeviSplitChar.suppAt_one e _)
        rw [one_mul] at hjc
        exact ⟨c * κ, GlobalTheory.FamilyTieProof.mod1All_mul' hc hm,
          fun q hq hf => unitAt_mul hc hm (@hcu q hf (hoff q hq)) (hu q hq hf), hjc⟩
      intro g hg
      induction hg using Subgroup.closure_induction'' with
      | mem g hg => exact gen g hg
      | inv_mem g hg =>
        obtain ⟨e, he, hoff, hsupp⟩ := hg
        exact gen g⁻¹ ⟨e, he, hoff, by rw [InvMemClass.coe_inv]; exact GlobalTheory.SplitPlace.suppAt_inv hsupp⟩
      | one => intro x' κ hj hm hu; exact ⟨κ, hm, hu, by rwa [one_mul]⟩
      | mul g₁ g₂ _ _ h1 h2 =>
        intro x' κ hj hm hu
        obtain ⟨κ₁, hm₁, hu₁, hj₁⟩ := h2 x' κ hj hm hu
        obtain ⟨κ₂, hm₂, hu₂, hj₂⟩ := h1 _ κ₁ hj₁ hm₁ hu₁
        exact ⟨κ₂, hm₂, hu₂, by rwa [mul_assoc]⟩
    have stepB : ∀ g ∈ splitOff (ch.G.V p.big) Q, ∀ (y' : FinPt ch.G p.big) (κ : ℂ), JetKap ch p (s * x₀) y' κ → Mod1All κ →
        (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
        ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (s * x₀) (g * y') κ' := by
      have gen : ∀ g : FinPt ch.G p.big, (∃ e, IsSplitIdem D e ∧ (∀ q ∈ Q, OffPrime e q) ∧
          SuppAt e _ (g : GA D (ch.G.V p.big))) → ∀ (y' : FinPt ch.G p.big) (κ : ℂ), JetKap ch p (s * x₀) y' κ → Mod1All κ →
          (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ) →
          ∃ κ', Mod1All κ' ∧ (∀ q ∈ Q, ∀ (_ : Fact q.Prime), UnitAt q κ') ∧ JetKap ch p (s * x₀) (g * y') κ' := by
        rintro g ⟨e, he, hoff, hsupp⟩ y' κ hj hm hu
        obtain ⟨c, hc, hcu, hjc⟩ := _root_.GlobalTheory.T.splitting_of_moved_kappa_twist hPr hInp ch hIs p hp (s * x₀) y' κ hj e he 1 g
          (by rw [OneMemClass.coe_one]; exact GlobalTheory.LeviSplitChar.suppAt_one e _) hsupp
        rw [one_mul] at hjc
        exact ⟨c * κ, GlobalTheory.FamilyTieProof.mod1All_mul' hc hm,
          fun q hq hf => unitAt_mul hc hm (@hcu q hf (hoff q hq)) (hu q hq hf), hjc⟩
      intro g hg
      induction hg using Subgroup.closure_induction'' with
      | mem g hg => exact gen g hg
      | inv_mem g hg =>
        obtain ⟨e, he, hoff, hsupp⟩ := hg
        exact gen g⁻¹ ⟨e, he, hoff, by rw [InvMemClass.coe_inv]; exact GlobalTheory.SplitPlace.suppAt_inv hsupp⟩
      | one => intro y' κ hj hm hu; exact ⟨κ, hm, hu, by rwa [one_mul]⟩
      | mul g₁ g₂ _ _ h1 h2 =>
        intro y' κ hj hm hu
        obtain ⟨κ₁, hm₁, hu₁, hj₁⟩ := h2 y' κ hj hm hu
        obtain ⟨κ₂, hm₂, hu₂, hj₂⟩ := h1 _ κ₁ hj₁ hm₁ hu₁
        exact ⟨κ₂, hm₂, hu₂, by rwa [mul_assoc]⟩
    obtain ⟨κ₁, hm₁, hu₁, hj₁⟩ := stepS s hs x₀ κ₀ hj₀ hm₀ (fun q _ hf => @hu₀ q hf)
    obtain ⟨κ₂, hm₂, hu₂, hj₂⟩ := stepB s' hs' y₀ κ₁ hj₁ hm₁ hu₁
    obtain ⟨c, hc, hcu, hjc⟩ := _root_.GlobalTheory.T.rational_jet_move_exists hPr hInp ch hIs p hp _ _ κ₂ hj₂ r r' hr hr'
    refine ⟨c * κ₂, GlobalTheory.FamilyTieProof.mod1All_mul' hc hm₂, fun q hq hf => unitAt_mul hc hm₂ ?_ (hu₂ q hq hf), ?_⟩
    · obtain ⟨hqx, hqy⟩ := hQx q hq
      rw [mul_assoc] at hqx hqy
      exact @hcu q hf (hsx q hq) (hsy q hq) hqx hqy
    · rw [mul_assoc, mul_assoc]
      exact hjc
  obtain ⟨κ₀, hm, -, hj⟩ := chain ∅ (by simp) (by simp)
  refine ⟨κ₀, hm, fun q hf hx hy lam => ?_, hj⟩
  obtain ⟨κq, -, hu, hjq⟩ := chain {q} (by simpa using hf.out) (by simpa using ⟨hx, hy⟩)
  obtain rfl := _root_.GlobalTheory.MovedKappaEx.jet_kappa_unique hPr hInp ch hIs p hp x y κ₀ κq hj hjq
  exact hu q (Finset.mem_singleton_self q) hf lam
end GlobalTheory.MovedKappaEx
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unique_moved_kappa_jet : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ₀ : ℂ, Mod1All κ₀ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ₀‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ₀ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  first | exact @_root_.GlobalTheory.MovedKappaEx.exists_moved_kappa | exact _root_.GlobalTheory.MovedKappaEx.exists_moved_kappa | (intros; apply _root_.GlobalTheory.MovedKappaEx.exists_moved_kappa <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
namespace GlobalTheory.MovedKappaArith
end GlobalTheory.MovedKappaArith
namespace GlobalTheory.MovedKappaArith
theorem movedKappa_unique : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∀ κ κ' : ℂ, (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)) → (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ' * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)) → κ = κ' := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y κ κ' h1 h2
  set F := Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) with hFdef
  have hF : Differentiable ℂ F :=
    _root_.GlobalTheory.MovedDict.Entire.differentiable_moved_operator_eval hPr hInp ch hIs p hp x y
  obtain ⟨hsd, hsd'⟩ := _root_.GlobalTheory.MovedSD.moved_series_decomposition hPr hInp ch hIs p hp x y
  have hF0 : F ≠ 0 := selfDualIntertwiner_baseVector_ne_zero ch.S.Z.crv ch.S.Z.pt0 (ch.S.Z.e0_is p hp) hsd hsd'
  obtain ⟨α, hα⟩ := GlobalTheory.NatFamily.exists_taylor_ne D hF hF0
  have e := (h1 α).symm.trans (h2 α)
  rw [applyAt0_monomial, applyAt0_monomial, GlobalTheory.ProdThetaConj.taylor_const_mul hF,
    GlobalTheory.ProdThetaConj.taylor_const_mul hF] at e
  have e' := (opp p).injective (mul_left_cancel₀ (ch.S.Z.c0 p).ne_zero e)
  have hP : (α.prod fun v e => period ch.S.Z.δ v.1 ^ e) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (GlobalTheory.FunObj.period_ne_zero (GlobalTheory.TwoTorsionPt.delta_ne ch.S.Z.crv) v.1)
  have hfac : (α.prod fun _ n => (n.factorial : ℂ)) ≠ 0 :=
    Finsupp.prod_ne_zero_iff.2 fun _ _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
  have e'' := mul_left_cancel₀ (mul_ne_zero hP hfac) (by simpa only [mul_assoc] using e')
  exact mul_right_cancel₀ hα e''
end GlobalTheory.MovedKappaArith
namespace GlobalTheory.MovedKappaArith
theorem movedKappa_arithmetic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∀ κ : ℂ, (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)) →
    Mod1All κ ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y κ hj
  obtain ⟨κ₀, hm, hu, hj₀⟩ := _root_.GlobalTheory.T.exists_unique_moved_kappa_jet hPr hInp ch hIs p hp x y
  obtain rfl := _root_.GlobalTheory.MovedKappaArith.movedKappa_unique hPr hInp ch hIs p hp x y κ κ₀ hj hj₀
  exact ⟨hm, hu⟩
end GlobalTheory.MovedKappaArith
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedKappa_rational_of_arithmetic : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∀ κ : ℂ, (∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z)) →
    Mod1All κ ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) := by
  first | exact @_root_.GlobalTheory.MovedKappaArith.movedKappa_arithmetic | exact _root_.GlobalTheory.MovedKappaArith.movedKappa_arithmetic | (intros; apply _root_.GlobalTheory.MovedKappaArith.movedKappa_arithmetic <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.MovedKappaFockJetsSpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedKappa
theorem fock_jets_of_moved_vacuum : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ : ℂ, ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  intro hP hI D Γ _ _ Pl0 T A Ks _ _ _ R ch hch p hp x y
  have hC := ch.S.Z.crv
  have hδ : ch.S.Z.δ ≠ 0 := GlobalTheory.InertSign.delta_ne_zero hC
  have he0 := ch.S.Z.e0_is p hp
  have hsd := _root_.GlobalTheory.T.twisted_moved_series_decomposition hP hI ch hch p hp x y
  have hvac := _root_.GlobalTheory.T.twisted_moved_vacuum_integral hP hI ch hch p hp x y
  have hc0 : (ch.S.Z.c0 p : ℂ) ≠ 0 := Units.ne_zero _
  cases p with
  | chi i j =>
    obtain ⟨hi, rfl⟩ := hp
    have hconj := GlobalTheory.T.isVacuum_conj_of_negHermitianSpace ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) _ _ _ hvac
    obtain ⟨Θ, hΘ, hΘ0, hjet⟩ := fock_jets_moved ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.fr (.grid (i + 1) D.R.m)) (ch.S.N.fr (.grid i D.R.m))
      (ch.S.N.fr_on _ ⟨hi, rfl⟩) (ch.S.N.fr_on _ ⟨by omega, rfl⟩)
      (ch.W.cart_is _ ⟨hi, le_rfl⟩) (ch.W.cart_is _ ⟨by omega, le_rfl⟩) ch.S.Z.δ hC hδ _ _ hsd.1 hsd.2 _ hconj
    obtain ⟨κ, hκ, hd⟩ := intertwining_mem_ne_zero hC ch.S.Z.pt0 he0 hsd.1 hsd.2 hΘ hΘ0
    refine ⟨κ / starRingEnd ℂ (ch.S.Z.c0 (.chi i D.R.m) : ℂ), fun k => ?_⟩
    have h2 := fun f => GlobalTheory.T.fockVector_negHermitianSpace_conj_monomial ch.W.ψ ch.W.θ (ch.G.V (.grid (i + 1) D.R.m)) (ch.G.V (.grid i D.R.m))
      (ch.W.cart (.grid (i + 1) D.R.m)) (ch.W.cart (.grid i D.R.m)) (ch.S.N.frC (.grid (i + 1) D.R.m))
      (ch.S.N.frC (.grid i D.R.m)) f ch.W.ψ_std ch.W.θ_is k 0
    show pureTensorO _ _ _ _ _ _ _ _ _ _ 0 = _
    rw [h2]
    have hj := hjet k
    erw [hj]
    rw [hκ, applyAt0_const_mul D _ hd, applyAt0_const_mul D _ hd]
    show starRingEnd ℂ _ = _ * starRingEnd ℂ _
    simp only [map_mul, map_div₀, Complex.conj_conj]
    have hc0' : starRingEnd ℂ (ch.S.Z.c0 (.chi i D.R.m) : ℂ) ≠ 0 := (map_ne_zero _).2 hc0
    field_simp
  | mu t i j => exact absurd hp id
  | core i => exact absurd hp id
  | top t j =>
    have hj1 : j + 1 ≤ D.R.m := hp
    obtain ⟨Θ, hΘ, hΘ0, hjet⟩ := fock_jets_moved ch.W.ψ ch.W.θ (ch.G.V (.top j)) (ch.G.V (.top (j + 1)))
      (ch.W.cart (.top j)) (ch.W.cart (.top (j + 1))) (ch.S.N.fr (.top j)) (ch.S.N.fr (.top (j + 1)))
      (ch.S.N.fr_on (.top j) (by show j ≤ D.R.m; omega)) (ch.S.N.fr_on (.top (j + 1)) hj1)
      (ch.W.cart_is (.top j) (by show j ≤ D.R.m; omega)) (ch.W.cart_is (.top (j + 1)) hj1) ch.S.Z.δ hC hδ _ _ hsd.1 hsd.2 _ hvac
    obtain ⟨κ, hκ, hd⟩ := intertwining_mem_ne_zero hC ch.S.Z.pt0 he0 hsd.1 hsd.2 hΘ hΘ0
    refine ⟨κ / (ch.S.Z.c0 (.top t j) : ℂ), fun k => ?_⟩
    show pureTensorO _ _ _ _ _ _ _ _ _ _ 0 = _
    erw [hjet k]
    rw [hκ, applyAt0_const_mul D _ hd, applyAt0_const_mul D _ hd]
    show _ = _ * RingHom.id ℂ _
    rw [RingHom.id_apply]
    field_simp
end GlobalTheory.MovedKappa
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.movedKappa_fock_jets_span : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ : ℂ, ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  first | exact @_root_.GlobalTheory.MovedKappa.fock_jets_of_moved_vacuum | exact _root_.GlobalTheory.MovedKappa.fock_jets_of_moved_vacuum | (intros; apply _root_.GlobalTheory.MovedKappa.fock_jets_of_moved_vacuum <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
namespace GlobalTheory.MovedDict
theorem moved_vacuum_kappa_eval : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ : ℂ, Mod1All κ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  intro hPr hInp D Γ _ _ Pl0 T A Ks _ _ _ R ch hIs p hp x y
  obtain ⟨κ, hj⟩ := _root_.GlobalTheory.T.movedKappa_fock_jets_span hPr hInp ch hIs p hp x y
  obtain ⟨hm, hu⟩ := _root_.GlobalTheory.T.movedKappa_rational_of_arithmetic hPr hInp ch hIs p hp x y κ hj
  exact ⟨κ, hm, hu, hj⟩
end GlobalTheory.MovedDict
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_moved_vacuum_kappa : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → ∀ {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 T : Type}
    {A : FamIn D.what₂.LL Γ Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    (ch : Choice R), ch.Is → ∀ (p : Pair T), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big),
    ∃ κ : ℂ, Mod1All κ ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ * Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) (GlobalTheory.MovedDict.srcLat ch.S.toGridChoice p x y) (GlobalTheory.MovedDict.tgtLat ch.S.toGridChoice p x y)) (ch.S.Z.e0 p) z) := by
  first | exact @_root_.GlobalTheory.MovedDict.moved_vacuum_kappa_eval | exact _root_.GlobalTheory.MovedDict.moved_vacuum_kappa_eval | (intros; apply _root_.GlobalTheory.MovedDict.moved_vacuum_kappa_eval <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
namespace GlobalTheory.MovedDict
theorem moved_vacuum_vector_correspondence : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (p : Pair _), DefPair D.R.m p →
    ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E))
    (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E)) (κ : ℂ), SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧
    Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) →
      EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) Ls) (inV (frT ch.S.N p) Lt)
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) ∧
    (∀ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True),
      actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w ∈
        latO _ _ (inV (frS ch.S.N p) Ls) (inV (frT ch.S.N p) Lt) (fun _ => True)) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ *
            Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
              (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p) z) := by
  intro hPr hInp
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F _ ch hIs _ => ?_⟩⟩
  intro p hp x y
  obtain ⟨hSs, hSt⟩ := _root_.GlobalTheory.T.twisted_moved_series_decomposition hPr hInp ch hIs p hp x y
  obtain ⟨κ, hκ, hu, hj⟩ := _root_.GlobalTheory.T.twisted_moved_vacuum_kappa hPr hInp ch hIs p hp x y
  refine ⟨_, _, κ, hSs, hSt, hκ, _root_.GlobalTheory.T.twisted_moved_operator_entire hPr hInp ch hIs p hp x y, ?_, _root_.GlobalTheory.T.twisted_moved_vacuum_integral hPr hInp ch hIs p hp x y,
    (_root_.GlobalTheory.T.twisted_moved_lattice_action hPr hInp ch hIs p hp x y).1, hj⟩
  intro q _ hx hy
  refine ⟨?_, ?_, hu q hx hy⟩
  · rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩ <;> first | exact hy | exact hx
  · rcases p with ⟨i, j⟩ | ⟨t, i, j⟩ | i | ⟨t, j⟩ <;> first | exact hx | exact hy
end GlobalTheory.MovedDict
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_moved_vacuum_correspondence : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (p : Pair _), DefPair D.R.m p →
    ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E))
    (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E)) (κ : ℂ), SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧
    Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) ∧
    (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) →
      EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) →
      EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧
    IsVacO ch.W.ψ ch.W.θ _ _ (ch.G.cartS ch.W.cart p) (ch.G.onT ch.W.cart p) (inV (frS ch.S.N p) Ls) (inV (frT ch.S.N p) Lt)
      (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p)) ∧
    (∀ w ∈ latO _ _ (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True),
      actO _ _ (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).1 (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))).2 w ∈
        latO _ _ (inV (frS ch.S.N p) Ls) (inV (frT ch.S.N p) Lt) (fun _ => True)) ∧
    ∀ k : FVar D (ch.G.pT p).rank (ch.G.pS p).rank →₀ ℕ,
      fockIn ch.W ch.S.N.frC p (ch.W.om p (ch.G.toPair p ((x * ch.S.N.u p.small : FinPt ch.G p.small) : Formalism.L2.Theta.GA D (ch.G.V p.small)) ((y * ch.S.N.u p.big : FinPt ch.G p.big) : Formalism.L2.Theta.GA D (ch.G.V p.big))) (ch.S.Z.vac p))
        (MvPolynomial.monomial k 1) 0 = ch.S.Z.c0 p * opp p ((k.prod fun v e => period ch.S.Z.δ v.1 ^ e) *
          Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial k 1) fun z => κ *
            Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _)
              (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p) z) := by
  first | exact @_root_.GlobalTheory.MovedDict.moved_vacuum_vector_correspondence | exact _root_.GlobalTheory.MovedDict.moved_vacuum_vector_correspondence | (intros; apply _root_.GlobalTheory.MovedDict.moved_vacuum_vector_correspondence <;> assumption)
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open scoped TensorProduct
open GlobalTheory.MovedDict Formalism.L2.Ker GlobalTheory.SignedHC
noncomputable section
namespace GlobalTheory.MovedDict
theorem jets_moved_by_translation : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (p : Pair _), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E)) (κ : ℂ), SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧ ∀ (k : ℕ), 0 < k → ∀ w : WO (ch.G.pS p) (ch.G.pT p), k • w ∈ latO (ch.G.pS p) (ch.G.pT p) (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True) → ∃ (ζ : Qbar) (s : VC D (ch.G.pS p).rank (ch.G.pT p).rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ k • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt ∧ ∀ mon, jetTab ch.W ch.S.N.frC p (heisO ch.W.ψ (ch.G.pS p) (ch.G.pT p) w (ch.S.Z.vac p)) (x * ch.S.N.u _) (y * ch.S.N.u _) mon = ch.S.Z.c0 p * opp p (((mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) 1) fun z => κ * ((ζ : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) s (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) z)) := by
  intro hPr hInp
  obtain ⟨CF0, h2⟩ := _root_.GlobalTheory.T.twist_moved_vacuum_correspondence hPr hInp
  refine ⟨CF0, fun ε CF hCF => ?_⟩
  obtain ⟨x₀, hx⟩ := h2 ε CF hCF
  refine ⟨x₀, fun D large₂ hε hx₀ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs hAt => ?_⟩
  intro p hp x y
  obtain ⟨Ls, Lt, κ, hSs, hSt, hκ, hd, hq, hvac, hmov, hjet⟩ := hx D large₂ hε hx₀ Γ Pl0 T A Ks R F hS ch hIs hAt p hp x y
  refine ⟨Ls, Lt, κ, hSs, hSt, hκ, hd, hq, fun n hn w hw => ?_⟩
  obtain ⟨ζ, s, hζ, hs, hj⟩ := GlobalTheory.T.finiteHeisenbergTranslate_selfDualVacuum_fockJets ch.S.toGridChoice p hp Ls Lt κ _ hSs hSt hd hvac hjet n hn _
    (by rw [← actO_nsmul]; exact hmov _ hw)
  refine ⟨ζ, s, hζ, hs, fun mon => ?_⟩
  rw [jetTab_heisO ch.W ch.S.N.frC p hp _ (ch.S.Z.vac_is p hp).2.theta w _ _ mon]
  exact hj _
end GlobalTheory.MovedDict
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.translated_jets_dictionary : _root_.GlobalTheory.FunPr.ThetaLocalInputs → (∀ D, GlobalTheory.NormSum.Inp D) → Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ (p : Pair _), DefPair D.R.m p → ∀ (x : FinPt ch.G p.small) (y : FinPt ch.G p.big), ∃ (Ls : Submodule (𝓞 D.host.E) (Fin (ch.G.pS p).rank → D.host.E)) (Lt : Submodule (𝓞 D.host.E) (Fin (ch.G.pT p).rank → D.host.E)) (κ : ℂ), SD D Ls ∧ SD D Lt ∧ Mod1All κ ∧ Differentiable ℂ (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) ∧ (∀ (q : ℕ) [Fact q.Prime], EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.small x) (stdL D _) → EqAt D q (GlobalTheory.SumSize.latAt ch.S.toGridChoice p.big y) (stdL D _) → EqAt D q Ls (stdL D _) ∧ EqAt D q Lt (stdL D _) ∧ ∀ lam : Qbar →+* ℂ_[q], ‖lamC lam κ‖ = 1) ∧ ∀ (k : ℕ), 0 < k → ∀ w : WO (ch.G.pS p) (ch.G.pT p), k • w ∈ latO (ch.G.pS p) (ch.G.pT p) (ch.S.N.latS p : Set _) (ch.S.N.latT p : Set _) (fun _ => True) → ∃ (ζ : Qbar) (s : VC D (ch.G.pS p).rank (ch.G.pT p).rank), (∃ m : ℕ, 0 < m ∧ ζ ^ m = 1) ∧ k • s ∈ Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt ∧ ∀ mon, jetTab ch.W ch.S.N.frC p (heisO ch.W.ψ (ch.G.pS p) (ch.G.pT p) w (ch.S.Z.vac p)) (x * ch.S.N.u _) (y * ch.S.N.u _) mon = ch.S.Z.c0 p * opp p (((mon.mapDomain (fvar ch.G p)).prod fun v e => period ch.S.Z.δ v.1 ^ e) * Formalism.MainNotions.GL3Theta.applyAt0 D (MvPolynomial.monomial (mon.mapDomain (fvar ch.G p)) 1) fun z => κ * ((ζ : ℂ) * Formalism.MainNotions.TaylorLogMetric.U D (tor0 D D.host.ccK ch.S.Z.δ) s (Iop D (tor0 D D.host.ccK ch.S.Z.δ) (La0 D (tor0 D D.host.ccK ch.S.Z.δ) _ _) (Formalism.MainNotions.TaylorLogMetric.La D (tor0 D D.host.ccK ch.S.Z.δ) Ls Lt) (ch.S.Z.e0 p)) z)) := by
  first | exact @_root_.GlobalTheory.MovedDict.jets_moved_by_translation | exact _root_.GlobalTheory.MovedDict.jets_moved_by_translation | (intros; apply _root_.GlobalTheory.MovedDict.jets_moved_by_translation <;> assumption)
end
