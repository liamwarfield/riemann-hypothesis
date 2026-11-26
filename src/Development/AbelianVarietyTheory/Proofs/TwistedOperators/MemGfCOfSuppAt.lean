module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeCharFiniteIdelesIsAlgebraicOfResEta
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CongruentPairsFixVacuumWeilDatum
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumFinitePairVacuumAlgebraicCombination
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBasisAtTransport
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteUnitaryPointsMemOfLevelAndSplitPlaceStatement
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnfoldingColumnArgsMovedPointConjAtPlace

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumIsAlgebraicCombinationDefiniteBottom
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumIsAlgebraicCombinationDefiniteBottom
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BotFourierSnd

open GlobalTheory.PlaceModel GlobalTheory.AlgWave GlobalTheory.BotFourier GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle

variable {D : D7}

theorem unitChar_mem {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) {k : ℕ} {N : Matrix (Fin k) (Fin k) (Lev.EAf D)} (hN : IsIntM N) : unitChar ν e N ∈ Qb := by
  obtain ⟨-, -, -, m, hm, hord⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  unfold unitChar
  split_ifs with hu
  · obtain ⟨h1, h2, h3⟩ := hu.choose_spec
    have hdet : N.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
      let B : Matrix (Fin k) (Fin k) (Formalism.L2.Herm.intAf D.host.F D.host.E) := fun a b => ⟨_, hN a b⟩
      have hB : N = (Formalism.L2.Herm.intAf D.host.F D.host.E).subtype.mapMatrix B := rfl
      rw [hB, ← RingHom.map_det]
      exact (B.det).2
    have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
    have hfu : Formalism.L2.Pj.FinUnit hu.choose := ⟨h1, GlobalTheory.PlaceDatum.finPart_mem_of_toEAf (by
      rw [h2]; exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hdet)), GlobalTheory.PlaceDatum.finPart_mem_of_toEAf h3⟩
    have hpow := hord _ hfu
    refine mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow (n := m) hm ?_)
    have e1 : (((ν hu.choose)⁻¹ : Circle) : ℂ) ^ m = Circle.coeHom (((ν hu.choose) ^ m)⁻¹) := by
      rw [← inv_pow, map_pow]; rfl
    rw [e1, hpow, inv_one, map_one]
    exact isAlgebraic_one
  · exact zero_mem _

theorem stdSnd_mem {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)}
    (he : IsIdemSum e S) (I : Ideal (𝓞 D.host.E)) (a : ℕ) (A' WW : HSp D) (βA : GL (Fin A'.rank) (Lev.EAf D))
    (βW : GL (Fin WW.rank) (Lev.EAf D)) (x : WO A' WW) : stdSnd ν e I a A' WW βA βW x ∈ Qb := by
  unfold stdSnd
  split_ifs with hc
  · exact unitChar_mem hν he (GlobalTheory.CompanionTheory.StdSndTheta.isIntM_rightBlock hc.2.1)
  · exact zero_mem _


set_option maxHeartbeats 2000000 in
theorem isAlgComb_of_isThetaAt {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1)) {S WW : HSp D}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)}
    (hSd : IsSelfDualC S ΛS) (hWd : IsSelfDualC WW ΛT) {e : AE D} (hee : e * e = e) (hinf : infPart D e = 0)
    {vac Φ f : WO S WW → ℂ} (hSB : IsSBHalf e (latO S WW ΛS ΛT fun _ => True) Φ) (hΦ : ∀ x, Φ x ∈ Qb)
    (hth : IsThetaAt ψ (symplO S WW) (heisO ψ S WW) e (latO S WW ΛS ΛT fun _ => True) 1 vac Φ f) :
    GlobalTheory.MovedAlg.IsAlgComb ψ S WW vac f := by
  classical
  have hinf' := GlobalTheory.PlaceDatum.infPart_cA hinf
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := hth
  rw [hall Tm hTm]
  set Λ : AddSubgroup (WO S WW) := latO S WW ΛS ΛT fun _ => True with hΛ

  have hdual := (GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S WW ΛS ΛT hψ hSd hWd).1
  have hfin := GlobalTheory.LatFinMod.latO_finite_mod D S WW _ _ hSd.1.fg hWd.1.fg fun _ => True
  have he' : cA D e * cA D e = cA D e := by rw [← RingHom.map_mul, hee]
  have hsm : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ ⊓ half S WW a := fun a ha u hu =>
    AddSubgroup.mem_inf.2 ⟨GlobalTheory.LatticeStable.smul_mem_latO D S WW _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha])) u hu, by rw [mem_half, smul_smul, ha]⟩
  have finX : ∀ x ∈ half S WW e, x.map (infPart D) = 0 := fun x hx =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf ((isHalf_iff S WW).2 hx)
  have finY : ∀ y ∈ half S WW (cA D e), y.map (infPart D) = 0 := fun y hy =>
    GlobalTheory.PlaceDatum.infPart_of_half hinf' ((isHalf_iff S WW).2 hy)
  have tf : ∀ k : ℕ, 0 < k → Function.Injective fun t : WO S WW => k • t := fun k hk a b hab => by
    rw [← inv_smul_nsmul S WW hk a, ← inv_smul_nsmul S WW hk b]
    exact congrArg _ hab
  have hb : IsBichar (fun x y : WO S WW => ψ (symplO S WW x y)) := by
    have hl (a b y : WO S WW) : symplO S WW (a + b) y = symplO S WW a y + symplO S WW b y := by
      unfold symplO hO
      simp only [Matrix.add_apply, mul_add, Finset.sum_add_distrib, map_add (f := _)]
    have hr (x a b : WO S WW) : symplO S WW x (a + b) = symplO S WW x a + symplO S WW x b := by
      unfold symplO hO
      simp only [Matrix.add_apply, mul_add, add_mul, Finset.sum_add_distrib, map_add (f := _)]
    have hz₁ (y : WO S WW) : symplO S WW 0 y = 0 := by simpa using hl 0 0 y
    have hz₂ (y : WO S WW) : symplO S WW y 0 = 0 := by simpa using hr y 0 0
    exact ⟨fun a b y => by rw [hl, AddChar.map_add_eq_mul],
      fun a b y => by rw [hr, AddChar.map_add_eq_mul],
      fun y => by rw [hz₁, AddChar.map_zero_eq_one],
      fun y => by rw [hz₂, AddChar.map_zero_eq_one]⟩

  obtain ⟨h1, k, hk, h2, h3⟩ := hSB
  have hmem := mem_algSpan (χ := fun x y : WO S WW => ψ (symplO S WW x y)) (X := half S WW e)
    (Y := half S WW (cA D e)) (L := Λ ⊓ half S WW e) (L' := Λ ⊓ half S WW (cA D e)) hb
    (fun x hx y hy => psi_mem hψ hSd hWd (finX x hx) (finY y hy)) inf_le_right inf_le_right
    (fun u hu y hy => (hdual u (finX u hu.2)).1 hu.1 y hy.1)
    (fun x hx h => ⟨(hdual x (finX x hx)).2 fun u hu => by
      have := h _ (hsm _ he' u hu)
      rwa [← symplO_smul, (mem_half S WW).1 hx] at this, hx⟩)
    (half_div S WW e) (half_div S WW _) tf
    (fun k hk => by
      obtain ⟨R, hR, h⟩ := hfin k hk
      refine ⟨(fun r => e • r) '' R, hR.image _, fun t ht => ?_⟩
      obtain ⟨r, hr, u, hu, htr⟩ := h t ht.1
      refine ⟨_, ⟨r, hr, rfl⟩, e • u, hsm e hee u hu, ?_⟩
      have := (mem_half S WW).1 ht.2
      rw [← this, htr, smul_add, smul_comm e k u])
    _ hΦ (fun t ht => (isHalf_iff S WW).1 (h1 t ht)) k hk
    (fun u hu => h2 u hu.1 ((isHalf_iff S WW).2 hu.2))
    (fun t ht => ⟨h3 t ht, (half S WW e).nsmul_mem ((isHalf_iff S WW).1 (h1 t ht)) _⟩)

  set V : Submodule Qb (WO S WW → ℂ) := Submodule.span Qb
    {F | ∃ w : WO S WW, w.map (infPart D) = 0 ∧ F = heisO ψ S WW w vac} with hV
  have hvac : Tm (halfInd e Λ) = vac := by simpa using hTm.vac
  have s0 := GlobalTheory.isSBHalf_halfInd e Λ
  have hT : ∀ Ψ ∈ algSpan (fun x y : WO S WW => ψ (symplO S WW x y)) (half S WW e) (half S WW (cA D e))
      (Λ ⊓ half S WW e), Tm Ψ ∈ V := by
    intro Ψ hΨ
    induction hΨ using Submodule.span_induction with
    | mem _ hh =>
      obtain ⟨x, hx, y, hy, rfl⟩ := hh
      have s1 : IsSBHalf e Λ fun t => ψ (symplO S WW t y) * halfInd e Λ t := by
        obtain ⟨k, hk, hk'⟩ := GlobalTheory.PlaceDatum.exists_nsmul_mem_latO' (S := S) (T := WW)
          (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hSd)
          (GlobalTheory.FinPl.PlacesAdeles.selfDual_isFull _ _ hWd) y (finY y hy)
        obtain ⟨a1, k', hk1, a2, a3⟩ := s0
        refine ⟨fun t ht => a1 t (right_ne_zero_of_mul ht), k * k', Nat.mul_pos hk hk1, fun u hu hh t => ?_,
          fun t ht => ?_⟩
        · have e1 : halfInd e Λ (t + (k * k') • u) = halfInd e Λ t := by
            rw [mul_nsmul]
            exact a2 _ (nsmul_mem hu k) ((isHalf_iff S WW).2 (nsmul_mem ((isHalf_iff S WW).1 hh) k)) t
          have e2 : ψ (symplO S WW ((k * k') • u) y) = 1 := by
            rw [mul_nsmul']
            refine (hb.nsmul k _ y).trans ((hdual _ (finX _ (nsmul_mem ((isHalf_iff S WW).1 hh) k'))).1
              (nsmul_mem hu k') _ hk')
          simp only [e1, symplO_add_left, AddChar.map_add_eq_mul, e2, mul_one]
        · rw [mul_nsmul']
          exact nsmul_mem (a3 t (right_ne_zero_of_mul ht)) k
      have e1 : wave (fun x y : WO S WW => ψ (symplO S WW x y)) (Λ ⊓ half S WW e) x y =
          fun t => (fun t => ψ (symplO S WW t y) * halfInd e Λ t) (t + x) := by
        rw [halfInd_eq_ind]; rfl
      rw [e1, hTm.trans _ s1 x ((isHalf_iff S WW).2 hx), hTm.modul _ s0 y ((isHalf_iff S WW).2 hy), hvac]
      have e2 : heisO ψ S WW x (heisO ψ S WW y vac) =
          ψ (symplOH S WW x y) • heisO ψ S WW (x + y) vac := heisL_heisL S WW ψ x y vac
      rw [e2]
      refine smul_mem_of_mem (psiH_mem hψ hSd hWd (finX x hx) (finY y hy)) (Submodule.subset_span ⟨x + y, ?_, rfl⟩)
      refine Matrix.ext fun a b => ?_
      have q1 : infPart D (x a b) = 0 := congrFun (congrFun (finX x hx) a) b
      have q2 : infPart D (y a b) = 0 := congrFun (congrFun (finY y hy) a) b
      change infPart D (x a b + y a b) = 0
      rw [RingHom.map_add (f := _), q1, q2, add_zero]
    | zero => rw [map_zero]; exact zero_mem _
    | add f g _ _ hf hg => rw [map_add]; exact add_mem hf hg
    | smul c f _ hf =>
      change Tm ((c : ℂ) • f) ∈ V
      rw [map_smul]
      exact V.smul_mem c hf
  obtain ⟨n, f, g, hfg⟩ := (Submodule.mem_span_set').1 (hT _ hmem)
  choose w hw hgw using fun p => (g p).2
  refine ⟨n, fun p => (f p : ℂ), w, fun p => mem_algebraicClosure_iff.1 (f p).2, hw, ?_⟩
  rw [← hfg]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← hgw p]
  rfl

theorem frMapAdj_nsmul (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (k : ℕ)
    (x : WO A' WW) : frMapAdj A' WW βA' βW (k • x) = k • frMapAdj A' WW βA' βW x :=
  map_nsmul (AddMonoidHom.mk' (frMapAdj A' WW βA' βW) (GlobalTheory.PlaceVec.frMapAdj_add A' WW βA' βW)) k x

theorem dualCoord_apply (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (x : WO A' WW)
    (i j) : dualCoord A' WW βA' βW x i j = eToEAf D D.host.xi0 * frMapAdj A' WW βA' βW x i j := rfl

theorem dualCoord_add (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (x y : WO A' WW) :
    dualCoord A' WW βA' βW (x + y) = dualCoord A' WW βA' βW x + dualCoord A' WW βA' βW y := by
  ext i j
  rw [Matrix.add_apply, dualCoord_apply, dualCoord_apply, dualCoord_apply, GlobalTheory.PlaceVec.frMapAdj_add, Matrix.add_apply,
    mul_add]

theorem dualCoord_nsmul (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D)) (βW : GL (Fin WW.rank) (EAf D)) (k : ℕ)
    (x : WO A' WW) : dualCoord A' WW βA' βW (k • x) = k • dualCoord A' WW βA' βW x :=
  map_nsmul (AddMonoidHom.mk' (dualCoord A' WW βA' βW) (dualCoord_add A' WW βA' βW)) k x

theorem exists_den_dualCoord {A' WW : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)} (hS : ΛS.FG) (hT : ΛT.FG) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) : ∃ M : ℕ, 0 < M ∧
      ∀ u ∈ latO A' WW (ΛS : Set (Fin A'.rank → D.host.E)) (ΛT : Set (Fin WW.rank → D.host.E)) (fun _ => True),
        ∀ i j, (M : EAf D) * dualCoord A' WW βA' βW u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  obtain ⟨k₃, hk₃, h₃⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := A') (T := WW) hS hT
  obtain ⟨k₁, hk₁, h₁⟩ := GlobalTheory.PlaceVec.frMapAdj_up A' WW βA' βW
  obtain ⟨d, hd, hξ⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_int (eToEAf D D.host.xi0)
  refine ⟨d * k₁ * k₃, by positivity, fun u hu i j => ?_⟩
  have h1 := h₁ (k₃ • u) (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₃ u hu) i j
  have e : ((d * k₁ * k₃ : ℕ) : EAf D) * dualCoord A' WW βA' βW u i j =
      (d • eToEAf D D.host.xi0) * (k₁ • frMapAdj A' WW βA' βW (k₃ • u)) i j := by
    rw [frMapAdj_nsmul, dualCoord_apply, Matrix.smul_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul]
    push_cast
    ring
  rw [e]
  exact mul_mem hξ h1

theorem exists_mul_dualCoord {A' WW : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)} (hS : Submodule.IsFullLattice D.host.E ΛS)
    (hT : Submodule.IsFullLattice D.host.E ΛT) {a : AE D} (hinf : infPart D a = 0) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) : ∃ K : ℕ, 0 < K ∧ ∀ t : WO A' WW, IsHalf a t → IsIntM (dualCoord A' WW βA' βW t) →
      K • t ∈ latO A' WW (ΛS : Set (Fin A'.rank → D.host.E)) (ΛT : Set (Fin WW.rank → D.host.E)) (fun _ => True) := by
  obtain ⟨m, hm, hξ⟩ := GlobalTheory.PlaceVec.exists_nsmul_mem_int (eToEAf D D.host.xi0⁻¹)
  obtain ⟨k₂, hk₂, h₂⟩ := GlobalTheory.PlaceVec.frMapAdj_down A' WW βA' βW
  obtain ⟨k₄, hk₄, h₄⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT (S := A') (T := WW)
  refine ⟨k₄ * (k₂ * m), by positivity, fun t ht hi => ?_⟩
  have hF : IsIntM (frMapAdj A' WW βA' βW (m • t)) := fun i j => by
    have e : frMapAdj A' WW βA' βW (m • t) i j = (m • eToEAf D D.host.xi0⁻¹) * dualCoord A' WW βA' βW t i j := by
      rw [frMapAdj_nsmul, dualCoord_apply, Matrix.smul_apply, nsmul_eq_mul, nsmul_eq_mul, mul_assoc, ← mul_assoc (eToEAf D _),
        ← RingHom.map_mul, inv_mul_cancel₀ (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D), RingHom.map_one, one_mul]
    rw [e]
    exact mul_mem hξ (hi i j)
  have h3 := h₄ (k₂ • m • t)
    (GlobalTheory.PlaceVec.half_infPart hinf (nsmul_mem (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A' WW).1 ht) _) _))
    (by rw [GlobalTheory.PlaceVec.map_toEAf_nsmul]; exact h₂ _ hF)
  rwa [smul_smul, smul_smul, mul_assoc] at h3

theorem isIntM_rightBlock {k d a : ℕ} {Y : Matrix (Fin k) (Fin d) (EAf D)} (h : IsIntM Y) : IsIntM (rightBlock a Y) :=
  fun i j => by
    unfold rightBlock
    split_ifs
    · exact h _ _
    · exact zero_mem _

theorem rightBlock_shift {k d a : ℕ} {Y Y' W : Matrix (Fin k) (Fin d) (EAf D)} {c : EAf D}
    (h : ∀ i j, Y' i j = Y i j + c * W i j) (i j : Fin k) :
    rightBlock a Y' i j = rightBlock a Y i j + c * rightBlock a W i j := by
  unfold rightBlock
  split_ifs
  · exact h _ _
  · rw [mul_zero, add_zero]


set_option maxHeartbeats 1000000 in
theorem stdSnd_shift {ν : (AE D)ˣ →* Circle} {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} {n₀ n c : ℕ} (hn₀ : ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I)
    (hl : ∀ x, Formalism.L2.Pj.FinUnit x → (∃ y ∈ intAE D, finPart D (x : AE D) - 1 = n • y) → ν x = 1)
    (hc : ∀ P ∈ S, ((c : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) (a : ℕ) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) {t t' : WO A' WW} (hh : IsHalf (cA D e) t' ↔ IsHalf (cA D e) t)
    {W : Matrix (Fin A'.rank) (Fin WW.rank) (EAf D)} (hW : IsIntM W)
    (h : ∀ i j, dualCoord A' WW βA' βW t' i j = dualCoord A' WW βA' βW t i j + ((n₀ * (n * c) : ℕ) : EAf D) * W i j) :
    stdSnd ν e I a A' WW βA' βW t' = stdSnd ν e I a A' WW βA' βW t := by
  have hW1 : ∀ i j, ((n * c : ℕ) : EAf D) * W i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j => mul_mem (natCast_mem _ _) (hW i j)
  have hW2 : ∀ i j, (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := fun i j => mul_mem (natCast_mem _ _) (hW1 i j)
  have ha : ∀ i j, dualCoord A' WW βA' βW t' i j =
      dualCoord A' WW βA' βW t i j + (n₀ : EAf D) * (((n * c : ℕ) : EAf D) * W i j) := fun i j => by
    rw [h, Nat.cast_mul n₀, mul_assoc]
  have hb : ∀ i j, dualCoord A' WW βA' βW t i j =
      dualCoord A' WW βA' βW t' i j + (n₀ : EAf D) * (-(((n * c : ℕ) : EAf D) * W i j)) := fun i j => by
    rw [ha, mul_neg, add_neg_cancel_right]
  have hint : IsIntM (dualCoord A' WW βA' βW t') ↔ IsIntM (dualCoord A' WW βA' βW t) :=
    forall_congr' fun i => forall_congr' fun j => by
      rw [ha]
      exact add_mem_cancel_right (hW2 i j)
  have hid : (∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t' i j)) ↔
      ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t i j) :=
    ⟨fun H i j hj => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hn₀ (neg_mem (hW1 i j)) (hb i j) (H i j hj),
      fun H i j hj => StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.inId_shift hn₀ (hW1 i j) (ha i j) (H i j hj)⟩
  unfold stdSnd
  by_cases hcnd : IsHalf (cA D e) t ∧ IsIntM (dualCoord A' WW βA' βW t) ∧
      ∀ i j, j.1 < a → InId I (dualCoord A' WW βA' βW t i j)
  · rw [if_pos hcnd, if_pos ⟨hh.2 hcnd.1, hint.2 hcnd.2.1, hid.2 hcnd.2.2⟩]
    refine (StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.unitChar_congr he hl hc (isIntM_rightBlock hcnd.2.1)
      (Z := rightBlock a fun i j => (n₀ : EAf D) * W i j) (isIntM_rightBlock fun i j => mul_mem (natCast_mem _ _) (hW i j))
      (rightBlock_shift (c := ((n * c : ℕ) : EAf D)) fun i j => ?_)).symm
    rw [h, Nat.cast_mul n₀]
    ring
  · rw [if_neg hcnd, if_neg fun h' => hcnd ⟨hh.1 h'.1, hint.1 h'.2.1, hid.1 h'.2.2⟩]


set_option maxHeartbeats 1000000 in
theorem stdSnd_isSB {ν : (AE D)ˣ →* Circle} (hν : Continuous ν) {e : AE D} {S : Finset (Pl D.host.E)} (he : IsIdemSum e S)
    {I : Ideal (𝓞 D.host.E)} (hI : I ≠ ⊥) (a : ℕ) (A' WW : HSp D) (βA' : GL (Fin A'.rank) (EAf D))
    (βW : GL (Fin WW.rank) (EAf D)) (Λ : AddSubgroup (WO A' WW))
    (hB : ∃ M : ℕ, 0 < M ∧ ∀ u ∈ Λ, ∀ i j, (M : EAf D) * dualCoord A' WW βA' βW u i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (hC : ∃ K : ℕ, 0 < K ∧ ∀ t : WO A' WW, IsHalf (cA D e) t → IsIntM (dualCoord A' WW βA' βW t) → K • t ∈ Λ) :
    IsSBHalf (cA D e) Λ (stdSnd ν e I a A' WW βA' βW) := by
  obtain ⟨M, hM, hB⟩ := hB
  obtain ⟨K, hK, hC⟩ := hC
  obtain ⟨n, hn, hl, -⟩ := GlobalTheory.CharFin.char_finUnit_finite_order D ν hν
  obtain ⟨n₀, hn₀, hnI⟩ : ∃ n₀ : ℕ, 0 < n₀ ∧ ((n₀ : ℕ) : 𝓞 D.host.E) ∈ I :=
    ⟨_, Nat.pos_of_ne_zero fun h => hI (Ideal.absNorm_eq_zero_iff.1 h), Ideal.absNorm_mem I⟩
  obtain ⟨c, hc, hcS⟩ := GlobalTheory.PlaceVec.exists_nat_mem_places S
  refine ⟨fun t ht => ?_, K * ((n₀ * (n * c)) * M), Nat.mul_pos hK (Nat.mul_pos (Nat.mul_pos hn₀ (Nat.mul_pos hn hc)) hM),
    fun u hu hh t => ?_, fun t ht => ?_⟩
  · unfold stdSnd at ht
    by_contra h
    exact ht (if_neg fun h' => h h'.1)
  · refine stdSnd_shift he hnI hl hcS a A' WW βA' βW
      (W := fun i j => (K : EAf D) * ((M : EAf D) * dualCoord A' WW βA' βW u i j))
      ?_ (fun i j => mul_mem (natCast_mem _ _) (hB u hu i j)) fun i j => ?_
    · rw [GlobalTheory.PlaceModel.isHalf_iff A' WW, GlobalTheory.PlaceModel.isHalf_iff A' WW]
      exact AddSubgroup.add_mem_cancel_right _ (nsmul_mem ((GlobalTheory.PlaceModel.isHalf_iff A' WW).1 hh) _)
    · rw [dualCoord_add, dualCoord_nsmul, Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
      push_cast
      ring
  · have h : IsHalf (cA D e) t ∧ IsIntM (dualCoord A' WW βA' βW t) := by
      unfold stdSnd at ht
      by_contra h
      exact ht (if_neg fun h' => h ⟨h'.1, h'.2.1⟩)
    rw [mul_nsmul]
    exact nsmul_mem (hC t h.1 h.2) _

theorem finDatum'_isAlgComb : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X →
    ∀ t : T, GlobalTheory.MovedAlg.IsAlgComb W.ψ A' WW X.vac' (X.f' t) := by
  intro D T L sc G W i j A A' WW X hX t
  have hI := hX.is
  have hν := (hI.weil' t).hecT
  have he := hI.idem t
  have hee := GlobalTheory.PlaceDatum.idemSum_mul_self he
  have hinf := GlobalTheory.PlaceDatum.infPart_cA (GlobalTheory.PlaceDatum.infPart_idemSum he)
  have hSd : IsSelfDualC A' X.rA'.Λ := hI.rigA'.1
  have hWd : IsSelfDualC WW X.rW.Λ := hI.rigW.1
  exact isAlgComb_of_isThetaAt hI.isVac'.1 hSd hWd (by rw [← RingHom.map_mul, hee]) hinf
    (stdSnd_isSB hν.1 he (GlobalTheory.ConstRatio.ideal_ne_bot X (locPl G) t) _ A' WW X.rA'.β X.rW.β _
      (exists_den_dualCoord hSd.1.fg hWd.1.fg X.rA'.β X.rW.β)
      (exists_mul_dualCoord (GlobalTheory.ProjXCols.selfDual_isFullLattice A' _ hSd)
        (GlobalTheory.ProjXCols.selfDual_isFullLattice WW _ hWd) hinf X.rA'.β X.rW.β))
    (fun x => stdSnd_mem hν.1 he _ _ A' WW X.rA'.β X.rW.β x) (hI.snd t)

end GlobalTheory.BotFourierSnd

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteDatumIsAlgebraicCombinationDefiniteBottomStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finiteDatum_isAlgebraicCombination_definiteBottom : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, IsBottomTri W i j X →
    ∀ t : T, GlobalTheory.MovedAlg.IsAlgComb W.ψ A' WW X.vac' (X.f' t) := by
  first | exact @GlobalTheory.BotFourierSnd.finDatum'_isAlgComb | exact GlobalTheory.BotFourierSnd.finDatum'_isAlgComb | (intros; apply GlobalTheory.BotFourierSnd.finDatum'_isAlgComb <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicInvariantFormVacuumSplitPlace
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicInvariantFormVacuumSplitPlace
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.SplitAlgForm

open GlobalTheory.SplitScalar GlobalTheory.LevelSeries.IdemSumForm GlobalTheory.AlgWave

theorem psi_ne_zero {G : Type} [AddGroup G] (ψ : AddChar G ℂ) (x : G) : ψ x ≠ 0 := by
  intro h
  have := ψ.map_add_eq_mul x (-x)
  rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
  exact one_ne_zero this

theorem fin_smul {D : D7} {m n : ℕ} (a : AE D) {x : Mx D m n} (hx : x.map (infPart D) = 0) :
    (a • x).map (infPart D) = 0 := by
  ext i j
  have : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
  show infPart D (a * x i j) = 0
  rw [RingHom.map_mul, this, mul_zero]

theorem fin_add {D : D7} {m n : ℕ} {x y : Mx D m n} (hx : x.map (infPart D) = 0) (hy : y.map (infPart D) = 0) :
    (x + y).map (infPart D) = 0 := by
  rw [Matrix.map_add _ (map_add (infPart D)), hx, hy, add_zero]


set_option maxHeartbeats 1000000 in
theorem exists_alg_form : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ e : Formalism.L2.Theta.AE D, IsSplitIdem D e → ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) →
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧
      ℓ v = 1 ∧ ∀ p, IsAlgebraic ℚ (ℓ (heisO ψ S T (w p) v)) := by
  intro D ψ θ S T sS sT ΛS ΛT v hv hS hT e he n w hw
  classical
  have hψ : IsStdChar D ψ (-1) := hv.1
  obtain ⟨hd, -, hsg⟩ := GlobalTheory.LatVac.latO_selfDual_approx_sign D ψ S T ΛS ΛT hψ hS hT
  set Λ : AddSubgroup (WO S T) := latO S T (ΛS : Set (Fin S.rank → D.host.E))
    (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛdef
  have hΛ : ∀ a : AE D, a * a = a → ∀ u ∈ Λ, a • u ∈ Λ := fun a ha =>
    GlobalTheory.LatticeStable.smul_mem_latO D S T _ _ _ a
      (GlobalTheory.AdIdem.idempotent_mem_intAE D _ (by rw [← RingHom.map_mul, ha]))
  have hΛfin : ∀ u ∈ Λ, u.map (infPart D) = 0 := fun u hu => latO_fin hu
  have hth : ∀ w f, IsThetaFunO ψ S T f → IsThetaFunO ψ S T (heisO ψ S T w f) :=
    (GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1
  have hvth : IsThetaFunO ψ S T v := hv.2.theta
  have hlat : IsLatVac (heisO ψ S T) Λ v := hv.2.lat
  have hsign : ∀ u ∈ Λ, ∃ ε : ℂ, (ε = 1 ∨ ε = -1) ∧ heisO ψ S T u v = ε • v := fun u hu => by
    obtain ⟨ε, hε, h⟩ := hsg v hlat u hu
    exact ⟨ε, hε, h v hlat⟩
  have hεQ : ∀ ε : ℂ, (ε = 1 ∨ ε = -1) → ε ∈ Qb ∧ ε ≠ 0 := by
    rintro ε (rfl | rfl)
    · exact ⟨one_mem _, one_ne_zero⟩
    · exact ⟨neg_mem (one_mem _), neg_ne_zero.2 one_ne_zero⟩
  have hpsi : ∀ x y : WO S T, x.map (infPart D) = 0 → y.map (infPart D) = 0 → ψ (symplO S T x y) ∈ Qb :=
    fun x y hx hy => GlobalTheory.BotFourier.psi_mem hψ hS hT hx hy
  have hpsiH : ∀ x y : WO S T, x.map (infPart D) = 0 → y.map (infPart D) = 0 → ψ (symplOH S T x y) ∈ Qb :=
    fun x y hx hy => GlobalTheory.BotFourier.psiH_mem hψ hS hT hx hy

  have hcS : IsSplitIdem D (cA D e) := isSplitIdem_conj he
  have he1 : e * e = e := he.1
  have hec : e * (cA D e) = 0 := he.2.1
  have hce : (cA D e) * e = 0 := by rw [mul_comm]; exact hec
  have hc1 : (cA D e) * (cA D e) = (cA D e) := by rw [← RingHom.map_mul, he1]
  have hcc : cA D (cA D e) = e := GlobalTheory.DualPairCheck.cA_cA e
  have hq1 : (1 - (e + (cA D e))) * (1 - (e + (cA D e))) = 1 - (e + (cA D e)) := by linear_combination he1 + hc1 + 2 * hec
  have hcq : cA D (1 - (e + (cA D e))) = 1 - (e + (cA D e)) := by
    rw [map_sub, map_one, map_add (f := _), hcc, add_comm (cA D e) e]
  have hcq0 : (cA D e) * (1 - (e + (cA D e))) = 0 := by linear_combination -hc1 - hce
  have hqc0 : cA D (1 - (e + (cA D e))) * (cA D e) = 0 := by rw [hcq, mul_comm]; exact hcq0
  have hdec : ∀ x : WO S T, (cA D e) • x + (e • x + (1 - (e + (cA D e))) • x) = x := fun x => by
    rw [← add_smul, ← add_smul, ← add_assoc, add_comm (cA D e) e, add_sub_cancel, one_smul]

  have caseB : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ℓ v = 1 → ∀ x : WO S T, x.map (infPart D) = 0 → (1 - (e + (cA D e))) • x ∈ Λ → ℓ (heisO ψ S T x v) ∈ Qb := by
    intro ℓ hinv h1 x hx hx'
    obtain ⟨ε, hε, hεv⟩ := hsign _ hx'
    have hxe : IsHalf e (e • x) := (isHalf_iff _ _).2 (by rw [smul_smul, he1])
    have hxc : IsHalf (cA D e) ((cA D e) • x) := (isHalf_iff _ _).2 (by rw [smul_smul, hc1])
    have hxq : IsHalf (1 - (e + (cA D e))) ((1 - (e + (cA D e))) • x) := (isHalf_iff _ _).2 (by rw [smul_smul, hq1])
    have horth : symplO S T (e • x) ((1 - (e + (cA D e))) • x) = 0 := symplO_eq_zero S T hcq0 hxe hxq
    have e1 : heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v = ε • heisO ψ S T (e • x) v := by
      rw [heisO_add_of_orth ψ S T horth, hεv, heisO_smul]
    have e2 : heisO ψ S T ((cA D e) • x) (heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v) =
        ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)) • heisO ψ S T x v := by
      rw [heisO_heisO, hdec x]
    have e3 : ℓ (heisO ψ S T ((cA D e) • x) (heisO ψ S T (e • x + (1 - (e + (cA D e))) • x) v)) =
        ε * ℓ (heisO ψ S T (e • x) v) := by
      rw [hinv _ hxc _ (hth _ _ hvth), e1, map_smul, smul_eq_mul]
    rw [e2, map_smul, smul_eq_mul] at e3
    have hx0 := psi_ne_zero ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x))
    have hpq : ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)) ∈ Qb :=
      hpsiH _ _ (fin_smul _ hx) (fin_add (fin_smul _ hx) (fin_smul _ hx))
    have e4 : ℓ (heisO ψ S T x v) = (ψ (symplOH S T ((cA D e) • x) (e • x + (1 - (e + (cA D e))) • x)))⁻¹ *
        (ε * ℓ (heisO ψ S T (e • x) v)) := by
      rw [← e3, inv_mul_cancel_left₀ hx0]
    rw [e4]
    refine mul_mem (inv_mem hpq) (mul_mem (hεQ ε hε).1 ?_)
    by_cases hxΛ : e • x ∈ Λ
    · rw [hlat.2 e he _ hxΛ hxe, h1]; exact one_mem _
    · obtain ⟨l, hl, hlc, hne⟩ := dual_half he1 (fun u hu => half_fin he hu) hd (fun u hu => hΛ (cA D e) hc1 u hu) hxe hxΛ
      have h0 : ℓ (heisO ψ S T (e • x) v) = 0 := by
        have k1 := hinv l hlc _ (hth (e • x) v hvth)
        rw [heisO_comm, hlat.2 (cA D e) hcS l hl hlc, map_smul, smul_eq_mul] at k1
        have : (ψ (symplO S T l (e • x)) - 1) * ℓ (heisO ψ S T (e • x) v) = 0 := by
          rw [sub_mul, k1, one_mul, sub_self]
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
      rw [h0]; exact zero_mem _

  have step : ∀ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) →
      ℓ v = 1 → ∀ x : WO S T, x.map (infPart D) = 0 → ∃ ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ,
        (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ' (heisO ψ S T u f) = ℓ' f) ∧ ℓ' v = 1 ∧
        ℓ' (heisO ψ S T x v) ∈ Qb ∧ ∀ y : WO S T, y.map (infPart D) = 0 →
          ∃ a ∈ Qb, ℓ' (heisO ψ S T y v) = a * ℓ (heisO ψ S T y v) := by
    intro ℓ hinv h1 x hx
    by_cases hB : (1 - (e + (cA D e))) • x ∈ Λ
    · exact ⟨ℓ, hinv, h1, caseB ℓ hinv h1 x hx hB, fun y _ => ⟨1, one_mem _, (one_mul _).symm⟩⟩
    have hex : ¬ ∀ u ∈ Λ, ψ (symplO S T ((1 - (e + (cA D e))) • x) u) = 1 := fun h => hB ((hd _ (fin_smul _ hx)).2 h)
    push_neg at hex
    obtain ⟨u', hu', hne'⟩ := hex
    have huΛ : (1 - (e + (cA D e))) • u' ∈ Λ := hΛ _ hq1 u' hu'
    have huq : IsHalf (1 - (e + (cA D e))) ((1 - (e + (cA D e))) • u') := (isHalf_iff _ _).2 (by rw [smul_smul, hq1])
    rw [symplO_smul, hcq] at hne'
    have hne := psi_skew_ne hne'
    obtain ⟨ε, hε, hεv⟩ := hsign _ huΛ
    obtain ⟨hεQ', hε0⟩ := hεQ ε hε
    have hzQ : ψ (symplO S T ((1 - (e + (cA D e))) • u') x) ∈ Qb := hpsi _ _ (hΛfin _ huΛ) hx
    have hk : ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x) ≠ 0 := by
      rw [← mul_one_sub]
      exact mul_ne_zero hε0 (sub_ne_zero.2 (Ne.symm hne))
    have hcomm : ∀ w₁ : WO S T, heisO ψ S T ((1 - (e + (cA D e))) • u') (heisO ψ S T w₁ v) =
        (ψ (symplO S T ((1 - (e + (cA D e))) • u') w₁) * ε) • heisO ψ S T w₁ v := fun w₁ => by
      rw [heisO_comm, hεv, heisO_smul, smul_smul]
    refine ⟨(ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x))⁻¹ •
      (ℓ ∘ₗ (heisL ψ S T ((1 - (e + (cA D e))) • u') - (ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x)) • LinearMap.id)),
      fun y hy f hf => ?_, ?_, ?_, fun y hy => ?_⟩
    all_goals simp only [LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.sub_apply, heisL_apply,
      LinearMap.id_apply, map_sub, map_smul, smul_eq_mul]
    · have hc' : heisO ψ S T ((1 - (e + (cA D e))) • u') (heisO ψ S T y f) =
          heisO ψ S T y (heisO ψ S T ((1 - (e + (cA D e))) • u') f) := by
        rw [heisO_comm, symplO_eq_zero S T hqc0 huq hy, AddChar.map_zero_eq_one, one_smul]
      rw [hc', hinv y hy _ (hth _ _ hf), hinv y hy f hf]
    · rw [hεv, map_smul, smul_eq_mul, h1, mul_one, mul_one, inv_mul_cancel₀ hk]
    · rw [hcomm, map_smul, smul_eq_mul]
      have : ψ (symplO S T ((1 - (e + (cA D e))) • u') x) * ε * ℓ (heisO ψ S T x v) -
          ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x) * ℓ (heisO ψ S T x v) = 0 := by ring
      rw [this, mul_zero]
      exact zero_mem _
    · refine ⟨(ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x))⁻¹ *
        (ψ (symplO S T ((1 - (e + (cA D e))) • u') y) * ε - ε * ψ (symplO S T ((1 - (e + (cA D e))) • u') x)),
        mul_mem (inv_mem (sub_mem hεQ' (mul_mem hεQ' hzQ)))
          (sub_mem (mul_mem (hpsi _ _ (hΛfin _ huΛ) hy) hεQ') (mul_mem hεQ' hzQ)), ?_⟩
      rw [hcomm, map_smul, smul_eq_mul]
      ring

  have hv0 : v ≠ 0 := by
    rintro rfl
    obtain ⟨p, hp⟩ := hv.2.norm.1
    have := hv.2.norm.2 p hp
    simp [nrm2] at this
  obtain ⟨ℓ₀, hℓ₀, hinv₀⟩ := invariant_form (e := (cA D e)) (Λ := Λ) hc1 (by rw [hcc]; exact hec)
    (fun u hu => half_fin hcS hu) hd (fun u hu => by rw [hcc]; exact hΛ e he1 u hu) hv0
    (fun l hl hh => hlat.2 (cA D e) hcS l hl hh) (fun l hl hh => hlat.2 e he l hl (by rwa [hcc] at hh))
  have main : ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) → ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, IsHalf (cA D e) u → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧ ℓ v = 1 ∧
      ∀ p, ℓ (heisO ψ S T (w p) v) ∈ Qb := by
    intro n
    induction n with
    | zero =>
      intro w _
      refine ⟨(ℓ₀ v)⁻¹ • ℓ₀, fun u hu f hf => ?_, ?_, fun p => p.elim0⟩
      · rw [LinearMap.smul_apply, LinearMap.smul_apply, hinv₀ u hu f hf]
      · rw [LinearMap.smul_apply, smul_eq_mul, inv_mul_cancel₀ hℓ₀]
    | succ n ih =>
      intro w hw
      obtain ⟨ℓ, hinv, h1, halg⟩ := ih (fun p => w p.castSucc) fun p => hw _
      obtain ⟨ℓ', hinv', h1', hlast, hfac⟩ := step ℓ hinv h1 (w (Fin.last n)) (hw _)
      refine ⟨ℓ', hinv', h1', fun p => ?_⟩
      induction p using Fin.lastCases with
      | last => exact hlast
      | cast q =>
        obtain ⟨a, ha, h⟩ := hfac _ (hw q.castSucc)
        rw [h]
        exact mul_mem ha (halg q)
  obtain ⟨ℓ, hinv, h1, halg⟩ := main n w hw
  exact ⟨ℓ, fun u hu f hf => hinv u hu f hf, h1, fun p => mem_algebraicClosure_iff.1 (halg p)⟩

end GlobalTheory.SplitAlgForm

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicInvariantFormVacuumSplitPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algebraicInvariantForm_vacuum_splitPlace : ∀ {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}, IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v → IsSelfDualC S ΛS → IsSelfDualC T ΛT →
    ∀ e : Formalism.L2.Theta.AE D, IsSplitIdem D e → ∀ (n : ℕ) (w : Fin n → WO S T), (∀ p, (w p).map (infPart D) = 0) →
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ, (∀ u : WO S T, (∀ i j, cA D e * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f → ℓ (heisO ψ S T u f) = ℓ f) ∧
      ℓ v = 1 ∧ ∀ p, IsAlgebraic ℚ (ℓ (heisO ψ S T (w p) v)) := by
  first | exact @GlobalTheory.SplitAlgForm.exists_alg_form | exact GlobalTheory.SplitAlgForm.exists_alg_form | (intros; apply GlobalTheory.SplitAlgForm.exists_alg_form <;> assumption)
end
end

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.BotExpand

section Gen

open GlobalTheory.MovedAlg GlobalTheory.AlgWave GlobalTheory.RawLift

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} {v : WO S T → ℂ}
    {χS χT : (Formalism.L2.Theta.AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem vac_ne_zero (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v) :
    v ≠ 0 := by
  rintro rfl
  obtain ⟨p, hp⟩ := hv.2.norm.1
  have := hv.2.norm.2 p hp
  simp [nrm2] at this

theorem alg_self : IsAlgComb ψ S T v v :=
  ⟨1, fun _ => 1, fun _ => 0, fun _ => isAlgebraic_one, fun _ => Matrix.ext fun _ _ => (infPart D).map_zero, by
    simp [GlobalTheory.SplitScalar.heisO_zero]⟩

theorem theta_of_alg (hψ : IsStdChar D ψ (-1)) (hv : IsThetaFunO ψ S T v) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) :
    IsThetaFunO ψ S T F := by
  obtain ⟨n, c, w, -, -, rfl⟩ := hF
  refine Finset.sum_induction _ (IsThetaFunO ψ S T) (fun _ _ => GlobalTheory.OrientedHeis.theta_add) GlobalTheory.OrientedHeis.theta_zero
    fun p _ => GlobalTheory.OrientedHeis.theta_smul _ ((GlobalTheory.HeisThetaLaws.heis_theta_laws D ψ hψ S T).1 _ _ hv)

theorem star_mem {a : ℂ} (ha : a ∈ Qb) : star a ∈ Qb :=
  mem_algebraicClosure_iff.2 ((mem_algebraicClosure_iff.1 ha).algHom (starRingEnd ℂ).toRatAlgHom)

variable (hv : IsVacO ψ θ S T sS sT (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) v)
  (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
include hv hS hT

theorem rigid {F F' : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) (hF' : IsAlgComb ψ S T v F') (h0 : F ≠ 0) {c : ℂ}
    (hc : F' = c • F) : IsAlgebraic ℚ c := by
  obtain ⟨p, hp⟩ := hv.2.norm.1
  have h1 := mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp F F hF hF)
  have h2 := mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp F F' hF hF')
  have h3 := GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hv.1 (theta_of_alg hv.1 hv.2.theta hF) h0 hp
  rw [hc, thetaInner_smul_right] at h2
  have := div_mem h2 h1
  rw [mul_div_cancel_right₀ _ h3] at this
  exact mem_algebraicClosure_iff.1 this

theorem om_scaled (hW : IsWeilDatumO ψ S T χS χT om) {p : GA D S × GA D T} {κ : ℂ} {F₀ : WO S T → ℂ}
    (h0 : IsAlgComb ψ S T v F₀) (hp : om p v = κ • F₀) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) :
    ∃ F₁, IsAlgComb ψ S T v F₁ ∧ om p F = κ • F₁ := by
  obtain ⟨n, c, w, hc, hw, rfl⟩ := hF
  obtain ⟨x, h⟩ := p
  refine ⟨∑ q, c q • heisO ψ S T (actO S T x h (w q)) F₀, IsAlgComb.finsum _ _ hc fun q => IsAlgComb.Heisenberg₂
    (fun a b ha hb => mem_algebraicClosure_iff.1 (GlobalTheory.BotFourier.psiH_mem hv.1 hS hT ha hb))
    (GlobalTheory.FinApprox.actO_fin _ _ (hw q)) h0, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_smul, hW.om_heis x h (w q) v hv.2.theta, hp, GlobalTheory.VacSchurFin.heisO_smul', smul_comm]

theorem om_alg (hW : IsWeilDatumO ψ S T χS χT om) {p : GA D S × GA D T}
    (h0 : IsAlgComb ψ S T v (om p v)) {F : WO S T → ℂ} (hF : IsAlgComb ψ S T v F) : IsAlgComb ψ S T v (om p F) := by
  obtain ⟨F₁, h1, h2⟩ := om_scaled hv hS hT hW (κ := 1) h0 (one_smul _ _).symm hF
  rwa [h2, one_smul]

theorem om_ne_zero (p : GA D S × GA D T) : om p v ≠ 0 := fun h => vac_ne_zero hv (by
  have : om p⁻¹ (om p v) = v := by rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [← this, h, map_zero])

variable (hcS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hcT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
  (hW : IsWeilDatumO ψ S T χS χT om)
include hcS hcT hW

theorem root_closed {x : GA D S} (hx : x ∈ GfC S) {h : GA D T} (hh : h ∈ GfC T) {m : ℕ} (hm : 0 < m)
    (hp : IsAlgComb ψ S T v (om ((x, h) ^ m) v)) : IsAlgComb ψ S T v (om (x, h) v) := by
  obtain ⟨κ, F, hF, e⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hv hS hT hcS hcT hW x hx h hh
  have key : ∀ k : ℕ, ∃ F₁, IsAlgComb ψ S T v F₁ ∧ om ((x, h) ^ k) v = κ ^ k • F₁ := by
    intro k
    induction k with
    | zero => exact ⟨v, alg_self, by simp⟩
    | succ k ih =>
      obtain ⟨F₁, h1, h2⟩ := ih
      obtain ⟨F₂, h3, h4⟩ := om_scaled hv hS hT hW hF e h1
      exact ⟨F₂, h3, by rw [pow_succ', map_mul, Module.End.mul_apply, h2, map_smul, h4, smul_smul, pow_succ]⟩
  obtain ⟨F₁, h1, h2⟩ := key m
  have h0 : F₁ ≠ 0 := fun h0 => om_ne_zero hv hS hT _ (by rw [h2, h0, smul_zero])
  rw [e]
  exact hF.smul (IsAlgebraic.of_pow hm (rigid hv hS hT h1 hp h0 h2))

def algGroup : Subgroup (GA D S × GA D T) where
  carrier := {p | p.1 ∈ GfC S ∧ p.2 ∈ GfC T ∧ IsAlgComb ψ S T v (om p v)}
  one_mem' := ⟨one_mem _, one_mem _, by rw [map_one]; exact alg_self⟩
  mul_mem' := fun {p q} hp hq => ⟨mul_mem hp.1 hq.1, mul_mem hp.2.1 hq.2.1, by
    rw [map_mul]; exact om_alg hv hS hT hW hp.2.2 hq.2.2⟩
  inv_mem' := fun {p} hp => ⟨inv_mem hp.1, inv_mem hp.2.1, by
    obtain ⟨κ, F, hF, e⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hv hS hT hcS hcT hW _ (inv_mem hp.1) _ (inv_mem hp.2.1)
    have e' : om p⁻¹ v = κ • F := e
    have h1 : v = κ • om p F := by
      rw [← map_smul, ← e', ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h0 : om p F ≠ 0 := fun h0 => vac_ne_zero hv (by rw [h1, h0, smul_zero])
    rw [e']
    exact hF.smul (rigid hv hS hT (om_alg hv hS hT hW hp.2.2 hF) alg_self h0 h1)⟩

omit hv hS hT hcS hcT hW in
theorem mem_GfC_of_suppAt {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {V : HSp D} {g : GA D V}
    (hg : Formalism.L2.Theta.SuppAt e V g) : g ∈ GfC V := by
  have h1 := GlobalTheory.SplitScalar.infPart_splitIdem he
  have h2 := GlobalTheory.PlaceDatum.infPart_cA h1
  refine MonoidHom.mem_ker.2 (Units.ext ?_)
  change (Formalism.L2.Theta.mt V g).map (infPart D) = 1
  rw [← sub_eq_zero]
  ext i j
  rw [← GlobalTheory.SplitCharTrivial.map_sub_one, ← hg i j, RingHom.map_mul, RingHom.map_add (f := _), h1, h2, add_zero, zero_mul]
  rfl

theorem split_alg {e : Formalism.L2.Theta.AE D} (he : IsSplitIdem D e) {g : GA D S} {h : GA D T}
    (hg : Formalism.L2.Theta.SuppAt e S g) (hh : Formalism.L2.Theta.SuppAt e T h) : IsAlgComb ψ S T v (om (g, h) v) := by
  obtain ⟨κ, F, hF, eF⟩ := GlobalTheory.T.weilDatum_finite_pair_vacuum_algebraic_combination hv hS hT hcS hcT hW g (mem_GfC_of_suppAt he hg) h (mem_GfC_of_suppAt he hh)
  obtain ⟨x, hx⟩ := GlobalTheory.WeilDetermined.exists_isDetAt he.1 S g
  obtain ⟨y, hy⟩ := GlobalTheory.WeilDetermined.exists_isDetAt he.1 T h
  obtain ⟨r, hr, hℓ⟩ := hW.om_split e he g h hg hh x y hx hy
  have h1 := GlobalTheory.SplitScalar.infPart_splitIdem he
  have hx1 : infPart D (x : Formalism.L2.Theta.AE D) = 1 := by
    rw [hx, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, h1, RingHom.map_one, zero_mul, zero_add, sub_zero]
  have hy1 : infPart D (y : Formalism.L2.Theta.AE D) = 1 := by
    rw [hy, RingHom.map_add (f := _), RingHom.map_mul, RingHom.map_sub, h1, RingHom.map_one, zero_mul, zero_add, sub_zero]
  have hz : ((splitFacO χS χT x y : Circle) : ℂ) ∈ Qb := by
    rw [splitFacO, Circle.coe_mul, Circle.coe_inv]
    exact mul_mem (inv_mem (mem_algebraicClosure_iff.2 (GlobalTheory.T.heckeChar_finiteIdeles_isAlgebraic_of_resEta hv.2.inf hW.hecT hW.resT x hx1)))
      (mem_algebraicClosure_iff.2 (GlobalTheory.T.heckeChar_finiteIdeles_isAlgebraic_of_resEta hv.2.inf hW.hecS hW.resS y hy1))
  have hz1 : star ((splitFacO χS χT x y : Circle) : ℂ) * (splitFacO χS χT x y : Circle) = 1 := by
    rw [Complex.star_def, ← Circle.coe_inv_eq_conj, ← Circle.coe_mul, inv_mul_cancel, Circle.coe_one]
  generalize ((splitFacO χS χT x y : Circle) : ℂ) = z at hℓ hz hz1

  obtain ⟨p, hp⟩ := hv.2.norm.1
  have hF0 : F ≠ 0 := fun h0 => om_ne_zero hv hS hT _ (by rw [eF, h0, smul_zero])
  have n1 := GlobalTheory.WeilPairing.thetaInner_weilRep D ψ S T χS χT om p.1 p.2 hW hp (g, h) v v hv.2.theta hv.2.theta
  rw [eF, thetaInner_smul_left, thetaInner_smul_right, ← mul_assoc] at n1
  have n2 : star κ * κ ∈ Qb := by
    rw [eq_div_of_mul_eq (GlobalTheory.RawLift.VecNonzero.thetaInner_self_ne_zero hv.1 (theta_of_alg hv.1 hv.2.theta hF) hF0 hp) n1]
    exact div_mem (mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp v v alg_self alg_self))
      (mem_algebraicClosure_iff.2 (GlobalTheory.T.vacuum_self_dual_lattices hv hS hT p.1 p.2 hp F F hF hF))

  obtain ⟨n, c, w, hc, hw, hFe⟩ := id hF
  obtain ⟨ℓ, l1, l2, l3⟩ := GlobalTheory.T.exists_algebraicInvariantForm_vacuum_splitPlace hv hS hT e he n w hw
  have ha : ℓ F ∈ Qb := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hFe, map_sum]
    exact sum_mem fun q _ => by
      rw [map_smul, smul_eq_mul]
      exact mul_mem (mem_algebraicClosure_iff.2 (hc q)) (mem_algebraicClosure_iff.2 (l3 q))
  have e1 := hℓ ℓ l1 v hv.2.theta
  rw [eF, map_smul, smul_eq_mul, l2, mul_one] at e1
  have hr0 : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hr.ne'
  have hz0 : z ≠ 0 := right_ne_zero_of_mul_eq_one hz1
  have ha0 : ℓ F ≠ 0 := fun h0 => mul_ne_zero hr0 hz0 (by rw [← e1, h0, mul_zero])
  have e2 : (r : ℂ) ^ 2 = (star κ * κ) * (star (ℓ F) * ℓ F) := by
    have e3 := congrArg star e1
    rw [star_mul', star_mul', Complex.star_def, Complex.conj_ofReal, ← Complex.star_def] at e3
    linear_combination (-(r : ℂ) ^ 2) * hz1 - (star κ * star (ℓ F)) * e1 - (r * z) * e3
  have hrq : (r : ℂ) ∈ Qb := mem_algebraicClosure_iff.2 (IsAlgebraic.of_pow two_pos (mem_algebraicClosure_iff.1
    (e2 ▸ mul_mem n2 (mul_mem (star_mem ha) ha))))
  have hκ : κ ∈ Qb := by
    rw [eq_div_of_mul_eq ha0 e1]
    exact div_mem (mul_mem hrq hz) ha
  rw [eF]
  exact hF.smul (mem_algebraicClosure_iff.1 hκ)

omit hv hS hT hcS hcT hW in
theorem finCong_one (V : HSp D) (N : ℕ) : GlobalTheory.Member.FinCong V N 1 := by
  have h := (GlobalTheory.Member.PrincLevel.levelGroup V N).one_mem
  exact h.2

theorem mem_algGroup {p : GA D S × GA D T} :
    p ∈ algGroup hv hS hT hcS hcT hW ↔ p.1 ∈ GfC S ∧ p.2 ∈ GfC T ∧ IsAlgComb ψ S T v (om p v) := Iff.rfl

set_option maxHeartbeats 1000000 in
theorem source_mem {x : GA D S} (hx : x ∈ GfC S) : (x, (1 : GA D T)) ∈ algGroup hv hS hT hcS hcT hW := by
  obtain ⟨N, hN, hlev⟩ := GlobalTheory.T.congruent_pairs_fix_vacuum_weilDatum hv hS hT hcS hcT hW
  refine GlobalTheory.T.finiteUnitaryPoints_mem_of_level_and_split_place S ((algGroup hv hS hT hcS hcT hW).comap (MonoidHom.inl _ _)) N hN (fun g hg m hm hp => ?_)
    (fun k hk hc => ?_) (fun e he g hg => ?_) x hx
  · rw [Subgroup.mem_comap, map_pow, mem_algGroup] at hp
    rw [Subgroup.mem_comap, MonoidHom.inl_apply, mem_algGroup]
    exact ⟨hg, one_mem _, root_closed hv hS hT hcS hcT hW hg (one_mem _) hm hp.2.2⟩
  · rw [Subgroup.mem_comap, MonoidHom.inl_apply, mem_algGroup, hlev k hk 1 (one_mem _) hc (finCong_one T N)]
    exact ⟨hk, one_mem _, alg_self⟩
  · rw [Subgroup.mem_comap, MonoidHom.inl_apply, mem_algGroup]
    exact ⟨mem_GfC_of_suppAt he hg, one_mem _,
      split_alg hv hS hT hcS hcT hW he hg (GlobalTheory.WeilDetermined.suppAt_one e T)⟩

set_option maxHeartbeats 1000000 in
theorem target_mem {h : GA D T} (hh : h ∈ GfC T) : ((1 : GA D S), h) ∈ algGroup hv hS hT hcS hcT hW := by
  obtain ⟨N, hN, hlev⟩ := GlobalTheory.T.congruent_pairs_fix_vacuum_weilDatum hv hS hT hcS hcT hW
  refine GlobalTheory.T.finiteUnitaryPoints_mem_of_level_and_split_place T ((algGroup hv hS hT hcS hcT hW).comap (MonoidHom.inr _ _)) N hN (fun g hg m hm hp => ?_)
    (fun k hk hc => ?_) (fun e he g hg => ?_) h hh
  · rw [Subgroup.mem_comap, map_pow, mem_algGroup] at hp
    rw [Subgroup.mem_comap, MonoidHom.inr_apply, mem_algGroup]
    exact ⟨one_mem _, hg, root_closed hv hS hT hcS hcT hW (one_mem _) hg hm hp.2.2⟩
  · rw [Subgroup.mem_comap, MonoidHom.inr_apply, mem_algGroup, hlev 1 (one_mem _) k hk (finCong_one S N) hc]
    exact ⟨one_mem _, hk, alg_self⟩
  · rw [Subgroup.mem_comap, MonoidHom.inr_apply, mem_algGroup]
    exact ⟨one_mem _, mem_GfC_of_suppAt he hg,
      split_alg hv hS hT hcS hcT hW he (GlobalTheory.WeilDetermined.suppAt_one e S) hg⟩

theorem om_vac_algComb {x : GA D S} (hx : x ∈ GfC S) {h : GA D T} (hh : h ∈ GfC T) :
    IsAlgComb ψ S T v (om (x, h) v) := by
  have h3 := (algGroup hv hS hT hcS hcT hW).mul_mem (source_mem hv hS hT hcS hcT hW hx)
    (target_mem hv hS hT hcS hcT hW hh)
  rw [Prod.mk_mul_mk, mul_one, one_mul, mem_algGroup] at h3
  exact h3.2.2

end Gen

end GlobalTheory.BotExpand

end
