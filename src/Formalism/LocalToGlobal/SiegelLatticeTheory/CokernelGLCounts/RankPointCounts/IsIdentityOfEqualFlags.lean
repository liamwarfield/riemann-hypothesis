module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RelevantSetZeroGNotIdentity
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCount
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbCut

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.IsIdentityOfEqualFlags
noncomputable section

open scoped Classical
open MeasureTheory NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.MainNotions.S.Cnt Formalism.MainNotions.KappaEndpoints Formalism.MainNotions.LatticeGluingRadicals
  Formalism.MainNotions.BridgeLemma

namespace Formalism.L2.SG.KappaOffDiagonal

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZsC1c

variable {D : D7} {X : HidaSetting D}

theorem isIdentity_of_equal_flags (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    (Y : Full X) {u : D.what₂.Word} (t : GTu Y u)
    (hXa : ∀ a, (frq X t.rep).fl.Xa a = (lf D (X.Fu u)).fl.Xa a)
    (hXp : (frq X t.rep).fl.Xplus = (lf D (X.Fu u)).fl.Xplus)
    (hrel : Relevant D.host.F (lf D (X.Fu u)).fl (frq X t.rep).fl) : t.isId := by
  have hT0 : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 (tie_Tu_pos D u).ne'
  have hrow : IsRowLat D (X.Fu u) t.lam := (Y.rowsOK u).1 t.lam t.mem
  have hfix : FixedHyp D t.lam (lf D (X.Fu u)) := hrow.2.1
  have hPD : TermDef.PD D t.lam (lf D (X.Fu u)) u (frq X t.rep) := t.rep.2.2.2.2
  have hlift : IsLift t.lam (frq X t.rep) := hPD.1
  have hadm : IsAdmissible t.lam (gS D) (lf D (X.Fu u)) (frq X t.rep) := hPD.2.1
  have hconv : IsFixedConv t.lam (gS D) (frq X t.rep) := hPD.2.2.1
  obtain ⟨c, hcc, he, hz⟩ := id_scal D.host.F D.host.E (hS D) D.R.rS _ (lf D (X.Fu u)).fl (frq X t.rep).fl hT0
    (tie_trace D.sp.cm) hXa hXp hrel
  have hX : (frq X t.rep).fl.X = (lf D (X.Fu u)).fl.X := by rw [tie_X_eq_Xa, tie_X_eq_Xa]; exact hXa _
  obtain ⟨o, ho, N, hN, hoN⟩ := id_unit D.host.E (hS D) D.R.rS _ t.lam (lf D (X.Fu u)) (frq X t.rep) c (p_starConj D)
    hlift.1 hfix.2.2.2.2 hcc hz hX
  have hcong : ∀ i : Fin 2, ∀ P : HeightOneSpectrum (𝓞 D.host.E), ((D.host.g i : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal →
      o - 1 ∈ P.asIdeal := by
    intro i P hP
    refine id_cong D.host.E (hS D) D.R.rS (Tu D u) t.lam (gS D) (lf D (X.Fu u)) (frq X t.rep) o hfix.2.1
      hfix.2.2.1.1 hadm (by rw [ho]; exact hz) P ?_ ?_
    · unfold gS
      rw [Nat.cast_mul]
      fin_cases i
      · exact P.asIdeal.mul_mem_right _ hP
      · exact P.asIdeal.mul_mem_left _ hP
    · refine id_coprime_notMem P.asIdeal P.isPrime.ne_top _ _ ?_ hP
      refine (Nat.coprime_primes (D.host.g_prime i) (D.mem u).A.T_prime).2 ?_
      fin_cases i
      · exact (hTg u).1.symm
      · exact (hTg u).2.symm
  obtain ⟨P1, hP1⟩ := id_over D.host.E _ (D.host.g_prime 0)
  obtain ⟨P2, hP2⟩ := id_over D.host.E _ (D.host.g_prime 1)
  have ho1 : o = 1 := id_root (𝓞 D.host.E) o N _ _ P1.asIdeal P2.asIdeal hN hoN (D.host.g_prime 0) (D.host.g_prime 1)
    D.host.g_ne P1.isPrime.ne_top P2.isPrime.ne_top hP1 hP2 (hcong 0 P1 hP1) (hcong 1 P2 hP2)
  have hc1 : c = 1 := by rw [← ho, ho1]; rfl
  subst hc1
  simp only [one_smul] at he hz
  obtain ⟨n, hn, hne⟩ := id_lift D _ t.lam (lf D (X.Fu u)) (frq X t.rep) hfix hlift hconv he hz
  have hzo : (lf D (X.Fu u)).fl.z ∈ orth (hS D) (Xsp (lf D (X.Fu u))) := by
    rw [p_mem_orth]
    exact tie_X_le_ker _ _ (lf D (X.Fu u)).fl.z_orth
  have h3' := hn.2.2 _ hzo
  have hzz : n (lf D (X.Fu u)).fl.z - (frq X t.rep).fl.z =
      (n (lf D (X.Fu u)).fl.z - (lf D (X.Fu u)).fl.z) - ((frq X t.rep).fl.z - (lf D (X.Fu u)).fl.z) := by abel
  refine ⟨frq X t.rep, TermDef.rep_mk (⟨frq X t.rep, hPD⟩ : TermDef.Carrier (TermDef.PD D t.lam (lf D (X.Fu u)) u)),
    n, hn, hne, ?_⟩
  rw [hzz]
  exact Submodule.sub_mem _ h3' hz

theorem one_le_index_of_relevant (hTg : ∀ u : D.what₂.Word, (D.mem u).A.T ≠ D.host.g 0 ∧ (D.mem u).A.T ≠ D.host.g 1)
    (Y : Full X) {u : D.what₂.Word} (t : GTu Y u) (ht : t ∈ relSet Y u) : 1 ≤ jT t := by
  obtain ⟨hr, hG, hid⟩ := relevantSet_zeroG_not_identity ht
  obtain ⟨j, hj, c, hN⟩ := exists_nfFull_of_relevant_of_G_eq_zero Y t hr hG
  rw [index_eq_normalForm t hN]
  by_contra hj0
  have hj0 : j = 0 := by omega
  subst hj0
  obtain ⟨k1, -, k3⟩ := Formalism.HermitianLatticeCounting.Final.S6.nFJZero _ _ _ _ _ _ c hN.1
  have hXa : ∀ a, (frq X t.rep).fl.Xa a = (lf D (X.Fu u)).fl.Xa a := fun a => by
    exact (nf_Xa (frq X t.rep).fl (nf_T_ne D u) a).symm.trans
      ((k1 a).trans (nf_Xa (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u) a))
  have k3' : (frq X t.rep).fl.z - c • (lf D (X.Fu u)).fl.z ∈ (lf D (X.Fu u)).fl.X := by
    rw [← normal_form_z_eq (frq X t.rep).fl (nf_T_ne D u),
      ← normal_form_z_eq (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u),
      ← nf_X (lf D (X.Fu u)).fl (fixedFlag_level_ne_zero D u)]
    exact k3
  have hXp : (frq X t.rep).fl.Xplus = (lf D (X.Fu u)).fl.Xplus :=
    nf_Xplus_eq _ _ (by rw [nf_X_eq, nf_X_eq]; exact hXa _) c hN.1.1 k3'
  exact hid (isIdentity_of_equal_flags hTg Y t hXa hXp (relRepC D X Y u u t hr hG).1)

end ZsC1c

theorem JPosC_holds : JPosC := by
  intro Cg cb Cw cT CT C0 C' Cl D large₂ X Y u hK _ t ht
  refine one_le_index_of_relevant (fun w => ?_) Y t ht

  have hc : Nat.Coprime (D.mem w).A.T (D.host.g 0 * D.host.g 1) := (hK.2.2.2.2.2.2.1 w).2
  have key : ∀ i : Fin 2, D.host.g i ∣ D.host.g 0 * D.host.g 1 → (D.mem w).A.T ≠ D.host.g i := by
    intro i hd h
    rw [h] at hc
    have h1 : Nat.Coprime (D.host.g i) (D.host.g i) := Nat.Coprime.coprime_dvd_right hd hc
    exact (D.host.g_prime i).one_lt.ne' (by simpa [Nat.coprime_self] using h1)
  exact ⟨key 0 (dvd_mul_right _ _), key 1 (dvd_mul_left _ _)⟩

end Formalism.L2.SG.KappaOffDiagonal
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PcIntGen
noncomputable section

open ValuativeRel Formalism.MainNotions.S Formalism.BasicNotions Formalism.L2.SG.TermLoc

namespace Formalism.L2.SG.Pf.PCount

namespace IntegralGeneration

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V)

theorem h_smul_right (x y : V) (c : E) : H.h x (c • y) = M.L.cj c * H.h x y := by
  rw [H.h_herm (c • y) x, H.h_smul_left, map_mul, ← H.h_herm y x]

theorem h_add_right (x y y' : V) : H.h x (y + y') = H.h x y + H.h x y' := by
  rw [H.h_herm (y + y') x, H.h_add_left, map_add (f := _), ← H.h_herm y x, ← H.h_herm y' x]

theorem fst_mem {g : Loc.SplitG M.L} {x : E} (hx : x ∈ M.L.O) : (g.e x).1 ∈ 𝒪[F] := by
  rw [M.L.O_def] at hx
  have h1 : IsIntegral 𝒪[F] (g.e x).1 := by
    have := hx.map (((AlgHom.fst F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F])
    simpa using this
  exact (Valuation.integer.integers (valuation F)).mem_of_integral h1

theorem snd_mem {g : Loc.SplitG M.L} {x : E} (hx : x ∈ M.L.O) : (g.e x).2 ∈ 𝒪[F] := by
  rw [M.L.O_def] at hx
  have h1 : IsIntegral 𝒪[F] (g.e x).2 := by
    have := hx.map (((AlgHom.snd F F F).comp g.e.toAlgHom).restrictScalars 𝒪[F])
    simpa using this
  exact (Valuation.integer.integers (valuation F)).mem_of_integral h1

theorem mem_R_of_split {g : Loc.SplitG M.L} (hM : M.split = some g) (x : E) :
    x ∈ M.R ↔ g.e x ∈ Formalism.FourierDecayAlt.I.orderR (𝒪[F]) (g.q : F) := by
  obtain ⟨L, s, mu⟩ := M
  simp only at hM g ⊢
  subst hM
  exact Formalism.MainNotions.LocalModelPeriodLattices.mem_R_split L g mu x

theorem e_alg (g : Loc.SplitG M.L) (c : F) : g.e (algebraMap F E c) = (c, c) := by
  rw [g.e.commutes]; rfl

theorem zzplus_int {r : ℕ} {t : Loc.Term V M r} (ht : H.IsGeneric t) (a b : Fin (r + 1)) :
    H.ZZplus t a b ∈ M.R := by
  obtain ⟨⟨hSD, hF, hF', -, -, hG⟩, hP⟩ := ht
  have hfL : ∀ a, t.f a ∈ t.abelian₂ := hF.1.1
  have hfL' : ∀ a, t.f' a ∈ t.abelian₂ := hF'.1.1
  have hint : ∀ x ∈ t.abelian₂, ∀ y ∈ t.abelian₂, H.h x y ∈ M.L.O := fun x hx y hy => (hSD.2.2 x).1 hx y hy
  have hff : ∀ a b : Fin (r + 1), H.h (t.f b) (t.f a) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t.T else 0 := by
    intro a b
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact hF.2.2.1
    · exact hF.2.1 b a (not_and_or.mp hc).symm
  have hff' : ∀ a b : Fin (r + 1), H.h (t.f' b) (t.f' a) =
      if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E t.T' else 0 := by
    intro a b
    split_ifs with hc
    · obtain ⟨rfl, rfl⟩ := hc; exact hF'.2.2.1
    · exact hF'.2.1 b a (not_and_or.mp hc).symm
  rcases hM : M.split with _ | g
  ·
    have hR : M.R = M.L.O := by simp only [Loc.Model.R, hM]
    simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Loc.HermSp.Zhat, Matrix.of_apply]
    rw [hR]
    exact hint _ (hfL' b) _ (hfL a)
  ·
    obtain ⟨-, ⟨c, hc⟩, -⟩ := hG g hM
    have hq : (g.q : F) ≠ 0 := by
      intro h; apply g.q_irr.ne_zero; exact_mod_cast h
    set q : F := (g.q : F) with hq_def
    set k : E := algebraMap F E q with hk
    set n : Fin (r + 1) → V := fun a => algebraMap F E q⁻¹ • (t.f' a - t.f a) with hn_def
    have hnL : ∀ a, n a ∈ t.abelian₂ := fun a => by
      have := hP.1 (Sum.inr a)
      simpa only [Loc.HermSp.MMfam, hM, Sum.elim_inr] using this
    have hf' : ∀ a, t.f' a = t.f a + k • n a := fun a => by
      simp only [hn_def, hk, smul_smul, ← map_mul, mul_inv_cancel₀ hq, map_one, one_smul]
      abel
    have hcjk : M.L.cj k = k := M.L.cj.commutes q
    have hek : g.e k = (q, q) := e_alg g q

    have E1 : H.h (t.f' b) (t.f a) = H.h (t.f b) (t.f a) + k * H.h (n b) (t.f a) := by
      rw [hf' b, H.h_add_left, H.h_smul_left]
    have E2 : H.h (t.f' a) (t.f b) = H.h (t.f a) (t.f b) + k * H.h (n a) (t.f b) := by
      rw [hf' a, H.h_add_left, H.h_smul_left]
    have E3 : H.h (t.f' b) (t.f' a) = H.h (t.f b) (t.f a) + k * H.h (n b) (t.f a) +
        k * H.h (t.f b) (n a) + k * k * H.h (n b) (n a) := by
      rw [hf' b, hf' a]
      simp only [H.h_add_left, H.h_smul_left, h_add_right, h_smul_right, hcjk]
      ring
    have hswap : (g.e (H.h (n a) (t.f b))).2 = (g.e (H.h (t.f b) (n a))).1 := by
      rw [H.h_herm (t.f b) (n a), g.e_cj]; rfl
    have hA := fst_mem (g := g) (hint _ (hnL b) _ (hfL a))
    have hB := snd_mem (g := g) (hint _ (hnL a) _ (hfL b))
    have hC := fst_mem (g := g) (hint _ (hnL b) _ (hnL a))
    have hqq : q * q⁻¹ = 1 := mul_inv_cancel₀ hq
    have F1 : (g.e (H.h (t.f' b) (t.f a))).1 = (g.e (H.h (t.f b) (t.f a))).1 + q * (g.e (H.h (n b) (t.f a))).1 := by
      rw [E1]; simp only [map_add (f := _), map_mul, hek, Prod.fst_add, Prod.fst_mul]
    have F2 : (g.e (H.h (t.f' a) (t.f b))).2 = (g.e (H.h (t.f a) (t.f b))).2 + q * (g.e (H.h (n a) (t.f b))).2 := by
      rw [E2]; simp only [map_add (f := _), map_mul, hek, Prod.snd_add, Prod.snd_mul]
    have F3 : (g.e (H.h (t.f' b) (t.f' a))).1 = (g.e (H.h (t.f b) (t.f a))).1 + q * (g.e (H.h (n b) (t.f a))).1 +
        q * (g.e (H.h (n a) (t.f b))).2 + q * q * (g.e (H.h (n b) (n a))).1 := by
      rw [E3, hswap]; simp only [map_add (f := _), map_mul, hek, Prod.fst_add, Prod.fst_mul]
    generalize (g.e (H.h (n b) (t.f a))).1 = A at hA F1 F3
    generalize (g.e (H.h (n a) (t.f b))).2 = B at hB F2 F3
    generalize (g.e (H.h (n b) (n a))).1 = C at hC F3
    simp only [Loc.HermSp.ZZplus, Loc.HermSp.ZZplusOf, hM, Loc.HermSp.Zhat, Matrix.of_apply]
    rw [mem_R_of_split hM]
    by_cases hcn : a = Fin.last r ∧ b = Fin.last r
    · obtain ⟨rfl, rfl⟩ := hcn
      have h1 := hff (Fin.last r) (Fin.last r)
      have h1' := hff' (Fin.last r) (Fin.last r)
      simp only [and_self, if_true] at h1 h1' ⊢
      rw [h1, map_neg, e_alg] at F1 F2 F3
      rw [h1', map_neg, e_alg] at F3
      simp only [Prod.fst_neg, Prod.snd_neg] at F1 F2 F3
      rw [map_sub, AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply, F1, F2]
      refine ⟨?_, ?_, -C, neg_mem hC, ?_⟩
      · simp only [Prod.fst_sub]
        have : (-t.T + q * A) / q - -t.T / q = A := by linear_combination A * hqq
        rw [this]; exact hA
      · simp only [Prod.snd_sub]
        have : -((-t.T + q * B) / q) - t.T' / q = q * c - B := by
          linear_combination q⁻¹ * hc + (q * c - B) * hqq
        rw [this]; exact sub_mem (mul_mem g.q.2 c.2) hB
      · simp only [Prod.fst_sub, Prod.snd_sub]
        linear_combination (-q⁻¹) * F3 + (-q * C) * hqq
    · have h1 := hff a b
      have h1' := hff' a b
      have h2 : H.h (t.f a) (t.f b) = 0 := by
        have := hff b a
        rw [if_neg (by rintro ⟨rfl, rfl⟩; exact hcn ⟨rfl, rfl⟩)] at this
        exact this
      rw [if_neg hcn] at h1 h1' ⊢
      rw [h1, map_zero] at F1 F3
      rw [h2, map_zero] at F2
      rw [h1', map_zero] at F3
      simp only [Prod.fst_zero, Prod.snd_zero, zero_add] at F1 F2 F3
      rw [sub_zero, AlgEquiv.apply_symm_apply, F1, F2]
      refine ⟨?_, ?_, -C, neg_mem hC, ?_⟩
      · have : q * A / q = A := by linear_combination A * hqq
        simp only; rw [this]; exact hA
      · have : -(q * B / q) = -B := by linear_combination (-B) * hqq
        simp only; rw [this]; exact neg_mem hB
      · simp only
        linear_combination (-q⁻¹) * F3 + (-q * C) * hqq

end IntegralGeneration

variable {D : Formalism.BasicNotions.D7}

theorem intGenP_holds (Zd : LocDat D) : IntGenP Zd :=
  fun p _ ht a b => IntegralGeneration.zzplus_int (locH Zd p) ht a b

end Formalism.L2.SG.Pf.PCount
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RealDecomp
noncomputable section

open scoped Classical ComplexConjugate

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge Formalism.L2.SG.TypedSets
  Formalism.L2.SG.MassDataConc Formalism.L2.SG.MassDataForm MeasureTheory

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

def RealDecompC : Prop :=
  ∀ t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'), t.relevant → t.G ≠ 0 →
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ) ∧
      ∀ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ →
        ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u', t.pt.1 = g * γ * g'⁻¹

theorem isPtRep_gamW {w : Point D.host.E (D.R.rS + 1)} (h : ∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' w γ) :
    Formalism.L2.SG.RealObj.IsPtRep X u u' w (Formalism.L2.SG.RealObj.gamW X u u' w) := by
  unfold Formalism.L2.SG.RealObj.gamW
  rw [dite_eq_left h]
  exact h.choose_spec

theorem realDecompC_gamW (h : RealDecompC X Y u u')
    (t : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')) (hrel : t.relevant) (hG : t.G ≠ 0) :
    (∃ γ, Formalism.L2.SG.RealObj.IsPtRep X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) γ) ∧
      ∃ g ∈ X.SinfU u, ∃ g' ∈ X.SinfU u',
        t.pt.1 = g * Formalism.L2.SG.RealObj.gamW X u u' (Formalism.L2.SG.PairVal.ptOf t.toTerm) * g'⁻¹ := by
  obtain ⟨hex, hall⟩ := h t hrel hG
  exact ⟨hex, hall _ (isPtRep_gamW X u u' hex)⟩

theorem realDecomp_G_ne (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (h : (Y.tO u u').G s ≠ 0) : s.G ≠ 0 := by
  intro h0
  apply h
  show Formalism.L2.SG.TermOp.Gt s = 0
  simp [Formalism.L2.SG.TermOp.Gt, h0]

theorem liftDecompC_of_real (h : RealDecompC X Y u u') : LiftDecompC X Y u u' κ := by
  intro R ρ s hrel
  exact realDecompC_gamW X Y u u' h s.1 hrel (realDecomp_G_ne X Y u u' s.1 s.2.1)

end Formalism.L2.SG.Pf.RowForm
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CoefCut
noncomputable section

namespace Formalism.L2.SG.Pf.Coef

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Steps

variable {D : Formalism.BasicNotions.D7} (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
  (δ : ∀ p : PlF D, (D.s.atP p).Fp) (u u' : D.what₂.Word)
  (F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)) (what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V))

def yT (γ : TermDef.Term D u u' F0 what₂) (p : PlF D) : MatP D p :=
  CntLocal.ZZP (M := M) δ u u' p (zT γ) * sgnP p

def LocClsE : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w → ∀ p,
    IntP M p (yT M δ u u' F0 what₂ γ p) ∧ InOrbP δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)

def PhCls : Prop :=
  ∀ (T T' : ℕ) (p : PlF D) (w : Point D.host.E (D.R.rS + 1)) (Y Y' : MatP D p), (M p).OK →
    IntP M p Y → InOrbP δ T T' p w Y → InOrbP δ T T' p w Y' → Y' ∈ kkOrb M p Y →
    phL M δ T T' p w Y' = phL M δ T T' p w Y

def PhaseProd : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    (Function.mulSupport fun p => phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)).Finite ∧
    PairVal.phaseAt γ w = ∏ᶠ p, phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p)

def VolProd : Prop :=
  ∀ (γ : TermDef.Term D u u' F0 what₂) (w : Point D.host.E (D.R.rS + 1)), EligAt γ w →
    (Function.mulSupport fun p =>
      (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)).Finite ∧
    (PairVal.vRdef D u u' F0 what₂ δ M γ : ℂ) =
      ((PairVal.orbT D u u' F0 what₂ γ (zT γ)).ncard : ℂ) *
        ∏ᶠ p, (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ)

end Steps

section Assembly

variable {D : Formalism.BasicNotions.D7} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
  {δ : ∀ p : PlF D, (D.s.atP p).Fp}

theorem repL_spec' {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {O : Set (MatP D p)}
    (h : IsLCls M δ T T' p w O) :
    IntP M p (repL M δ T T' p w O) ∧ InOrbP δ T T' p w (repL M δ T T' p w O) ∧ O = kkOrb M p (repL M δ T T' p w O) := by
  unfold repL; rw [dite_eq_left h]; exact h.choose_spec

theorem wtL_congr {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {Y Y' : MatP D p}
    (h : kkOrb M p Y = kkOrb M p Y') : wtL M δ T T' p w Y = wtL M δ T T' p w Y' := by
  unfold wtL; rw [h]

theorem hL_at {T T' : ℕ} {p : PlF D} {w : Point D.host.E (D.R.rS + 1)} {Y : MatP D p}
    (hPC : PhCls M δ) (hOK : (M p).OK) (hY : IntP M p Y) (hO : InOrbP δ T T' p w Y) :
    hL M δ T T' p w (kkOrb M p Y) = phL M δ T T' p w Y * (wtL M δ T T' p w Y : ℂ) := by
  have hcls : IsLCls M δ T T' p w (kkOrb M p Y) := ⟨Y, hY, hO, rfl⟩
  obtain ⟨-, hrO, hrE⟩ := repL_spec' hcls
  unfold hL
  rw [if_pos hcls]
  generalize repL M δ T T' p w (kkOrb M p Y) = R at hrO hrE ⊢
  have hmem : R ∈ kkOrb M p Y := by
    rw [hrE]; exact PCount.mem_kkOrb_self p R
  rw [hPC T T' p w Y R hOK hY hO hrO hmem, wtL_congr hrE.symm]

variable {u u' : D.what₂.Word} {F0 : FlagG (VS D) D.R.rS (CntLocal.Tn u)}
  {what₂ : Finset (Submodule (𝓞 D.host.E) (VS D).V)}

theorem coefProd_of (hA : ∀ p, Agree δ M p) (hC : LocClsE M δ u u' F0 what₂) (hPC : PhCls M δ) (hP : PhaseProd M δ u u' F0 what₂)
    (hV : VolProd M δ u u' F0 what₂) : CoefProd M δ u u' F0 what₂ := by
  intro γ w hγ
  obtain ⟨hPf, hPe⟩ := hP γ w hγ
  obtain ⟨hVf, hVe⟩ := hV γ w hγ
  have hfac : ∀ p, hL M δ (D.mem u).A.T (D.mem u').A.T p w (locT M δ γ p) =
      phL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) *
        (wtL M δ (D.mem u).A.T (D.mem u').A.T p w (yT M δ u u' F0 what₂ γ p) : ℂ) := by
    intro p
    obtain ⟨hyI, hyObP⟩ := hC γ w hγ p
    show hL M δ (D.mem u).A.T (D.mem u').A.T p w (kkOrb M p (yT M δ u u' F0 what₂ γ p)) = _
    exact hL_at hPC (hA p).1 hyI hyObP
  unfold PairVal.cAt
  rw [hPe, hVe, finprod_congr hfac, finprod_mul_distrib hPf hVf]
  ring

end Assembly

end Formalism.L2.SG.Pf.Coef
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LocOrbVal
noncomputable section

namespace Formalism.L2.SG.Pf.LocOrbCut

open MeasureTheory Formalism.MainNotions.S Formalism.L2.SG.Pf.LocOrbSumPf
open Classical

section Cast

variable {K : Type} [CommRing K]

theorem sLow_cast {n n' : ℕ} (h : n' = n) (A : Matrix (Fin n) (Fin n) K) :
    Formalism.DoubleCosetMeasures.sLow (A.submatrix (finCongr h) (finCongr h)) = Formalism.DoubleCosetMeasures.sLow A := by
  subst h
  rfl

theorem sUp_cast {n n' : ℕ} (h : n' = n) (A : Matrix (Fin n) (Fin n) K) :
    Formalism.DoubleCosetMeasures.sUp (A.submatrix (finCongr h) (finCongr h)) = Formalism.DoubleCosetMeasures.sUp A := by
  subst h
  rfl

theorem lowUni_cast {n n' : ℕ} (h : n' = n) {A : Matrix (Fin n) (Fin n) K} (hA : Formalism.DoubleCosetMeasures.IsLowUni A) :
    Formalism.DoubleCosetMeasures.IsLowUni (A.submatrix (finCongr h) (finCongr h)) := by
  subst h
  exact hA

theorem upUni_cast {n n' : ℕ} (h : n' = n) {A : Matrix (Fin n) (Fin n) K} (hA : Formalism.DoubleCosetMeasures.IsUpUni A) :
    Formalism.DoubleCosetMeasures.IsUpUni (A.submatrix (finCongr h) (finCongr h)) := by
  subst h
  exact hA

theorem sLow_one {n : ℕ} : Formalism.DoubleCosetMeasures.sLow (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  simp [Formalism.DoubleCosetMeasures.sLow, Matrix.one_apply, Fin.ext_iff]

theorem sUp_one {n : ℕ} : Formalism.DoubleCosetMeasures.sUp (1 : Matrix (Fin n) (Fin n) K) = 0 := by
  simp [Formalism.DoubleCosetMeasures.sUp, Matrix.one_apply, Fin.ext_iff]

theorem sLow_mem (R : Subring K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j ∈ R) :
    Formalism.DoubleCosetMeasures.sLow A ∈ R := by
  unfold Formalism.DoubleCosetMeasures.sLow
  refine Subring.sum_mem R (fun j _ => ?_)
  split_ifs
  · exact hA _ _
  · exact R.zero_mem

theorem sUp_mem (R : Subring K) {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (hA : ∀ i j, A i j ∈ R) :
    Formalism.DoubleCosetMeasures.sUp A ∈ R := by
  unfold Formalism.DoubleCosetMeasures.sUp
  refine Subring.sum_mem R (fun j _ => ?_)
  split_ifs
  · exact hA _ _
  · exact R.zero_mem

end Cast

section Val

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] [IsTopologicalRing E]

theorem uLow_lowUni {n : ℕ} (x : Loc.IL n → E) : Formalism.DoubleCosetMeasures.IsLowUni (Loc.uLow x) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h' : i < j := OrderDual.toDual_lt_toDual.mp hij
    simp only [Loc.uLow]
    rw [if_neg (ne_of_lt h'), dite_eq_right (not_lt.mpr h'.le)]
  · simp [Loc.uLow]

theorem uUp_upUni {n : ℕ} (w : Loc.Pt E n) (y : Loc.IN w → E) : Formalism.DoubleCosetMeasures.IsUpUni (Loc.uUp w y) := by
  refine ⟨fun i j hij => ?_, fun a => ?_⟩
  · have h' : j < i := hij
    simp only [Loc.uUp]
    rw [if_neg (ne_of_gt h'), dite_eq_right (fun h => absurd h.1 (not_lt.mpr h'.le))]
  · simp [Loc.uUp]

def rI {m : ℕ} (a : Loc.Pt E (m + 1)) (B : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E :=
  B.submatrix (finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a)) (finCongr (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a))

theorem rI_mul {m : ℕ} (a : Loc.Pt E (m + 1)) (A B : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    rI a (A * B) = rI a A * rI a B := by
  unfold rI
  rw [Matrix.submatrix_mul_equiv]

theorem rI_mat {m : ℕ} (a : Loc.Pt E (m + 1)) :
    rI a a.mat = Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
  unfold rI
  rw [Formalism.MainNotions.LocalModelPeriodLattices.mat_eq]
  ext i j
  simp

theorem rI_zQ {m : ℕ} (R : Subring E) (a : Loc.Pt E (m + 1)) (q : Formalism.FourierDecayAlt.A5.Cos R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) :
    rI a (zQ R a q) = Formalism.FourierDecayAlt.A5.orbZ (Formalism.MainNotions.LocalModelPeriodLattices.tr a) (Formalism.FourierDecayAlt.A5.rep R q) := by
  unfold rI zQ
  ext i j
  simp

theorem lowUni_rI {m : ℕ} (a : Loc.Pt E (m + 1)) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) E}
    (hA : Formalism.DoubleCosetMeasures.IsLowUni A) : Formalism.DoubleCosetMeasures.IsLowUni (rI a A) := lowUni_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) hA

theorem upUni_rI {m : ℕ} (a : Loc.Pt E (m + 1)) {A : Matrix (Fin (m + 1)) (Fin (m + 1)) E}
    (hA : Formalism.DoubleCosetMeasures.IsUpUni A) : Formalism.DoubleCosetMeasures.IsUpUni (rI a A) := upUni_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) hA

theorem sLow_rI {m : ℕ} (a : Loc.Pt E (m + 1)) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Formalism.DoubleCosetMeasures.sLow (rI a A) = Formalism.DoubleCosetMeasures.sLow A := sLow_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) A

theorem sUp_rI {m : ℕ} (a : Loc.Pt E (m + 1)) (A : Matrix (Fin (m + 1)) (Fin (m + 1)) E) :
    Formalism.DoubleCosetMeasures.sUp (rI a A) = Formalism.DoubleCosetMeasures.sUp A := sUp_cast (Formalism.MainNotions.LocalModelPeriodLattices.tr_sum a) A

theorem phase_eq (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1))
    (q : Formalism.FourierDecayAlt.A5.Cos M.R (Formalism.MainNotions.LocalModelPeriodLattices.tr a)) (xy : (Loc.IL (m + 1) → E) × (Loc.IN a → E))
    (l ρ : Matrix (Fin (m + 1)) (Fin (m + 1)) E) (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ)
    (hq : zQ M.R a q = l * zAt a xy * ρ) :
    M.psiR (phQ M.R a q) = M.psiR (Loc.simpleLow (Loc.uLow xy.1) + Loc.simpleUp (Loc.uUp a xy.2)) := by
  have hψ : ∀ x ∈ M.R, M.psiR x = 1 := fun r hr => by
    simpa using (Formalism.MainNotions.LocalModelPeriodLattices.selfDual_of_core M hOK 1).2 M.R.one_mem r hr
  have hLo : Formalism.DoubleCosetMeasures.IsLowUni (rI a l * rI a (Loc.uLow xy.1)) :=
    Formalism.DoubleCosetMeasures.isLowUni_mul E (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))
  have hUp : Formalism.DoubleCosetMeasures.IsUpUni (rI a (Loc.uUp a xy.2) * rI a ρ) :=
    Formalism.DoubleCosetMeasures.isUpUni_mul E (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))
  have hv : Formalism.DoubleCosetMeasures.IsLowUni (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := (Formalism.FourierDecayAlt.A5.rep M.R q).1.2.1
  have hu : Formalism.DoubleCosetMeasures.IsUpUni (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) := (Formalism.FourierDecayAlt.A5.rep M.R q).2.2
  have hvPu : (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 * (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) =
      (rI a l * rI a (Loc.uLow xy.1)) * Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
        (rI a (Loc.uUp a xy.2) * rI a ρ) := by
    have h := congrArg (rI a) hq
    rw [rI_zQ] at h
    unfold zAt at h
    rw [rI_mul, rI_mul, rI_mul, rI_mul, rI_mat] at h
    unfold Formalism.FourierDecayAlt.A5.orbZ at h
    rw [h]
    simp only [Matrix.mul_assoc]
  have hLd : IsUnit (rI a l * rI a (Loc.uLow xy.1)).det := by rw [Formalism.DoubleCosetMeasures.isLowUni_det E hLo]; exact isUnit_one
  have hUd : IsUnit (rI a (Loc.uUp a xy.2) * rI a ρ).det := by rw [Formalism.DoubleCosetMeasures.isUpUni_det E hUp]; exact isUnit_one
  have hfix : ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)) *
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
      ((((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) =
      Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 := by
    calc _ = (rI a l * rI a (Loc.uLow xy.1))⁻¹ * ((((Formalism.FourierDecayAlt.A5.rep M.R q).1 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          (((Formalism.FourierDecayAlt.A5.rep M.R q).2 : GL (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E) : Matrix (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) (Fin (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum) E)) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹ := by
          simp only [Matrix.mul_assoc]
      _ = ((rI a l * rI a (Loc.uLow xy.1))⁻¹ * (rI a l * rI a (Loc.uLow xy.1))) *
          Formalism.DoubleCosetMeasures.pt (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 *
          ((rI a (Loc.uUp a xy.2) * rI a ρ) * (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹) := by
          rw [hvPu]; simp only [Matrix.mul_assoc]
      _ = _ := by rw [Matrix.nonsing_inv_mul _ hLd, Matrix.mul_nonsing_inv _ hUd, Matrix.one_mul, Matrix.mul_one]
  have h0 := Formalism.DoubleCosetMeasures.Final.phaseWellDef E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1 (Formalism.MainNotions.LocalModelPeriodLattices.tr a).2 _ _
    (Formalism.DoubleCosetMeasures.isLowUni_mul E (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv) (Formalism.DoubleCosetMeasures.isUpUni_mul E hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)) hfix
  have sa := Formalism.DoubleCosetMeasures.Final.simpleAdd E (Formalism.MainNotions.LocalModelPeriodLattices.tr a).1.sum
  rw [(sa _ _).1 (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hv, (sa _ _).2 hu (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)] at h0
  have hLi := (sa (rI a l * rI a (Loc.uLow xy.1))⁻¹ (rI a l * rI a (Loc.uLow xy.1))).1
    (Formalism.DoubleCosetMeasures.isLowUni_inv E hLo) hLo
  rw [Matrix.nonsing_inv_mul _ hLd, sLow_one] at hLi
  have hUi := (sa (rI a (Loc.uUp a xy.2) * rI a ρ) (rI a (Loc.uUp a xy.2) * rI a ρ)⁻¹).2
    hUp (Formalism.DoubleCosetMeasures.isUpUni_inv E hUp)
  rw [Matrix.mul_nonsing_inv _ hUd, sUp_one] at hUi
  rw [(sa _ _).1 (lowUni_rI a (lowUni_of M hl)) (lowUni_rI a (uLow_lowUni xy.1))] at hLi
  rw [(sa _ _).2 (upUni_rI a (uUp_upUni a xy.2)) (upUni_rI a (upUni_of M hρ))] at hUi
  have hph : phQ M.R a q = Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) +
      (Formalism.DoubleCosetMeasures.sLow (rI a (Loc.uLow xy.1)) + Formalism.DoubleCosetMeasures.sUp (rI a (Loc.uUp a xy.2))) := by
    unfold phQ
    linear_combination h0 + hLi + hUi
  have h1 : Formalism.DoubleCosetMeasures.sLow (rI a l) + Formalism.DoubleCosetMeasures.sUp (rI a ρ) ∈ M.R :=
    add_mem (by rw [sLow_rI]; exact sLow_mem M.R _ hl.2.2) (by rw [sUp_rI]; exact sUp_mem M.R _ hρ.2.2)
  rw [hph, AddChar.map_add_eq_mul, hψ _ h1, one_mul]
  rw [sLow_rI, sUp_rI, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleLow_eq, Formalism.MainNotions.LocalOrbitGerms.Cls.simpleUp_eq]

theorem nIso_orb (M : Loc.Model F E) {n : ℕ} {Z Z' : Matrix (Fin (n + 1)) (Fin (n + 1)) E}
    (l ρ : Matrix (Fin (n + 1)) (Fin (n + 1)) E) (hl : Formalism.MainNotions.S.TieN.IntLow M l) (hρ : Formalism.MainNotions.S.TieN.IntUp M ρ)
    (hZ : Z' = l * Z * ρ) (h1 : ∀ i j, Z' i j ∈ M.R) (h2 : IsUnit Z'.det) (h1' : ∀ i j, Z i j ∈ M.R)
    (h2' : IsUnit Z.det) (Z0 : M.Mat (n + 1)) :
    M.nIso (Formalism.MainNotions.LocalOrbitGerms.Cls.toMat M Z' h1 h2) Z0 = M.nIso (Formalism.MainNotions.LocalOrbitGerms.Cls.toMat M Z h1' h2') Z0 := by
  subst hZ
  unfold Loc.Model.nIso
  rw [Nat.card_congr (Formalism.MainNotions.LocalOrbitGerms.Cls.isoEquiv M _ Z0), Nat.card_congr (Formalism.MainNotions.LocalOrbitGerms.Cls.isoEquiv M _ Z0),
    Formalism.MainNotions.LocalOrbitGerms.Cls.toMat_map, Formalism.MainNotions.LocalOrbitGerms.Cls.toMat_map]
  exact Formalism.DoubleCosetMeasures.Final.isoInv E M.R (n + 1) l ρ Z (lowUni_of M hl) (upUni_of M hρ) hl.2.2 hρ.2.2 _ _ _

theorem val (M : Loc.Model F E) (hOK : M.OK) {m : ℕ} (a : Loc.Pt E (m + 1)) (c : M.Cls m) : IntegrandConstantOnOrbit M a c := by
  intro q xy hI hmem
  obtain ⟨l, ρ, hl, hρ, hq⟩ := hmem
  have hIq : ∀ i j, zQ M.R a q i j ∈ M.R := int_of_mem M hI ⟨l, ρ, hl, hρ, hq⟩
  have hdq : IsUnit (zQ M.R a q).det := Formalism.MainNotions.LocalOrbitGerms.Cls.isUnit_det_sub a _
  have hI' : ∀ i j, (Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2) i j ∈ M.R := hI
  have hdz : IsUnit (Loc.uLow xy.1 * a.mat * Loc.uUp a xy.2).det := by
    rw [Matrix.det_mul, Matrix.det_mul, Formalism.L2.SG.Pf.LocModel.uLow_det, Formalism.L2.SG.Pf.LocModel.uUp_det, one_mul,
      mul_one, Formalism.MainNotions.LocalModelPeriodLattices.det_eq]
    exact Formalism.FourierDecayAlt.P.A5x6.pt_det_isUnit _
  rw [Formalism.MainNotions.LocalOrbitGerms.Cls.bbIntegrand_eq]
  unfold valQ Formalism.MainNotions.LocalOrbitGerms.Cls.GG
  rw [dite_eq_left ⟨hIq, hdq⟩, dite_eq_left ⟨hI', hdz⟩, phase_eq M hOK a q xy l ρ hl hρ hq,
    nIso_orb M l ρ hl hρ hq hIq hdq hI' hdz]
  rfl

end Val

end Formalism.L2.SG.Pf.LocOrbCut
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.PartnerCountLoc
noncomputable section

namespace Formalism.L2.SG.Pf.PCount

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermDef Formalism.L2.SG.DataCut
  Formalism.L2.SG.LsDatumB
open Classical ValuativeRel
open Formalism.L2.SG.Pf.AtPt Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section ZOrb

variable {D : Formalism.BasicNotions.D7} (Zd : LocDat D)

section Typed

variable (p : PlF D) (sg : Loc.SplitAt (D.s.atP p).Fp (D.s.atP p).Ep (D.s.atP p).cj (Loc.resChar p))
  (hR : (D.s.atP p).split = some sg) (g : Loc.SplitG (Zd.M p).L) (hM : (Zd.M p).split = some g)
  (hge : g.e = sg.e) (hgq : g.q = sg.q)
include hR hM hge hgq

theorem zz1' (u u' : D.what₂.Word) (Z : PairVal.MatR D) :
    (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p).map (p1 sg.e) =
      (sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) *
        (Z * Sg D.host.E D.R.rS).map ((p1 sg.e).comp (D.s.atP p).ιE) * Matrix.diagonal (cf Zd p)) -
        (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
  have hcj1 : ∀ x, p1 sg.e ((D.s.atP p).cj x) = p2 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hf1 : ∀ a, p1 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl
  have hf2 : ∀ a, p2 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl
  have hm1 : ∀ k : ℕ, p1 sg.e ((-1 : (D.s.atP p).Ep) ^ k) = (-1) ^ k := fun k => by simp
  ext a b
  simp only [Matrix.map_apply, CntLocal.ZZP, Loc.HermSp.ZZplusOf, hM, CntLocal.ZhatLoc, LsDatumB.sgnP,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, hge, hgq, map_mul, map_sub, fst_proj_symm,
    apply_ite (p1 sg.e), map_zero, Prod.fst_mul, ← adeleInfiniteComponent_apply, ← adele_ext_components, hcj1, hf1, hf2, hm1, Zd.hcj p,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Ecorner, Sg, RingHom.comp_apply, map_pow, map_neg, map_one]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Fin.val_last, Nat.sub_self, pow_zero]
    ring
  · ring

theorem zz2' (u u' : D.what₂.Word) (Z : PairVal.MatR D) :
    (CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p).map (p2 sg.e) =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) *
        ((Z.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
        ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp)) • Ecorner D.R.rS := by
  have hcj2 : ∀ x, p2 sg.e ((D.s.atP p).cj x) = p1 sg.e x := fun x => by
    rw [adeleInfiniteComponent_apply, adele_ext_components, sg.e_cj]; rfl
  have hf1 : ∀ a, p1 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, fst_proj_algebraMap]; rfl
  have hf2 : ∀ a, p2 sg.e (frFac Zd.δ p a) = cf Zd p a := fun a => by rw [frFac_eq, snd_proj_algebraMap]; rfl
  have hm2 : ∀ k : ℕ, p2 sg.e ((-1 : (D.s.atP p).Ep) ^ k) = (-1) ^ k := fun k => by simp
  ext a b
  simp only [Matrix.map_apply, CntLocal.ZZP, Loc.HermSp.ZZplusOf, hM, CntLocal.ZhatLoc, LsDatumB.sgnP,
    Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply, hge, hgq, map_mul, map_sub, snd_proj_symm,
    apply_ite (p2 sg.e), map_zero, Prod.snd_mul, ← adeleInfiniteComponent_apply, ← adele_ext_components, hcj2, hf1, hf2, hm2, Zd.hcj p,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, Ecorner, Sg, RingHom.comp_apply, map_pow, map_neg, map_one,
    Matrix.transpose_apply]
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    simp only [Fin.val_last, Nat.sub_self, pow_zero]
    ring
  · ring

theorem mm1' (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    (modMat Zd.δ Tn T'n p w).map (p1 sg.e) =
      (sg.q : (D.s.atP p).Fp)⁻¹ • (Matrix.diagonal (cf Zd p) * (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE) *
        Matrix.diagonal (cf Zd p)) -
        (if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then -(Tn : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp) else 0) •
          Ecorner D.R.rS := by
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd
  set φ1 := (p1 sg.e).comp (D.s.atP p).ιE with hφ1
  have hq : q ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hqi : Ring.inverse (qE p) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹ := by
    simp only [qE, hR]
    have := Ring.inverse_unit ((Units.mk0 q hq).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)
    simpa only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv,
      Units.val_inv_eq_inv_val] using this
  have htw1 : ∀ s x, p1 sg.e (twist p s x) = p1 sg.e x := fun s x => by
    simp only [twist, hR]; rw [fst_proj_symm]; rfl
  have hta1 : ∀ T T' : ℕ, p1 sg.e (tau0 p T T') = -(T : (D.s.atP p).Fp) * q⁻¹ := fun T T' => by
    simp only [tau0, hR, map_mul, fst_proj_symm, hqi, fst_proj_algebraMap]
  ext a b
  simp only [Matrix.map_apply, modMat_apply', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, ptMat_apply', Ecorner, Matrix.of_apply]
  by_cases hb : b = sgF w a
  · subst hb
    simp only [if_true, modMat_blk, map_sub, map_mul, fst_proj_algebraMap, htw1, hqi, apply_ite (p1 sg.e), hta1, map_zero,
      hφ1, RingHom.comp_apply]
    by_cases ha : a = Fin.last D.R.rS
    · subst ha; split_ifs <;> first | ring1 | (exfalso; rename_i h1 h2; exact h2 h1.2) | (exfalso; rename_i h1 h2; exact h1 h2.2)
    · simp only [ha, false_and, if_false]; ring
  · rw [if_neg hb, if_neg hb, map_zero, map_zero, mul_zero, zero_mul, mul_zero]
    by_cases ha : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
    · obtain ⟨rfl, rfl⟩ := ha
      have : ¬ sgF w (Fin.last D.R.rS) = Fin.last D.R.rS := fun h => hb h.symm
      simp [this]
    · simp [ha]

theorem mm2' (Tn T'n : ℕ) (w : Point D.host.E (D.R.rS + 1)) :
    (modMat Zd.δ Tn T'n p w).map (p2 sg.e) =
      (-(sg.q : (D.s.atP p).Fp)⁻¹) • (Matrix.diagonal (cf Zd p) * (Sg (D.s.atP p).Fp D.R.rS *
        (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) * Sg (D.s.atP p).Fp D.R.rS) * Matrix.diagonal (cf Zd p)) -
        (if sgF w (Fin.last D.R.rS) = Fin.last D.R.rS then (T'n : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp) else 0) •
          Ecorner D.R.rS := by
  set q : (D.s.atP p).Fp := (sg.q : (D.s.atP p).Fp) with hqd
  set φ2 := (p2 sg.e).comp (D.s.atP p).ιE with hφ2
  have hq : q ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hqi : Ring.inverse (qE p) = algebraMap (D.s.atP p).Fp (D.s.atP p).Ep q⁻¹ := by
    simp only [qE, hR]
    have := Ring.inverse_unit ((Units.mk0 q hq).map (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep).toMonoidHom)
    simpa only [Units.coe_map, Units.val_mk0, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, Units.coe_map_inv,
      Units.val_inv_eq_inv_val] using this
  have htw2 : ∀ s x, p2 sg.e (twist p s x) = (-1) ^ s * p2 sg.e x := fun s x => by
    simp only [twist, hR]; rw [snd_proj_symm]; rfl
  have hta2 : ∀ T T' : ℕ, p2 sg.e (tau0 p T T') = (T' : (D.s.atP p).Fp) * q⁻¹ := fun T T' => by
    simp only [tau0, hR, map_mul, snd_proj_symm, hqi, snd_proj_algebraMap]
  ext a b
  simp only [Matrix.map_apply, modMat_apply', Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.mul_diagonal, Matrix.diagonal_mul, ptMat_apply', Ecorner, Matrix.of_apply, Sg]
  by_cases hb : b = sgF w a
  · subst hb
    have hsr := sign_rel (R := (D.s.atP p).Fp) _ _ _ (nu_parity w a)
    simp only [if_true, modMat_blk, map_sub, map_mul, snd_proj_algebraMap, htw2, hqi, apply_ite (p2 sg.e), hta2, map_zero,
      hφ2, RingHom.comp_apply, hsr]
    by_cases ha : a = Fin.last D.R.rS
    · subst ha; split_ifs <;> first | ring1 | (exfalso; rename_i h1 h2; exact h2 h1.2) | (exfalso; rename_i h1 h2; exact h1 h2.2)
    · simp only [ha, false_and, if_false]; ring
  · rw [if_neg hb, if_neg hb, map_zero, map_zero, mul_zero, zero_mul, mul_zero, zero_mul]
    by_cases ha : a = Fin.last D.R.rS ∧ b = Fin.last D.R.rS
    · obtain ⟨rfl, rfl⟩ := ha
      have : ¬ sgF w (Fin.last D.R.rS) = Fin.last D.R.rS := fun h => hb h.symm
      simp [this]
    · simp [ha]

theorem zzpSgn_orb_typed (u u' : D.what₂.Word) {w : Point D.host.E (D.R.rS + 1)} {Z L B : PairVal.MatR D}
    (hL : IsLo L) (hB : IsUp B) (hf' : Z * Sg D.host.E D.R.rS = L * ptMat w * B) :
    ∃ uL uU : MatP D p, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p = uL * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * uU := by
  have hq : (sg.q : (D.s.atP p).Fp) ≠ 0 := fun h => sg.q_irr.ne_zero (Subtype.ext h)
  have hA' : Z = L * ptMat w * B * Sg D.host.E D.R.rS := by
    rw [← hf', Matrix.mul_assoc, sg_sq, Matrix.mul_one]
  have hs0 : ∀ a : Fin (D.R.rS + 1), (-1 : (D.s.atP p).Fp) ^ (D.R.rS - a.val) ≠ 0 :=
    fun a => pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)
  obtain ⟨L1, U1, hL1, hU1, h1⟩ := generic_comp (sgF w) (sgF_sgF _)
    (isLo_map ((p1 sg.e).comp (D.s.atP p).ιE) hL) (isUp_map ((p1 sg.e).comp (D.s.atP p).ιE) hB)
    (W := (ptMat w).map ((p1 sg.e).comp (D.s.atP p).ιE))
    (fun a b hb => by simp only [Matrix.map_apply, ptMat_apply', if_neg hb, map_zero])
    (fun a => by
      simp only [Matrix.map_apply, ptMat_apply', if_true]
      exact (map_ne_zero _).2 (pTau_ne' _ a))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (sg.q : (D.s.atP p).Fp)⁻¹ (inv_ne_zero hq)
    (-(((D.mem u).A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  obtain ⟨L2, U2, hL2, hU2, h2⟩ := generic_comp (sgF w) (sgF_sgF _)
    (isLo_conj (isLo_transpose (isUp_map ((p2 sg.e).comp (D.s.atP p).ιE) hB)) _ _ (fun a => sgn_sq' D.R.rS a) :
      IsLo (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    (isUp_conj (isUp_transpose (isLo_map ((p2 sg.e).comp (D.s.atP p).ιE) hL)) _ _ (fun a => sgn_sq' D.R.rS a) :
      IsUp (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS))
    (L := Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS)
    (B := Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS)
    (W := Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) *
      Sg (D.s.atP p).Fp D.R.rS)
    (fun a b hb => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_neg hb, map_zero,
        mul_zero, zero_mul])
    (fun a => by
      simp only [Sg, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply', if_true]
      exact mul_ne_zero (mul_ne_zero (hs0 _) ((map_ne_zero _).2 (pTau_ne' _ a))) (hs0 _))
    (cf Zd p) (cfi Zd p) (cfi_cf Zd p) (-(sg.q : (D.s.atP p).Fp)⁻¹) (neg_ne_zero.2 (inv_ne_zero hq))
    ((((D.mem u').A.T : ℕ) : (D.s.atP p).Fp) / (sg.q : (D.s.atP p).Fp))
  have e2 : (Z.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS =
      (Sg (D.s.atP p).Fp D.R.rS * (B.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) *
        (Sg (D.s.atP p).Fp D.R.rS * (ptMat w).map ((p2 sg.e).comp (D.s.atP p).ιE) *
          Sg (D.s.atP p).Fp D.R.rS) *
        (Sg (D.s.atP p).Fp D.R.rS * (L.map ((p2 sg.e).comp (D.s.atP p).ιE)).transpose * Sg (D.s.atP p).Fp D.R.rS) := by
    rw [hA', Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, sg_map]
    exact fact2 _ _ _ _ (sg_sq _) (Matrix.diagonal_transpose _) (by rw [← Matrix.transpose_map, ptMat_transpose])
  refine goal_of (isLo_glue sg.e hL1 hL2) (isUp_glue sg.e hU1 hU2) (mat_eq sg.e ?_ ?_)
  · rw [zz1' Zd p sg hR g hM hge hgq, hf']
    conv_lhs => rw [Matrix.map_mul, Matrix.map_mul]
    rw [h1]
    conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_fst, glue_map_fst]
    rw [mm1' Zd p sg hR g hM hge hgq]
  · rw [zz2' Zd p sg hR g hM hge hgq, e2, h2]
    conv_rhs => rw [Matrix.map_mul, Matrix.map_mul, glue_map_snd, glue_map_snd]
    rw [mm2' Zd p sg hR g hM hge hgq]

end Typed

theorem zzpSgn_orb (u u' : D.what₂.Word) {w : Point D.host.E (D.R.rS + 1)} {Z : PairVal.MatR D} (hZ : AtMat w Z)
    (p : PlF D) :
    ∃ uL uU : MatP D p, (∀ a, uL a a = 1 ∧ uU a a = 1) ∧ (∀ a b, a < b → uL a b = 0 ∧ uU b a = 0) ∧
      CntLocal.ZZP (M := Zd.M) Zd.δ u u' p Z * LsDatumB.sgnP p = uL * modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w * uU := by
  obtain ⟨L, U, hL, hU, e⟩ := hZ
  have hL' := isLo_of_uni hL
  have hU' := isUp_of_uni hU
  have hf' : Z * Sg D.host.E D.R.rS = L * ptMat w * U := by rw [← zhatOM_eq]; exact e
  have hAg := (Zd.agree p).2.2.2.2.2
  rcases hM : (Zd.M p).split with _ | g <;> rcases hR : (D.s.atP p).split with _ | sg <;>
    simp only [hM, hR] at hAg
  · set ι := (D.s.atP p).ιE
    set fr : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cf Zd p a)
    set fri : Fin (D.R.rS + 1) → (D.s.atP p).Ep := fun a => algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (cfi Zd p a)
    have hfr : ∀ a, fri a * fr a = 1 := fun a => by simp only [fr, fri, ← map_mul, cfi_cf, map_one]
    have hfr' : ∀ a, fr a * fri a = 1 := fun a => by simp only [fr, fri, ← map_mul, cf_cfi, map_one]
    have hmod : Matrix.diagonal fr * (ptMat w).map ι * Matrix.diagonal fr =
        modMat Zd.δ (D.mem u).A.T (D.mem u').A.T p w := by
      ext a b
      rw [modMat_apply', Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.map_apply, ptMat_apply']
      by_cases hb : b = sgF w a
      · rw [if_pos hb, if_pos hb, modMat_blk Zd]
        simp only [twist, qE, tau0, hR, Ring.inverse_one, mul_one, ite_self, sub_zero, map_mul, fr]
        subst hb
        ring
      · rw [if_neg hb, if_neg hb, map_zero, mul_zero, zero_mul]
    rw [zzp_sgn_ord Zd u u' p hM Z, hf', Matrix.map_mul, Matrix.map_mul, regroup fr fri hfr, hmod]
    exact goal_of (isLo_conj (isLo_map ι hL') fr fri hfr') (isUp_conj (isUp_map ι hU') fri fr hfr) rfl
  · exact zzpSgn_orb_typed Zd p sg hR g hM hAg.1 hAg.2 u u' hL' hU' hf'

end ZOrb

end Formalism.L2.SG.Pf.PCount
end
end
