module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.OrthogonalComplementRational
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.GenericRatioOfBoundHolds

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.FrameZEqLinZu
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.SecondNormalTransport
noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat

namespace Formalism.L2.SG.Pf.RowForm.ClassFramePositivePartDecomposition

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E}

section Basic

variable {r : ℕ} {T : E}

theorem hswap (x y : S.V) : S.hT y x = star (S.hT x y) := PI.ScalarPairDr.W.hT_swap (S := S) x y

theorem e_X (F : FlagG S r T) (a : Fin r) {x : S.V} (hx : x ∈ F.X) : S.hT (F.e a) x = 0 :=
  ((PI.ScalarPairDr.W.mem_orth_Xplus (S := S) F).1 (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F hx)).1 a

theorem z_X (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT F.z x = 0 :=
  ((PI.ScalarPairDr.W.mem_orth_Xplus (S := S) F).1 (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F hx)).2

theorem xplus_dec (F : FlagG S r T) {v : S.V} (hv : v ∈ F.Xplus) : ∃ a : E, ∃ x ∈ F.X, v = a • F.z + x := by
  change v ∈ F.X ⊔ Submodule.span E {F.z} at hv
  obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
  exact ⟨a, x, hx, by abel⟩

theorem xplus_mem (F : FlagG S r T) (a : E) {x : S.V} (hx : x ∈ F.X) : a • F.z + x ∈ F.Xplus :=
  Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
    (Submodule.mem_sup_left hx)

theorem zz_ne (F : FlagG S r T) (hT : T ≠ 0) : S.hT F.z F.z ≠ 0 := by
  rw [F.z_norm]; exact neg_ne_zero.mpr hT

theorem indep {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (C C' : Fin (r + 1) → E)
    (h : ∑ a, C a • F.fvec a + ∑ b, C' b • F'.fvec b = 0) : C = 0 ∧ C' = 0 :=
  PI.UnitaryGroupMassFormula.BetaLUniq.GN.coeffs_zero F F' C C' 0 h.symm (fun _ => by simp) (fun _ => by simp) hG

theorem sum_fvec (F : FlagG S r T) (c : Fin r → E) (a : E) :
    ∑ i, (Fin.snoc (α := fun _ => E) c a : Fin (r + 1) → E) i • F.fvec i = a • F.z + ∑ i, c i • F.e i := by
  rw [Fin.sum_univ_castSucc]
  simp only [FlagG.fvec, Fin.snoc_castSucc, Fin.snoc_last]
  abel

theorem x_sum (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : ∃ c : Fin r → E, ∑ i, c i • F.e i = x :=
  (Submodule.mem_span_range_iff_exists_fun E).1 hx

theorem disj {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) {v : S.V} (hv : v ∈ F.X)
    (hv' : v ∈ F'.Xplus) : v = 0 := by
  obtain ⟨c, hc⟩ := x_sum F hv
  obtain ⟨a', x', hx', e'⟩ := xplus_dec F' hv'
  obtain ⟨c', hc'⟩ := x_sum F' hx'
  have h := indep F F' hG (Fin.snoc (α := fun _ => E) c 0) (Fin.snoc (α := fun _ => E) (-c') (-a')) (by
    rw [sum_fvec, sum_fvec]
    simp only [zero_smul, zero_add, Pi.neg_apply, neg_smul, Finset.sum_neg_distrib]
    rw [hc, hc', e']; abel)
  have ha : a' = 0 := by
    have := congrFun h.2 (Fin.last r)
    simpa using this
  have hc0 : c' = 0 := by
    funext i
    have := congrFun h.2 (Fin.castSucc i)
    simpa using this
  rw [e', ← hc', ha, hc0]
  simp

theorem indep' {T' : E} (F : FlagG S r T) (F' : FlagG S r T') (hG : Gflag F F' ≠ 0) (C' : Fin (r + 1) → E)
    (h : ∑ b, C' b • F'.fvec b = 0) : C' = 0 :=
  (indep F F' hG 0 C' (by simp [h])).2

end Basic

section Pair

variable {Λ : Submodule (𝓞 E) S.V} {r : ℕ} {T T' : E} {F : LFlag S r T} {F' F'' : LFlag S r T'}
  {β : S.V ≃ₗ[E] S.V}

theorem zt_mem (F : LFlag S r T) (F' : LFlag S r T') : F.zt ∈ UUE Λ F F' ∧ F'.zt ∈ UUE Λ F F' := by
  constructor
  · apply Submodule.subset_span
    show F.zt ∈ UU Λ F F'
    unfold UU
    exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  · apply Submodule.subset_span
    show F'.zt ∈ UU Λ F F'
    unfold UU
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem xplus_le (hΛ : Submodule.IsFullLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') (hz : F.zt = F.fl.z) :
    Xplus F ≤ UUE Λ F F' := by
  change F.fl.X ⊔ Submodule.span E {F.fl.z} ≤ _
  refine sup_le (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE S Λ hΛ F F') ?_
  rw [Submodule.span_le, Set.singleton_subset_iff, ← hz]
  exact (zt_mem (Λ := Λ) F F').1

theorem xplus_le' (hΛ : Submodule.IsFullLattice E Λ) (F : LFlag S r T) (F' : LFlag S r T') (hz' : F'.zt = F'.fl.z) :
    Xplus F' ≤ UUE Λ F F' := by
  change F'.fl.X ⊔ Submodule.span E {F'.fl.z} ≤ _
  refine sup_le (PI.UnitaryGroupMassFormula.BetaLUniq.Xsp_le_UUE' S Λ hΛ F F') ?_
  rw [Submodule.span_le, Set.singleton_subset_iff, ← hz']
  exact (zt_mem (Λ := Λ) F F').2

theorem orth_xplus_iff {T₀ : E} (G : LFlag S r T₀) {v : S.V} :
    v ∈ orth S (Xplus G) ↔ (∀ a, S.hT (G.fl.e a) v = 0) ∧ S.hT G.fl.z v = 0 :=
  PI.ScalarPairDr.W.mem_orth_Xplus (S := S) G.fl

theorem ylift_rev (hTh : Th Λ F F' F'' β = Hp Λ F F') {y : S.V} (hy : y ∈ Ylift Λ F F'') : y ∈ UUE Λ F F' := by
  rw [← PI.UnitaryGroupMassFormula.ScalEquivGen.orthOrthQ (UUE Λ F F'), PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ]
  intro h hh
  change h ∈ Hp Λ F F' at hh
  rw [← hTh] at hh
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hh
  rw [PI.UnitaryGroupMassFormula.ScalEquivGen.memThPairsQ] at hp
  have hp2 : p.2 ∈ orth S (UUE Λ F F'') := hp.1.1.2
  have hy1 : y ∈ UUE Λ F F'' := hy.1
  have hy2 : y ∈ orth S (Xplus F) := hy.2
  have e1 : S.hT p.2 y = 0 :=
    PI.UnitaryGroupMassFormula.ScalEquivGen.hTCommQ.mp ((PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp hp2) y hy1)
  have e2 : S.hT (p.1 - p.2) y = 0 :=
    PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp (PI.UnitaryGroupMassFormula.ScalEquivGen.orthAntiQ (PI.UnitaryGroupMassFormula.ScalEquivGen.XspLeXplusQ F) hy2) _ hp.1.2
  show S.hT p.1 y = 0
  have e : p.1 = (p.1 - p.2) + p.2 := by abel
  rw [e, map_add (f := _), LinearMap.add_apply, e1, e2, add_zero]

variable (hΛ : Submodule.IsFullLattice E Λ) (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) (hz'' : F''.zt = F''.fl.z)
include hΛ hz hz' hz''

theorem firstNormal_transport (hT : T ≠ 0) (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') (hSc : IsScalar Λ F F' F'' β)
    {ν : S.V} (hν : ν ∈ Xplus F') (he : ∀ a, S.hT (F.fl.e a) ν = 0) (hzν : S.hT F.fl.z ν = 1) :
    ∃ ν₂ ∈ Xplus F'', (∀ a, S.hT (F.fl.e a) ν₂ = 0) ∧ S.hT F.fl.z ν₂ = 1 ∧ ν - ν₂ ∈ Xsp F := by
  have hzz := zz_ne F.fl hT
  set c : E := (S.hT F.fl.z F.fl.z)⁻¹ with hc
  set y : S.V := ν - c • F.fl.z with hy
  have hyU : y ∈ UUE Λ F F' :=
    Submodule.sub_mem _ (xplus_le' hΛ F F' hz' hν)
      (Submodule.smul_mem _ _ (hz ▸ (zt_mem (Λ := Λ) F F').1))
  have hyO : y ∈ orth S (Xplus F) := by
    rw [orth_xplus_iff]
    refine ⟨fun a => ?_, ?_⟩
    · rw [hy, map_sub, map_smul, he a, F.fl.z_orth a, smul_zero, sub_zero]
    · rw [hy, map_sub, map_smul, hzν, smul_eq_mul, hc, inv_mul_cancel₀ hzz, sub_self]
  have hy' : y ∈ Ylift Λ F F' := ⟨hyU, hyO⟩
  have hy'' : y ∈ Ylift Λ F F'' := ⟨PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh hy', hyO⟩
  obtain ⟨α', x', hx', hνe⟩ := xplus_dec F'.fl hν
  have hsg : SgRel F F' y 0 (-c) α' := by
    refine ⟨0, Submodule.zero_mem _, x', hx', ?_⟩
    rw [hz, hz', hy, hνe, neg_smul]
    abel
  have h0 : y - y ∈ Xsp F := by rw [sub_self]; exact Submodule.zero_mem _
  have h0' : (0 : S.V) - β 0 ∈ Xsp F'' := by simp
  obtain ⟨x₂, hx₂, x'', hx'', h3⟩ :=
    (hSc y hy' y hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' (-c) α').1 hsg
  rw [hz, hz''] at h3
  refine ⟨α' • F''.fl.z + x'', xplus_mem F''.fl α' hx'', ?_⟩
  have hd : ν - (α' • F''.fl.z + x'') = x₂ := by
    have h4 : ν = (-c) • F.fl.z + x₂ + (α' • F''.fl.z + x'') + c • F.fl.z := by
      rw [← h3, hy]; abel
    rw [h4, neg_smul]; abel
  have hν₂ : α' • F''.fl.z + x'' = ν - x₂ := by rw [← hd]; abel
  refine ⟨fun a => ?_, ?_, hd ▸ hx₂⟩
  · rw [hν₂, map_sub, he a, e_X F.fl a hx₂, sub_zero]
  · rw [hν₂, map_sub, hzν, z_X F.fl hx₂, sub_zero]

theorem ker_transport (hG' : Gflag F.fl F'.fl ≠ 0) (hTh : Th'' Λ F F' F'' β = Hp Λ F F'')
    (hSc : IsScalar Λ F F' F'' β) {d : S.V} (hd : d ∈ Xplus F') (hdO : d ∈ orth S (Xplus F)) (hd0 : d ≠ 0) :
    ∃ d₂ ∈ Xplus F'', d₂ ∈ orth S (Xplus F) ∧ d₂ ≠ 0 := by
  have hy' : d ∈ Ylift Λ F F' := ⟨xplus_le' hΛ F F' hz' hd, hdO⟩
  have hy'' : d ∈ Ylift Λ F F'' := ⟨PI.UnitaryGroupMassFormula.ScalEquivGen.yliftMemQ hTh hy', hdO⟩
  obtain ⟨α', x', hx', hde⟩ := xplus_dec F'.fl hd
  have hsg : SgRel F F' d 0 0 α' := by
    refine ⟨0, Submodule.zero_mem _, x', hx', ?_⟩
    rw [hz', hde, zero_smul]
    abel
  have h0 : d - d ∈ Xsp F := by rw [sub_self]; exact Submodule.zero_mem _
  have h0' : (0 : S.V) - β 0 ∈ Xsp F'' := by simp
  obtain ⟨x₂, hx₂, x'', hx'', h3⟩ :=
    (hSc d hy' d hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' 0 α').1 hsg
  rw [hz''] at h3
  have hd2 : α' • F''.fl.z + x'' = d - x₂ := by
    rw [sub_zero] at h3; rw [h3, zero_smul]; abel
  refine ⟨α' • F''.fl.z + x'', xplus_mem F''.fl α' hx'', ?_, ?_⟩
  · rw [hd2]
    exact Submodule.sub_mem _ hdO (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F.fl hx₂)
  · intro h
    rw [hd2, sub_eq_zero] at h
    exact hd0 (disj F.fl F'.fl hG' (h ▸ hx₂) hd)

theorem ker_transport_rev (hG'' : Gflag F.fl F''.fl ≠ 0) (hTh : Th Λ F F' F'' β = Hp Λ F F')
    (hSc : IsScalar Λ F F' F'' β) {d : S.V} (hd : d ∈ Xplus F'') (hdO : d ∈ orth S (Xplus F)) (hd0 : d ≠ 0) :
    ∃ d₁ ∈ Xplus F', d₁ ∈ orth S (Xplus F) ∧ d₁ ≠ 0 := by
  have hy'' : d ∈ Ylift Λ F F'' := ⟨xplus_le' hΛ F F'' hz'' hd, hdO⟩
  have hy' : d ∈ Ylift Λ F F' := ⟨ylift_rev hTh hy'', hdO⟩
  obtain ⟨α', x', hx', hde⟩ := xplus_dec F''.fl hd
  have hsg : SgRel F F'' d 0 0 α' := by
    refine ⟨0, Submodule.zero_mem _, x', hx', ?_⟩
    rw [hz'', hde, zero_smul]
    abel
  have h0 : d - d ∈ Xsp F := by rw [sub_self]; exact Submodule.zero_mem _
  have h0' : (0 : S.V) - β 0 ∈ Xsp F'' := by simp
  obtain ⟨x₂, hx₂, x'', hx'', h3⟩ :=
    (hSc d hy' d hy'' 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) h0 h0' 0 α').2 hsg
  rw [hz'] at h3
  have hd2 : α' • F'.fl.z + x'' = d - x₂ := by
    rw [sub_zero] at h3; rw [h3, zero_smul]; abel
  refine ⟨α' • F'.fl.z + x'', xplus_mem F'.fl α' hx'', ?_, ?_⟩
  · rw [hd2]
    exact Submodule.sub_mem _ hdO (PI.ScalarPairDr.W.X_le_orth_Xplus (S := S) F.fl hx₂)
  · intro h
    rw [hd2, sub_eq_zero] at h
    exact hd0 (disj F.fl F''.fl hG'' (h ▸ hx₂) hd)

omit hz hz' hz'' hΛ in
theorem xflag_map (hβe : ∀ b, β (F'.fl.e b) = F''.fl.e b) (j : ℕ) :
    (Xflag F' j).map (β : S.V →ₗ[E] S.V) = Xflag F'' j := by
  show (Submodule.span E (F'.fl.e '' {i | i.1 < j})).map (β : S.V →ₗ[E] S.V) =
    Submodule.span E (F''.fl.e '' {i | i.1 < j})
  rw [Submodule.map_span, Set.image_image]
  congr 1
  exact Set.image_congr fun b _ => by simp [hβe]

omit hz hz' hz'' hΛ in
theorem symm_X (hβe : ∀ b, β (F'.fl.e b) = F''.fl.e b) {x : S.V} (hx : x ∈ Xsp F'') : β.symm x ∈ Xsp F' := by
  have h := xflag_map hβe r
  rw [PI.UnitaryGroupMassFormula.ScalEquivGen.XflagTopQ, PI.UnitaryGroupMassFormula.ScalEquivGen.XflagTopQ] at h
  rw [← h] at hx
  obtain ⟨x', hx', rfl⟩ := Submodule.mem_map.mp hx
  simpa using hx'

theorem secondNormal_transport (hT' : T' ≠ 0) (hi : β ∈ Formalism.HermitianLatticesTheory.isom S.hT) (hβe : ∀ b, β (F'.fl.e b) = F''.fl.e b)
    (hβz : β F'.fl.z = F''.fl.z) (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') (hSc : IsScalar Λ F F' F'' β)
    {x₁ : S.V} (hx : x₁ ∈ Xplus F) (he : ∀ b, S.hT x₁ (F'.fl.e b) = 0) (hzx : S.hT x₁ F'.fl.z = 1) :
    ∃ x₂ ∈ Xplus F, (∀ b, S.hT x₂ (F''.fl.e b) = 0) ∧ S.hT x₂ F''.fl.z = 1 ∧ β.symm x₂ - x₁ ∈ Xsp F' := by
  have hzz := zz_ne F'.fl hT'
  set c : E := (S.hT F'.fl.z F'.fl.z)⁻¹ with hc
  set y : S.V := x₁ - c • F'.fl.z with hy
  have hyU : y ∈ UUE Λ F F' :=
    Submodule.sub_mem _ (xplus_le hΛ F F' hz hx)
      (Submodule.smul_mem _ _ (hz' ▸ (zt_mem (Λ := Λ) F F').2))
  have hyO : y ∈ orth S (Xplus F') := by
    rw [orth_xplus_iff]
    refine ⟨fun b => ?_, ?_⟩
    · rw [hy, map_sub, map_smul, hswap, he b, F'.fl.z_orth b, star_zero, smul_zero, sub_zero]
    · rw [hy, map_sub, map_smul, hswap, hzx, star_one, smul_eq_mul, hc, inv_mul_cancel₀ hzz, sub_self]
  have hy' : y ∈ Ylift' Λ F F' := ⟨hyU, hyO⟩
  have hby : β y ∈ UUE Λ F F'' := PI.UnitaryGroupMassFormula.ScalEquivGen.ylift'MemQ hi (xflag_map hβe) hTh hy'
  have hyO' := (orth_xplus_iff F').1 hyO
  have hbyO : β y ∈ orth S (Xplus F'') := by
    rw [orth_xplus_iff]
    refine ⟨fun b => ?_, ?_⟩
    · rw [← hβe b, hi]; exact hyO'.1 b
    · rw [← hβz, hi]; exact hyO'.2
  have hby' : β y ∈ Ylift' Λ F F'' := ⟨hby, hbyO⟩
  obtain ⟨a, ξ, hξ, hxe⟩ := xplus_dec F.fl hx
  have hsg : SgRel F F' 0 y (-a) c := by
    refine ⟨-ξ, Submodule.neg_mem _ hξ, 0, Submodule.zero_mem _, ?_⟩
    rw [hz, hz', hy, hxe, neg_smul]
    abel
  have h0 : (0 : S.V) - 0 ∈ Xsp F := by simp
  have h0' : β y - β y ∈ Xsp F'' := by rw [sub_self]; exact Submodule.zero_mem _
  obtain ⟨x₃, hx₃, x'', hx'', h3⟩ :=
    (hSc 0 (Submodule.zero_mem _) 0 (Submodule.zero_mem _) y hy' (β y) hby' h0 h0' (-a) c).1 hsg
  rw [hz, hz''] at h3
  have hx2 : a • F.fl.z + -x₃ = β y + c • F''.fl.z + x'' := by
    have h4 : β y = -((-a) • F.fl.z + x₃ + (c • F''.fl.z + x'')) := by rw [← h3]; abel
    rw [h4, neg_smul]; abel
  refine ⟨a • F.fl.z + -x₃, xplus_mem F.fl a (Submodule.neg_mem _ hx₃), ?_⟩
  have hzz'' : S.hT F''.fl.z F''.fl.z = S.hT F'.fl.z F'.fl.z := by rw [← hβz, hi]
  have k1 : ∀ b, S.hT (F''.fl.e b) (a • F.fl.z + -x₃) = 0 := by
    intro b
    rw [hx2, map_add (f := _), map_add (f := _), map_smul, (orth_xplus_iff F'').1 hbyO |>.1 b, F''.fl.z_orth b,
      e_X F''.fl b hx'', smul_zero, zero_add, add_zero]
  have k2 : S.hT F''.fl.z (a • F.fl.z + -x₃) = 1 := by
    rw [hx2, map_add (f := _), map_add (f := _), map_smul, (orth_xplus_iff F'').1 hbyO |>.2, z_X F''.fl hx'', hzz'', smul_eq_mul,
      hc, inv_mul_cancel₀ hzz, zero_add, add_zero]
  refine ⟨fun b => ?_, ?_, ?_⟩
  · rw [hswap, k1 b, star_zero]
  · rw [hswap, k2, star_one]
  · have hs : β.symm F''.fl.z = F'.fl.z := by rw [← hβz]; simp
    rw [hx2, map_add (f := _), map_add (f := _), map_smul, LinearEquiv.symm_apply_apply, hs, hy]
    have : x₁ - c • F'.fl.z + c • F'.fl.z + β.symm x'' - x₁ = β.symm x'' := by abel
    rw [this]
    exact symm_X hβe hx''


omit hz hz' hz'' hΛ in
theorem orthogonal_transport (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y₂ : S.V} (hy : y₂ ∈ Hp Λ F F'') :
    ∃ y₁ ∈ Hp Λ F F', y₁ - y₂ ∈ Xsp F ∧ β y₁ - y₂ ∈ Xsp F'' := by
  rw [← hTh] at hy
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hy
  rw [PI.UnitaryGroupMassFormula.ScalEquivGen.memThPairsQ] at hp
  exact ⟨p.1, hp.1.1.1, hp.1.2, hp.2⟩

end Pair

end Formalism.L2.SG.Pf.RowForm.ClassFramePositivePartDecomposition
end
end

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowForm.ClassFrameOO2Aux
  Formalism.L2.SG.Pf.RowForm.ClassFramePositivePartDecomposition

open scoped Matrix

namespace Formalism.L2.SG.Pf.RowForm.ClassFrameFirstNormalAdjugate

section Coord

variable {D : D7} (X : HidaSetting D) (u u' : D.what₂.Word)

theorem hE_comb (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (c : Fin (D.R.rS + 1) → X.B.I.E)
    (a : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.Level.hE X (famE X u a) (∑ b, c b • (M *ᵥ famE X u' b)) = (ZE X u u' M *ᵥ c) a := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Formalism.L2.SG.Pf.Level.hEl_apply, map_sum]
  simp only [map_smul, Formalism.L2.SG.Pf.Level.hEl_apply, smul_eq_mul, Matrix.mulVec, dotProduct, ZE]
  exact Finset.sum_congr rfl fun b _ => mul_comm _ _

theorem firstNormal_eq_adjugate (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    nu1E X u u' M = ∑ b, ((ZE X u u' M).det⁻¹ * (ZE X u u' M).adjugate b (Fin.last _)) • (M *ᵥ famE X u' b) := by
  unfold nu1E xPrE
  rw [Finset.smul_sum]
  simp only [smul_smul]

theorem hermitian_firstNormal (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (hdet : (ZE X u u' M).det ≠ 0)
    (a : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.Level.hE X (famE X u a) (nu1E X u u' M) = if a = Fin.last _ then 1 else 0 := by
  rw [firstNormal_eq_adjugate, hE_comb]
  simp only [Matrix.mulVec, dotProduct]
  have h1 : ∑ b, ZE X u u' M a b * ((ZE X u u' M).det⁻¹ * (ZE X u u' M).adjugate b (Fin.last _)) =
      (ZE X u u' M).det⁻¹ * (ZE X u u' M * (ZE X u u' M).adjugate) a (Fin.last _) := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [h1, Matrix.mul_adjugate, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs
  · field_simp
  · simp

def x2E (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : Fin X.B.I.n → X.B.I.E :=
  (star (ZE X u u' M).det)⁻¹ • xUnE X u u' M

theorem hE_sum_left {m : ℕ} (k : Fin m → X.B.I.E) (f : Fin m → Fin X.B.I.n → X.B.I.E) (y : Fin X.B.I.n → X.B.I.E) :
    Formalism.L2.SG.Pf.Level.hE X (∑ a, star (k a) • f a) y = ∑ a, k a * Formalism.L2.SG.Pf.Level.hE X (f a) y := by
  conv_lhs => rw [Formalism.L2.SG.Pf.Level.hE_symm]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Formalism.L2.SG.Pf.Level.hEl_apply, map_sum, star_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_smul, Formalism.L2.SG.Pf.Level.hEl_apply, smul_eq_mul, star_mul', star_star, ← Formalism.L2.SG.Pf.Level.hE_symm]

theorem secondNormal_eq_adjugate (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) :
    x2E X u u' M = ∑ a, star ((ZE X u u' M).det⁻¹ * (ZE X u u' M).adjugate (Fin.last _) a) • famE X u a := by
  unfold x2E xUnE
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [smul_smul, star_mul', star_inv₀]

theorem hermitian_secondNormal (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) (hdet : (ZE X u u' M).det ≠ 0)
    (b : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.Level.hE X (x2E X u u' M) (M *ᵥ famE X u' b) = if b = Fin.last _ then 1 else 0 := by
  rw [secondNormal_eq_adjugate, hE_sum_left]
  have h1 : ∑ a, (ZE X u u' M).det⁻¹ * (ZE X u u' M).adjugate (Fin.last _) a *
      Formalism.L2.SG.Pf.Level.hE X (famE X u a) (M *ᵥ famE X u' b) =
      (ZE X u u' M).det⁻¹ * ((ZE X u u' M).adjugate * ZE X u u' M) (Fin.last _) b := by
    rw [Matrix.mul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by simp only [ZE]; ring
  rw [h1, Matrix.adjugate_mul, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  split_ifs with h h' h'
  · field_simp
  · exact absurd h.symm h'
  · exact absurd h'.symm h
  · simp

theorem secondNormal_eq_mulVec (M Mi : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) : nu2E X u u' M Mi = Mi *ᵥ x2E X u u' M := by
  unfold nu2E x2E
  rw [Matrix.mulVec_smul]

end Coord

section Flag

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T : E}

theorem fvec_mem_xplus (F : FlagG S r T) (a : Fin (r + 1)) : F.fvec a ∈ F.Xplus := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp only [FlagG.fvec, Fin.snoc_last]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  · simp only [FlagG.fvec, Fin.snoc_castSucc]
    exact Submodule.mem_sup_left (Submodule.subset_span ⟨i, rfl⟩)

theorem sum_mem_xplus (F : FlagG S r T) (c : Fin (r + 1) → E) : ∑ a, c a • F.fvec a ∈ F.Xplus :=
  Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (fvec_mem_xplus F a)

theorem orth_fvec (F : FlagG S r T) {v : S.V} : v ∈ orth S F.Xplus ↔ ∀ a, S.hT (F.fvec a) v = 0 := by
  rw [PI.ScalarPairDr.W.mem_orth_Xplus (S := S) F]
  constructor
  · rintro ⟨h1, h2⟩ a
    refine Fin.lastCases ?_ (fun i => ?_) a
    · simpa [FlagG.fvec] using h2
    · simpa [FlagG.fvec] using h1 i
  · intro h
    exact ⟨fun i => by simpa [FlagG.fvec] using h i.castSucc, by simpa [FlagG.fvec] using h (Fin.last r)⟩

theorem xplus_sum (F : FlagG S r T) {v : S.V} (hv : v ∈ F.Xplus) : ∃ C : Fin (r + 1) → E, ∑ a, C a • F.fvec a = v := by
  obtain ⟨a', x', hx', e'⟩ := xplus_dec F hv
  obtain ⟨c', hc'⟩ := x_sum F hx'
  exact ⟨Fin.snoc (α := fun _ => E) c' a', by rw [sum_fvec, hc', e']⟩

end Flag

section GT

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))

abbrev Mof : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  ((ratM X Y u u' s : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)

abbrev Miof : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E :=
  (((ratM X Y u u' s)⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)

theorem toV_famE (w : D.what₂.Word) (a : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.Level.toV X (famE X w a) = (X.Fu w).fvec a := by
  refine Fin.lastCases ?_ (fun i => ?_) a
  · simp [famE, FlagG.fvec, HidaSetting.zR, Formalism.L2.SG.Pf.Level.toV_crd, X.flagZVector]
  · simp [famE, FlagG.fvec, HidaSetting.eR, Formalism.L2.SG.Pf.Level.toV_crd, X.Fu_e]

theorem lin_iso : s.lin ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := s.rep.2.2.1

theorem frame_e (b : Fin D.R.rS) : s.frame.fl.e b = s.lin (X.eX b) := by
  unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
  rw [dite_eq_left (lin_iso X Y u u' s)]
  show s.lin ((X.Fu u').e b) = _
  rw [X.Fu_e]

theorem frame_z_eq_lin_zu : s.frame.fl.z = s.lin (X.zu u') := by
  unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
  rw [dite_eq_left (lin_iso X Y u u' s)]
  show s.lin ((X.Fu u').z) = _
  rw [X.flagZVector]

theorem frame_zt : s.frame.zt = s.frame.fl.z := by
  unfold Formalism.L2.SG.TermOp.GTerm.frame Formalism.L2.SG.TermOp.mapLF
  rw [dite_eq_left (lin_iso X Y u u' s)]
  rfl

theorem frame_fvec (b : Fin (D.R.rS + 1)) : s.frame.fl.fvec b = s.lin ((X.Fu u').fvec b) := by
  refine Fin.lastCases ?_ (fun i => ?_) b
  · simp only [FlagG.fvec, Fin.snoc_last]; rw [frame_z_eq_lin_zu, X.flagZVector]
  · simp only [FlagG.fvec, Fin.snoc_castSucc]; rw [frame_e, X.Fu_e]

theorem lin_toV (x : Fin X.B.I.n → X.B.I.E) :
    s.lin (Formalism.L2.SG.Pf.Level.toV X x) = Formalism.L2.SG.Pf.Level.toV X (Mof X Y u u' s *ᵥ x) := by
  have h := s.rep.2.1.choose_spec.2.2.2 (Formalism.L2.SG.Pf.Level.toV X x)
  rw [Formalism.L2.SG.Pf.Level.crd_toV] at h
  rw [← Formalism.L2.SG.Pf.Level.toV_crd X (s.lin (Formalism.L2.SG.Pf.Level.toV X x))]
  exact congrArg (Formalism.L2.SG.Pf.Level.toV X) h

theorem linsymm_toV (x : Fin X.B.I.n → X.B.I.E) :
    s.lin.symm (Formalism.L2.SG.Pf.Level.toV X x) = Formalism.L2.SG.Pf.Level.toV X (Miof X Y u u' s *ᵥ x) := by
  rw [LinearEquiv.symm_apply_eq, lin_toV, Matrix.mulVec_mulVec, Mof, Miof, Units.mul_inv, Matrix.one_mulVec]

theorem toV_Mfam (b : Fin (D.R.rS + 1)) :
    Formalism.L2.SG.Pf.Level.toV X (Mof X Y u u' s *ᵥ famE X u' b) = s.frame.fl.fvec b := by
  rw [← lin_toV, toV_famE, frame_fvec]

theorem toV_comb (c : Fin (D.R.rS + 1) → X.B.I.E) :
    Formalism.L2.SG.Pf.Level.toV X (∑ b, c b • (Mof X Y u u' s *ᵥ famE X u' b)) = ∑ b, X.ιE (c b) • s.frame.fl.fvec b := by
  rw [Formalism.L2.SG.Pf.Level.toV_sum]
  simp only [Formalism.L2.SG.Pf.Level.toV_smul, toV_Mfam]

theorem toV_combL (c : Fin (D.R.rS + 1) → X.B.I.E) :
    Formalism.L2.SG.Pf.Level.toV X (∑ a, c a • famE X u a) = ∑ a, X.ιE (c a) • (X.Fu u).fvec a := by
  rw [Formalism.L2.SG.Pf.Level.toV_sum]
  simp only [Formalism.L2.SG.Pf.Level.toV_smul, toV_famE]

theorem iota_if (p : Prop) [Decidable p] : X.ιE (if p then 1 else 0) = if p then 1 else 0 := by
  split_ifs <;> simp

theorem firstNormal_mem_Xplus : Formalism.L2.SG.Pf.Level.toV X (nu1E X u u' (Mof X Y u u' s)) ∈ s.frame.fl.Xplus := by
  rw [firstNormal_eq_adjugate, toV_comb]
  exact sum_mem_xplus _ _

theorem firstNormal_pairing (hdet : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) (a : Fin (D.R.rS + 1)) :
    (VS D).hT ((X.Fu u).fvec a) (Formalism.L2.SG.Pf.Level.toV X (nu1E X u u' (Mof X Y u u' s))) =
      if a = Fin.last _ then 1 else 0 := by
  rw [← toV_famE, ← Formalism.L2.SG.Pf.Level.iota_hE, hermitian_firstNormal X u u' _ hdet, iota_if]

theorem secondNormal_mem_Xplus : Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s)) ∈ (X.Fu u).Xplus := by
  rw [secondNormal_eq_adjugate, toV_combL]
  exact sum_mem_xplus _ _

theorem secondNormal_pairing (hdet : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) (b : Fin (D.R.rS + 1)) :
    (VS D).hT (Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s))) (s.frame.fl.fvec b) =
      if b = Fin.last _ then 1 else 0 := by
  rw [← toV_Mfam, ← Formalism.L2.SG.Pf.Level.iota_hE, hermitian_secondNormal X u u' _ hdet, iota_if]

theorem secondNormal_toV : Formalism.L2.SG.Pf.Level.toV X (nu2E X u u' (Mof X Y u u' s) (Miof X Y u u' s)) =
    s.lin.symm (Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s))) := by
  rw [secondNormal_eq_mulVec, linsymm_toV]

theorem ker_of_det (hG : Gflag (X.Fu u) s.frame.fl ≠ 0) (hdet : (ZE X u u' (Mof X Y u u' s)).det = 0) :
    ∃ d ∈ s.frame.fl.Xplus, d ∈ orth (VS D) (X.Fu u).Xplus ∧ d ≠ 0 := by
  obtain ⟨c, hc0, hc⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  refine ⟨Formalism.L2.SG.Pf.Level.toV X (∑ b, c b • (Mof X Y u u' s *ᵥ famE X u' b)), ?_, ?_, ?_⟩
  · rw [toV_comb]; exact sum_mem_xplus _ _
  · rw [orth_fvec]
    intro a
    rw [← toV_famE, ← Formalism.L2.SG.Pf.Level.iota_hE, hE_comb, hc, Pi.zero_apply, map_zero]
  · intro h
    rw [toV_comb] at h
    have h2 := indep' (X.Fu u) s.frame.fl hG _ h
    apply hc0
    funext b
    have h3 := congrFun h2 b
    simpa using h3

theorem det_of_ker {d : (VS D).V} (hd : d ∈ s.frame.fl.Xplus) (hdO : d ∈ orth (VS D) (X.Fu u).Xplus) (hd0 : d ≠ 0) :
    (ZE X u u' (Mof X Y u u' s)).det = 0 := by
  obtain ⟨C, hC⟩ := xplus_sum _ hd
  set c : Fin (D.R.rS + 1) → X.B.I.E := fun b => X.ιE.symm (C b) with hc
  have hd' : Formalism.L2.SG.Pf.Level.toV X (∑ b, c b • (Mof X Y u u' s *ᵥ famE X u' b)) = d := by
    rw [toV_comb, ← hC]
    simp [c]
  have hZ : ZE X u u' (Mof X Y u u' s) *ᵥ c = 0 := by
    funext a
    apply X.ιE.injective
    rw [← hE_comb, Formalism.L2.SG.Pf.Level.iota_hE, toV_famE, hd', Pi.zero_apply, map_zero]
    exact (orth_fvec _).1 hdO a
  have hc0 : c ≠ 0 := by
    intro h
    apply hd0
    rw [← hd', h]
    simp [Formalism.L2.SG.Pf.Level.toV]
  exact Matrix.exists_mulVec_eq_zero_iff.1 ⟨c, hc0, hZ⟩

theorem det_of_lker {d : (VS D).V} (hd : d ∈ (X.Fu u).Xplus) (hdO : ∀ b, (VS D).hT d (s.frame.fl.fvec b) = 0)
    (hd0 : d ≠ 0) : (ZE X u u' (Mof X Y u u' s)).det = 0 := by
  obtain ⟨C, hC⟩ := xplus_sum _ hd
  set k : Fin (D.R.rS + 1) → X.B.I.E := fun a => star (X.ιE.symm (C a)) with hk
  have hd' : Formalism.L2.SG.Pf.Level.toV X (∑ a, star (k a) • famE X u a) = d := by
    rw [toV_combL, ← hC]
    simp [k]
  have hZ : k ᵥ* ZE X u u' (Mof X Y u u' s) = 0 := by
    funext b
    apply X.ιE.injective
    have e1 : (k ᵥ* ZE X u u' (Mof X Y u u' s)) b =
        Formalism.L2.SG.Pf.Level.hE X (∑ a, star (k a) • famE X u a) (Mof X Y u u' s *ᵥ famE X u' b) := by
      rw [hE_sum_left]
      simp only [Matrix.vecMul, dotProduct, ZE]
    rw [e1, Formalism.L2.SG.Pf.Level.iota_hE, hd', toV_Mfam, Pi.zero_apply, map_zero]
    exact hdO b
  have hk0 : k ≠ 0 := by
    intro h
    apply hd0
    rw [← hd', h]
    simp [Formalism.L2.SG.Pf.Level.toV]
  exact Matrix.exists_vecMul_eq_zero_iff.1 ⟨k, hk0, hZ⟩

theorem uue_le {Λ : Submodule (𝓞 D.host.E) (VS D).V} {T T' : D.host.E} (F : LFlag (D.sp.Y 0) D.R.rS T)
    (F' : LFlag (D.sp.Y 0) D.R.rS T') (hz : F.zt = F.fl.z) (hz' : F'.zt = F'.fl.z) :
    UUE Λ F F' ≤ F.fl.Xplus ⊔ F'.fl.Xplus := by
  unfold UUE spanE
  rw [Submodule.span_le]
  have h : UU Λ F F' ≤ (F.fl.Xplus ⊔ F'.fl.Xplus).restrictScalars (𝓞 D.host.E) := by
    unfold UU
    refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
    · exact inf_le_right.trans (fun v hv => Submodule.mem_sup_left (Submodule.mem_sup_left hv))
    · rw [Submodule.span_le, Set.singleton_subset_iff, hz]
      exact Submodule.mem_sup_left (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    · exact inf_le_right.trans (fun v hv => Submodule.mem_sup_right (Submodule.mem_sup_left hv))
    · rw [Submodule.span_le, Set.singleton_subset_iff, hz']
      exact Submodule.mem_sup_right (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  exact fun v hv => h hv

theorem orthogonal_toV {Λ : Submodule (𝓞 D.host.E) (VS D).V} {y : Fin X.B.I.n → X.B.I.E}
    (hy : orthogonalComplementRational X u u' (Mof X Y u u' s) y) :
    Formalism.L2.SG.Pf.Level.toV X y ∈ Hp Λ (lf D (X.Fu u)) s.frame := by
  have h1 : ∀ a, (VS D).hT ((X.Fu u).fvec a) (Formalism.L2.SG.Pf.Level.toV X y) = 0 := fun a => by
    rw [← toV_famE, ← Formalism.L2.SG.Pf.Level.iota_hE, hy.1 a, map_zero]
  have h2 : ∀ b, (VS D).hT (s.frame.fl.fvec b) (Formalism.L2.SG.Pf.Level.toV X y) = 0 := fun b => by
    rw [← toV_Mfam, ← Formalism.L2.SG.Pf.Level.iota_hE, hy.2 b, map_zero]
  have o1 := (orth_fvec (X.Fu u)).2 h1
  have o2 := (orth_fvec s.frame.fl).2 h2
  apply PI.UnitaryGroupMassFormula.ScalEquivGen.orthAntiQ (uue_le (Λ := Λ) (lf D (X.Fu u)) s.frame rfl (frame_zt X Y u u' s))
  rw [PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ]
  intro x hx
  obtain ⟨x1, hx1, x2, hx2, rfl⟩ := Submodule.mem_sup.mp hx
  rw [map_add (f := _), LinearMap.add_apply, PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp o1 x1 hx1,
    PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp o2 x2 hx2, add_zero]

theorem orthogonal_ofV {Λ : Submodule (𝓞 D.host.E) (VS D).V} (hΛ : Submodule.IsFullLattice D.host.E Λ)
    (hL : IsLift Λ (lf D (X.Fu u))) (hL' : IsLift Λ s.frame) {y : (VS D).V}
    (hy : y ∈ Hp Λ (lf D (X.Fu u)) s.frame) : orthogonalComplementRational X u u' (Mof X Y u u' s) (X.crd y) := by
  have hm := PI.PairCorankPos.W.frame_mem_UUE Λ hΛ (lf D (X.Fu u)) s.frame hL hL'
  have hy' : ∀ x ∈ UUE Λ (lf D (X.Fu u)) s.frame, (VS D).hT x y = 0 := PI.UnitaryGroupMassFormula.ScalEquivGen.memOrthQ.mp hy
  refine ⟨fun a => ?_, fun b => ?_⟩
  · apply X.ιE.injective
    rw [Formalism.L2.SG.Pf.Level.iota_hE, toV_famE, Formalism.L2.SG.Pf.Level.toV_crd, map_zero]
    exact hy' _ (hm (Sum.inl a))
  · apply X.ιE.injective
    rw [Formalism.L2.SG.Pf.Level.iota_hE, toV_Mfam, Formalism.L2.SG.Pf.Level.toV_crd, map_zero]
    exact hy' _ (hm (Sum.inr b))

theorem wperp_of (w : D.what₂.Word) {x : Fin X.B.I.n → X.B.I.E}
    (h : Formalism.L2.SG.Pf.Level.toV X x ∈ Submodule.span D.host.E (Set.range X.eX)) : x ∈ WperpE X w := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 h
  have e : x = ∑ i, X.ιE.symm (c i) • X.eR i := by
    rw [← Formalism.L2.SG.Pf.Level.crd_toV X x, ← Formalism.L2.SG.Pf.Level.crd_toV X (∑ i, X.ιE.symm (c i) • X.eR i)]
    congr 1
    rw [Formalism.L2.SG.Pf.Level.toV_sum, ← hc]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Formalism.L2.SG.Pf.Level.toV_smul, HidaSetting.eR, Formalism.L2.SG.Pf.Level.toV_crd, RingEquiv.apply_symm_apply]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl (Or.inl ⟨i, rfl⟩)))

theorem fixedX (v : (VS D).V) (hv : v ∈ (X.Fu u).X) : v ∈ Submodule.span D.host.E (Set.range X.eX) := by
  simpa [FlagG.X, X.Fu_e] using hv

theorem symm_frameX {v : (VS D).V} (hv : v ∈ s.frame.fl.X) : s.lin.symm v ∈ Submodule.span D.host.E (Set.range X.eX) := by
  obtain ⟨c, hc⟩ := x_sum _ hv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hc, map_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [map_smul, frame_e, LinearEquiv.symm_apply_apply]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GT

end Formalism.L2.SG.Pf.RowForm.ClassFrameFirstNormalAdjugate
end
end

noncomputable section

open scoped Classical

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.RowForm.ClassFrameOO2Aux
  Formalism.L2.SG.Pf.RowForm.ClassFramePositivePartDecomposition Formalism.L2.SG.Pf.RowForm.ClassFrameFirstNormalAdjugate

open scoped Matrix

namespace Formalism.L2.SG.Pf.RowForm.ClassFrameNormalVectorScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)

theorem gval_ne (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (hG : (Y.tO u u').G s ≠ 0) : Gval (lf D (X.Fu u)) s.frame ≠ 0 := by
  have hG' : s.G ≠ 0 := fun h => hG (by show Formalism.L2.SG.TermOp.Gt s = 0; simp [Formalism.L2.SG.TermOp.Gt, h])
  have hRL : IsRowLat D (X.Fu u) s.lam := (Y.rowsOK u).1 s.lam s.mem
  have hEq := Formalism.L2.SG.Closed.TermEqIff_holds D u u' (X.Fu u) s.lam hRL
  have hGF := (Formalism.L2.SG.Closed.TermFun_holds D u u' (X.Fu u) s.lam hRL).1
  let x : Formalism.L2.SG.TermDef.Carrier (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u') := ⟨s.frame, s.rep.2.2.2.2⟩
  have gv : Formalism.L2.SG.TermDef.Gt s.lam (lf D (X.Fu u)) (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u')
      (Formalism.L2.SG.TermDef.mk _ _ _ x) = Gval (lf D (X.Fu u)) x.1 :=
    hGF _ _ ((hEq _ _).1 (Quot.out_eq (Formalism.L2.SG.TermDef.mk s.lam (lf D (X.Fu u))
      (Formalism.L2.SG.TermDef.PD D s.lam (lf D (X.Fu u)) u') x)))
  intro hz
  apply hG'
  exact gv.trans (by with_unfolding_all exact hz)

variable (s : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))

theorem firstNormal_e (h : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) (a : Fin D.R.rS) :
    (VS D).hT ((X.Fu u).e a) (Formalism.L2.SG.Pf.Level.toV X (nu1E X u u' (Mof X Y u u' s))) = 0 := by
  have := firstNormal_pairing X Y u u' s h a.castSucc
  rw [if_neg (Fin.castSucc_lt_last a).ne] at this
  simpa [FlagG.fvec] using this

theorem firstNormal_z (h : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) :
    (VS D).hT (X.Fu u).z (Formalism.L2.SG.Pf.Level.toV X (nu1E X u u' (Mof X Y u u' s))) = 1 := by
  have := firstNormal_pairing X Y u u' s h (Fin.last _)
  rw [if_pos rfl] at this
  simpa [FlagG.fvec] using this

theorem secondNormal_e (h : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) (b : Fin D.R.rS) :
    (VS D).hT (Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s))) (s.frame.fl.e b) = 0 := by
  have := secondNormal_pairing X Y u u' s h b.castSucc
  rw [if_neg (Fin.castSucc_lt_last b).ne] at this
  simpa [FlagG.fvec] using this

theorem secondNormal_z (h : (ZE X u u' (Mof X Y u u' s)).det ≠ 0) :
    (VS D).hT (Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s))) s.frame.fl.z = 1 := by
  have := secondNormal_pairing X Y u u' s h (Fin.last _)
  rw [if_pos rfl] at this
  simpa [FlagG.fvec] using this

theorem agree_pair (s₁ s₂ : Formalism.L2.SG.TermOp.GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u'))
    (hG₁ : (Y.tO u u').G s₁ ≠ 0) (hG₂ : (Y.tO u u').G s₂ ≠ 0) (hl : s₁.lam = s₂.lam)
    (hs0 : Lat.s0 s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹) D.R.k = 1)
    (hsc : IsScalar s₁.lam (lf D (X.Fu u)) s₁.frame s₂.frame (s₂.lin * s₁.lin⁻¹)) :
    nu1E X u u' (Mof X Y u u' s₁) - nu1E X u u' (Mof X Y u u' s₂) ∈ WperpE X u ∧
      nu2E X u u' (Mof X Y u u' s₁) (Miof X Y u u' s₁) - nu2E X u u' (Mof X Y u u' s₂) (Miof X Y u u' s₂) ∈
        WperpE X u' ∧
      ∀ y₂, orthogonalComplementRational X u u' (Mof X Y u u' s₂) y₂ →
        ∃ y₁, orthogonalComplementRational X u u' (Mof X Y u u' s₁) y₁ ∧ y₁ - y₂ ∈ WperpE X u ∧
          Miof X Y u u' s₁ *ᵥ y₁ - Miof X Y u u' s₂ *ᵥ y₂ ∈ WperpE X u' := by
  have hRL : IsRowLat D (X.Fu u) s₁.lam := (Y.rowsOK u).1 s₁.lam s₁.mem
  obtain ⟨hgen, ⟨_, _, hlift, _⟩, _⟩ := hRL
  have hlat : Submodule.IsFullLattice D.host.E s₁.lam := hgen.1
  have hL₁ : IsLift s₁.lam s₁.frame := s₁.rep.2.2.2.2.1
  have hL₂ : IsLift s₁.lam s₂.frame := by rw [hl]; exact s₂.rep.2.2.2.2.1
  have gv₁ := gval_ne X Y u u' s₁ hG₁
  have gv₂ := gval_ne X Y u u' s₂ hG₂
  have nd₁ := PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hlat hlift hL₁ gv₁
  have nd₂ := PI.UnitaryGroupMassFormula.ScalEquivGen.ndOfQ hlat hlift hL₂ gv₂
  have hdim := PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace.finrank_VS D
  have hTh := PI.UnitaryGroupMassFormula.ScalEquivGen.thEqQ hdim nd₁ hs0
  have hTh'' := PI.UnitaryGroupMassFormula.ScalEquivGen.thEq''Q hlat hdim nd₁ nd₂ hs0
  have hz₁ := frame_zt X Y u u' s₁
  have hz₂ := frame_zt X Y u u' s₂
  have hT0 := PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace.tu_ne_zero D u
  have hT0' := PI.UnitaryGroupMassFormula.ScalarEquivalenceHermitianSpace.tu_ne_zero D u'
  have hi : s₂.lin * s₁.lin⁻¹ ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT :=
    Subgroup.mul_mem _ (lin_iso X Y u u' s₂) (Subgroup.inv_mem _ (lin_iso X Y u u' s₁))
  have hβ : ∀ x, (s₂.lin * s₁.lin⁻¹) x = s₂.lin (s₁.lin.symm x) := fun x => rfl
  have hβe : ∀ b, (s₂.lin * s₁.lin⁻¹) (s₁.frame.fl.e b) = s₂.frame.fl.e b := by
    intro b; rw [hβ, frame_e, frame_e, LinearEquiv.symm_apply_apply]
  have hβz : (s₂.lin * s₁.lin⁻¹) s₁.frame.fl.z = s₂.frame.fl.z := by
    rw [hβ, frame_z_eq_lin_zu, frame_z_eq_lin_zu, LinearEquiv.symm_apply_apply]
  have hdet : (ZE X u u' (Mof X Y u u' s₁)).det = 0 ↔ (ZE X u u' (Mof X Y u u' s₂)).det = 0 := by
    constructor
    · intro h
      obtain ⟨d, hd, hdO, hd0⟩ := ker_of_det X Y u u' s₁ gv₁ h
      obtain ⟨d₂, hd₂, hd₂O, hd₂0⟩ := ker_transport (by first | exact hlat | exact hlat.toIsLattice) rfl hz₁ hz₂ gv₁ hTh'' hsc hd hdO hd0
      exact det_of_ker X Y u u' s₂ hd₂ hd₂O hd₂0
    · intro h
      obtain ⟨d, hd, hdO, hd0⟩ := ker_of_det X Y u u' s₂ gv₂ h
      obtain ⟨d₁, hd₁, hd₁O, hd₁0⟩ := ker_transport_rev (by first | exact hlat | exact hlat.toIsLattice) rfl hz₁ hz₂ gv₂ hTh hsc hd hdO hd0
      exact det_of_ker X Y u u' s₁ hd₁ hd₁O hd₁0
  refine ⟨?_, ?_, ?_⟩
  ·
    by_cases h₁ : (ZE X u u' (Mof X Y u u' s₁)).det = 0
    · have h₂ := hdet.1 h₁
      simp [nu1E, h₁, h₂]
    have h₂ : (ZE X u u' (Mof X Y u u' s₂)).det ≠ 0 := fun h => h₁ (hdet.2 h)
    obtain ⟨ν, hνm, hνe, hνz, hνd⟩ := firstNormal_transport (by first | exact hlat | exact hlat.toIsLattice) rfl hz₁ hz₂ hT0 hTh'' hsc (firstNormal_mem_Xplus X Y u u' s₁)
      (firstNormal_e X Y u u' s₁ h₁) (firstNormal_z X Y u u' s₁ h₁)
    have hνeq : ν = Formalism.L2.SG.Pf.Level.toV X (nu1E X u u' (Mof X Y u u' s₂)) := by
      by_contra hne
      apply h₂
      refine det_of_ker X Y u u' s₂ (Submodule.sub_mem _ hνm (firstNormal_mem_Xplus X Y u u' s₂)) ?_ (sub_ne_zero.2 hne)
      rw [PI.ScalarPairDr.W.mem_orth_Xplus (S := VS D) (X.Fu u)]
      refine ⟨fun a => ?_, ?_⟩
      · rw [map_sub]
        have e1 := hνe a
        have e2 := firstNormal_e X Y u u' s₂ h₂ a
        simp only at e1
        rw [e1, e2, sub_zero]
      · rw [map_sub]
        have e1 := hνz
        simp only at e1
        rw [e1, firstNormal_z X Y u u' s₂ h₂, sub_self]
    apply wperp_of X u
    rw [Formalism.L2.SG.Pf.Level.toV_sub, ← hνeq]
    exact fixedX X u _ hνd
  ·
    by_cases h₁ : (ZE X u u' (Mof X Y u u' s₁)).det = 0
    · have h₂ := hdet.1 h₁
      simp [nu2E, h₁, h₂]
    have h₂ : (ZE X u u' (Mof X Y u u' s₂)).det ≠ 0 := fun h => h₁ (hdet.2 h)
    obtain ⟨x, hxm, hxe, hxz, hxd⟩ := secondNormal_transport (by first | exact hlat | exact hlat.toIsLattice) rfl hz₁ hz₂ hT0' hi hβe hβz hTh'' hsc
      (secondNormal_mem_Xplus X Y u u' s₁) (secondNormal_e X Y u u' s₁ h₁) (secondNormal_z X Y u u' s₁ h₁)
    have hxeq : x = Formalism.L2.SG.Pf.Level.toV X (x2E X u u' (Mof X Y u u' s₂)) := by
      by_contra hne
      apply h₂
      refine det_of_lker X Y u u' s₂ (Submodule.sub_mem _ hxm (secondNormal_mem_Xplus X Y u u' s₂)) ?_ (sub_ne_zero.2 hne)
      intro b
      refine Fin.lastCases ?_ (fun i => ?_) b
      · simp only [FlagG.fvec, Fin.snoc_last]
        rw [map_sub, LinearMap.sub_apply, hxz, secondNormal_z X Y u u' s₂ h₂, sub_self]
      · simp only [FlagG.fvec, Fin.snoc_castSucc]
        rw [map_sub, LinearMap.sub_apply, hxe i, secondNormal_e X Y u u' s₂ h₂ i, sub_self]
    apply wperp_of X u'
    rw [Formalism.L2.SG.Pf.Level.toV_sub, secondNormal_toV, secondNormal_toV, ← hxeq]
    have key : s₂.lin.symm x = s₁.lin.symm ((s₂.lin * s₁.lin⁻¹).symm x) := by
      rw [LinearEquiv.symm_apply_eq, ← hβ, LinearEquiv.apply_symm_apply]
    rw [key, ← map_sub, ← neg_sub, map_neg]
    exact Submodule.neg_mem _ (symm_frameX X Y u u' s₁ hxd)
  ·
    intro y₂ hy₂
    have hV := orthogonal_toV (Λ := s₁.lam) X Y u u' s₂ hy₂
    obtain ⟨y₁, hy₁, hd1, hd2⟩ := orthogonal_transport hTh'' hV
    refine ⟨X.crd y₁, orthogonal_ofV X Y u u' s₁ (by first | exact hgen.1 | exact hgen.1.toIsLattice) hlift hL₁ hy₁, ?_, ?_⟩
    · apply wperp_of X u
      rw [Formalism.L2.SG.Pf.Level.toV_sub, Formalism.L2.SG.Pf.Level.toV_crd]
      exact fixedX X u _ hd1
    · apply wperp_of X u'
      rw [Formalism.L2.SG.Pf.Level.toV_sub, ← linsymm_toV, ← linsymm_toV, Formalism.L2.SG.Pf.Level.toV_crd]
      have key : s₁.lin.symm y₁ = s₂.lin.symm ((s₂.lin * s₁.lin⁻¹) y₁) := by
        rw [hβ, LinearEquiv.symm_apply_apply]
      rw [key, ← map_sub]
      exact symm_frameX X Y u u' s₂ hd2

end Formalism.L2.SG.Pf.RowForm.ClassFrameNormalVectorScalars

namespace Formalism.L2.SG.Pf.RowForm

open Formalism.L2.SG.Pf.RowForm.ClassFrameNormalVectorScalars

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (Y : Formalism.L2.SG.Full.Full X) (u u' : D.what₂.Word)
  (κ : Formalism.L2.SG.TermDef.Term D u u' (X.Fu u) (Y.what₂ u) → ℕ)

theorem scalarAgreeRatC_of_scalT (hS : ScalTC X Y u u' κ) : ScalarAgreeRatC X Y u u' κ := by
  intro R ρ s₁ s₂ _ _
  obtain ⟨hG₁, hn₁, hr₁, hk₁⟩ := s₁.2
  obtain ⟨hG₂, hn₂, hr₂, hk₂⟩ := s₂.2
  have h := (hS s₁.1 s₂.1 hG₁ hG₂ hn₁ hn₂ (hr₁.trans hr₂.symm)).2 (hk₁.trans hk₂.symm)
  have h2 : Formalism.L2.SG.TermOp.scalT s₁.1 s₂.1 := h.2
  obtain ⟨⟨hl, -⟩, hs0, hsc⟩ := h2
  exact agree_pair X Y u u' s₁.1 s₂.1 hG₁ hG₂ hl hs0 hsc

theorem scalarAgreeC_of_scalT (hS : ScalTC X Y u u' κ) : ScalarAgreeC X Y u u' κ :=
  scalarAgreeC_of_rat X Y u u' κ (scalarAgreeRatC_of_scalT X Y u u' κ hS)

end Formalism.L2.SG.Pf.RowForm
