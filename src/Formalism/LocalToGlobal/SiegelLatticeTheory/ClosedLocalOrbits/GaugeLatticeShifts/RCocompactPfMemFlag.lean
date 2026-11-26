module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HaarDisintegrationRealHolds
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SlabNDensePf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemFlag
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.Pf.FlagCoordinates

variable {D : D7} (X : HidaSetting D)

theorem gE_sub_one (Z : Matrix (Kap X) (Kap X) X.B.I.E) :
    Formalism.L2.SG.Pf.UnipB.gE X Z - 1 = Bm X * (cay (N0 D) Z - 1) * Bm' X := by
  unfold Formalism.L2.SG.Pf.UnipB.gE
  rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Bm_mul_Bm']

theorem Bm_mulVec_mem (S : Set (Fin D.R.rS)) (c : Kap X → X.B.I.E) (hc : ∀ k, k ∉ Sum.inl '' S → c k = 0) :
    Bm X *ᵥ c ∈ Submodule.span X.B.I.E (X.eR '' S) := by
  rw [Bm_mulVec]
  refine Submodule.sum_mem _ fun k _ => ?_
  by_cases hk : k ∈ Sum.inl '' S
  · obtain ⟨b, hb, rfl⟩ := hk
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, hb, rfl⟩)
  · rw [hc k hk, zero_smul]
    exact Submodule.zero_mem _

theorem flag_coord {Z : Matrix (Kap X) (Kap X) X.B.I.E} (hZ : InPat (lvk X) 1 Z) (a : Fin D.R.rS) :
    (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ X.eR a ∈ Submodule.span X.B.I.E (X.eR '' {b | b.1 < a.1}) := by
  rw [gE_sub_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hB : Bm' X *ᵥ X.eR a = Pi.single (Sum.inl a) 1 := by
    rw [Bm'_mulVec]
    funext k
    rw [show X.eR a = bv X (Sum.inl a) from rfl, cE_bv]
    simp [Pi.single_apply]
  rw [hB]
  refine Bm_mulVec_mem X _ _ fun k hk => ?_
  rw [mulVec_single_one]
  refine cay_sub_one _ hZ k _ ?_
  rcases k with b | i | b
  · have : ¬ b.1 < a.1 := fun h => hk ⟨b, h, rfl⟩
    simp only [lvk, Sum.elim_inl]; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; omega
  · simp only [lvk, Sum.elim_inl, Sum.elim_inr]; have := a.2; have := b.2; omega

theorem orth_coord {Z : Matrix (Kap X) (Kap X) X.B.I.E} (hZ : InPat (lvk X) 1 Z) (x : Fin X.B.I.n → X.B.I.E)
    (hx : ∀ a, hE X (X.eR a) x = 0) :
    (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ x ∈ Submodule.span X.B.I.E (X.eR '' Set.univ) := by
  rw [gE_sub_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Bm'_mulVec]
  refine Bm_mulVec_mem X Set.univ _ fun k hk => ?_
  have hk' : ∀ b, k ≠ Sum.inl b := by
    rintro b rfl
    exact hk ⟨b, Set.mem_univ _, rfl⟩
  rw [mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hlk := lvk_notinl X k hk'
  rcases j with b | i | b
  · rw [cay_sub_one _ hZ k _ (by rw [lvk_inl]; have := b.2; omega), zero_mul]
  · rw [cay_sub_one _ hZ k _ (by rw [lvk_w]; omega), zero_mul]
  · rw [show cE X x (Sum.inr (Sum.inr b)) = hE X (X.eR b) x from rfl, hx b, mul_zero]

theorem crd_desc (S : Set (Fin D.R.rS)) (v : (VS D).V)
    (hv : X.crd v ∈ Submodule.span X.B.I.E (X.eR '' S)) :
    v ∈ Submodule.span D.host.E (X.eX '' S) := by
  obtain ⟨c, hc⟩ := (Fintype.mem_span_image_iff_exists_fun X.B.I.E).1 hv
  have e : v = ∑ i : S, X.ιE (c i) • X.eX i := by
    rw [← Formalism.L2.SG.Pf.Level.toV_crd X v, ← hc, Formalism.L2.SG.Pf.Level.toV_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Formalism.L2.SG.Pf.Level.toV_smul, show X.eR i = X.crd (X.eX i) from rfl, Formalism.L2.SG.Pf.Level.toV_crd]
  rw [e]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, i.2, rfl⟩)

end Formalism.L2.SG.Pf.FlagCoordinates

namespace Formalism.L2.SG.TermOp.Vanish

open Formalism.L2.SG.Pf.FlagCoordinates

theorem memFlagOf_holds : MemFlagOf := by
  intro D X u Z n hZ hn
  have hm : ∀ v, (Formalism.L2.SG.Pf.UnipB.gE X Z - 1) *ᵥ X.crd v = X.crd (n v - v) := fun v => Formalism.L2.SG.Pf.Vanish2.mcrd X hn v
  have hXf : ∀ k, Xflag (lf D (X.Fu u)) k = Submodule.span D.host.E (X.eX '' {i | i.1 < k}) := by
    intro k
    show Submodule.span D.host.E ((X.Fu u).e '' {i | i.1 < k}) = _
    rw [X.Fu_e]
  have hXs : Xsp (lf D (X.Fu u)) = Submodule.span D.host.E (X.eX '' Set.univ) := by
    show Submodule.span D.host.E (Set.range (X.Fu u).e) = _
    rw [X.Fu_e, Set.image_univ]
  have he : ∀ a : Fin D.R.rS, n (X.eX a) - X.eX a ∈ Submodule.span D.host.E (X.eX '' {b | b.1 < a.1}) := by
    intro a
    have hd := flag_coord X hZ a
    rw [show X.eR a = X.crd (X.eX a) from rfl, hm] at hd
    exact crd_desc X _ _ hd
  refine ⟨fun j x hx => ?_, fun x hx => ?_⟩
  · rw [hXf] at hx ⊢
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, ha, rfl⟩ := hy
      refine Submodule.span_mono ?_ (he a)
      rintro _ ⟨b, hb, rfl⟩
      exact ⟨b, lt_of_lt_of_le hb (Nat.lt_succ_iff.1 ha), rfl⟩
    | zero => simp
    | add y z _ _ hy hz =>
      rw [map_add (f := _), add_sub_add_comm]
      exact add_mem hy hz
    | smul c y _ hy =>
      rw [map_smul, ← smul_sub]
      exact Submodule.smul_mem _ _ hy
  · have hx0 : ∀ a, hE X (X.eR a) (X.crd x) = 0 := by
      intro a
      have hmem : X.eX a ∈ Xsp (lf D (X.Fu u)) := by
        rw [hXs]
        exact Submodule.subset_span ⟨a, Set.mem_univ _, rfl⟩
      have h0 : (VS D).hT (X.eX a) x = 0 := (Formalism.L2.SG.Pf.mem_orth_iff _ _).1 hx _ hmem
      rw [show X.eR a = X.crd (X.eX a) from rfl, hE_crd, h0, map_zero]
    have hd := orth_coord X hZ _ hx0
    rw [hm] at hd
    rw [hXs]
    exact crd_desc X _ _ hd

end Formalism.L2.SG.TermOp.Vanish
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemConj
noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

section MemConj

variable {D : D7} (X : HidaSetting D)

theorem mc_gr_mul_inv (M : GL (Fin X.B.I.n) X.B.I.E) :
    Gr X (M : Matrix _ _ _) * Gr X (↑M⁻¹ : Matrix _ _ _) = 1 := by
  unfold Gr
  have h1 := Bm_mul_Bm' X
  have h2 : Bm' X * Bm X = 1 := Bm'_mul_Bm X
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bm X) (Bm' X), h1, Matrix.one_mul]
  have h3 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *
      (((M⁻¹ : GL (Fin X.B.I.n) X.B.I.E) : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Bm X) = Bm X := by
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  rw [h3, h2]

theorem mc_gr_unitary (M : GL (Fin X.B.I.n) X.B.I.E) (hM : M ∈ Formalism.UG.UJ (starRingEnd X.B.I.E) X.B.I.J) :
    (Gr X (M : Matrix _ _ _))ᴴ * JB X * Gr X (M : Matrix _ _ _) = JB X := by
  have hc : Formalism.UG.cT (starRingEnd X.B.I.E) (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ := by
    ext i j
    unfold Formalism.UG.cT
    simp [Matrix.conjTranspose_apply, starRingEnd_apply]
  have hMJ : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ * X.B.I.J *
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = X.B.I.J := by
    rw [← hc]
    exact hM
  have hJB : JB X = (Bm X)ᴴ * X.B.I.J * Bm X := by
    ext k k'
    unfold JB hE Formalism.UG.hform Bm
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul, starRingEnd_apply]
    rw [Finset.sum_comm]
  have h1 := Bm_mul_Bm' X
  have h5 : ∀ Z : Matrix (Fin X.B.I.n) (Kap X) X.B.I.E, (Bm' X)ᴴ * ((Bm X)ᴴ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one, Matrix.one_mul]
  rw [hJB]
  unfold Gr
  simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (Bm X) (Bm' X), h1, Matrix.one_mul, h5]
  have h4 : (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E)ᴴ * (X.B.I.J *
      ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) * Bm X)) = X.B.I.J * Bm X := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hMJ]
  rw [h4]

theorem memConjOf_holds : MemConjOf := by
  intro D X M hM
  letI : Invertible (2 : X.B.I.E) := invertibleOfNonzero two_ne_zero
  have h1 : Gr X (M : Matrix _ _ _) * Gr X (↑M⁻¹ : Matrix _ _ _) = 1 := mc_gr_mul_inv X M
  have h2 : Gr X (↑M⁻¹ : Matrix _ _ _) * Gr X (M : Matrix _ _ _) = 1 := by
    have := mc_gr_mul_inv X M⁻¹
    rwa [inv_inv] at this
  have hU := mc_gr_unitary X M hM
  refine ⟨fun Z => ?_, fun Z hZ => ?_, ?_⟩
  ·
    have hBB : ∀ Y : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E, Bm X * (Bm' X * Y) = Y := by
      intro Y
      rw [← Matrix.mul_assoc, Bm_mul_Bm', Matrix.one_mul]
    unfold Formalism.L2.SG.Pf.UnipB.gE
    rw [← conj_cay h1]
    unfold Gr
    simp only [Matrix.mul_assoc, hBB, Bm_mul_Bm', Matrix.mul_one]
  ·
    set G := Gr X (M : Matrix _ _ _) with hG
    set G' := Gr X (↑M⁻¹ : Matrix _ _ _) with hG'
    have hA : Gᴴ * JB X = JB X * G' := by
      calc Gᴴ * JB X = Gᴴ * JB X * (G * G') := by rw [h1, Matrix.mul_one]
        _ = Gᴴ * JB X * G * G' := by simp only [Matrix.mul_assoc]
        _ = JB X * G' := by rw [hU]
    have hB : G'ᴴ * JB X = JB X * G := by
      calc G'ᴴ * JB X = G'ᴴ * (Gᴴ * JB X * G) := by rw [hU]
        _ = (G * G')ᴴ * JB X * G := by rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
        _ = JB X * G := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul]
    calc (G' * Z * G)ᴴ * JB X = Gᴴ * Zᴴ * (G'ᴴ * JB X) := by
          rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul]
          simp only [Matrix.mul_assoc]
      _ = Gᴴ * (Zᴴ * JB X) * G := by rw [hB]; simp only [Matrix.mul_assoc]
      _ = Gᴴ * (-(JB X * Z)) * G := by rw [hZ]
      _ = -(Gᴴ * JB X * Z * G) := by simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
      _ = -(JB X * (G' * Z * G)) := by rw [hA]; simp only [Matrix.mul_assoc]
  ·
    obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ
      ((Finset.univ.image fun ij : Kap X × Kap X => Gr X (↑M⁻¹ : Matrix _ _ _) ij.1 ij.2) ∪
        (Finset.univ.image fun ij : Kap X × Kap X => Gr X (M : Matrix _ _ _) ij.1 ij.2))
    have hint : ∀ z ∈ ((Finset.univ.image fun ij : Kap X × Kap X => Gr X (↑M⁻¹ : Matrix _ _ _) ij.1 ij.2) ∪
        (Finset.univ.image fun ij : Kap X × Kap X => Gr X (M : Matrix _ _ _) ij.1 ij.2)),
        (y.natAbs : X.B.I.E) * z ∈ integralClosure ℤ X.B.I.E := by
      intro z hz
      rw [mem_integralClosure_iff]
      have h := hy z hz
      rw [zsmul_eq_mul] at h
      rcases Int.natAbs_eq y with e | e
      · rw [e] at h
        simpa using h
      · rw [e] at h
        have h' := h.neg
        simpa [neg_mul] using h'
    have hP : ∀ i j, (y.natAbs : X.B.I.E) * Gr X (↑M⁻¹ : Matrix _ _ _) i j ∈ integralClosure ℤ X.B.I.E :=
      fun i j => hint _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
    have hQ : ∀ i j, (y.natAbs : X.B.I.E) * Gr X (M : Matrix _ _ _) i j ∈ integralClosure ℤ X.B.I.E :=
      fun i j => hint _ (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(i, j), Finset.mem_univ _, rfl⟩))
    let P1 : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E) := Matrix.of fun i j => ⟨_, hP i j⟩
    let Q1 : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E) := Matrix.of fun i j => ⟨_, hQ i j⟩
    have hP1 : P1.map (fun a => (a : X.B.I.E)) = (y.natAbs : X.B.I.E) • Gr X (↑M⁻¹ : Matrix _ _ _) := by
      ext i j
      rfl
    have hQ1 : Q1.map (fun a => (a : X.B.I.E)) = (y.natAbs : X.B.I.E) • Gr X (M : Matrix _ _ _) := by
      ext i j
      rfl
    have hmap : ∀ U V : Matrix (Kap X) (Kap X) (𝓞 X.B.I.E),
        (U * V).map (fun a => (a : X.B.I.E)) =
          U.map (fun a => (a : X.B.I.E)) * V.map (fun a => (a : X.B.I.E)) :=
      fun U V => Matrix.map_mul (f := algebraMap (𝓞 X.B.I.E) X.B.I.E)
    refine ⟨y.natAbs * y.natAbs, Nat.one_le_iff_ne_zero.mpr
      (mul_ne_zero (Int.natAbs_ne_zero.mpr hy0) (Int.natAbs_ne_zero.mpr hy0)), fun d A => ⟨P1 * A * Q1, ?_⟩⟩
    rw [hmap, hmap, hP1, hQ1]
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Nat.cast_mul]
    congr 1
    ring

end MemConj

end Formalism.L2.SG.TermOp.Vanish
end
end

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.IdMeetVolIndexPf
noncomputable section

namespace Formalism.L2.SG.Pf.IdMeet

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open scoped Classical ENNReal
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat
open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp Formalism.L2.SG.TermOp.IdBlocks Formalism.L2.SG.Full
  Formalism.L2.SG.PoincareInHH.Cut

theorem relIndex_eq_of_dense {G : Type*} [Group G] {R U U' : Subgroup G} (hRU : R ≤ U)
    (hd : ∀ x ∈ U, ∃ r ∈ R, r⁻¹ * x ∈ U') : U'.relIndex R = U'.relIndex U := by
  let f := Subgroup.quotientSubgroupOfEmbeddingOfLE U' hRU
  have hs : Function.Surjective f := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      obtain ⟨r, hr, hrx⟩ := hd x x.2
      refine ⟨QuotientGroup.mk ⟨r, hr⟩, ?_⟩
      rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simpa using hrx
  show Nat.card (R ⧸ U'.subgroupOf R) = Nat.card (U ⧸ U'.subgroupOf U)
  exact Nat.card_congr (Equiv.ofBijective f ⟨f.injective, hs⟩)

variable {D : D7} (X : HidaSetting D) (u : D.what₂.Word)

theorem mem_conj_level_subgroup (hK : X.LevelSubgroupCharacter) (c y : X.B.I.Gf) :
    y ∈ (concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom ↔ c⁻¹ * y * c ∈ X.K2 := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have e : c⁻¹ * ((MulAut.conj c).toMonoidHom k) * c = k := by
      simp [MulAut.conj_apply]; group
    rw [e]; exact hk
  · intro h
    refine ⟨c⁻¹ * y * c, h, ?_⟩
    simp [MulAut.conj_apply]; group

theorem coe_conj_level_subgroup (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) :
    (((concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom : Subgroup X.B.I.Gf) : Set X.B.I.Gf) =
      (fun y => c⁻¹ * y * c) ⁻¹' X.K2 := by
  ext y
  exact mem_conj_level_subgroup X hK c y

theorem rat_fst_inj {q s : X.B.I.GA} (hq : q ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I) (hs : s ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I)
    (h : q.1 = s.1) : q = s := by
  have h1 : (q⁻¹ * s).1 = 1 := by rw [Prod.fst_mul, Prod.fst_inv, h, inv_mul_cancel]
  have := Formalism.L2.SG.Pf.SlabCoverPf.finite_infinite_injective D X (q⁻¹ * s) (mul_mem (inv_mem hq) hs) h1
  exact (inv_mul_eq_one.1 this)

theorem mem_RcS (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) (s : X.B.I.GA) :
    s ∈ RcS X u hK c ↔ s ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ∧
      s.1 ∈ Formalism.L2.SG.Pf.NinfSub (I := X.B.I) X.eR (X.zR u) ∧ s.2 ∈ UcS X u hK c := by
  unfold RcS
  rw [Subgroup.mem_inf, Subgroup.mem_prod]

theorem relIndex_gc (hK : X.LevelSubgroupCharacter) (c c' : X.B.I.Gf) :
    (GcS X u hK c').relIndex (GcS X u hK c) =
      (UcS X u hK c').relIndex ((RcS X u hK c).map (MonoidHom.snd _ _)) := by
  let φ : RcS X u hK c →* X.B.I.Ginf := (MonoidHom.fst _ _).comp (RcS X u hK c).subtype
  let ψ : RcS X u hK c →* X.B.I.Gf := (MonoidHom.snd _ _).comp (RcS X u hK c).subtype
  have hφ : GcS X u hK c = φ.range := by
    unfold GcS
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hψ : (RcS X u hK c).map (MonoidHom.snd _ _) = ψ.range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hcomap : (GcS X u hK c').comap φ = (UcS X u hK c').comap ψ := by
    ext r
    obtain ⟨r, hr⟩ := r
    rw [Subgroup.mem_comap, Subgroup.mem_comap]
    show r.1 ∈ GcS X u hK c' ↔ r.2 ∈ UcS X u hK c'
    obtain ⟨hrQ, hr1, -⟩ := (mem_RcS X u hK c r).1 hr
    constructor
    · rintro ⟨s, hs, hs1⟩
      obtain ⟨hsQ, -, hs2⟩ := (mem_RcS X u hK c' s).1 hs
      have e : s = r := rat_fst_inj X hsQ hrQ hs1
      rw [← e]; exact hs2
    · intro h2
      exact ⟨r, (mem_RcS X u hK c' r).2 ⟨hrQ, hr1, h2⟩, rfl⟩
  rw [hφ, hψ, ← Subgroup.index_comap, ← Subgroup.index_comap, hcomap]

theorem isOpen_conj_level_subgroup (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) :
    IsOpen (((concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom : Subgroup X.B.I.Gf) : Set X.B.I.Gf) := by
  rw [coe_conj_level_subgroup]
  exact (level_subgroup_isClopen X hK (Formalism.L2.SG.Closed.level_subgroup_properties X)).isOpen.preimage
    ((continuous_const.mul continuous_id).mul continuous_const)

theorem isCompact_conj_level_subgroup (hK : X.LevelSubgroupCharacter) (c : X.B.I.Gf) :
    IsCompact (((concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom : Subgroup X.B.I.Gf) : Set X.B.I.Gf) := by
  have hKL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have hK2 : IsCompact X.K2 :=
    (PI.WAU.Cpt.isCompact_Kset X.B.I).of_isClosed_subset (level_subgroup_isClopen X hK hKL).isClosed hKL.2.1
  have e : (((concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom : Subgroup X.B.I.Gf) : Set X.B.I.Gf) =
      (fun k => c * k * c⁻¹) '' X.K2 := by
    rw [Subgroup.coe_map]
    rfl
  rw [e]
  exact hK2.image ((continuous_const.mul continuous_id).mul continuous_const)

theorem relIndex_uc_ne_zero (hK : X.LevelSubgroupCharacter) (c c' : X.B.I.Gf) :
    (UcS X u hK c').relIndex (UcS X u hK c) ≠ 0 := by
  set N := Formalism.L2.SG.Pf.NfinSub (I := X.B.I) X.eR (X.zR u)
  set C := (concreteLevelAdelicSubset X hK).map (MulAut.conj c).toMonoidHom
  set C' := (concreteLevelAdelicSubset X hK).map (MulAut.conj c').toMonoidHom
  have hU : UcS X u hK c = N ⊓ C := rfl
  have hU' : UcS X u hK c' = N ⊓ C' := rfl
  have hCC : C'.relIndex C ≠ 0 := by
    have : CompactSpace C := isCompact_iff_compactSpace.mp (isCompact_conj_level_subgroup X hK c)
    have ho : IsOpen ((C'.subgroupOf C : Subgroup C) : Set C) :=
      (isOpen_conj_level_subgroup X hK c').preimage continuous_subtype_val
    have := Subgroup.quotient_finite_of_isOpen (C'.subgroupOf C) ho
    exact Subgroup.index_ne_zero_of_finite
  have e1 : (N ⊓ C').relIndex (N ⊓ C) = C'.relIndex (N ⊓ C) := by
    rw [← Subgroup.inf_relIndex_right (N ⊓ C'), ← Subgroup.inf_relIndex_right C' (N ⊓ C)]
    congr 1
    ext y
    simp only [Subgroup.mem_inf]
    tauto
  rw [hU, hU', e1]
  intro h0
  exact hCC (Subgroup.relIndex_eq_zero_of_le_right inf_le_right h0)

theorem dense_uc (hK : X.LevelSubgroupCharacter) (c c' : X.B.I.Gf) :
    ∀ x ∈ UcS X u hK c, ∃ y ∈ (RcS X u hK c).map (MonoidHom.snd _ _), y⁻¹ * x ∈ UcS X u hK c' := by
  intro x hx
  obtain ⟨hxN, hxC⟩ := Subgroup.mem_inf.1 hx
  have hxK : c⁻¹ * x * c ∈ X.K2 := (mem_conj_level_subgroup X hK c x).1 hxC
  have hKo := (level_subgroup_isClopen X hK (Formalism.L2.SG.Closed.level_subgroup_properties X)).isOpen
  let O : Set X.B.I.Gf := {y | c⁻¹ * (x⁻¹ * y) * c ∈ X.K2 ∧ c'⁻¹ * (x⁻¹ * y) * c' ∈ X.K2}
  have hO : IsOpen O := by
    refine (hKo.preimage ?_).inter (hKo.preimage ?_)
    · exact (continuous_const.mul (continuous_const.mul continuous_id)).mul continuous_const
    · exact (continuous_const.mul (continuous_const.mul continuous_id)).mul continuous_const
  have hxO : x ∈ O := by
    refine ⟨?_, ?_⟩ <;> simpa using hK.1
  obtain ⟨ν, hνQ, hν1, hν2, hνO⟩ := Formalism.L2.SG.Pf.SlabNDensePf.nilradical_strong_approximation D X u x hxN O hO hxO
  obtain ⟨hk1, hk2⟩ := hνO
  have hν2C : c⁻¹ * ν.2 * c ∈ X.K2 := by
    have e : c⁻¹ * ν.2 * c = (c⁻¹ * x * c) * (c⁻¹ * (x⁻¹ * ν.2) * c) := by group
    rw [e]; exact hK.2.1 _ hxK _ hk1
  have hνR : ν ∈ RcS X u hK c :=
    (mem_RcS X u hK c ν).2 ⟨hνQ, hν1, Subgroup.mem_inf.2 ⟨hν2, (mem_conj_level_subgroup X hK c _).2 hν2C⟩⟩
  refine ⟨ν.2, ⟨ν, hνR, rfl⟩, Subgroup.mem_inf.2 ⟨?_, (mem_conj_level_subgroup X hK c' _).2 ?_⟩⟩
  · exact mul_mem (inv_mem (show ν.2 ∈ Formalism.L2.SG.Pf.NfinSub (I := X.B.I) X.eR (X.zR u) from hν2)) hxN
  · have e : c'⁻¹ * (ν.2⁻¹ * x) * c' = (c'⁻¹ * (x⁻¹ * ν.2) * c')⁻¹ := by group
    rw [e]; exact hK.2.2.1 _ hk2

theorem indexTransferC_holds : IndexTransferC := by
  intro D X u hK g h
  set c := (g : X.B.I.Gf) * X.xu u
  set c' := (h : X.B.I.Gf) * X.xu u
  have hle : (RcS X u hK c).map (MonoidHom.snd _ _) ≤ UcS X u hK c := by
    rintro _ ⟨s, hs, rfl⟩
    exact ((mem_RcS X u hK c s).1 hs).2.2
  refine ⟨?_, relIndex_uc_ne_zero X u hK c c'⟩
  rw [relIndex_gc X u hK c c']
  exact relIndex_eq_of_dense hle (dense_uc X u hK c c')

end Formalism.L2.SG.Pf.IdMeet
end
end
