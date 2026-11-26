module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActFrame

@[expose] public section

section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfI
section -- merged from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ScalarFramePfH
noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open PI.ScalarPairDr.W (mem_orth hT_swap orth_orth finrank_orth fvec_castSucc fvec_last mem_orth_Xplus
  X_le_orth_Xplus mem_ThPairs hT_add_left hT_sub_left hT_smul_left)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

theorem exists_hos : ∃ _P : HeightOneSpectrum (𝓞 E), True := by
  obtain ⟨p, hp0, hp⟩ := Ring.not_isField_iff_exists_prime.1 (NumberField.RingOfIntegers.not_isField E)
  exact ⟨⟨p, hp, hp0⟩, trivial⟩

theorem X_le_spanE_of_conv (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (g : ℕ) (hc : IsFixedConv Λ g F) :
    Xsp F ≤ spanE S (XLam Λ F) := by
  obtain ⟨P, -⟩ := exists_hos (E := E)
  have := P.isPrime
  obtain ⟨c, hc0, -, heq⟩ := hc.1 P
  rw [Xsp, FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  have h1 : c a • F.fl.e a ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ F) := by
    rw [heq]
    exact ⟨1, Submonoid.one_mem _, by rw [one_smul]; exact Submodule.subset_span ⟨a, rfl⟩⟩
  obtain ⟨s, hs, hsx⟩ := h1
  have hs0 : (algebraMap (𝓞 E) E s) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := (FaithfulSMul.algebraMap_injective (𝓞 E) E) (by rw [h, map_zero])
    rw [this]
    exact P.asIdeal.zero_mem
  have hmem : s • (c a • F.fl.e a) ∈ spanE S (XLam Λ F) := Submodule.subset_span hsx
  have e : F.fl.e a = ((algebraMap (𝓞 E) E s) * c a)⁻¹ • (s • (c a • F.fl.e a)) := by
    rw [algebra_compatible_smul E s, smul_smul, smul_smul, mul_assoc, inv_mul_cancel₀ (mul_ne_zero hs0 (hc0 a)),
      one_smul]
  rw [SetLike.mem_coe, e]
  exact Submodule.smul_mem _ _ hmem

theorem Xs_fvec (F : FlagG S r T) : Xs (S := S) F.fvec = F.X := by
  have h : (fun a : Fin r => F.fvec a.castSucc) = F.e := funext fun a => fvec_castSucc F a
  show Submodule.span E (Set.range fun a : Fin r => F.fvec a.castSucc) = _
  rw [h]
  rfl

theorem Xflag_top (F : LFlag S r T) : Xflag F r = Xsp F := by
  rw [Xflag, FlagG.Xa, Xsp, FlagG.X]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨i, -, rfl⟩; exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩; exact ⟨i, i.2, rfl⟩

theorem hT_X_X (F : FlagG S r T) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) : S.hT x y = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  refine key y (fun a => ?_) x hx
  rw [hT_swap]
  have h1 : S.hT y (F.e a) = 0 := key (F.e a) (fun b => F.e_iso b a) y hy
  rw [h1, star_zero]

theorem hT_z_X (F : FlagG S r T) {y : S.V} (hy : y ∈ F.X) : S.hT F.z y = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  rw [hT_swap, key F.z F.z_orth y hy, star_zero]

theorem hT_X_alt (F : FlagG S r T) {x : S.V} (hx : x ∈ F.X) : S.hT x F.z = 0 := by
  have key : ∀ w : S.V, (∀ a, S.hT (F.e a) w = 0) → ∀ x ∈ F.X, S.hT x w = 0 := by
    intro w hw x hx
    have hx' : x ∈ Submodule.span E (Set.range F.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, rfl⟩ := h
      exact hw a
    | zero =>
      have h0 := hT_sub_left (S := S) w w w
      rwa [sub_self, sub_self] at h0
    | add x y _ _ ihx ihy => rw [hT_add_left, ihx, ihy, add_zero]
    | smul c x _ ihx => rw [hT_smul_left, ihx, mul_zero]
  exact key F.z F.z_orth x hx

theorem theta_eq (Λ : Submodule (𝓞 E) S.V) (k : ℕ) (F : LFlag S r T) (F' F'' : LFlag S r T')
    (β : S.V ≃ₗ[E] S.V) (hn : finrank E S.V = k + 2 * r + 1)
    (hd1 : finrank E (UUE Λ F F') = 2 * r + 2) (hd2 : finrank E (UUE Λ F F'') = 2 * r + 2)
    (hU1 : UUE Λ F F' = Submodule.span E (Set.range (Sum.elim F.fl.fvec F'.fl.fvec)))
    (hG' : Gval F F' ≠ 0) (hs : s0 Λ F F' F'' β k = 1) :
    Th Λ F F' F'' β = Hp Λ F F' ∧ Th'' Λ F F' F'' β = Hp Λ F F'' := by
  have hH1 : finrank E (Hp Λ F F') + 1 = k := by
    have := finrank_orth S (UUE Λ F F')
    rw [Hp]
    omega
  have hH2 : finrank E (Hp Λ F F'') + 1 = k := by
    have := finrank_orth S (UUE Λ F F'')
    rw [Hp]
    omega
  have hTh : finrank E (Th Λ F F' F'' β) + 1 = k := by
    unfold s0 at hs
    omega
  have hThle : Th Λ F F' F'' β ≤ Hp Λ F F' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).1
  refine ⟨Submodule.eq_of_le_of_finrank_eq hThle (by omega), ?_⟩
  have hTh''le : Th'' Λ F F' F'' β ≤ Hp Λ F F'' := by
    rintro x ⟨p, hp, rfl⟩
    exact ((mem_ThPairs Λ F F' F'' β p).1 hp).2.1
  refine Submodule.eq_of_le_of_finrank_eq hTh''le ?_
  let f := (LinearMap.snd E S.V S.V).comp (ThPairs Λ F F' F'' β).subtype
  have hker : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro p hp
    have hm := (mem_ThPairs Λ F F' F'' β p.1).1 p.2
    have h2 : p.1.2 = 0 := hp
    have hx1 : p.1.1 ∈ F.fl.X := by
      have := hm.2.2.1
      rwa [h2, sub_zero] at this
    have h1 : p.1.1 = 0 := by
      refine PI.ScalarPairDr.W.eq_zero_of_orth F.fl F'.fl hG' hx1 fun b => ?_
      have hm1 := hm.1
      rw [Hp, mem_orth] at hm1
      exact hm1 _ (by rw [hU1]; exact Submodule.subset_span ⟨Sum.inr b, rfl⟩)
    exact Subtype.ext (Prod.ext h1 h2)
  have hrange : LinearMap.range f = Th'' Λ F F' F'' β := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
    rfl
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  rw [hker, hrange, finrank_bot] at h1
  have h2 : finrank E (Th Λ F F' F'' β) ≤ finrank E (ThPairs Λ F F' F'' β) :=
    Submodule.finrank_map_le _ _
  have h3 := Submodule.finrank_mono hTh''le
  omega

theorem ylift_tr (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hTh : Th Λ F F' F'' β = Hp Λ F F') {y : S.V} (hy : y ∈ UUE Λ F F'') (hyo : y ∈ orth S (Xplus F)) :
    y ∈ UUE Λ F F' := by
  rw [← orth_orth S (UUE Λ F F'), mem_orth]
  intro v hv
  have hv' : v ∈ Th Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT p.2 y = 0 := by
    have := (mem_orth S).1 hm.2.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (p.1 - p.2) y = 0 := (mem_orth S).1 hyo _ (Submodule.mem_sup_left hm.2.2.1)
  have : p.1 = (p.1 - p.2) + p.2 := by abel
  show S.hT p.1 y = 0
  rw [this, hT_add_left, e1, e2, add_zero]

theorem ylift_tr' (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y : S.V} (hy : y ∈ UUE Λ F F') (hyo : y ∈ orth S (Xplus F)) :
    y ∈ UUE Λ F F'' := by
  rw [← orth_orth S (UUE Λ F F''), mem_orth]
  intro v hv
  have hv' : v ∈ Th'' Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT p.1 y = 0 := by
    have := (mem_orth S).1 hm.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (p.1 - p.2) y = 0 := (mem_orth S).1 hyo _ (Submodule.mem_sup_left hm.2.2.1)
  have : p.2 = p.1 - (p.1 - p.2) := by abel
  show S.hT p.2 y = 0
  rw [this, hT_sub_left, e1, e2, sub_zero]

theorem ylift_beta (Λ : Submodule (𝓞 E) S.V) (F : LFlag S r T) (F' F'' : LFlag S r T') (β : S.V ≃ₗ[E] S.V)
    (hiso : ∀ x y, S.hT (β x) (β y) = S.hT x y) (hX : ∀ x ∈ Xsp F'', β.symm x ∈ Xsp F')
    (hTh : Th'' Λ F F' F'' β = Hp Λ F F'') {y : S.V} (hy : y ∈ UUE Λ F F') (hyo : y ∈ orth S (Xsp F')) :
    β y ∈ UUE Λ F F'' := by
  rw [← orth_orth S (UUE Λ F F''), mem_orth]
  intro v hv
  have hv' : v ∈ Th'' Λ F F' F'' β := by rw [hTh]; exact hv
  obtain ⟨p, hp, rfl⟩ := hv'
  have hm := (mem_ThPairs Λ F F' F'' β p).1 hp
  have e1 : S.hT (β p.1) (β y) = 0 := by
    rw [hiso]
    have := (mem_orth S).1 hm.1 _ hy
    rw [hT_swap, this, star_zero]
  have e2 : S.hT (β p.1 - p.2) (β y) = 0 := by
    have h := hX _ hm.2.2.2
    have : β p.1 - p.2 = β (β.symm (β p.1 - p.2)) := (β.apply_symm_apply _).symm
    rw [this, hiso]
    exact (mem_orth S).1 hyo _ h
  have : p.2 = β p.1 - (β p.1 - p.2) := by abel
  show S.hT p.2 (β y) = 0
  rw [this, hT_sub_left, e1, e2, sub_zero]

end Lat

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Cof

variable {D : D7}

theorem GZ_apply (u v : Fin (D.R.rS + 1) → (VS D).V) (a b : Fin (D.R.rS + 1)) :
    GZ u v a b = (VS D).hT (u a) (v b) := rfl

theorem GDl_top' (u v : Fin (D.R.rS + 1) → (VS D).V) : GDl u v (D.R.rS + 1) = (GZ u v).det := by
  unfold GDl
  rw [dite_eq_left le_rfl]
  congr 1

theorem GDl_r' (u v : Fin (D.R.rS + 1) → (VS D).V) :
    GDl u v D.R.rS = ((GZ u v).submatrix Fin.castSucc Fin.castSucc).det := by
  unfold GDl
  rw [dite_eq_left (Nat.le_succ _)]
  have ecs : (Fin.castLE (Nat.le_succ D.R.rS) : Fin D.R.rS → Fin (D.R.rS + 1)) = Fin.castSucc :=
    funext fun i => Fin.ext rfl
  rw [ecs]

theorem om'_pair (u v : Fin (D.R.rS + 1) → (VS D).V) (a : Fin (D.R.rS + 1)) :
    (VS D).hT (u a) (Gom' u v) = if a = Fin.last _ then GDl u v (D.R.rS + 1) else 0 := by
  have key := congrFun (congrFun (Matrix.mul_adjugate (GZ u v)) a) (Fin.last _)
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at key
  rw [GDl_top']
  unfold Gom'
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rw [show (∑ b, (GZ u v).adjugate b (Fin.last _) * (VS D).hT (u a) (v b)) =
      ∑ b, GZ u v a b * (GZ u v).adjugate b (Fin.last _) from
    Finset.sum_congr rfl fun b _ => by rw [GZ_apply, mul_comm], key]
  split_ifs <;> simp

theorem om'_decomp (u v : Fin (D.R.rS + 1) → (VS D).V) :
    Gom' u v - GDl u v D.R.rS • v (Fin.last _) ∈ Xs (S := VS D) v := by
  unfold Gom'
  rw [Fin.sum_univ_castSucc, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r', add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem om_pair (u v : Fin (D.R.rS + 1) → (VS D).V) (b : Fin (D.R.rS + 1)) :
    (VS D).hT (Gom u v) (v b) = if b = Fin.last _ then GDl u v (D.R.rS + 1) else 0 := by
  have key := congrFun (congrFun (Matrix.adjugate_mul (GZ u v)) (Fin.last _)) b
  rw [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply] at key
  rw [GDl_top']
  unfold Gom
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, LinearMap.sum_apply]
  simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply, star_star]
  rw [show (∑ a, (GZ u v).adjugate (Fin.last _) a * (VS D).hT (u a) (v b)) =
      ∑ a, (GZ u v).adjugate (Fin.last _) a * GZ u v a b from rfl, key]
  rcases eq_or_ne b (Fin.last _) with hb | hb
  · subst hb
    simp
  · rw [if_neg (Ne.symm hb), if_neg hb, smul_zero]

theorem om_decomp (u v : Fin (D.R.rS + 1) → (VS D).V) :
    Gom u v - star (GDl u v D.R.rS) • u (Fin.last _) ∈ Xs (S := VS D) u := by
  unfold Gom
  rw [Fin.sum_univ_castSucc, PI.UnitaryGroupMassFormula.BetaLUniq.GN.adj_last, ← GDl_r', add_sub_cancel_right]
  exact Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)

theorem lemB (u v : Fin (D.R.rS + 1) → (VS D).V) (hdet : GDl u v (D.R.rS + 1) ≠ 0) {q : (VS D).V}
    (hq : q ∈ Submodule.span D.host.E (Set.range v)) (h : ∀ a, (VS D).hT (u a) q = 0) : q = 0 := by
  obtain ⟨π, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hq
  have hm : Matrix.mulVec (GZ u v) π = 0 := by
    funext a
    have := h a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    simp only [map_smul, smul_eq_mul] at this
    simp only [Matrix.mulVec, dotProduct, Pi.zero_apply, GZ_apply]
    rw [← this]
    exact Finset.sum_congr rfl fun b _ => mul_comm _ _
  rw [GDl_top'] at hdet
  have hπ := Matrix.eq_zero_of_mulVec_eq_zero hdet hm
  simp [hπ]

theorem eq_zero_of_orth_of_det_ne_zero (u v : Fin (D.R.rS + 1) → (VS D).V) (hdet : GDl u v (D.R.rS + 1) ≠ 0) {q : (VS D).V}
    (hq : q ∈ Submodule.span D.host.E (Set.range u)) (h : ∀ b, (VS D).hT q (v b) = 0) : q = 0 := by
  obtain ⟨κ, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hq
  have hm : Matrix.vecMul (fun a => star (κ a)) (GZ u v) = 0 := by
    funext b
    have := h b
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, LinearMap.sum_apply] at this
    simp only [LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at this
    simp only [Matrix.vecMul, dotProduct, Pi.zero_apply, GZ_apply]
    exact this
  rw [GDl_top'] at hdet
  have hκ := Matrix.eq_zero_of_vecMul_eq_zero hdet hm
  have : κ = 0 := by
    funext a
    have := congrFun hκ a
    simpa using this
  simp [this]

theorem lemC (v : Fin (D.R.rS + 1) → (VS D).V) (hv : LinearIndependent D.host.E v) {c : D.host.E}
    (h : c • v (Fin.last _) ∈ Xs (S := VS D) v) : c = 0 := by
  obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 h
  have h0 : ∑ i, (Fin.snoc (α := fun _ => D.host.E) d (-c) i) • v i = 0 := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.snoc_castSucc, Fin.snoc_last, neg_smul]
    rw [hd, add_neg_cancel]
  have := Fintype.linearIndependent_iff.1 hv _ h0 (Fin.last _)
  simpa using this

end Cof

end Formalism.L2.SG.Pf.ScalarFramePf
end
end

noncomputable section

open scoped Classical

namespace Formalism.L2.SG.Pf.ScalarFramePf

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc
open PI.ScalarPairDr.W (mem_orth hT_swap orth_orth fvec_castSucc fvec_last mem_orth_Xplus hT_smul_left)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Scal

variable {D : D7} (Λ : Submodule (𝓞 D.host.E) (VS D).V) {T T' : D.host.E}

theorem span_left_le (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule.span D.host.E (Set.range F.fl.fvec) ≤
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₁.fl.fvec)) :=
  Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inl a, rfl⟩)

theorem span_right_le (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ : LFlag (D.sp.Y 0) D.R.rS T') :
    Submodule.span D.host.E (Set.range F₁.fl.fvec) ≤
      Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₁.fl.fvec)) :=
  Submodule.span_mono (by rintro _ ⟨a, rfl⟩; exact ⟨Sum.inr a, rfl⟩)

theorem Xsp_le_span (F : LFlag (D.sp.Y 0) D.R.rS T) :
    Xsp F ≤ Submodule.span D.host.E (Set.range F.fl.fvec) := by
  rw [Xsp, FlagG.X, Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact Submodule.subset_span ⟨a.castSucc, fvec_castSucc _ _⟩

theorem Xsp_eq_Xs (F : LFlag (D.sp.Y 0) D.R.rS T) : Xsp F = Xs (S := VS D) F.fl.fvec := (Xs_fvec F.fl).symm

theorem z_mem_span (F : LFlag (D.sp.Y 0) D.R.rS T) :
    F.fl.z ∈ Submodule.span D.host.E (Set.range F.fl.fvec) :=
  Submodule.subset_span ⟨Fin.last _, fvec_last _⟩

theorem Gom'_mem (u v : Fin (D.R.rS + 1) → (VS D).V) : Gom' u v ∈ Submodule.span D.host.E (Set.range v) :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem Gom_mem (u v : Fin (D.R.rS + 1) → (VS D).V) : Gom u v ∈ Submodule.span D.host.E (Set.range u) :=
  Submodule.sum_mem _ fun b _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨b, rfl⟩)

theorem scal_dir (F : LFlag (D.sp.Y 0) D.R.rS T) (F₁ F₂ : LFlag (D.sp.Y 0) D.R.rS T')
    (hz : F.zt = F.fl.z) (hz₁ : F₁.zt = F₁.fl.z) (hz₂ : F₂.zt = F₂.fl.z) (hT0 : T ≠ 0)
    (hU2 : UUE Λ F F₂ = Submodule.span D.host.E (Set.range (Sum.elim F.fl.fvec F₂.fl.fvec)))
    (htr : ∀ y ∈ UUE Λ F F₂, y ∈ orth (VS D) (Xplus F) → y ∈ UUE Λ F F₁)
    (hsc : ∀ y, y ∈ Ylift Λ F F₁ → y ∈ Ylift Λ F F₂ → ∀ α α', SgRel F F₂ y 0 α α' → SgRel F F₁ y 0 α α')
    (hind : LinearIndependent D.host.E F₁.fl.fvec)
    (hD1 : GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) ≠ 0) :
    (∃ x ∈ Xsp F, GDl F.fl.fvec F₂.fl.fvec (D.R.rS + 1) • Gom' F.fl.fvec F₁.fl.fvec =
      GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) • (Gom' F.fl.fvec F₂.fl.fvec - x)) ∧
    GDl F.fl.fvec F₁.fl.fvec (D.R.rS + 1) * GDl F.fl.fvec F₂.fl.fvec D.R.rS =
      GDl F.fl.fvec F₂.fl.fvec (D.R.rS + 1) * GDl F.fl.fvec F₁.fl.fvec D.R.rS := by
  set f := F.fl.fvec with hf
  set f1 := F₁.fl.fvec with hf1
  set f2 := F₂.fl.fvec with hf2
  set D1 := GDl f f1 (D.R.rS + 1) with hD1def
  set D2 := GDl f f2 (D.R.rS + 1) with hD2def
  set R1 := GDl f f1 D.R.rS with hR1def
  set R2 := GDl f f2 D.R.rS with hR2def
  set om1 := Gom' f f1 with hom1
  set om2 := Gom' f f2 with hom2
  have hfl : f (Fin.last _) = F.fl.z := fvec_last _
  have hfc : ∀ a : Fin D.R.rS, f a.castSucc = F.fl.e a := fun a => fvec_castSucc _ a
  have p1 : ∀ a, (VS D).hT (f a) om1 = if a = Fin.last _ then D1 else 0 := om'_pair f f1
  have p2 : ∀ a, (VS D).hT (f a) om2 = if a = Fin.last _ then D2 else 0 := om'_pair f f2
  have hzz : (VS D).hT F.fl.z F.fl.z = -T := F.fl.z_norm
  set u2 := om2 + (D2 / T) • F.fl.z with hu2
  have hu2U : u2 ∈ UUE Λ F F₂ := by
    rw [hU2]
    exact Submodule.add_mem _ (span_right_le F F₂ (Gom'_mem f f2))
      (Submodule.smul_mem _ _ (span_left_le F F₂ (z_mem_span F)))
  have hu2o : u2 ∈ orth (VS D) (Xplus F) := by
    rw [Xplus, mem_orth_Xplus]
    refine ⟨fun a => ?_, ?_⟩
    · have h1 := p2 a.castSucc
      rw [if_neg (Fin.castSucc_ne_last a), hfc] at h1
      rw [hu2, map_add (f := _), map_smul, h1, F.fl.z_orth a, smul_zero, add_zero]
    · have h1 := p2 (Fin.last _)
      rw [if_pos rfl, hfl] at h1
      rw [hu2, map_add (f := _), map_smul, h1, hzz, smul_eq_mul]
      field_simp
      ring
  have hu2U1 := htr u2 hu2U hu2o
  have hx2 : om2 - R2 • F₂.fl.z ∈ Xsp F₂ := by
    rw [Xsp_eq_Xs, ← fvec_last F₂.fl]
    exact om'_decomp f f2
  have hsg : SgRel F F₂ u2 0 (D2 / T) R2 :=
    ⟨0, Submodule.zero_mem _, om2 - R2 • F₂.fl.z, hx2, by rw [hz, hz₂, hu2]; abel⟩
  obtain ⟨x, hx, x1, hx1, heq⟩ := hsc u2 (Submodule.mem_inf.2 ⟨hu2U1, hu2o⟩)
    (Submodule.mem_inf.2 ⟨hu2U, hu2o⟩) _ _ hsg
  rw [hz, hz₁, hu2, sub_zero] at heq
  have hp : R2 • F₁.fl.z + x1 = om2 - x := by
    have : om2 - x = (om2 + (D2 / T) • F.fl.z) - (D2 / T) • F.fl.z - x := by abel
    rw [this, heq]
    abel
  have hpspan : om2 - x ∈ Submodule.span D.host.E (Set.range f1) := by
    rw [← hp]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (z_mem_span F₁)) (Xsp_le_span F₁ hx1)
  have hxX : x ∈ F.fl.X := hx
  have hq0 : D1 • (om2 - x) - D2 • om1 = 0 := by
    refine lemB f f1 hD1 (Submodule.sub_mem _ (Submodule.smul_mem _ _ hpspan)
      (Submodule.smul_mem _ _ (Gom'_mem f f1))) fun a => ?_
    rw [map_sub, map_smul, map_smul, map_sub, p1, p2, smul_eq_mul, smul_eq_mul]
    induction a using Fin.lastCases with
    | last =>
      rw [if_pos rfl, if_pos rfl, hfl, hT_z_X F.fl hxX]
      ring
    | cast a =>
      rw [if_neg (Fin.castSucc_ne_last a), if_neg (Fin.castSucc_ne_last a), hfc,
        hT_X_X F.fl (Submodule.subset_span ⟨a, rfl⟩) hxX]
      ring
  refine ⟨⟨x, hx, (sub_eq_zero.1 hq0).symm⟩, ?_⟩
  have hy1 : om1 - R1 • f1 (Fin.last _) ∈ Xs (S := VS D) f1 := om'_decomp f f1
  have hx1' : x1 ∈ Xs (S := VS D) f1 := by rw [← Xsp_eq_Xs]; exact hx1
  have hlast1 : f1 (Fin.last _) = F₁.fl.z := fvec_last _
  have e : (D1 * R2 - D2 * R1) • f1 (Fin.last _) =
      D2 • (om1 - R1 • f1 (Fin.last _)) - D1 • x1 + (D1 • (om2 - x) - D2 • om1) := by
    rw [← hp, hlast1]
    module
  rw [hq0, add_zero] at e
  have hmem : (D1 * R2 - D2 * R1) • f1 (Fin.last _) ∈ Xs (S := VS D) f1 := by
    rw [e]
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hy1) (Submodule.smul_mem _ _ hx1')
  have hc := lemC f1 hind hmem
  linear_combination hc

end Scal

end Formalism.L2.SG.Pf.ScalarFramePf
