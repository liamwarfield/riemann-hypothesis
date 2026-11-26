module

public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceAt

@[expose] public section

section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InvForm
section -- merged from Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FourVac
set_option linter.style.haveILetI false

noncomputable section

namespace Formalism.IndefR.Fin.Four

variable {W V : Type*} [AddCommGroup W] [AddCommGroup V] [Module ℂ V]

def Yk (L Y : AddSubgroup W) (k : ℕ) : AddSubgroup W := Y ⊓ L.comap (nsmulAddMonoidHom k)

theorem mem_Yk {L Y : AddSubgroup W} {k : ℕ} {y : W} : y ∈ Yk L Y k ↔ y ∈ Y ∧ k • y ∈ L := by
  simp [Yk, AddSubgroup.mem_inf, AddSubgroup.mem_comap]

abbrev Ik (L Y : AddSubgroup W) (k : ℕ) : Type _ := ↥(Yk L Y k) ⧸ (smulSub k (L ⊓ Y)).addSubgroupOf (Yk L Y k)

theorem Ik_finite {L Y : AddSubgroup W} {k : ℕ} [Finite (Qt (k * k) (L ⊓ Y))]
    (htf : ∀ t : W, k • t = 0 → t = 0) : Finite (Ik L Y k) := by
  let f : Ik L Y k → Qt (k * k) (L ⊓ Y) := fun q => QuotientAddGroup.mk
    ⟨k • ((q.out : ↥(Yk L Y k)) : W), AddSubgroup.mem_inf.2 ⟨(mem_Yk.1 (q.out : ↥(Yk L Y k)).2).2,
      Y.nsmul_mem (mem_Yk.1 (q.out : ↥(Yk L Y k)).2).1 k⟩⟩
  refine Finite.of_injective f fun q q' h => ?_
  have h1 := QuotientAddGroup.eq.1 h
  rw [AddSubgroup.mem_addSubgroupOf] at h1
  obtain ⟨u, hu, hux⟩ := mem_smulSub.1 h1
  have h2 : k • (-((q.out : ↥(Yk L Y k)) : W) + ((q'.out : ↥(Yk L Y k)) : W) - k • u) = 0 := by
    rw [smul_sub, smul_add, smul_neg, smul_smul, hux]
    simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
    abel
  have h3 := sub_eq_zero.1 (htf _ h2)
  refine (QuotientAddGroup.out_eq' q).symm.trans ((QuotientAddGroup.eq.2 ?_).trans (QuotientAddGroup.out_eq' q'))
  rw [AddSubgroup.mem_addSubgroupOf]
  simp only [AddSubgroup.coe_add, AddSubgroup.coe_neg]
  rw [h3]
  exact mem_smulSub.2 ⟨u, hu, rfl⟩

def IsLev (ρ : W → Module.End ℂ V) (L X Y : AddSubgroup W) (k : ℕ) (G : V) : Prop :=
  (∀ u ∈ L ⊓ X, ρ (k • u) G = G) ∧ ∀ u ∈ L ⊓ Y, ρ (k • u) G = G

theorem IsLev.mul {ρ : W → Module.End ℂ V} {L X Y : AddSubgroup W} {k : ℕ} {G : V} (h : IsLev ρ L X Y k G) (j : ℕ) :
    IsLev ρ L X Y (k * j) G := by
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · rw [← smul_smul]
    exact h.1 _ (AddSubgroup.nsmul_mem _ hu j)
  · rw [← smul_smul]
    exact h.2 _ (AddSubgroup.nsmul_mem _ hu j)

def piK (ρ : W → Module.End ℂ V) (L X Y : AddSubgroup W) (k : ℕ) (G : V) : V :=
  ∑ᶠ b : Qt k (L ⊓ X), ρ ((b.out : ↥(L ⊓ X)) : W) (∑ᶠ y : Ik L Y k, ρ ((y.out : ↥(Yk L Y k)) : W) G)

theorem Ik_out_mk {L Y : AddSubgroup W} {k : ℕ} (z : Yk L Y k) :
    ∃ v ∈ L ⊓ Y, ((((QuotientAddGroup.mk z : Ik L Y k)).out : ↥(Yk L Y k)) : W) + k • v = (z : W) := by
  have h := QuotientAddGroup.eq.1 (QuotientAddGroup.out_eq' (QuotientAddGroup.mk z : Ik L Y k))
  rw [AddSubgroup.mem_addSubgroupOf] at h
  obtain ⟨v, hv, hvx⟩ := mem_smulSub.1 h
  refine ⟨v, hv, ?_⟩
  rw [hvx]
  push_cast
  abel

section PiK

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}

theorem piK_add {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] (G H : V) :
    piK ρ L X Y k (G + H) = piK ρ L X Y k G + piK ρ L X Y k H := by
  haveI := Fintype.ofFinite (Qt k (L ⊓ X))
  haveI := Fintype.ofFinite (Ik L Y k)
  simp only [piK, finsum_eq_sum_of_fintype, map_add (f := _), Finset.sum_add_distrib]

theorem piK_smul {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] (c : ℂ) (G : V) :
    piK ρ L X Y k (c • G) = c • piK ρ L X Y k G := by
  haveI := Fintype.ofFinite (Qt k (L ⊓ X))
  haveI := Fintype.ofFinite (Ik L Y k)
  simp only [piK, finsum_eq_sum_of_fintype, map_smul, ← Finset.smul_sum]

theorem piK_sub {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] (G H : V) :
    piK ρ L X Y k (G - H) = piK ρ L X Y k G - piK ρ L X Y k H := by
  haveI := Fintype.ofFinite (Qt k (L ⊓ X))
  haveI := Fintype.ofFinite (Ik L Y k)
  simp only [piK, finsum_eq_sum_of_fintype, map_sub, Finset.sum_sub_distrib]

theorem piK_shift (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y') {k : ℕ} [Finite (Ik L Y k)]
    {u : W} (hu : u ∈ Yk L Y k) {G : V} (hG : ∀ v ∈ L ⊓ Y, ρ (k • v) G = G) :
    piK ρ L X Y k (ρ u G) = piK ρ L X Y k G := by
  classical
  letI := Fintype.ofFinite (Ik L Y k)
  unfold piK
  congr 1
  funext b
  congr 1
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
  let m : Ik L Y k := QuotientAddGroup.mk ⟨u, hu⟩
  have huY : u ∈ Y := (mem_Yk.1 hu).1
  have key : ∀ y : Ik L Y k, ρ ((y.out : ↥(Yk L Y k)) : W) (ρ u G) = ρ (((y + m).out : ↥(Yk L Y k)) : W) G := by
    intro y
    have hyY : ((y.out : ↥(Yk L Y k)) : W) ∈ Y := (mem_Yk.1 (y.out : ↥(Yk L Y k)).2).1
    have h1 : y + m = QuotientAddGroup.mk (y.out + ⟨u, hu⟩) := by
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
    obtain ⟨v, hv, hout⟩ := Ik_out_mk (L := L) (Y := Y) (k := k) (y.out + ⟨u, hu⟩)
    rw [h1]
    have hoY : ((((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out : ↥(Yk L Y k)) : W) ∈ Y :=
      (mem_Yk.1 ((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out.2).1
    have hkvY : k • v ∈ Y := Y.nsmul_mem (AddSubgroup.mem_inf.1 hv).2 k
    rw [← Module.End.mul_apply, ← hY _ hyY _ huY]
    have h2 : ((y.out : ↥(Yk L Y k)) : W) + u =
        ((((QuotientAddGroup.mk (y.out + ⟨u, hu⟩) : Ik L Y k)).out : ↥(Yk L Y k)) : W) + k • v := by
      rw [hout]
      push_cast
      rfl
    rw [h2, hY _ hoY _ hkvY, Module.End.mul_apply, hG v hv]
  rw [Finset.sum_congr rfl fun y _ => key y]
  exact Fintype.sum_equiv (Equiv.addRight m) _ _ (fun _ => rfl)

end PiK

section Vac

variable {ρ : W → Module.End ℂ V} {χ : W → W → ℂ} {L X Y : AddSubgroup W}
  (hX : ∀ x ∈ X, ∀ x' ∈ X, ρ (x + x') = ρ x * ρ x')
  (hY : ∀ y ∈ Y, ∀ y' ∈ Y, ρ (y + y') = ρ y * ρ y')
  (hXY : ∀ x ∈ X, ∀ y ∈ Y, ρ x * ρ y = χ x y • (ρ y * ρ x))
  (hχl : ∀ t t' y, χ (t + t') y = χ t y * χ t' y)
  (hχr : ∀ t y y', χ t (y + y') = χ t y * χ t y') (hχ0 : ∀ t y, χ t y ≠ 0)
  (hLL : ∀ x ∈ L ⊓ X, ∀ y ∈ L ⊓ Y, χ x y = 1)
  (hdY : ∀ y ∈ Y, (∀ x ∈ L ⊓ X, χ x y = 1) → y ∈ L)
  (hfinX : ∀ k, 0 < k → Finite (Qt k (L ⊓ X))) (hfinY : ∀ k, 0 < k → Finite (Qt k (L ⊓ Y)))
  (htf : ∀ k : ℕ, 0 < k → ∀ t : W, k • t = 0 → t = 0)

include hχl hχr hχ0 hLL hdY in
open Classical in
theorem chi_sum_X {k : ℕ} [Fintype (Qt k (L ⊓ X))] {y : W} (hy : y ∈ Yk L Y k) :
    ∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y =
      if y ∈ L then (Fintype.card (Qt k (L ⊓ X)) : ℂ) else 0 := by
  classical
  have hy' := mem_Yk.1 hy
  split_ifs with hyL
  · have h1 : ∀ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y = 1 := fun b =>
      hLL _ (b.out : ↥(L ⊓ X)).2 y (AddSubgroup.mem_inf.2 ⟨hyL, hy'.1⟩)
    simp only [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
  · have hne : ¬ ∀ x ∈ L ⊓ X, χ x y = 1 := fun hall => hyL (hdY y hy'.1 hall)
    push_neg at hne
    obtain ⟨u, hu, hχu⟩ := hne
    let m : Qt k (L ⊓ X) := QuotientAddGroup.mk ⟨u, hu⟩
    have hkey : ∀ b : Qt k (L ⊓ X), χ (((b + m).out : ↥(L ⊓ X)) : W) y = χ ((b.out : ↥(L ⊓ X)) : W) y * χ u y := by
      intro b
      have h1 : b + m = QuotientAddGroup.mk (b.out + ⟨u, hu⟩) := by
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq']
      obtain ⟨v, hv, hout⟩ := out_mk k (L ⊓ X) (b.out + ⟨u, hu⟩)
      rw [h1]
      have h2 : (((QuotientAddGroup.mk (b.out + ⟨u, hu⟩) : Qt k (L ⊓ X)).out : ↥(L ⊓ X)) : W) =
          ((b.out : ↥(L ⊓ X)) : W) + u + -(k • v) := by
        rw [eq_sub_of_add_eq hout]; push_cast; abel
      rw [h2, hχl, hχl, chi_neg_left hχl hχ0, chi_nsmul_left hχl hχ0, ← chi_nsmul_right hχr hχ0,
        hLL v hv _ (AddSubgroup.mem_inf.2 ⟨hy'.2, Y.nsmul_mem hy'.1 k⟩), inv_one, mul_one]
    have hshift : ∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y =
        (∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y) * χ u y := by
      rw [Finset.sum_mul]
      rw [← Fintype.sum_equiv (Equiv.addRight m) (fun b => χ (((b + m).out : ↥(L ⊓ X)) : W) y)
        (fun b => χ ((b.out : ↥(L ⊓ X)) : W) y) (fun b => rfl)]
      exact Finset.sum_congr rfl fun b _ => hkey b
    have hz : (1 - χ u y) * ∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) y = 0 := by
      linear_combination hshift
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd (sub_eq_zero.1 h).symm hχu
    · exact h

include hXY hχl hχr hχ0 hLL hdY in
theorem piK_vac {k : ℕ} [Finite (Qt k (L ⊓ X))] [Finite (Ik L Y k)] {w : V} (hwX : ∀ u ∈ L ⊓ X, ρ u w = w)
    (hwY : ∀ u ∈ L ⊓ Y, ρ u w = w) : ∃ c : ℂ, c ≠ 0 ∧ piK ρ L X Y k w = c • w := by
  classical
  letI := Fintype.ofFinite (Qt k (L ⊓ X))
  letI := Fintype.ofFinite (Ik L Y k)
  have hyk : ∀ y : Ik L Y k, ((y.out : ↥(Yk L Y k)) : W) ∈ Yk L Y k := fun y => (y.out : ↥(Yk L Y k)).2
  have hterm : ∀ (b : Qt k (L ⊓ X)) (y : Ik L Y k), ρ ((b.out : ↥(L ⊓ X)) : W) (ρ ((y.out : ↥(Yk L Y k)) : W) w) =
      χ ((b.out : ↥(L ⊓ X)) : W) ((y.out : ↥(Yk L Y k)) : W) • ρ ((y.out : ↥(Yk L Y k)) : W) w := by
    intro b y
    have := congrArg (fun T : Module.End ℂ V => T w)
      (hXY _ (AddSubgroup.mem_inf.1 (b.out : ↥(L ⊓ X)).2).2 _ (mem_Yk.1 (hyk y)).1)
    simp only [Module.End.mul_apply, LinearMap.smul_apply] at this
    rw [this, hwX _ (b.out : ↥(L ⊓ X)).2]
  have e1 : piK ρ L X Y k w = ∑ y : Ik L Y k,
      (∑ b : Qt k (L ⊓ X), χ ((b.out : ↥(L ⊓ X)) : W) ((y.out : ↥(Yk L Y k)) : W)) •
        ρ ((y.out : ↥(Yk L Y k)) : W) w := by
    unfold piK
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, hterm, Finset.sum_smul]
    exact Finset.sum_comm
  rw [e1]
  simp only [chi_sum_X hχl hχr hχ0 hLL hdY (hyk _)]
  have e2 : ∀ y : Ik L Y k, (if ((y.out : ↥(Yk L Y k)) : W) ∈ L then (Fintype.card (Qt k (L ⊓ X)) : ℂ) else 0) •
      ρ ((y.out : ↥(Yk L Y k)) : W) w =
      (if ((y.out : ↥(Yk L Y k)) : W) ∈ L then (Fintype.card (Qt k (L ⊓ X)) : ℂ) else 0) • w := by
    intro y
    split_ifs with h
    · rw [hwY _ (AddSubgroup.mem_inf.2 ⟨h, (mem_Yk.1 (hyk y)).1⟩)]
    · rw [zero_smul, zero_smul]
  simp only [e2, ← Finset.sum_smul]
  refine ⟨_, ?_, rfl⟩
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul]
  refine mul_ne_zero ?_ (by exact_mod_cast Fintype.card_ne_zero)
  have h0 : (0 : Ik L Y k) ∈ Finset.univ.filter (fun y : Ik L Y k => ((y.out : ↥(Yk L Y k)) : W) ∈ L) := by
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := (QuotientAddGroup.eq_zero_iff _).1 (QuotientAddGroup.out_eq' (0 : Ik L Y k))
    rw [AddSubgroup.mem_addSubgroupOf] at this
    obtain ⟨v, hv, hvx⟩ := mem_smulSub.1 this
    rw [← hvx]
    exact L.nsmul_mem (AddSubgroup.mem_inf.1 hv).1 k
  exact_mod_cast (Finset.card_pos.2 ⟨_, h0⟩).ne'


include hY hXY hχl hχr hχ0 hLL hdY hfinX hfinY htf in
theorem vac_eq_zero_of_mem_span (hoY : ∀ y ∈ Y, ∃ k : ℕ, 0 < k ∧ k • y ∈ L) (Θ : Set V)
    (hlev : ∀ G ∈ Θ, ∃ k : ℕ, 0 < k ∧ IsLev ρ L X Y k G) {w : V}
    (hwX : ∀ u ∈ L ⊓ X, ρ u w = w) (hwY : ∀ u ∈ L ⊓ Y, ρ u w = w)
    (hw : w ∈ Submodule.span ℂ {v | ∃ u ∈ Y, ∃ G ∈ Θ, v = ρ u G - G}) : w = 0 := by
  classical
  obtain ⟨n, f, g, hsum⟩ := Submodule.mem_span_set'.1 hw
  choose u hu G hG hg using fun i => (g i).2
  choose kf hkf0 hkf using fun i => hlev (G i) (hG i)
  choose mf hmf0 hmf using fun i => hoY (u i) (hu i)
  set K := ∏ i, (kf i * mf i) with hKdef
  have hK0 : 0 < K := Finset.prod_pos fun i _ => Nat.mul_pos (hkf0 i) (hmf0 i)
  have hdiv : ∀ i, kf i * mf i ∣ K := fun i => Finset.dvd_prod_of_mem _ (Finset.mem_univ i)
  haveI := hfinX K hK0
  haveI := hfinY (K * K) (Nat.mul_pos hK0 hK0)
  haveI : Finite (Ik L Y K) := Ik_finite (htf K hK0)
  have hzero : ∀ i, piK ρ L X Y K (ρ (u i) (G i) - G i) = 0 := by
    intro i
    obtain ⟨c, hc⟩ := hdiv i
    have hGK : IsLev ρ L X Y K (G i) := by
      have := (hkf i).mul (mf i * c)
      rwa [← mul_assoc, ← hc] at this
    have huK : u i ∈ Yk L Y K := mem_Yk.2 ⟨hu i, by
      rw [hc, mul_comm (kf i) (mf i), mul_assoc, mul_comm, ← smul_smul]
      exact L.nsmul_mem (hmf i) _⟩
    rw [piK_sub, piK_shift hY huK hGK.2, sub_self]
  have hpw : piK ρ L X Y K w = 0 := by
    rw [← hsum]
    have : ∀ s : Finset (Fin n), piK ρ L X Y K (∑ i ∈ s, f i • ((g i : {v | ∃ u ∈ Y, ∃ G ∈ Θ, v = ρ u G - G}) : V)) = 0 := by
      intro s
      induction s using Finset.induction_on with
      | empty =>
        rw [Finset.sum_empty]
        have := piK_smul (ρ := ρ) (L := L) (X := X) (Y := Y) (k := K) (0 : ℂ) (0 : V)
        rwa [zero_smul, zero_smul] at this
      | insert i s his ih =>
        rw [Finset.sum_insert his, piK_add, ih, add_zero, piK_smul, hg i, hzero i, smul_zero]
    exact this Finset.univ
  obtain ⟨c, hc0, hc⟩ := piK_vac hXY hχl hχr hχ0 hLL hdY (k := K) hwX hwY
  rw [hc] at hpw
  exact (smul_eq_zero.1 hpw).resolve_left hc0

end Vac

end Formalism.IndefR.Fin.Four

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D)

theorem exists_invForm (e₁ : AE D) (he : e₁ * cA D e₁ = 0) (Λ : AddSubgroup (WO S T))
    (hLL : ∀ x ∈ Λ, IsHalf e₁ x → ∀ y ∈ Λ, IsHalf (cA D e₁) y → ψ (symplO S T x y) = 1)
    (hdY : ∀ y, IsHalf (cA D e₁) y → (∀ x ∈ Λ, IsHalf e₁ x → ψ (symplO S T x y) = 1) → y ∈ Λ)
    (hfX : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf e₁ u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf e₁ v ∧ u = r + k • v)
    (hfY : ∀ k : ℕ, 0 < k → ∃ R : Finset (WO S T), ∀ u ∈ Λ, IsHalf (cA D e₁) u →
      ∃ r ∈ R, ∃ v ∈ Λ, IsHalf (cA D e₁) v ∧ u = r + k • v)
    (hoY : ∀ y, IsHalf (cA D e₁) y → ∃ k : ℕ, 0 < k ∧ k • y ∈ Λ)
    (hlev : ∀ f, IsThetaFunO ψ S T f → ∃ k : ℕ, 0 < k ∧
      ∀ u ∈ Λ, (IsHalf e₁ u ∨ IsHalf (cA D e₁) u) → heisO ψ S T (k • u) f = f)
    {w : WO S T → ℂ} (hw : IsThetaFunO ψ S T w) (hwX : ∀ u ∈ Λ, IsHalf e₁ u → heisO ψ S T u w = w)
    (hwY : ∀ u ∈ Λ, IsHalf (cA D e₁) u → heisO ψ S T u w = w) (hw0 : w ≠ 0) :
    ∃ ℓ : (WO S T → ℂ) →ₗ[ℂ] ℂ,
      (∀ u : WO S T, (∀ i j, cA D e₁ * u i j = u i j) → ∀ f, IsThetaFunO ψ S T f →
        ℓ (heisO ψ S T u f) = ℓ f) ∧ ℓ w ≠ 0 := by
  have mi := fun {x : WO S T} {H K : AddSubgroup (WO S T)} (h : x ∈ H ⊓ K) => AddSubgroup.mem_inf.1 h
  let N : Submodule ℂ (WO S T → ℂ) := Submodule.span ℂ
    {v | ∃ u ∈ halfSub S T (cA D e₁), ∃ G ∈ {f : WO S T → ℂ | IsThetaFunO ψ S T f}, v = heisL ψ S T u G - G}
  have hwN : w ∉ N := by
    intro hmem
    refine hw0 (Four.vac_eq_zero_of_mem_span (ρ := heisL ψ S T) (χ := fun t y => ψ (symplO S T t y))
      (L := Λ) (X := halfSub S T e₁) (Y := halfSub S T (cA D e₁))
      (fun y hy y' hy' => heisL_add_half ψ S T (cA_half_orth he) hy hy')
      (fun x _ y _ => heisL_comm ψ S T x y)
      (fun t t' y => by simp only [symplO_add_left, AddChar.map_add_eq_mul])
      (fun t y y' => by simp only [symplO_add_right, AddChar.map_add_eq_mul])
      (fun t y => psi_ne_zero ψ _)
      (fun x hx y hy => hLL x (mi hx).1 (mi hx).2 y (mi hy).1 (mi hy).2)
      (fun y hy h => hdY y hy fun x hx hxe => h x (AddSubgroup.mem_inf.2 ⟨hx, hxe⟩))
      (fun k hk => by
        obtain ⟨R, hR⟩ := hfX k hk
        exact finite_qt_of S T R fun u hu => by
          obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
          exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
      (fun k hk => by
        obtain ⟨R, hR⟩ := hfY k hk
        exact finite_qt_of S T R fun u hu => by
          obtain ⟨r, hr, v, hv, hve, huv⟩ := hR u (mi hu).1 (mi hu).2
          exact ⟨r, hr, v, AddSubgroup.mem_inf.2 ⟨hv, hve⟩, huv⟩)
      (fun k hk t h => nsmul_eq_zero_WO S T hk h)
      (fun y hy => hoY y hy) {f | IsThetaFunO ψ S T f}
      (fun G hG => by
        obtain ⟨k, hk, hGk⟩ := hlev G hG
        exact ⟨k, hk, fun u hu => hGk u (mi hu).1 (Or.inl (mi hu).2),
          fun u hu => hGk u (mi hu).1 (Or.inr (mi hu).2)⟩)
      (fun u hu => hwX u (mi hu).1 (mi hu).2) (fun u hu => hwY u (mi hu).1 (mi hu).2) hmem)
  obtain ⟨ℓ, hℓw, hℓN⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hwN inferInstance
  refine ⟨ℓ, fun u hu f hf => ?_, hℓw⟩
  have hmem : heisL ψ S T u f - f ∈ N := Submodule.subset_span ⟨u, hu, f, hf, rfl⟩
  have h0 : ℓ (heisL ψ S T u f - f) = 0 := by
    have : ℓ (heisL ψ S T u f - f) ∈ N.map ℓ := Submodule.mem_map_of_mem hmem
    rw [hℓN] at this
    exact (Submodule.mem_bot ℂ).1 this
  rw [map_sub, sub_eq_zero] at h0
  exact h0

end Formalism.IndefR.Fin

end
end

set_option synthInstance.maxHeartbeats 100000

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Matrix NumberField
open scoped TensorProduct

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_nsmul_mem_cpt' {X : Type*} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X]
    (K : Set X) (hK : IsCompact K) (hKs : ∀ y ∈ K, ∀ n : ℕ, n • y ∈ K) (H : AddSubgroup X)
    (hH : IsOpen (H : Set X)) : ∃ m : ℕ, 0 < m ∧ ∀ y ∈ K, m • y ∈ H := by
  classical
  let U : X → Set X := fun y => (fun x => x - y) ⁻¹' (H : Set X)
  have hU : ∀ y, IsOpen (U y) := fun y => hH.preimage (continuous_id.sub continuous_const)
  have hcov : K ⊆ ⋃ y ∈ K, U y := fun x hx => Set.mem_biUnion hx (by simp [U, H.zero_mem])
  obtain ⟨t, -, htf, hcov'⟩ := hK.elim_finite_subcover_image (fun y _ => hU y) hcov
  obtain ⟨t', rfl⟩ : ∃ t' : Finset X, (t' : Set X) = t := ⟨htf.toFinset, by simp⟩
  refine ⟨t'.card.factorial, Nat.factorial_pos _, fun y hy => ?_⟩
  have hmaps : ∀ j ∈ Finset.range (t'.card + 1), ∃ i ∈ t', j • y ∈ U i := fun j _ => by
    have := hcov' (hKs y hy j)
    simp only [Set.mem_iUnion] at this
    obtain ⟨i, hi, hji⟩ := this
    exact ⟨i, by simpa using hi, hji⟩
  choose! f hf using hmaps
  obtain ⟨j1, hj1, j2, hj2, hne, heq⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (t'.card + 1)) (t := t') (by simp) (f := f) (fun j hj => (hf j hj).1)
  have h1 := (hf j1 hj1).2
  have h2 := (hf j2 hj2).2
  rw [heq] at h1
  have hdiff : ((j1 : ℤ) - j2) • y ∈ H := by
    convert H.sub_mem h1 h2 using 1
    show _ = (j1 • y - f j2) - (j2 • y - f j2)
    rw [sub_zsmul, natCast_zsmul, natCast_zsmul]
    abel
  have hj1' : j1 ≤ t'.card := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj1)
  have hj2' : j2 ≤ t'.card := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj2)
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have hk : ((j2 - j1 : ℕ) : ℤ) • y ∈ H := by
      have := H.neg_mem hdiff
      rw [← neg_zsmul, neg_sub] at this
      rwa [Nat.cast_sub hlt.le]
    rw [natCast_zsmul] at hk
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hlt) (le_trans (Nat.sub_le _ _) hj2')
    rw [hc, mul_comm, ← smul_smul]
    exact H.nsmul_mem hk c
  · have hk : ((j1 - j2 : ℕ) : ℤ) • y ∈ H := by rwa [Nat.cast_sub hlt.le]
    rw [natCast_zsmul] at hk
    obtain ⟨c, hc⟩ := Nat.dvd_factorial (Nat.sub_pos_of_lt hlt) (le_trans (Nat.sub_le _ _) hj1')
    rw [hc, mul_comm, ← smul_smul]
    exact H.nsmul_mem hk c

def LatLevel (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (S T : HSp D)
    (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)),
    IsSelfDualC S ΛS → IsSelfDualC T ΛT → ∀ f : WO S T → ℂ, IsThetaFunO ψ S T f →
      ∃ k : ℕ, 0 < k ∧ ∀ u ∈ latAll S T ΛS ΛT, heisO ψ S T (k • u) f = f

theorem latAll_inf (S T : HSp D) (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E))
    (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)) {u : WO S T} (hu : u ∈ latAll S T ΛS ΛT) :
    u.map (infPart D) = 0 := by
  induction hu using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, -, -, a, -, s, -, t, -, rfl⟩ := hx
    ext i j
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.zero_apply]
    show fstA D.host.F (pairA D.host.F 0 α) ⊗ₜ[D.host.F] _ = 0
    rw [show fstA D.host.F (pairA D.host.F 0 α) = 0 from rfl, TensorProduct.zero_tmul]
  | zero => ext i j; simp
  | add x y _ _ hx hy =>
    ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    have h2 : infPart D (y i j) = 0 := congrFun (congrFun hy i) j
    show infPart D (x i j + y i j) = 0
    rw [(infPart D).map_add, h1, h2, add_zero]
  | neg x _ hx =>
    ext i j
    have h1 : infPart D (x i j) = 0 := congrFun (congrFun hx i) j
    show infPart D (-x i j) = 0
    rw [(infPart D).map_neg, h1, neg_zero]

theorem latLevel_of (hL : LatSelfDual D) : LatLevel D := by
  intro ψ hψ S T ΛS ΛT hS hT f hf
  obtain ⟨U, hUo, hU⟩ := hf.level
  obtain ⟨hcpt, -, -, -⟩ := hL ψ hψ S T ΛS ΛT hS hT
  obtain ⟨m, hm, hmU⟩ := exists_nsmul_mem_cpt' _ hcpt (fun y hy n => AddSubgroup.nsmul_mem _ hy n) U hUo
  refine ⟨m, hm, fun u hu => hU _ (hmU u hu) ?_⟩
  have h0 := latAll_inf S T ΛS ΛT hu
  ext i j
  have h1 : infPart D (u i j) = 0 := congrFun (congrFun h0 i) j
  show infPart D ((m • u) i j) = 0
  rw [Matrix.smul_apply, nsmul_eq_mul, (infPart D).map_mul, h1, mul_zero]

end Formalism.IndefR.Fin

end
