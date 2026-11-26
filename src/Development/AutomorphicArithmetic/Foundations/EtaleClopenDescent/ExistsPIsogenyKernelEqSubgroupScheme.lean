module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.RepDataGeometricPointsOfSubData
public import Development.AutomorphicArithmetic.CommutativeAlgebra.SubDataPointsCorrespondRepData

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsIsPIsogIsTjOfSectionRepData
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

noncomputable section

namespace UpperTheory.QO.PullIsog

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem comp_eq_one_iff {S S' : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] {C C' : Over S'}
    [GrpObj C] [GrpObj C'] {f : S' ⟶ S} {u : C.left ⟶ A.left} {v : C'.left ⟶ A'.left}
    (hu : IsGrpPullback C A f u) (hv : IsGrpPullback C' A' f v) {g : A ⟶ A'} {g' : C ⟶ C'}
    (hg : g'.left ≫ v = u ≫ g.left) {T : Over S'} (x : T ⟶ C) :
    x ≫ g' = 1 ↔ pushHom hu T x ≫ g = 1 := by
  have hleftu : (pushHom hu T x).left = x.left ≫ u := rfl
  have hinj : Function.Injective (pushHom hv T) := by
    intro y z hyz
    apply Over.OverMorphism.ext
    apply hv.1.hom_ext
    · exact congrArg Over.Hom.left hyz
    · rw [Over.w y, Over.w z]
  have hpush : pushHom hv T (x ≫ g') = pushHom hu T x ≫ g := by
    apply Over.OverMorphism.ext
    show (x ≫ g').left ≫ v = (pushHom hu T x).left ≫ g.left
    rw [hleftu, Over.comp_left, Category.assoc, hg, Category.assoc]
  constructor
  · intro h1
    rw [← hpush, h1, map_one]
  · intro h1
    apply hinj
    rw [hpush, h1, map_one]

theorem exists_isPIsog_pull {c : ℕ} {T Y : Scheme.{0}} {s₁ : T ⟶ Sp R} {s : Y ⟶ Sp R} {t : T ⟶ Y}
    {o₁ o₁' : Obj b N s₁} {o o' : Obj b N s} (m : ObjMap o₁ o t) (m' : ObjMap o₁' o' t) {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) :
    ∃ ψ₁ : o₁.A ⟶ o₁'.A, m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ ∧ IsPIsog c o₁ o₁' ψ₁ := by
  obtain ⟨ψ', hq⟩ := h.exists_quasiInv
  obtain ⟨B₁, _, _, θ, ψ₁, ψ₁', _, hpb, hq₁, h1, h2⟩ :=
    GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback T Y t o.A o'.A c ψ ψ' o₁.A m.φ o'.ab hq m.cart
  obtain ⟨e, he, heθ⟩ := grpPullback_iso hpb m'.cart
  have hψ : m.φ ≫ ψ.left = (ψ₁ ≫ e.hom).left ≫ m'.φ := by
    rw [h1, ← heθ, Over.comp_left, Category.assoc]
  have hψ' : ∀ {W : Scheme} (k : o'.A.left ⟶ W), ψ₁.left ≫ e.hom.left ≫ m'.φ ≫ k = m.φ ≫ ψ.left ≫ k := by
    intro W k
    rw [← Category.assoc m.φ, hψ, Over.comp_left]
    simp only [Category.assoc]
  have hψ0 : ψ₁.left ≫ e.hom.left ≫ m'.φ = m.φ ≫ ψ.left := by
    rw [hψ, Over.comp_left, Category.assoc]
  have ext' : ∀ {Z : Over T} (f g : Z ⟶ o₁'.A), f.left ≫ m'.φ = g.left ≫ m'.φ → f = g :=
    fun f g hfg => Over.OverMorphism.ext (m'.cart.1.hom_ext hfg (by rw [Over.w f, Over.w g]))
  haveI := hq₁.1
  haveI := hq₁.2.1
  haveI := he
  refine ⟨ψ₁ ≫ e.hom, hψ, h.1, inferInstance, ?_, ?_, ?_, e.inv ≫ ψ₁', inferInstance, ?_, ?_⟩
  · intro c'
    apply ext'
    simp only [Over.comp_left, Category.assoc]
    rw [hψ0, m'.act c', hψ', ← Category.assoc (o₁.act.act c').left m.φ, m.act c', Category.assoc]
    congr 1
    have := congrArg Over.Hom.left (h.2.2.1 c')
    simpa only [Over.comp_left, Category.assoc] using this
  · intro y
    apply ext'
    simp only [Over.comp_left, Category.assoc]
    rw [hψ0, m'.eta y, ← Category.assoc (o₁.eta y).left m.φ, m.eta y, Category.assoc]
    congr 1
    have := congrArg Over.Hom.left (h.2.2.2.1 y)
    simpa only [Over.comp_left] using this
  · have hpow₁ : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hpull₁ : (o₁'.P.pull (sq2 (ψ₁ ≫ e.hom))).IsLB := pull_isLB o₁'.isLB _
    have e1 : GlobalTheory.CechPic.cls o₁.P o₁.isLB = GlobalTheory.CechPic.pull m.φ₂ (GlobalTheory.CechPic.cls o.P o.isLB) := by
      rw [← GlobalTheory.CechPic.cls_pull o.isLB m.φ₂ (pull_isLB o.isLB _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).mpr m.pol
    have e2 : GlobalTheory.CechPic.cls o₁'.P o₁'.isLB = GlobalTheory.CechPic.pull m'.φ₂ (GlobalTheory.CechPic.cls o'.P o'.isLB) := by
      rw [← GlobalTheory.CechPic.cls_pull o'.isLB m'.φ₂ (pull_isLB o'.isLB _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).mpr m'.pol
    obtain ⟨hpolψ⟩ := h.2.2.2.2.1
    have e3 : GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls o'.P o'.isLB) = c • GlobalTheory.CechPic.cls o.P o.isLB := by
      rw [← GlobalTheory.CechPic.cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _),
        ← GlobalTheory.LocTrivDescent.cls_lbPow_eq o.isLB c (LB.isLB_linComb o.isLB _ _)]
      exact ((GlobalTheory.CechPic.cls_eq_iff _ _).mpr hpolψ).symm
    have key : sq2 (ψ₁ ≫ e.hom) ≫ m'.φ₂ = m.φ₂ ≫ sq2 ψ := by
      apply pullback.hom_ext
      · change (sq2 (ψ₁ ≫ e.hom) ≫ m'.φ₂) ≫ (fst o'.A o'.A).left = (m.φ₂ ≫ sq2 ψ) ≫ (fst o'.A o'.A).left
        rw [Category.assoc, m'.sq.1, Category.assoc]
        simp only [sq2]
        rw [← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst, Over.comp_left,
          Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ0, ← Category.assoc,
          ← Category.assoc, m.sq.1]
      · change (sq2 (ψ₁ ≫ e.hom) ≫ m'.φ₂) ≫ (snd o'.A o'.A).left = (m.φ₂ ≫ sq2 ψ) ≫ (snd o'.A o'.A).left
        rw [Category.assoc, m'.sq.2, Category.assoc]
        simp only [sq2]
        rw [← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd, Over.comp_left,
          Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ0, ← Category.assoc,
          ← Category.assoc, m.sq.2]
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff hpow₁ hpull₁).mp ?_⟩
    rw [GlobalTheory.LocTrivDescent.cls_lbPow_eq o₁.isLB c hpow₁, GlobalTheory.CechPic.cls_pull o₁'.isLB _ hpull₁, e1, e2,
      ← GlobalTheory.CechPic.pull_comp, key, GlobalTheory.CechPic.pull_comp, e3, map_nsmul]
  · rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hq₁.2.2.1
  · rw [Category.assoc, ← Category.assoc ψ₁', hq₁.2.2.2, MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, Iso.inv_hom_id]

end UpperTheory.QO.PullIsog

open UpperTheory.QO.PullIsog in
theorem UpperTheory.exists_isPIsog_isTj_of_section_repData :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (σ : S ⟶ Rd.Y.left), σ ≫ Rd.Y.hom = 𝟙 S → ∃ (o'' : Obj b N s) (ψ'' : o.A ⟶ o''.A), IsPIsog c o o'' ψ'' ∧ IsTj r w j o o'' ψ'' ∧ ∀ (T : Over S) (a : T ⟶ o.A), ∃ a₀ : Over.mk (T.hom ≫ σ) ⟶ Rd.o₀.A, a₀.left ≫ Rd.m₀.φ = a.left ∧ (a ≫ ψ'' = 1 ↔ a₀ ≫ Rd.ψ = 1) ∧ ∀ v : Ideal (𝓞 D.F), KilledBy o v a ↔ KilledBy Rd.o₀ v a₀ := by
  intro p _ D R _ b N hN hNp r w j c S s o Rd σ hσ
  let idm : ObjMap o o (𝟙 S) :=
    { φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
      act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }
  obtain ⟨m', hm'⟩ := IsogRep.exists_factor hN hNp hσ Rd.m₀ idm
  have hs : σ ≫ Rd.Y.hom ≫ s = s := by rw [← Category.assoc, hσ, Category.id_comp]
  obtain ⟨o'', ⟨m''⟩⟩ := IsogRep.exists_pull σ Rd.o' hs
  obtain ⟨ψ'', hsq, hiso⟩ := exists_isPIsog_pull m' m'' Rd.isog
  refine ⟨o'', ψ'', hiso, ?_, fun T a => ?_⟩
  · exact (tjAt_id_iff r w j o o'' ψ'').1
      ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o Rd.o₀ m' o''.A Rd.o'.A m''.φ ψ'' Rd.ψ r w j m''.cart hsq).1
        fun k _ _ _ x _ => Rd.tj k x)
  · refine ⟨pushHom m'.cart T a, ?_, comp_eq_one_iff m'.cart m''.cart hsq.symm a, fun v => ?_⟩
    · change (a.left ≫ m'.φ) ≫ Rd.m₀.φ = a.left
      rw [Category.assoc, hm']
      exact Category.comp_id _
    · unfold GlobalTheory.UPel.HT.ES.KilledBy
      exact forall₂_congr fun x _ => comp_eq_one_iff m'.cart m'.cart (m'.act _) a
end
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsClopenSubgroupLocus
section -- merged from Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsMemUIdealIdempotentModPrimePow
open NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.ES

private theorem UpperTheory.Cb.idempotent_lift_succ_pow {R : Type*} [CommRing R] (σ : R →+* R) (P : R) (I : Ideal R) (k : ℕ)
    (a : R) (ha : a ∈ I) (h1 : P ^ (k + 1) ∣ a + σ a - 1) (h2 : P ^ (k + 1) ∣ a * σ a) :
    ∃ a' ∈ I, P ^ (k + 2) ∣ a' + σ a' - 1 ∧ P ^ (k + 2) ∣ a' * σ a' := by
  obtain ⟨c, hc⟩ := h1
  obtain ⟨d, hd⟩ := h2
  refine ⟨3 * a ^ 2 - 2 * a ^ 3, ?_, ?_, ?_⟩
  · have h3 : a ^ 2 * (3 - 2 * a) ∈ I := I.mul_mem_right _ (by
      rw [pow_two]
      exact I.mul_mem_left _ ha)
    have e : 3 * a ^ 2 - 2 * a ^ 3 = a ^ 2 * (3 - 2 * a) := by ring
    rw [e]
    exact h3
  · have e1 : 3 * a ^ 2 - 2 * a ^ 3 + σ (3 * a ^ 2 - 2 * a ^ 3) - 1 =
        -3 * (a + σ a - 1) ^ 2 - 2 * (a + σ a - 1) ^ 3 + 6 * (a * σ a) * (a + σ a - 1) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      ring
    rw [e1, hc, hd]
    exact ⟨P ^ k * (-3 * c ^ 2 - 2 * P ^ (k + 1) * c ^ 3 + 6 * d * c), by ring⟩
  · have e2 : (3 * a ^ 2 - 2 * a ^ 3) * σ (3 * a ^ 2 - 2 * a ^ 3) =
        (a * σ a) ^ 2 * ((3 - 2 * a) * (3 - 2 * σ a)) := by
      simp only [map_sub, map_mul, map_pow, map_ofNat]
      ring
    rw [e2, hd]
    exact ⟨P ^ k * d ^ 2 * ((3 - 2 * a) * (3 - 2 * σ a)), by ring⟩

private theorem UpperTheory.Cb.exists_idempotent_lift_pow {R : Type*} [CommRing R] (σ : R →+* R) (P : R) (I : Ideal R)
    (a : R) (ha : a ∈ I) (h1 : P ∣ a + σ a - 1) (h2 : P ∣ a * σ a) (k : ℕ) :
    ∃ a' ∈ I, P ^ (k + 1) ∣ a' + σ a' - 1 ∧ P ^ (k + 1) ∣ a' * σ a' := by
  induction k with
  | zero => exact ⟨a, ha, by simpa using h1, by simpa using h2⟩
  | succ k ih =>
    obtain ⟨b, hb, hb1, hb2⟩ := ih
    exact UpperTheory.Cb.idempotent_lift_succ_pow σ P I k b hb hb1 hb2

theorem UpperTheory.Cb.exists_mem_uIdeal_idempotent_mod_prime_pow :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (r : ℤ) (w : Ideal (𝓞 D.F)) (e : ℕ), w ≠ ⊤ → uIdeal D r ≤ w → ∃ a ∈ uIdeal D r, (p : 𝓞 D.F) ^ e ∣ a + D.bar a - 1 ∧ (p : 𝓞 D.F) ^ e ∣ a * D.bar a := by
  intro p _ D r w e hw hle
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp (Fact.out : p.Prime)
  set x : 𝓞 D.F := D.ω - (r : 𝓞 D.F) with hx
  set N : ℤ := r ^ 2 - D.tr * r + D.nm with hN
  set s : ℤ := D.tr - 2 * r with hs
  have hbx : D.bar x = D.bar D.ω - (r : 𝓞 D.F) := by
    simp [x, map_sub, map_intCast]
  have hxN : x * D.bar x = (N : 𝓞 D.F) := by
    rw [hbx]
    push_cast [N]
    linear_combination D.nm_eq - (r : 𝓞 D.F) * D.tr_eq
  have hxs : x + D.bar x = (s : 𝓞 D.F) := by
    rw [hbx]
    push_cast [s]
    linear_combination D.tr_eq
  have hpN : (p : ℤ) ∣ N := by
    by_contra hnd
    obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr hnd
    apply hw
    rw [Ideal.eq_top_iff_one]
    have hpw : ((p : ℤ) : 𝓞 D.F) ∈ w := by
      have := hle (p_mem_uIdeal D r)
      simpa using this
    have hNw : ((N : ℤ) : 𝓞 D.F) ∈ w := by
      rw [← hxN]
      exact w.mul_mem_right _ (hle (sub_mem_uIdeal D r))
    have h1 : ((u * p + v * N : ℤ) : 𝓞 D.F) ∈ w := by
      push_cast
      exact w.add_mem (w.mul_mem_left _ (by simpa using hpw)) (w.mul_mem_left _ hNw)
    rw [huv] at h1
    simpa using h1
  have hps : ¬ (p : ℤ) ∣ s := by
    intro hd
    apply D.disc_p
    have e : D.tr ^ 2 - 4 * D.nm = s ^ 2 - 4 * N := by
      simp only [s, N]
      ring
    rw [e]
    exact dvd_sub (dvd_pow hd two_ne_zero) (dvd_mul_of_dvd_right hpN 4)
  obtain ⟨u, v, huv⟩ := (Irreducible.coprime_iff_not_dvd hp.irreducible).mpr hps
  obtain ⟨N', hN'⟩ := hpN
  have ha : (v : 𝓞 D.F) * x ∈ uIdeal D r := (uIdeal D r).mul_mem_left _ (sub_mem_uIdeal D r)
  have h1 : (p : 𝓞 D.F) ∣ (v : 𝓞 D.F) * x + D.bar ((v : 𝓞 D.F) * x) - 1 := by
    refine ⟨-(u : 𝓞 D.F), ?_⟩
    rw [map_mul, map_intCast]
    have e : (v : 𝓞 D.F) * x + (v : 𝓞 D.F) * D.bar x - 1 = (v : 𝓞 D.F) * (x + D.bar x) - 1 := by ring
    rw [e, hxs]
    have huv' : ((u * p + v * s : ℤ) : 𝓞 D.F) = 1 := by rw [huv]; simp
    push_cast at huv'
    linear_combination huv'
  have h2 : (p : 𝓞 D.F) ∣ (v : 𝓞 D.F) * x * D.bar ((v : 𝓞 D.F) * x) := by
    refine ⟨(v : 𝓞 D.F) ^ 2 * (N' : 𝓞 D.F), ?_⟩
    rw [map_mul, map_intCast]
    have e : (v : 𝓞 D.F) * x * ((v : 𝓞 D.F) * D.bar x) = (v : 𝓞 D.F) ^ 2 * (x * D.bar x) := by ring
    rw [e, hxN, hN']
    push_cast
    ring
  obtain ⟨a', ha', h1', h2'⟩ := UpperTheory.Cb.exists_idempotent_lift_pow (D.bar : 𝓞 D.F →+* 𝓞 D.F) (p : 𝓞 D.F)
    (uIdeal D r) _ ha (by simpa using h1) (by simpa using h2) e
  refine ⟨a', ha', ?_, ?_⟩
  · exact (pow_dvd_pow _ (Nat.le_succ e)).trans (by simpa using h1')
  · exact (pow_dvd_pow _ (Nat.le_succ e)).trans (by simpa using h2')
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

section ring
variable {p : ℕ} [Fact p.Prime] {D : Datum p}

private theorem mul_bar_eq (r : ℤ) (w : Ideal (𝓞 D.F)) (hw : w ≠ ⊤) (hu : uIdeal D r ≤ w) :
    ∃ z : 𝓞 D.F, (D.ω - (r : 𝓞 D.F)) * (D.bar D.ω - (r : 𝓞 D.F)) = (p : 𝓞 D.F) * z := by
  have htr := D.tr_eq
  have hnm := D.nm_eq
  have hp : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 Fact.out
  have e1 : ((r ^ 2 - D.tr * r + D.nm : ℤ) : 𝓞 D.F) = (D.ω - r) * (D.bar D.ω - r) := by
    push_cast
    linear_combination r * htr - hnm
  have hcw : ((r ^ 2 - D.tr * r + D.nm : ℤ) : 𝓞 D.F) ∈ w := by
    rw [e1]
    exact w.mul_mem_right (D.bar D.ω - r) (hu (sub_mem_uIdeal D r))
  have hpc : (p : ℤ) ∣ r ^ 2 - D.tr * r + D.nm := by
    by_contra hnd
    obtain ⟨x, y, hxy⟩ := hp.coprime_iff_not_dvd.2 hnd
    refine hw ((Ideal.eq_top_iff_one w).2 ?_)
    have h := congrArg (Int.cast : ℤ → 𝓞 D.F) hxy
    rw [Int.cast_add, Int.cast_mul, Int.cast_mul, Int.cast_one, Int.cast_natCast] at h
    rw [← h]
    exact w.add_mem (w.mul_mem_left _ (hu (p_mem_uIdeal D r))) (w.mul_mem_left _ hcw)
  obtain ⟨z, hz⟩ := hpc
  refine ⟨z, ?_⟩
  rw [← e1, hz]
  push_cast
  rfl

private theorem uIdeal_pow_le (r : ℤ) (w : Ideal (𝓞 D.F)) (hw : w ≠ ⊤) (hu : uIdeal D r ≤ w) (e : ℕ)
    (ε : 𝓞 D.F) (hε : ε ∈ uIdeal D r) (h1 : (p : 𝓞 D.F) ^ e ∣ ε + D.bar ε - 1) :
    uIdeal D r ^ e ≤ Ideal.span {(p : 𝓞 D.F) ^ e, ε} := by
  set I := Ideal.span {(p : 𝓞 D.F) ^ e, ε} with hI
  let π := Ideal.Quotient.mk I
  have hpe : π ((p : 𝓞 D.F) ^ e) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_insert _ _))
  have hε0 : π ε = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.subset_span (Set.mem_insert_of_mem _ rfl))
  have hbar1 : π (D.bar ε) = 1 := by
    obtain ⟨d, hd⟩ := h1
    have e0 : D.bar ε = 1 + (p : 𝓞 D.F) ^ e * d - ε := by linear_combination hd
    rw [e0, map_sub, map_add (f := _), map_mul, hpe, hε0, map_one]
    ring
  obtain ⟨x, y, hxy⟩ := Ideal.mem_span_pair.1 hε
  obtain ⟨z, hz⟩ := mul_bar_eq r w hw hu
  have hb : D.bar ε = D.bar x * (p : 𝓞 D.F) + D.bar y * (D.bar D.ω - (r : 𝓞 D.F)) := by
    rw [← hxy]
    simp only [map_add (f := _), map_mul, map_sub, map_natCast, map_intCast]
  have hkey : π (D.ω - (r : 𝓞 D.F)) ∈ Ideal.span {π (p : 𝓞 D.F)} := by
    refine Ideal.mem_span_singleton'.2 ⟨π (D.bar x * (D.ω - (r : 𝓞 D.F)) + D.bar y * z), ?_⟩
    have e2 : (D.bar x * (D.ω - (r : 𝓞 D.F)) + D.bar y * z) * (p : 𝓞 D.F)
        = (D.ω - (r : 𝓞 D.F)) * D.bar ε := by
      rw [hb]
      linear_combination (-D.bar y) * hz
    rw [← map_mul, e2, map_mul, hbar1, _root_.mul_one]
  have hle : Ideal.map π (uIdeal D r) ≤ Ideal.span {π (p : 𝓞 D.F)} := by
    rw [uIdeal, Ideal.map_span, Ideal.span_le]
    rintro _ ⟨a, ha, rfl⟩
    rcases ha with rfl | rfl
    · exact Ideal.subset_span rfl
    · exact hkey
  intro u hu'
  rw [← Ideal.Quotient.eq_zero_iff_mem]
  have h2 : π u ∈ Ideal.span {π (p : 𝓞 D.F)} ^ e :=
    Ideal.pow_right_mono hle e (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hu')
  rw [Ideal.span_singleton_pow, ← map_pow, hpe] at h2
  simpa using h2

private theorem mem_of_pow_mem (I : Ideal (𝓞 D.F)) (e : ℕ) (ε : 𝓞 D.F) (hc : (p : 𝓞 D.F) ^ e ∈ I)
    (h1 : (p : 𝓞 D.F) ^ e ∣ ε + D.bar ε - 1) (h2 : (p : 𝓞 D.F) ^ e ∣ ε * D.bar ε) (k : ℕ)
    (hk : ε ^ (k + 1) ∈ I) : ε ∈ I := by
  have hq : ε ^ 2 - ε ∈ I := by
    obtain ⟨d, hd⟩ := h1
    obtain ⟨f, hf⟩ := h2
    have e0 : ε ^ 2 - ε = (p : 𝓞 D.F) ^ e * (ε * d - f) := by linear_combination ε * hd - hf
    rw [e0]
    exact I.mul_mem_right _ hc
  induction k with
  | zero => simpa using hk
  | succ k ih =>
    refine ih ?_
    have e1 : ε ^ (k + 1) = ε ^ (k + 1 + 1) - ε ^ k * (ε ^ 2 - ε) := by ring
    rw [e1]
    exact I.sub_mem hk (I.mul_mem_left _ hq)
end ring

section pts
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
  {S : Scheme.{0}} {s : S ⟶ Sp R}

private def ann (o : Obj b N s) {T : Over S} (g : T ⟶ o.A) : Ideal (𝓞 D.F) where
  carrier := {x | g ≫ o.act.act (algebraMap (𝓞 D.F) D.O x) = 1}
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq] at hx hy ⊢
    rw [map_add (f := _), o.act.add, MonObj.comp_mul, hx, hy, _root_.mul_one]
  zero_mem' := by
    have h := o.act.add 0 0
    rw [add_zero] at h
    have h0 : o.act.act 0 = 1 := left_eq_mul.1 h
    simp only [Set.mem_setOf_eq]
    rw [map_zero, h0, MonObj.comp_one]
  smul_mem' := by
    intro y x hx
    simp only [Set.mem_setOf_eq] at hx ⊢
    have := o.act.hom (algebraMap (𝓞 D.F) D.O y)
    rw [smul_eq_mul, map_mul, o.act.mul, ← Category.assoc, hx, MonObj.one_comp]

private theorem mem_ann {o : Obj b N s} {T : Over S} (g : T ⟶ o.A) (x : 𝓞 D.F) :
    x ∈ ann o g ↔ g ≫ o.act.act (algebraMap (𝓞 D.F) D.O x) = 1 := Iff.rfl

private theorem killedBy_iff {o : Obj b N s} {T : Over S} (g : T ⟶ o.A) (v : Ideal (𝓞 D.F)) :
    KilledBy o v g ↔ v ≤ ann o g := Iff.rfl

private theorem act_natCast (o : Obj b N s) (n : ℕ) :
    o.act.act (algebraMap (𝓞 D.F) D.O (n : 𝓞 D.F)) = (𝟙 o.A) ^ n := by
  induction n with
  | zero =>
    have h := o.act.add 0 0
    rw [add_zero] at h
    have h0 : o.act.act 0 = 1 := left_eq_mul.1 h
    rw [Nat.cast_zero, map_zero, h0, pow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, map_add (f := _), o.act.add, ih, map_one, o.act.one, pow_succ]

private theorem natCast_mem_ann {o : Obj b N s} {T : Over S} (g : T ⟶ o.A) (n : ℕ) :
    (n : 𝓞 D.F) ∈ ann o g ↔ g ^ n = 1 := by
  rw [mem_ann, act_natCast, MonObj.comp_pow, Category.comp_id]

private theorem eq_one_of_rank_one {K A T : Over S} [GrpObj K] [GrpObj A] (i : K ⟶ A) [IsMonHom i]
    (h : IsIsogDeg (toUnit K) 1) (y : T ⟶ K) : y ≫ i = 1 := by
  have := h.fin
  have := h.flat
  have hiso : IsIso (toUnit K).left := by
    rw [Scheme.Hom.isIso_iff_finrank_eq]
    funext z
    exact h.rank z
  have : IsIso ((Over.forget S).map (toUnit K)) := hiso
  have : IsIso (toUnit K) := isIso_of_reflects_iso _ (Over.forget S)
  have hy : y = 1 := by
    rw [← cancel_mono (toUnit K)]
    exact toUnit_unique _ _
  rw [hy, MonObj.one_comp]

private theorem ann_push {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s} (Rd : RepData b N r w j c s o)
    {T₀ : Over Rd.Y.left} (a₀ : T₀ ⟶ Rd.o₀.A) :
    ann Rd.o₀ a₀ = ann o (pushHom Rd.m₀.cart T₀ a₀) := by
  ext x
  exact GlobalTheory.IwLevel.comp_eq_one_iff_push Rd.m₀.cart Rd.m₀.cart (Rd.m₀.act _) a₀

private theorem tors_of_ker {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s} (Rd : RepData b N r w j c s o)
    {T₀ : Over Rd.Y.left} (a₀ : T₀ ⟶ Rd.o₀.A) (h : a₀ ≫ Rd.ψ = 1) : a₀ ^ c = 1 := by
  obtain ⟨-, -, -, -, -, ψ', hψ', h1, -⟩ := Rd.isog
  have h2 : a₀ ≫ (𝟙 Rd.o₀.A) ^ c = 1 := by
    rw [← h1, ← Category.assoc, h, MonObj.one_comp]
  rwa [MonObj.comp_pow, Category.comp_id] at h2

private theorem tors_of_sub {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s}
    (hu : uIdeal D r ≤ w) (hc : ∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) (Sd : SubData w j o)
    {T : Over S} (x : T ⟶ o.A) (hx : InSub Sd.i x) : (c : 𝓞 D.F) ∈ ann o x := by
  obtain ⟨e, rfl, he⟩ := hc
  rcases Nat.eq_zero_or_pos e with rfl | he0
  · have hj : j = 0 := by
      by_contra hj
      exact absurd (he (Nat.pos_of_ne_zero hj)) (lt_irrefl 0)
    subst hj
    have hdeg := Sd.deg
    rw [pow_zero] at hdeg
    obtain ⟨y, rfl⟩ := hx
    have := Sd.hom
    rw [natCast_mem_ann, eq_one_of_rank_one Sd.i hdeg y, one_pow]
  · have hp : (p : 𝓞 D.F) ∈ ann o x := Sd.killed T x hx _ (hu (p_mem_uIdeal D r))
    rw [Nat.cast_pow]
    exact Ideal.pow_mem_of_mem _ hp e he0

private theorem core_fwd {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s} (Rd : RepData b N r w j c s o)
    (Sd : SubData w j o) (hu : uIdeal D r ≤ w) (hc : ∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) (e : ℕ)
    (hce : c = p ^ e) (ε : 𝓞 D.F) (hε : ε ∈ uIdeal D r) (h1 : (p : 𝓞 D.F) ^ e ∣ ε + D.bar ε - 1)
    (h2 : (p : 𝓞 D.F) ^ e ∣ ε * D.bar ε) {T₀ : Over Rd.Y.left} (a₀ : T₀ ⟶ Rd.o₀.A)
    (H₁ : a₀ ^ c = 1 → a₀ ≫ Rd.ψ = 1 → a₀ ≫ Rd.o₀.act.act (algebraMap (𝓞 D.F) D.O ε) = 1 →
      InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀))
    (H₂ : a₀ ^ c = 1 → InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀) → a₀ ≫ Rd.ψ = 1) :
    (a₀ ≫ Rd.ψ = 1 ∧ ∃ e : ℕ, KilledBy Rd.o₀ (uIdeal D r ^ e) a₀) ↔
      InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀) := by
  constructor
  · rintro ⟨hψ, e', hk⟩
    have hcT := tors_of_ker Rd a₀ hψ
    have hcm : (p : 𝓞 D.F) ^ e ∈ ann Rd.o₀ a₀ := by
      have h3 := (natCast_mem_ann a₀ c).2 hcT
      have ec : (c : 𝓞 D.F) = (p : 𝓞 D.F) ^ e := by rw [hce, Nat.cast_pow]
      rwa [ec] at h3
    refine H₁ hcT hψ (mem_of_pow_mem (ann Rd.o₀ a₀) e ε hcm h1 h2 e' (hk _ ?_))
    rw [pow_succ]
    exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow hε e')
  · intro hs
    have hcm := tors_of_sub hu hc Sd _ hs
    rw [← ann_push] at hcm
    have hcT := (natCast_mem_ann a₀ c).1 hcm
    refine ⟨H₂ hcT hs, 1, ?_⟩
    rw [killedBy_iff, ann_push, pow_one]
    exact fun x hx => Sd.killed _ _ hs _ (hu hx)

private theorem core_bwd {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s} (Rd : RepData b N r w j c s o)
    (Sd : SubData w j o) (hw : w ≠ ⊤) (hu : uIdeal D r ≤ w) (e : ℕ)
    (hce : c = p ^ e) (ε : 𝓞 D.F) (hε : ε ∈ uIdeal D r) (h1 : (p : 𝓞 D.F) ^ e ∣ ε + D.bar ε - 1)
    {T₀ : Over Rd.Y.left} (a₀ : T₀ ⟶ Rd.o₀.A)
    (H : (a₀ ≫ Rd.ψ = 1 ∧ ∃ e : ℕ, KilledBy Rd.o₀ (uIdeal D r ^ e) a₀) ↔
      InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀)) :
    (a₀ ^ c = 1 → a₀ ≫ Rd.ψ = 1 → a₀ ≫ Rd.o₀.act.act (algebraMap (𝓞 D.F) D.O ε) = 1 →
      InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀)) ∧
    (InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀) → a₀ ≫ Rd.ψ = 1) := by
  refine ⟨fun hcT hψ hεa => H.1 ⟨hψ, e, ?_⟩, fun hs => (H.2 hs).1⟩
  have hcm : (p : 𝓞 D.F) ^ e ∈ ann Rd.o₀ a₀ := by
    have h3 := (natCast_mem_ann a₀ c).2 hcT
    have ec : (c : 𝓞 D.F) = (p : 𝓞 D.F) ^ e := by rw [hce, Nat.cast_pow]
    rwa [ec] at h3
  rw [killedBy_iff]
  refine (uIdeal_pow_le r w hw hu e ε hε h1).trans ?_
  rw [Ideal.span_le]
  rintro x (rfl | rfl)
  · exact hcm
  · exact hεa

private theorem two_locus (Y : Scheme.{0}) (A B₁ B₂ B' : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B₁] [GrpObj B₂]
    [GrpObj B'] (n : ℕ) (f₁ : A ⟶ B₁) (f₂ : A ⟶ B₂) (f' : A ⟶ B') (hA : IsAbelianScheme A)
    (h₁ : IsAbelianScheme B₁) (h₂ : IsAbelianScheme B₂) (h' : IsAbelianScheme B') [IsMonHom f₁] [IsMonHom f₂]
    [IsMonHom f'] (hn : IsUnit (n : Γ(Y, ⊤))) :
    ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧
      (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W → ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom →
        ∀ a : T ⟶ A, a ^ n = 1 → a ≫ f₁ = 1 → a ≫ f₂ = 1 → a ≫ f' = 1) ∧
      ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y), Set.range x.base ⊆ W ↔
        ∀ a : Over.mk x ⟶ A, a ^ n = 1 → a ≫ f₁ = 1 → a ≫ f₂ = 1 → a ≫ f' = 1 := by
  let Bf : Bool → Over Y := fun i => match i with
    | false => B₁
    | true => B₂
  letI gB : ∀ i, GrpObj (Bf i) := fun i => match i with
    | false => inferInstanceAs (GrpObj B₁)
    | true => inferInstanceAs (GrpObj B₂)
  let ff : ∀ i, A ⟶ Bf i := fun i => match i with
    | false => f₁
    | true => f₂
  obtain ⟨W, o, c, H, G⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y A n Bool Bf ff B' f' hA
    (fun i => match i with
      | false => h₁
      | true => h₂) h'
    (fun i => match i with
      | false => inferInstanceAs (IsMonHom f₁)
      | true => inferInstanceAs (IsMonHom f₂)) inferInstance hn
  have key : ∀ {T : Over Y} (a : T ⟶ A), (∀ i, a ≫ ff i = 1) ↔ (a ≫ f₁ = 1 ∧ a ≫ f₂ = 1) := fun a =>
    ⟨fun h => ⟨h false, h true⟩, fun h i => match i with
      | false => h.1
      | true => h.2⟩
  refine ⟨W, o, c, fun Tb t hW T σ hσ a ha g₁ g₂ => (H Tb t).1 hW T σ hσ a ha ((key a).2 ⟨g₁, g₂⟩),
    fun k _ _ x => (G k x).trans ?_⟩
  exact ⟨fun h a ha g₁ g₂ => h a ha ((key a).2 ⟨g₁, g₂⟩), fun h a ha g => h a ha ((key a).1 g).1 ((key a).1 g).2⟩

private theorem insub_push {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {o : Obj b N s} (Rd : RepData b N r w j c s o)
    (Sd : SubData w j o) (Tl : Scheme.{0}) (Th : Tl ⟶ S) (u : Tl ⟶ Rd.Y.left) (a₀ : Over.mk u ⟶ Rd.o₀.A)
    (a : Over.mk Th ⟶ o.A) (ha : a₀.left ≫ Rd.m₀.φ = a.left) :
    InSub Sd.i a ↔ InSub Sd.i (pushHom Rd.m₀.cart (Over.mk u) a₀) := by
  have hT : Th = u ≫ Rd.Y.hom := by
    have h₁ : a.left ≫ o.A.hom = Th := Over.w a
    have h₂ : a₀.left ≫ Rd.o₀.A.hom = u := Over.w a₀
    rw [← h₁, ← ha, Category.assoc, Rd.m₀.cart.1.w, ← Category.assoc, h₂]
  subst hT
  have ea : a = pushHom Rd.m₀.cart (Over.mk u) a₀ := Over.OverMorphism.ext ha.symm
  rw [ea]
end pts

section quot
open scoped CategoryTheory.Obj
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem exists_quot {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} {S : Scheme.{0}} [IsLocallyNoetherian S]
    {s : S ⟶ Sp R} {o : Obj b N s} (Rd : RepData b N r w j c s o) (Sd : SubData w j o) :
    ∃ (B₀ : Over Rd.Y.left) (_ : GrpObj B₀) (q₀ : Rd.o₀.A ⟶ B₀), IsAbelianScheme B₀ ∧ IsMonHom q₀ ∧
      ∀ {T₀ : Over Rd.Y.left} (a₀ : T₀ ⟶ Rd.o₀.A), a₀ ≫ q₀ = 1 ↔ InSub Sd.i (pushHom Rd.m₀.cart T₀ a₀) := by
  have hfin := Sd.fin
  have het := Sd.et
  have hflat : Flat Sd.K.hom := inferInstance
  have hSm := Sd.mono
  have hSh := Sd.hom
  obtain ⟨B, _, q, hab, hqm, -, -, -, hq⟩ :=
    GlobalTheory.IwLevel.quotGlobal_holds S o.A Sd.K Sd.i o.ab Sd.hom Sd.mono Sd.fin hflat
  have hker := GlobalTheory.UPel.HT.ES.IsogDVR.isPullback_kernel_of_kernelPair Sd.i q hq
  have hsub : ∀ {T : Over S} (x : T ⟶ o.A), x ≫ q = 1 ↔ InSub Sd.i x := by
    intro T x
    constructor
    · intro h
      exact ⟨hker.lift x (toUnit T) (by rw [h, Hom.one_def]), hker.lift_fst _ _ _⟩
    · rintro ⟨y, rfl⟩
      rw [Category.assoc, hker.w, ← Category.assoc, toUnit_unique (y ≫ toUnit _) (toUnit T), Hom.one_def]
  have := hab.comm
  have hP := isGrpPullback_pullback B Rd.Y.hom
  obtain ⟨e₀, he₀m, he₀⟩ := grpPullback_iso Rd.m₀.cart (isGrpPullback_pullback o.A Rd.Y.hom)
  let q₀ : Rd.o₀.A ⟶ (Over.pullback Rd.Y.hom).obj B := e₀.hom ≫ (Over.pullback Rd.Y.hom).map q
  have hq₀m : IsMonHom q₀ := by
    have := he₀m
    infer_instance
  have hsq : q₀.left ≫ pullback.fst B.hom Rd.Y.hom = Rd.m₀.φ ≫ q.left := by
    have h3 : ((Over.pullback Rd.Y.hom).map q).left ≫ pullback.fst B.hom Rd.Y.hom =
        pullback.fst o.A.hom Rd.Y.hom ≫ q.left := pullback.lift_fst _ _ _
    rw [Over.comp_left, Category.assoc, h3, ← Category.assoc, he₀]
  exact ⟨_, inferInstance, q₀, GlobalTheory.isAbelianScheme_pullback_obj _ _ hab, hq₀m, fun a₀ =>
    (GlobalTheory.IwLevel.comp_eq_one_iff_push Rd.m₀.cart hP hsq a₀).trans (hsub _)⟩
end quot

theorem UpperTheory.exists_clopen_subgroup_locus :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), IsUnit ((p : ℕ) : R) → w.IsMaximal → uIdeal D r ≤ w → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (Sd : SubData w j o), ∃ W : Set Rd.Y.left, IsOpen W ∧ IsClosed W ∧ (∀ (Tb : Scheme.{0}) (t : Tb ⟶ Rd.Y.left), Set.range t.base ⊆ W → KerAt Rd Sd t) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (y : Sp k ⟶ Rd.Y.left), Set.range y.base ⊆ W ↔ KerGeo Rd Sd y := by
  intro p _ D R _ b N r w j c hp hw hu hc S _ s o Rd Sd
  obtain ⟨e, hce, -⟩ := id hc
  have hwt : w ≠ ⊤ := hw.ne_top
  obtain ⟨ε, hε, h1, h2⟩ := UpperTheory.Cb.exists_mem_uIdeal_idempotent_mod_prime_pow p D r w e hwt hu
  obtain ⟨B₀, _, q₀, hB₀, hq₀m, hqp⟩ := exists_quot Rd Sd
  have hcu : IsUnit ((c : ℕ) : Γ(Rd.Y.left, ⊤)) := by
    have h3 := hp.map (gam (Rd.Y.hom ≫ s))
    rw [map_natCast] at h3
    have ec : ((c : ℕ) : Γ(Rd.Y.left, ⊤)) = ((p : ℕ) : Γ(Rd.Y.left, ⊤)) ^ e :=
      (congrArg Nat.cast hce).trans (Nat.cast_pow p e)
    rw [ec]
    exact h3.pow _
  have hψm : IsMonHom Rd.ψ := Rd.isog.2.1
  have hεm := Rd.o₀.act.hom (algebraMap (𝓞 D.F) D.O ε)
  obtain ⟨W₁, o₁, c₁, H₁, G₁⟩ := two_locus Rd.Y.left Rd.o₀.A Rd.o'.A Rd.o₀.A B₀ c Rd.ψ
    (Rd.o₀.act.act (algebraMap (𝓞 D.F) D.O ε)) q₀ Rd.o₀.ab Rd.o'.ab Rd.o₀.ab hB₀ hcu
  obtain ⟨W₂, o₂, c₂, H₂, G₂⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Rd.Y.left Rd.o₀.A c Unit (fun _ => B₀)
    (fun _ => q₀) Rd.o'.A Rd.ψ Rd.o₀.ab (fun _ => hB₀) Rd.o'.ab (fun _ => hq₀m) hψm hcu
  refine ⟨W₁ ∩ W₂, o₁.inter o₂, c₁.inter c₂, fun Tb t hW => ?_, fun k _ _ y => ?_⟩
  · have hW₁ := H₁ Tb t (hW.trans Set.inter_subset_left)
    have hW₂ := (H₂ Tb t).1 (hW.trans Set.inter_subset_right)
    intro T τ a₀ a ha
    exact (core_fwd Rd Sd hu hc e hce ε hε h1 h2 a₀
      (fun hcT hψ hεa => (hqp a₀).1 (hW₁ _ τ rfl a₀ hcT hψ hεa))
      (fun hcT hs => hW₂ _ τ rfl a₀ hcT (fun _ => (hqp a₀).2 hs))).trans
      (insub_push Rd Sd T.left T.hom (τ ≫ t) a₀ a ha).symm
  · rw [Set.subset_inter_iff, G₁, G₂]
    constructor
    · rintro ⟨g₁, g₂⟩ a₀ a ha
      have ea : a = pushHom Rd.m₀.cart (Over.mk y) a₀ := Over.OverMorphism.ext ha.symm
      subst ea
      exact core_fwd Rd Sd hu hc e hce ε hε h1 h2 a₀
        (fun hcT hψ hεa => (hqp a₀).1 (g₁ a₀ hcT hψ hεa))
        (fun hcT hs => g₂ a₀ hcT (fun _ => (hqp a₀).2 hs))
    · intro H
      refine ⟨fun a₀ hcT hψ hεa => ?_, fun a₀ hcT g => ?_⟩
      · exact (hqp a₀).2 ((core_bwd Rd Sd hwt hu e hce ε hε h1 a₀ (H a₀ _ rfl)).1 hcT hψ hεa)
      · exact (core_bwd Rd Sd hwt hu e hce ε hε h1 a₀ (H a₀ _ rfl)).2 ((hqp a₀).1 (g ()))
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsSectionOfEtaleClopenGeomPointUnique
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

theorem UpperTheory.exists_section_of_etale_clopen_geomPoint_unique :
    ∀ (S : Scheme.{0}) (Y : Over S), IsFinite Y.hom → Etale Y.hom → ∀ (W : Set Y.left), IsOpen W → IsClosed W → (∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S), ∃ y : Sp k ⟶ Y.left, y ≫ Y.hom = x ∧ Set.range y.base ⊆ W) → (∀ (k : Type) [Field k] [IsAlgClosed k] (y₁ y₂ : Sp k ⟶ Y.left), y₁ ≫ Y.hom = y₂ ≫ Y.hom → Set.range y₁.base ⊆ W → Set.range y₂.base ⊆ W → y₁ = y₂) → ∃ σ : S ⟶ Y.left, σ ≫ Y.hom = 𝟙 S ∧ Set.range σ.base ⊆ W := by
  intro S Y hfin het W hWo hWc hex huniq
  let U : Y.left.Opens := ⟨W, hWo⟩
  have hrange : Set.range U.ι.base = W := U.range_ι
  haveI : IsClosedImmersion U.ι :=
    IsClosedImmersion.of_isPreimmersion _ (by rw [hrange]; exact hWc)
  haveI : IsFinite (U.ι ≫ Y.hom) := inferInstance
  haveI : Etale (U.ι ≫ Y.hom) := inferInstance
  have hiso : IsIso (U.ι ≫ Y.hom) := by
    rw [GlobalTheory.FinEt.isIso_iff_bijective_algClosed]
    intro k _ _
    constructor
    · intro z₁ z₂ h
      apply (cancel_mono U.ι).mp
      apply huniq k (z₁ ≫ U.ι) (z₂ ≫ U.ι)
      · simpa [Category.assoc] using h
      · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange.symm]
        exact Set.image_subset_range _ _
      · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hrange.symm]
        exact Set.image_subset_range _ _
    · intro x
      obtain ⟨y, hy, hyW⟩ := hex k x
      refine ⟨IsOpenImmersion.lift U.ι y (by rw [hrange]; exact hyW), ?_⟩
      simp only
      rw [← Category.assoc, IsOpenImmersion.lift_fac, hy]
  refine ⟨inv (U.ι ≫ Y.hom) ≫ U.ι, ?_, ?_⟩
  · rw [Category.assoc, IsIso.inv_hom_id]
  · rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, ← hrange]
    exact Set.image_subset_range _ _
end

section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsNoetherianBaseLink
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

namespace UpperTheory.BaseNoeth

private theorem exists_ratHom {A : Type} [CommRing A] (h : ∀ k : ℕ, k ≠ 0 → IsUnit (k : A)) :
    Nonempty (ℚ →+* A) := by
  have hu : ∀ y : nonZeroDivisors ℤ, IsUnit (Int.castRingHom A y) := by
    rintro ⟨y, hy⟩
    have hy0 : y ≠ 0 := nonZeroDivisors.ne_zero hy
    have hn := h y.natAbs (Int.natAbs_ne_zero.mpr hy0)
    rcases Int.natAbs_eq y with e | e
    · have : Int.castRingHom A y = (y.natAbs : A) := by
        conv_lhs => rw [e]
        simp
      simpa [this] using hn
    · have : Int.castRingHom A y = -(y.natAbs : A) := by
        conv_lhs => rw [e]
        simp
      simpa [this] using hn.neg
  exact ⟨IsLocalization.lift (M := nonZeroDivisors ℤ) (S := ℚ) hu⟩

variable {p : ℕ} [Fact p.Prime]

private theorem units_of {A : Type} [CommRing A] (hp : IsUnit ((p : ℕ) : A))
    (hu : ∀ k : ℕ, k.Coprime p → IsUnit (k : A)) (k : ℕ) (hk : k ≠ 0) : IsUnit (k : A) := by
  have pp : p.Prime := Fact.out
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hk p pp.ne_one
  have hcop : m.Coprime p := ((Nat.Prime.coprime_iff_not_dvd pp).mpr hm).symm
  rw [Nat.cast_mul, Nat.cast_pow]
  exact (hp.pow e).mul (hu m hcop)

private theorem core (D : Datum p) {A : Type} [CommRing A] (hp : IsUnit ((p : ℕ) : A))
    (hu : ∀ k : ℕ, k.Coprime p → IsUnit (k : A)) (ρ : A) (hρ : ρ ^ 2 - D.tr * ρ + D.nm = 0)
    (t : Fin D.a → (𝓞 D.F →+* A)) (hω : ∀ i, t i D.ω = ρ)
    (hc : ∀ i j, i ≠ j → Ideal.span (Set.range fun x => t i x - t j x) = ⊤) :
    ∃ (R₁ : Subring A) (_ : IsNoetherianRing R₁) (b₁ : Base D R₁), IsUnit ((p : ℕ) : R₁) ∧
      ((b₁.ρ : R₁) : A) = ρ ∧ ∀ i c, ((b₁.t i c : R₁) : A) = t i c := by
  classical
  obtain ⟨f⟩ := exists_ratHom (units_of hp hu)
  letI : Algebra ℚ A := f.toAlgebra

  obtain ⟨G, hG⟩ := (Module.Finite.fg_top : (⊤ : Submodule ℤ (𝓞 D.F)).FG)

  have hw : ∀ ij : Fin D.a × Fin D.a, ∃ c : 𝓞 D.F →₀ A, ij.1 ≠ ij.2 →
      (c.sum fun x a => a * (t ij.1 x - t ij.2 x)) = 1 := by
    rintro ⟨i, j⟩
    by_cases hij : i = j
    · exact ⟨0, fun h => absurd hij h⟩
    · have h1 : (1 : A) ∈ Ideal.span (Set.range fun x => t i x - t j x) := by
        rw [hc i j hij]; trivial
      obtain ⟨c, hc'⟩ := (Finsupp.mem_ideal_span_range_iff_exists_finsupp).mp h1
      exact ⟨c, fun _ => hc'⟩
  choose w hw using hw

  let T : Finset A := insert ρ ((Finset.univ.biUnion fun i : Fin D.a => G.image (t i)) ∪
    (Finset.univ.biUnion fun ij : Fin D.a × Fin D.a => (w ij).support.image (w ij)))
  let B : Subalgebra ℚ A := Algebra.adjoin ℚ (T : Set A)
  have hfg : B.FG := Subalgebra.fg_adjoin_finset T
  haveI : Algebra.FiniteType ℚ B := (Subalgebra.fg_iff_finiteType B).mp hfg
  haveI hN : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing ℚ B
  have hTB : ∀ a ∈ T, a ∈ B := fun a ha => Algebra.subset_adjoin (by exact_mod_cast ha)
  have hρB : ρ ∈ B := hTB _ (Finset.mem_insert_self _ _)
  have htB : ∀ i c, t i c ∈ B := by
    intro i c
    have hcG : c ∈ Submodule.span ℤ (G : Set (𝓞 D.F)) := by rw [hG]; trivial
    induction hcG using Submodule.span_induction with
    | mem x hx =>
      refine hTB _ (Finset.mem_insert_of_mem (Finset.mem_union_left _ ?_))
      exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_image_of_mem _ (by exact_mod_cast hx)⟩
    | zero => simpa using B.zero_mem
    | add x y _ _ hx hy => simpa using B.add_mem hx hy
    | smul a x _ hx =>
      have : t i (a • x) = (a : A) * t i x := by simp
      rw [this]
      exact B.mul_mem (by simpa using B.toSubring.intCast_mem a) hx
  have hwB : ∀ ij x, w ij x ∈ B := by
    intro ij x
    by_cases hx : x ∈ (w ij).support
    · refine hTB _ (Finset.mem_insert_of_mem (Finset.mem_union_right _ ?_))
      exact Finset.mem_biUnion.mpr ⟨ij, Finset.mem_univ _, Finset.mem_image_of_mem _ hx⟩
    · rw [Finsupp.notMem_support_iff.mp hx]; exact B.zero_mem
  have hun : ∀ k : ℕ, k ≠ 0 → IsUnit ((k : ℕ) : B.toSubring) := by
    intro k hk
    have h := (IsUnit.mk0 (k : ℚ) (by exact_mod_cast hk)).map (algebraMap ℚ B)
    simpa using h
  let t₁ : Fin D.a → (𝓞 D.F →+* B.toSubring) := fun i => (t i).codRestrict B.toSubring (htB i)
  let ρ₁ : B.toSubring := ⟨ρ, hρB⟩
  have pp : p.Prime := Fact.out
  have hpu : IsUnit ((p : ℕ) : B.toSubring) := hun p pp.ne_zero
  refine ⟨B.toSubring, hN, ?_⟩
  refine ⟨⟨fun k hk => hun k ?_, ρ₁, ?_, t₁, ?_, ?_, ?_⟩, hpu, rfl, fun i c => rfl⟩
  · rintro rfl
    have := (Nat.coprime_zero_left p).mp hk
    exact pp.ne_one this
  · apply Subtype.ext
    simpa [ρ₁] using hρ
  · intro i
    exact Subtype.ext (hω i)
  · intro i j hij
    rw [Ideal.eq_top_iff_one]
    have key : ((((w (i, j)).support.sum fun x =>
        (⟨w (i, j) x, hwB _ x⟩ : B.toSubring) * (t₁ i x - t₁ j x)) : B.toSubring)) = 1 := by
      apply Subtype.ext
      have := hw (i, j) hij
      rw [Finsupp.sum] at this
      simpa [t₁] using this
    rw [← key]
    exact Ideal.sum_mem _ fun x _ => Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨x, rfl⟩)
  · intro i j _ k _ _ β
    exfalso
    have h1 := hpu.map β
    simp at h1

private theorem gam_toSpecΓ {S : Scheme.{0}} {R₁ : Type} [CommRing R₁] (f : R₁ →+* Γ(S, ⊤)) (a : R₁) :
    gam (S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f) : S ⟶ Sp R₁) a = f a := by
  have h : (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv ≫
      (S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom f)).appTop = CommRingCat.ofHom f := by
    rw [Scheme.Hom.comp_appTop, ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality,
      Scheme.toSpecΓ_appTop, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact congrArg (fun g => CommRingCat.Hom.hom g a) h

end UpperTheory.BaseNoeth

open UpperTheory.BaseNoeth in
theorem UpperTheory.exists_noetherian_base_link :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (S : Scheme.{0}) (s : S ⟶ Sp R), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∃ (R₁ : Type) (_ : CommRing R₁) (_ : IsNoetherianRing R₁) (b₁ : Base D R₁) (s₁ : S ⟶ Sp R₁), IsUnit ((p : ℕ) : R₁) ∧ Link b b₁ s s₁ := by
  intro p _ D R _ b S s hp
  let g : R →+* Γ(S, ⊤) := gam s
  obtain ⟨R₁, hN, b₁, hpu, h1, h2⟩ := core D (A := Γ(S, ⊤)) hp
    (fun k hk => by simpa using (b.unit k hk).map g) (g b.ρ)
    (by simpa using congrArg g b.ρ_root)
    (fun i => g.comp (b.t i)) (fun i => by simp [b.t_ω])
    (fun i j hij => by
      have h := congrArg (Ideal.map g) (b.comax i j hij)
      rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
      simpa [Function.comp_def] using h)
  refine ⟨R₁, inferInstance, hN, b₁, S.toSpecΓ ≫ Spec.map (CommRingCat.ofHom R₁.subtype), hpu, ?_, ?_⟩
  · rw [gam_toSpecΓ]
    exact h1.symm
  · intro i c
    rw [gam_toSpecΓ]
    exact (h2 i c).symm
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel
open ReciprocityTheory.ChartRestriction.G.Out (RingAct)

namespace UpperTheory.QO

private theorem main' : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s) (K : Over S) [GrpObj K] (i : K ⟶ o.A), IsMonHom i → Mono i → IsFinite K.hom → Etale K.hom → (∀ (T : Over S) (x : T ⟶ o.A), InSub i x → KilledBy o w x) → (∀ a : D.O, ∃ g : K ⟶ K, g ≫ i = i ≫ o.act.act a) → IsIsogDeg (toUnit K) (Ideal.absNorm w ^ j) → ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ ∧ ∀ (T : Over S) (x : T ⟶ o.A), (x ≫ ψ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
  intro p _ D R _ _ b N h3 hcop hp hm r w j c hw hle hj hc S _ s o K _ i hi hmono hfin het hkill hstab hdeg
  obtain ⟨Y, o₀, m₀, o', ψ, hYf, hYe, his, htj, hu⟩ :=
    GlobalTheory.T.harrisTaylor_typeTj_isogenies_representable p D R b N h3 hcop hp r w j c hw hle hj hc hm S s o
  let Rd : RepData b N r w j c s o := ⟨Y, o₀, m₀, o', ψ, hYf, hYe, his, htj, hu⟩
  let Sd : SubData w j o := ⟨K, i, hi, hmono, hfin, het, hkill, hstab, hdeg⟩
  obtain ⟨W, hWo, hWc, hWat, hWgeo⟩ := UpperTheory.exists_clopen_subgroup_locus p D R b N r w j c hp hw hle hc S s o Rd Sd
  have hex : ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ S),
      ∃ y, y ≫ Rd.Y.hom = x ∧ Set.range y ⊆ W := by
    intro k _ _ x
    obtain ⟨y, hy, hg⟩ := UpperTheory.repData_geometric_points_of_subData p D R b N h3 hcop hp hm r w j c hw hle hj hc S s o Rd Sd k x
    exact ⟨y, hy, (hWgeo k y).2 hg⟩
  have huq : ∀ (k : Type) [Field k] [IsAlgClosed k] (y₁ y₂ : Sp k ⟶ Rd.Y.left),
      y₁ ≫ Rd.Y.hom = y₂ ≫ Rd.Y.hom → Set.range y₁ ⊆ W → Set.range y₂ ⊆ W → y₁ = y₂ := by
    intro k _ _ y₁ y₂ h h₁ h₂
    exact UpperTheory.subData_points_correspond_repData p D R b N h3 hcop hp hm r w j c hw hle hc S s o Rd Sd k y₁ y₂ h
      ((hWgeo k y₁).1 h₁) ((hWgeo k y₂).1 h₂)
  obtain ⟨σ, hσ, hσW⟩ := UpperTheory.exists_section_of_etale_clopen_geomPoint_unique S Rd.Y Rd.fin Rd.et W hWo hWc hex huq
  obtain ⟨o'', ψ'', h1, h2, h3'⟩ := UpperTheory.exists_isPIsog_isTj_of_section_repData p D R b N h3 hcop r w j c S s o Rd σ hσ
  refine ⟨o'', ψ'', h1, h2, fun T a => ?_⟩
  obtain ⟨a₀, ha₀, hψ, hk⟩ := h3' T a
  have key := hWat S σ hσW T T.hom a₀ a ha₀
  rw [hψ]
  simp only [hk]
  exact key

end UpperTheory.QO

theorem UpperTheory.Cb.exists_pIsogeny_kernel_eq_subgroupScheme :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → D.m = 1 → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R), IsUnit ((p : ℕ) : Γ(S, ⊤)) → ∀ (o : Obj b N s) (K : Over S) [GrpObj K] (i : K ⟶ o.A), IsMonHom i → Mono i → IsFinite K.hom → Etale K.hom → (∀ (T : Over S) (x : T ⟶ o.A), InSub i x → KilledBy o w x) → (∀ a : D.O, ∃ g : K ⟶ K, g ≫ i = i ≫ o.act.act a) → IsIsogDeg (toUnit K) (Ideal.absNorm w ^ j) → ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsPIsog c o o' ψ ∧ IsTj r w j o o' ψ ∧ ∀ (T : Over S) (x : T ⟶ o.A), (x ≫ ψ = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) x) ↔ InSub i x := by
  intro p _ D R _ b N hN hNp hm r w j c hw hu hj hc S _ s hp o K _ i hi hmono hKf hKe hkill hst hdeg
  obtain ⟨R₁, _, _, b₁, s₁, hp₁, L⟩ := UpperTheory.exists_noetherian_base_link p D R b S s hp
  obtain ⟨o', ψ, h1, h2, h3⟩ := UpperTheory.QO.main' p D R₁ b₁ N hN hNp hp₁ hm r w j c hw hu hj hc S s₁
    (UpperTheory.QO.conv L o) K i hi hmono hKf hKe hkill hst hdeg
  exact ⟨UpperTheory.QO.conv L.symm o', ψ, h1, h2, h3⟩
