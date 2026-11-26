module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeFirstDeRhamStructure
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLPowerTorsionKernelEqLPartIsogenyDegree

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeExistsCompEqNsmulOfKernelKilled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInverseDeg
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.InvDegInverse

variable {K : Type} [Field K]

def invKer {A B : AbVar K} (f : A ⟶ B) : Subgroup A.Pt where
  carrier := {x | ptMap f x = 1 ∧ ∃ k : ℕ, (k : K) ≠ 0 ∧ x ^ k = 1}
  one_mem' := ⟨map_one _, 1, by simp, one_pow _⟩
  mul_mem' := by
    rintro x y ⟨hx, a, ha, hxa⟩ ⟨hy, b, hb, hyb⟩
    refine ⟨by rw [map_mul, hx, hy, _root_.one_mul], a * b, by push_cast; exact mul_ne_zero ha hb, ?_⟩
    rw [mul_pow, pow_mul, hxa, one_pow, mul_comm a b, pow_mul, hyb, one_pow, _root_.one_mul]
  inv_mem' := by
    rintro x ⟨hx, a, ha, hxa⟩
    exact ⟨by rw [map_inv, hx, inv_one], a, ha, by rw [inv_pow, hxa, inv_one]⟩

theorem finite_invKer {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) : Finite (invKer f) := by
  have : Finite (ptMap f).ker := (GlobalTheory.AV.AbVar.isFinite_iff_finite_ker K A B f).1 hf.1
  exact Finite.of_injective (fun x : invKer f => (⟨x.1, x.2.1⟩ : (ptMap f).ker))
    (fun x y h => Subtype.ext (congrArg (fun z : (ptMap f).ker => (z : A.Pt)) h))

theorem card_invKer_ne_zero {A B : AbVar K} (f : A ⟶ B) (hf : IsIsogeny f) :
    ((Nat.card (invKer f) : ℕ) : K) ≠ 0 := by
  haveI := finite_invKer f hf
  intro h0
  have hpos : 0 < Nat.card (invKer f) := Nat.card_pos
  have hpd : ringChar K ∣ Nat.card (invKer f) := (ringChar.spec K _).1 h0
  rcases CharP.char_is_prime_or_zero K (ringChar K) with hpp | hp0
  · haveI := Fact.mk hpp
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (ringChar K) hpd
    obtain ⟨_, k, hk, hyk⟩ := y.2
    have : ringChar K ∣ k := by
      rw [← hy, ← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hyk
    exact hk ((ringChar.spec K k).2 this)
  · rw [hp0, zero_dvd_iff] at hpd
    omega

theorem galPts_mem_invKer {A B : AbVar K} (f : A ⟶ B) (σ : Gal K) (x : A.Pt) (hx : x ∈ invKer f) :
    galPts A.X σ x ∈ invKer f := by
  obtain ⟨h1, k, hk, hxk⟩ := hx
  refine ⟨?_, k, hk, by rw [← map_pow, hxk, map_one]⟩
  have e : ptMap f (galPts A.X σ x) = galPts B.X σ (ptMap f x) :=
    show (specAut σ ≫ x) ≫ f.hom = specAut σ ≫ (x ≫ f.hom) from Category.assoc _ _ _
  rw [e, h1, map_one]

end GlobalTheory.AV.AbVar.InvDegInverse
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeExistsCompEqNsmulOfKernelKilled
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AV.AbVar.KilledInverse

open GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.AV.KerPart GlobalTheory.AV.AbVar.InvDegInverse

variable {k : Type} [Field k]

theorem exists_kerPow_finrank_ne_zero {A B : AbVar k} (f : A ⟶ B) (e : ℕ) (he : IsUnit (e : k)) :
    ∃ (H : Type) (_ : CommRing H) (_ : Algebra k H) (i : ptOver k H ⟶ A.X),
      KerPow f e H i ∧ ((Module.finrank k H : ℕ) : k) ≠ 0 := by
  have he0 : (e : k) ≠ 0 := he.ne_zero
  have hepos : 0 < e := Nat.pos_of_ne_zero (by rintro rfl; exact he0 Nat.cast_zero)

  have key : ∃ p : ℕ, p.Prime ∧ ¬ p ∣ e ∧ ∀ n : ℕ, ¬ p ∣ n → (n : k) ≠ 0 := by
    rcases CharP.char_is_prime_or_zero k (ringChar k) with hp | hp0
    · refine ⟨ringChar k, hp, fun h => he0 ((ringChar.spec k e).2 h), fun n hn h0 => hn ((ringChar.spec k n).1 h0)⟩
    · obtain ⟨p, hpe, hp⟩ := Nat.exists_infinite_primes (e + 1)
      refine ⟨p, hp, fun h => ?_, fun n hn h0 => ?_⟩
      · have := Nat.le_of_dvd hepos h
        omega
      · have h1 := (ringChar.spec k n).1 h0
        rw [hp0, zero_dvd_iff] at h1
        exact hn (h1 ▸ dvd_zero p)
  obtain ⟨p, hp, hpe, hpk⟩ := key
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨H, _, _, i, hi, hH⟩ := exists_kerPow_not_dvd p k A B f e hepos hpe
  exact ⟨H, inferInstance, inferInstance, i, hi, hpk _ hH⟩

theorem finite_ker_of_kerPow {A B : AbVar k} (f : A ⟶ B) (e : ℕ) {H : Type} [CommRing H] [Algebra k H]
    {i : ptOver k H ⟶ A.X} (hi : KerPow f e H i) (hH : Module.finrank k H ≠ 0)
    (hkill : ∀ (T : Over (Sp k)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ e = 1) : Finite (ptMap f).ker := by
  haveI : Module.Finite k H := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hH)
  have hx : ∀ x : (ptMap f).ker, x.1 ≫ f.hom = 1 := fun x => MonoidHom.mem_ker.mp x.2
  let φ : (ptMap f).ker → (H →ₐ[k] AlgebraicClosure k) := fun x =>
    (hi.2 (AlgebraicClosure k) x.1 (hx x) (hkill _ x.1 (hx x))).exists.choose
  have hφ : ∀ x, spMap (φ x).toRingHom ≫ i.left = x.1.left := fun x =>
    (hi.2 (AlgebraicClosure k) x.1 (hx x) (hkill _ x.1 (hx x))).exists.choose_spec
  refine Finite.of_injective φ fun x y hxy => ?_
  apply Subtype.ext
  apply Over.OverMorphism.ext
  rw [← hφ x, ← hφ y, hxy]

theorem exists_comp_eq_nsmul (A B : AbVar k) (f : A ⟶ B) (hdim : A.dim = B.dim) (e : ℕ) (he : IsUnit (e : k))
    (hkill : ∀ (T : Over (Sp k)) (x : T ⟶ A.X), x ≫ f.hom = 1 → x ^ e = 1) :
    ∃ m : B ⟶ A, f ≫ m = e • 𝟙 A := by
  obtain ⟨H, _, _, i, hi, hH⟩ := exists_kerPow_finrank_ne_zero f e he
  have hH0 : Module.finrank k H ≠ 0 := fun h0 => hH (by rw [h0, Nat.cast_zero])
  have hfin : IsFinite f.hom.left :=
    (isFinite_iff_finite_ker k A B f).2 (finite_ker_of_kerPow f e hi hH0 hkill)
  have hf : IsIsogeny f := ⟨hfin, surjective_of_isFinite_of_dim_eq k A B f hdim hfin⟩
  have hd : ((deg f : ℕ) : k) ≠ 0 := by
    obtain ⟨H0, _, _, i0, hi0, h0⟩ := exists_kerPow_zero_finrank_eq_deg k A B f hf
    rw [← h0, finrank_eq_of_kerPow hi0 hi (fun R _ _ x hx => ⟨fun _ => hkill _ x hx, fun _ => pow_zero x⟩)]
    exact hH
  haveI hGfin := finite_invKer f hf
  obtain ⟨C, q, hq, hdq, hker, huniv⟩ := GlobalTheory.T.exists_quotient_of_galoisStable_finite_subgroup k A (invKer f) hGfin (card_invKer_ne_zero f hf)
    (galPts_mem_invKer f)
  obtain ⟨h, hqh⟩ := huniv B f (fun x hx => hx.1)
  have hdimAC := (GlobalTheory.AV.AbVar.isogeny_flat_finrank k A C q hq).1
  have hdimAB := (GlobalTheory.AV.AbVar.isogeny_flat_finrank k A B f hf).1
  have hcomp := GlobalTheory.AV.AbVar.isIsogeny_comp_iff_and_deg_comp k A C B q h hdimAC (hdimAC.symm.trans hdimAB)
  rw [hqh] at hcomp
  have hdeg : deg f = deg q * deg h := hcomp.2
  have hv : ∀ l : ℕ, l.Prime → (l : k) ≠ 0 → padicValNat l (deg f) = padicValNat l (deg q) := by
    intro l hl hlK
    haveI := Fact.mk hl
    have e1 := GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree k l hlK A B f hf
    have e2 := GlobalTheory.T.card_lPowerTorsion_kernel_eq_lPart_isogenyDegree k l hlK A C q hq
    have hset : Nat.card {x : A.Pt // x ≫ f.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} =
        Nat.card {x : A.Pt // x ≫ q.hom = 1 ∧ ∃ n : ℕ, x ^ l ^ n = 1} := by
      apply Nat.card_congr
      apply Equiv.subtypeEquivRight
      intro x
      constructor
      · rintro ⟨h1, n, hn⟩
        refine ⟨?_, n, hn⟩
        have hm : x ∈ invKer f := ⟨h1, l ^ n, by push_cast; exact pow_ne_zero _ hlK, hn⟩
        rw [← hker] at hm
        exact hm
      · rintro ⟨h1, n, hn⟩
        refine ⟨?_, n, hn⟩
        rw [← hqh, comp_hom, ← Category.assoc, h1]
        exact (ptMap h).map_one
    rw [e1, e2] at hset
    exact Nat.pow_right_injective hl.two_le hset
  have hd0 : deg f ≠ 0 := by
    intro h0; apply hd; rw [h0]; simp
  have hq0 : deg q ≠ 0 := by
    intro h0; apply hd0; rw [hdeg, h0, zero_mul]
  have hh0 : deg h ≠ 0 := by
    intro h0; apply hd0; rw [hdeg, h0, mul_zero]
  have hh1 : deg h = 1 := by
    rw [Nat.eq_one_iff_not_exists_prime_dvd]
    intro l hl hdvd
    by_cases hlK : (l : k) = 0
    · apply hd
      obtain ⟨c, hc⟩ : l ∣ deg f := hdeg ▸ dvd_mul_of_dvd_right hdvd _
      rw [hc]; push_cast; rw [hlK, zero_mul]
    · haveI := Fact.mk hl
      have e' := hv l hl hlK
      rw [hdeg, (show ∀ {p a b : ℕ} [_root_.Fact (_root_.Nat.Prime p)], a ≠ 0 → b ≠ 0 → _root_.padicValNat p (a * b) = _root_.padicValNat p a + _root_.padicValNat p b from by simpa only [← _root_.Nat.padicValNat_def] using @_root_.Nat.multiplicity_mul) hq0 hh0] at e'
      have h1 := one_le_padicValNat_of_dvd hh0 hdvd
      rw [← Nat.padicValNat_def] at h1
      omega
  have hiso : IsIso h := (GlobalTheory.AV.AbVar.isIso_iff_deg_eq_one k C B h).2 hh1
  obtain ⟨r, hr⟩ := huniv A (e • 𝟙 A) (fun x hx => by
    change x ≫ (e • 𝟙 A).hom = 1
    rw [nsmul_hom, id_hom, GlobalTheory.AV.DegSep.comp_pow_id]
    exact hkill _ x hx.1)
  refine ⟨inv h ≫ r, ?_⟩
  rw [← hqh, Category.assoc, IsIso.hom_inv_id_assoc, hr]

end GlobalTheory.AV.AbVar.KilledInverse

namespace GlobalTheory.AV

theorem exists_comp_eq_pow_of_ker_killed : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (l : A ⟶ B), IsMonHom l → ∀ e : ℕ, IsUnit (e : k) → (∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → x ^ e = 1) → ∃ m : B ⟶ A, IsMonHom m ∧ l ≫ m = 𝟙 A ^ e := by
  intro k _ A B _ _ _ _ g hA hB sA sB l hl e he hkill
  let A' : AbVar k := { X := A, ab := hA, dim := g, smooth := sA }
  let B' : AbVar k := { X := B, ab := hB, dim := g, smooth := sB }
  obtain ⟨m, hm⟩ := AbVar.KilledInverse.exists_comp_eq_nsmul A' B' (AbVar.Hom.mk (A := A') (B := B') l) rfl e he
    (fun T x hx => hkill T x hx)
  refine ⟨m.hom, inferInstance, ?_⟩
  have h2 := congrArg AbVar.Hom.hom hm
  rw [AbVar.comp_hom, AbVar.mk_hom, AbVar.nsmul_hom, AbVar.id_hom] at h2
  exact h2

end GlobalTheory.AV
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeExistsCompEqNsmulOfKernelKilledStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelianScheme_exists_comp_eq_nsmul_of_kernel_killed : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ (l : A ⟶ B), IsMonHom l → ∀ e : ℕ, IsUnit (e : k) → (∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → x ^ e = 1) → ∃ m : B ⟶ A, IsMonHom m ∧ l ≫ m = 𝟙 A ^ e := by
  first | exact @GlobalTheory.AV.exists_comp_eq_pow_of_ker_killed | exact GlobalTheory.AV.exists_comp_eq_pow_of_ker_killed | (intros; apply GlobalTheory.AV.exists_comp_eq_pow_of_ker_killed <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfTriv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfTriv
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbDual GlobalTheory.CechPic
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BirigidHom

theorem exists_hom_of_triv : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B],
    IsAbelianScheme A → IsAbelianScheme B → ∀ (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ →
    ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    ∃ l : A ⟶ B, IsMonHom l ∧ LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) := by
  intro k _ A B _ _ _ hA hB P₀ hd P hP h₁ h₂
  obtain ⟨g, hg⟩ := GlobalTheory.AbelianDim.exists_relDim k A hA
  let AV : GlobalTheory.AV.AbVar k := { X := A, ab := hA, dim := g, smooth := hg }
  obtain ⟨c, L, hL, hamp, -⟩ := GlobalTheory.AV.exists_isAmpleCls k AV
  obtain ⟨H, hH, aH⟩ := GlobalTheory.BirigidLift.exists_relAmple_prod (A := A) (B := A) hA hA hL hamp hL hamp
  obtain ⟨a₁, -⟩ := GlobalTheory.BirigidLift.additive_of_triv hA hA hH aH hP h₁ h₂
  obtain ⟨x, hx, -⟩ := hd.univ A P hP a₁
  have hE : (ev P₀ (fst A A) (snd A A ≫ x)).IsLB := pull_isLB hd.isLB _
  have e : cls P hP = evc hd.isLB (fst A A) (snd A A ≫ x) := (cls_eq_iff hP hE).2 hx
  refine ⟨x, GlobalTheory.rigidity_holds (Sp k) A B hA hB x ?_, hx⟩
  apply hd.eq_one
  rw [triv_ev_iff hd.isLB, ← Category.assoc, ← GlobalTheory.BirigidLift.evc_of_cls hd.isLB hP e]
  have u1 : snd A (𝟙_ (Over (Sp k))) ≫ (η : 𝟙_ (Over (Sp k)) ⟶ A) = 1 := by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A (𝟙_ (Over (Sp k)))) (toUnit _)]
  rw [u1]
  exact evc_one_right hP h₂ _

end GlobalTheory.BirigidHom
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomOfTrivStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_monHom_lbIso_ev_of_trivial_pullbacks : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [IsCommMonObj A] [GrpObj B], IsAbelianScheme A → IsAbelianScheme B → ∀ (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → ∃ l : A ⟶ B, IsMonHom l ∧ LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) := by
  first | exact @GlobalTheory.BirigidHom.exists_hom_of_triv | exact GlobalTheory.BirigidHom.exists_hom_of_triv | (intros; apply GlobalTheory.BirigidHom.exists_hom_of_triv <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsoSwapTrivialOfKernelPoint
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsoSwapTrivialOfKernelPoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory

open GlobalTheory.AbLaw GlobalTheory.CechPic

namespace GlobalTheory.AbDual

theorem lbIso_swap_and_triv_of_ker : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (l : A ⟶ B), LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) → LBIso (GlobalTheory.AbDual.ev P (fst A A) (snd A A ≫ 𝟙 A)) (GlobalTheory.AbDual.ev (GlobalTheory.AbDual.swap P₀) (fst A A ≫ l) (snd A A)) ∧ ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen := by
  intro k _ A B _ _ P₀ hD P hP hsym l hl
  have hP₀ := hD.isLB
  have pull_isLB : ∀ {X Y : Scheme.{0}} {L : LB X}, L.IsLB → (F : Y ⟶ X) → (L.pull F).IsLB := by
    intro X Y L hL F
    refine { cover := top_le_iff.1 ?_, g_self := ?_, cocycle := ?_ }
    · intro y _
      obtain ⟨i, hi⟩ := exists_chart hL (F y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 Y) y _ hy, map_one, gm_pull_g L F (𝟙 Y) y J J hy hy]
      exact gm_self hL _ y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_pull_g L F (𝟙 Y) y I J hy.1.1 hy.1.2,
        gm_pull_g L F (𝟙 Y) y J K hy.1.2 hy.2, gm_pull_g L F (𝟙 Y) y I K hy.1.1 hy.2]
      exact gm_cocycle hL _ y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  have pullIso : ∀ {X Y Z : Scheme.{0}} {M : LB Y} {N : LB X} {f : Y ⟶ X},
      LBIso M (N.pull f) → (g : Z ⟶ Y) → LBIso (M.pull g) (N.pull (g ≫ f)) := by
    intro X Y Z M N f H g
    exact H.chartPull (chartPullPull M g)
      (chartPullSame N (fun _ : PUnit => g ≫ f) (fun _ : PUnit => f) (fun _ => 1) g fun _ => rfl)
  have key : ∀ (Y : Over (Sp k)) (a b : Y ⟶ A), LBIso (ev P a b) (ev P₀ b (a ≫ l)) := by
    intro Y a b
    have hs := pullIso hsym (lift a b).left
    have hl' := pullIso hl (lift b a).left
    have es : LBIso (ev P a b) (ev P b a) := by
      simpa only [← Over.comp_left, comp_lift, lift_snd, lift_fst] using hs
    have el : LBIso (ev P b a) (ev P₀ b (a ≫ l)) := by
      simpa only [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc] using hl'
    exact (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).1
      (((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP _)).2 es).trans
       ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 el))
  refine ⟨?_, fun T x hx => ?_⟩
  · have hs : LBIso (swap P₀) (swap P₀) := (CechPic.cls_eq_iff (pull_isLB hP₀ _) (pull_isLB hP₀ _)).1 rfl
    have hs' := pullIso hs (lift (fst A A ≫ l) (snd A A)).left
    have hs'' : LBIso (ev (swap P₀) (fst A A ≫ l) (snd A A)) (ev P₀ (snd A A) (fst A A ≫ l)) := by
      simpa only [swap, ev, ← Over.comp_left, comp_lift, lift_fst, lift_snd] using hs'
    apply (CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB (pull_isLB hP₀ _) _)).1
    exact ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 (by simpa only [Category.comp_id] using key (A ⊗ A) (fst A A) (snd A A))).trans
      ((CechPic.cls_eq_iff (pull_isLB (pull_isLB hP₀ _) _) (pull_isLB hP₀ _)).2 hs'').symm
  · have hk := key (A ⊗ T) (snd A T ≫ x) (fst A T)
    simp only [Category.assoc, hx, MonObj.comp_one] at hk
    have ht : Triv (ev P₀ (fst A T) (1 : A ⊗ T ⟶ B)) := by
      obtain ⟨t, ht⟩ := hD.zero
      have h := DVR.pullGen_isGen _ _ _ t ht (fst A T).left
      simpa only [ev, ← Over.comp_left, comp_lift, Category.comp_id, MonObj.comp_one] using (show Triv _ from ⟨_, h⟩)
    exact (CechPic.iso_triv_iff _).1 ((CechPic.cls_eq_iff (LB.isLB_triv _) (pull_isLB hP _)).1
      (((CechPic.cls_eq_iff (LB.isLB_triv _) (pull_isLB hP₀ _)).2 ((CechPic.iso_triv_iff _).2 ht)).trans
        ((CechPic.cls_eq_iff (pull_isLB hP _) (pull_isLB hP₀ _)).2 hk).symm))

end GlobalTheory.AbDual
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareBundleIsoSwapTrivialOfKernelPointStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincareBundleIso_swap_trivial_of_kernelPoint : ∀ (k : Type) [Field k] (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (P₀ : LB (A ⊗ B).left), GlobalTheory.AbDual.IsDual A B P₀ → ∀ (P : LB (A ⊗ A).left), P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → ∀ (l : A ⟶ B), LBIso P (GlobalTheory.AbDual.ev P₀ (fst A A) (snd A A ≫ l)) → LBIso (GlobalTheory.AbDual.ev P (fst A A) (snd A A ≫ 𝟙 A)) (GlobalTheory.AbDual.ev (GlobalTheory.AbDual.swap P₀) (fst A A ≫ l) (snd A A)) ∧ ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ l = 1 → ∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen := by
  first | (exact @GlobalTheory.AbDual.lbIso_swap_and_triv_of_ker) | (exact GlobalTheory.AbDual.lbIso_swap_and_triv_of_ker) | (intros; apply GlobalTheory.AbDual.lbIso_swap_and_triv_of_ker  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationPairingNondegenerate
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham

attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.HTPolPair
open GlobalTheory.AbDual

theorem nondeg : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ x, (∀ y, φ x y = 0) → x = 0 := by
  intro p _ D R _ b N _ _ k _ _ t o₀ β ht φ hφ x hx
  obtain ⟨g, hg⟩ := GlobalTheory.AbVarRelDim.exists_relDim k o₀.A o₀.ab
  let A' : GlobalTheory.AV.AbVar k := ⟨o₀.A, o₀.ab, g, hg⟩
  obtain ⟨B, P₀, ⟨h1, h2⟩, hdim⟩ := GlobalTheory.AV.exists_dualPair k A'
  have hgB : SmoothOfRelativeDimension g B.X.hom := by
    have := B.smooth; rw [hdim] at this; exact this
  obtain ⟨l, hl, hlP⟩ := GlobalTheory.T.exists_monHom_lbIso_ev_of_trivial_pullbacks k o₀.A B.X o₀.ab B.ab P₀ h1 o₀.P o₀.isLB o₀.rig₁ o₀.rig₂
  obtain ⟨iso, hker⟩ := GlobalTheory.T.poincareBundleIso_swap_trivial_of_kernelPoint k o₀.A B.X P₀ h1 o₀.P o₀.isLB o₀.symm l hlP
  obtain ⟨e, he, hkP⟩ := o₀.kerP
  have hu : IsUnit (e : k) := by
    have := (b.unit e he).map β
    simpa using this
  obtain ⟨m, hm, hlm⟩ := GlobalTheory.T.abelianScheme_exists_comp_eq_nsmul_of_kernel_killed k o₀.A B.X g o₀.ab B.ab hg hgB l hl e hu fun T y hy => hkP T y (hker T y hy)
  have hPf : IsPerfect B.X o₀.A (swap P₀) := (IsDual.isPerfect h1 h2).swap
  have CAA := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor o₀.A o₀.A o₀.ab o₀.ab)
    (smooth_prod hg hg)
  have CBA := cupSquare_of_free GlobalTheory.abelianDeRham.1 (AbelianSchemeGerms.isAbelianScheme_tensor B.X o₀.A B.ab o₀.ab)
    (smooth_prod hgB hg)
  obtain ⟨φ', hφ'⟩ := exists_isCorrForm CBA hPf.isLB hPf.zero_left hPf.zero_right
  have hadj := IsCorrForm.adjoint CAA o₀.isLB hPf.isLB hφ hφ' l (𝟙 o₀.A) iso
  have perf := (IsCorrForm.perfect GlobalTheory.abelianDeRham B.ab hgB o₀.ab hg hPf hφ').1
  have h0 : push (dp0 k) (𝟙 _) l x = 0 := by
    refine (injective_iff_map_eq_zero _).1 perf.bijective_left.1 _ (LinearMap.ext fun y => ?_)
    rw [← hadj x y, push_id]
    exact hx y

  have hpowM : ∀ j : ℕ, IsMonHom (𝟙 o₀.A ^ j) := by
    intro j
    induction j with
    | zero => rw [pow_zero]; exact isMonHom_one o₀.A o₀.A
    | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift (𝟙 o₀.A ^ n) (𝟙 o₀.A) ≫ μ[o₀.A]))
  have hpush : ∀ j : ℕ, push (dp0 k) (𝟙 _) (𝟙 o₀.A ^ j) = (j : k) • LinearMap.id := by
    intro j
    induction j with
    | zero =>
      rw [push_congr (dp0 k) (𝟙 _) (pow_zero (𝟙 o₀.A)), push_one]
      simp
    | succ n ih =>
      haveI := hpowM n
      haveI : IsMonHom (𝟙 o₀.A ^ n * 𝟙 o₀.A) := by rw [← pow_succ]; exact hpowM (n + 1)
      rw [push_congr (dp0 k) (𝟙 _) (pow_succ (𝟙 o₀.A) n), push_mul, ih, push_id]
      push_cast
      rw [add_smul, one_smul]
  haveI := hpowM e
  have key : push (dp0 k) (𝟙 _) m (push (dp0 k) (𝟙 _) l x) = (e : k) • x := by
    rw [← LinearMap.comp_apply, ← push_comp, push_congr (dp0 k) (𝟙 _) hlm, hpush]
    rfl
  rw [h0, map_zero] at key
  exact (hu.smul_eq_zero.1 key.symm)

end GlobalTheory.HTPolPair
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPolarisationPairingNondegenerateStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_polarisation_pairing_nondegenerate : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] (b : GlobalTheory.UPel.HT.Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ Sp R) (o₀ : GlobalTheory.UPel.HT.Obj b N t) (β : R →+* k), t = spMap β → ∀ φ : LinearMap.BilinForm k (HdR o₀.A), GlobalTheory.AbDual.IsCorrForm (dp0 k) (𝟙 _) o₀.A o₀.A o₀.P φ → ∀ x, (∀ y, φ x y = 0) → x = 0 := by
  first | exact @GlobalTheory.HTPolPair.nondeg | exact GlobalTheory.HTPolPair.nondeg | (intros; apply GlobalTheory.HTPolPair.nondeg <;> assumption)
end
