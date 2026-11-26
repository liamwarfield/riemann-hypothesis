module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PNuInt
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKNBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGSimOf
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeTranslateLocallyNoetherianBase
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactOfQProj
public import Development.AutomorphicArithmetic.CommutativeAlgebra.ClopProjFiniteEtaleOfIsClosed
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitForget
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHomDesc
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.ExistsDeeperNormalLevel
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasicHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRelArith
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransCancel

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwFEt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem card_eq_relIndex {G Γ : Type} [Group G] (H L : Subgroup G) (r : Γ → G) (hr : ∀ x, r x ∈ L)
    (hu : ∀ k ∈ L, ∃! x, k * (r x)⁻¹ ∈ H) : Nat.card Γ = H.relIndex L := by
  unfold Subgroup.relIndex Subgroup.index
  refine Nat.card_congr (Equiv.ofBijective
    (fun x => (QuotientGroup.mk ⟨(r x)⁻¹, L.inv_mem (hr x)⟩ : L ⧸ H.subgroupOf L)) ⟨?_, ?_⟩)
  · intro x y e
    have e' := QuotientGroup.eq.mp e
    have h2 : r x * (r y)⁻¹ ∈ H := by simpa [Subgroup.mem_subgroupOf] using e'
    have h1 : r x * (r x)⁻¹ ∈ H := by simp [H.one_mem]
    exact (hu (r x) (hr x)).unique h1 h2
  · intro q
    induction q using QuotientGroup.induction_on with
    | H g =>
      obtain ⟨x, hx, -⟩ := hu (g : G)⁻¹ (L.inv_mem g.2)
      refine ⟨x, QuotientGroup.eq.mpr ?_⟩
      rw [Subgroup.mem_subgroupOf]
      have h3 := H.inv_mem hx
      simpa using h3

private theorem fEt_normal (hb : FEtBasic) (hg : TwGal) {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G)
    (m j : X.ι) (b : X.admitted m j 1) (hn : ∀ k ∈ X.K j, ∀ u ∈ X.K m, k * u * k⁻¹ ∈ X.K m) :
    FEt (X.tr m j 1 b.1 b.2) ((X.K m).relIndex (X.K j)) := by
  obtain ⟨Γ, _, _, r, c, hr, hu, hG⟩ := hg X m j b hn
  rw [← card_eq_relIndex _ _ r hr hu]
  exact hb.2.2 _ Γ _ hG

theorem UpperTheory.Gal.G3.pTwFEt :
    FEtBasic → TwGal → TwFEt := by
  intro hb hg
  unfold TwFEt
  intro B G _ X i j a
  obtain ⟨m, hmj, hn, hS⟩ := X.deep j {(i, 1)}
  have hmi : X.K m ≤ X.K i := fun u hu => by simpa using hS (i, 1) (by simp) u hu
  have hij : X.K i ≤ X.K j := fun u hu => by simpa using a.2 u hu
  have b : X.admitted m j 1 := X.isAdmissibleIntegralBasisChange_one hmj
  have b' : X.admitted m i 1 := X.isAdmissibleIntegralBasisChange_one hmi
  have h1 := fEt_normal hb hg X m j b hn
  have h2 := fEt_normal hb hg X m i b' (fun k hk u hu => hn k (hij hk) u hu)
  have hc : X.tr m i 1 b'.1 b'.2 ≫ X.tr i j 1 a.1 a.2 = X.tr m j 1 b.1 b.2 := by
    have e : ∀ (h : G) (_ : h = 1) p q, X.tr m j h p q = X.tr m j 1 b.1 b.2 := by
      rintro _ rfl _ _; rfl
    rw [X.tr_mul m i j 1 1 b'.1 b'.2 a.1 a.2 (by simpa using a.1) (by simpa using b.2)]
    exact e _ (mul_one 1) _ _
  refine ⟨X.fin i j a.1 a.2, X.etale i j a.1 a.2, fun K _ _ x => ?_⟩
  set s := X.tr i j 1 a.1 a.2 with hs
  set r := X.tr m i 1 b'.1 b'.2 with hr
  have fs : Finite {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x} :=
    have := X.fin i j a.1 a.2
    (UpperTheory.Gal.TranscendenceTraces.fibFin_holds s K x).to_subtype
  have fr : ∀ y : {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x},
      Finite {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ r = y.1} := fun y =>
    have := X.fin m i b'.1 b'.2
    (UpperTheory.Gal.TranscendenceTraces.fibFin_holds r K y.1).to_subtype
  have := Fintype.ofFinite {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x}
  have e1 : {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ X.tr m j 1 b.1 b.2 = x} ≃
      Σ y : {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x},
        {w : Spec (CommRingCat.of K) ⟶ X.Z m // w ≫ r = y.1} :=
    { toFun := fun w => ⟨⟨w.1 ≫ r, by rw [Category.assoc, hc, w.2]⟩, ⟨w.1, rfl⟩⟩
      invFun := fun p => ⟨p.2.1, by rw [← hc, ← Category.assoc, p.2.2, p.1.2]⟩
      left_inv := fun w => rfl
      right_inv := by
        rintro ⟨⟨y, hy⟩, ⟨w, hw⟩⟩
        change w ≫ r = y at hw
        subst hw
        rfl }
  have hcount : Nat.card {y : Spec (CommRingCat.of K) ⟶ X.Z i // y ≫ s = x} * (X.K m).relIndex (X.K i) =
      (X.K m).relIndex (X.K j) := by
    rw [← h1.2.2 K x, Nat.card_congr e1, Nat.card_sigma]
    simp only [h2.2.2 K, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    rw [Nat.card_eq_fintype_card]
  have hmul := Subgroup.relIndex_mul_relIndex (X.K m) (X.K i) (X.K j) hmi hij
  have hpos : 0 < (X.K m).relIndex (X.K i) := Nat.pos_of_ne_zero (X.idx m i)
  apply Nat.eq_of_mul_eq_mul_left hpos
  rw [hmul, ← hcount, mul_comm]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransSelf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pol_one {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R]
    {gb : GBase D.toG R} {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) :
    Nonempty (LBIso (Hecke.lbPow o.P 1) (o.P.pull (Hecke.sq2 (𝟙 o.A)))) := by
  have h : Hecke.sq2 (𝟙 o.A) = 𝟙 _ := by simp [Hecke.sq2]
  refine ⟨?_⟩
  rw [h]
  unfold Hecke.lbPow LB.pull
  exact (GlobalTheory.PrimNorm.lbIso_iff o.isLB _ _ _ _).2 rfl

private theorem gTateIso_ev_nsmul' {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q]
    {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop} (I : GTateIso G k Q act e) (n c : ℕ)
    (y : G.La) : I.ev n (c • y) = I.ev n y ^ c := by
  induction c with
  | zero =>
    have h := I.add n 0 0
    rw [add_zero] at h
    have h1 : I.ev n 0 = 1 :=
      mul_left_cancel (a := I.ev n 0) (by rw [_root_.mul_one]; exact h.symm)
    rw [zero_smul, pow_zero, h1]
  | succ c ih => rw [succ_nsmul, I.add, ih, pow_succ]

theorem UpperTheory.Gal.G3.pTransSelf :
    MultBasic → RelComp → TateTwist → TransSelf := by
  intro hM hR hT p _ D G L R _ _ gb S s N
  refine ⟨fun o u hu => ?_, fun c hN hc o => ?_⟩
  · have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
    obtain ⟨a, a', ha, ha', haa, heq⟩ := (hM p).2.2 D G L u hu1
    refine ⟨⟨by simp, by simp⟩, fun _ => by simp, ⟨𝟙 _, 1, ⟨by simp, by simp⟩, fun _ => by simp,
      by simp, by simp, Nat.coprime_one_left _⟩, ⟨1, Nat.coprime_one_left _, pol_one o, a, a', ha,
      ha', haa, heq⟩, ?_⟩
    intro k _ _ x β hβ
    obtain ⟨I, hI⟩ := o.geom k x β hβ
    obtain ⟨J, hJ, hRel⟩ := hT p D G L R gb S s N o k x I hI u hu
    exact ⟨I, J, hI, hJ, hRel⟩
  · obtain ⟨a, a', ha, ha', haa, heq⟩ := (hM p).2.2 D G L 1 (one_mem _)
    have hmon : IsMonHom (𝟙 o.A) := ⟨by simp, by simp⟩
    refine ⟨show IsMonHom (𝟙 o.A) from hmon, fun _ => by simp [GObj.forgetMul],
      ⟨𝟙 _, 1, show IsMonHom (𝟙 o.A) from hmon,
      fun _ => by simp [GObj.forgetMul], by simp; exact Category.comp_id _,
      by simp; exact Category.comp_id _, Nat.coprime_one_left _⟩,
      ⟨1, Nat.coprime_one_left _, pol_one o, a, a', ha, ha', haa, heq⟩, ?_⟩
    intro k _ _ x β hβ
    obtain ⟨I, hI⟩ := o.geom k x β hβ
    have hInt : UpperTheory.Gal.Int.Geo.Integ L 1 := UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)
    refine ⟨I, I, hI, fun y => ?_, ?_⟩
    · show toUnit _ ≫ o.eta (c • y) = _
      rw [hI, gTateIso_ev_nsmul', I.tower _ _ hN hc]
    · exact (hR p D G L R gb S s _ _ _ o o o k x I I I (𝟙 _) (𝟙 _) 1 1 hmon hmon hInt).1
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PAdmOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

private theorem conj_core {V : Type*} [AddCommGroup V] [Module ℚ V] (H U Hi : V →+ V) {k N : ℕ} (hk : 0 < k) {v w : V}
    (hv : H (Hi v) = v) (e : U (k • Hi v) = k • Hi v + (N * k) • w) : H (U (Hi v)) = v + N • H w := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk.ne'
  have h1 := congrArg H e
  simp only [map_nsmul, map_add (f := _), hv] at h1
  have h2 : k • H (U (Hi v)) = k • (v + N • H w) := by
    rw [h1, smul_add, mul_comm N k, mul_smul]
  rw [← Nat.cast_smul_eq_nsmul ℚ k, ← Nat.cast_smul_eq_nsmul ℚ k] at h2
  exact MulAction.injective₀ hk' h2

private theorem congOne_conj {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) {h u : G.GAf} {k N : ℕ}
    (hI : Integ L h) (hk : 0 < k) (hinv : ∀ v ∈ LaHat D, k • L.actG h⁻¹ v ∈ LaHat D) (hu : L.CongOne (N * k) u) :
    L.CongOne N (h * u * h⁻¹) := by
  intro v hv
  obtain ⟨w, hw, e⟩ := hu _ (hinv v hv)
  refine ⟨L.actG h w, hI w hw, ?_⟩
  have hhv : L.actG h (L.actG h⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have := conj_core (L.actG h).toAddMonoidHom (L.actG u).toAddMonoidHom (L.actG h⁻¹).toAddMonoidHom hk (v := v) (w := w) hhv e
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  exact this

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pAdmOf :
    AdmOf := by
  intro p _ D G L h k N hI hk hinv u hu
  refine ⟨congOne_conj L hI hk hinv hu.1, ?_⟩
  have e : (h * u * h⁻¹)⁻¹ = h * u⁻¹ * h⁻¹ := by group
  rw [e]
  exact congOne_conj L hI hk hinv hu.2
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransKer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

section

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {R : Type} [CommRing R] [Algebra ℚ R]
  {gb : GBase D.toG R} {S : Scheme.{0}} {s : S ⟶ Sp R}

private theorem comp_pow_overScheme_grpObj {A T T' : Over S} [GrpObj A] (f : T' ⟶ T) (x : T ⟶ A) (n : ℕ) :
    f ≫ x ^ n = (f ≫ x) ^ n := MonObj.comp_pow x n f

private theorem pow_comp_monHom_overScheme_grpObj {A B T : Over S} [GrpObj A] [GrpObj B] (φ : A ⟶ B) [IsMonHom φ] (x : T ⟶ A) (n : ℕ) :
    (x ^ n) ≫ φ = (x ≫ φ) ^ n := MonObj.pow_comp x n φ

private theorem pt_transfer {N' N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {o : GObj gb N' s} {o₁ o₂ : GObj gb N s}
    {ψ₁ : o.A ⟶ o₁.A} {ψ₂ : o.A ⟶ o₂.A} {ψ' : o₁.A ⟶ o.A} {d : ℕ} (hψ' : IsMonHom ψ')
    (hd : ψ₁ ≫ ψ' = (𝟙 o.A) ^ d) (hdp : d.Coprime p) {h : G.GAf} {k : Type} [Field k] {t : Sp k ⟶ S}
    (I : UpperTheory.Gal.Int.Geo.TIso o t) (J₁ : UpperTheory.Gal.Int.Geo.TIso o₁ t) (J₂ : UpperTheory.Gal.Int.Geo.TIso o₂ t)
    (H₁ : Rel L I J₁ ψ₁ h) (H₂ : Rel L I J₂ ψ₂ h) (a : Over.mk t ⟶ o.A) (y : D.La)
    (ha : a ≫ ψ₁ = J₁.ev N y) : a ≫ ψ₂ = J₂.ev N y := by
  haveI := hψ'
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · rw [Nat.coprime_zero_left] at hdp
      exact absurd hdp (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  have hn : 0 < N * d := Nat.mul_pos hN hd0
  have hnp : (N * d).Coprime p := Nat.Coprime.mul_left hNp hdp
  have h1 : (a ≫ ψ₁) ^ N = 1 := by
    rw [ha]
    exact (J₁.onto N hN _).mpr ⟨y, rfl⟩
  have h2 : a ^ d = (a ≫ ψ₁) ≫ ψ' := by
    rw [Category.assoc, hd, comp_pow_overScheme_grpObj, Category.comp_id]
  have h3 : a ^ (N * d) = 1 := by
    rw [mul_comm, pow_mul, h2, ← pow_comp_monHom_overScheme_grpObj, h1, MonObj.one_comp]
  obtain ⟨x, hx⟩ := (I.onto (N * d) hn a).mp h3
  let y' : D.toG.La := y
  have hJ₁ : J₁.ev N y' = J₁.ev (N * d) (d • y') := by
    rw [HeckeRestrict.ev_nsmul, J₁.tower N d hN hd0]
  have hJ₂ : J₂.ev N y' = J₂.ev (N * d) (d • y') := by
    rw [HeckeRestrict.ev_nsmul, J₂.tower N d hN hd0]
  change a ≫ ψ₁ = J₁.ev N y' at ha
  change a ≫ ψ₂ = J₂.ev N y'
  rw [← hx] at ha ⊢
  rw [hJ₂]
  rw [hJ₁] at ha
  exact (H₂ (N * d) hn hnp x (d • y')).mpr ((H₁ (N * d) hn hnp x (d • y')).mp ha)

end

theorem UpperTheory.Gal.G3.pTransKer :
    RelComp → TateDiff → TateTwist → TransKer := by
  intro RC TD TT p _ D G L R _ _ gb S s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm T₁ T₂ k _ _ t
  let β : R →+* k := (Spec.preimage (t ≫ s)).hom
  have hβ : t ≫ s = spMap β := by
    simp [β, spMap, Spec.map_preimage]
  have key : ∀ (q₁ q₂ : GObj gb (↑N) s) (φ₁ : o.A ⟶ q₁.A) (φ₂ : o.A ⟶ q₂.A),
      IsTrans L h o q₁ φ₁ → IsTrans L h o q₂ φ₂ → ∀ (a : Over.mk t ⟶ o.A) (y : D.La),
      a ≫ φ₁ = toUnit (Over.mk t) ≫ q₁.eta y → a ≫ φ₂ = toUnit (Over.mk t) ≫ q₂.eta y := by
    intro q₁ q₂ φ₁ φ₂ U₁ U₂ a y ha
    obtain ⟨-, -, ⟨φ', d, hφ', -, hd, -, hdp⟩, -, tate₁⟩ := U₁
    obtain ⟨hmon₂, -, -, -, tate₂⟩ := U₂
    obtain ⟨I₁, J₁, hI₁, hJ₁, R₁⟩ := tate₁ k t β hβ
    obtain ⟨I₂, J₂, hI₂, hJ₂, R₂⟩ := tate₂ k t β hβ
    obtain ⟨u, hu, hR⟩ := TD p D G L R gb S s N' o k t I₁ I₂ hI₁ hI₂
    have hc₁ := (RC p D G L R gb S s (↑N') (↑N') (↑N) o o q₂ k t I₁ I₂ J₂ (𝟙 _) φ₂ u h
      inferInstance hmon₂ hint).2 hR R₂
    have hw : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hadm _ (Subgroup.inv_mem _ hu)
    obtain ⟨J₃, hJ₃, hR₃⟩ := TT p D G L R gb S s N q₂ k t J₂ hJ₂ _ hw
    have hwi : Integ L (h * u⁻¹ * h⁻¹) :=
      UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hw)
    have hc₂ := (RC p D G L R gb S s (↑N') (↑N) (↑N) o q₂ q₂ k t I₁ J₂ J₃ (𝟙 _ ≫ φ₂) (𝟙 _) (h * u) _
      inferInstance inferInstance hwi).2 hc₁ hR₃
    have hg : h * u⁻¹ * h⁻¹ * (h * u) = h := by group
    rw [hg, Category.id_comp, Category.comp_id] at hc₂
    have hN : 0 < (N : ℕ) := lt_of_lt_of_le (by norm_num) N.2.1
    rw [hJ₁ y] at ha
    rw [hJ₃ y]
    exact pt_transfer hN N.2.2 hφ' hd hdp I₁ J₁ J₃ R₁ hc₂ a y ha
  have hz : ∀ q : GObj gb (↑N) s, toUnit (Over.mk t) ≫ q.eta (0 : D.La) = 1 := by
    intro q
    rw [show q.eta (0 : D.La) = 1 from q.eta_zero, MonObj.comp_one]
  refine ⟨fun a => ⟨fun h1 => ?_, fun h2 => ?_⟩, fun a y => ⟨key o₁ o₂ ψ₁ ψ₂ T₁ T₂ a y, key o₂ o₁ ψ₂ ψ₁ T₂ T₁ a y⟩⟩
  · have := key o₁ o₂ ψ₁ ψ₂ T₁ T₂ a 0 (by rw [h1, hz])
    rwa [hz] at this
  · have := key o₂ o₁ ψ₂ ψ₁ T₂ T₁ a 0 (by rw [h2, hz])
    rwa [hz] at this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtOrbit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem exists_comp {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} {e : S₁ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g)
    (he : f ≫ g = e) : ∃ m : GObjMap o₁ o₃ e, m.φ = h₁.φ ≫ h₂.φ := by
  subst he
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol
      (GlobalTheory.UPel.HT.MapComp.lbIso_pull_comp h₂.pol h₁.φ₂ rfl)
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

theorem UpperTheory.Gal.G3.pPtOrbit :
    TransComp → TransPull → TransOfMap → TransOrbit → Rigid → PtOrbit := by
  intro hC hP hM hO hRg p _ D G L R _ _ gb N' N X' X π Φ w k _ _ x y hxy
  obtain ⟨e, o, ψ, φ, tψ, rfl⟩ := w
  have hs : y ≫ X'.s = x ≫ X'.s := by rw [← e, ← Category.assoc, ← hxy, Category.assoc]
  obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl X'.univ
  obtain ⟨oy, ⟨my⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) y hs X'.univ
  obtain ⟨ox', ⟨nx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl o
  obtain ⟨oy', ⟨ny⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) y hs o
  refine ⟨ox, oy, mx, my, hs, ?_⟩
  obtain ⟨ψx, tx, cx⟩ := hP p D G L R gb X'.X (Sp k) X'.s (x ≫ X'.s) x rfl _ _ X'.univ o ox ox' mx nx ψ 1 tψ
  obtain ⟨ψy, ty, cy⟩ := hP p D G L R gb X'.X (Sp k) X'.s (x ≫ X'.s) y hs _ _ X'.univ o oy oy' my ny ψ 1 tψ
  obtain ⟨A, hA⟩ := exists_comp nx φ (rfl : x ≫ π = x ≫ π)
  obtain ⟨B, hB⟩ := exists_comp ny φ hxy.symm
  obtain ⟨A', hA'⟩ := exists_comp nx φ (Category.id_comp (x ≫ π)).symm
  obtain ⟨c⟩ := BaseChange.gObjMap_cancel (f := 𝟙 (Sp k)) A' B
  obtain ⟨θ', hθ', tθ'⟩ := hM p D G L R gb (Sp k) (x ≫ X'.s) N ox' oy' c
  have i1 : Integ L 1 := UpperTheory.Gal.Int.Geo.integ_of_mem (L.KN 1).one_mem
  have a1 : AdmK L N N 1 := fun v hv => by simpa using hv
  have t₂ := hC p D G L R gb (Sp k) (x ≫ X'.s) N' N N ox ox' oy' ψx θ' 1 1 i1 a1 tx tθ'
  rw [_root_.mul_one] at t₂
  obtain ⟨u, hu, θ, tθ, hθ⟩ := hO p D G L R gb k (x ≫ X'.s) N' N ox oy oy' (ψx ≫ θ') ψy t₂ ty
  refine ⟨u, hu, θ, tθ, ?_⟩
  have hr := hRg p D R gb X.X (Sp k) X.s (x ≫ X'.s) (x ≫ π) (by rw [Category.assoc, e]) N X.univ ox'
  obtain ⟨C, hC'⟩ := exists_comp c B (Category.id_comp (x ≫ π))
  have key : c.φ ≫ ny.φ ≫ φ.φ = nx.φ ≫ φ.φ := by
    have := hr C A
    rw [hC', hB, hA] at this
    exact this
  calc Over.Hom.left θ ≫ my.φ ≫ Over.Hom.left ψ ≫ φ.φ
      = Over.Hom.left θ ≫ (my.φ ≫ Over.Hom.left ψ) ≫ φ.φ := by rw [Category.assoc]
    _ = Over.Hom.left (θ ≫ ψy) ≫ ny.φ ≫ φ.φ := by rw [← cy]; simp
    _ = Over.Hom.left ψx ≫ c.φ ≫ ny.φ ≫ φ.φ := by rw [hθ, Over.comp_left, hθ', Category.assoc]
    _ = Over.Hom.left ψx ≫ nx.φ ≫ φ.φ := by rw [key]
    _ = mx.φ ≫ Over.Hom.left ψ ≫ φ.φ := by rw [← Category.assoc, cx, Category.assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRigid
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt)
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor GlobalTheory.CechPic GlobalTheory.AmpleRigid
open scoped TensorProduct CategoryTheory.Obj
universe u

private theorem diag_fst {S : Scheme.{0}} (A : Over S) :
    (lift (𝟙 A) (𝟙 A)).left ≫ (fst A A).left = 𝟙 A.left := by
  rw [← Over.comp_left, lift_fst]
  rfl

private theorem diag_snd {S : Scheme.{0}} (A : Over S) :
    (lift (𝟙 A) (𝟙 A)).left ≫ (snd A A).left = 𝟙 A.left := by
  rw [← Over.comp_left, lift_snd]
  rfl

section

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase G R} {N : ℕ} {S S' : Scheme.{0}}
  {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {o : GObj gb N s} {o' : GObj gb N s'} {f : S' ⟶ S}

private theorem tensor_left_hom_ext_of_fst_snd {S : Scheme.{0}} {X Y : Over S} {W : Scheme.{0}} {u v : W ⟶ (X ⊗ Y).left}
    (h₁ : u ≫ (fst X Y).left = v ≫ (fst X Y).left) (h₂ : u ≫ (snd X Y).left = v ≫ (snd X Y).left) : u = v := by
  have hw : u ≫ (X ⊗ Y).hom = v ≫ (X ⊗ Y).hom := by
    rw [← Over.w (fst X Y), ← Category.assoc, h₁, Category.assoc]
  let U : Over.mk (u ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y := Over.homMk u
  let V : Over.mk (u ≫ (X ⊗ Y).hom) ⟶ X ⊗ Y := Over.homMk v hw.symm
  have hUV : U = V := by
    apply CartesianMonoidalCategory.hom_ext
    · exact Over.OverMorphism.ext (by simpa [U, V] using h₁)
    · exact Over.OverMorphism.ext (by simpa [U, V] using h₂)
  exact congrArg CommaMorphism.left hUV

private theorem map_diag (m : GObjMap o' o f) :
    (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ m.φ₂ = m.φ ≫ (lift (𝟙 o.A) (𝟙 o.A)).left := by
  apply tensor_left_hom_ext_of_fst_snd
  · have key : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (fst o'.A o'.A).left ≫ m.φ = m.φ := by
      rw [← Category.assoc, diag_fst, Category.id_comp]
    rw [Category.assoc, m.sq.1, key, Category.assoc, diag_fst, Category.comp_id]
  · have key : (lift (𝟙 o'.A) (𝟙 o'.A)).left ≫ (snd o'.A o'.A).left ≫ m.φ = m.φ := by
      rw [← Category.assoc, diag_snd, Category.id_comp]
    rw [Category.assoc, m.sq.2, key, Category.assoc, diag_snd, Category.comp_id]

private theorem pull_diag_cls (m : GObjMap o' o f) :
    pull m.φ (cls (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (pull_isLB o.isLB _)) =
      cls (o'.P.pull (lift (𝟙 o'.A) (𝟙 o'.A)).left) (pull_isLB o'.isLB _) := by
  rw [cls_pull o.isLB, cls_pull o'.isLB, ← pull_comp, ← map_diag m, pull_comp,
    ← cls_pull o.isLB _ (pull_isLB o.isLB m.φ₂),
    (cls_eq_iff (pull_isLB o.isLB m.φ₂) o'.isLB).2 (LBIso.symm m.pol)]

private theorem eq_at_point (hN : 3 ≤ N) (m m' : GObjMap o' o f) {K : Type} [Field K] [IsAlgClosed K] (j : Sp K ⟶ S') :
    pullback.fst o'.A.hom j ≫ m.φ = pullback.fst o'.A.hom j ≫ m'.φ := by
  have hA' : IsAbelianScheme ((Over.pullback j).obj o'.A) := by
    haveI := o'.ab.comm
    haveI := o'.ab.smooth
    haveI := o'.ab.proper
    haveI := o'.ab.geomConnected
    constructor
    · infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
    · dsimp; infer_instance
  have c := (isGrpPullback_pullback o'.A j).comp m.cart
  have c' := (isGrpPullback_pullback o'.A j).comp m'.cart
  refine GlobalTheory.SiegRigid.eq_of_field (pull_isLB o.isLB _) o.ample hA' c c' ?_ hN ?_ ?_
  · rw [pull_comp, pull_comp, pull_diag_cls m, pull_diag_cls m']
  · intro h0
    let ψ : ℚ →+* K := (Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of K) (j ≫ s')).hom.comp
      (algebraMap ℚ R)
    have e0 : ψ (N : ℚ) = ψ 0 := by rw [map_natCast, map_zero]; exact h0
    have e1 : (N : ℚ) = 0 := ψ.injective e0
    norm_cast at e1
    omega
  · intro Ω _ _ t x hx
    let β : R →+* Ω := (Spec.preimage (R := CommRingCat.of R) (S := CommRingCat.of Ω) ((t ≫ j) ≫ s')).hom
    have hβ : (t ≫ j) ≫ s' = spMap β := by
      simp only [spMap, β, CommRingCat.ofHom_hom, Spec.map_preimage]
    obtain ⟨I, hI⟩ := o'.geom Ω (t ≫ j) β hβ
    let x₁ := pushHom (isGrpPullback_pullback o'.A j) (Over.mk t) x
    have hx₁ : x₁ ^ N = 1 := by
      simp only [x₁]
      rw [← map_pow, hx, map_one]
    obtain ⟨y, hy⟩ := (I.onto N (by omega) x₁).1 hx₁
    have hl : x.left ≫ pullback.fst o'.A.hom j = x₁.left := rfl
    have key : ∀ mm : GObjMap o' o f, x.left ≫ pullback.fst o'.A.hom j ≫ mm.φ =
        (toUnit (Over.mk (t ≫ j))).left ≫ f ≫ (o.eta y).left := by
      intro mm
      rw [← Category.assoc, hl, ← hy, ← hI y, Over.comp_left, Category.assoc, mm.eta y]
    rw [key m, key m']

end

theorem UpperTheory.Gal.G3.pRigid :
    Rigid := by
  intro p _ D R _ _ gb S S' s s' f hf N o o' m m'
  have hN : 3 ≤ (N : ℕ) := N.2.1
  obtain ⟨σ, hσmon, hσ⟩ := GlobalTheory.SiegRigid.exists_aut m.cart m'.cart
  have hid : σ.hom = 𝟙 o'.A := by
    refine GlobalTheory.eq_id_of_forall_geometric_fibre GlobalTheory.laws_without_cohomology.1 o'.A o'.ab σ.hom
      (IsMonHom.one_hom σ.hom) ?_
    intro t
    let K := AlgebraicClosure (S'.residueField t)
    let j : Sp K ⟶ S' := Spec.map (CommRingCat.ofHom (algebraMap (S'.residueField t) K)) ≫
      S'.fromSpecResidueField t
    refine ⟨Sp K, pullback o'.A.hom j, j, pullback.fst o'.A.hom j, pullback.snd o'.A.hom j,
      IsLocalRing.closedPoint K, ?_, IsPullback.of_hasPullback _ _, ?_⟩
    · exact Scheme.fromSpecResidueField_apply t _
    · apply m'.cart.1.hom_ext
      · rw [Category.assoc, hσ, eq_at_point hN m m' j]
      · rw [Category.assoc, Over.w]
  rw [← hσ, hid, Over.id_left, Category.id_comp]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSigmaFEt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem exists_sigma_point {W : Scheme.{0}} {I : Type} (K : Type) [Field K]
    (y : Spec (CommRingCat.of K) ⟶ ∐ fun _ : I => W) :
    ∃ (i : I) (y' : Spec (CommRingCat.of K) ⟶ W), y' ≫ Sigma.ι (fun _ : I => W) i = y := by
  obtain ⟨pt⟩ : Nonempty (Spec (CommRingCat.of K)) := inferInstance
  obtain ⟨⟨i, w⟩, hw⟩ := (sigmaMk (fun _ : I => W)).surjective (y pt)
  rw [sigmaMk_mk] at hw
  refine ⟨i, IsOpenImmersion.lift (Sigma.ι (fun _ : I => W) i) y ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨q, rfl⟩
  rw [Subsingleton.elim q pt]
  exact ⟨w, hw⟩

private theorem card_sigma_fibre {Y Z : Scheme.{0}} (s : Y ⟶ Z) (I : Type) (K : Type) [Field K]
    (x : Spec (CommRingCat.of K) ⟶ Z) :
    Nat.card {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} =
      Nat.card I * Nat.card {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} := by
  let F : I × {y' : Spec (CommRingCat.of K) ⟶ Y // y' ≫ s = x} →
      {y : Spec (CommRingCat.of K) ⟶ ∐ (fun _ : I => Y) // y ≫ (Sigma.desc fun _ : I => s) = x} :=
    fun q => ⟨q.2.1 ≫ Sigma.ι (fun _ : I => Y) q.1, by
      rw [Category.assoc, Sigma.ι_desc]
      exact q.2.2⟩
  have hF : Function.Bijective F := by
    constructor
    · rintro ⟨i, a, ha⟩ ⟨j, b, hb⟩ h
      have h' : a ≫ Sigma.ι (fun _ : I => Y) i = b ≫ Sigma.ι (fun _ : I => Y) j :=
        congrArg Subtype.val h
      by_cases hij : i = j
      · subst hij
        have hab : a = b := (cancel_mono _).mp h'
        subst hab
        rfl
      · exfalso
        have hE := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : I => Y) ⟨h'⟩ hij
        obtain ⟨p⟩ := (inferInstance : Nonempty (Spec (CommRingCat.of K)))
        exact hE.false p
    · rintro ⟨y, hy⟩
      obtain ⟨i, y', rfl⟩ := exists_sigma_point K y
      refine ⟨⟨i, y', ?_⟩, rfl⟩
      rw [Category.assoc, Sigma.ι_desc] at hy
      exact hy
  rw [← Nat.card_congr (Equiv.ofBijective F hF), Nat.card_prod]

theorem UpperTheory.Gal.G3.pSigmaFEt :
    SigmaFEt := by
  intro Y Z s d I _ hs
  obtain ⟨hfin, het, hcard⟩ := hs
  obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin I
  have hid : IsFinite (Sigma.desc fun _ : I => 𝟙 Y) := by
    have h1 := GlobalTheory.Et.TrivTors.isFinite_sigmaDesc_fin Y n
    have h2 : IsFinite ((Sigma.reindex e (fun _ : Fin n => Y)).hom ≫
        Sigma.desc fun _ : Fin n => 𝟙 Y) := inferInstance
    have h3 : (Sigma.desc fun _ : I => 𝟙 Y) =
        (Sigma.reindex e (fun _ : Fin n => Y)).hom ≫ Sigma.desc fun _ : Fin n => 𝟙 Y := by
      refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
      rw [Sigma.ι_desc, ← Category.assoc]
      erw [Sigma.ι_reindex_hom (f := fun _ : Fin n => Y) e i]
      rw [Sigma.ι_desc]
    rw [h3]
    exact h2
  have hfac : (Sigma.desc fun _ : I => s) = (Sigma.desc fun _ : I => 𝟙 Y) ≫ s := by
    refine Sigma.hom_ext (f := fun _ : I => Y) _ _ fun i => ?_
    simp
  have hloc : IsZariskiLocalAtSource @Etale.{0} := HasRingHomProperty.instIsZariskiLocalAtSource
  refine ⟨?_, ?_, ?_⟩
  · rw [hfac]
    infer_instance
  · exact IsZariskiLocalAtSource.sigmaDesc (P := @Etale.{0}) fun _ => het
  · intro K _ _ x
    rw [card_sigma_fibre, hcard]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PQuotUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private lemma twisted_kernel_forms_nonvanishing (hE : EtDesc) (k : Type) [Field k] [IsAlgClosed k] (A A₁ A₂ : Over (Sp k)) [GrpObj A]
    [GrpObj A₁] [GrpObj A₂] (hA : IsAbelianScheme A) (hA₂ : IsAbelianScheme A₂)
    (ψ₁ : A ⟶ A₁) (ψ₂ : A ⟶ A₂) [IsMonHom ψ₁] [IsMonHom ψ₂] [IsFinite ψ₁.left] [Etale ψ₁.left] [Surjective ψ₁.left]
    (hker : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (t : Sp Ω ⟶ Sp k) (a : Over.mk t ⟶ A), a ≫ ψ₁ = 1 → a ≫ ψ₂ = 1) :
    ∃ θ : A₁ ⟶ A₂, ψ₁ ≫ θ = ψ₂ := by
  haveI := hA.smooth
  haveI := hA₂.proper
  haveI : AlgebraicGeometry.IsReduced A.left := GlobalTheory.isReduced_of_smooth_of_isReduced A.hom
  have hw : ψ₂.left ≫ A₂.hom = ψ₁.left ≫ A₁.hom := by rw [Over.w, Over.w]
  obtain ⟨hepi, g, hg⟩ := hE ψ₁.left A₁.hom A₂.hom ψ₂.left hw (by
    intro Ω _ _ x y hxy
    have hxy' : x ≫ A.hom = y ≫ A.hom := by
      rw [← Over.w ψ₁, ← Category.assoc, hxy, Category.assoc]
    let X : Over.mk (x ≫ A.hom) ⟶ A := Over.homMk x
    let Y : Over.mk (x ≫ A.hom) ⟶ A := Over.homMk y hxy'.symm
    have h1 : X ≫ ψ₁ = Y ≫ ψ₁ := Over.OverMorphism.ext hxy
    have h2 : (X * Y⁻¹) ≫ ψ₁ = 1 := by
      have e := (IsMonHom.monoidHom ψ₁ (Over.mk (x ≫ A.hom))).map_mul X Y⁻¹
      have e' := map_inv (IsMonHom.monoidHom ψ₁ (Over.mk (x ≫ A.hom))) Y
      simp only [IsMonHom.monoidHom_apply] at e e'
      rw [e, e', h1, mul_inv_cancel]
    have h3 := hker Ω (x ≫ A.hom) (X * Y⁻¹) h2
    have e := (IsMonHom.monoidHom ψ₂ (Over.mk (x ≫ A.hom))).map_mul X Y⁻¹
    have e' := map_inv (IsMonHom.monoidHom ψ₂ (Over.mk (x ≫ A.hom))) Y
    simp only [IsMonHom.monoidHom_apply] at e e'
    rw [e, e', mul_inv_eq_one] at h3
    exact congrArg CommaMorphism.left h3)
  haveI := hepi
  refine ⟨Over.homMk g ?_, ?_⟩
  · rw [← cancel_epi ψ₁.left, ← Category.assoc, hg, hw]
  · exact Over.OverMorphism.ext hg

theorem UpperTheory.Gal.G3.pQuotUniq :
    EtDesc → QuotUniq := by
  intro hE k _ _ A A₁ A₂ _ _ _ _ _ _ hA hA₁ hA₂ ψ₁ ψ₂ h₁ h₂ f₁ e₁ s₁ f₂ e₂ s₂ hker
  obtain ⟨θ, hθ⟩ := twisted_kernel_forms_nonvanishing hE k A A₁ A₂ hA hA₂ ψ₁ ψ₂ (fun Ω _ _ t a => (hker Ω t a).1)
  obtain ⟨θ', hθ'⟩ := twisted_kernel_forms_nonvanishing hE k A A₂ A₁ hA hA₁ ψ₂ ψ₁ (fun Ω _ _ t a => (hker Ω t a).2)
  haveI : Flat ψ₁.left := inferInstance
  haveI : Flat ψ₂.left := inferInstance
  haveI : Epi ψ₁ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ₁
  haveI : Epi ψ₂ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ₂
  haveI : Epi (ψ₁ ⊗ₘ ψ₁) := GlobalTheory.FlatQuotient.epi_tensorHom ψ₁ ψ₁
  have i1 : θ ≫ θ' = 𝟙 _ := by
    rw [← cancel_epi ψ₁, ← Category.assoc, hθ, hθ', Category.comp_id]
  have i2 : θ' ≫ θ = 𝟙 _ := by
    rw [← cancel_epi ψ₂, ← Category.assoc, hθ', hθ, Category.comp_id]
  refine ⟨θ, ⟨θ', i1, i2⟩, ⟨?_, ?_⟩, hθ⟩
  · rw [← IsMonHom.one_hom ψ₁, Category.assoc, hθ, IsMonHom.one_hom ψ₂]
  · have h1 : (ψ₁ ⊗ₘ ψ₁) ≫ (θ ⊗ₘ θ) = ψ₂ ⊗ₘ ψ₂ := by
      rw [tensorHom_comp_tensorHom, hθ]
    rw [← cancel_epi (ψ₁ ⊗ₘ ψ₁), ← Category.assoc, ← IsMonHom.mul_hom ψ₁, Category.assoc, hθ,
      IsMonHom.mul_hom ψ₂, ← Category.assoc, h1]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pow_push {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [GrpObj G] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (d : ℕ) :
    ((𝟙 G') ^ d : G' ⟶ G').left ≫ φ = φ ≫ ((𝟙 G) ^ d : G ⟶ G).left := by
  obtain ⟨hpb, hm⟩ := h
  have hw : φ ≫ G.hom = G'.hom ≫ f := hpb.w
  let P : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk φ (by simpa using hw)
  have key : ∀ n : ℕ, ((𝟙 G') ^ n : G' ⟶ G').left ≫ φ = (P ^ n).left := by
    intro n
    induction n with
    | zero =>
      let x₀ : Over.mk (G'.hom ≫ f) ⟶ G := Over.homMk ((1 : G' ⟶ G').left ≫ φ)
        (by rw [Category.assoc, hw, ← Category.assoc, Over.w]; rfl)
      have e : (x₀ * x₀).left = x₀.left := by
        rw [hm G' 1 1 x₀ x₀ rfl rfl, _root_.mul_one (1 : G' ⟶ G')]
        rfl
      have e2 : x₀ * x₀ = x₀ := Over.OverMorphism.ext e
      have e3 : x₀ = 1 := by simpa using e2
      rw [pow_zero, pow_zero]
      exact congrArg CommaMorphism.left e3
    | succ n ih =>
      rw [pow_succ, pow_succ, ← hm G' _ _ (P ^ n) P ih.symm (by simp [P])]
  rw [key d]
  have hP : P ≫ ((𝟙 G) ^ d) = P ^ d := by rw [MonObj.comp_pow, Category.comp_id]
  rw [← hP]
  rfl

private theorem qinv_pull {S S' : Scheme.{0}} {A₁' A₂' : Over S'} {A₁ A₂ : Over S} [GrpObj A₁'] [GrpObj A₁] {f : S' ⟶ S}
    {φ₁ : A₁'.left ⟶ A₁.left} {φ₂ : A₂'.left ⟶ A₂.left} (c₁ : IsGrpPullback A₁' A₁ f φ₁) {ψ : A₁ ⟶ A₂} {χ : A₂ ⟶ A₁}
    {ψ' : A₁' ⟶ A₂'} {χ' : A₂' ⟶ A₁'} (e : ψ'.left ≫ φ₂ = φ₁ ≫ ψ.left) (e' : χ'.left ≫ φ₁ = φ₂ ≫ χ.left) {d : ℕ}
    (h : ψ ≫ χ = (𝟙 A₁) ^ d) : ψ' ≫ χ' = (𝟙 A₁') ^ d := by
  apply Over.OverMorphism.ext
  apply c₁.1.hom_ext
  · rw [Over.comp_left, Category.assoc, e', ← Category.assoc, e, Category.assoc, ← Over.comp_left, h, pow_push c₁]
  · rw [Over.w, Over.w]

theorem UpperTheory.Gal.G3.pTransPull :
    HomPull → TatePull → TransPull := by
  intro hHom hTate p _ D G L R _ _ gb S S' s s' f hf N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ h hT
  obtain ⟨hmon, hact, ⟨χ, d, hχmon, hχact, e1, e2, hd⟩, ⟨c, hc, ⟨lb⟩, tt⟩, hgeo⟩ := hT
  obtain ⟨ψ', hψ, hmon', hact', hlb'⟩ := hHom D.toG R gb S S' s s' f N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ
  obtain ⟨χ', hχ, hχmon', hχact', -⟩ := hHom D.toG R gb S S' s s' f N₂ N₁ o₂ o₁ o₂' o₁' m₂ m₁ χ
  refine ⟨ψ', ⟨hmon' hmon, hact' hact, ⟨χ', d, hχmon' hχmon, hχact' hχact, qinv_pull m₁.cart hψ hχ e1,
    qinv_pull m₂.cart hχ hψ e2, hd⟩, ⟨c, hc, hlb' c ⟨lb⟩, tt⟩, ?_⟩, hψ⟩
  intro k _ _ t β ht
  obtain ⟨I₁, I₂, hI₁, hI₂, hev⟩ := hgeo k (t ≫ f) β (by rw [Category.assoc, hf, ht])
  obtain ⟨I₁', hI₁', hev₁⟩ := (hTate p D R gb S S' s s' f N₁ o₁ o₁' m₁ k t).1 I₁
  obtain ⟨I₂', hI₂', hev₂⟩ := (hTate p D R gb S S' s s' f N₂ o₂ o₂' m₂ k t).1 I₂
  refine ⟨I₁', I₂', hI₁' hI₁, hI₂' hI₂, fun n hn hnp x y => ?_⟩
  rw [← hev n hn hnp x y]
  constructor
  · intro e
    apply Over.OverMorphism.ext
    have key := congrArg (fun a => a.left ≫ m₂.φ) e
    simp only [Over.comp_left, Category.assoc, hψ] at key
    erw [← Category.assoc, hev₁ n x, hev₂ n y] at key
    rw [Over.comp_left]
    exact key
  · intro e
    apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hψ, ← Category.assoc]
      erw [hev₁ n x, hev₂ n y]
      rw [← Over.comp_left, e]
    · rw [Over.w, Over.w]
end


section -- merged from Development.AutomorphicArithmetic.CommutativeAlgebra.ExistsGTateIsoTwistOfSimilitude
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen UpperTheory.Lev

namespace UpperTheory.Lev

section Twist

variable {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q}
  {e : ℕ → Q → Q → kˣ → Prop}

private theorem ev_MN (I : GTateIso G k Q act e) {n : ℕ} (hn : 0 < n) {a b : G.La} (h : MN n a b) :
    I.ev n a = I.ev n b := by
  obtain ⟨c, rfl⟩ := h
  rw [I.add, (I.ker n hn (n • c)).2 ⟨c, rfl⟩, _root_.mul_one]

private theorem zpow_congr_of_dvd {u : kˣ} {n : ℕ} (hu : u ^ n = 1) {a b : ℤ} (h : (n : ℤ) ∣ a - b) :
    u ^ a = u ^ b := by
  obtain ⟨c, hc⟩ := h
  have hab : a = b + n * c := by linarith
  rw [hab, zpow_add, zpow_mul, zpow_natCast, hu, one_zpow, _root_.mul_one]

private theorem prim_zpow {u : kˣ} {n : ℕ} (hu : IsPrimitiveRoot u n) {v : ℤ}
    (hc : IsCoprime v (n : ℤ)) : IsPrimitiveRoot (u ^ v) n := by
  exact hu.zpow_of_gcd_eq_one v (Int.isCoprime_iff_gcd_eq_one.mp hc)

end Twist

end UpperTheory.Lev

theorem UpperTheory.exists_gTateIso_twist_of_similitude :
    ∀ {G : GDatum} {k : Type} [Field k] {Q : Type} [Group Q] {act : G.O → Q → Q} {e : ℕ → Q → Q → kˣ → Prop}
        (I : GTateIso G k Q act e) (g : GSim G),
        ∃ I' : GTateIso G k Q act e, ∀ n, 0 < n → ∀ x, I'.ev n x = I.ev n (g.f n x) := by
  intro G k _ Q _ act e I g
  have hφadd : ∀ n, 0 < n → ∀ x y, I.ev n (g.f n (x + y)) = I.ev n (g.f n x) * I.ev n (g.f n y) :=
    fun n hn x y => by rw [Lev.ev_MN I hn ((g.sim n hn).add x y), I.add]
  have hφpow : ∀ n, 0 < n → ∀ (j : ℕ) y, I.ev n (g.f n (j • y)) = I.ev n (g.f n y) ^ j := by
    intro n hn j y
    induction j with
    | zero =>
      rw [zero_smul, pow_zero]
      have h0 := hφadd n hn 0 0
      rw [add_zero] at h0
      exact (mul_eq_left.mp h0.symm)
    | succ j ih => rw [succ_nsmul, hφadd n hn, ih, pow_succ]
  refine ⟨⟨fun n => I.ζ n ^ g.ν n, ?_, ?_, fun n x => if n = 0 then I.ev 0 x else I.ev n (g.f n x),
    ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro n hn
    exact Lev.prim_zpow (I.ζ_prim n hn) (g.sim n hn).cop
  · intro n m hn hm
    rw [← zpow_natCast, ← zpow_mul, mul_comm (g.ν _), zpow_mul, zpow_natCast, I.ζ_pow n m hn hm]
    exact Lev.zpow_congr_of_dvd (I.ζ_prim n hn).pow_eq_one (g.νtower n m hn hm)
  · intro n x y
    by_cases hn : n = 0
    · simp only [hn, if_true, I.add]
    · simp only [hn, if_false]
      exact hφadd n (Nat.pos_of_ne_zero hn) x y
  · intro n b x
    by_cases hn : n = 0
    · simp only [hn, if_true, I.lin]
    · simp only [hn, if_false]
      rw [Lev.ev_MN I (Nat.pos_of_ne_zero hn) ((g.sim n (Nat.pos_of_ne_zero hn)).lin b x), I.lin]
  · intro n hn x
    simp only [hn.ne', if_false]
    constructor
    · intro h1
      obtain ⟨y, hy⟩ := (I.ker n hn _).mp h1
      obtain ⟨c, hc⟩ := (g.sim n hn).inj x ⟨y, by rw [hy, zero_add]⟩
      exact ⟨c, by rw [hc, zero_add]⟩
    · rintro ⟨y, rfl⟩
      rw [hφpow n hn]
      exact (I.onto n hn _).mpr ⟨_, rfl⟩
  · intro n hn q
    simp only [hn.ne', if_false]
    rw [I.onto n hn]
    constructor
    · rintro ⟨z, rfl⟩
      obtain ⟨x, hx⟩ := (g.sim n hn).surj z
      exact ⟨x, Lev.ev_MN I hn hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, rfl⟩
  · intro n m hn hm x
    simp only [(Nat.mul_pos hn hm).ne', hn.ne', if_false]
    rw [I.tower n m hn hm, Lev.ev_MN I hn (g.tower n m hn hm x)]
  · intro n hn x y
    simp only [hn.ne', if_false]
    have h := I.isom n hn (g.f n x) (g.f n y)
    have hd := ((g.sim n hn).isom x y)
    rw [Lev.zpow_congr_of_dvd (I.ζ_prim n hn).pow_eq_one hd] at h
    rw [← zpow_mul]
    exact h
  · intro n hn x
    simp only [hn.ne', if_false]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateWeilLocal
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.UPel.HT.HeckeAd

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd.TateTranslAt

open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.Hecke.TateTransl GlobalTheory.UPel.HT.HeckeAd.TateTranslSys

theorem exists_tateIsoO_of_given {p : ℕ} [Fact p.Prime] (D : Datum p) {R : Type} [CommRing R] (b : Base D R)
    (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ) (hcp : c.Coprime p) (hkp : k.Coprime p) (hN : 3 ≤ N)
    (hNp : N.Coprime p) (hck : c ∣ k ^ 2)
    (hlin : ∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z)
    (hcomp : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧
      (n : ℤ) ∣ u (n * m) - u n)
    (hsim : ∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧
      ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hsurj : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z)
    {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b (N * k) s) (A' : Over S) [GrpObj A'] [IsCommMonObj A']
    (act' : OActN D.O A') (ψ : o.A ⟶ A') (hA' : IsAbelianScheme A') (hψ : IsMonHom ψ)
    (hGal : GlobalTheory.ZM.IsGaloisCover (heckeSubA o (h (N * k)) N) (fun g => (transl g.1).left) ψ.left)
    (hact : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c') (P' : LB (G2 A').left) (hP' : P'.IsLB)
    (hiso : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) (P'.pull (GlobalTheory.UPel.HT.Hecke.sq2 ψ)))
    (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ S) (β : R →+* κ)
    (I : TateIsoO D κ (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
      (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)))
    (hI : ∀ y, toUnit _ ≫ o.eta y = I.ev (N * k) y) :
    ∃ I' : TateIsoO D κ (Over.mk x ⟶ A') (fun c g => g ≫ act'.act c)
        (fun n g g' z => Out.WeilIs A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) n g g' (unitOn z)),
      (∀ y, toUnit _ ≫ (o.eta (h (N * k) y) ≫ ψ) = I'.ev N y) ∧
      ∀ n, 0 < n → n.Coprime p → ∀ y, I'.ev n y = I.ev (n * k) (h (n * k) y) ≫ ψ := by
  haveI := D.freeLa
  have kpos : 0 < k := levelPos_of_coprime hkp
  have cpos : 0 < c := levelPos_of_coprime hcp
  have Npos : 0 < N := by omega
  let Ψ : (Over.mk x ⟶ o.A) →* (Over.mk x ⟶ A') :=
    MonoidHom.mk' (fun t => t ≫ ψ) (fun a a' => MonObj.mul_comp a a' ψ)
  have hΨ : ∀ t, Ψ t = t ≫ ψ := fun _ => rfl
  have hlev : ∀ n, 0 < n → n.Coprime p → ∀ w, I.ev (n * k) (n • w) = I.ev k w := fun n hn hnp w =>
    ev_mul_nsmul I n k hn kpos (Nat.Coprime.mul_left hkp hnp) w

  have hk_eq : ∀ n, 0 < n → n.Coprime p → ∀ z, I.ev k (h (n * k) z) = I.ev k (h k z) := by
    intro n hn hnp z
    obtain ⟨z', hz'⟩ := (hcomp k n kpos hn (Nat.Coprime.mul_left hkp hnp)).1 z
    rw [mul_comm n k, hz', I.add, (I.ker k kpos hkp (k • z')).2 ⟨z', rfl⟩, _root_.mul_one]
  have hker : ∀ t : Over.mk x ⟶ o.A, t ≫ ψ = 1 ↔ ∃ z, t = I.ev (N * k) (N • h (N * k) z) := by
    intro t
    constructor
    · intro ht
      have e1 : t.left ≫ ψ.left = (1 : Over.mk x ⟶ o.A).left ≫ ψ.left := by
        rw [← Over.comp_left, ← Over.comp_left, ht, MonObj.one_comp]
      obtain ⟨g, hg, -⟩ := hGal.fibre κ (1 : Over.mk x ⟶ o.A).left t.left e1.symm
      obtain ⟨z, hz⟩ := g.2
      refine ⟨z, ?_⟩
      have e2 : t = (1 : Over.mk x ⟶ o.A) ≫ transl g.1 :=
        Over.OverMorphism.ext (by rw [Over.comp_left]; exact hg.symm)
      rw [e2, one_comp_transl_pt, hz, hI]
    · rintro ⟨z, rfl⟩
      rw [← hI, Category.assoc, comp_eq_one_of_transl ψ (o.eta (N • h (N * k) z))
        (hGal.inv ⟨_, mem_heckeSubA o (h (N * k)) N z⟩), MonObj.comp_one]
  have hkerN : ∀ n, 0 < n → n.Coprime p → ∀ t : Over.mk x ⟶ o.A,
      t ≫ ψ = 1 ↔ ∃ z, t = I.ev (n * k) (n • h (n * k) z) := by
    intro n hn hnp t
    rw [hker]
    have e : ∀ z, I.ev (N * k) (N • h (N * k) z) = I.ev (n * k) (n • h (n * k) z) := fun z => by
      rw [hlev N Npos hNp, hk_eq N Npos hNp, hlev n hn hnp, hk_eq n hn hnp]
    simp only [e]
  have ker' : ∀ n, 0 < n → n.Coprime p → ∀ y, I.ev (n * k) (h (n * k) y) ≫ ψ = 1 ↔ ∃ z, y = n • z := by
    intro n hn hnp y
    have hnk : 0 < n * k := Nat.mul_pos hn kpos
    have hnkp : (n * k).Coprime p := Nat.Coprime.mul_left hnp hkp
    rw [hkerN n hn hnp]
    constructor
    · rintro ⟨z, hz⟩
      obtain ⟨v, hv⟩ := (ev_eq_iff I (n * k) hnk hnkp _ _).1 hz
      obtain ⟨z', hz'⟩ := exists_nsmul_of_map_eq D h u c k hcp hkp hcomp hsim hsurj n hn hnp (y - n • z) v
        (by rw [map_sub, map_nsmul, hv])
      exact ⟨z + z', by rw [smul_add, ← hz', add_sub_cancel]⟩
    · rintro ⟨z, rfl⟩
      exact ⟨z, by rw [map_nsmul]⟩
  have htor : ∀ n, 0 < n → n.Coprime p → ∀ y, (I.ev (n * k) (h (n * k) y) ≫ ψ) ^ n = 1 := by
    intro n hn hnp y
    rw [← hΨ, ← map_pow, hΨ, ← TateTransl.ev_nsmul, ← map_nsmul]
    exact (ker' n hn hnp (n • y)).2 ⟨y, rfl⟩
  have onto' : ∀ n, 0 < n → n.Coprime p → ∀ q : Over.mk x ⟶ A',
      q ^ n = 1 ↔ ∃ y, I.ev (n * k) (h (n * k) y) ≫ ψ = q := by
    intro n hn hnp q
    constructor
    · intro hq
      haveI := hGal.fin
      haveI := hGal.onto
      obtain ⟨a₀, ha₀⟩ := GlobalTheory.GeomSurj.exists_lift_of_surjective ψ.left q.left
      let a : Over.mk x ⟶ o.A := Over.homMk a₀ (by
        show a₀ ≫ o.A.hom = x
        rw [← Over.w ψ, ← Category.assoc, ← ha₀, Over.w q]; rfl)
      have ha : a ≫ ψ = q := Over.OverMorphism.ext (by rw [Over.comp_left]; exact ha₀.symm)
      have han : (a ^ n) ≫ ψ = 1 := by rw [← hΨ, map_pow, hΨ, ha, hq]
      obtain ⟨z, hz⟩ := (hkerN n hn hnp _).1 han
      have hnk : 0 < n * k := Nat.mul_pos hn kpos
      have hnkp : (n * k).Coprime p := Nat.Coprime.mul_left hnp hkp
      have hak : a ^ (n * k) = 1 := by
        rw [pow_mul, hz, ← TateTransl.ev_nsmul, I.ker _ hnk hnkp]
        exact ⟨h (n * k) z, by rw [smul_smul, mul_comm]⟩
      obtain ⟨w, hw⟩ := (I.onto _ hnk hnkp a).1 hak
      rw [← hw, ← TateTransl.ev_nsmul, ev_eq_iff I _ hnk hnkp] at hz
      obtain ⟨v, hv⟩ := hz
      have e1 : n • (w - h (n * k) z - k • v) = 0 := by rw [smul_sub, smul_sub, smul_smul, ← hv, sub_self]
      have e2 : w - h (n * k) z - k • v = 0 := by
        have e3 : ((n : ℤ)) • (w - h (n * k) z - k • v) = 0 := by rw [natCast_zsmul]; exact e1
        exact (smul_eq_zero.1 e3).resolve_left (by exact_mod_cast hn.ne')
      have e4 : w = h (n * k) z + k • v := by rw [sub_sub, sub_eq_zero] at e2; exact e2
      obtain ⟨y'', z'', hy''⟩ := hsurj (n * k) hnk hnkp v
      have e5 : h (n * k) (z + y'') = w + (n * k) • z'' := by rw [map_add (f := _), hy'', e4, add_assoc]
      refine ⟨z + y'', ?_⟩
      rw [e5, I.add, (I.ker _ hnk hnkp ((n * k) • z'')).2 ⟨z'', rfl⟩, _root_.mul_one, hw, ha]
    · rintro ⟨y, rfl⟩
      exact htor n hn hnp y
  have hnκ : ∀ n : ℕ, n.Coprime p → (n : κ) ≠ 0 := fun n hnp => by
    have h := (b.unit n hnp).map β
    rw [map_natCast] at h
    exact h.ne_zero
  have hiso2 : LBIso (ReciprocityTheory.ChartRestriction.G.Geo.Tor.lbPow (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (k ^ 2 / c))
      ((P'.pull (lift (𝟙 A') (𝟙 A')).left).pull ψ.left) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb (pull_isLB o.isLB _) _ _) (pull_isLB (pull_isLB hP' _) _)).1 ?_
    rw [GlobalTheory.CechPic.cls_lbPow (pull_isLB o.isLB _), GlobalTheory.CechPic.cls_pull o.isLB, GlobalTheory.CechPic.cls_pull (pull_isLB hP' _),
      GlobalTheory.CechPic.cls_pull hP', ← GlobalTheory.CechPic.pull_comp]
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o.isLB _ _) (pull_isLB hP' _)).2 hiso
    rw [GlobalTheory.CechPic.cls_linComb o.isLB, GlobalTheory.CechPic.cls_pull hP'] at h1
    simp only [GlobalTheory.CechPic.pull_id, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at h1
    have h2 := congrArg (GlobalTheory.CechPic.pull (lift (𝟙 o.A) (𝟙 o.A)).left) h1
    rw [map_nsmul, ← GlobalTheory.CechPic.pull_comp] at h2
    rw [h2]
    congr 1
    simp only [sq2, ← Over.comp_left, comp_lift, Category.id_comp, lift_fst_assoc, lift_snd_assoc, Category.comp_id]

  have hmc : k ^ 2 / c * c = k ^ 2 := Nat.div_mul_cancel hck
  have hm0 : 0 < k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd (by positivity) hck) cpos
  have hmp : (k ^ 2 / c).Coprime p :=
    Nat.Coprime.coprime_dvd_left (Dvd.intro c hmc) (Nat.Coprime.pow_left 2 hkp)
  let ev' : ℕ → D.La → (Over.mk x ⟶ A') := fun n y =>
    if 0 < n ∧ n.Coprime p then I.ev (n * k) (h (n * k) y) ≫ ψ else 1
  have hev' : ∀ n, 0 < n → n.Coprime p → ∀ y, ev' n y = I.ev (n * k) (h (n * k) y) ≫ ψ :=
    fun n hn hnp y => if_pos ⟨hn, hnp⟩
  refine ⟨⟨fun n => I.ζ n ^ u n, ?_, ?_, ev', ?_, ?_, ?_, ?_, ?_, ?_⟩, fun y => ?_, hev'⟩
  · intro n hn hnp
    exact (I.ζ_prim n hn hnp).zpow_of_gcd_eq_one (u n) (Int.isCoprime_iff_gcd_eq_one.1 (hsim n hn hnp).1)
  · intro n m hn hm hnm
    show (I.ζ (n * m) ^ u (n * m)) ^ m = I.ζ n ^ u n
    rw [← I.ζ_pow n m hn hm hnm]
    simp only [← zpow_natCast, ← zpow_mul]
    apply zpow_eq_zpow_of_dvd (I.ζ_prim (n * m) (Nat.mul_pos hn hm) hnm).pow_eq_one
    obtain ⟨t, ht⟩ := (hcomp n m hn hm hnm).2
    exact ⟨t, by push_cast; linear_combination (m : ℤ) * ht⟩
  · intro n y y'
    simp only [ev']
    split_ifs with hn
    · rw [map_add (f := _), I.add, MonObj.mul_comp]
    · rw [_root_.mul_one]
  · intro n b' y
    simp only [ev']
    split_ifs with hn
    · have hnk : 0 < n * k := Nat.mul_pos hn.1 kpos
      have hnkp : (n * k).Coprime p := Nat.Coprime.mul_left hn.2 hkp
      obtain ⟨z, hz⟩ := hlin (n * k) hnk hnkp b' y
      rw [hz, I.add, (I.ker _ hnk hnkp _).2 ⟨z, rfl⟩, _root_.mul_one, I.lin, Category.assoc, hact,
        ← Category.assoc]
    · haveI := act'.hom b'
      rw [MonObj.one_comp]
  · intro n hn hnp y
    rw [hev' n hn hnp]
    exact ker' n hn hnp y
  · intro n hn hnp q
    simp only [hev' n hn hnp]
    exact onto' n hn hnp q
  · intro n m hn hm hnm y
    have hn' : n.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) hnm
    have hnk : 0 < n * k := Nat.mul_pos hn kpos
    have hnkm : (n * k * m).Coprime p := by rw [Nat.mul_right_comm]; exact Nat.Coprime.mul_left hnm hkp
    rw [hev' (n * m) (Nat.mul_pos hn hm) hnm, hev' n hn hn', ← hΨ, ← map_pow, hΨ, Nat.mul_right_comm n m k,
      I.tower (n * k) m hnk hm hnkm]
    obtain ⟨z, hz⟩ := (hcomp (n * k) m hnk hm hnkm).1 y
    rw [hz, I.add, (I.ker _ hnk (Nat.Coprime.mul_left hn' hkp) _).2 ⟨z, rfl⟩, _root_.mul_one]
  · intro n hn hnp y y'
    have hnk : 0 < n * k := Nat.mul_pos hn kpos
    have hnkp : (n * k).Coprime p := Nat.Coprime.mul_left hnp hkp
    have hnkc : (n * k * c).Coprime p := Nat.Coprime.mul_left hnkp hcp
    have hrep : ∀ y, I.ev (n * k) (h (n * k) y) = I.ev (n * k) (h (n * k * c) y) := fun y => by
      obtain ⟨z, hz⟩ := (hcomp (n * k) c hnk cpos hnkc).1 y
      rw [hz, I.add, (I.ker _ hnk hnkp _).2 ⟨z, rfl⟩, _root_.mul_one]
    rw [hev' n hn hnp, hev' n hn hnp]
    obtain ⟨e, he⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S A' (P'.pull (lift (𝟙 A') (𝟙 A')).left) hA'
      (pull_isLB hP' _) κ x n hn (hnκ n hnp) _ _ (htor n hn hnp y) (htor n hn hnp y')
    have h2 := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds o.ab (pull_isLB o.isLB _) (pull_isLB hP' _) ψ
      hiso2 he
    rw [hrep y, hrep y'] at h2
    have hNp' : (n * (k ^ 2 / c * k ^ 2)).Coprime p :=
      Nat.Coprime.mul_left hnp (Nat.Coprime.mul_left hmp (Nat.Coprime.pow_left 2 hkp))
    have h3 := weilIs_ev_value o I k (k ^ 2 / c) n kpos hm0 hn hNp' _ _ e (by rw [Nat.cast_mul]; exact h2)
    have h4 : I.ζ (n * (k ^ 2 / c * k ^ 2)) ^ (2 * D.EF ((k ^ 2 / c) • h (n * k * c) y) ((k ^ 2 / c) • h (n * k * c) y'))
        = (I.ζ n ^ u n) ^ (2 * D.EF y y') := by
      rw [← I.ζ_pow n (k ^ 2 / c * k ^ 2) hn (by positivity) hNp']
      simp only [← zpow_natCast, ← zpow_mul]
      apply zpow_eq_zpow_of_dvd (I.ζ_prim _ (by positivity) hNp').pow_eq_one
      obtain ⟨t, ht⟩ := (hsim (n * k * c) (by positivity) hnkc).2 y y'
      obtain ⟨s', hs'⟩ := (hcomp n (k * c) hn (by positivity) (by rw [← _root_.mul_assoc]; exact hnkc)).2
      rw [← _root_.mul_assoc] at hs'
      have hmcZ : ((k ^ 2 / c : ℕ) : ℤ) * (c : ℤ) = (k : ℤ) ^ 2 := by exact_mod_cast hmc
      simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
      refine ⟨2 * s' * D.EF y y' + 2 * k * t, ?_⟩
      simp only [Nat.cast_mul, Nat.cast_pow] at ht hs' ⊢
      linear_combination (2 * ((k ^ 2 / c : ℕ) : ℤ) * ((k ^ 2 / c : ℕ) : ℤ)) * ht
        + (2 * ((k ^ 2 / c : ℕ) : ℤ) * (k : ℤ) ^ 2 * D.EF y y') * hs'
        + (2 * ((k ^ 2 / c : ℕ) : ℤ) * u (n * k * c) * D.EF y y'
          + 2 * ((k ^ 2 / c : ℕ) : ℤ) * (n : ℤ) * (k : ℤ) * t) * hmcZ
    rw [h3, h4] at he
    exact he
  · show toUnit _ ≫ (o.eta (h (N * k) y) ≫ ψ) = ev' N y
    rw [hev' N Npos hNp, ← Category.assoc, hI]

end GlobalTheory.UPel.HT.HeckeAd.TateTranslAt

namespace GlobalTheory.UPel.HT.HeckeAd

end GlobalTheory.UPel.HT.HeckeAd
end -- noncomputable section
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMultBasic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem dvd_of_mult {p : ℕ} [Fact p.Prime] {m n : ℕ} (hm : m.Coprime p) {s t t' : AfP p}
    (hs : IsIntAf s) (ht' : IsIntAf t') (e : t * t' = 1) (h : (n : AfP p) * t = (m : AfP p) * s) : m ∣ n := by
  have hpos : 0 < m := by
    refine Nat.pos_of_ne_zero ?_
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' (Nat.coprime_zero_left p |>.1 hm)
  refine Int.natCast_dvd_natCast.1 (GlobalTheory.IntDvdAdele.dvd_of_eq_mul_int p m hpos hm (n : ℤ) (s * t')
    (GlobalTheory.HeckeApprox.isInt_mul hs ht') ?_)
  rw [Int.cast_natCast, ← _root_.mul_assoc, ← h, _root_.mul_assoc, e, _root_.mul_one]

theorem UpperTheory.Gal.G3.pMultBasic :
    NuInt → MultBasic := by
  intro hNu p _
  refine ⟨?_, ?_, ?_⟩
  · rintro a c c' hc hc' ⟨t, t', ht, ht', e, ha⟩ ⟨s, s', hs, hs', e', ha'⟩
    have h : (c : AfP p) * t = (c' : AfP p) * s := ha.symm.trans ha'
    exact Nat.dvd_antisymm (dvd_of_mult hc ht hs' e' h.symm) (dvd_of_mult hc' hs ht' e h)
  · rintro a a' c c' ⟨t, t', ht, ht', e, ha⟩ ⟨s, s', hs, hs', e', ha'⟩
    refine ⟨t * s, t' * s', GlobalTheory.HeckeApprox.isInt_mul ht hs, GlobalTheory.HeckeApprox.isInt_mul ht' hs', ?_, ?_⟩
    · rw [_root_.mul_mul_mul_comm, e, e', _root_.one_mul]
    · rw [ha, ha', Nat.cast_mul, _root_.mul_mul_mul_comm]
  · intro D G L u hu
    refine ⟨UpperTheory.Gal.G3.mul u, UpperTheory.Gal.G3.mul u⁻¹, hNu p D G L u (UpperTheory.Gal.Int.Geo.integ_of_mem hu),
      hNu p D G L u⁻¹ (UpperTheory.Gal.Int.Geo.integ_of_mem (inv_mem hu)),
      Units.mul_inv ((u : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2), ?_⟩
    rw [Nat.cast_one, _root_.one_mul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSysOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open GlobalTheory GlobalTheory.LKMid GlobalTheory.LKRes GlobalTheory.HeckeApprox
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pSysOf :
    NuInt → SysOf := by
  intro hNu p _ D G L g hI
  classical
  set A := L.actG g with hA
  set B := L.actG g⁻¹ with hB
  have hBA : ∀ v, B (A v) = v := fun v => by
    rw [hA, hB, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hAB : ∀ v, A (B v) = v := fun v => by
    rw [hA, hB, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hAint : ∀ v ∈ LaHat D, A v ∈ LaHat D := hI
  obtain ⟨j₁, hj₁, hj₁p, hj₁B⟩ := GlobalTheory.T.exists_coprime_nsmul_endomorphism_preserves_completion p D B
  set ν : AfP p := UpperTheory.Gal.G3.mul g with hν
  set ν' : AfP p := ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) with hν'
  have hνν' : ν * ν' = 1 := Units.mul_inv _
  have hνint : IsIntAf ν := hNu p D G L g hI
  obtain ⟨j₃, hj₃, hj₃p, hj₃ν⟩ := GlobalTheory.T.exists_coprime_nat_mul_finiteAdeleAwayP_integral p ν'
  set k := j₁ * j₃ with hk
  have hkp : k.Coprime p := Nat.Coprime.mul_left hj₁p hj₃p
  have hk0 : 0 < k := Nat.mul_pos hj₁ hj₃
  set h₀ : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D) := k • B with hh₀
  have hh₀v : ∀ v, h₀ v = k • B v := fun v => rfl
  have hh₀int : ∀ v ∈ LaHat D, h₀ v ∈ LaHat D := fun v hv => by
    rw [hh₀v, hk, mul_comm, mul_smul]; exact nsmul_mem (hj₁B v hv) _
  have hh₀A : ∀ v, h₀ (A v) = k • v := fun v => by
    rw [hh₀v, hBA]
  have hAh₀ : ∀ v, A (h₀ v) = k • v := fun v => by
    rw [hh₀v, map_nsmul, hAB]
  have hh₀O : ∀ (c : D.O) v, h₀ (actAf D c v) = actAf D c (h₀ v) := fun c v => by
    rw [hh₀v, hh₀v, hB, actG_actAf, map_nsmul]
  set mu : AfP p := (k : AfP p) ^ 2 * ν' with hmu
  have hh₀sim : ∀ v w, fAf D (h₀ v) (h₀ w) = mu * fAf D v w := fun v w => by
    simp only [hh₀v, map_nsmul, LinearMap.smul_apply]
    rw [hB, GlobalTheory.T.harrisTaylor_action_form_eq_similitude_mul p D G L g⁻¹ v w]
    simp only [nsmul_eq_mul, hmu, hν']
    rw [show (((g⁻¹ : G.GAf) : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2 : AfP p) =
      ((((g : (AfP p ⊗[ℚ] G.C)ˣ × (AfP p)ˣ).2)⁻¹ : (AfP p)ˣ) : AfP p) from rfl]
    ring
  have hmuint : IsIntAf mu := by
    have e : mu = ((j₁ : AfP p) ^ 2 * j₃) * ((j₃ : AfP p) * ν') := by rw [hmu, hk]; push_cast; ring
    rw [e]; exact isInt_mul (isInt_mul (by rw [sq]; exact isInt_mul (isInt_natCast _) (isInt_natCast _))
      (isInt_natCast _)) hj₃ν
  have hmuν : mu * ν = ((k ^ 2 : ℕ) : AfP p) := by
    rw [hmu]; push_cast; linear_combination ((k : AfP p) ^ 2) * hνν'
  obtain ⟨c, ε, ε', hcp, hck, hε, hε', hεε', hmuε⟩ :=
    GlobalTheory.T.exists_divisor_mul_integralUnit_finiteAdelesAwayP p mu ν (k ^ 2) (pow_pos hk0 2) (Nat.Coprime.pow_left 2 hkp) hmuint hνint hmuν
  obtain ⟨u, hut, hu⟩ := GlobalTheory.T.integral_adele_unit_congruence_sequence p ε ε' hε hε' hεε'
  obtain ⟨f, hf⟩ := GlobalTheory.T.lattice_endomorphism_integral_approximation p D h₀ hh₀int
  have hfe : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ w ∈ LaHat D, inAf D (f n x) = h₀ (inAf D x) - n • w :=
    fun n hn hnp x => by
      obtain ⟨w, hw, e⟩ := hf n hn hnp x
      exact ⟨w, hw, by rw [e]; abel⟩
  have hmult : IsMult ν (k ^ 2 / c) := by
    refine ⟨ε', ε, hε', hε, by rw [mul_comm]; exact hεε', ?_⟩
    have hc0 : c ≠ 0 := fun h0 => by
      rw [h0, zero_dvd_iff] at hck
      exact (pow_pos hk0 2).ne' hck
    have hcu : IsUnit (c : AfP p) := by
      have : IsUnit (algebraMap ℚ (AfP p) (c : ℚ)) :=
        (IsUnit.mk0 (c : ℚ) (Nat.cast_ne_zero.mpr hc0)).map _
      simpa using this
    have e1 : ((k ^ 2 : ℕ) : AfP p) = (c : AfP p) * ((k ^ 2 / c : ℕ) : AfP p) := by
      rw [← Nat.cast_mul, Nat.mul_div_cancel' hck]
    apply hcu.mul_left_cancel
    have e2 : (c : AfP p) * ε * ν = (c : AfP p) * ((k ^ 2 / c : ℕ) : AfP p) := by
      rw [← hmuε, hmuν, e1]
    linear_combination ε' * e2 - ((c : AfP p) * ν) * hεε'
  refine ⟨f, u, c, k, ⟨hcp, hkp, hck, ?_, ?_, ?_, ?_⟩, hmult, fun v hv => hh₀int v hv, ?_⟩
  ·
    intro n hn hnp a x
    obtain ⟨w₁, hw₁, e₁⟩ := hfe n hn hnp (a • x)
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp x
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f n (a • x) - a • f n x) n hn hnp
      (actAf D a w₂ - w₁) (sub_mem (actAf_mem_laHat D a hw₂) hw₁) (by
        rw [inAf_sub, ← actAf_inAf, e₁, e₂, ← actAf_inAf, hh₀O, map_sub, map_nsmul, smul_sub]; abel)
    exact ⟨z, by rw [← hz]; abel⟩
  ·
    intro n m hn hm hnm
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (dvd_mul_right n m) hnm
    refine ⟨fun x => ?_, hut n m hn hm hnm⟩
    obtain ⟨w₁, hw₁, e₁⟩ := hfe (n * m) (Nat.mul_pos hn hm) hnm x
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp x
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f (n * m) x - f n x) n hn hnp
      (w₂ - m • w₁) (sub_mem hw₂ (nsmul_mem hw₁ m)) (by
        rw [inAf_sub, e₁, e₂, smul_sub, smul_smul]; abel)
    exact ⟨z, by rw [← hz]; abel⟩
  ·
    intro n hn hnp
    obtain ⟨hco, β, hβ, hεβ⟩ := hu n hn hnp
    refine ⟨hco, fun x y => ?_⟩
    obtain ⟨w₁, hw₁, e₁⟩ := hfe n hn hnp x
    obtain ⟨w₂, hw₂, e₂⟩ := hfe n hn hnp y
    have hX := hh₀int _ (inAf_mem D x)
    have hY := hh₀int _ (inAf_mem D y)
    refine IntDvdAdele.dvd_of_eq_mul_int p n hn hnp _
      ((c : AfP p) * β * (D.EF x y : AfP p) - fAf D (h₀ (inAf D x)) w₂ - fAf D w₁ (h₀ (inAf D y)) +
        (n : AfP p) * fAf D w₁ w₂)
      (isInt_add (isInt_sub (isInt_sub (isInt_mul (isInt_mul (isInt_natCast c) hβ) (isInt_intCast _))
        (formInt_laHat p D _ _ hX hw₂)) (formInt_laHat p D _ _ hw₁ hY))
        (isInt_mul (isInt_natCast n) (formInt_laHat p D _ _ hw₁ hw₂))) ?_
    have e : ((D.EF (f n x) (f n y) : ℤ) : AfP p) = fAf D (inAf D (f n x)) (inAf D (f n y)) :=
      (form_inAf D _ _).symm
    push_cast
    rw [e, e₁, e₂]
    simp only [map_sub, map_nsmul, LinearMap.sub_apply, LinearMap.smul_apply, nsmul_eq_mul]
    rw [hh₀sim, hmuε, hεβ, form_inAf]
    ring
  ·
    intro n hn hnp x
    obtain ⟨y, w, hw, e⟩ := exists_inAf_add_nsmul_of_mem_laHat p D n hn hnp (A (inAf D x))
      (hAint _ (inAf_mem D x))
    obtain ⟨w', hw', e'⟩ := hfe n hn hnp y
    have e2 : h₀ (inAf D y) = k • inAf D x - n • h₀ w := by
      rw [← hh₀A, e, map_add (f := _), map_nsmul]; abel
    obtain ⟨z, hz⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D (f n y - k • x) n hn hnp
      (-(w' + h₀ w)) (neg_mem (add_mem hw' (hh₀int w hw))) (by
        rw [inAf_sub, e', e2, inAf_nsmul, smul_neg, smul_add]; abel)
    exact ⟨y, z, by rw [← hz]; abel⟩
  ·
    intro n hn hnp x
    obtain ⟨w, hw, e⟩ := hfe n hn hnp x
    refine ⟨-(A w), neg_mem (hAint w hw), ?_⟩
    rw [e, map_sub, map_nsmul, hAh₀, smul_neg]
    abel
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKNCong
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pKNCong :
    KNCong := by
  intro p _ D G L N _ _ u hu h
  have h1 : L.CongOne N u := GlobalTheory.AdelicSim.congOne_of D (L.actG u) N h
  refine ⟨h1, ?_⟩
  intro v hv
  obtain ⟨w₁, hw₁, e₁⟩ := hu.2 v hv
  have hv' : L.actG u⁻¹ v ∈ LaHat D := by
    rw [e₁]
    exact add_mem hv (nsmul_mem hw₁ _)
  obtain ⟨w, hw, e⟩ := h1 _ hv'
  have e' : L.actG u (L.actG u⁻¹ v) = v := by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  refine ⟨-w, neg_mem hw, ?_⟩
  rw [e'] at e
  rw [smul_neg]
  exact eq_add_neg_of_add_eq e.symm
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PRelComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pRelComp :
    RelComp := by
  unfold UpperTheory.Gal.G3.RelComp
  intro p _ D G L R _ _ gb S s N₁ N₂ N₃ o₁ o₂ o₃ k _ t I₁ I₂ I₃ ψ₁ ψ₂ h₁ h₂ hψ₁ hψ₂ hint
  unfold UpperTheory.Gal.G3.Rel
  refine ⟨?_, ?_⟩
  · intro n hn hcop x y
    rw [Category.comp_id]
    refine (HeckeRestrict.ev_eq_iff I₁ n hn x y).trans
      ((ForgetHecke.acts_one_iff L n hn hcop x y).symm.trans ?_)
    simp
  · intro r₁ r₂ n hn hcop x z
    have htor : (I₁.ev n x ≫ ψ₁) ^ n = 1 := by
      haveI := hψ₁
      have e := map_pow (IsMonHom.monoidHom ψ₁ (Over.mk t)) (I₁.ev n x) n
      simp only [IsMonHom.monoidHom_apply] at e
      rw [← e, (I₁.onto n hn (I₁.ev n x)).2 ⟨x, rfl⟩]
      exact (IsMonHom.monoidHom ψ₁ (Over.mk t)).map_one
    obtain ⟨y, hy⟩ := (I₂.onto n hn _).1 htor
    obtain ⟨v₁, hv₁, e₁⟩ := (r₁ n hn hcop x y).1 hy.symm
    rw [← Category.assoc, ← hy, r₂ n hn hcop y z, map_mul, Module.End.mul_apply, e₁, map_add (f := _),
      map_nsmul]
    have hw := hint v₁ hv₁
    constructor
    · rintro ⟨v, hv, e⟩
      refine ⟨v + L.actG h₂ v₁, add_mem hv hw, ?_⟩
      rw [e, smul_add, add_assoc]
    · rintro ⟨v, hv, e⟩
      refine ⟨v - L.actG h₂ v₁, sub_mem hv hw, ?_⟩
      rw [smul_sub, ← add_sub_assoc, ← e, add_sub_cancel_right]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTateDiff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTateDiff :
    TateDiff := by
  unfold TateDiff
  intro p _ D G L R _ _ gb S s N o k _ _ t I J hI hJ
  have hN : 0 < N.1 := by have := N.2.1; omega
  have hNp : N.1.Coprime p := N.2.2
  obtain ⟨g, hg⟩ := GlobalTheory.LKGeo.GammaUniq.exists_simSys_all hN hNp
    (fun n q q' z z' h h' => GlobalTheory.weilIs_unique_fieldPoint S o.A _ (LB.isLB_pull o.isLB _) k t n q q' z z' h h')
    (GenCmp.tateRestrict J) (GenCmp.tateRestrict I)
    (fun y => (hJ y).symm.trans (hI y))
  obtain ⟨u, hu, hh⟩ := GlobalTheory.AdelicSim.exists_mem_KN p D G L N.1 hN hNp g
  refine ⟨u, hu, fun n hn hc x y => ?_⟩
  have e₁ : I.ev n x = J.ev n (g.g n x) := hg n hn hc x
  have e₂ : ∀ a b : D.La, J.ev n a = J.ev n b ↔ ∃ z, a = b + n • z := fun a b =>
    GlobalTheory.UPel.HT.TateCompare.ev_eq_iff (GenCmp.tateRestrict J) hn hc
  obtain ⟨w, hw, e₃⟩ := hh n hn hc x
  let f : D.La →+ (AfP p ⊗[ℚ] VQ D) := AddMonoidHom.mk' (inAf D) (GlobalTheory.LKGeo.GammaUniq.inAf_add (p := p) (D := D))
  have hf : ∀ a, f a = inAf D a := fun _ => rfl
  rw [Category.comp_id, e₁, e₂]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨inAf D z + w, add_mem (GlobalTheory.LKGeo.GammaUniq.inAf_mem z) hw, ?_⟩
    rw [e₃, hz, ← hf, ← hf, ← hf, map_add (f := _), map_nsmul, smul_add, add_assoc]
  · rintro ⟨v, hv, e₄⟩
    have e₅ : inAf D (g.g n x - y) = n • (v - w) := by
      rw [← hf, map_sub, hf, hf, smul_sub]
      rw [e₃] at e₄
      rw [sub_eq_sub_iff_add_eq_add, e₄, add_comm]
    obtain ⟨z, hz⟩ := GlobalTheory.LKGeo.LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hc _ (sub_mem hv hw) e₅
    exact ⟨z, by rw [← hz]; abel⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTateTwist
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTateTwist :
    GSimOf → TateTwist := by
  unfold GSimOf TateTwist
  intro hG p _ D G L R _ _ gb S s N o k _ t I hI u hu
  have hNpos : 0 < (N : ℕ) := by
    have := N.2.1
    omega
  have hNcop : (N : ℕ).Coprime p := N.2.2
  have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
  have hui1 : u⁻¹ ∈ L.KN 1 := inv_mem hu1
  obtain ⟨g, hg⟩ := hG p D G L u⁻¹ hui1
  obtain ⟨J, hJ⟩ := UpperTheory.exists_gTateIso_twist_of_similitude I g
  have intU := UpperTheory.Gal.Int.Geo.integ_of_mem hu1
  have intUi := UpperTheory.Gal.Int.Geo.integ_of_mem hui1
  unfold UpperTheory.Gal.Int.Geo.Integ at intU intUi
  have hcong : L.CongOne (N : ℕ) u⁻¹ := by
    unfold GlobalTheory.LKGeo.Link.KN at hu
    simp only [Subgroup.mem_mk, Submonoid.mem_mk, Subsemigroup.mem_mk, Set.mem_ofPred_eq] at hu
    exact hu.2
  unfold GlobalTheory.LKGeo.Link.CongOne at hcong
  have inv_act : ∀ v, L.actG u⁻¹ (L.actG u v) = v := by
    intro v
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one, one_apply_eq_self]
  have act_inv : ∀ v, L.actG u (L.actG u⁻¹ v) = v := by
    intro v
    rw [← mul_apply_eq_comp, ← map_mul, mul_inv_cancel, map_one, one_apply_eq_self]
  refine ⟨J, ?_, ?_⟩
  · unfold UpperTheory.Gal.G3.Ind at hI ⊢
    intro y
    rw [hI y, hJ _ hNpos y]
    symm
    refine (HeckeRestrict.ev_eq_iff I _ hNpos (g.f N y) y).mpr ?_
    obtain ⟨w, hw, hgw⟩ := hg N hNpos hNcop y
    obtain ⟨w', hw', hcw⟩ := hcong (inAf D y) (GlobalTheory.HeckeApprox.inAf_mem D y)
    apply LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ N hNpos hNcop (w' - w) (sub_mem hw' hw)
    have e := hgw.symm.trans hcw
    rw [show inAf D (g.f N y - y) = inAf D (g.f N y) - inAf D y from GlobalTheory.HeckeApprox.inAf_sub D _ _, smul_sub]
    calc inAf D (g.f N y) - inAf D y = (inAf D (g.f N y) + (N : ℕ) • w) - (N : ℕ) • w - inAf D y := by abel
      _ = (inAf D y + (N : ℕ) • w') - (N : ℕ) • w - inAf D y := by rw [e]
      _ = (N : ℕ) • w' - (N : ℕ) • w := by abel
  · unfold UpperTheory.Gal.G3.Rel
    intro n hn hnp x y
    rw [Category.comp_id, hJ n hn y]
    refine (HeckeRestrict.ev_eq_iff I n hn x (g.f n y)).trans ?_
    obtain ⟨w, hw, hgw⟩ := hg n hn hnp y
    constructor
    · rintro ⟨z, hz⟩
      refine ⟨L.actG u (inAf D z - w), intU _ (sub_mem (GlobalTheory.HeckeApprox.inAf_mem D z) hw), ?_⟩
      have h1 := GlobalTheory.HeckeApprox.inAf_add D (g.f n y) (n • z)
      have h2 := GlobalTheory.HeckeApprox.inAf_nsmul D n z
      have hx : inAf D x = inAf D (g.f n y) + n • inAf D z :=
        (congrArg (inAf D) (sub_eq_iff_eq_add'.mp hz)).trans (h1.trans (congrArg (inAf D (g.f n y) + ·) h2))
      have e1 : inAf D (g.f n y) = L.actG u⁻¹ (inAf D y) - n • w := by
        rw [hgw]
        abel
      rw [hx, e1, map_add (f := _), map_sub, map_nsmul, map_nsmul, act_inv, map_sub, smul_sub]
      abel
    · rintro ⟨v, hv, hxv⟩
      apply LatDiv.eq_nsmul_of_inAf_eq_nsmul p D _ n hn hnp (w + L.actG u⁻¹ v) (add_mem hw (intUi _ hv))
      have hx : inAf D x = L.actG u⁻¹ (inAf D y) + n • L.actG u⁻¹ v := by
        rw [← map_nsmul, ← map_add (f := _), ← hxv, inv_act]
      refine (GlobalTheory.HeckeApprox.inAf_sub D x (g.f n y)).trans ?_
      rw [hx, hgw, smul_add]
      abel
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PFullOf
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pFullOf :
    FullOf := by
  intro p _ D R _ _ gb S s N o k _ _ t J
  have hp : p.Prime := Fact.out
  have hts : t ≫ s = spMap (Spec.preimage (t ≫ s)).hom := by
    simp only [spMap, CommRingCat.ofHom_hom, Spec.map_preimage]
  obtain ⟨I', -⟩ := o.geom k t _ hts
  have hLB : (o.P.pull (Over.Hom.left (lift (𝟙 o.A) (𝟙 o.A)))).IsLB := pull_isLB o.isLB _
  have hpos : ∀ r : ℕ, 0 < p ^ r := fun r => pow_pos hp.pos r
  refine HeckeGen.exists_join (fun c g => g ≫ o.act.act c) _ ?_ ?_ ?_ ?_ ?_ J (fun r => I'.ζ (p ^ r))
    (fun r => I'.ev (p ^ r)) (fun r => I'.ζ_prim _ (hpos r)) ?_ (fun r x y => I'.add _ x y)
    (fun r b x => I'.lin _ b x) (fun r x => I'.ker _ (hpos r) x) (fun r q => I'.onto _ (hpos r) q) ?_
    (fun r x y => I'.isom _ (hpos r) x y)
  · intro c a b
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  · intro n hn g g' hg hg'
    obtain ⟨e, he⟩ := GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S o.A _ o.ab hLB k t n hn
      (HeckeGen.natCast_ne_zero_of_hom (Spec.preimage (t ≫ s)).hom n hn) g g' hg hg'
    obtain ⟨z, rfl⟩ := HeckeGen.unitOn_bij.2 e
    exact ⟨z, he⟩
  · intro n g g' z z' h1 h2
    exact HeckeGen.unitOn_bij.1 (GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds o.ab hLB h1 h2)
  · intro n j g g' z h
    have hu : unitOn (z ^ j) = unitOn z ^ j := by
      unfold unitOn
      exact map_pow _ _ _
    rw [hu, Nat.cast_mul]
    exact GlobalTheory.WeilIsogeny.weilIs_pow GlobalTheory.globalFns_holds o.ab hLB j h
  · intro n j g g' z h
    haveI := isMonHom_mulA (A := o.A) j
    have hiso := GlobalTheory.HeckeWeilValue.lbIso_mulA_diag o.ab o.isLB o.ample o.rig₁ o.rig₂ j
    have e1 : ∀ x : Over.mk t ⟶ o.A, x ≫ Out.mulA o.A j = x ^ j := fun x => by
      rw [Out.mulA, MonObj.comp_pow, Category.comp_id]
    have h' := h
    rw [← e1, ← e1] at h'
    have := GlobalTheory.WeilIsogeny.weilIs_pull_hom GlobalTheory.globalFns_holds o.ab hLB hLB (Out.mulA o.A j) hiso h'
    rw [Nat.cast_mul]
    exact this
  · intro r s'
    rw [pow_add]
    exact I'.ζ_pow _ _ (hpos r) (hpos s')
  · intro r s' x
    rw [pow_add]
    exact I'.tower _ _ (hpos r) (hpos s') x
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransComp :
    MultBasic → RelComp → TateDiff → TateTwist → TransComp := by
  intro hMB hRC hTD hTT p _ D G L R _ _ gb S s N₁ N₂ N₃ o₁ o₂ o₃ ψ₁ ψ₂ h₁ h₂ hI hA t1 t2
  obtain ⟨m1, a1, ⟨ψ₁', d₁, m1', a1', e1, e1', cp1⟩, ⟨c₁, cc1, ⟨iso1⟩, hm1⟩, g1⟩ := t1
  obtain ⟨m2, a2, ⟨ψ₂', d₂, m2', a2', e2, e2', cp2⟩, ⟨c₂, cc2, ⟨iso2⟩, hm2⟩, g2⟩ := t2
  haveI := m1
  haveI := m2
  haveI := m1'
  haveI := m2'
  refine ⟨inferInstance, ?_, ⟨ψ₂' ≫ ψ₁', d₁ * d₂, inferInstance, ?_, ?_, ?_, Nat.Coprime.mul_left cp1 cp2⟩,
    ⟨c₂ * c₁, Nat.Coprime.mul_left cc2 cc1, ⟨?_⟩, ?_⟩, ?_⟩
  · intro c
    rw [← Category.assoc, a1 c, Category.assoc, a2 c, Category.assoc]
  · intro c
    rw [← Category.assoc, a2' c, Category.assoc, a1' c, Category.assoc]
  · rw [Category.assoc, ← Category.assoc ψ₂, e2, MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, e1, pow_mul]
  · rw [Category.assoc, ← Category.assoc ψ₁', e1', MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, e2', mul_comm, pow_mul]
  · have hlb : (Hecke.lbPow o₁.P (c₂ * c₁)).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hpl : (o₃.P.pull (Hecke.sq2 (ψ₁ ≫ ψ₂))).IsLB := pull_isLB o₃.isLB _
    have hl1 : (Hecke.lbPow o₁.P c₁).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hl2 : (Hecke.lbPow o₂.P c₂).IsLB := LB.isLB_linComb o₂.isLB _ _
    have k1 := (GlobalTheory.CechPic.cls_eq_iff hl1 (pull_isLB o₂.isLB (Hecke.sq2 ψ₁))).2 iso1
    have k2 := (GlobalTheory.CechPic.cls_eq_iff hl2 (pull_isLB o₃.isLB (Hecke.sq2 ψ₂))).2 iso2
    rw [Hecke.Comp.cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₂.isLB] at k1
    rw [Hecke.Comp.cls_lbPow' o₂.isLB, GlobalTheory.CechPic.cls_pull o₃.isLB] at k2
    apply (GlobalTheory.CechPic.cls_eq_iff hlb hpl).1
    rw [Hecke.Comp.cls_lbPow' o₁.isLB, GlobalTheory.CechPic.cls_pull o₃.isLB, Hecke.Comp.grpSchemeSquareProductMap_comp,
      GlobalTheory.CechPic.pull_comp, ← k2, map_nsmul, ← k1, smul_smul]
  · exact (hMB p).2.1 _ _ _ _ hm2 hm1
  · intro k _ _ t β hts
    obtain ⟨I1', I1'', ind1', ind1'', rel1⟩ := g1 k t β hts
    obtain ⟨I2', I2'', ind2', ind2'', rel2⟩ := g2 k t β hts
    obtain ⟨u, hu, ru⟩ := hTD p D G L R gb S s N₂ o₂ k t I1'' I2' ind1'' ind2'
    have hint : ∀ {M : ℕ} {g : G.GAf}, g ∈ L.KN M → Integ L g := fun hg =>
      UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hg)
    have rA := (hRC p D G L R gb S s N₁ N₂ N₂ o₁ o₂ o₂ k t I1' I1'' I2' ψ₁ (𝟙 _) h₁ u
      inferInstance inferInstance (hint hu)).2 rel1 ru
    have rB := (hRC p D G L R gb S s N₁ N₂ N₃ o₁ o₂ o₃ k t I1' I2' I2'' (ψ₁ ≫ 𝟙 _) ψ₂ (u * h₁) h₂
      inferInstance inferInstance hI).2 rA rel2
    have hu' : (h₂ * u * h₂⁻¹)⁻¹ ∈ L.KN N₃ := inv_mem (hA u hu)
    obtain ⟨J, indJ, rJ⟩ := hTT p D G L R gb S s N₃ o₃ k t I2'' ind2'' _ hu'
    have rC := (hRC p D G L R gb S s N₁ N₃ N₃ o₁ o₃ o₃ k t I1' I2'' J ((ψ₁ ≫ 𝟙 _) ≫ ψ₂) (𝟙 _)
      (h₂ * (u * h₁)) _ inferInstance inferInstance (hint hu')).2 rB rJ
    have hg : (h₂ * u * h₂⁻¹)⁻¹ * (h₂ * (u * h₁)) = h₂ * h₁ := by group
    rw [hg] at rC
    simp only [Category.comp_id] at rC
    exact ⟨I1', J, ind1', indJ, rC⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PHomPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem square_map_isSquare {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (ψ : A ⟶ B) :
    Geo.Tor.IsSquare ψ.left (Hecke.sq2 ψ) := by
  constructor
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]

theorem UpperTheory.Gal.G3.pHomPull :
    HomPull := by
  intro G₀ R _ _ gb S S' s s' f N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ
  let g : Over.mk (o₁'.A.hom ≫ f) ⟶ o₂.A := GlobalTheory.ObjPull.pushEquiv m₁.cart o₁'.A (𝟙 o₁'.A) ≫ ψ
  refine ⟨(GlobalTheory.ObjPull.pushEquiv m₂.cart o₁'.A).symm g, ?_⟩
  set ψ' := (GlobalTheory.ObjPull.pushEquiv m₂.cart o₁'.A).symm g with hψ'eq
  have hψ' : ψ'.left ≫ m₂.φ = m₁.φ ≫ ψ.left := by
    rw [← GlobalTheory.ObjPull.pushEquiv_left m₂.cart, hψ'eq, MulEquiv.apply_symm_apply]
    simp only [g, Over.comp_left, GlobalTheory.ObjPull.pushEquiv_left, Over.id_left, Category.id_comp]
  have key : ∀ (T : Over S') (z : T ⟶ o₁'.A),
      GlobalTheory.ObjPull.pushEquiv m₂.cart T (z ≫ ψ') = GlobalTheory.ObjPull.pushEquiv m₁.cart T z ≫ ψ := by
    intro T z
    apply Over.OverMorphism.ext
    simp only [GlobalTheory.ObjPull.pushEquiv_left, Over.comp_left, Category.assoc, hψ']
  have inj : ∀ {T : Over S'} (u v : T ⟶ o₂'.A), u.left ≫ m₂.φ = v.left ≫ m₂.φ → u = v := by
    intro T u v huv
    apply (GlobalTheory.ObjPull.pushEquiv m₂.cart T).injective
    apply Over.OverMorphism.ext
    rw [GlobalTheory.ObjPull.pushEquiv_left, GlobalTheory.ObjPull.pushEquiv_left, huv]
  have hsq : m₁.φ₂ ≫ Hecke.sq2 ψ = Hecke.sq2 ψ' ≫ m₂.φ₂ := by
    have a := MapComp.isSquare_comp m₁.sq (square_map_isSquare ψ)
    have b := MapComp.isSquare_comp (square_map_isSquare ψ') m₂.sq
    rw [hψ'] at b
    exact MapComp.isSquare_unique a b
  refine ⟨hψ', ?_, ?_, ?_⟩
  · intro hψ
    apply GlobalTheory.Serre.isMonHom_of_mul_comp
    intro T x y
    apply (GlobalTheory.ObjPull.pushEquiv m₂.cart T).injective
    rw [map_mul, key, key, key, map_mul, MonObj.mul_comp]
  · intro hc c
    apply inj
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ', m₂.act,
      ← Category.assoc ψ'.left, hψ', ← Category.assoc, m₁.act, Category.assoc, Category.assoc,
      ← Over.comp_left, ← Over.comp_left, hc c]
  · intro c hc
    obtain ⟨e⟩ := hc
    have h1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o₁.isLB _ _) (pull_isLB o₂.isLB _)).2 e
    have hP1 := (GlobalTheory.CechPic.cls_eq_iff o₁'.isLB (pull_isLB o₁.isLB m₁.φ₂)).2 m₁.pol
    have hP2 := (GlobalTheory.CechPic.cls_eq_iff o₂'.isLB (pull_isLB o₂.isLB m₂.φ₂)).2 m₂.pol
    rw [GlobalTheory.CechPic.cls_pull o₁.isLB] at hP1
    rw [GlobalTheory.CechPic.cls_pull o₂.isLB] at hP2
    rw [GlobalTheory.CechPic.cls_pull o₂.isLB, GlobalTheory.CechPic.cls_linComb o₁.isLB] at h1
    simp only [GlobalTheory.CechPic.pull_id] at h1
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb o₁'.isLB _ _) (pull_isLB o₂'.isLB _)).1 ?_⟩
    rw [GlobalTheory.CechPic.cls_linComb o₁'.isLB, GlobalTheory.CechPic.cls_pull o₂'.isLB, hP1, hP2]
    simp only [GlobalTheory.CechPic.pull_id]
    rw [← GlobalTheory.CechPic.pull_comp, ← hsq, GlobalTheory.CechPic.pull_comp, ← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, map_zsmul]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTatePull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

theorem pTatePull : TatePull := by
  unfold TatePull
  intro p _ D R _ _ gb S S' s s' f N o o' m k _ t
  have hT := HeckeRestrict.tate_pullback D.toG o.A o'.A o.act o'.act o.P o'.P o.isLB o'.isLB f m.φ m.φ₂
    m.cart m.sq m.act m.pol k t
  have hpt : ∀ y, (toUnit (Over.mk (t ≫ f)) ≫ o.eta y).left = t ≫ (o'.eta y).left ≫ m.φ := by
    intro y
    rw [Over.comp_left, HeckeRestrict.toUnit_left, m.eta y]
    exact Category.assoc _ _ _
  have hpt' : ∀ y, (toUnit (Over.mk t) ≫ o'.eta y).left ≫ m.φ = t ≫ (o'.eta y).left ≫ m.φ := by
    intro y
    rw [Over.comp_left, HeckeRestrict.toUnit_left]
    exact Category.assoc _ _ _
  refine ⟨fun I => ?_, fun I' => ?_⟩
  · obtain ⟨I', hI'⟩ := hT.2 I
    refine ⟨I', fun hI y => ?_, fun n x => (hI' n x).symm⟩
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [hpt', ← hpt, hI y, hI' N y]
    · rw [Over.w, Over.w]
  · obtain ⟨I, hI⟩ := hT.1 I'
    refine ⟨I, fun hI' y => ?_, fun n x => (hI n x).symm⟩
    apply Over.OverMorphism.ext
    rw [hpt, hI N y, ← hI' y, hpt']

end UpperTheory.Gal.G3
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransOfMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem tiso_congr {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [Algebra ℚ R] {gb : GBase D.toG R}
    {S : Scheme.{0}} {s : S ⟶ Sp R} {N : ℕ} (o : GObj gb N s) {k : Type} [Field k] {t t' : Sp k ⟶ S} (e : t = t')
    (I : UpperTheory.Gal.Int.Geo.TIso o t) (hI : Ind o I) :
    ∃ J : UpperTheory.Gal.Int.Geo.TIso o t', Ind o J ∧ ∀ n x, (J.ev n x).left = (I.ev n x).left := by
  subst e
  exact ⟨I, hI, fun _ _ => rfl⟩

private theorem lbIso_hecke_lbPow_one {X : Scheme.{0}} {P : LB X} (hP : P.IsLB) : LBIso (Hecke.lbPow P 1) P := by
  have h1 : (Hecke.lbPow P 1).IsLB := LB.isLB_linComb hP _ _
  have h2 : (lbPow P 1).IsLB := GlobalTheory.isLB_lbPow hP 1
  have h3 : ((Hecke.lbPow P 1).pull (𝟙 X)).IsLB := pull_isLB h1 _
  exact LBIso.trans h1 h2 hP
    (LBIso.trans h1 h3 h2 (GlobalTheory.DescendedPrincipal.lbIso_pull_id h1).symm
      (GlobalTheory.BiextPairing.lbIso_lbPow_hecke hP 1).symm)
    (GlobalTheory.lbIso_lbPow_one hP)

theorem UpperTheory.Gal.G3.pTransOfMap :
    MultBasic → RelComp → TatePull → TransOfMap := by
  intro MB RC TP p _ D G L R _ _ gb S s N o o' m
  have hw : m.φ ≫ o'.A.hom = o.A.hom := by simpa using m.cart.1.w
  let θ : o.A ⟶ o'.A := Over.homMk m.φ hw
  have hθ : θ.left = m.φ := rfl
  refine ⟨θ, rfl, ?_⟩
  have hmon : IsMonHom θ :=
    GlobalTheory.AmpleRigid.isMonHom_of_mul_comp θ
      (fun T => GlobalTheory.AmpleRigid.mul_comp_of_grpPullback_id (T := T) θ m.cart)
  have hact : ∀ c, o.act.act c ≫ θ = θ ≫ o'.act.act c := by
    intro c
    ext
    simpa [θ] using m.act c
  haveI : IsIso m.φ := m.cart.1.isIso_fst_of_isIso
  haveI : IsIso θ := by
    have : IsIso ((Over.forget S).map θ) := by
      change IsIso m.φ
      infer_instance
    exact isIso_of_reflects_iso θ (Over.forget S)
  have hsq : Hecke.sq2 θ = m.φ₂ := by
    apply Hecke.ProdGalois.grpScheme_square_hom_ext_fst_snd
    · rw [Hecke.ProdGalois.grpSchemeSquareProductMap_comp_fst, m.sq.1, hθ]
    · rw [Hecke.ProdGalois.grpSchemeSquareProductMap_comp_snd, m.sq.2, hθ]
  have hmon' : IsMonHom (asIso θ).hom := hmon
  have hinvmon : IsMonHom (inv θ) := (inferInstance : IsMonHom (asIso θ).inv)
  refine ⟨hmon, hact, ⟨inv θ, 1, hinvmon, ?_, ?_, ?_, by simp⟩, ⟨1, by simp, ?_, ?_⟩, ?_⟩
  · intro c
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← hact c, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · rw [pow_one]
    exact IsIso.hom_inv_id θ
  · rw [pow_one]
    exact IsIso.inv_hom_id θ
  · refine ⟨?_⟩
    rw [hsq]
    exact LBIso.trans (LB.isLB_linComb o.isLB _ _) o.isLB (pull_isLB o'.isLB _)
      (lbIso_hecke_lbPow_one o.isLB) m.pol
  · exact (MB p).2.2 D G L 1 (Subgroup.one_mem _)
  · intro k _ _ t β ht
    obtain ⟨I₁, hI₁⟩ := o.geom k t β ht
    obtain ⟨I₂, hind, hev⟩ := (TP p D R gb S S s s (𝟙 S) (↑N) o' o m k t).2 I₁
    obtain ⟨J, hJ, hJe⟩ := tiso_congr o' (Category.comp_id t) I₂ (hind hI₁)
    refine ⟨I₁, J, hI₁, hJ, ?_⟩
    intro n hn hcop x y
    have key : I₁.ev n x ≫ θ = J.ev n x := by
      ext
      exact (hev n x).trans (hJe n x).symm
    rw [key]
    have hint : Integ L 1 := by
      intro v hv
      simpa using hv
    have hR := (RC p D G L R gb S s (↑N) (↑N) (↑N) o' o' o' k t J J J (𝟙 _) (𝟙 _) 1 1
      inferInstance inferInstance hint).1 n hn hcop x y
    simpa using hR
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsogFEt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isUnit_nat_of_rat {R : Type} [CommRing R] [Algebra ℚ R] {S : Scheme.{0}} (s : S ⟶ Sp R) {d : ℕ}
    (hd : 0 < d) : IsUnit (d : Γ(S, ⊤)) := by
  have hR : IsUnit (d : R) := by
    have hq : IsUnit (algebraMap ℚ R (d : ℚ)) :=
      (isUnit_iff_ne_zero.mpr (by exact_mod_cast hd.ne')).map _
    simpa using hq
  have h := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
  simpa using h

theorem UpperTheory.Gal.G3.pIsogFEt :
    IsogFEt := by
  intro R _ _ S s A A' _ _ _ _ hA hA' ψ ψ' d hd hψ hψ' h1 h2
  exact GlobalTheory.UPel.HT.ES.isFinite_etale_surjective_of_isQuasiInv S A A' d ψ ψ' hA hA'
    (isUnit_nat_of_rat s hd) ⟨hψ, hψ', h1, h2⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPolUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u


open GlobalTheory.CechPic GlobalTheory.BirigUniq in
theorem UpperTheory.Gal.G3.pPolUniq :
    PolUniq := by
  intro S A A' _ _ _ _ hA hA' ψ hm hfin het hsurj P Q hP hQ h1 h2 h3 h4 hiso
  have hfl : Flat (Over.Hom.left ψ) := inferInstance
  have hqc : QuasiCompact (Over.Hom.left ψ) := inferInstance
  have hcls : ∀ {Y : Scheme} (F : Y ⟶ (G2 A').left),
      pull F (cls P hP - cls Q hQ) = cls (P.pull F) (pull_isLB hP F) - cls (Q.pull F) (pull_isLB hQ F) := by
    intro Y F
    rw [map_sub]
    rfl
  have hzero : ∀ {Y : Scheme} (F : Y ⟶ (G2 A').left), LBIso (P.pull F) (Q.pull F) →
      pull F (cls P hP - cls Q hQ) = 0 := by
    intro Y F h
    rw [hcls, sub_eq_zero]
    exact (cls_eq_iff _ _).mpr h
  set d := cls P hP - cls Q hQ with hd
  have hs1 : pull (Over.Hom.left (lift (1 : A' ⟶ A') (𝟙 A'))) d = 0 := by
    rw [hcls, sub_eq_zero, (cls_eq_zero_iff _).mpr h1, (cls_eq_zero_iff _).mpr h3]
  have hs2 : pull (Over.Hom.left (lift (𝟙 A') (1 : A' ⟶ A'))) d = 0 := by
    rw [hcls, sub_eq_zero, (cls_eq_zero_iff _).mpr h2, (cls_eq_zero_iff _).mpr h4]
  have hsq : pull (Hecke.sq2 ψ) d = 0 := hzero _ hiso
  let E : A' ⊗ A ⟶ A' ⊗ A' := lift (fst A' A) (snd A' A ≫ ψ)
  let W : A ⊗ A' ⟶ A' ⊗ A := lift (snd A A') (fst A A')
  let W' : A' ⊗ A ⟶ A ⊗ A' := lift (snd A' A) (fst A' A)
  have hf : pull (Over.Hom.left (W ≫ E)) d = 0 := by
    refine pic_eq_zero_of_fpqc A A' A hA ψ hfl hsurj hqc _ ?_ ?_
    · rw [← pull_comp_left]
      have : lift (1 : A' ⟶ A) (𝟙 A') ≫ W ≫ E = lift (𝟙 A') (1 : A' ⟶ A') := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [E, W, one_comp_monHom]
      rw [this, hs2]
    · rw [← pull_comp_left]
      have : lift (fst A A) (snd A A ≫ ψ) ≫ W ≫ E
          = lift (snd A A) (fst A A) ≫ lift (fst A A ≫ ψ) (snd A A ≫ ψ) := by
        apply CartesianMonoidalCategory.hom_ext <;> simp [E, W]
      rw [this, pull_comp_left]
      have h' : pull (Over.Hom.left (lift (fst A A ≫ ψ) (snd A A ≫ ψ))) d = 0 := hsq
      rw [h', map_zero]
  have he : pull (Over.Hom.left E) d = 0 := by
    have : W' ≫ W ≫ E = E := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [E, W, W']
    rw [← this, pull_comp_left, hf, map_zero]
  have hd0 : d = 0 := pic_eq_zero_of_fpqc A' A' A hA' ψ hfl hsurj hqc d hs1 he
  rw [hd, sub_eq_zero] at hd0
  exact (cls_eq_iff hP hQ).mp hd0
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMapOfIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pMapOfIso :
    MapOfIso := by
  intro G₀ R _ _ gb S s N o o' θ hiso hmon hact hpol heta
  haveI : IsIso θ.left := (Over.forget S).map_isIso θ
  refine ⟨⟨θ.left, Hecke.sq2 θ, ⟨IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩, ?_⟩, ⟨?_, ?_⟩,
    fun c => ?_, hpol, fun y => ?_⟩, rfl⟩
  · intro T x y x₀ y₀ hx hy
    let u : Over.mk (T.hom ≫ 𝟙 S) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have ex : x₀ = u ≫ x ≫ θ := Over.OverMorphism.ext (by simp [u, hx])
    have ey : y₀ = u ≫ y ≫ θ := Over.OverMorphism.ext (by simp [u, hy])
    rw [ex, ey, ← MonObj.comp_mul, ← MonObj.mul_comp]
    simp [u]
  · rw [Hecke.sq2, ← Over.comp_left, lift_fst, Over.comp_left]
  · rw [Hecke.sq2, ← Over.comp_left, lift_snd, Over.comp_left]
  · rw [← Over.comp_left, hact c, Over.comp_left]
  · rw [← Over.comp_left, heta y, Category.id_comp]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransUniqPt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransUniqPt :
    MultBasic → IsogFEt → TransKer → QuotUniq → PolUniq → MapOfIso → TransUniqPt := by
  intro hMB hFE hTK hQU hPU hMI p _ D G L R _ _ gb k _ _ s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm tr₁ tr₂
  have hK := hTK p D G L R gb (Sp k) s N' N o o₁ o₂ ψ₁ ψ₂ h hint hadm tr₁ tr₂
  obtain ⟨mon₁, -, ⟨ψ₁', d₁, mon₁', -, e₁, e₁', cop₁⟩, ⟨c₁, hc₁, ⟨lb₁⟩, t₁, t₁', i₁, i₁', tt₁, hm₁⟩, -⟩ := id tr₁
  obtain ⟨mon₂, -, ⟨ψ₂', d₂, mon₂', -, e₂, e₂', cop₂⟩, ⟨c₂, hc₂, ⟨lb₂⟩, t₂, t₂', i₂, i₂', tt₂, hm₂⟩, -⟩ := id tr₂
  have dpos : ∀ d : ℕ, d.Coprime p → 0 < d := fun d hd => Nat.pos_of_ne_zero fun h0 => by
    subst h0
    exact (Fact.out : p.Prime).one_lt.ne' (by simpa using hd)
  obtain ⟨f₁, et₁, sj₁⟩ := hFE R (Sp k) s o.A o₁.A o.ab o₁.ab ψ₁ ψ₁' d₁ (dpos _ cop₁) mon₁ mon₁' e₁ e₁'
  obtain ⟨f₂, et₂, sj₂⟩ := hFE R (Sp k) s o.A o₂.A o.ab o₂.ab ψ₂ ψ₂' d₂ (dpos _ cop₂) mon₂ mon₂' e₂ e₂'
  obtain ⟨θ, isoθ, monθ, hθ⟩ := hQU k o.A o₁.A o₂.A o.ab o₁.ab o₂.ab ψ₁ ψ₂ mon₁ mon₂ f₁ et₁ sj₁ f₂ et₂ sj₂
    (fun Ω _ _ t a => (hK Ω t).1 a)
  have lin₁ := tr₁.2.1
  have lin₂ := tr₂.2.1
  haveI := f₁
  haveI := et₁
  haveI := sj₁
  haveI : Epi ψ₁.left := Flat.epi_of_flat_of_surjective _
  have cancel : ∀ {X : Over (Sp k)} (a b : o₁.A ⟶ X), ψ₁ ≫ a = ψ₁ ≫ b → a = b := fun a b e =>
    Over.OverMorphism.ext ((cancel_epi ψ₁.left).1 (by simpa using congrArg (·.left) e))
  have lin : ∀ c, o₁.act.act c ≫ θ = θ ≫ o₂.act.act c := fun c => cancel _ _ (by
    rw [← Category.assoc, ← lin₁ c, Category.assoc, hθ, lin₂ c, ← hθ, Category.assoc])
  have hcc : c₁ = c₂ := (hMB p).1 (mul h) c₁ c₂ hc₁ hc₂ ⟨t₁, t₁', i₁, i₁', tt₁, hm₁⟩ ⟨t₂, t₂', i₂, i₂', tt₂, hm₂⟩
  subst hcc
  have hPo := o.isLB
  have hP1 := o₁.isLB
  have hP2 := o₂.isLB
  have hQ : (o₂.P.pull (Hecke.sq2 θ)).IsLB := pull_isLB hP2 _
  have sqc : Hecke.sq2 ψ₁ ≫ Hecke.sq2 θ = Hecke.sq2 ψ₂ := by
    rw [← hθ]
    simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.assoc]
  have key : LBIso (o₁.P.pull (Hecke.sq2 ψ₁)) ((o₂.P.pull (Hecke.sq2 θ)).pull (Hecke.sq2 ψ₁)) := by
    refine (GlobalTheory.CechPic.cls_eq_iff (pull_isLB hP1 _) (pull_isLB hQ _)).1 ?_
    have a1 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hPo _ _) (pull_isLB hP1 _)).2 lb₁
    have a2 := (GlobalTheory.CechPic.cls_eq_iff (LB.isLB_linComb hPo _ _) (pull_isLB hP2 _)).2 lb₂
    rw [← a1, a2, GlobalTheory.CechPic.cls_pull hP2, GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2,
      ← GlobalTheory.CechPic.pull_comp, sqc]
  have r₁ : ∃ t : ((o₂.P.pull (Hecke.sq2 θ)).pull (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left).Gen, t.IsGen := by
    refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ _)).1 ?_
    have e : (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left ≫ Hecke.sq2 θ =
        θ.left ≫ (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left := by
      simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
        Category.comp_id, one_comp, comp_one]
    rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hP2 _ (pull_isLB hP2 _), (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _)).2 o₂.rig₁, map_zero]
  have r₂ : ∃ t : ((o₂.P.pull (Hecke.sq2 θ)).pull (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left).Gen, t.IsGen := by
    refine (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hQ _)).1 ?_
    have e : (lift (𝟙 o₁.A) (1 : o₁.A ⟶ o₁.A)).left ≫ Hecke.sq2 θ =
        θ.left ≫ (lift (𝟙 o₂.A) (1 : o₂.A ⟶ o₂.A)).left := by
      simp only [Hecke.sq2, ← Over.comp_left, comp_lift, lift_fst_assoc, lift_snd_assoc, Category.id_comp,
        Category.comp_id, one_comp, comp_one]
    rw [GlobalTheory.CechPic.cls_pull hQ, GlobalTheory.CechPic.cls_pull hP2, ← GlobalTheory.CechPic.pull_comp, e, GlobalTheory.CechPic.pull_comp,
      ← GlobalTheory.CechPic.cls_pull hP2 _ (pull_isLB hP2 _), (GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hP2 _)).2 o₂.rig₂, map_zero]
  have pol : LBIso o₁.P (o₂.P.pull (Hecke.sq2 θ)) :=
    hPU (Sp k) o.A o₁.A o.ab o₁.ab ψ₁ mon₁ f₁ et₁ sj₁ o₁.P _ hP1 hQ o₁.rig₁ o₁.rig₂ r₁ r₂ key
  have lev : ∀ y, o₁.eta y ≫ θ = o₂.eta y := by
    intro y
    obtain ⟨v, hv⟩ := sj₁.surj (UpperTheory.Gal.TranscendenceTraces.pt (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y).left)
    obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ₁.left k (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y).left v hv
    let a : Over.mk (𝟙 (Sp k)) ⟶ o.A := Over.homMk z (by
      have w1 := Over.w ψ₁
      have w2 := Over.w (toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y)
      simp only [Over.mk_hom] at w2 ⊢
      rw [← w1, ← Category.assoc, hz, w2])
    have ha : a ≫ ψ₁ = toUnit _ ≫ o₁.eta y := Over.OverMorphism.ext hz
    have hb := ((hK k (𝟙 _)).2 a y).1 ha
    have e : toUnit (Over.mk (𝟙 (Sp k))) ≫ o₁.eta y ≫ θ = toUnit (Over.mk (𝟙 (Sp k))) ≫ o₂.eta y := by
      rw [← Category.assoc, ← ha, Category.assoc, hθ, hb]
    let i : 𝟙_ (Over (Sp k)) ⟶ Over.mk (𝟙 (Sp k)) := Over.mkIdTerminal.from _
    have hi : i ≫ toUnit (Over.mk (𝟙 (Sp k))) = 𝟙 _ := toUnit_unique _ _
    have e' := congrArg (i ≫ ·) e
    simpa [← Category.assoc, hi] using e'
  obtain ⟨m, hm⟩ := hMI D.toG R gb (Sp k) s N.1 o₁ o₂ θ isoθ monθ lin pol lev
  exact ⟨m, by rw [hm, ← hθ, Over.comp_left]⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDeep
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem oActN_act_natCast_eq_one_pow {S : Scheme} {O : Type} [Ring O] {G : Over S} [GrpObj G]
    (a : GlobalTheory.UPel.HT.OActN O G) (n : ℕ) : a.act (n : O) = 𝟙 G ^ n := by
  induction n with
  | zero =>
    have h := a.add 0 0
    rw [add_zero] at h
    have h2 := congrArg (· * (a.act 0)⁻¹) h
    simp only [mul_inv_cancel, mul_inv_cancel_right] at h2
    rw [Nat.cast_zero, pow_zero]
    exact h2.symm
  | succ n ih =>
    rw [Nat.cast_succ, a.add, ih, a.one, pow_succ]

theorem UpperTheory.Gal.G3.pTransDeep :
    SysOf → AdmOf → FullOf → RelArith → TransDeep := by
  intro hSys hAdm hFull hRel p _ D G L R _ _ gb h hI
  obtain ⟨f, u, c, k, hsys, hm, hk, hf⟩ := hSys p D G L h hI
  obtain ⟨hc, hkp, hck, hlin, hcomp, hEF, hsurj⟩ := hsys
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Nat.coprime_zero_left p |>.mp hkp) (Fact.out : Nat.Prime p).one_lt.ne'
    · exact hpos
  refine ⟨k, hkp, fun N => hAdm p D G L h k N hI hk0 hk, ?_⟩
  intro N S _ s o'
  have hρ : gb.ρ = (RingHom.id R) (GenCmp.baseOf gb).ρ := rfl
  have ht : ∀ i, gb.t i = (RingHom.id R).comp ((GenCmp.baseOf gb).t i) := fun i => rfl
  let o1 := GenCmp.toObj hρ ht o' (GenCmp.genericObject_kernelCondition o')
  obtain ⟨o2, ψ, hψm, hψa, hψe, hgal, ⟨hlb⟩, -⟩ :=
    GlobalTheory.T.exists_hecke_translate_locallyNoetherian_base p D R (GenCmp.baseOf gb) f u c k N N.2.1 N.2.2 hc hkp hck hlin hcomp hEF hsurj S _ o1
  let o3 := GenCmp.rebase (t := s) hρ ht rfl o2
  let o : GObj gb N s := GenCmp.toGObj o3 (GenCmp.geomFull N.2.2 o3)
  refine ⟨o, ψ, ?_⟩
  unfold UpperTheory.Gal.Int.Geo.IsTrans
  haveI := hψm
  haveI : Epi (Over.Hom.left ψ) := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
  haveI : Epi ψ := Over.epi_of_epi_left ψ
  obtain ⟨ψ', hψ'm, hψψ'⟩ := GlobalTheory.HomDescent.exists_desc S o1.A o2.A o1.A
    (HeckeAd.heckeSubA o1 (f (↑N * k)) ↑N) ψ hψm hgal (o1.act.act (k : D.O)) (o1.act.hom _)
    (fun g hg => by
      rw [oActN_act_natCast_eq_one_pow, comp_pow, Category.comp_id, HeckeAd.pow_eq_one_of_mem o1 _ g hg])
  refine ⟨hψm, hψa, ⟨ψ', k, hψ'm, ?_, ?_, ?_, hkp⟩, ?_, ?_⟩
  · intro a
    change o2.act.act a ≫ ψ' = ψ' ≫ o1.act.act a
    apply (cancel_epi ψ).1
    rw [← Category.assoc, ← hψa a, Category.assoc, hψψ', ← Category.assoc, hψψ',
      ← o1.act.mul, ← o1.act.mul, Nat.cast_comm]
  · change ψ ≫ ψ' = 𝟙 o1.A ^ k
    rw [hψψ', oActN_act_natCast_eq_one_pow]
  · change ψ' ≫ ψ = 𝟙 o2.A ^ k
    apply (cancel_epi ψ).1
    rw [← Category.assoc, hψψ', oActN_act_natCast_eq_one_pow, pow_comp, comp_pow, Category.id_comp,
      Category.comp_id]
  · obtain ⟨t, t', ht1, ht2, ht3, ht4⟩ := hm
    exact ⟨k ^ 2 / c, Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hck) (Nat.Coprime.pow_left 2 hkp),
      ⟨hlb⟩, t, t', ht1, ht2, ht3, ht4⟩
  · intro kk _ _ t β htβ
    obtain ⟨I', hI'⟩ := o'.geom kk t β htβ
    obtain ⟨J0, hJ0e, hJ0r⟩ := HeckeAd.TateTranslAt.exists_tateIsoO_of_given D (GenCmp.baseOf gb) f u c k
      N hc hkp N.2.1 N.2.2 hck hlin hcomp hEF hsurj o1 o2.A o2.act ψ o2.ab hψm hgal hψa o2.P o2.isLB hlb
      kk t β (GenCmp.tateRestrict I') (fun y => hI' y)
    obtain ⟨I'', hI''⟩ := hFull p D R gb S s N o kk t J0
    have hNpos : 0 < (N : ℕ) := lt_of_lt_of_le (by norm_num) N.2.1
    refine ⟨I', I'', hI', fun y => ?_, ?_⟩
    · rw [hI'' _ hNpos N.2.2, ← hJ0e y]
      change toUnit (Over.mk t) ≫ o2.eta y = _
      rw [hψe y]
    · exact hRel p D G L R gb S s N (↑N * k) o' o kk t I' I'' ψ h f u c k hψm hI
        ⟨hc, hkp, hck, hlin, hcomp, hEF, hsurj⟩ hf
        (fun n hn hnp x => by rw [hI'' n hn hnp]; exact hJ0r n hn hnp x)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransIso :
    IsoPts → IsogFEt → TransIso := by
  intro IP IF p _ D G L R _ _ gb S s N' N o' o ψ u hu T
  obtain ⟨hmon, -, ⟨ψ', d, hψ', -, hd, hd', hdp⟩, -, tate⟩ := T
  haveI := hmon
  haveI := hψ'
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with rfl | h0
    · rw [Nat.coprime_zero_left] at hdp
      exact absurd hdp (Fact.out : p.Prime).one_lt.ne'
    · exact h0
  obtain ⟨hfin, het, hsurj⟩ := IF R S s o'.A o.A o'.ab o.ab ψ ψ' d hd0 hmon hψ' hd hd'
  haveI := het
  haveI := hfin
  have hiso : IsIso ψ.left := by
    apply IP ψ.left
    intro Ω _ _ z
    obtain ⟨v, hv⟩ := hsurj.surj (UpperTheory.Gal.TranscendenceTraces.pt z)
    obtain ⟨y, hy, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds ψ.left Ω z v hv
    refine ⟨y, hy, fun y₂ hy₂ => ?_⟩
    let t : sp Ω ⟶ S := y ≫ o'.A.hom
    have ht2 : y₂ ≫ o'.A.hom = t := by
      rw [← Over.w ψ, ← Category.assoc, hy₂, ← hy, Category.assoc, Over.w ψ]
    let a₁ : Over.mk t ⟶ o'.A := Over.homMk y rfl
    let a₂ : Over.mk t ⟶ o'.A := Over.homMk y₂ ht2
    have hc : a₁ ≫ ψ = a₂ ≫ ψ := by
      ext
      simp [a₁, a₂, hy, hy₂]
    have ha : (a₂ * a₁⁻¹) ≫ ψ = 1 := by
      rw [MonObj.mul_comp, GrpObj.inv_comp, ← hc, mul_inv_cancel]
    have had : (a₂ * a₁⁻¹) ^ d = 1 := by
      have e : (a₂ * a₁⁻¹) ^ d = (a₂ * a₁⁻¹) ≫ ψ ≫ ψ' := by
        rw [hd, MonObj.comp_pow, Category.comp_id]
      rw [e, ← Category.assoc, ha, MonObj.one_comp]
    let β : R →+* Ω := (Spec.preimage (t ≫ s)).hom
    have hβ : t ≫ s = spMap β := by
      simp [β, spMap, Spec.map_preimage]
    obtain ⟨I', I'', -, -, hrel⟩ := tate Ω t β hβ
    obtain ⟨x, hx⟩ := (I'.onto d hd0 _).mp had
    have h0 : I'.ev d x ≫ ψ = I''.ev d 0 := by
      rw [hx, ha, HeckeRestrict.ev_zero]
    obtain ⟨w, hw, hxw⟩ := (hrel d hd0 hdp x 0).mp h0
    have hinv : u⁻¹ ∈ L.KN 1 := Subgroup.inv_mem _ hu
    have hdw : d • w = L.actG u (inAf D x) := by
      rw [hxw]
      simp [inAf]
    have hxa : inAf D x = d • L.actG u⁻¹ w := by
      rw [← map_nsmul, hdw, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    obtain ⟨z', hz'⟩ := LatDiv.eq_nsmul_of_inAf_eq_nsmul p D x d hd0 hdp _
      (UpperTheory.Gal.Int.Geo.integ_of_mem hinv w hw) hxa
    have h1 : a₂ * a₁⁻¹ = 1 := by
      rw [← hx]
      exact (I'.ker d hd0 x).mpr ⟨z', hz'⟩
    have h2 : a₂ = a₁ := mul_inv_eq_one.mp h1
    exact congrArg Over.Hom.left h2
  have : IsIso ((Over.forget S).map ψ) := hiso
  exact isIso_of_reflects_iso ψ (Over.forget S)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransOrbit
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem pol_step {S : Scheme.{0}} {A₁ A₂ A : Over S} [GrpObj A₁] [IsCommMonObj A₁] [GrpObj A₂] [IsCommMonObj A₂]
    [GrpObj A] [IsCommMonObj A] {P₁ : LB (G2 A₁).left} {P₂ : LB (G2 A₂).left} {P : LB (G2 A).left}
    (h₁ : P₁.IsLB) (h₂ : P₂.IsLB) (h : P.IsLB) (θ : A₁ ⟶ A₂) (ψ₁ : A₁ ⟶ A) (ψ₂ : A₂ ⟶ A) (e : θ ≫ ψ₂ = ψ₁)
    (i₁ : LBIso (Hecke.lbPow P₁ 1) (P.pull (Hecke.sq2 ψ₁))) (i₂ : LBIso (Hecke.lbPow P₂ 1) (P.pull (Hecke.sq2 ψ₂))) :
    LBIso (Hecke.lbPow P₁ 1) (P₂.pull (Hecke.sq2 θ)) := by
  have pw : ∀ {X : Scheme} (L : LB X), L.IsLB → (Hecke.lbPow L 1).IsLB := by
    intro X L hL
    unfold Hecke.lbPow
    exact LB.isLB_linComb hL _ _
  have c₁ := (GlobalTheory.CechPic.cls_eq_iff (pw P₁ h₁) (pull_isLB h (Hecke.sq2 ψ₁))).mpr i₁
  have c₂ := (GlobalTheory.CechPic.cls_eq_iff (pw P₂ h₂) (pull_isLB h (Hecke.sq2 ψ₂))).mpr i₂
  rw [Hecke.Comp.cls_lbPow' h₁ 1 (pw P₁ h₁), one_smul] at c₁
  rw [Hecke.Comp.cls_lbPow' h₂ 1 (pw P₂ h₂), one_smul] at c₂
  rw [GlobalTheory.CechPic.cls_pull h] at c₁ c₂
  apply (GlobalTheory.CechPic.cls_eq_iff (pw P₁ h₁) (pull_isLB h₂ (Hecke.sq2 θ))).mp
  rw [Hecke.Comp.cls_lbPow' h₁ 1 (pw P₁ h₁), one_smul, GlobalTheory.CechPic.cls_pull h₂, c₁, c₂, ← e,
    Hecke.Comp.grpSchemeSquareProductMap_comp, GlobalTheory.CechPic.pull_comp]

private theorem isMonHom_inv' {C : Type*} [Category C] [MonoidalCategory C] {A B : C} [MonObj A] [MonObj B]
    (f : A ⟶ B) [IsIso f] [IsMonHom f] : IsMonHom (inv f) := by
  have : IsMonHom (asIso f).inv := inferInstance
  simpa using this

theorem UpperTheory.Gal.G3.pTransOrbit :
    MultBasic → RelComp → TateDiff → TateTwist → KNCong → TransIso → TransOrbit := by
  intro hMB hRC hTD hTT hKN hTI p _ D G L R _ _ gb k _ _ s N' N o₁ o₂ o ψ₁ ψ₂ h₁ h₂
  have one_mem : (1 : G.GAf) ∈ L.KN 1 := (L.KN 1).one_mem
  have kn1 : ∀ {M : ℕ} {g : G.GAf}, g ∈ L.KN M → g ∈ L.KN 1 :=
    fun hg => UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hg
  haveI : IsIso ψ₁ := hTI p D G L R gb _ s _ _ o₁ o ψ₁ 1 one_mem h₁
  haveI : IsIso ψ₂ := hTI p D G L R gb _ s _ _ o₂ o ψ₂ 1 one_mem h₂
  unfold UpperTheory.Gal.Int.Geo.IsTrans at h₁ h₂
  haveI hm₁ : IsMonHom ψ₁ := h₁.1
  haveI hm₂ : IsMonHom ψ₂ := h₂.1
  haveI hmi₁ : IsMonHom (inv ψ₁) := isMonHom_inv' ψ₁
  haveI hmi₂ : IsMonHom (inv ψ₂) := isMonHom_inv' ψ₂
  have hNpos : 0 < (N' : ℕ) := by
    have := N'.2.1
    omega
  have hNcop : (N' : ℕ).Coprime p := N'.2.2
  have flip : ∀ {X Y : Over (Sp k)} (a : X ⟶ X) (b : Y ⟶ Y) (ψ : X ⟶ Y) [IsIso ψ],
      a ≫ ψ = ψ ≫ b → b ≫ inv ψ = inv ψ ≫ a := by
    intro X Y a b ψ _ h
    rw [IsIso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have rev : ∀ {k' : Type} [Field k'] {t : Sp k' ⟶ Sp k} (I : UpperTheory.Gal.Int.Geo.TIso o₂ t)
      (J : UpperTheory.Gal.Int.Geo.TIso o t),
      UpperTheory.Gal.G3.Rel L I J ψ₂ 1 → UpperTheory.Gal.G3.Rel L J I (inv ψ₂) 1 := by
    intro k' _ t I J hIJ n hn hc x y
    rw [IsIso.comp_inv_eq]
    refine (eq_comm.trans (hIJ n hn hc y x)).trans ?_
    simp only [map_one, Module.End.one_apply]
    constructor
    · rintro ⟨v, hv, e⟩
      exact ⟨-v, neg_mem hv, by rw [e, smul_neg, add_neg_cancel_right]⟩
    · rintro ⟨v, hv, e⟩
      exact ⟨-v, neg_mem hv, by rw [e, smul_neg, add_neg_cancel_right]⟩
  have key : ∀ (k' : Type) [Field k'] [IsAlgClosed k'] (t : Sp k' ⟶ Sp k) (β' : R →+* k'),
      t ≫ s = spMap β' →
      ∃ (I' : UpperTheory.Gal.Int.Geo.TIso o₁ t) (I'' : UpperTheory.Gal.Int.Geo.TIso o₂ t),
        UpperTheory.Gal.G3.Ind o₁ I' ∧ UpperTheory.Gal.G3.Ind o₂ I'' ∧
          ∃ w ∈ L.KN N, UpperTheory.Gal.G3.Rel L I' I'' (ψ₁ ≫ inv ψ₂) w := by
    intro k' _ _ t β' ht
    obtain ⟨I₁', I₁'', a₁, b₁, r₁⟩ := h₁.2.2.2.2 k' t β' ht
    obtain ⟨I₂', I₂'', a₂, b₂, r₂⟩ := h₂.2.2.2.2 k' t β' ht
    obtain ⟨w, hw, rr⟩ := hTD p D G L R gb _ s N o k' t I₁'' I₂'' b₁ b₂
    have s1 := (hRC p D G L R gb _ s _ _ _ o₁ o o k' t I₁' I₁'' I₂'' ψ₁ (𝟙 _) 1 w hm₁ inferInstance
      (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw))).2 r₁ rr
    have s2 := (hRC p D G L R gb _ s _ _ _ o₁ o o₂ k' t I₁' I₂'' I₂' (ψ₁ ≫ 𝟙 _) (inv ψ₂) (w * 1) 1
      inferInstance hmi₂ (UpperTheory.Gal.Int.Geo.integ_of_mem one_mem)).2 s1 (rev I₂' I₂'' r₂)
    refine ⟨I₁', I₂', a₁, a₂, w, hw, ?_⟩
    rw [Category.comp_id, _root_.mul_one, _root_.one_mul] at s2
    exact s2
  obtain ⟨I₀', I₀'', hI₀', hI₀'', w₀, hw₀, r₀⟩ :=
    key k (𝟙 (Sp k)) (Spec.preimage s).hom (by simp [spMap])
  obtain ⟨c₁, hc₁, ⟨i₁⟩, t₁, t₁', x1, x2, x3, x4⟩ := h₁.2.2.2.1
  have e₁ : c₁ = 1 := (hMB p).1 _ c₁ 1 hc₁ (Nat.coprime_one_left p) ⟨t₁, t₁', x1, x2, x3, x4⟩
    ((hMB p).2.2 D G L 1 one_mem)
  subst e₁
  obtain ⟨c₂, hc₂, ⟨i₂⟩, t₂, t₂', y1, y2, y3, y4⟩ := h₂.2.2.2.1
  have e₂ : c₂ = 1 := (hMB p).1 _ c₂ 1 hc₂ (Nat.coprime_one_left p) ⟨t₂, t₂', y1, y2, y3, y4⟩
    ((hMB p).2.2 D G L 1 one_mem)
  subst e₂
  refine ⟨w₀, hw₀, ψ₁ ≫ inv ψ₂, ?_, by simp⟩
  unfold UpperTheory.Gal.Int.Geo.IsTrans
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · intro c
    rw [← Category.assoc, h₁.2.1 c, Category.assoc, flip _ _ ψ₂ (h₂.2.1 c)]
    simp only [Category.assoc]
  · refine ⟨ψ₂ ≫ inv ψ₁, 1, inferInstance, ?_, by simp, by simp, Nat.coprime_one_left p⟩
    intro c
    rw [← Category.assoc, h₂.2.1 c, Category.assoc, flip _ _ ψ₁ (h₁.2.1 c)]
    simp only [Category.assoc]
  · exact ⟨1, Nat.coprime_one_left p,
      ⟨pol_step o₁.isLB o₂.isLB o.isLB (ψ₁ ≫ inv ψ₂) ψ₁ ψ₂ (by simp) i₁ i₂⟩,
      (hMB p).2.2 D G L w₀ (kn1 hw₀)⟩
  · intro k' _ _ t β' ht
    obtain ⟨I', I'', hI', hI'', w, hw, r⟩ := key k' t β' ht
    have A : ∀ x y : D.La, (∃ v ∈ LaHat D, (L.actG w₀) (inAf D x) = inAf D y + (N' : ℕ) • v) →
        ∃ v ∈ LaHat D, (L.actG w) (inAf D x) = inAf D y + (N' : ℕ) • v := by
      intro x y hxy
      have e0 := (r₀ N' hNpos hNcop x y).mpr hxy
      apply (r N' hNpos hNcop x y).mp
      rw [← hI₀' x, ← hI₀'' y] at e0
      rw [← hI' x, ← hI'' y]
      have hu : toUnit (Over.mk t) =
          Over.homMk (U := Over.mk t) (V := Over.mk (𝟙 (Sp k))) t (by simp) ≫ toUnit (Over.mk (𝟙 (Sp k))) :=
        toUnit_unique _ _
      rw [hu]
      simp only [Category.assoc] at e0 ⊢
      rw [e0]
    have cong : ∀ x : D.La, ∃ m ∈ LaHat D,
        (L.actG (w₀ * w⁻¹)) (inAf D x) = inAf D x + (N' : ℕ) • m := by
      intro x
      have hwi : w⁻¹ ∈ L.KN 1 := (L.KN 1).inv_mem (kn1 hw)
      obtain ⟨x', m, hm, hz⟩ := exists_inAf_add_nsmul_of_mem_laHat p D N' hNpos hNcop _
        (UpperTheory.Gal.Int.Geo.integ_of_mem hwi _ (GlobalTheory.HeckeApprox.inAf_mem D x))
      obtain ⟨y', m₁, hm₁, e₁⟩ := exists_inAf_add_nsmul_of_mem_laHat p D N' hNpos hNcop _
        (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw₀) _ (GlobalTheory.HeckeApprox.inAf_mem D x'))
      obtain ⟨m₂, hm₂, e₂⟩ := A x' y' ⟨m₁, hm₁, e₁⟩
      have hback : (L.actG w) ((L.actG w⁻¹) (inAf D x)) = inAf D x := by
        rw [← Module.End.mul_apply, ← map_mul, _root_.mul_inv_cancel, map_one, Module.End.one_apply]
      refine ⟨m₁ - m₂ + ((L.actG w₀) m - (L.actG w) m), ?_, ?_⟩
      · exact add_mem (sub_mem hm₁ hm₂) (sub_mem (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw₀) _ hm)
          (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hw) _ hm))
      · rw [map_mul, Module.End.mul_apply, hz, map_add (f := _), map_nsmul, e₁]
        rw [hz, map_add (f := _), map_nsmul, e₂] at hback
        rw [← hback]
        simp only [smul_add, smul_sub]
        abel
    have hv : w₀ * w⁻¹ ∈ L.KN (N' : ℕ) :=
      hKN p D G L N' hNpos hNcop _ (mul_mem (kn1 hw₀) (inv_mem (kn1 hw))) cong
    obtain ⟨J, hJ, rJ⟩ := hTT p D G L R gb _ s N' o₂ k' t I'' hI'' _ hv
    refine ⟨I', J, hI', hJ, ?_⟩
    have := (hRC p D G L R gb _ s _ _ _ o₁ o₂ o₂ k' t I' I'' J (ψ₁ ≫ inv ψ₂) (𝟙 _) w (w₀ * w⁻¹)
      inferInstance inferInstance (UpperTheory.Gal.Int.Geo.integ_of_mem (kn1 hv))).2 r rJ
    rw [Category.comp_id, _root_.inv_mul_cancel_right] at this
    exact this
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pTransFree :
    KNCong → TransFree := by
  intro hK p _ D G L R _ _ gb k _ _ s N o u hu hT
  obtain ⟨-, -, -, -, hp⟩ := hT
  obtain ⟨I', I'', h', h'', hr⟩ := hp k (𝟙 _) (Spec.preimage (𝟙 _ ≫ s)).hom (by
    simp [spMap])
  refine hK p D G L N.1 (by have := N.2.1; omega) N.2.2 u hu fun x => ?_
  exact (hr N.1 (by have := N.2.1; omega) N.2.2 x x).1 (by
    rw [← h' x, ← h'' x]; simp)
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PGenSm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pGenSm : GenSm := by
  intro p _ D R _ _ gb N X
  haveI : CharZero R := charZero_of_injective_algebraMap (algebraMap ℚ R).injective
  obtain ⟨M⟩ := GlobalTheory.T.harrisTaylorIntegralModel_nonempty p D R (GenCmp.baseOf gb) N.1 N.2.1 N.2.2
  obtain ⟨j, hoi, hci, hj, -⟩ := GenCmp.genModel_eq_genericFibre p D R (GenCmp.baseOf gb) R (RingHom.id R) gb
    rfl (fun _ => rfl) N.1 N.2.1 N.2.2 M X
  haveI := hoi
  haveI := hci
  haveI : IsQProjOver M.s := M.qproj
  haveI : SmoothOfRelativeDimension (D.a * (D.n - 1)) M.s := M.smooth
  haveI : IsSeparated M.s := GlobalTheory.ZM.isSeparated_of_isQProjOver M.qproj
  haveI : QuasiCompact M.s := quasiCompact_of_qProj M.qproj
  haveI : Smooth M.s := SmoothOfRelativeDimension.smooth (D.a * (D.n - 1)) M.s
  rw [← hj]
  refine ⟨inferInstance, inferInstance, inferInstance, fun hB => ?_⟩
  exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion j
    (GlobalTheory.ProjSpace.isProjOver_pullback_snd (RingHom.id R)
      (Model.isProjOver_of_compactB p D R (GenCmp.baseOf gb) N.1 N.2.1 N.2.2 hB M))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPowSm
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private lemma smooth_pow_hom {S : Scheme.{0}} (A : Over S) (hA : Smooth A.hom) (k : ℕ) :
    Smooth (GlobalTheory.KS.pow A k).hom := by
  have hiso : ∀ {X Y : Over S} (e : X ≅ Y), Smooth Y.hom → Smooth X.hom := by
    intro X Y e h
    rw [← Over.w e.hom]
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget S).mapIso e).hom)
    infer_instance
  have hprod : ∀ (Y Z : Over S), Smooth Y.hom → Smooth Z.hom → Smooth (Y ⨯ Z).hom := by
    intro Y Z hY hZ
    rw [← Over.w (prod.snd (X := Y) (Y := Z)), ← Over.prodLeftIsoPullback_hom_snd]
    infer_instance
  induction k with
  | zero =>
    exact hiso (((isLimitEquivIsTerminalOfIsEmpty _ _) (productIsProduct _)).uniqueUpToIso
      Over.mkIdTerminal) (by dsimp; infer_instance)
  | succ k ih =>
    exact hiso ((productIsProduct _).conePointUniqueUpToIso
      (extendFanIsLimit _ (productIsProduct fun _ : Fin k => A) (prodIsProd _ _))) (hprod _ _ hA ih)

theorem UpperTheory.Gal.G3.pPowSm :
    GenSm → PowSm := by
  intro hG p _ D R _ _ gb N X k
  obtain ⟨hs, hsep, -, hproj⟩ := hG p D R gb N X
  haveI := hs
  haveI := hsep
  haveI : Smooth X.univ.A.hom := X.univ.ab.smooth
  haveI : Smooth (GlobalTheory.KS.pow X.univ.A k).hom := smooth_pow_hom _ inferInstance k
  haveI : IsProper (GlobalTheory.KS.pow X.univ.A k).hom :=
    GlobalTheory.KS.Leray.isProper_pow_hom _ X.univ.ab.proper k
  refine ⟨inferInstance, inferInstance, fun hD => ?_⟩
  exact GlobalTheory.KS.isProjOver_pow R X.X X.s (hproj hD) X.univ.A X.univ.ab _
    (LB.isLB_pull X.univ.isLB _) X.univ.ample k
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PEtDesc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pEtDesc :
    ExtPts → EtDesc := by
  intro hE W Z Y B _ c _ _ _ pZ pY _ f hf hpts
  haveI : Flat c := inferInstance
  haveI : EffectiveEpi c := inferInstance
  haveI : IsReduced (pullback c c) := GlobalTheory.isReduced_of_smooth_of_isReduced (pullback.fst c c)
  have key : pullback.fst c c ≫ f = pullback.snd c c ≫ f := by
    refine hE pY _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, hf, ← Category.assoc, ← Category.assoc, pullback.condition]
    · intro Ω _ _ x
      refine hpts Ω (x ≫ pullback.fst c c) (x ≫ pullback.snd c c) ?_ |>.trans ?_ <;> simp [pullback.condition]
  refine ⟨inferInstance, EffectiveEpi.desc c f (fun {T} g₁ g₂ h => ?_), EffectiveEpi.fac _ _ _⟩
  have e₁ : pullback.lift g₁ g₂ h ≫ pullback.fst c c = g₁ := pullback.lift_fst _ _ _
  have e₂ : pullback.lift g₁ g₂ h ≫ pullback.snd c c = g₂ := pullback.lift_snd _ _ _
  calc g₁ ≫ f = pullback.lift g₁ g₂ h ≫ pullback.fst c c ≫ f := by rw [← Category.assoc, e₁]
    _ = pullback.lift g₁ g₂ h ≫ pullback.snd c c ≫ f := by rw [key]
    _ = g₂ ≫ f := by rw [← Category.assoc, e₂]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.GObjMapCast
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem gObjMap_comp_φ {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁}
    {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f)
    (h₂ : GObjMap o₂ o₃ g) : ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

private theorem gObjMap_cast {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {f f' : S₁ ⟶ S₂} (e : f = f') (m : GObjMap o₁ o₂ f) : ∃ m' : GObjMap o₁ o₂ f', m'.φ = m.φ := by
  subst e
  exact ⟨m, rfl⟩

theorem UpperTheory.Gal.G3.pPtEq :
    TransSelf → TransComp → TransPull → TransUniqPt → Rigid → PtEq := by
  intro hS hC hP hU hRg p _ D G L R _ _ gb N₁ N₂ N X₁ X₂ X h₁ h₂ g u π₁ Φ₁ π₂ Φ₂ w₁ w₂ i₁ i₂ a₁ a₂ hu he
    k _ _ s x y hx hy ox oy mx my θ hθ
  obtain ⟨e₁, o₁, ψ₁, f₁, t₁, rfl⟩ := w₁
  obtain ⟨e₂, o₂, ψ₂, f₂, t₂, rfl⟩ := w₂
  obtain ⟨o₁x, ⟨n₁⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero s x hx o₁
  obtain ⟨o₂y, ⟨n₂⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero s y hy o₂
  obtain ⟨ψ₁', t₁', c₁⟩ := hP p D G L R gb X₁.X (Sp k) X₁.s s x hx _ _ X₁.univ o₁ ox o₁x mx n₁ ψ₁ h₁ t₁
  obtain ⟨ψ₂', t₂', c₂⟩ := hP p D G L R gb X₂.X (Sp k) X₂.s s y hy _ _ X₂.univ o₂ oy o₂y my n₂ ψ₂ h₂ t₂
  have iu : Integ L u := UpperTheory.Gal.Int.Geo.integ_of_mem (UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu)
  have au : AdmK L N N u := fun v hv =>
    (L.KN N).mul_mem ((L.KN N).mul_mem hu hv) ((L.KN N).inv_mem hu)
  have t₃ := hC p D G L R gb (Sp k) s N₁ N₂ N ox oy o₂y θ ψ₂' g h₂ i₂ a₂ hθ t₂'
  have t₄ := hC p D G L R gb (Sp k) s N₁ N N ox o₂y o₂y (θ ≫ ψ₂') (𝟙 _) (h₂ * g) u iu au t₃
    ((hS p D G L R gb (Sp k) s N).1 o₂y u hu)
  rw [← he] at t₄
  obtain ⟨m, hm⟩ := hU p D G L R gb k s N₁ N ox o₁x o₂y ψ₁' _ h₁ i₁ a₁ t₁' t₄
  obtain ⟨A, hA⟩ := gObjMap_comp_φ n₁ f₁
  obtain ⟨B₀, hB₀⟩ := gObjMap_comp_φ n₂ f₂
  obtain ⟨B, hB⟩ := gObjMap_comp_φ m B₀
  have hxs : (x ≫ π₁) ≫ X.s = s := by rw [Category.assoc, e₁, hx]
  have hys : (𝟙 (Sp k) ≫ y ≫ π₂) ≫ X.s = s := by simp [Category.assoc, e₂, hy]
  have hxy : x ≫ π₁ = 𝟙 (Sp k) ≫ y ≫ π₂ :=
    (X.rep (Sp k) s o₁x).unique ⟨hxs, ⟨A⟩⟩ ⟨hys, ⟨B⟩⟩
  obtain ⟨B', hB'⟩ := gObjMap_cast hxy.symm B
  have hAB := hRg p D R gb X.X (Sp k) X.s s (x ≫ π₁) hxs N X.univ o₁x A B'
  refine ⟨by simpa using hxy, ?_⟩
  rw [hB', hB, hB₀, hA] at hAB
  calc mx.φ ≫ Over.Hom.left ψ₁ ≫ f₁.φ = (mx.φ ≫ Over.Hom.left ψ₁) ≫ f₁.φ := by rw [Category.assoc]
    _ = Over.Hom.left ψ₁' ≫ n₁.φ ≫ f₁.φ := by rw [← c₁, Category.assoc]
    _ = Over.Hom.left ψ₁' ≫ m.φ ≫ n₂.φ ≫ f₂.φ := by rw [hAB]
    _ = Over.Hom.left ((θ ≫ ψ₂') ≫ 𝟙 _) ≫ n₂.φ ≫ f₂.φ := by rw [← hm, Category.assoc]
    _ = Over.Hom.left θ ≫ (Over.Hom.left ψ₂' ≫ n₂.φ) ≫ f₂.φ := by simp
    _ = Over.Hom.left θ ≫ my.φ ≫ Over.Hom.left ψ₂ ≫ f₂.φ := by rw [c₂, Category.assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitUniq
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitUniq :
    GenSm → ExtPts → TransSelf → PtEq → WitUniq := by
  intro hG hE hS hP p _ D G L R _ _ gb N' N X' X h ih ah π Φ π' Φ' w w'
  have hsm : Smooth X'.s := (hG p D R gb N' X').1
  haveI : IsSeparated X.s := (hG p D R gb N X).2.1
  haveI : AlgebraicGeometry.IsReduced X'.X := GlobalTheory.isReduced_of_smooth_of_isReduced X'.s
  have pt : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ X'.X),
      ∃ ox : GObj gb N' (x ≫ X'.s), ∃ mx : GObjMap ox X'.univ x,
        x ≫ π = x ≫ π' ∧ mx.φ ≫ Φ = mx.φ ≫ Φ' := by
    intro Ω _ _ x
    obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ X'.s) x rfl X'.univ
    have t := (hS p D G L R gb (Sp Ω) (x ≫ X'.s) N').1 ox 1 (L.KN N').one_mem
    have e := hP p D G L R gb N' N' N X' X' X h h 1 1 π Φ π' Φ' w w' ih ih ah ah
      (L.KN N).one_mem (by simp) Ω (x ≫ X'.s) x x rfl rfl ox ox mx mx (𝟙 _) t
    exact ⟨ox, mx, e.1, by simpa using e.2⟩
  have hπ : π = π' := hE X.s π π' (by rw [w.1, w'.1]) fun Ω _ _ x => by
    obtain ⟨_, _, e, _⟩ := pt Ω x
    exact e
  refine ⟨hπ, ?_⟩
  haveI := X'.univ.ab
  haveI := X.univ.ab
  haveI : Smooth X'.univ.A.hom := IsAbelianScheme.smooth
  haveI : AlgebraicGeometry.IsReduced X'.univ.A.left :=
    GlobalTheory.isReduced_of_smooth_of_isReduced X'.univ.A.hom
  haveI : IsProper X.univ.A.hom := IsAbelianScheme.proper
  refine hE X.univ.A.hom Φ Φ' (by rw [w.w, w'.w, hπ]) fun Ω _ _ z => ?_
  obtain ⟨ox, mx, -, e⟩ := pt Ω (z ≫ X'.univ.A.hom)
  obtain ⟨l, hl, -⟩ := mx.cart.1.exists_lift z (𝟙 _) (by simp)
  calc z ≫ Φ = l ≫ mx.φ ≫ Φ := by rw [← Category.assoc, hl]
    _ = l ≫ mx.φ ≫ Φ' := by rw [e]
    _ = z ≫ Φ' := by rw [← Category.assoc, hl]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

namespace UpperTheory.Gal.G3

section Maps

open GlobalTheory.UPel.HT.Hecke

variable {G : GDatum} {R : Type} [CommRing R] [Algebra ℚ R]

private theorem exists_map_id {b : GBase G R} {N : ℕ} {S : Scheme.{0}} {s : S ⟶ Sp R} (o : GObj b N s) :
    ∃ m : GObjMap o o (𝟙 S), m.φ = 𝟙 _ :=
  ⟨{ φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
     act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }, rfl⟩

private theorem exists_map_comp {b : GBase G R} {N : ℕ} {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R}
    {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂} {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃}
    (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) : ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have sq : IsSquare (h₁.φ ≫ h₂.φ) (h₁.φ₂ ≫ h₂.φ₂) := by
    constructor
    · rw [Category.assoc, h₂.sq.1, ← Category.assoc, h₁.sq.1, Category.assoc]
    · rw [Category.assoc, h₂.sq.2, ← Category.assoc, h₁.sq.2, Category.assoc]
  have act : ∀ c, (o₁.act.act c).left ≫ (h₁.φ ≫ h₂.φ) = (h₁.φ ≫ h₂.φ) ≫ (o₃.act.act c).left := by
    intro c
    rw [← Category.assoc, h₁.act, Category.assoc, h₂.act, Category.assoc]
  have eta : ∀ y, (o₁.eta y).left ≫ (h₁.φ ≫ h₂.φ) = (f ≫ g) ≫ (o₃.eta y).left := by
    intro y
    rw [← Category.assoc, h₁.eta, Category.assoc, h₂.eta, Category.assoc]
  have H : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have H' : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ : PUnit => h₂.φ₂) (fun _ => 1) h₁.φ₂) H
  have pol : LBIso o₁.P (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol H'
  exact ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, sq, act, pol, eta⟩, rfl⟩

end Maps

end UpperTheory.Gal.G3

theorem UpperTheory.Gal.G3.pWitComp :
    TransSelf → TransComp → TransPull → WitComp := by
  intro hS hC hP
  intro p _ D G L R _ _ gb N₁ N₂ N₃ X₁ X₂ X₃ h h'
  refine ⟨fun u hu => ?_, fun hI hA π Φ π' Φ' hW hW' => ?_⟩
  · obtain ⟨m, hm⟩ := exists_map_id X₁.univ
    refine ⟨by simp, X₁.univ, 𝟙 _, m, (hS p D G L R gb X₁.X X₁.s N₁).1 X₁.univ u hu, ?_⟩
    rw [hm]
    simp
  · obtain ⟨hπ, o, ψ, φ, hT, hΦ⟩ := hW
    obtain ⟨hπ', o', ψ', φ', hT', hΦ'⟩ := hW'
    obtain ⟨o'', ⟨m''⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero X₁.s π hπ o'
    obtain ⟨ψ'', hT'', hsq⟩ := hP p D G L R gb X₂.X X₁.X X₂.s X₁.s π hπ _ _ X₂.univ o' o o'' φ m'' ψ' h' hT'
    have hTT := hC p D G L R gb X₁.X X₁.s N₁ N₂ N₃ X₁.univ o o'' ψ ψ'' h h' hI hA hT hT''
    obtain ⟨mm, hmm⟩ := exists_map_comp m'' φ'
    refine ⟨by rw [Category.assoc, hπ', hπ], o'', ψ ≫ ψ'', mm, hTT, ?_⟩
    rw [hmm, hΦ, hΦ', Over.comp_left, Category.assoc, Category.assoc, ← Category.assoc φ.φ, ← hsq,
      Category.assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitCart
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitCart :
    TransIso → WitCart := by
  intro hI p _ D G L R _ _ gb N' N X' X u hu π Φ hW
  obtain ⟨-, o, ψ, φ, hT, rfl⟩ := hW
  have hψ : IsIso ψ := hI p D G L R gb X'.X X'.s N' N X'.univ o ψ u hu hT
  have hl : IsIso ψ.left := inferInstanceAs (IsIso ((Over.forget _).map ψ))
  have h₁ : IsPullback ψ.left X'.univ.A.hom o.A.hom (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by rw [Over.w, Category.comp_id]⟩
  have h₂ := h₁.paste_horiz φ.cart.1
  rwa [Category.id_comp] at h₂
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitDeep
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitDeep :
    KNBasic → GenSm → TransDeep → WitComp → WitForget → WitDeep := by
  intro _ hSm hTD hWC hWF p _ D G L R _ _ gb X N' N h hI
  obtain ⟨k, hk, hAk, hex⟩ := hTD p D G L R gb h hI
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · exact absurd (Nat.coprime_zero_left _ |>.mp hk) (Fact.out : p.Prime).one_lt.ne'
    · exact hpos
  let Nk : Lv p := ⟨↑N * k, le_trans N.2.1 (Nat.le_mul_of_pos_right _ hk0), Nat.Coprime.mul_left N.2.2 hk⟩
  let M : Lv p := ⟨↑N' * (↑N * k), le_trans Nk.2.1 (Nat.le_mul_of_pos_left _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul_left N'.2.2 Nk.2.2⟩
  have hNkM : (↑Nk : ℕ) ∣ ↑M := Dvd.intro_left _ rfl
  refine ⟨M, Dvd.intro _ rfl, ?_, ?_⟩
  · intro u hu
    exact hAk N u (UpperTheory.Gal.Int.Geo.KN_anti hNkM hu)
  · haveI : Smooth (X Nk).s := (hSm p D R gb Nk (X Nk)).1
    haveI : IsLocallyNoetherian (X Nk).X := LocallyOfFiniteType.isLocallyNoetherian (X Nk).s
    obtain ⟨o, ψ, ht⟩ := hex N (X Nk).X (X Nk).s (X Nk).univ
    obtain ⟨π, ⟨hπ, ⟨φ⟩⟩, -⟩ := (X N).rep (X Nk).X (X Nk).s o
    have w₂ : Wit L h (X Nk) (X N) π (ψ.left ≫ φ.φ) := ⟨hπ, o, ψ, φ, ht, rfl⟩
    obtain ⟨c, Φc, w₁, -⟩ := hWF p D G L R gb Nk M hNkM (X Nk) (X M)
    have := (hWC p D G L R gb M Nk N (X M) (X Nk) (X N) 1 h).2 hI (hAk N) c Φc π _ w₁ w₂
    rw [_root_.mul_one] at this
    exact ⟨_, _, this⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PDescMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pDescMap :
    GenSm → EtDesc → PtEq → PtOrbit → WitCart → DescMap := by
  intro hSm hEt hEq hOrb hCart p _ D G L R _ _ gb M N' N XM X' X h hI hA' hA1 c Φc π₁ Φ₁ hWc hFin hEtc hSurj hW1
  have hAd : AdmK L (↑M) (↑N) h := by
    intro v hv
    have h1 := hA1 v hv
    have h2 : v ∈ L.KN ↑N' := by simpa using h1
    exact hA' v h2
  haveI hred : IsReduced XM.X :=
    (GlobalTheory.isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field R XM.X XM.s
      (hSm p D R gb M XM).1).1
  haveI hsep : IsSeparated X.s := (hSm p D R gb N X).2.1
  haveI := hFin
  haveI := hEtc
  haveI := hSurj
  have hsq : π₁ ≫ X.s = c ≫ X'.s := hW1.1.trans hWc.1.symm
  obtain ⟨hepi, π, hπ⟩ := hEt c X'.s X.s π₁ hsq (by
    intro Ω _ _ x y hxy
    obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, _⟩ := hOrb p D G L R gb M N' XM X' c Φc hWc Ω x y hxy
    have hu' : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hA' _ (inv_mem hu)
    have hh : h = h * u⁻¹ * h⁻¹ * (h * u) := by group
    exact (hEq p D G L R gb M M N XM XM X h h u (h * u⁻¹ * h⁻¹) π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI hI hAd hAd
      hu' hh Ω (x ≫ XM.s) x y rfl hys ox oy mx my θ hθ).1)
  have hπs : π ≫ X.s = X'.s := by
    rw [← cancel_epi c, ← Category.assoc, hπ, hW1.1, hWc.1]
  have wsq : ∀ {NN NN' : ℕ} (Y' : GenModel gb NN') (Y : GenModel gb NN) (g : G.GAf) (ρ : Y'.X ⟶ Y.X)
      (Ψ : Y'.univ.A.left ⟶ Y.univ.A.left), Wit L g Y' Y ρ Ψ → Ψ ≫ Y.univ.A.hom = Y'.univ.A.hom ≫ ρ := by
    rintro _ _ Y' Y g ρ Ψ ⟨_, o, ψ, φ, _, rfl⟩
    rw [Category.assoc, φ.cart.1.w, ← Category.assoc, Over.w ψ]
  have hC : IsPullback Φc XM.univ.A.hom X'.univ.A.hom c :=
    hCart p D G L R gb (↑M) (↑N') XM X' 1 (one_mem _) c Φc hWc
  haveI : IsReduced XM.univ.A.left := by
    haveI := XM.univ.ab.smooth
    exact GlobalTheory.isReduced_of_smooth_of_isReduced XM.univ.A.hom
  haveI : IsSeparated X.univ.A.hom := by
    haveI := X.univ.ab.proper
    infer_instance
  haveI : IsFinite Φc := MorphismProperty.of_isPullback (P := @IsFinite) hC.flip hFin
  haveI : Etale Φc := MorphismProperty.of_isPullback (P := @Etale) hC.flip hEtc
  haveI : Surjective Φc := MorphismProperty.of_isPullback (P := @Surjective) hC.flip hSurj
  have hsq2 : Φ₁ ≫ X.univ.A.hom = Φc ≫ X'.univ.A.hom ≫ π := by
    rw [wsq _ _ _ _ _ hW1, reassoc_of% hC.w, hπ]
  obtain ⟨hepi2, Φ, hΦ⟩ := hEt Φc (X'.univ.A.hom ≫ π) X.univ.A.hom Φ₁ hsq2 (by
    intro Ω _ _ x y hxy
    have hab : (x ≫ XM.univ.A.hom) ≫ c = (y ≫ XM.univ.A.hom) ≫ c := by
      have e := congrArg (· ≫ X'.univ.A.hom) hxy
      simpa [hC.w] using e
    obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, hθeq⟩ :=
      hOrb p D G L R gb M N' XM X' c Φc hWc Ω _ _ hab
    have hu' : h * u⁻¹ * h⁻¹ ∈ L.KN ↑N := hA' _ (inv_mem hu)
    have hh : h = h * u⁻¹ * h⁻¹ * (h * u) := by group
    have key := (hEq p D G L R gb M M N XM XM X h h u (h * u⁻¹ * h⁻¹) π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI hI hAd hAd
      hu' hh Ω ((x ≫ XM.univ.A.hom) ≫ XM.s) _ _ rfl hys ox oy mx my θ hθ).2
    obtain ⟨x', hx1, hx2⟩ : ∃ x' : sp Ω ⟶ ox.A.left, x' ≫ mx.φ = x ∧ x' ≫ ox.A.hom = 𝟙 _ :=
      ⟨mx.cart.1.lift x (𝟙 _) (by simp), mx.cart.1.lift_fst _ _ _, mx.cart.1.lift_snd _ _ _⟩
    obtain ⟨y', hy1, hy2⟩ : ∃ y' : sp Ω ⟶ oy.A.left, y' ≫ my.φ = y ∧ y' ≫ oy.A.hom = 𝟙 _ :=
      ⟨my.cart.1.lift y (𝟙 _) (by simp), my.cart.1.lift_fst _ _ _, my.cart.1.lift_snd _ _ _⟩
    have hP := my.cart.1.paste_horiz hC
    have hxy' : x' ≫ θ.left = y' := by
      apply hP.hom_ext
      · rw [Category.assoc, hθeq, ← Category.assoc, hx1, hxy, ← Category.assoc, hy1]
      · rw [Category.assoc, Over.w θ, hx2, hy2]
    calc x ≫ Φ₁ = x' ≫ mx.φ ≫ Φ₁ := by rw [← Category.assoc, hx1]
      _ = x' ≫ θ.left ≫ my.φ ≫ Φ₁ := by rw [key]
      _ = y' ≫ my.φ ≫ Φ₁ := by rw [← Category.assoc x', hxy']
      _ = y ≫ Φ₁ := by rw [← Category.assoc, hy1])
  have hΦs : Φ ≫ X.univ.A.hom = X'.univ.A.hom ≫ π := by
    rw [← cancel_epi Φc, ← Category.assoc, hΦ, wsq _ _ _ _ _ hW1, reassoc_of% hC.w, hπ]
  exact ⟨π, Φ, hπ, hΦ, hπs, hΦs⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPolDesc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

open GlobalTheory.CechPic GlobalTheory.BirigUniq in
theorem UpperTheory.Gal.G3.pPolDesc :
    PolDesc := by
  intro G₀ R _ _ gb S S' s s' c _ _ _ N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' hψ hcomm e h'
  obtain ⟨h'⟩ := h'
  haveI := hψ
  have hpb : IsPullback m₁.φ o₁'.A.hom o₁.A.hom c := m₁.cart.1
  let Y' : Over S := Over.mk (m₁.φ ≫ o₁.A.hom)
  let cO : Y' ⟶ o₁.A := Over.homMk m₁.φ rfl
  have hP1 : (Hecke.lbPow o₁.P e).IsLB := by
    unfold Hecke.lbPow
    exact LB.isLB_linComb o₁.isLB _ _
  have hP1' : (Hecke.lbPow o₁'.P e).IsLB := by
    unfold Hecke.lbPow
    exact LB.isLB_linComb o₁'.isLB _ _
  have hQ : (o₂.P.pull (Hecke.sq2 ψ)).IsLB := pull_isLB o₂.isLB _
  have hQ' : (o₂'.P.pull (Hecke.sq2 ψ')).IsLB := pull_isLB o₂'.isLB _
  refine ⟨(cls_eq_iff hP1 hQ).1 ?_⟩
  rw [← sub_eq_zero]
  have hfl : Flat m₁.φ := MorphismProperty.of_isPullback (P := @Flat) hpb.flip (inferInstance : Flat c)
  have hsu : Surjective m₁.φ :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb.flip (inferInstance : Surjective c)
  have hqc : QuasiCompact m₁.φ :=
    MorphismProperty.of_isPullback (P := @QuasiCompact) hpb.flip (inferInstance : QuasiCompact c)
  refine pic_eq_zero_of_fpqc o₁.A o₁.A Y' o₁.ab cO hfl hsu hqc _ ?_ ?_
  · have key : (lift (1 : o₁.A ⟶ o₁.A) (𝟙 o₁.A)).left ≫ Hecke.sq2 ψ =
        ψ.left ≫ (lift (1 : o₂.A ⟶ o₂.A) (𝟙 o₂.A)).left := by
      unfold Hecke.sq2
      rw [← Over.comp_left, ← Over.comp_left]
      congr 1
      apply CartesianMonoidalCategory.hom_ext
      · simp [one_comp_monHom]
      · simp
    rw [map_sub, GlobalTheory.BirigidPow.cls_lbPow o₁.isLB e hP1, map_nsmul,
      ← cls_pull o₁.isLB _ (pull_isLB o₁.isLB _), (cls_eq_zero_iff _).2 o₁.rig₁, smul_zero,
      cls_pull o₂.isLB _ hQ, ← pull_comp, key, pull_comp,
      ← cls_pull o₂.isLB _ (pull_isLB o₂.isLB _), (cls_eq_zero_iff _).2 o₂.rig₁, map_zero, sub_zero]
  · have hw : (fst o₁.A Y').left ≫ o₁.A.hom = ((snd o₁.A Y').left ≫ o₁'.A.hom) ≫ c := by
      have h1 := Over.w (fst o₁.A Y')
      have h2 := Over.w (snd o₁.A Y')
      rw [h1, ← h2, Category.assoc, ← hpb.w]
      rfl
    let u₀ : (o₁.A ⊗ Y').left ⟶ o₁'.A.left := hpb.lift (fst o₁.A Y').left ((snd o₁.A Y').left ≫ o₁'.A.hom) hw
    have hu₀ : u₀ ≫ o₁'.A.hom = (snd o₁.A Y').left ≫ o₁'.A.hom := hpb.lift_snd _ _ _
    let g : (o₁.A ⊗ Y').left ⟶ Limits.pullback o₁'.A.hom o₁'.A.hom :=
      Limits.pullback.lift u₀ (snd o₁.A Y').left hu₀
    have K1 : (lift (fst o₁.A Y') (snd o₁.A Y' ≫ cO)).left = g ≫ m₁.φ₂ := by
      apply Limits.pullback.hom_ext (f := o₁.A.hom) (g := o₁.A.hom)
      · change _ ≫ (fst o₁.A o₁.A).left = (g ≫ m₁.φ₂) ≫ (fst o₁.A o₁.A).left
        rw [← Over.comp_left, lift_fst, Category.assoc, m₁.sq.1, ← Category.assoc]
        change _ = (g ≫ Limits.pullback.fst _ _) ≫ m₁.φ
        rw [Limits.pullback.lift_fst]
        exact (hpb.lift_fst _ _ _).symm
      · change _ ≫ (snd o₁.A o₁.A).left = (g ≫ m₁.φ₂) ≫ (snd o₁.A o₁.A).left
        rw [← Over.comp_left, lift_snd, Category.assoc, m₁.sq.2, ← Category.assoc]
        change _ = (g ≫ Limits.pullback.snd _ _) ≫ m₁.φ
        rw [Limits.pullback.lift_snd, Over.comp_left]
        rfl
    have K2 : m₁.φ₂ ≫ Hecke.sq2 ψ = Hecke.sq2 ψ' ≫ m₂.φ₂ := by
      unfold Hecke.sq2
      apply Limits.pullback.hom_ext (f := o₂.A.hom) (g := o₂.A.hom)
      · change (_ ≫ _) ≫ (fst o₂.A o₂.A).left = (_ ≫ _) ≫ (fst o₂.A o₂.A).left
        rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_fst, m₂.sq.1, Over.comp_left,
          ← Category.assoc, m₁.sq.1, ← Category.assoc, ← Over.comp_left, lift_fst, Over.comp_left,
          Category.assoc, Category.assoc, hcomm]
      · change (_ ≫ _) ≫ (snd o₂.A o₂.A).left = (_ ≫ _) ≫ (snd o₂.A o₂.A).left
        rw [Category.assoc, Category.assoc, ← Over.comp_left, lift_snd, m₂.sq.2, Over.comp_left,
          ← Category.assoc, m₁.sq.2, ← Category.assoc, ← Over.comp_left, lift_snd, Over.comp_left,
          Category.assoc, Category.assoc, hcomm]
    have pol1 : cls o₁'.P o₁'.isLB = cls (o₁.P.pull m₁.φ₂) (pull_isLB o₁.isLB _) :=
      (cls_eq_iff _ _).2 m₁.pol
    have pol2 : cls o₂'.P o₂'.isLB = cls (o₂.P.pull m₂.φ₂) (pull_isLB o₂.isLB _) :=
      (cls_eq_iff _ _).2 m₂.pol
    have E1 : (pull (lift (fst o₁.A Y') (snd o₁.A Y' ≫ cO)).left) (cls _ hP1) =
        (pull g) (cls _ hP1') := by
      rw [K1, pull_comp, GlobalTheory.BirigidPow.cls_lbPow o₁.isLB e hP1, map_nsmul,
        ← cls_pull o₁.isLB _ (pull_isLB o₁.isLB _), ← pol1, ← GlobalTheory.BirigidPow.cls_lbPow o₁'.isLB e hP1']
    have E2 : (pull (lift (fst o₁.A Y') (snd o₁.A Y' ≫ cO)).left) (cls _ hQ) =
        (pull g) (cls _ hQ') := by
      rw [K1, cls_pull o₂.isLB _ hQ, ← pull_comp, Category.assoc, K2, ← Category.assoc, pull_comp,
        pull_comp, ← cls_pull o₂.isLB _ (pull_isLB o₂.isLB _), ← pol2, cls_pull o₂'.isLB _ hQ']
    rw [map_sub, E1, E2, (cls_eq_iff hP1' hQ').2 h', sub_self]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTransDesc
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem epi_of_isGrpPullback_etale_surjective {S S' : Scheme} (c : S' ⟶ S) [Etale c] [Surjective c] (A : Over S)
    (A' : Over S') [GrpObj A] [GrpObj A'] (a : A'.left ⟶ A.left) (ha : IsGrpPullback A' A c a) : Epi a := by
  haveI : Etale a := MorphismProperty.of_isPullback (P := @Etale) ha.1.flip ‹Etale c›
  haveI : Surjective a := MorphismProperty.of_isPullback (P := @Surjective) ha.1.flip ‹Surjective c›
  exact AlgebraicGeometry.Flat.epi_of_flat_of_surjective a

private theorem comp_eq_comp_of_over_left_comm {S S' : Scheme} {A B : Over S} {A' B' : Over S'}
    (a : A'.left ⟶ A.left) (b : B'.left ⟶ B.left) [Epi a] (u : A ⟶ A) (v : B ⟶ B) (u' : A' ⟶ A')
    (v' : B' ⟶ B') (f : A ⟶ B) (f' : A' ⟶ B')
    (hf : Over.Hom.left f' ≫ b = a ≫ Over.Hom.left f)
    (hu : Over.Hom.left u' ≫ a = a ≫ Over.Hom.left u)
    (hv : Over.Hom.left v' ≫ b = b ≫ Over.Hom.left v) (h' : u' ≫ f' = f' ≫ v') : u ≫ f = f ≫ v := by
  apply Over.OverMorphism.ext
  rw [← cancel_epi a]
  have e3 : Over.Hom.left u' ≫ Over.Hom.left f' = Over.Hom.left f' ≫ Over.Hom.left v' := by
    rw [← Over.comp_left, h', Over.comp_left]
  simp only [Over.comp_left]
  calc a ≫ Over.Hom.left u ≫ Over.Hom.left f
        = Over.Hom.left u' ≫ Over.Hom.left f' ≫ b := by rw [← reassoc_of% hu, ← hf]
    _ = Over.Hom.left f' ≫ Over.Hom.left v' ≫ b := by rw [reassoc_of% e3]
    _ = a ≫ Over.Hom.left f ≫ Over.Hom.left v := by rw [hv, reassoc_of% hf]

theorem UpperTheory.Gal.G3.pTransDesc :
    IsogFEt → TatePull → HomDesc → PolDesc → TransDesc := by
  intro hIsog hTate hHom hPol p _ D G L R _ _ gb S S' _ s s' c _ _ _ hcs N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' h hsq hT
  obtain ⟨hmon', hact', ⟨χ', d, hχmon', hχact', hd1', hd2', hdp⟩, ⟨e, hep, hpol', hint⟩, hgeo'⟩ := hT
  haveI : Epi m₁.φ := epi_of_isGrpPullback_etale_surjective c o₁.A o₁'.A m₁.φ m₁.cart
  haveI : Epi m₂.φ := epi_of_isGrpPullback_etale_surjective c o₂.A o₂'.A m₂.φ m₂.cart
  have hH := hHom S S' c o₁.A o₂.A o₁'.A o₂'.A o₁.ab o₂.ab o₂'.ab m₁.φ m₂.φ m₁.cart m₂.cart ψ ψ' hsq hmon'
  have hmon : IsMonHom ψ := hH.1
  have hdpos : 0 < d := Nat.pos_of_ne_zero (by
    rintro rfl
    exact (Fact.out : p.Prime).one_lt.ne' ((Nat.coprime_zero_left p).mp hdp))
  obtain ⟨hfin, -, hsurj⟩ := hIsog R S' s' o₁'.A o₂'.A o₁'.ab o₂'.ab ψ' χ' d hdpos hmon' hχmon' hd1' hd2'
  obtain ⟨χ, hχsq, hd1, hd2⟩ := hH.2 χ' d hχmon' hsurj hfin hd1' hd2'
  have hχmon : IsMonHom χ := (hHom S S' c o₂.A o₁.A o₂'.A o₁'.A o₂.ab o₁.ab o₁'.ab m₂.φ m₁.φ
    m₂.cart m₁.cart χ χ' hχsq hχmon').1
  refine ⟨hmon, fun b => comp_eq_comp_of_over_left_comm m₁.φ m₂.φ _ _ _ _ ψ ψ' hsq (m₁.act b) (m₂.act b) (hact' b),
    ⟨χ, d, hχmon, fun b => comp_eq_comp_of_over_left_comm m₂.φ m₁.φ _ _ _ _ χ χ' hχsq (m₂.act b) (m₁.act b) (hχact' b),
      hd1, hd2, hdp⟩,
    ⟨e, hep, hPol D.toG R gb S S' s s' c N₁ N₂ o₁ o₂ o₁' o₂' m₁ m₂ ψ ψ' hmon hsq e hpol', hint⟩, ?_⟩
  intro k _ _ t β htβ
  obtain ⟨v, hv⟩ := ‹Surjective c›.surj (UpperTheory.Gal.TranscendenceTraces.pt t)
  obtain ⟨z, hz, -⟩ := UpperTheory.Gal.TranscendenceTraces.ptLift_holds c k t v hv
  subst hz
  have hz' : z ≫ s' = spMap β := by
    rw [← hcs, ← Category.assoc]
    exact htβ
  obtain ⟨I₁', I₂', hI₁', hI₂', hiff'⟩ := hgeo' k z β hz'
  obtain ⟨-, hT1⟩ := hTate p D R gb S S' s s' c N₁ o₁ o₁' m₁ k z
  obtain ⟨-, hT2⟩ := hTate p D R gb S S' s s' c N₂ o₂ o₂' m₂ k z
  obtain ⟨I₁, hInd₁, hev₁⟩ := hT1 I₁'
  obtain ⟨I₂, hInd₂, hev₂⟩ := hT2 I₂'
  refine ⟨I₁, I₂, hInd₁ hI₁', hInd₂ hI₂', fun n hn hnp x y => ?_⟩
  have e1 : Over.Hom.left (I₁'.ev n x) ≫ m₁.φ = Over.Hom.left (I₁.ev n x) := hev₁ n x
  have e2 : Over.Hom.left (I₂'.ev n y) ≫ m₂.φ = Over.Hom.left (I₂.ev n y) := hev₂ n y
  rw [← hiff' n hn hnp x y]
  constructor
  · intro hxy
    apply Over.OverMorphism.ext
    apply m₂.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hsq, ← Category.assoc, e1, ← Over.comp_left, hxy, e2]
    · rw [Over.w, Over.w]
  · intro hxy
    apply Over.OverMorphism.ext
    rw [Over.comp_left, ← e1, ← e2, Category.assoc, ← hsq, ← Category.assoc, ← Over.comp_left, hxy]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitEx
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u


open GlobalTheory.UPel.HT.Hecke in
private theorem gObjMap_comp_keep {G₀ : GDatum} {R : Type} [CommRing R] [Algebra ℚ R] {b : GBase G₀ R} {N : ℕ}
    {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : GObj b N s₁} {o₂ : GObj b N s₂}
    {o₃ : GObj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : GObjMap o₁ o₂ f) (h₂ : GObjMap o₂ o₃ g) :
    ∃ m : GObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
  have e₁ : LBIso (o₂.P.pull h₁.φ₂) ((o₃.P.pull h₂.φ₂).pull h₁.φ₂) :=
    LBIso.chartPull (chartPullPull o₂.P h₁.φ₂ h₁.φ₂ rfl)
      (chartPullPull (o₃.P.pull h₂.φ₂) h₁.φ₂ h₁.φ₂ rfl) h₂.pol
  have e₂ : LBIso (o₂.P.pull h₁.φ₂) (o₃.P.pull (h₁.φ₂ ≫ h₂.φ₂)) :=
    LBIso.chartPull (chartPullId _) (chartPullIn o₃.P (fun _ => h₂.φ₂) (fun _ => 1) h₁.φ₂) e₁
  refine ⟨⟨h₁.φ ≫ h₂.φ, h₁.φ₂ ≫ h₂.φ₂, h₁.cart.comp h₂.cart, ?_, ?_,
    LBIso.trans o₁.isLB (pull_isLB o₂.isLB _) (pull_isLB o₃.isLB _) h₁.pol e₂, ?_⟩, rfl⟩
  · exact ⟨by simp only [Category.assoc, h₂.sq.1, reassoc_of% h₁.sq.1],
      by simp only [Category.assoc, h₂.sq.2, reassoc_of% h₁.sq.2]⟩
  · intro c
    simp only [← Category.assoc, h₁.act c]
    simp only [Category.assoc, h₂.act c]
  · intro y
    simp only [reassoc_of% h₁.eta y, h₂.eta y, Category.assoc]

theorem UpperTheory.Gal.G3.pWitEx :
    KNBasic → GenSm → Rigid → WitForget → WitDeep → DescMap → TransIso → TransCancel → TransDesc → WitEx := by
  intro _ hSm hRig hWF hWD hDM hTI hTC hTD p _ D G L R _ _ gb X N' N h hI hA
  obtain ⟨M, hdiv, hAM, π₁, Φ₁, hs₁, o₁, ψ₁, φ₁, ht₁, hΦ₁⟩ := hWD p D G L R gb X N' N h hI
  obtain ⟨c, Φc, hw, hfin, het, hsur⟩ := hWF p D G L R gb N' M hdiv (X N') (X M)
  have hA1 : AdmK L (↑M) (↑N') 1 := by
    intro u hu
    simpa using UpperTheory.Gal.Int.Geo.KN_anti hdiv hu
  obtain ⟨π, Φ, hcπ, hΦ, hπs, hΦw⟩ :=
    hDM p D G L R gb M N' N (X M) (X N') (X N) h hI hA hA1 c Φc π₁ Φ₁ hw hfin het hsur
      ⟨hs₁, o₁, ψ₁, φ₁, ht₁, hΦ₁⟩
  subst hcπ
  obtain ⟨hsc, oc, ψc, φc, htc, hΦc⟩ := hw
  obtain ⟨o, ⟨φ⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (X N').s π hπs (X N).univ
  let ψl : (X N').univ.A.left ⟶ o.A.left :=
    φ.cart.1.lift Φ (X N').univ.A.hom hΦw
  have hψ₁ : ψl ≫ φ.φ = Φ := φ.cart.1.lift_fst _ _ _
  have hψ₂ : ψl ≫ o.A.hom = (X N').univ.A.hom := φ.cart.1.lift_snd _ _ _
  let ψ : (X N').univ.A ⟶ o.A := Over.homMk ψl hψ₂
  refine ⟨π, Φ, hπs, o, ψ, φ, ?_, hψ₁.symm⟩
  obtain ⟨m₂⟩ := BaseChange.gObjMap_cancel φ₁ φ
  haveI := hTI p D G L R gb (X M).X (X M).s M N' (X M).univ oc ψc 1 (one_mem _) htc
  have htr : IsTrans L h oc o₁ (inv ψc ≫ ψ₁) :=
    hTC p D G L R gb (X M).X (X M).s M N' N (X M).univ oc o₁ ψc (inv ψc ≫ ψ₁) h hI hAM htc
      (by simpa using ht₁)
  haveI : Smooth (X M).s := (hSm p D R gb M (X M)).1
  haveI : AlgebraicGeometry.IsReduced (X M).X := GlobalTheory.isReduced_of_smooth_of_isReduced (X M).s
  have hcomp : m₂.φ ≫ φ.φ = φ₁.φ := by
    obtain ⟨m, hm⟩ := gObjMap_comp_keep m₂ φ
    rw [← hm]
    exact hRig p D R gb (X N).X (X M).X (X N).s (X M).s (c ≫ π)
      (by rw [Category.assoc, hπs, hsc]) N (X N).univ o₁ m φ₁
  refine hTD p D G L R gb (X N').X (X M).X (X N').s (X M).s c hsc N' N (X N').univ o oc o₁ φc m₂ ψ
    (inv ψc ≫ ψ₁) h ?_ htr
  have key : ψc.left ≫ φc.φ ≫ Φ = ψ₁.left ≫ φ₁.φ := by
    rw [← Category.assoc, ← hΦc, hΦ, hΦ₁]
  apply φ.cart.1.hom_ext
  · simp only [Category.assoc, hcomp, ψ, Over.homMk_left, hψ₁, Over.comp_left]
    rw [← key, ← Category.assoc, ← Over.comp_left, IsIso.inv_hom_id, Over.id_left, Category.id_comp]
  · simp only [Category.assoc, ψ, Over.homMk_left, hψ₂, Over.comp_left]
    rw [m₂.cart.1.w, φc.cart.1.w, ← Over.comp_left_assoc, Over.w_assoc]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitOne :
    GenSm → WitUniq → WitComp → WitForget → WitOne := by
  intro hS hU hC hF p _ D G L R _ _ gb X N' N hA π Φ hW
  let M : Lv p := ⟨N.1 * N'.1, Nat.le_trans N.2.1 (Nat.le_mul_of_pos_right _ (by have := N'.2.1; omega)),
    Nat.Coprime.mul_left N.2.2 N'.2.2⟩
  have hI : Integ L (1 : G.GAf) := fun v hv => by simpa using hv
  have hMN : AdmK L M.1 N.1 1 := fun u hu => by
    simpa using UpperTheory.Gal.Int.Geo.KN_anti (Dvd.intro _ rfl : N.1 ∣ M.1) hu
  obtain ⟨c, Φc, Wc, cF, cE, cS⟩ := hF p D G L R gb N' M (Dvd.intro_left _ rfl) (X N') (X M)
  obtain ⟨e, Φe, We, eF, eE, eS⟩ := hF p D G L R gb N M (Dvd.intro _ rfl) (X N) (X M)
  have W1 := (hC p D G L R gb M N' N (X M) (X N') (X N) 1 1).2 hI hA c Φc π Φ Wc hW
  rw [_root_.mul_one] at W1
  have hce : c ≫ π = e := (hU p D G L R gb M N (X M) (X N) 1 hI hMN _ _ _ _ W1 We).1
  obtain ⟨s1, s2, s3, -⟩ := hS p D R gb N' (X N')
  obtain ⟨t1, t2, t3, -⟩ := hS p D R gb N (X N)
  have hs : π ≫ (X N).s = (X N').s := hW.1
  have sep : IsSeparated (π ≫ (X N).s) := by rw [hs]; exact s2
  have lft : LocallyOfFiniteType (π ≫ (X N).s) := by rw [hs]; infer_instance
  have πS : IsSeparated π := IsSeparated.of_comp π (X N).s
  have πL : LocallyOfFiniteType π := locallyOfFiniteType_of_comp π (X N).s
  have hE : Etale (c ≫ π) := by rw [hce]; exact eE
  have hFi : IsFinite (c ≫ π) := by rw [hce]; exact eF
  obtain ⟨r1, r2⟩ := GlobalTheory.etale_isFinite_of_comp_etale_surjective _ _ _ c π cE cS hE hFi πS πL
  have hSu : Surjective (c ≫ π) := by rw [hce]; exact eS
  exact ⟨r2, r1, Surjective.of_comp c π⟩
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitTrans
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pWitTrans :
    KNBasic → PtEq → PtOrbit → WitComp → WitTrans := by
  intro hKN hEq hOrb hWC p _ D G L R _ _ gb X N' N π Φ hW k _ _ x y hxy
  obtain ⟨ox, oy, mx, my, hys, u, hu, θ, hθ, hθΦ⟩ := hOrb p D G L R gb N' N (X N') (X N) π Φ hW k x y hxy
  refine ⟨u, hu, fun π' Φ' hW' => ?_⟩
  have hu1 : u ∈ L.KN 1 := UpperTheory.Gal.Int.Geo.KN_anti (one_dvd _) hu
  have h1 : (1 : G.GAf) ∈ L.KN 1 := one_mem _
  have hid := (hWC p D G L R gb N' N' N' (X N') (X N') (X N') 1 1).1 1 (one_mem _)
  obtain ⟨hA, hB⟩ := hEq p D G L R gb N' N' N' (X N') (X N') (X N') u 1 u 1 π' Φ' (𝟙 _) (𝟙 _) hW' hid
    (UpperTheory.Gal.Int.Geo.integ_of_mem hu1) (UpperTheory.Gal.Int.Geo.integ_of_mem h1)
    ((hKN p D G L N').1 u hu1) ((hKN p D G L N').1 1 h1) (one_mem _) (by simp) k (x ≫ (X N').s) x y rfl hys
    ox oy mx my θ hθ
  refine ⟨by simpa using hA, fun a ha => ?_⟩
  obtain ⟨l, rfl⟩ : ∃ l, l ≫ mx.φ = a :=
    ⟨_, mx.cart.1.lift_fst a (𝟙 _) (by rw [ha, Category.id_comp])⟩
  simp only [Category.assoc]
  rw [reassoc_of% hB, hθΦ]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PWitFree
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem kn_le_one {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} (L : Link D G) (N : ℕ) {g : G.GAf}
    (hg : g ∈ L.KN N) : g ∈ L.KN 1 := by
  have key : ∀ {a : G.GAf}, L.CongOne N a → L.CongOne 1 a := by
    intro a ha v hv
    obtain ⟨w, hw, e⟩ := ha v hv
    exact ⟨N • w, nsmul_mem hw N, by rw [e, one_smul]⟩
  exact ⟨key hg.1, key hg.2⟩

theorem UpperTheory.Gal.G3.pWitFree :
    KNBasic → TransComp → TransPull → TransOfMap → TransFree → PtEq → WitCart → WitEx → WitFree := by
  intro hKN hComp hPull hOfMap hFree hPt hCart hEx
  intro p _ D G L R _ _ gb X N' N hle u hu π Φ hW k _ _ x hx
  have hu1 : u ∈ L.KN 1 := kn_le_one L N hu
  have hI1 : Integ L (1 : G.GAf) := UpperTheory.Gal.Int.Geo.integ_of_mem (one_mem _)
  have hA1 : AdmK L (↑N') (↑N) (1 : G.GAf) := by
    intro v hv
    simpa using hle hv
  have hA0 : AdmK L (↑N') (↑N') (1 : G.GAf) := (hKN p D G L N').1 1 (one_mem _)
  obtain ⟨π₁, Φ₁, hW1⟩ := hEx p D G L R gb X N' N 1 hI1 hA1
  have hpb1 := hCart p D G L R gb _ _ (X N') (X N) 1 (one_mem _) π₁ Φ₁ hW1
  obtain ⟨_, o, ψ, φ, hψ, _⟩ := hW
  obtain ⟨ox, ⟨mx⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ (X N').s) x rfl (X N').univ
  obtain ⟨oo, ⟨m2⟩⟩ := UpperTheory.exists_levelObj_pullback_of_charZero (x ≫ (X N').s) x rfl o
  obtain ⟨ψ', hψ', _⟩ := hPull p D G L R gb _ _ _ _ x rfl _ _ (X N').univ o ox oo mx m2 ψ u hψ
  have hn1 : Nonempty (GObjMap oo (X N').univ (𝟙 _ ≫ x)) := by
    have h := Unique.gObjMap_comp m2 φ
    have e : x ≫ π = 𝟙 _ ≫ x := by rw [hx, Category.id_comp]
    rwa [e] at h
  obtain ⟨mm⟩ := hn1
  obtain ⟨n⟩ := BaseChange.gObjMap_cancel mm mx
  obtain ⟨θ, _, hθ⟩ := hOfMap p D G L R gb _ _ N' oo ox n
  have hα := hComp p D G L R gb _ _ _ N' N' ox oo ox ψ' θ u 1 hI1 hA0 hψ' hθ
  rw [_root_.one_mul] at hα
  have hpt := (hPt p D G L R gb N' N' N (X N') (X N') (X N) 1 1 u u⁻¹ π₁ Φ₁ π₁ Φ₁ hW1 hW1 hI1 hI1
    hA1 hA1 (inv_mem hu) (by rw [_root_.one_mul, inv_mul_cancel]) k (x ≫ (X N').s) x x rfl rfl
    ox ox mx mx (ψ' ≫ θ) hα).2
  have hpb := IsPullback.paste_horiz mx.cart.1 hpb1
  have hid : ψ' ≫ θ = 𝟙 ox.A := by
    apply Over.OverMorphism.ext
    apply hpb.hom_ext
    · simpa [Category.assoc] using hpt.symm
    · simp
  rw [hid] at hα
  exact hFree p D G L R gb k (x ≫ (X N').s) N' ox u hu1 hα
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTwMem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
open GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh
universe u

private theorem sp_sub (Ω : Type) [Field Ω] : Subsingleton (UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSumFn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem isAdmissible_flagPair_of_unitriangular_left_automorphism {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {m j : X.ι} {k h : G}
    (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.admitted m j (k * h) := by
  refine ⟨X.Δ.mul_mem (X.K_le j k hk) hh.1, fun u hu => ?_⟩
  have h3 := (X.K j).mul_mem ((X.K j).mul_mem hk (hh.2 u hu)) ((X.K j).inv_mem hk)
  have e : k * h * u * (k * h)⁻¹ = k * (h * u * h⁻¹) * k⁻¹ := by group
  rw [e]
  exact h3

private theorem pl_left {B : Scheme.{0}} {G : Type} [Group G] (X : Tower B G) {F : Type} [Field F] (T : UpperTheory.Gal.G3.Th.{u} B F)
    {m j : X.ι} {k h : G} (hk : k ∈ X.K j) (hh : X.admitted m j h) : X.pl T m j (k * h) = X.pl T m j h := by
  have a := isAdmissible_flagPair_of_unitriangular_left_automorphism X hk hh
  have e : X.tr m j (k * h) a.1 a.2 = X.tr m j h hh.1 hh.2 := by
    rw [← X.tr_mul m j j h k hh.1 hh.2 (X.K_le j k hk)
      (fun u hu => (X.K j).mul_mem ((X.K j).mul_mem hk hu) ((X.K j).inv_mem hk)) a.1 a.2,
      X.tr_self j k _ _ hk, Category.comp_id]
  unfold Tower.pl
  rw [dite_eq_left a, dite_eq_left hh]
  simp only [e]
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PMemOp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

private theorem cos_bij {G : Type} [Group G] (K V U : Subgroup G) (hVK : V ≤ K) (hUV : U ≤ V) :
    Function.Bijective (fun p : (K ⧸ V.subgroupOf K) × (V ⧸ U.subgroupOf V) =>
      (((⟨(p.1.out : G) * (p.2.out : G), K.mul_mem p.1.out.2 (hVK p.2.out.2)⟩ : K)) : K ⧸ U.subgroupOf K)) := by
  constructor
  · rintro ⟨c, y⟩ ⟨c', y'⟩ h
    have h1 : ((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G)) ∈ U := by
      have := QuotientGroup.eq.1 h
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    have hc : c = c' := by
      rw [← QuotientGroup.out_eq' c, ← QuotientGroup.out_eq' c']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((c.out)⁻¹ * c'.out : K) : G) =
          (y.out : G) * (((c.out : G) * (y.out : G))⁻¹ * ((c'.out : G) * (y'.out : G))) * (y'.out : G)⁻¹ := by
        push_cast; group
      rw [e]
      exact V.mul_mem (V.mul_mem y.out.2 (hUV h1)) (V.inv_mem y'.out.2)
    subst hc
    have hy : y = y' := by
      rw [← QuotientGroup.out_eq' y, ← QuotientGroup.out_eq' y']
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : (((y.out)⁻¹ * y'.out : V) : G) =
          ((c.out : G) * (y.out : G))⁻¹ * ((c.out : G) * (y'.out : G)) := by
        push_cast; group
      rw [e]; exact h1
    rw [hy]
  · intro a
    induction a using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨v, hv⟩ := QuotientGroup.mk_out_eq_mul (V.subgroupOf K) a
      have hvV : ((v : K) : G) ∈ V := Subgroup.mem_subgroupOf.1 v.2
      let b : V := ⟨((v : K) : G)⁻¹, V.inv_mem hvV⟩
      obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (U.subgroupOf V) b
      have hwU : ((w : V) : G) ∈ U := Subgroup.mem_subgroupOf.1 w.2
      refine ⟨((a : K ⧸ V.subgroupOf K), (b : V ⧸ U.subgroupOf V)), ?_⟩
      refine QuotientGroup.eq.2 ?_
      rw [Subgroup.mem_subgroupOf]
      have e : ((((⟨(((a : K ⧸ V.subgroupOf K).out : K) : G) * (((b : V ⧸ U.subgroupOf V).out : V) : G),
          K.mul_mem (a : K ⧸ V.subgroupOf K).out.2 (hVK (b : V ⧸ U.subgroupOf V).out.2)⟩ : K))⁻¹ * a : K) : G) =
          ((w : V) : G)⁻¹ := by
        simp only [hv, hw, b]
        push_cast
        group
      rw [e]; exact U.inv_mem hwU
end

section -- merged from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PKSNice
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (Lv IsTrans Integ KS Mem FEt KSEx KSNice)
open scoped TensorProduct
universe u

theorem UpperTheory.Gal.G3.pKSNice :
    KNBasic → PowSm → TwFEt → SigmaFEt → KSNice := by
  intro hKN hP hT hS p _ D G L hsc R _ _ gb k T N J g
  have hq := T.e_q N
  obtain ⟨hsm, -, hpr⟩ := hP p D R gb N (T.M N) k
  refine ⟨?_, ?_, ?_⟩
  · show Smooth (T.X.q (T.lev N))
    rw [← hq]
    infer_instance
  · show IsProjOver (T.X.q (T.lev N))
    rw [← hq]
    exact GlobalTheory.ProjSpace.isProjOver_comp_of_isClosedImmersion _ (hpr hsc.cpt)
  · intro j
    dsimp only [UpperTheory.Gal.Int.Geo.KS.tower]
    have hne : ((L.KN ↑N).subgroupOf (g j).K).index ≠ 0 := by
      have h0 := (hKN p D G L 1).2.2 N (by norm_num) (by have := N.2.1; omega)
      rw [← Subgroup.relIndex_mul_relIndex _ _ _ (g j).le (g j).le_one] at h0
      exact left_ne_zero_of_mul h0
    haveI : ((L.KN ↑N).subgroupOf (g j).K).FiniteIndex := ⟨hne⟩
    refine ⟨_, hS _ _ _ (hT T.X _ _ ⟨?_, ?_⟩)⟩
    · exact one_mem _
    · intro u hu
      rw [T.K_eq] at hu ⊢
      simpa using UpperTheory.Gal.Int.Geo.KN_anti (g j).dvd hu
end

open UpperTheory.Gal.Int.Geo (KSEx KSNice)

universe u

namespace UpperTheory.Gal.G3

theorem nuInt_holds : NuInt := @pNuInt

theorem multBasic_holds : MultBasic := @pMultBasic @nuInt_holds

theorem kNBasic_holds : KNBasic := @pKNBasic

theorem sysOf_holds : SysOf := @pSysOf @nuInt_holds

theorem fibrePowerTower_admissibleLevel : AdmOf := @pAdmOf

theorem kNCong_holds : KNCong := @pKNCong

theorem gSimOf_holds : GSimOf := @pGSimOf @multBasic_holds

theorem relComp_holds : RelComp := @pRelComp

theorem tateDiff_holds : TateDiff := @pTateDiff

theorem tateTwist_holds : TateTwist := @pTateTwist @gSimOf_holds

theorem fullOf_holds : FullOf := @pFullOf

theorem relArith_holds : RelArith := @pRelArith

theorem transSelf_holds : TransSelf := @pTransSelf @multBasic_holds @relComp_holds @tateTwist_holds

theorem transComp_holds : TransComp := @pTransComp @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds

theorem homPull_holds : HomPull := @pHomPull

theorem tatePull_holds : TatePull := @pTatePull

theorem transPull_holds : TransPull := @pTransPull @homPull_holds @tatePull_holds

theorem transOfMap_holds : TransOfMap := @pTransOfMap @multBasic_holds @relComp_holds @tatePull_holds

theorem rigid_holds : Rigid := @pRigid

theorem isogFEt_holds : IsogFEt := @pIsogFEt

theorem transKer_holds : TransKer := @pTransKer @relComp_holds @tateDiff_holds @tateTwist_holds

theorem polUniq_holds : PolUniq := @pPolUniq

theorem mapOfIso_holds : MapOfIso := @pMapOfIso

theorem transDeep_holds : TransDeep := @pTransDeep @sysOf_holds @fibrePowerTower_admissibleLevel @fullOf_holds @relArith_holds

theorem transIso_holds : TransIso := @pTransIso @isoPts_holds @isogFEt_holds

theorem transOrbit_holds : TransOrbit := @pTransOrbit @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @kNCong_holds @transIso_holds

theorem transFree_holds : TransFree := @pTransFree @kNCong_holds

theorem genSm_holds : GenSm := @pGenSm

theorem powSm_holds : PowSm := @pPowSm @genSm_holds

theorem etDesc_holds : EtDesc := @pEtDesc @extPts_holds

theorem ptOrbit_holds : PtOrbit := @pPtOrbit @transComp_holds @transPull_holds @transOfMap_holds @transOrbit_holds @rigid_holds

theorem witComp_holds : WitComp := @pWitComp @transSelf_holds @transComp_holds @transPull_holds

theorem witCart_holds : WitCart := @pWitCart @transIso_holds

theorem witForget_holds : WitForget := @pWitForget @mapOfIso_holds @transSelf_holds

theorem witDeep_holds : WitDeep := @pWitDeep @kNBasic_holds @genSm_holds @transDeep_holds @witComp_holds @witForget_holds

theorem homDesc_holds : HomDesc := @pHomDesc @etDesc_holds

theorem polDesc_holds : PolDesc := @pPolDesc

theorem transDesc_holds : TransDesc := @pTransDesc @isogFEt_holds @tatePull_holds @homDesc_holds @polDesc_holds

theorem transCancel_holds : TransCancel := @pTransCancel @multBasic_holds @relComp_holds @tateDiff_holds @tateTwist_holds @transIso_holds

theorem twFEt_holds : TwFEt := @pTwFEt @fEtBasic_holds @twGal_holds

theorem sigmaFEt_holds : SigmaFEt := @pSigmaFEt

theorem kSNice_holds : KSNice := @pKSNice @kNBasic_holds @powSm_holds @twFEt_holds @sigmaFEt_holds

theorem quotUniq_holds : QuotUniq := @pQuotUniq @etDesc_holds

theorem transUniqPt_holds : TransUniqPt := @pTransUniqPt @multBasic_holds @isogFEt_holds @transKer_holds @quotUniq_holds @polUniq_holds @mapOfIso_holds

theorem ptEq_holds : PtEq := @pPtEq @transSelf_holds @transComp_holds @transPull_holds @transUniqPt_holds @rigid_holds

theorem witUniq_holds : WitUniq := @pWitUniq @genSm_holds @extPts_holds @transSelf_holds @ptEq_holds

theorem descMap_holds : DescMap := @pDescMap @genSm_holds @etDesc_holds @ptEq_holds @ptOrbit_holds @witCart_holds

theorem witEx_holds : WitEx := @pWitEx @kNBasic_holds @genSm_holds @rigid_holds @witForget_holds @witDeep_holds @descMap_holds @transIso_holds @transCancel_holds @transDesc_holds

theorem witOne_holds : WitOne := @pWitOne @genSm_holds @witUniq_holds @witComp_holds @witForget_holds

theorem witTrans_holds : WitTrans := @pWitTrans @kNBasic_holds @ptEq_holds @ptOrbit_holds @witComp_holds

theorem witFree_holds : WitFree := @pWitFree @kNBasic_holds @transComp_holds @transPull_holds @transOfMap_holds @transFree_holds @ptEq_holds @witCart_holds @witEx_holds

theorem kSEx_holds : KSEx := @pKSEx @kNBasic_holds @witUniq_holds @witComp_holds @witCart_holds @witEx_holds @witOne_holds @witTrans_holds @witFree_holds

end UpperTheory.Gal.G3
