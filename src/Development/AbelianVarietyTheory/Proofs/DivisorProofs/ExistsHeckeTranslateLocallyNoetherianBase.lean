module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCommutatorPairingValueHeckePoints
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateSimilitudeHeckeTranslateLatticeSystem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCoefficientsCongruence
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormOffVarietyMul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UPel.HT.HeckeRootA
open GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem dvd_pair (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k n : ℕ) (hk0 : k ≠ 0) (hck : c ∣ k ^ 2)
    (hkn : (k : ℤ) ^ 2 ∣ n) (hsim : ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ x, ∃ y z, h n y = k • x + n • z) (x v : D.La) :
    (k : ℤ) ∣ ((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v := by
  obtain ⟨y, z, hyz⟩ := hon v
  have hmZ : ((k ^ 2 / c : ℕ) : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast Nat.div_mul_cancel hck
  have h1 : D.EF (h n x) (h n y) = (k : ℤ) * D.EF (h n x) v + n * D.EF (h n x) z := by
    rw [hyz, map_add (f := _), map_nsmul, map_nsmul, nsmul_eq_mul, nsmul_eq_mul]
  have h2 := hsim x y
  rw [h1] at h2

  have h3 : (k : ℤ) ^ 2 ∣ (k : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v) := by
    have e1 : (k : ℤ) * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h n x) v)
        = ((k ^ 2 / c : ℕ) : ℤ) * ((k : ℤ) * D.EF (h n x) v + n * D.EF (h n x) z - c * u n * D.EF x y)
          - ((k ^ 2 / c : ℕ) : ℤ) * n * D.EF (h n x) z + (k : ℤ) ^ 2 * (u n * D.EF x y) := by
      rw [← hmZ]; ring
    rw [e1]
    refine dvd_add (dvd_sub (Dvd.dvd.mul_left (hkn.trans h2) _) ?_) (dvd_mul_right _ _)
    exact (hkn.trans (dvd_mul_left _ _)).mul_right _
  have hkZ : (k : ℤ) ≠ 0 := by exact_mod_cast hk0
  rw [pow_two] at h3
  exact (mul_dvd_mul_iff_left hkZ).1 h3

end GlobalTheory.UPel.HT.HeckeRootA

namespace GlobalTheory.UPel.HT.HeckeRootA
open GlobalTheory.UPel.HT.HeckeRoot

variable {p : ℕ} [Fact p.Prime] {D : GlobalTheory.UPel.HT.Datum p} {K : Type} [Field K] {Q : Type} [Group Q]
    {act : D.O → Q → Q} {e : ℕ → Q → Q → Kˣ → Prop}

theorem sqrt_hecke_point_weil_orthogonal (I : TateIsoO D K Q act e) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ)
    (c k N : ℕ) (hk : k.Coprime p) (hN : 0 < N) (hNp : N.Coprime p) (hck : c ∣ k ^ 2)
    (hcomp : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p →
      (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n)
    (hsim : ∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧
      ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) (x : D.La) :
    ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • h (N * k) x) ∧
      (h' ^ (k ^ 2 / c)) ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
  have hp : p.Prime := Fact.out
  have hk0 : k ≠ 0 := by
    rintro rfl; exact hp.one_lt.ne' (Nat.coprime_zero_left _ |>.mp hk)
  have hL : 0 < N * k := Nat.mul_pos hN (Nat.pos_of_ne_zero hk0)
  have gen : ∀ M j t : ℕ, 0 < M → k ∣ M → (N * k * M).Coprime p → 2 * j = M + t * (k * M) →
      ∃ (n : ℕ) (h' : Q), 0 < n ∧ n.Coprime p ∧ h' ^ 2 = I.ev (N * k) (N • h (N * k) x) ∧
        (h' ^ (k ^ 2 / c)) ^ n = 1 ∧ ∀ z : Q, z ^ n = 1 → e n (h' ^ (k ^ 2 / c)) z 1 := by
    intro M j t hM hkM hcop hj
    have hn' : 0 < N * k * M := Nat.mul_pos hL hM
    obtain ⟨M', rfl⟩ := hkM
    have hkn : (k : ℤ) ^ 2 ∣ ((N * k * (k * M') : ℕ) : ℤ) := ⟨N * M', by push_cast; ring⟩
    refine ⟨N * k * (k * M'), I.ev (N * k * (k * M')) (j • N • h (N * k * (k * M')) x), hn', hcop, ?_, ?_⟩
    · obtain ⟨z, hz⟩ := (hcomp (N * k) (k * M') hL hM hcop).1 x
      have e1 : 2 • j • N • h (N * k * (k * M')) x
          = (k * M') • (N • h (N * k * (k * M')) x) + (N * k * (k * M')) • (t • h (N * k * (k * M')) x) := by
        simp only [smul_smul, ← add_smul]
        congr 1
        calc 2 * (j * N) = (2 * j) * N := by ring
          _ = _ := by rw [hj]; ring
      rw [← ev_nsmul, e1, I.add, (I.ker _ hn' hcop _).2 ⟨_, rfl⟩, _root_.mul_one, ev_nsmul,
        I.tower (N * k) (k * M') hL hM hcop, hz, smul_add, I.add, smul_comm N (N * k) z,
        (I.ker _ hL (Nat.Coprime.coprime_dvd_left (Dvd.intro _ rfl) hcop) _).2 ⟨_, rfl⟩, _root_.mul_one]
    · rw [← ev_nsmul]
      refine pair_one I _ hn' hcop _ (fun v => ?_)
      obtain ⟨a, ha⟩ := dvd_pair h u c k _ hk0 hck hkn ((hsim _ hn' hcop).2) (hon _ hn' hcop) x v
      have e2 : 2 * D.EF ((k ^ 2 / c) • j • N • h (N * k * (k * M')) x) v
          = (2 * j : ℕ) * N * (((k ^ 2 / c : ℕ) : ℤ) * D.EF (h (N * k * (k * M')) x) v) := by
        simp only [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
        push_cast; ring
      rw [e2, ha, hj]
      exact ⟨(1 + t * k) * a, by push_cast; ring⟩
  by_cases hp2 : p = 2
  · subst hp2
    have hodd : k % 2 = 1 := by
      rcases Nat.mod_two_eq_zero_or_one k with h0 | h0
      · exfalso
        have h2 : 2 ∣ Nat.gcd k 2 := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h0) dvd_rfl
        rw [hk] at h2; omega
      · exact h0
    obtain ⟨r, hr⟩ : ∃ r, k = 2 * r + 1 := ⟨k / 2, by omega⟩
    refine gen k (k * (r + 1)) 1 (Nat.pos_of_ne_zero hk0) dvd_rfl (Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hk) hk) ?_
    rw [hr]; ring
  · have h2p : (2 : ℕ).Coprime p := (Nat.coprime_primes Nat.prime_two hp).2 (fun h0 => hp2 h0.symm)
    refine gen (k * 2) k 0 (by positivity) (dvd_mul_right _ _)
      (Nat.Coprime.mul_left (Nat.Coprime.mul_left hNp hk) (Nat.Coprime.mul_left hk h2p)) ?_
    ring

end GlobalTheory.UPel.HT.HeckeRootA

namespace GlobalTheory.UPel.HT.HeckeAd.KerPol
open GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.HeckeAd

theorem fibre_triv (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R)
    (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ) (hk : k.Coprime p) (hN : 3 ≤ N) (hNp : N.Coprime p)
    (hck : c ∣ k ^ 2)
    (hcomp : ∀ n m, 0 < n → 0 < m → (n * m).Coprime p →
      (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n)
    (hsim : ∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧
      ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y)
    (hon : ∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z)
    (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s) (g : 𝟙_ (Over S) ⟶ o.A)
    (hg : g ∈ heckeSubA o (h (N * k)) N) (K : Type) [Field K] [IsAlgClosed K] (y : Sp K ⟶ S) :
    ∃ t : (((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ g) (𝟙 o.A)).left).pull
      (pullback.fst o.A.hom y)).Gen, t.IsGen := by
  obtain ⟨x, rfl⟩ := hg
  obtain ⟨β, hβ⟩ : ∃ β : R →+* K, y ≫ s = spMap β :=
    ⟨(Spec.preimage (y ≫ s)).hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := o.geom K y β hβ
  obtain ⟨n, h', hn0, hnp, hsq, hpow, hW⟩ :=
    GlobalTheory.UPel.HT.HeckeRootA.sqrt_hecke_point_weil_orthogonal I h u c k N hk (by omega) hNp hck hcomp hsim hon x
  have hnK : (n : K) ≠ 0 := by
    have := (b.unit n hnp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have htr := GlobalTheory.HeckeFibre.transl_triv o.A o.ab _ (pull_isLB o.isLB _)
    (GlobalTheory.HeckeFibre.rigidified_diag o.A o.P o.isLB o.rig₁) K y n hnK
    (h' ^ (k ^ 2 / c)) hpow (fun z hz => by
      have w := hW z hz
      have e1 : unitOn (1 : Kˣ) = 1 := map_one _
      rw [e1] at w
      exact w)
  exact GlobalTheory.PicBilin.triv_pow_of_translDiff o.A o.ab o.P o.isLB o.rig₁ o.rig₂ o.symm (Over.mk y)
    (GlobalTheory.HeckeFibre.pic_field_eq_zero K) (o.eta (N • h (N * k) x)) h' (k ^ 2 / c) (by rw [hsq, hI]) htr

end GlobalTheory.UPel.HT.HeckeAd.KerPol

section Main
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

namespace GlobalTheory.UPel.HT.HeckeAd.KerPol

theorem hecke_sections_triv : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ g) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ g)).left).Gen, t.IsGen) := by
  intro p _ D R _ b h u c k N hc hk hN hNp hck hlin hcomp hsim hon S s o g hg
  have hfib := fibre_triv p D R b h u c k N hk hN hNp hck hcomp hsim hon S s o g hg
  have hP := o.isLB
  have clsPow : ∀ {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) (n : ℕ) (h' : (GlobalTheory.UPel.HT.Hecke.lbPow L n).IsLB),
      GlobalTheory.CechPic.cls (GlobalTheory.UPel.HT.Hecke.lbPow L n) h' = n • GlobalTheory.CechPic.cls L hL := by
    intro X L hL n h'
    unfold GlobalTheory.UPel.HT.Hecke.lbPow at h' ⊢
    rw [GlobalTheory.CechPic.cls_linComb hL]
    simp [GlobalTheory.CechPic.pull_id]
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb hP _ _
  have hadd := (GlobalTheory.AbDual.additive_of_cube GlobalTheory.CubeTop.cubeTheorem o.ab o.ab hP o.rig₁ o.rig₂).1
  have evcCls : ∀ {M : LB (o.A ⊗ o.A).left} (hM : M.IsLB) {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hM a t = GlobalTheory.CechPic.pull (lift a t).left (GlobalTheory.CechPic.cls M hM) := by
    intro M hM Y a t
    rw [← GlobalTheory.AbDual.cls_ev hM a t (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM]
  have evcQ : ∀ {Y : Over S} (a t : Y ⟶ o.A),
      GlobalTheory.AbDual.evc hQ a t = (k ^ 2 / c) • GlobalTheory.AbDual.evc hP a t := by
    intro Y a t
    rw [evcCls hQ, evcCls hP, clsPow hP _ hQ, map_nsmul]
  have hpow : ∀ (a : o.A ⟶ o.A) (n : ℕ),
      GlobalTheory.AbDual.evc hP (a ^ n) (𝟙 o.A) = n • GlobalTheory.AbDual.evc hP a (𝟙 o.A) := by
    intro a n
    induction n with
    | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
    | succ n ih => rw [pow_succ, (GlobalTheory.AbDual.isAdditive_iff hP).1 hadd, ih, succ_nsmul]
  set th : o.A ⟶ o.A := toUnit o.A ≫ g with hth
  have hk1 : th ^ k = 1 := by
    rw [hth, ← MonObj.comp_pow, GlobalTheory.UPel.HT.HeckeAd.pow_eq_one_of_mem o (h (N * k)) g hg, MonObj.comp_one]
  have htors : k • GlobalTheory.AbDual.evc hP th (𝟙 o.A) = 0 := by
    rw [← hpow, hk1]; exact GlobalTheory.AbDual.IsAdditive.evc_one hP hadd _
  have hQth : GlobalTheory.AbDual.evc hQ th (𝟙 o.A) = 0 := by
    have hM : (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).IsLB := pull_isLB hQ _
    have hunit : IsUnit ((k : Γ(S, ⊤))) := by
      have hR := b.unit k hk
      have e := hR.map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
      have e2 := e.map (s.appTop.hom)
      simpa using e2
    have hrig : ∃ t : ((GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)).pull
        (1 : 𝟙_ (Over S) ⟶ o.A).left).Gen, t.IsGen := by
      rw [← GlobalTheory.CechPic.cls_eq_zero_iff (pull_isLB hM _), GlobalTheory.CechPic.cls_pull hM, GlobalTheory.AbDual.cls_ev hQ,
        GlobalTheory.AbDual.pull_evc, evcQ, Category.comp_id, GlobalTheory.AbDual.evc_one_right hP o.rig₂, smul_zero]
    have hpowM : ∃ t : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).Gen, t.IsGen := by
      have hMk : (GlobalTheory.UPel.HT.Hecke.lbPow (GlobalTheory.AbDual.ev (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) th (𝟙 o.A)) k).IsLB :=
        LB.isLB_linComb hM _ _
      refine (GlobalTheory.CechPic.cls_eq_zero_iff hMk).1 ?_
      rw [clsPow hM k hMk, GlobalTheory.AbDual.cls_ev hQ, evcQ,
        smul_comm, htors, smul_zero]
    obtain ⟨t, ht⟩ := GlobalTheory.T.rigidified_lineBundle_trivial_of_torsion_geometricFibres S o.A o.ab _ hM hrig k hunit hpowM hfib
    exact (GlobalTheory.AbDual.triv_ev_iff hQ _ _).1 ⟨t, ht⟩
  have hsw : GlobalTheory.CechPic.cls o.P hP = GlobalTheory.CechPic.cls (GlobalTheory.AbDual.swap o.P) (pull_isLB hP _) :=
    (GlobalTheory.CechPic.cls_eq_iff _ _).2 o.symm
  refine ⟨(GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 hQth, (GlobalTheory.AbDual.triv_ev_iff hQ _ _).2 ?_⟩
  rw [evcQ, evcCls hP, hsw, ← evcCls (pull_isLB hP _), GlobalTheory.AbDual.evc_swap hP, ← evcQ]
  exact hQth

end GlobalTheory.UPel.HT.HeckeAd.KerPol
end Main
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_coefficients_congruence : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (toUnit o.A ≫ g) (𝟙 o.A)).left).Gen, t.IsGen) ∧ (∃ t : ((GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).pull (lift (𝟙 o.A) (toUnit o.A ≫ g)).left).Gen, t.IsGen) := by
  first | (exact @GlobalTheory.UPel.HT.HeckeAd.KerPol.hecke_sections_triv) | (exact GlobalTheory.UPel.HT.HeckeAd.KerPol.hecke_sections_triv) | (intros; apply GlobalTheory.UPel.HT.HeckeAd.KerPol.hecke_sections_triv <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsIsotropicCommutatorPairingPower
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCoefficientsCongruenceScaled
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueModelAtPrime
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open GlobalTheory.UPel.HT.Hecke

section GeomAux

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

theorem liftSq_mul' {T : Over S} (a b a' b' : T ⟶ A) :
    (lift a b : T ⟶ G2 A) * lift a' b' = lift (a * a') (b * b') := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.mul_comp]; simp
  · rw [MonObj.mul_comp]; simp

theorem liftSq_pow' {T : Over S} (a b : T ⟶ A) (n : ℕ) :
    (lift a b : T ⟶ G2 A) ^ n = lift (a ^ n) (b ^ n) := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [MonObj.pow_comp]; simp
  · rw [MonObj.pow_comp]; simp

end GeomAux

theorem weilIs_heckeSubA_geom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → ∀ v : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (toUnit (Over.mk x) ≫ (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)) (toUnit (Over.mk x) ≫ (lift 1 g₂ : 𝟙_ (Over S) ⟶ G2 o.A)) v → v = 1 := by

  intro p _ D R _ b h u c k N hc hk hN hNp hck _hlin hcomp hsim _hsurj S s o g₁ hg₁ g₂ hg₂ K _ _ x β hx v hv
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hPL : o.P.IsLB := o.isLB
  obtain ⟨I, hI⟩ := o.geom K x β hx
  obtain ⟨x₁, rfl⟩ := hg₁
  obtain ⟨x₂, rfl⟩ := hg₂
  have hpp : p.Prime := Fact.out
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; exact absurd (Nat.coprime_zero_left p |>.1 hk) hpp.one_lt.ne'
    · exact h0
  have hN0 : 0 < N := by omega
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h0 | h0
    · subst h0; exact absurd (Nat.eq_zero_of_zero_dvd hck) (pow_ne_zero 2 hk0.ne')
    · exact h0

  have hNk0 : 0 < N * k := Nat.mul_pos hN0 hk0
  have hNkp : (N * k).Coprime p := Nat.Coprime.mul_left hNp hk
  have hn'p : (N * k * c).Coprime p := Nat.Coprime.mul_left hNkp hc
  have hn'0 : 0 < N * k * c := Nat.mul_pos hNk0 hc0
  have hmove : ∀ z : D.La, o.eta (N • h (N * k) z) = o.eta (N • h (N * k * c) z) := fun z => by
    obtain ⟨z', hz'⟩ := (hcomp (N * k) c hNk0 hc0 hn'p).1 z
    rw [hz', smul_add, o.eta_add, smul_comm N (N * k) z', o.eta_ker, _root_.mul_one]
  rw [hmove, hmove] at hv
  have hdivE : ((c : ℕ) : ℤ) ∣ D.EF (h (N * k * c) x₁) (h (N * k * c) x₂) := by
    have h1 := (hsim (N * k * c) hn'0 hn'p).2 x₁ x₂
    have h2 : ((c : ℕ) : ℤ) ∣ ((N * k * c : ℕ) : ℤ) := by
      exact_mod_cast Dvd.intro_left (N * k) rfl
    have h3 := h2.trans h1
    have h4 : ((c : ℕ) : ℤ) ∣ (c : ℤ) * u (N * k * c) * D.EF x₁ x₂ :=
      Dvd.dvd.mul_right (Dvd.dvd.mul_right (dvd_refl _) _) _
    have h5 := dvd_add h3 h4
    rwa [sub_add_cancel] at h5
  obtain ⟨e', he'⟩ := hdivE
  obtain ⟨f, hf⟩ : ∃ f, f = h (N * k * c) := ⟨_, rfl⟩
  rw [← hf] at hv he'
  obtain ⟨m, hm⟩ : ∃ m, m = k ^ 2 / c := ⟨_, rfl⟩
  rw [← hm] at hv
  have hmc : m * c = k ^ 2 := by rw [hm]; exact Nat.div_mul_cancel hck
  have hm0 : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, zero_mul] at hmc; exact absurd hmc.symm (pow_ne_zero 2 hk0.ne')
    · exact h0
  obtain ⟨j, hj0, hjp, hjpar⟩ : ∃ j : ℕ, 0 < j ∧ (j * k ^ 2).Coprime p ∧ (Even j ∨ Odd (j * k ^ 2)) := by
    by_cases h2 : p = 2
    · subst h2
      have hko : Odd k := Nat.coprime_two_right.1 hk
      exact ⟨1, one_pos, by rw [_root_.one_mul]; exact Nat.Coprime.pow_left 2 hk,
        Or.inr (by rw [_root_.one_mul]; exact hko.pow)⟩
    · refine ⟨2, two_pos, Nat.coprime_mul_iff_left.2 ⟨?_, Nat.Coprime.pow_left 2 hk⟩, Or.inl even_two⟩
      exact (Nat.coprime_primes Nat.prime_two hpp).2 (Ne.symm h2)
  obtain ⟨n₀, hn₀⟩ : ∃ n₀, n₀ = j * k ^ 2 := ⟨_, rfl⟩
  rw [← hn₀] at hjp hjpar
  have hn0 : 0 < n₀ := by rw [hn₀]; positivity
  have ev0 : ∀ n, I.ev n 0 = 1 := fun n => by
    have h0 := I.add n 0 0
    rw [add_zero] at h0
    exact (mul_eq_left.1 h0.symm)
  have evs : ∀ n (z : D.La) (r : ℕ), I.ev n (r • z) = I.ev n z ^ r := fun n z r => by
    induction r with
    | zero => rw [zero_smul, pow_zero, ev0]
    | succ r ih => rw [succ_nsmul, I.add, ih, pow_succ]
  have hdown : ∀ z : D.La, toUnit (Over.mk x) ≫ o.eta (N • z) = I.ev n₀ z ^ (j * k) := fun z => by
    have t1 := I.tower k N hk0 hN0 (Nat.coprime_mul_iff_left.2 ⟨hk, hNp⟩) z
    have e : k * (j * k) = n₀ := by rw [hn₀]; ring
    have t2 := I.tower k (j * k) hk0 (by positivity) (by rw [e]; exact hjp) z
    rw [Nat.mul_comm k N] at t1
    rw [hI, evs, t1, ← t2, e]
  obtain ⟨w, hw⟩ : ∃ w, w = I.ev n₀ (f x₁) := ⟨_, rfl⟩
  obtain ⟨y, hy⟩ : ∃ y, y = I.ev n₀ (f x₂) := ⟨_, rfl⟩
  have ha : toUnit (Over.mk x) ≫ (lift (o.eta (N • f x₁)) 1 : 𝟙_ (Over S) ⟶ G2 o.A) =
      lift (w ^ (j * k)) (1 ^ (j * k)) := by
    rw [comp_lift, hdown, ← hw, one_pow, MonObj.comp_one]
  have hb : toUnit (Over.mk x) ≫ (lift 1 (o.eta (N • f x₂)) : 𝟙_ (Over S) ⟶ G2 o.A) =
      lift (1 ^ (j * k)) (y ^ (j * k)) := by
    rw [comp_lift, hdown, ← hy, one_pow, MonObj.comp_one]
  rw [ha, hb] at hv
  have e1 := GlobalTheory.T.commutatorPairing_pullback_powerMap_level S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) o.P o.ab (pull_isLB hPL _) o.ample hPL
    o.rig₁ o.rig₂ m (j * k) (j * k) 1 (Over.mk x) w 1 1 y v hv
  have hwn : w ^ n₀ = 1 := (I.onto n₀ hn0 hjp w).2 ⟨f x₁, hw.symm⟩
  have hyn : y ^ n₀ = 1 := (I.onto n₀ hn0 hjp y).2 ⟨f x₂, hy.symm⟩
  have hK : ((n₀ : ℕ) : K) ≠ 0 := by
    have := (b.unit n₀ hjp).map β
    rw [map_natCast] at this
    exact this.ne_zero
  have tor : ∀ a a' : Over.mk x ⟶ o.A, a ^ n₀ = 1 → a' ^ n₀ = 1 →
      (lift a a' : Over.mk x ⟶ G2 o.A) ^ n₀ = 1 := fun a a' h1 h1' => by
    rw [liftSq_pow', h1, h1']
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have one_n : (1 : Over.mk x ⟶ o.A) ^ n₀ = 1 := one_pow _
  have ex : ∀ X Y : Over.mk x ⟶ G2 o.A, X ^ n₀ = 1 → Y ^ n₀ = 1 →
      ∃ e : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) X Y e := fun X Y hX hY =>
    GlobalTheory.WeilGeomPt.exists_weilIs_geomPt S (G2 o.A) o.P hA2 hPL K x n₀ hn0 hK X Y hX hY
  obtain ⟨F, hF⟩ := ex _ _ (tor w 1 hwn one_n) (tor 1 y one_n hyn)
  have hFp : ∀ r : ℕ, Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) (lift (w ^ (r + 1)) 1) (lift 1 y) (F ^ (r + 1)) := by
    intro r
    induction r with
    | zero => simpa using hF
    | succ r ih =>
      have := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL ih hF
      rwa [liftSq_mul', _root_.mul_one, ← pow_succ, ← pow_succ] at this
  have hjm : j * m = (j * m - 1) + 1 := (Nat.sub_add_cancel (Nat.mul_pos hj0 hm0)).symm
  have hFjm : Out.WeilIs (G2 o.A) o.P (n₀ : ℤ) (lift (w ^ (j * m)) 1) (lift 1 y) (F ^ (j * m)) := by
    rw [hjm]; exact hFp _
  have hl1 : (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1).IsLB := LB.isLB_linComb hPL _ _
  have iso1 : LBIso (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1) (o.P.pull (Over.Hom.left (𝟙 (G2 o.A)))) := by
    have c1 := GlobalTheory.CechPic.cls_linComb hPL (fun _ : Fin 1 => 𝟙 (G2 o.A).left) (fun _ => (1 : ℤ)) hl1
    have c2 := GlobalTheory.CechPic.cls_pull hPL (Over.Hom.left (𝟙 (G2 o.A))) (pull_isLB hPL _)
    refine (GlobalTheory.CechPic.cls_eq_iff hl1 (pull_isLB hPL _)).1 (c1.trans (Eq.trans ?_ c2.symm))
    simp
  have e2' : Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P 1) (n₀ : ℤ) (lift (w ^ (j * m)) (1 ^ 1))
      (lift (1 ^ (j * m)) (y ^ 1)) (F ^ (j * m)) := by
    rw [one_pow, one_pow, pow_one]
    exact GlobalTheory.PELFamily.weilIs_of_lbIso hG hA2 hl1 hPL iso1 hFjm
  have e2 := GlobalTheory.T.commutatorPairing_pullback_powerMap_level S o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) o.P o.ab (pull_isLB hPL _) o.ample hPL
    o.rig₁ o.rig₂ 1 (j * m) 1 (n₀ : ℤ) (Over.mk x) w 1 1 y _ e2'
  have hlev : (1 : ℤ) * ((m * (j * k) * (j * k) : ℕ) : ℤ) = (n₀ : ℤ) * ((1 * (j * m) * 1 : ℕ) : ℤ) := by
    rw [hn₀]; push_cast; ring
  have hv' : v = F ^ (j * m) := GlobalTheory.CommutatorPairing.weilIs_unique hG hA2 hPL e1 (hlev ▸ e2)
  have hgeo := I.isom n₀ hn0 hjp (f x₁) (f x₂)
  rw [← hw, ← hy] at hgeo
  obtain ⟨c11, h11⟩ := ex (lift w 1) (lift y 1) (tor w 1 hwn one_n) (tor y 1 hyn one_n)
  obtain ⟨c21, h21⟩ := ex (lift 1 w) (lift y 1) (tor 1 w one_n hwn) (tor y 1 hyn one_n)
  obtain ⟨c22, h22⟩ := ex (lift 1 w) (lift 1 y) (tor 1 w one_n hwn) (tor 1 y one_n hyn)
  have hA := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL h11 h21
  have hB := GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL hF h22
  rw [liftSq_mul', _root_.mul_one, _root_.one_mul] at hA hB
  have hs := GlobalTheory.CommPairing.weilIs_symm hPL (GlobalTheory.SiegelTypings.weilIs_mul hA2 hPL
    (GlobalTheory.CommPairing.weilIs_symm hPL hA) (GlobalTheory.CommPairing.weilIs_symm hPL hB))
  rw [liftSq_mul', _root_.mul_one, _root_.one_mul] at hs
  have hd := GlobalTheory.T.weilPairing_diagonal_pullback_eq S o.A o.P o.ab hPL _ (Over.mk x) w y _ _ hs hgeo
  have e11 := (GlobalTheory.T.weilPairing_birigidified_trivial_on_axes S o.A o.P o.ab hPL o.rig₁ o.rig₂ _ (Over.mk x) w y c11).1 h11
  have e22 := (GlobalTheory.T.weilPairing_birigidified_trivial_on_axes S o.A o.P o.ab hPL o.rig₁ o.rig₂ _ (Over.mk x) w y c22).2 h22
  have e21 := GlobalTheory.T.commutatorPairing_swap_eq_of_swap_invariant S o.A o.P o.ab hPL o.symm _ (Over.mk x) w y c21 F h21 hF
  rw [e11, e22, e21] at hd
  have hF2 : F ^ 2 = unitOn (I.ζ n₀ ^ (2 * ((c : ℤ) * e'))) := by
    rw [← he', ← hd]; group
  have hζ : I.ζ n₀ ^ n₀ = 1 := (I.ζ_prim n₀ hn0 hjp).pow_eq_one
  have hz : ∀ z : ℤ, I.ζ n₀ ^ ((n₀ : ℤ) * z) = 1 := fun z => by
    rw [zpow_mul, zpow_natCast, hζ, one_zpow]
  have hmcZ : (m : ℤ) * c = (k : ℤ) ^ 2 := by exact_mod_cast hmc
  have hnZ : (n₀ : ℤ) = j * (k : ℤ) ^ 2 := by rw [hn₀]; push_cast; ring
  have uPow : ∀ (a : Kˣ) (n : ℕ), unitOn (a ^ n) = unitOn a ^ n := fun a n => map_pow (Units.map _) a n
  have uOne : unitOn (1 : Kˣ) = 1 := map_one (Units.map _)
  have hpw : ∀ t : ℕ, F ^ (2 * t) = unitOn (I.ζ n₀ ^ (2 * ((c : ℤ) * e') * (t : ℤ))) := fun t => by
    rw [pow_mul, hF2, ← uPow, ← zpow_natCast, ← zpow_mul]
  rcases hjpar with ⟨i, hi⟩ | hodd
  · have e : j * m = 2 * (i * m) := by rw [hi]; ring
    rw [hv', e, hpw]
    have ex' : 2 * ((c : ℤ) * e') * ((i * m : ℕ) : ℤ) = (n₀ : ℤ) * e' := by
      rw [hnZ, ← hmcZ, hi]; push_cast; ring
    rw [ex', hz, uOne]
  · have h2 : v ^ 2 = 1 := by
      rw [hv', ← pow_mul, Nat.mul_comm, hpw]
      have ex' : 2 * ((c : ℤ) * e') * ((j * m : ℕ) : ℤ) = (n₀ : ℤ) * (2 * e') := by
        rw [hnZ, ← hmcZ]; push_cast; ring
      rw [ex', hz, uOne]
    have hFn : F ^ n₀ = 1 := GlobalTheory.SiegelTypings.weil_pow_eq_one hA2 hPL (tor w 1 hwn one_n) hF
    have hn : v ^ n₀ = 1 := by rw [hv', ← pow_mul, Nat.mul_comm, pow_mul, hFn, one_pow]
    have hgcd := pow_gcd_eq_one.2 ⟨h2, hn⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.coprime_two_left.2 hodd), pow_one] at hgcd

end GlobalTheory.UPel.HT.HeckeAd
end
end

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hecke_coefficients_congruence_scaled : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (β : R →+* K), x ≫ s = spMap β → ∀ v : Γ((Over.mk x).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (toUnit (Over.mk x) ≫ (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)) (toUnit (Over.mk x) ≫ (lift 1 g₂ : 𝟙_ (Over S) ⟶ G2 o.A)) v → v = 1 := by
  first | (exact @GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_geom) | (exact GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_geom) | (intros; apply GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_geom <;> assumption)
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsIsotropicCommutatorPairingPower
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

open GlobalTheory.CechPic GlobalTheory.DiagPairing GlobalTheory.HeckeWeilLift

theorem exists_weilIs_heckeA : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∃ v : Γ((𝟙_ (Over S)).left, ⊤)ˣ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 g₂) v := by
  intro p _ D R _ b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁ g₂ hg₂
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  have hB : ∀ (T : Over S) (x x' y : T ⟶ o.A), pc o.isLB (x * x') y = pc o.isLB x y + pc o.isLB x' y :=
    fun T x x' y => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T x x' y).1
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), pc o.isLB x (y * y') = pc o.isLB x y + pc o.isLB x y' :=
    fun T x y y' => by
      obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S o.A _ o.ab hD o.ample o.P o.isLB o.rig₁
        o.rig₂ T y y' x).2
      have e := (cls_eq_zero_iff (LB.isLB_linComb o.isLB _ _)).2 ⟨t, ht⟩
      rw [cls_linComb o.isLB, Fin.sum_univ_three] at e
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
        Matrix.tail_cons, one_smul, neg_smul] at e
      unfold pc
      rw [← sub_eq_zero, ← e]
      abel
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hcls : cls _ hQ = (k ^ 2 / c) • cls o.P o.isLB := by
    refine (cls_linComb o.isLB (K := Fin (k ^ 2 / c)) (fun _ => 𝟙 _) (fun _ => 1) hQ).trans ?_
    simp [pull_id]
  have hQB : ∀ (T : Over S) (x x' y : T ⟶ o.A), qc hQ (x * x') y = qc hQ x y + qc hQ x' y :=
    fun T x x' y => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB T x x' y)).trans (smul_add _ _ _)
  have hQB' : ∀ (T : Over S) (x y y' : T ⟶ o.A), qc hQ x (y * y') = qc hQ x y + qc hQ x y' :=
    fun T x y y' => by
      unfold qc
      rw [hcls, map_nsmul, map_nsmul, map_nsmul]
      exact (congrArg _ (hB' T x y y')).trans (smul_add _ _ _)
  obtain ⟨t₁, -⟩ := GlobalTheory.T.hecke_coefficients_congruence p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁
  obtain ⟨-, t₂⟩ := GlobalTheory.T.hecke_coefficients_congruence p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₂ hg₂
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  exact CommutatorPairing.exists_weilIs hG hA2 hQ
    (fun _ => ⟨⊤, trivial, exists_theta_left hQB (Out.overResι ⊤) g₁ t₁⟩)
    (fun _ => ⟨⊤, trivial, exists_theta_right hQB' (Out.overResι ⊤) g₂ t₂⟩)

theorem weilIs_heckeA_pow_eq_one {S : Scheme.{0}} {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R]
    {b : Base D R} {s : S ⟶ Sp R} (f : D.La →+ D.La) (c k N : ℕ) (o : Obj b (N * k) s)
    (g₁ : 𝟙_ (Over S) ⟶ o.A) (hg₁ : g₁ ∈ heckeSubA o f N) (g₂ : 𝟙_ (Over S) ⟶ o.A)
    (v : Γ((𝟙_ (Over S)).left, ⊤)ˣ)
    (hv : Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A)
      (lift 1 g₂) v) : v ^ k = 1 := by
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hA : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have hL : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hk1 : g₁ ^ k = 1 := pow_eq_one_of_mem o f g₁ hg₁
  have hxk : (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ k = 1 := by
    apply CartesianMonoidalCategory.hom_ext
    · rw [MonObj.pow_comp]; simp [hk1]
    · rw [MonObj.pow_comp]; simp
  rcases Nat.eq_zero_or_pos k with hk | hk
  · rw [hk, pow_zero]
  have pw : ∀ m : ℕ, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1
      ((lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) ^ (m + 1)) (lift 1 g₂) (v ^ (m + 1)) := by
    intro m
    induction m with
    | zero => simpa using hv
    | succ m ih =>
      rw [pow_succ _ (m + 1), pow_succ v (m + 1)]
      exact GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL ih hv
  have hp := pw (k - 1)
  rw [Nat.sub_add_cancel hk, hxk] at hp
  have h11 := GlobalTheory.DiagPairing.weilIs_mul_left hG hA hL hp hp
  rw [_root_.mul_one] at h11
  exact mul_eq_left.1 (GlobalTheory.CommutatorPairing.weilIs_unique hG hA hL h11 hp)

theorem weilIs_heckeSubA_one : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 g₂) 1 := by
  intro p _ D R _ b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁ g₂ hg₂
  obtain ⟨v, hv⟩ := exists_weilIs_heckeA p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁
    g₂ hg₂
  have hQ : (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)).IsLB := LB.isLB_linComb o.isLB _ _
  have hA2 : IsAbelianScheme (G2 o.A) := AbelianSchemeGerms.isAbelianScheme_tensor o.A o.A o.ab o.ab
  have h1 : v = 1 := by
    refine GlobalTheory.rootOfUnity_eq_one_of_geom R S s k v (b.unit k hk)
      (weilIs_heckeA_pow_eq_one (h (N * k)) c k N o g₁ hg₁ g₂ v hv) ?_
    intro K _ _ x β hx
    have hp := GlobalTheory.CommPairing.weilIs_pull (A := G2 o.A) GlobalTheory.globalFns_holds hA2 hQ (toUnit (Over.mk x)) hv
    exact GlobalTheory.T.hecke_coefficients_congruence_scaled p D R b h u c k N hc hk hN hNp hdiv hlin hcomp hsim honto S s o g₁ hg₁ g₂ hg₂ K x β hx _ hp
  subst h1
  exact hv

end GlobalTheory.UPel.HT.HeckeAd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeSectionsIsotropicCommutatorPairingPowerStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heckeSections_isotropic_commutatorPairing_power : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), c.Coprime p → k.Coprime p → 3 ≤ N → N.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∀ g₁ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, ∀ g₂ ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o (h (N * k)) N, Out.WeilIs (G2 o.A) (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) 1 (lift g₁ 1 : 𝟙_ (Over S) ⟶ G2 o.A) (lift 1 g₂) 1 := by
  first | (exact @GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_one) | (exact GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_one) | (intros; apply GlobalTheory.UPel.HT.HeckeAd.weilIs_heckeSubA_one <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeTranslateLocallyNoetherianBase
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.UPel.HT.HeckeAd

noncomputable section

namespace GlobalTheory.UPel.HT.HeckeAd

theorem exists_isTranslA : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), 3 ≤ N → N.Coprime p → c.Coprime p → k.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsTranslA (h (N * k)) c k N o o' ψ := by
  intro p _ D R _ b h u c k N hN hNp hc hk hck hlin hcomp hsim honto S _ s o
  have hk0 : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hk; exact (Fact.out : p.Prime).one_lt.ne' hk)
  have hN0 : 0 < N := by omega
  have hNk : 0 < N * k := Nat.mul_pos hN0 hk0
  have hNkp : (N * k).Coprime p := Nat.Coprime.mul_left hNp hk
  set f := h (N * k) with hf
  obtain ⟨hfin, hfree⟩ := GlobalTheory.UPel.HT.HeckeAd.heckeSubA_finite_free b f k N hk0 hN0 hk hNp s o
  obtain ⟨A', _, _, ψ, hA', hψ, hgal⟩ := GlobalTheory.TranslQuotient.exists_quotient S o.A
    (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) (GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N) o.ab (pull_isLB o.isLB _)
    o.ample hfin hfree
  have hepi : Epi ψ := by
    have := GlobalTheory.GaloisCartDesc.epi_of_isGaloisCover hgal
    exact (Over.forget S).epi_of_epi_map this
  have kill : ∀ g ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N, g ≫ ψ = 1 := fun g hg =>
    GlobalTheory.UPel.HT.Hecke.comp_eq_one_of_transl ψ g (hgal.inv ⟨g, hg⟩)
  have stab : ∀ c' : D.O, ∀ g ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N,
      g ≫ o.act.act c' ∈ GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N := fun c' g hg =>
    GlobalTheory.UPel.HT.HeckeAd.act_mem o f (hlin (N * k) hNk hNkp) c' g hg
  choose actf hactf using fun c' : D.O => GlobalTheory.UPel.HT.Hecke.exists_desc_endo S o.A A'
    (GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N) ψ hψ hgal (o.act.act c') (o.act.hom c') (stab c')
  let act' : OActN D.O A' :=
    { act := actf
      hom := fun c' => (hactf c').1
      one := by
        rw [← cancel_epi ψ, (hactf 1).2, o.act.one, Category.id_comp, Category.comp_id]
      mul := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.mul, Category.assoc, ← (hactf b').2, ← Category.assoc,
          ← (hactf c').2, Category.assoc]
      add := fun b' c' => by
        rw [← cancel_epi ψ, (hactf _).2, o.act.add, mul_comp, comp_mul, (hactf _).2, (hactf _).2] }
  have hcomp' : ∀ c' : D.O, o.act.act c' ≫ ψ = ψ ≫ act'.act c' := fun c' => ((hactf c').2).symm

  have hker := GlobalTheory.T.hecke_coefficients_congruence p D R b h u c k N hc hk hN hNp hck hlin hcomp hsim honto S s o
  obtain ⟨u₀, hu₀, hcoc⟩ := GlobalTheory.T.exists_linearisation_birigidifiedPower_isotropicSections S o.A o.ab o.P o.isLB o.rig₁ o.rig₂ (k ^ 2 / c)
    (GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N) (fun g hg => (hker g hg).1) (fun g hg => (hker g hg).2)
    (GlobalTheory.T.heckeSections_isotropic_commutatorPairing_power p D R b h u c k N hc hk hN hNp hck hlin hcomp hsim honto S s o)
  have hGC := GlobalTheory.T.isGaloisCover_prod_sq2_of_isGaloisCover S o.A A' (GlobalTheory.UPel.HT.HeckeAd.heckeSubA o f N) ψ hψ hgal
  obtain ⟨P₀, hP₀, w₀⟩ := GlobalTheory.LinDescent.exists_descent_of_isGaloisCover _ _ (GlobalTheory.UPel.HT.Hecke.sq2 ψ) _ _
    (GlobalTheory.UPel.HT.Hecke.lbPow o.P (k ^ 2 / c)) hGC (DVR.linComb_isLB _ o.isLB _ _) u₀ hu₀ hcoc
  obtain ⟨P', hP', r1, r2, w⟩ := GlobalTheory.T.exists_birigidified_bundle_of_descent p D R b (N * k) S s o A' ψ hψ _ P₀ hP₀ w₀
  have hk2 : 0 < k ^ 2 := by positivity
  have hc0 : 0 < c := Nat.pos_of_ne_zero (by rintro rfl; rw [zero_dvd_iff] at hck; omega)
  have hm1 : 1 ≤ k ^ 2 / c := Nat.div_pos (Nat.le_of_dvd hk2 hck) hc0
  have hmp : (k ^ 2 / c).Coprime p :=
    Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hck) (hk.pow_left 2)
  have hsym := GlobalTheory.T.descended_birigidified_bundle_symmetric p D R b (N * k) S s o A' ψ _ hA' hψ hgal _ P' hP' w r1 r2
  have hamp := GlobalTheory.T.relAmple_diagonal_descended_bundle_galois_cover p D R b (N * k) S s o A' ψ _ hA' hψ hgal _ hm1 P' hP' w
  have hkerP := GlobalTheory.T.descendedBundle_kernel_killed_by_integer_prime_to_p p D R b (N * k) S s o A' ψ _ hA' hψ hgal _ hmp P' hP' w
  have hros := GlobalTheory.T.rosati_involution_of_galois_isogeny_descent p D R b (N * k) S s o A' act' ψ _ hA' hψ hgal hcomp' _ P' hP' w r1 r2
  obtain ⟨hlie, hlieR⟩ := GlobalTheory.UPel.HT.EtaleLie.lie_of_etale p D R b (N * k) S s o A' act' ψ _ _ hA' hψ hgal hcomp'
  have hgeom := GlobalTheory.T.exists_tateSimilitude_heckeTranslate_latticeSystem p D R b h u c k N hc hk hN hNp hck hlin hcomp hsim honto S s o A' act' ψ hA' hψ hgal
    hcomp' P' hP' r1 r2 w
  let o' : Obj b N s :=
    { A := A'
      ab := hA'
      act := act'
      P := P'
      isLB := hP'
      rig₁ := r1
      rig₂ := r2
      symm := hsym
      ample := hamp
      kerP := hkerP
      rosati := hros
      lie := hlie
      lieRank := hlieR
      eta := fun x => o.eta (f x) ≫ ψ
      eta_add := fun x y => by rw [map_add (f := _), o.eta_add, mul_comp]
      eta_lin := fun c' x => by
        show o.eta (f (c' • x)) ≫ ψ = (o.eta (f x) ≫ ψ) ≫ act'.act c'
        obtain ⟨z, hz⟩ := hlin (N * k) hNk hNkp c' x
        rw [← hf] at hz
        rw [hz, o.eta_add, o.eta_ker, _root_.mul_one, o.eta_lin, Category.assoc, hcomp', Category.assoc]
      eta_ker := fun x => by rw [map_nsmul]; exact kill _ (GlobalTheory.UPel.HT.HeckeAd.mem_heckeSubA o f N x)
      geom := hgeom }
  exact ⟨o', ψ, hψ, hcomp', fun x => rfl, hgal, ⟨w⟩, hck⟩

end GlobalTheory.UPel.HT.HeckeAd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeckeTranslateLocallyNoetherianBaseStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.UPel.HT.HeckeAd
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_hecke_translate_locallyNoetherian_base : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (h : ℕ → D.La →+ D.La) (u : ℕ → ℤ) (c k N : ℕ), 3 ≤ N → N.Coprime p → c.Coprime p → k.Coprime p → c ∣ k ^ 2 → (∀ n, 0 < n → n.Coprime p → ∀ (a : D.O) (x : D.La), ∃ z, h n (a • x) = a • h n x + n • z) → (∀ n m, 0 < n → 0 < m → (n * m).Coprime p → (∀ x, ∃ z, h (n * m) x = h n x + n • z) ∧ (n : ℤ) ∣ u (n * m) - u n) → (∀ n, 0 < n → n.Coprime p → IsCoprime (u n) (n : ℤ) ∧ ∀ x y, (n : ℤ) ∣ D.EF (h n x) (h n y) - c * u n * D.EF x y) → (∀ n, 0 < n → n.Coprime p → ∀ x, ∃ y z, h n y = k • x + n • z) → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b (N * k) s), ∃ (o' : Obj b N s) (ψ : o.A ⟶ o'.A), IsTranslA (h (N * k)) c k N o o' ψ := by
  first | (exact @GlobalTheory.UPel.HT.HeckeAd.exists_isTranslA) | (exact GlobalTheory.UPel.HT.HeckeAd.exists_isTranslA) | (intros; apply GlobalTheory.UPel.HT.HeckeAd.exists_isTranslA  <;> assumption)
end
