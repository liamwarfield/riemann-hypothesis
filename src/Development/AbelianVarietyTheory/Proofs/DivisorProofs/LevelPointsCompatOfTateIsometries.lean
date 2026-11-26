module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UValThruTopOfDisjoint

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateIsoGenericAbelianOfUniformisation
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateIsoGenericAbelianOfUniformisation
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem exists_tateIso_toA : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
  (I : (letI := H.starRing; TateIsoQ D P.D.toPre P.oD F)),
  ∃ J : TateIso D F (TFK (R := R) F ⟶ P.A.A) (fun a g => g ≫ (letI := H.starRing; P.oA.act a))
      (fun n g g' z => Out.WeilIs P.A.A P.A.L n g g' (unitOn z)),
    (∀ n, J.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ a, P.ToA F n (I.ev n a) (J.ev n a) := by
  intro E _ _ _ H D R _ _ _ hR t P F _ _ _ I
  letI := H.starRing
  have hA : AdmBase R (maximalIdeal R) := hR.1
  have h0 : CharZero R := hR.2
  have hT := GlobalTheory.FlatTors.torsionIso_holds E H R _ hA t P
  choose f f₁ f₂ f₃ f₄ f₅ f₆ using hT F
  obtain ⟨ev, ev0, evp⟩ : ∃ ev : ℕ → D.La → (TFK (R := R) F ⟶ P.A.A), (∀ a, ev 0 a = 1) ∧
      ∀ n (hn : 0 < n) a, ev n a = f n hn (I.ev n a) :=
    ⟨fun n a => if hn : 0 < n then f n hn (I.ev n a) else 1, fun a => dif_neg (lt_irrefl 0),
      fun n hn a => dif_pos hn⟩
  have add : ∀ n a b, ev n (a + b) = ev n a * ev n b := fun n a b => by
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ev0, ev0, ev0, _root_.one_mul]
    · rw [evp n hn, evp n hn, evp n hn, f₄ n hn _ _ _ (I.add n hn a b)]
  have zero : ∀ n, ev n 0 = 1 := fun n => by
    have := add n 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have tors : ∀ n (hn : 0 < n) p, f n hn p ^ n = 1 := fun n hn p => by
    obtain ⟨w, hw⟩ := P.U.ext
    exact ((f₁ n hn p _).2 rfl w hw).1
  refine ⟨{ ζ := I.ζ, ζ_prim := I.ζ_prim, ζ_pow := I.ζ_pow, ev := ev, add := add
            lin := fun n c a => ?_, ker := fun n hn a => ?_, onto := fun n hn x => ⟨fun hx => ?_, ?_⟩
            tower := fun n m hn hm a => ?_, isom := fun n hn a b => ?_ },
    fun _ => rfl, fun j hj x => (f₁ j hj _ _).2 (evp j hj x)⟩
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [ev0, ev0]
      have := P.oA.hom c
      exact (MonObj.one_comp _).symm
    · rw [evp n hn, evp n hn, f₅ n hn _ _ _ (I.lin n hn c a)]
  · rw [← zero n, evp n hn, evp n hn, f₃, I.ker n hn]
    simp only [zero_add]
  · obtain ⟨p, hp⟩ := f₂ n hn x hx
    obtain ⟨a, ha⟩ := I.onto n hn p
    exact ⟨a, by rw [evp n hn, (f₃ n hn _ _).2 ha, hp]⟩
  · rintro ⟨a, rfl⟩
    rw [evp n hn, tors]
  · obtain ⟨q, q₁, q₂, q₃⟩ := I.tower n m hn hm a
    have hN := Nat.mul_pos hn hm
    have h := (GlobalTheory.LevelCompat.qkToAkU_level GlobalTheory.firstFiveLaws R _ hA P.D P.A t.G t.semi P.U F n m _ hn hm rfl q
      (I.ev (n * m) a) _).2 q₁ q₂ ((f₁ _ hN _ _).2 rfl)
    rw [evp _ hN, evp n hn, (f₁ n hn _ _).1 h, (f₃ n hn _ _).2 q₃]
  · have h := (f₆ n hn _ _ _).1 (I.isom n hn a b)
    rw [← evp, ← evp] at h
    exact h

end GlobalTheory.LowDat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTateIsoGenericAbelianOfUniformisationStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_tateIso_generic_abelian_of_uniformisation : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R →
  ∀ (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F]
  (I : (letI := H.starRing; TateIsoQ D P.D.toPre P.oD F)),
  ∃ J : TateIso D F (TFK (R := R) F ⟶ P.A.A) (fun a g => g ≫ (letI := H.starRing; P.oA.act a))
      (fun n g g' z => Out.WeilIs P.A.A P.A.L n g g' (unitOn z)),
    (∀ n, J.ζ n = I.ζ n) ∧ ∀ n, 0 < n → ∀ a, P.ToA F n (I.ev n a) (J.ev n a) := by
  first | exact @GlobalTheory.LowDat.exists_tateIso_toA | exact GlobalTheory.LowDat.exists_tateIso_toA | (intros; apply GlobalTheory.LowDat.exists_tateIso_toA <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoEvEqAtLcmLevel
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoEvEqAtLcmLevel
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat.Uniq

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem ev_zsmul {D : Datum H} {k : Type} [Field k] {Q : Type} [Group Q] {act : 𝓞 E → Q → Q}
    {e : ℕ → Q → Q → kˣ → Prop} (J : TateIso D k Q act e) (n : ℕ) (m : ℤ) (x : D.La) :
    J.ev n (m • x) = J.ev n x ^ m := by
  let f : Multiplicative D.La →* Q :=
    MonoidHom.mk' (fun y => J.ev n (Multiplicative.toAdd y)) (fun a b => J.add n _ _)
  have h := map_zpow f (Multiplicative.ofAdd x) m
  rw [← ofAdd_zsmul] at h
  exact h

theorem mul_mem_M (l : Level H) {x y : 𝓞 E} (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E)) (hy : y ∈ l.Mb) :
    ∃ r : 𝓞 E, x * y = r * (l.M : 𝓞 E) := by
  have h : y * x ∈ l.Mb * l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mul_mem_mul hy hx
  rw [l.prod, Ideal.mem_span_singleton'] at h
  obtain ⟨r, hr⟩ := h
  exact ⟨r, by rw [mul_comm, ← hr]⟩

theorem smul_mem_M {D : Datum H} (l : Level H) {x : 𝓞 E} (hx : x ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E))
    {b : D.La} (hb : b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : ∃ c : D.La, x • b = l.M • c := by
  refine Submodule.smul_induction_on (p := fun b => ∃ c : D.La, x • b = l.M • c) hb ?_ ?_
  · intro y hy t _
    obtain ⟨r, hr⟩ := mul_mem_M l hx hy
    refine ⟨r • t, ?_⟩
    rw [← mul_smul, hr, mul_comm, mul_smul, Nat.cast_smul_eq_nsmul]
  · rintro b1 b2 ⟨c1, hc1⟩ ⟨c2, hc2⟩
    exact ⟨c1 + c2, by rw [smul_add, hc1, hc2, smul_add]⟩

theorem dvd_EF (D : Datum H) (l : Level H) {a c : D.La} (ha : a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La))
    (hc : c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La)) : (l.M : ℤ) ∣ D.EF a c := by
  refine Submodule.smul_induction_on (p := fun a => (l.M : ℤ) ∣ D.EF a c) ha ?_ ?_
  · intro y hy t _
    show (l.M : ℤ) ∣ D.EF (y • t) c
    rw [D.adj]
    have hy' : H.bar y ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := Ideal.mem_map_of_mem (H.bar : 𝓞 E →+* 𝓞 E) hy
    obtain ⟨c', hc'⟩ := smul_mem_M l hy' hc
    rw [hc', map_nsmul, nsmul_eq_mul]
    exact dvd_mul_right _ _
  · intro x y hx hy
    show (l.M : ℤ) ∣ D.EF (x + y) c
    rw [map_add (f := _), LinearMap.add_apply]
    exact dvd_add hx hy

end GlobalTheory.LowDat.Uniq

namespace GlobalTheory.LowDat


open GlobalTheory.LowDat.Uniq in
theorem tateIso_ev_lcm_eq : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Level H)
    (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop),
    (∀ n, 0 < n → ∀ x y c c', e n x y c → e n x y c' → c = c') → ∀ J J' : TateIso D k Q act e, J.ζ l.M' = J'.ζ l.M' →
    (∀ a, J.ev l.A a = J'.ev l.A a) →
    (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M a = J'.ev l.M a) →
    ∀ a, J.ev l.M' a = J'.ev l.M' a := by
  intro E _ _ _ H D l k _ Q _ act e huniq J J' hζ hA hM
  have hM0 : 0 < l.M := by have := l.three_le; omega
  have hA0 := l.A_pos

  obtain ⟨j, hj⟩ := Nat.gcd_dvd_left l.M l.A
  obtain ⟨kk, hkk⟩ := Nat.gcd_dvd_right l.M l.A
  have hgl : Nat.gcd l.M l.A * l.M' = l.M * l.A := Nat.gcd_mul_lcm _ _
  have hg0 : 0 < Nat.gcd l.M l.A := Nat.gcd_pos_of_pos_left _ hM0
  have hcop0 := Nat.coprime_div_gcd_div_gcd (m := l.M) (n := l.A) hg0
  generalize Nat.gcd l.M l.A = G at hj hkk hgl hg0 hcop0
  have hMk : l.M' = l.M * kk := Nat.eq_of_mul_eq_mul_left hg0 (by rw [hgl, hkk]; ring)
  have hAj : l.M' = l.A * j := Nat.eq_of_mul_eq_mul_left hg0 (by rw [hgl, hj]; ring)
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, mul_zero] at hj; omega
    · exact h
  have hk0 : 0 < kk := by
    rcases Nat.eq_zero_or_pos kk with h | h
    · rw [h, mul_zero] at hkk; omega
    · exact h
  have hcop : Nat.Coprime j kk := by
    have e1 : l.M / G = j := by rw [hj]; exact Nat.mul_div_cancel_left j hg0
    have e2 : l.A / G = kk := by rw [hkk]; exact Nat.mul_div_cancel_left kk hg0
    rw [e1, e2] at hcop0; exact hcop0
  obtain ⟨u, v, huv⟩ := Nat.isCoprime_iff_coprime.mpr hcop

  have hζM : J.ζ l.M = J'.ζ l.M := by
    rw [← J.ζ_pow l.M kk hM0 hk0, ← J'.ζ_pow l.M kk hM0 hk0, ← hMk, hζ]

  have h1 : (1 : 𝓞 E) ∈ l.Mb ⊔ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) := by rw [l.coprime]; trivial
  obtain ⟨f, hf, g2, hg2, hfg⟩ := Submodule.mem_sup.mp h1
  have decomp : ∀ x : D.La, x = f • x + g2 • x := fun x => by rw [← add_smul, hfg, one_smul]

  have key : ∀ b ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M b = J'.ev l.M b := by
    intro b hb
    have hord : (J'.ev l.M b) ^ l.M = 1 := (J'.onto l.M hM0 _).mpr ⟨b, rfl⟩
    obtain ⟨b', hb'⟩ := (J.onto l.M hM0 _).mp hord
    have h2 : J.ev l.M (g2 • b') = 1 := by
      rw [J.lin, hb', ← J'.lin]
      obtain ⟨c, hc⟩ := smul_mem_M (D := D) l hg2 hb
      rw [hc]; exact (J'.ker l.M hM0 _).mpr ⟨c, rfl⟩
    have hb'' : J.ev l.M (f • b') = J'.ev l.M b := by
      have h := J.add l.M (f • b') (g2 • b')
      rw [← decomp b', h2, _root_.mul_one] at h
      rw [← hb', h]
    have hf' : f • b' ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := Submodule.smul_mem_smul hf Submodule.mem_top
    set c := b - f • b' with hcdef
    have hcm : c ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := Submodule.sub_mem _ hb hf'
    have hdiv : ∀ a, (l.M : ℤ) ∣ D.EF a c := by
      intro a
      rw [decomp a, map_add (f := _), LinearMap.add_apply]
      refine dvd_add (dvd_EF D l (Submodule.smul_mem_smul hf Submodule.mem_top) hcm) ?_
      have hga : g2 • a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La) :=
        Submodule.smul_mem_smul hg2 Submodule.mem_top
      have i1 := J.isom l.M hM0 (g2 • a) (f • b')
      have i2 := J'.isom l.M hM0 (g2 • a) b
      rw [hM _ hga, hb'', hζM] at i1
      have heq := huniq l.M hM0 _ _ _ _ i1 i2
      rw [← (J'.ζ_prim l.M hM0).zpow_eq_one_iff_dvd, hcdef, map_sub, zpow_sub, heq, mul_inv_cancel]
    have hdiv' : ∀ a, (l.M : ℤ) ∣ D.EF c a := fun a => by
      have h := D.alt (a + c)
      simp only [map_add (f := _), LinearMap.add_apply, D.alt a, D.alt c, zero_add, add_zero] at h
      have h' : D.EF c a = - D.EF a c := by linarith
      rw [h']; exact (hdiv a).neg_right
    choose q hq using hdiv'
    have hMne : (l.M : ℤ) ≠ 0 := by exact_mod_cast hM0.ne'
    let φ : D.La →ₗ[ℤ] ℤ :=
      { toFun := q
        map_add' := fun x y => by
          apply mul_left_cancel₀ hMne
          rw [← hq, mul_add, ← hq, ← hq, map_add (f := _)]
        map_smul' := fun m x => by
          apply mul_left_cancel₀ hMne
          rw [← hq, RingHom.id_apply, smul_eq_mul, mul_left_comm, ← hq, map_zsmul, smul_eq_mul] }
    obtain ⟨c0, hc0⟩ := D.unimod.2 φ
    have hc : c = l.M • c0 := by
      apply D.unimod.1
      ext a
      rw [map_nsmul, LinearMap.smul_apply, hc0, nsmul_eq_mul]
      exact hq a
    have hJc : J.ev l.M c = 1 := (J.ker l.M hM0 _).mpr ⟨c0, hc⟩
    have hbc : b = f • b' + c := by rw [hcdef]; abel
    rw [hbc, J.add, hJc, _root_.mul_one, hb'', ← hbc]
  have hall : ∀ a, J.ev l.M a = J'.ev l.M a := by
    intro a
    rw [decomp a, J.add, J'.add, key _ (Submodule.smul_mem_smul hf Submodule.mem_top),
      hM _ (Submodule.smul_mem_smul hg2 Submodule.mem_top)]

  have expand : ∀ (K : TateIso D k Q act e) (a : D.La),
      K.ev l.M' a = K.ev l.A (u • a) * K.ev l.M (v • a) := by
    intro K a
    have ha : a = (j : ℤ) • (u • a) + (kk : ℤ) • (v • a) := by
      rw [smul_smul, smul_smul, ← add_smul, mul_comm (j : ℤ), mul_comm (kk : ℤ), huv, one_smul]
    conv_lhs => rw [ha]
    rw [K.add, ev_zsmul K l.M' (j : ℤ) (u • a), ev_zsmul K l.M' (kk : ℤ) (v • a), zpow_natCast, zpow_natCast]
    congr 1
    · have h := K.tower l.A j hA0 hj0 (u • a); rw [← hAj] at h; exact h
    · have h := K.tower l.M kk hM0 hk0 (v • a); rw [← hMk] at h; exact h
  intro a
  rw [expand J, expand J', hA, hall]

end GlobalTheory.LowDat
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateIsoEvEqAtLcmLevelStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tateIso_ev_eq_at_lcm_level : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) (l : Level H) (k : Type) [Field k] (Q : Type) [Group Q] (act : 𝓞 E → Q → Q) (e : ℕ → Q → Q → kˣ → Prop),
  (∀ n, 0 < n → ∀ x y c c', e n x y c → e n x y c' → c = c') → ∀ J J' : TateIso D k Q act e, J.ζ l.M' = J'.ζ l.M' →
  (∀ a, J.ev l.A a = J'.ev l.A a) →
  (∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), J.ev l.M a = J'.ev l.M a) →
  ∀ a, J.ev l.M' a = J'.ev l.M' a := by
  first | exact @GlobalTheory.LowDat.tateIso_ev_lcm_eq | exact GlobalTheory.LowDat.tateIso_ev_lcm_eq | (intros; apply GlobalTheory.LowDat.tateIso_ev_lcm_eq <;> assumption)
end
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsCompatOfTateIsometries
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.LowDat

theorem mono_jK_of_domain (R : Type) [CommRing R] [IsDomain R] : Mono (jK R) := by
  have : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  infer_instance

theorem spMap_comp_jFK {R : Type} [CommRing R] [IsDomain R] {F F' : Type} [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') :
    spMap σ.toRingHom ≫ jFK (R := R) F = jFK (R := R) F' := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

theorem left_eq_of_section (C : UChart.Fam Xo c R) (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R))
    (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _)) {F F' : Type} [Field F] [Algebra (FractionRing R) F]
    [Field F'] [Algebra (FractionRing R) F'] (σ : F →ₐ[FractionRing R] F') (s : 𝟙_ (Over Xo.X) ⟶ Xo.univ.t.G)
    (x : TFK (R := R) F ⟶ C.P.A.A) (x' : TFK (R := R) F' ⟶ C.P.A.A)
    (g : Sp F ⟶ tK.G.left) (h1 : g ≫ m1.φ = x.left ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R))
    (h2 : g ≫ m2.φ = jFK (R := R) F ≫ C.y ≫ pullback.fst _ _ ≫ s.left)
    (g' : Sp F' ⟶ tK.G.left) (h1' : g' ≫ m1.φ = x'.left ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R))
    (h2' : g' ≫ m2.φ = jFK (R := R) F' ≫ C.y ≫ pullback.fst _ _ ≫ s.left) :
    x'.left = spMap σ.toRingHom ≫ x.left := by
  have := mono_jK_of_domain R
  have w0 : C.P.U.gen.inv.left ≫ pullback.snd C.t.G.hom (jK R) = C.P.A.A.hom := Over.w C.P.U.gen.inv
  have w : x.left ≫ C.P.A.A.hom = jFK (R := R) F := Over.w x
  have w' : x'.left ≫ C.P.A.A.hom = jFK (R := R) F' := Over.w x'
  have c1 : m1.φ ≫ C.t.G.hom = tK.G.hom ≫ jK R := m1.cart.1.w
  have key : ∀ {T : Scheme.{0}} (p : T ⟶ tK.G.left) (z : T ⟶ C.P.A.A.left),
      p ≫ m1.φ = z ≫ C.P.U.gen.inv.left ≫ pullback.fst C.t.G.hom (jK R) → p ≫ tK.G.hom = z ≫ C.P.A.A.hom := by
    intro T p z h
    rw [← cancel_mono (jK R), Category.assoc, ← c1, ← Category.assoc, h, ← w0]
    simp only [Category.assoc, pullback.condition]
  have e1 : g ≫ tK.G.hom = jFK (R := R) F := (key g _ h1).trans w
  have e1' : g' ≫ tK.G.hom = jFK (R := R) F' := (key g' _ h1').trans w'
  have e : g' = spMap σ.toRingHom ≫ g := by
    refine m2.cart.1.hom_ext ?_ ?_
    · have q := congrArg (· ≫ C.y ≫ pullback.fst _ _ ≫ s.left) (spMap_comp_jFK σ)
      exact h2'.trans (q.symm.trans ((Category.assoc _ _ _).trans
        ((congrArg (spMap σ.toRingHom ≫ ·) h2.symm).trans (Category.assoc _ _ _).symm)))
    · rw [Category.assoc, e1, e1', spMap_comp_jFK]
  have e2 : x'.left ≫ C.P.U.gen.inv.left = spMap σ.toRingHom ≫ x.left ≫ C.P.U.gen.inv.left := by
    refine pullback.hom_ext ?_ ?_
    · simp only [Category.assoc]
      rw [← h1, ← h1', e, Category.assoc]
    · simp only [Category.assoc]
      rw [w0, w, w', spMap_comp_jFK]
  have hi : C.P.U.gen.inv.left ≫ C.P.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  have e3 := congrArg (· ≫ C.P.U.gen.hom.left) e2
  simpa only [Category.assoc, hi, Category.comp_id] using e3

theorem exists_tateIso_ext (D : Datum H) {S : Scheme.{0}} (P : Out.PolAV S) (act : 𝓞 E → (P.A ⟶ P.A))
    {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed K] [IsAlgClosed Ω] [CharZero K] (i : K →+* Ω)
    (x : Sp K ⟶ S) (x' : Sp Ω ⟶ S) (h : spMap i ≫ x = x')
    (I : TateIso D K (Over.mk x ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c))) :
    ∃ I' : TateIso D Ω (Over.mk x' ⟶ P.A) (fun c y => y ≫ act c) (fun n y y' c => Out.WeilIs P.A P.L n y y' (unitOn c)),
      ∀ n, 0 < n → (I'.ζ n : Ω) = i (I.ζ n) ∧ ∀ v, (I'.ev n v).left = spMap i ≫ (I.ev n v).left := by
  subst h
  obtain ⟨I', hI⟩ := (TateIsoFieldExt.tateIso_fieldExt abelianSchemeLaws_all.1 E H D S P act K Ω i x).1 I
  exact ⟨I', fun n hn => ⟨(hI n hn).1, fun v => by rw [(hI n hn).2 v]; rfl⟩⟩

end GlobalTheory.LowDat

theorem GlobalTheory.LowDat.level_points_compat : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
  (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F']
  (σ : F →ₐ[FractionRing R] F')
  (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F')),
  GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.XFLevel C tK m1 m2 F' I' →
  ∀ (a : Dw.La) (x : TFK (R := R) F ⟶ C.P.A.A) (x' : TFK (R := R) F' ⟶ C.P.A.A),
    C.P.ToA F l.M' (I.ev l.M' a) x → C.P.ToA F' l.M' (I'.ev l.M' a) x' → x'.left = spMap σ.toRingHom ≫ x.left := by
  intro E _ _ _ H Dw l Xo c R _ _ _ hR C tK m1 m2 F F' _ _ _ _ _ _ σ I I' hI hI' a x x' hx hx'
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) := charZero_of_injective_algebraMap (IsFractionRing.injective R _)
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap (FractionRing R) F).injective
  obtain ⟨J, hJζ, hJ⟩ := GlobalTheory.T.exists_tateIso_generic_abelian_of_uniformisation Dw R hR C.t C.P F I
  obtain ⟨J', hJζ', hJ'⟩ := GlobalTheory.T.exists_tateIso_generic_abelian_of_uniformisation Dw R hR C.t C.P F' I'
  obtain ⟨J₂, h₂⟩ := GlobalTheory.LowDat.exists_tateIso_ext Dw C.P.A _ σ.toRingHom _ _ (GlobalTheory.LowDat.spMap_comp_jFK σ) J
  have hM : 0 < l.M := by have := l.three_le; omega
  have hM' : 0 < l.M' := Nat.lcm_pos hM l.A_pos
  have hT := GlobalTheory.T.linearUniformisation_torsionIsomorphism E H R _ hR.1 C.t C.P
  have u : J₂.ev l.M' a = J'.ev l.M' a := by
    refine GlobalTheory.T.tateIso_ev_eq_at_lcm_level Dw l F' _ _ _
      (fun n _ p q d d' => GlobalTheory.weilIs_unique_fieldPoint _ _ _ C.P.A.isLB F' _ n p q d d') J₂ J' ?_ ?_ ?_ a
    · apply Units.ext
      rw [(h₂ _ hM').1, hJζ, hJζ', hI.1, hI'.1]
      simp [GlobalTheory.LowDat.toF]
    · intro b
      obtain ⟨g, g1, g2⟩ := hI.2 _ b _ (Or.inl ⟨rfl, rfl⟩) _ (hJ _ l.A_pos b)
      obtain ⟨g', g1', g2'⟩ := hI'.2 _ b _ (Or.inl ⟨rfl, rfl⟩) _ (hJ' _ l.A_pos b)
      exact Over.OverMorphism.ext (((h₂ _ l.A_pos).2 b).trans
        (GlobalTheory.LowDat.left_eq_of_section C tK m1 m2 σ _ _ _ g g1 g2 g' g1' g2').symm)
    · intro b hb
      obtain ⟨g, g1, g2⟩ := hI.2 _ b _ (Or.inr ⟨rfl, hb, rfl⟩) _ (hJ _ hM b)
      obtain ⟨g', g1', g2'⟩ := hI'.2 _ b _ (Or.inr ⟨rfl, hb, rfl⟩) _ (hJ' _ hM b)
      exact Over.OverMorphism.ext (((h₂ _ hM).2 b).trans
        (GlobalTheory.LowDat.left_eq_of_section C tK m1 m2 σ _ _ _ g g1 g2 g' g1' g2').symm)
  obtain ⟨f, hf, -⟩ := hT F l.M' hM'
  obtain ⟨f', hf', -⟩ := hT F' l.M' hM'
  have e : x = J.ev l.M' a := ((hf _ _).1 hx).trans ((hf _ _).1 (hJ _ hM' a)).symm
  have e' : x' = J'.ev l.M' a := ((hf' _ _).1 hx').trans ((hf' _ _).1 (hJ' _ hM' a)).symm
  rw [e, e', ← u]
  exact (h₂ _ hM').2 a
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelPointsCompatOfTateIsometriesStatement
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPoints_compat_of_tateIsometries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H} (Xo : Moduli Dw l)
  (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (C : GlobalTheory.UChart.Fam Xo c R)
  (tK : SAB H (Sp (FractionRing R))) (m1 : SABMap tK C.t (jK R)) (m2 : SABMap tK Xo.univ.t (C.y ≫ pullback.fst _ _))
  (F F' : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Field F'] [IsAlgClosed F'] [Algebra (FractionRing R) F']
  (σ : F →ₐ[FractionRing R] F')
  (I : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F)) (I' : (letI := H.starRing; TateIsoQ Dw C.P.D.toPre C.P.oD F')),
  GlobalTheory.LowDat.XFLevel C tK m1 m2 F I → GlobalTheory.LowDat.XFLevel C tK m1 m2 F' I' →
  ∀ (a : Dw.La) (x : TFK (R := R) F ⟶ C.P.A.A) (x' : TFK (R := R) F' ⟶ C.P.A.A),
    C.P.ToA F l.M' (I.ev l.M' a) x → C.P.ToA F' l.M' (I'.ev l.M' a) x' → x'.left = spMap σ.toRingHom ≫ x.left := by
  first | exact @GlobalTheory.LowDat.level_points_compat | exact GlobalTheory.LowDat.level_points_compat | (intros; apply GlobalTheory.LowDat.level_points_compat <;> assumption)
end
end
