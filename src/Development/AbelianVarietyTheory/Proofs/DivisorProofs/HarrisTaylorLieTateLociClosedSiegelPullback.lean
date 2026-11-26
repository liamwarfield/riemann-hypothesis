module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieOcExistsSpMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomPointsFactorHenselianOfSpecializes
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeTorsionPointsRestrictBijective

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Definitions.Divisors.EtaLin
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

structure PreEta (b : Base D R) (N : ℕ) (s : S ⟶ Sp R) extends Pre b s where
  eta : D.La → (𝟙_ (Over S) ⟶ A)
  eta_add : ∀ x y, eta (x + y) = eta x * eta y
  eta_lin : ∀ (c : D.O) x, eta (c • x) = eta x ≫ act.act c
  eta_ker : ∀ x, eta (N • x) = 1

def PreEta.GeomAt {b : Base D R} {N : ℕ} {s : S ⟶ Sp R} (o : PreEta b N s) (k : Type) [Field k] (x : Sp k ⟶ S) : Prop :=
  ∃ I : TateIsoO D k (Over.mk x ⟶ o.A) (fun c g => g ≫ o.act.act c)
      (fun n g g' z => Out.WeilIs o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) n g g' (unitOn z)),
    ∀ y, toUnit _ ≫ o.eta y = I.ev N y

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorPreObjectOfSiegelPullback
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorPreObjectOfSiegelPullback
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor

namespace GlobalTheory.PreEtaPull

variable {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} [GrpObj A] [GrpObj A'] {f : S' ⟶ S}
  {φ : A'.left ⟶ A.left} {φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left}

theorem one_left (h : IsGrpPullback A' A f φ) : (1 : A' ⟶ A').left ≫ φ = φ ≫ (1 : A ⟶ A).left := by
  have e : (1 : A' ⟶ A').left ≫ φ = (1 : Over.mk (A'.hom ≫ f) ⟶ A).left :=
    congrArg (fun q => q.left) (map_one (pushHom h A'))
  rw [e, Hom.one_def, Hom.one_def, Over.comp_left, Over.comp_left, Over.toUnit_left, Over.toUnit_left,
    ← Category.assoc, h.1.w]
  rfl

theorem lift_one_id (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (1 : A' ⟶ A') (𝟙 A')).left ≫ φ₂ = φ ≫ (lift (1 : A ⟶ A) (𝟙 A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (1 : A' ⟶ A') (𝟙 A')
    (Z := A) φ (1 : A ⟶ A) (𝟙 A) (by exact (Category.id_comp _).trans (one_left h)) (by simp)
  exact (Category.id_comp _).symm.trans this

theorem lift_id_one (h : IsGrpPullback A' A f φ) (sq : IsSquare φ φ₂) :
    (lift (𝟙 A') (1 : A' ⟶ A')).left ≫ φ₂ = φ ≫ (lift (𝟙 A) (1 : A ⟶ A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ ≫ A.hom)) (T' := A') (𝟙 A'.left) (𝟙 A') (1 : A' ⟶ A')
    (Z := A) φ (𝟙 A) (1 : A ⟶ A) (by simp) (by exact (Category.id_comp _).trans (one_left h))
  exact (Category.id_comp _).symm.trans this


omit [GrpObj A] [GrpObj A'] in
theorem lift_swap (sq : IsSquare φ φ₂) :
    (lift (snd A' A') (fst A' A')).left ≫ φ₂ = φ₂ ≫ (lift (snd A A) (fst A A)).left := by
  have := GlobalTheory.SiegelPull.lift_sq sq (T := Over.mk (φ₂ ≫ (A ⊗ A).hom)) (T' := A' ⊗ A') (𝟙 _) (snd A' A') (fst A' A')
    (Z := A ⊗ A) φ₂ (snd A A) (fst A A) (by exact (Category.id_comp _).trans sq.2.symm)
    (by exact (Category.id_comp _).trans sq.1.symm)
  exact (Category.id_comp _).symm.trans this

end GlobalTheory.PreEtaPull

namespace GlobalTheory.UPel.HT

open GlobalTheory.PreEtaPull

theorem exists_preEta_of_siegPull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ o : PreEta b N (πX ≫ t), ∀ (k : Type) [Field k] (x : Sp k ⟶ X), (o.GeomAt k x ↔ GeomAt D N actX (c.P.pull φ₂X) ηX k x) := by
  intro p _ D R _ b N h M B _ ζ S s₁ t c e he hK X πX AX _ _ φX φ₂X actX ηX hpb hsq hros heta
  have hP : (c.P.pull φ₂X).IsLB := pull_isLB c.isLB φ₂X
  have H : LBIso (c.P.pull φ₂X) (c.P.pull φ₂X) := ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_refl _ hP
  refine ⟨{
    A := AX
    ab := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab hpb
    act := actX
    P := c.P.pull φ₂X
    isLB := hP
    rig₁ := by
      obtain ⟨t₁, ht₁⟩ := c.rig₁
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_one_id hpb hsq) t₁ ht₁
    rig₂ := by
      obtain ⟨t₂, ht₂⟩ := c.rig₂
      exact gen_chartPull (chartPullLinComb c.P φ₂X _ _ _ φX fun _ => lift_id_one hpb hsq) t₂ ht₂
    symm := LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull c.P _ _ rfl)
      (chartPullLinComb c.P _ _ _ _ φ₂X fun _ => lift_swap hsq) c.symm
    ample := (GlobalTheory.pol_pull S X c.A AX πX φX c.diag _ (pull_isLB c.isLB _) (pull_isLB hP _) c.ab hpb
      (GlobalTheory.SiegelPull.diag_iso hsq H)).2.1 hK.1
    kerP := ⟨e, he, kerBy_pull hpb hsq c.isLB hP H e hK.2⟩
    rosati := hros
    eta := ηX
    eta_add := heta.1
    eta_lin := heta.2.1
    eta_ker := heta.2.2 }, fun k _ x => Iff.rfl⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorPreObjectOfSiegelPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_harrisTaylorPreObject_of_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ o : PreEta b N (πX ≫ t), ∀ (k : Type) [Field k] (x : Sp k ⟶ X), (o.GeomAt k x ↔ GeomAt D N actX (c.P.pull φ₂X) ηX k x) := by
  first | (exact @GlobalTheory.UPel.HT.exists_preEta_of_siegPull) | (exact GlobalTheory.UPel.HT.exists_preEta_of_siegPull) | (intros; apply GlobalTheory.UPel.HT.exists_preEta_of_siegPull  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.GeomAtIffOfSpecializes
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportAlg
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.UPel.HT.TateTransportO

theorem exists_torsLift {G H : Type} [Group G] [Group H] (p : ℕ) (ρ : G →* H)
    (hi : ∀ n, 0 < n → n.Coprime p → ∀ g h : G, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h) :
    ∃ L : H → G, ∀ n, 0 < n → n.Coprime p → ∀ g : G, g ^ n = 1 → L (ρ g) = g := by
  classical
  refine ⟨fun x => if h : ∃ g : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g ^ n = 1) ∧ ρ g = x then h.choose else 1, ?_⟩
  intro n hn hnp g hg
  have h : ∃ g' : G, (∃ n, 0 < n ∧ n.Coprime p ∧ g' ^ n = 1) ∧ ρ g' = ρ g := ⟨g, ⟨n, hn, hnp, hg⟩, rfl⟩
  simp only [dif_pos h]
  obtain ⟨⟨m, hm, hmp, hgm⟩, he⟩ := h.choose_spec
  exact hi (m * n) (Nat.mul_pos hm hn) (Nat.Coprime.mul_left hmp hnp) _ _
    (by rw [pow_mul, hgm, one_pow]) (by rw [mul_comm, pow_mul, hg, one_pow]) he

theorem transport_alg :
    ∀ {p : ℕ} [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p)
    {R k k' QR Q Q' : Type} [CommRing R] [Field k] [Field k'] [Group QR] [Group Q] [Group Q'],
    (∀ a b : QR, a * b = b * a) →
    ∀ (actR : D.O → QR → QR) (act : D.O → Q → Q) (act' : D.O → Q' → Q')
    (e : ℕ → Q → Q → kˣ → Prop) (e' : ℕ → Q' → Q' → k'ˣ → Prop)
    (ρ : QR →* Q) (ρ' : QR →* Q') (φ : Rˣ →* kˣ) (φ' : Rˣ →* k'ˣ),
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h) →
    (∀ n, 0 < n → n.Coprime p → ∀ x : Q, x ^ n = 1 → ∃ g : QR, g ^ n = 1 ∧ ρ g = x) →
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 → ρ' g = ρ' h → g = h) →
    (∀ n, 0 < n → n.Coprime p → ∀ x : Q', x ^ n = 1 → ∃ g : QR, g ^ n = 1 ∧ ρ' g = x) →
    (∀ n, 0 < n → n.Coprime p → ∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → φ u = φ v → u = v) →
    (∀ n, 0 < n → n.Coprime p → ∀ z : kˣ, z ^ n = 1 → ∃ u : Rˣ, u ^ n = 1 ∧ φ u = z) →
    (∀ n, 0 < n → n.Coprime p → ∀ u v : Rˣ, u ^ n = 1 → v ^ n = 1 → φ' u = φ' v → u = v) →
    (∀ c g h, actR c (g * h) = actR c g * actR c h) →
    (∀ c g, ρ (actR c g) = act c (ρ g)) → (∀ c g, ρ' (actR c g) = act' c (ρ' g)) →
    (∀ c, act' c 1 = 1) →
    (∀ n, 0 < n → n.Coprime p → ∀ g h : QR, g ^ n = 1 → h ^ n = 1 →
      ∃ u : Rˣ, u ^ n = 1 ∧ e n (ρ g) (ρ h) (φ u) ∧ e' n (ρ' g) (ρ' h) (φ' u)) →
    (∀ n, 0 < n → n.Coprime p → ∀ x y c c', e n x y c → e n x y c' → c = c') →
    ∀ (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e),
    ∃ I' : GlobalTheory.UPel.HT.TateIsoO D k' Q' act' e', ∀ n, 0 < n → n.Coprime p → ∀ a (g : QR), g ^ n = 1 →
      ρ g = I.ev n a → ρ' g = I'.ev n a := by
  intro p _ D R k k' QR Q Q' _ _ _ _ _ _ hcomm actR act act' e e' ρ ρ' φ φ' hρi hρs hρ'i hρ's hφi hφs hφ'i
    hactR hρact hρ'act hact'1 hpair huniq I
  obtain ⟨L, hL⟩ := exists_torsLift p ρ hρi
  obtain ⟨W, hW⟩ := exists_torsLift p φ hφi
  have hLx : ∀ n, 0 < n → n.Coprime p → ∀ x : Q, x ^ n = 1 → L x ^ n = 1 ∧ ρ (L x) = x := by
    intro n hn hnp x hx
    obtain ⟨g, hg, rfl⟩ := hρs n hn hnp x hx
    rw [hL n hn hnp g hg]; exact ⟨hg, rfl⟩
  have hWx : ∀ n, 0 < n → n.Coprime p → ∀ z : kˣ, z ^ n = 1 → W z ^ n = 1 ∧ φ (W z) = z := by
    intro n hn hnp z hz
    obtain ⟨u, hu, rfl⟩ := hφs n hn hnp z hz
    rw [hW n hn hnp u hu]; exact ⟨hu, rfl⟩
  have hLmul : ∀ n, 0 < n → n.Coprime p → ∀ x y : Q, x ^ n = 1 → y ^ n = 1 → L (x * y) = L x * L y := by
    intro n hn hnp x y hx hy
    obtain ⟨hx1, hx2⟩ := hLx n hn hnp x hx
    obtain ⟨hy1, hy2⟩ := hLx n hn hnp y hy
    have := hL n hn hnp (L x * L y)
      (by rw [(show Commute (L x) (L y) from hcomm _ _).mul_pow, hx1, hy1, _root_.one_mul])
    rwa [map_mul, hx2, hy2] at this
  have hevt : ∀ n, 0 < n → n.Coprime p → ∀ a, I.ev n a ^ n = 1 :=
    fun n hn hnp a => (I.onto n hn hnp _).2 ⟨a, rfl⟩
  have hζt : ∀ n, 0 < n → n.Coprime p → I.ζ n ^ n = 1 :=
    fun n hn hnp => (I.ζ_prim n hn hnp).pow_eq_one
  have hactR1 : ∀ c, actR c 1 = 1 := fun c => by
    have := hactR c 1 1
    rw [_root_.mul_one] at this
    exact mul_left_cancel (this.symm.trans (_root_.mul_one _).symm)
  have hactRpow : ∀ c g (n : ℕ), actR c (g ^ n) = actR c g ^ n := by
    intro c g n
    induction n with
    | zero => simp [hactR1]
    | succ n ih => rw [pow_succ, hactR, ih, pow_succ]
  have hLact : ∀ n, 0 < n → n.Coprime p → ∀ c x, x ^ n = 1 → L (act c x) = actR c (L x) := by
    intro n hn hnp c x hx
    obtain ⟨h1, h2⟩ := hLx n hn hnp x hx
    have := hL n hn hnp (actR c (L x)) (by rw [← hactRpow, h1, hactR1])
    rwa [hρact, h2] at this
  refine ⟨{ ζ := fun n => φ' (W (I.ζ n)),
             ζ_prim := ?_,
             ζ_pow := ?_,
             ev := fun n a => if 0 < n ∧ n.Coprime p then ρ' (L (I.ev n a)) else 1,
             add := ?_,
             lin := ?_,
             ker := ?_,
             onto := ?_,
             tower := ?_,
             isom := ?_ }, ?_⟩
  · intro n hn hnp
    obtain ⟨hw1, hw2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    refine ⟨by rw [← map_pow, hw1, map_one], fun l hl => ?_⟩
    rw [← map_pow] at hl
    have : W (I.ζ n) ^ l = 1 := hφ'i n hn hnp _ _
      (by rw [← pow_mul, mul_comm, pow_mul, hw1, one_pow]) (one_pow n) (by rw [hl, map_one])
    exact (I.ζ_prim n hn hnp).dvd_of_pow_eq_one l (by rw [← hw2, ← map_pow, this, map_one])
  · intro n m hn hm hnm
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hnm
    obtain ⟨a1, a2⟩ := hWx (n * m) (Nat.mul_pos hn hm) hnm _ (hζt _ (Nat.mul_pos hn hm) hnm)
    obtain ⟨b1, b2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    show φ' (W (I.ζ (n * m))) ^ m = φ' (W (I.ζ n))
    rw [← map_pow, hφi n hn hnp (W (I.ζ (n * m)) ^ m) (W (I.ζ n))
      (by rw [← pow_mul, mul_comm m n, a1]) b1 (by rw [map_pow, a2, b2, I.ζ_pow n m hn hm hnm])]
  · intro n a b
    split_ifs with h
    · rw [I.add, hLmul n h.1 h.2 _ _ (hevt n h.1 h.2 a) (hevt n h.1 h.2 b), map_mul]
    · rw [_root_.mul_one]
  · intro n c a
    split_ifs with h
    · rw [I.lin, hLact n h.1 h.2 c _ (hevt n h.1 h.2 a), hρ'act]
    · rw [hact'1]
  · intro n hn hnp a
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    rw [← I.ker n hn hnp a]
    obtain ⟨h1, h2⟩ := hLx n hn hnp _ (hevt n hn hnp a)
    constructor
    · intro h
      have := hρ'i n hn hnp _ 1 h1 (one_pow n) (by rw [h, map_one])
      rw [← h2, this, map_one]
    · intro h
      rw [h, ← map_one ρ, hL n hn hnp 1 (one_pow n), map_one]
  · intro n hn hnp y
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    constructor
    · intro hy
      obtain ⟨g, hg1, rfl⟩ := hρ's n hn hnp y hy
      obtain ⟨a, ha⟩ := (I.onto n hn hnp (ρ g)).1 (by rw [← map_pow, hg1, map_one])
      exact ⟨a, by rw [ha, hL n hn hnp g hg1]⟩
    · rintro ⟨a, rfl⟩
      rw [← map_pow, (hLx n hn hnp _ (hevt n hn hnp a)).1, map_one]
  · intro n m hn hm hnm a
    have hnp : n.Coprime p := Nat.Coprime.coprime_dvd_left (Dvd.intro m rfl) hnm
    have hnm0 : 0 < n * m := Nat.mul_pos hn hm
    have hg1 : 0 < n * m ∧ (n * m).Coprime p := ⟨hnm0, hnm⟩
    have hg2 : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg1, if_pos hg2]
    obtain ⟨h1, h2⟩ := hLx (n * m) hnm0 hnm _ (hevt _ hnm0 hnm a)
    have := hL n hn hnp (L (I.ev (n * m) a) ^ m) (by rw [← pow_mul, mul_comm m n, h1])
    rw [map_pow, h2, I.tower n m hn hm hnm] at this
    rw [← map_pow, ← this]
  · intro n hn hnp a b
    have hg : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hg]
    obtain ⟨ga1, ga2⟩ := hLx n hn hnp _ (hevt n hn hnp a)
    obtain ⟨gb1, gb2⟩ := hLx n hn hnp _ (hevt n hn hnp b)
    obtain ⟨u, hu, he, he'⟩ := hpair n hn hnp _ _ ga1 gb1
    rw [ga2, gb2] at he
    obtain ⟨w1, w2⟩ := hWx n hn hnp _ (hζt n hn hnp)
    have hk := huniq n hn hnp _ _ _ _ he (I.isom n hn hnp a b)
    have hu' : u = W (I.ζ n) ^ (2 * D.EF a b) := hφi n hn hnp _ _ hu
      (by rw [← zpow_natCast, ← zpow_mul, mul_comm (2 * D.EF a b), zpow_mul, zpow_natCast, w1, one_zpow])
      (by rw [hk, map_zpow, w2])
    rw [hu', map_zpow] at he'
    exact he'
  · intro n hn hnp a g hg hρg
    have hgd : 0 < n ∧ n.Coprime p := ⟨hn, hnp⟩
    simp only [if_pos hgd]
    rw [← hρg, hL n hn hnp g hg]

end GlobalTheory.UPel.HT.TateTransportO
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

noncomputable section

namespace GlobalTheory.UPel.HT.LevelClopen

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {S : Scheme.{0}}

theorem eSec_diag {A : Over S} [GrpObj A] :
    eSec A ≫ (lift (1 : A ⟶ A) (𝟙 A)).left = eSec A ≫ (lift (𝟙 A) (𝟙 A)).left := by
  simp only [eSec, ← Over.comp_left]
  congr 1
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, lift_fst, Category.comp_id]
    rw [MonObj.comp_one]
    show toUnit _ ≫ η = η
    rw [toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  · simp

theorem exists_cub {b : Base D R} {s : S ⟶ Sp R} (o : Pre b s) :
    ∃ PP : RigLB o.A, PP.L = o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left ∧ Nonempty (CubicalStr o.A PP) := by
  have hL : (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left).IsLB := pull_isLB o.isLB _
  obtain ⟨t, ht⟩ := GlobalTheory.HkFam.cube_of_exists_relAmple o.ab hL o.ample hL
  have hR : Out.Rigidified o.A (o.P.pull (lift (𝟙 o.A) (𝟙 o.A)).left) := by
    obtain ⟨t₁, ht₁⟩ := o.rig₁
    exact ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison.gen_pull_pull o.P (lift (1 : o.A ⟶ o.A) (𝟙 o.A)).left (eSec o.A) _
      (eSec o.A) eSec_diag ⟨pullGenLB t₁ (eSec o.A), pullGenLB_isGen ht₁ _⟩
  exact GlobalTheory.Moduli.cubicalStr_of_triv_theta GlobalTheory.abelianSchemeLaws_all.1 S o.A o.ab _ hL hR ⟨t, ht⟩

theorem isUnit_base {b : Base D R} {s : S ⟶ Sp R} (n : ℕ) (hnp : n.Coprime p) : IsUnit (n : Γ(S, ⊤)) := by
  have := ((b.unit n hnp).map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).map s.appTop.hom
  simpa using this

theorem geomAt_transport {b : Base D R} {N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {s : S ⟶ Sp R}
    (o : PreEta b N s) (R' : Type) [CommRing R'] [HenselianLocalRing R']
    [IsAlgClosed (IsLocalRing.ResidueField R')] (t : Sp R' ⟶ S) {k k' : Type} [Field k] [IsAlgClosed k]
    [Field k'] [IsAlgClosed k'] (i : Sp k ⟶ Sp R') (i' : Sp k' ⟶ Sp R') :
    o.GeomAt k (i ≫ t) → o.GeomAt k' (i' ≫ t) := by
  intro hT
  have hA := o.ab
  have hS : ∀ n : ℕ, 0 < n → n.Coprime p → IsUnit (n : Γ(S, ⊤)) :=
    fun n _ hnp => isUnit_base (b := b) (s := s) n hnp
  have hRu : ∀ n : ℕ, 0 < n → n.Coprime p → IsUnit (n : R') := by
    intro n hn hnp
    have := ((hS n hn hnp).map t.appTop.hom).map (Scheme.ΓSpecIso (CommRingCat.of R')).hom.hom
    simpa using this
  obtain ⟨PP, hPP, ⟨cub⟩⟩ := exists_cub o.toPre
  unfold PreEta.GeomAt at hT ⊢
  change ∃ I : TateIsoO D k' (Over.mk (i' ≫ t) ⟶ o.A) _
      (fun n g g' z => Out.WeilIs o.A (o.toPre.P.pull (lift (𝟙 o.toPre.A) (𝟙 o.toPre.A)).left) n g g' (unitOn z)), _
  rw [← hPP]
  change ∃ I : TateIsoO D k (Over.mk (i ≫ t) ⟶ o.A) _
      (fun n g g' z => Out.WeilIs o.A (o.toPre.P.pull (lift (𝟙 o.toPre.A) (𝟙 o.toPre.A)).left) n g g' (unitOn z)), _ at hT
  rw [← hPP] at hT
  obtain ⟨φ, rfl⟩ : ∃ φ : R' →+* k, i = spMap φ := ⟨(Spec.preimage i).hom, by simp [spMap]⟩
  obtain ⟨φ', rfl⟩ : ∃ φ' : R' →+* k', i' = spMap φ' := ⟨(Spec.preimage i').hom, by simp [spMap]⟩
  obtain ⟨I, hI⟩ := hT
  let A := o.A
  let lvR : D.La → (Over.mk t ⟶ A) := fun a => toUnit _ ≫ o.eta a
  let j : Over.mk (spMap φ ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ) rfl
  let j' : Over.mk (spMap φ' ≫ t) ⟶ Over.mk t := Over.homMk (spMap φ') rfl
  have hj : ∀ a, toUnit (Over.mk (spMap φ ≫ t)) ≫ o.eta a = j ≫ lvR a := fun a => by
    simp only [lvR, ← Category.assoc]; congr 1
  have hj' : ∀ a, toUnit (Over.mk (spMap φ' ≫ t)) ≫ o.eta a = j' ≫ lvR a := fun a => by
    simp only [lvR, ← Category.assoc]; congr 1
  let ρ : (Over.mk t ⟶ A) →* (Over.mk (spMap φ ≫ t) ⟶ A) :=
    { toFun := fun g => j ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun g h => MonObj.comp_mul _ _ _ }
  let ρ' : (Over.mk t ⟶ A) →* (Over.mk (spMap φ' ≫ t) ⟶ A) :=
    { toFun := fun g => j' ≫ g, map_one' := MonObj.comp_one _, map_mul' := fun g h => MonObj.comp_mul _ _ _ }
  have hpull : ∀ {K : Type} [Field K] (ψ : R' →+* K) (n : ℕ) (g h : Over.mk t ⟶ A) (u : R'ˣ),
      Out.WeilIs A PP.L (n : ℤ) g h (unitOn u) →
      Out.WeilIs A PP.L (n : ℤ) ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) ≫ g)
        ((Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) ≫ h)
        (unitOn (Units.map ψ.toMonoidHom u)) := by
    intro K _ ψ n g h u H
    have H' := GlobalTheory.CommPairing.weilIs_pull GlobalTheory.globalFns_holds hA PP.isLB
      (Over.homMk (spMap ψ) rfl : Over.mk (spMap ψ ≫ t) ⟶ Over.mk t) H
    have e : Units.map (spMap ψ).appTop.hom.toMonoidHom (unitOn u) = unitOn (Units.map ψ.toMonoidHom u) :=
      Units.ext (congrArg (fun q => q.hom (u : R')) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom ψ))).symm
    exact e ▸ H'
  have hetapow : ∀ a, o.eta a ^ N = 1 := by
    intro a
    have : ∀ m : ℕ, o.eta (m • a) = o.eta a ^ m := by
      intro m
      induction m with
      | zero =>
        have h0 := o.eta_add 0 0
        rw [add_zero] at h0
        rw [zero_smul, pow_zero]
        exact left_eq_mul.1 h0 |>.symm ▸ rfl
      | succ m ih => rw [succ_nsmul, o.eta_add, ih, pow_succ]
    rw [← this]; exact o.eta_ker a
  have hpow : ∀ a, lvR a ^ N = 1 := fun a => by
    simp only [lvR]; rw [← MonObj.comp_pow, hetapow, MonObj.comp_one]
  have h1 : ∀ n, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 → ρ g = ρ h → g = h :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k φ).1
  have h2 : ∀ n, 0 < n → n.Coprime p → ∀ x : Over.mk (spMap φ ≫ t) ⟶ A, x ^ n = 1 →
      ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧ ρ g = x :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k φ).2
  have h3 : ∀ n, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 → ρ' g = ρ' h → g = h :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k' φ').1
  have h4 : ∀ n, 0 < n → n.Coprime p → ∀ x : Over.mk (spMap φ' ≫ t) ⟶ A, x ^ n = 1 →
      ∃ g : Over.mk t ⟶ A, g ^ n = 1 ∧ ρ' g = x :=
    fun n hn hnp => (GlobalTheory.T.abelian_scheme_torsion_points_restrict_bijective S A hA n hn (hS n hn hnp) R' t k' φ').2
  have h5 := fun n (hn : 0 < n) (hnp : n.Coprime p) =>
    (GlobalTheory.rootsOfUnity_map_bijective_of_henselian R' k φ n hn (hRu n hn hnp))
  have h6 := fun n (hn : 0 < n) (hnp : n.Coprime p) =>
    (GlobalTheory.rootsOfUnity_map_bijective_of_henselian R' k' φ' n hn (hRu n hn hnp))
  have h7 : ∀ (c : D.O) (g h : Over.mk t ⟶ A), (g * h) ≫ o.act.act c = (g ≫ o.act.act c) * (h ≫ o.act.act c) := by
    intro c g h
    haveI := o.act.hom c
    exact MonObj.mul_comp _ _ _
  have h8 : ∀ c, (1 : Over.mk (spMap φ' ≫ t) ⟶ A) ≫ o.act.act c = 1 := by
    intro c
    haveI := o.act.hom c
    exact MonObj.one_comp _
  have h9 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ g h : Over.mk t ⟶ A, g ^ n = 1 → h ^ n = 1 →
      ∃ u : R'ˣ, u ^ n = 1 ∧ Out.WeilIs A PP.L (n : ℤ) (ρ g) (ρ h) (unitOn (Units.map φ.toMonoidHom u)) ∧
        Out.WeilIs A PP.L (n : ℤ) (ρ' g) (ρ' h) (unitOn (Units.map φ'.toMonoidHom u)) := by
    intro n hn hnp g h hg hh
    have loc : ∀ z : Over.mk t ⟶ A, z ^ n = 1 → ∀ p : (Over.mk t).left,
        ∃ V : (Over.mk t).left.Opens, p ∈ V ∧
          ∃ θ : Out.ThetaGrp A PP.L (n : ℤ) (Out.overRes V), θ.pt = Out.overResι V ≫ z := by
      intro z hz p
      obtain ⟨θ, hθ⟩ := GlobalTheory.TorsionThetaLocal.exists_theta_of_pow_eq_one S A PP cub R' t n z hz
      obtain ⟨θ', hθ'⟩ := GlobalTheory.CommutatorPairing.exists_pull PP.isLB θ (Out.overResι ⊤)
      exact ⟨⊤, trivial, θ', by rw [hθ', hθ]⟩
    obtain ⟨c, hc⟩ := GlobalTheory.CommutatorPairing.exists_weilIs GlobalTheory.globalFns_holds hA PP.isLB (loc g hg) (loc h hh)
    have pw : ∀ m : ℕ, Out.WeilIs A PP.L (n : ℤ) (g ^ (m + 1)) h (c ^ (m + 1)) := by
      intro m
      induction m with
      | zero => simpa using hc
      | succ m ih =>
        rw [pow_succ g (m + 1), pow_succ c (m + 1)]
        exact GlobalTheory.DiagPairing.weilIs_mul_left GlobalTheory.globalFns_holds hA PP.isLB ih hc
    have e := pw n
    rw [pow_succ g, hg, _root_.one_mul] at e
    have hcn := GlobalTheory.CommutatorPairing.weilIs_unique GlobalTheory.globalFns_holds hA PP.isLB e hc
    rw [pow_succ, mul_eq_right] at hcn
    obtain ⟨u, rfl⟩ : ∃ u : R'ˣ, unitOn u = c :=
      (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R')).symm.commRingCatIsoToRingEquiv.toMulEquiv).surjective c
    have hu : u ^ n = 1 := by
      apply unitOn_injective_of_commRing
      show unitOn (u ^ n) = unitOn 1
      rw [unitOn, unitOn, map_pow, map_one]
      exact hcn
    have H := hc
    exact ⟨u, hu, hpull φ n g h u H, hpull φ' n g h u H⟩
  have h10 : ∀ n : ℕ, 0 < n → n.Coprime p → ∀ (x y : Over.mk (spMap φ ≫ t) ⟶ A) (c c' : kˣ),
      Out.WeilIs A PP.L (n : ℤ) x y (unitOn c) → Out.WeilIs A PP.L (n : ℤ) x y (unitOn c') → c = c' :=
    fun n _ _ x y c c' h h' => GlobalTheory.weilIs_unique_fieldPoint S A PP.L PP.isLB k (spMap φ ≫ t) n x y c c' h h'
  obtain ⟨I', hI'⟩ := GlobalTheory.UPel.HT.TateTransportO.transport_alg D (R := R') (k := k) (k' := k')
    (QR := Over.mk t ⟶ A) (Q := Over.mk (spMap φ ≫ t) ⟶ A) (Q' := Over.mk (spMap φ' ≫ t) ⟶ A)
    (fun a b => mul_comm a b) (fun c g => g ≫ o.act.act c) (fun c g => g ≫ o.act.act c)
    (fun c g => g ≫ o.act.act c)
    (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c)) (fun n g g' c => Out.WeilIs A PP.L n g g' (unitOn c))
    ρ ρ' (Units.map φ.toMonoidHom) (Units.map φ'.toMonoidHom)
    h1 h2 h3 h4 (fun n hn hnp => (h5 n hn hnp).1) (fun n hn hnp => (h5 n hn hnp).2)
    (fun n hn hnp => (h6 n hn hnp).1)
    h7 (fun c g => (Category.assoc j g (o.act.act c)).symm) (fun c g => (Category.assoc j' g (o.act.act c)).symm)
    h8 h9 h10 I
  exact ⟨I', fun a => (hj' a).trans (hI' N hN hNp a (lvR a) (hpow a) ((hj a).symm.trans (hI a)))⟩

theorem geomAt_iff_of_specializes {b : Base D R} {N : ℕ} (hN : 0 < N) (hNp : N.Coprime p) {s : S ⟶ Sp R}
    (o : PreEta b N s) {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] [IsAlgClosed k']
    (x : Sp k ⟶ S) (x' : Sp k' ⟶ S) (u : Sp k) (u' : Sp k') (h : x'.base u' ⤳ x.base u) :
    o.GeomAt k x ↔ o.GeomAt k' x' := by
  obtain ⟨R', _, _, _, r, i, i', rfl, rfl⟩ := GlobalTheory.geomPoints_factor_henselian_of_specializes x x' u u' h
  exact ⟨geomAt_transport hN hNp o R' r i i', geomAt_transport hN hNp o R' r i' i⟩

end GlobalTheory.UPel.HT.LevelClopen

namespace GlobalTheory.UPel.HT

open LevelClopen

theorem PreEta.exists_clopen_geomAt : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R]
    (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R)
    (o : PreEta b N s), ∃ U : S.Opens, IsClosed (U : Set S) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k]
    (x : Sp k ⟶ S), (Set.range x.base ⊆ (U : Set S) ↔ o.GeomAt k x) := by
  intro p _ D R _ b N hN3 hNp S _ s o
  have hN : 0 < N := by omega
  let U : Set S := {z | ∃ (k : Type) (_ : Field k) (_ : IsAlgClosed k) (x : Sp k ⟶ S),
    z ∈ Set.range x.base ∧ o.GeomAt k x}
  have hclo : IsClopen U := by
    refine GlobalTheory.SpecGenClopen.isClopen_of_specializes_iff S U fun z w hzw => ?_
    constructor
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := GlobalTheory.FinEt.exists_algClosed_point S w
      obtain ⟨u', hu'⟩ : w ∈ Set.range x'.base := by rw [show Set.range x'.base = {w} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩,
        (geomAt_iff_of_specializes hN hNp o x' x u' u ?_).2 hG⟩
      rw [hu, hu']
      exact hzw
    · rintro ⟨k, _, _, x, ⟨u, hu⟩, hG⟩
      obtain ⟨k', _, _, x', hx'⟩ := GlobalTheory.FinEt.exists_algClosed_point S z
      obtain ⟨u', hu'⟩ : z ∈ Set.range x'.base := by rw [show Set.range x'.base = {z} from hx']; rfl
      refine ⟨k', inferInstance, inferInstance, x', ⟨u', hu'⟩,
        (geomAt_iff_of_specializes hN hNp o x x' u u' ?_).1 hG⟩
      rw [hu, hu']
      exact hzw
  refine ⟨⟨U, hclo.isOpen⟩, hclo.isClosed, fun k _ _ x => ⟨fun hx => ?_,
    fun hG z hz => ⟨k, inferInstance, inferInstance, x, hz, hG⟩⟩⟩
  let pt : Sp k := (⊥ : PrimeSpectrum k)
  obtain ⟨k', _, _, x', ⟨u', hu'⟩, hG'⟩ := hx ⟨pt, rfl⟩
  exact (geomAt_iff_of_specializes hN hNp o x x' pt u' (hu' ▸ specializes_rfl)).2 hG'

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionRestrictClopenFactorization
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionRestrictClopenFactorization
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem clopen_cut_closedImmersion : ∀ {X Z₁ : Scheme.{0}} (i : Z₁ ⟶ X), IsClosedImmersion i → ∀ (U : X.Opens), IsClosed (U : Set X) → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), ((∃ z : T ⟶ Z, z ≫ j = g) ↔ (∃ y : T ⟶ Z₁, y ≫ i = g) ∧ Set.range g.base ⊆ (U : Set X)) := by
  intro X Z₁ i hi U hU
  have hVc : IsClosed (Set.range (i ⁻¹ᵁ U).ι.base) := by
    rw [Scheme.Opens.range_ι]
    exact hU.preimage i.base.hom.continuous
  haveI : IsClosedImmersion (i ⁻¹ᵁ U).ι := IsClosedImmersion.of_isPreimmersion _ hVc
  refine ⟨(i ⁻¹ᵁ U), (i ⁻¹ᵁ U).ι ≫ i, inferInstance, fun T g => ?_⟩
  constructor
  · rintro ⟨z, rfl⟩
    refine ⟨⟨z ≫ (i ⁻¹ᵁ U).ι, by simp⟩, ?_⟩
    rintro _ ⟨t, rfl⟩
    have : ((i ⁻¹ᵁ U).ι.base (z.base t)) ∈ (i ⁻¹ᵁ U : Set Z₁) := by
      rw [← Scheme.Opens.range_ι]; exact ⟨_, rfl⟩
    simpa [Scheme.Hom.comp_base] using this
  · rintro ⟨⟨y, rfl⟩, hg⟩
    have h : Set.range y.base ⊆ Set.range (i ⁻¹ᵁ U).ι.base := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      have := hg ⟨t, rfl⟩
      simpa using this
    exact ⟨IsOpenImmersion.lift (i ⁻¹ᵁ U).ι y h, by rw [← Category.assoc, IsOpenImmersion.lift_fac]⟩

end GlobalTheory
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedImmersionRestrictClopenFactorizationStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closedImmersion_restrict_clopen_factorization : ∀ {X Z₁ : Scheme.{0}} (i : Z₁ ⟶ X), IsClosedImmersion i → ∀ (U : X.Opens), IsClosed (U : Set X) → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), ((∃ z : T ⟶ Z, z ≫ j = g) ↔ (∃ y : T ⟶ Z₁, y ≫ i = g) ∧ Set.range g.base ⊆ (U : Set X)) := by
  first | (exact @GlobalTheory.clopen_cut_closedImmersion) | (exact GlobalTheory.clopen_cut_closedImmersion) | (intros; apply GlobalTheory.clopen_cut_closedImmersion <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersionOfAffinePoints
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersionOfAffinePoints
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem GlobalTheory.factor_closedImmersion_of_affine_points :
    ∀ {X Z T : Scheme.{0}} (i : Z ⟶ X), IsClosedImmersion i → ∀ (g : T ⟶ X),
      (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ T), ∃ y : Sp R' ⟶ Z, y ≫ i = x ≫ g) →
      ∃ z : T ⟶ Z, z ≫ i = g := by
  intro X Z T i hi g h
  let 𝒰 := T.affineCover
  have hj : ∀ j, ∃ y : 𝒰.X j ⟶ Z, y ≫ i = 𝒰.f j ≫ g := fun j => h _ (𝒰.f j)
  choose y hy using hj
  have hc : ∀ a b, pullback.fst (𝒰.f a) (𝒰.f b) ≫ y a = pullback.snd (𝒰.f a) (𝒰.f b) ≫ y b := by
    intro a b
    rw [← cancel_mono i, Category.assoc, Category.assoc, hy, hy, ← Category.assoc, ← Category.assoc,
      pullback.condition]
  refine ⟨𝒰.glueMorphisms y hc, ?_⟩
  refine 𝒰.hom_ext _ _ fun j => ?_
  rw [← Category.assoc, Scheme.Cover.ι_glueMorphisms, hy]
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorClosedImmersionOfAffinePointsStatement
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_factor_closedImmersion_of_affine_points : ∀ {X Z T : Scheme.{0}} (i : Z ⟶ X), IsClosedImmersion i → ∀ (g : T ⟶ X), (∀ (R' : Type) [CommRing R'] (x : Sp R' ⟶ T), ∃ y : Sp R' ⟶ Z, y ≫ i = x ≫ g) → ∃ z : T ⟶ Z, z ≫ i = g := by
  first | (exact @GlobalTheory.factor_closedImmersion_of_affine_points) | (exact GlobalTheory.factor_closedImmersion_of_affine_points) | (intros; apply GlobalTheory.factor_closedImmersion_of_affine_points <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateLociClosedSiegelPullback
noncomputable section

namespace GlobalTheory.UPel.HT

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.SiegelTor

theorem lieGeom_locus_closed : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), (∃ z : T ⟶ Z, z ≫ j = g) ↔ ((∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ g ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ g)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : R →+* k), x ≫ g ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ g)) := by
  intro p _ D R _ b N hN3 hNp h M B _ ζ S s₁ t c e he hK X _ πX AX _ _ φX φ₂X actX ηX hpb hsq hros heta
  have hab : IsAbelianScheme AX := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback c.ab hpb
  obtain ⟨Z₁, i₁, hi₁, hZ₁⟩ := lieHer_closed b (πX ≫ t) AX hab.smooth actX
  obtain ⟨o, ho⟩ := GlobalTheory.T.exists_harrisTaylorPreObject_of_siegelPullback p D R b N h M B ζ S s₁ t c e he hK X πX AX φX φ₂X actX ηX hpb hsq hros heta
  obtain ⟨U, hU, hUx⟩ := PreEta.exists_clopen_geomAt p D R b N hN3 hNp X (πX ≫ t) o
  obtain ⟨Z, j, hj, hZ⟩ := GlobalTheory.T.closedImmersion_restrict_clopen_factorization i₁ hi₁ U hU
  refine ⟨Z, j, hj, fun T g => ?_⟩
  rw [hZ T g]
  apply and_congr
  · constructor
    · rintro ⟨y, rfl⟩ R' _ β x hx
      exact (hZ₁ R' β (x ≫ y ≫ i₁) (by simpa only [Category.assoc] using hx)).1 ⟨x ≫ y, by simp⟩
    · intro H
      refine GlobalTheory.T.exists_factor_closedImmersion_of_affine_points i₁ hi₁ g fun R' _ x => ?_
      obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ g ≫ πX ≫ t)
      exact (hZ₁ R' β (x ≫ g) (by simpa only [Category.assoc] using hβ)).2 (H R' β x hβ)
  · constructor
    · intro hg k _ _ x β _
      refine (ho k (x ≫ g)).1 ((hUx k (x ≫ g)).1 ?_)
      rintro _ ⟨u, rfl⟩
      exact hg ⟨x.base u, by simp⟩
    · intro H
      rintro _ ⟨τ, rfl⟩
      obtain ⟨k, _, _, x, hx⟩ := GlobalTheory.FinEt.exists_algClosed_point T τ
      obtain ⟨β, hβ⟩ := lieOc_exists_spMap (x ≫ g ≫ πX ≫ t)
      have hG := (hUx k (x ≫ g)).2 ((ho k (x ≫ g)).2 (H k x β hβ))
      obtain ⟨u, hu⟩ : τ ∈ Set.range x.base := by rw [hx]; rfl
      exact hG ⟨u, by simp [hu]⟩

end GlobalTheory.UPel.HT
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieTateLociClosedSiegelPullbackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.SiegelTor
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_tate_loci_closed_siegelPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (h M : ℕ) (B : Type) [CommRing B] (ζ : B) (S : Scheme.{0}) (s₁ : S ⟶ Sp B) (t : S ⟶ Sp R) (c : SiegPre h M ζ s₁) (e : ℕ), e.Coprime p → SiegKerBy c e → ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (πX : X ⟶ S) (AX : Over X) [GrpObj AX] [IsCommMonObj AX] (φX : AX.left ⟶ c.A.left) (φ₂X : (G2 AX).left ⟶ (G2 c.A).left) (actX : OActN D.O AX) (ηX : D.La → (𝟙_ (Over X) ⟶ AX)), IsGrpPullback AX c.A πX φX → IsSquare φX φ₂X → RosatiFor D actX (c.P.pull φ₂X) → EtaOK D N actX ηX → ∃ (Z : Scheme.{0}) (j : Z ⟶ X), IsClosedImmersion j ∧ ∀ (T : Scheme.{0}) (g : T ⟶ X), (∃ z : T ⟶ Z, z ≫ j = g) ↔ ((∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ T), x ≫ g ≫ πX ≫ t = spMap β → LieHer b actX β (x ≫ g)) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ T) (β : R →+* k), x ≫ g ≫ πX ≫ t = spMap β → GeomAt D N actX (c.P.pull φ₂X) ηX k (x ≫ g)) := by
  first | (exact @GlobalTheory.UPel.HT.lieGeom_locus_closed) | (exact GlobalTheory.UPel.HT.lieGeom_locus_closed) | (intros; apply GlobalTheory.UPel.HT.lieGeom_locus_closed  <;> assumption)
end
