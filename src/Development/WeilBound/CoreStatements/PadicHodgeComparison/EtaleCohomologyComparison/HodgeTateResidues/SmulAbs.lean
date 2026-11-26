module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.FirstChernHodgeTateCompatAlt
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RedTrans
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BcOnFalse
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.SmoothGaloisGeometry.NormLtOneOfIrreducible
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.BocksteinBaseChange.AdicTorsionCup.PrimOfOver

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.RhoExA
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT.RhoA

open Pb GlobalTheory.CompanionTheory.LiftLat

section Gr
variable {b : Base} {L : b.Fun} (Q : ObjectProperty (Thick L))

theorem pow_tf (c : b.R) (r : ℤ)
    (hT : ∀ (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x ∈ (sFil Q r).S T → x ∈ (sFil Q r).S T) (n : ℕ)
    (T : Q.FullSubcategory) (x : (sP Q).A.obj T) (h : c ^ n • x ∈ (sFil Q r).S T) : x ∈ (sFil Q r).S T := by
  induction n generalizing x with
  | zero => simpa using h
  | succ n ih =>
    rw [pow_succ, mul_smul] at h
    exact hT T x (ih _ h)

theorem gr_part (c : b.R) (r : ℕ)
    (hT : ∀ (r : ℤ) (T : Q.FullSubcategory) (x : (sP Q).A.obj T), c • x ∈ (sFil Q r).S T → x ∈ (sFil Q r).S T) (j k : ℕ)
    (h1 : ∀ (x : HG Q r (j + 1)) (n : ℕ), c ^ n • x = 0 → c ^ k • x = 0)
    (h2 : ∀ x : HG Q r j, (∀ n : ℕ, ∃ y, x = c ^ n • y) → c ^ k • x = 0)
    (h3 : ∀ x : ℕ → HG Q r j, (∀ n, ∃ y, x (n + 1) - x n = c ^ n • y) → ∃ z : HG Q r j, ∀ n, ∃ y, z - c ^ k • x n = c ^ n • y) :
    (∀ x : ∀ n, HGm Q (c ^ n) r j, (∀ n, trG Q c n r j (x (n + 1)) = x n) →
      ∃ z : HG Q r j, ∀ n, redG' Q (c ^ n) r j z = c ^ (2 * k) • x n) ∧
    ∀ z : HG Q r j, (∀ n, redG' Q (c ^ n) r j z = 0) → c ^ k • z = 0 := by
  have hle : ∀ T : Q.FullSubcategory, (sFil Q ((r : ℤ) + 1)).S T ≤ (sFil Q r).S T := fun T => T.obj.pdPow_anti (Nat.le_succ r)
  let red := fun n : ℕ => sqLe (a := sFil Q r) (b := sFil Q ((r : ℤ) + 1)) (a' := stdI Q (some (r : ℤ)) (c ^ n))
    (b' := stdI Q (some ((r : ℤ) + 1)) (c ^ n)) (fun _ => le_sup_left) fun _ => le_sup_left
  let tr := fun n : ℕ => sqLe (stdI_le Q (some (r : ℤ)) c n) (stdI_le Q (some ((r : ℤ) + 1)) c n)
  refine gen (G := fun n => sq (stdI Q (some (r : ℤ)) (c ^ n)) (stdI Q (some ((r : ℤ) + 1)) (c ^ n))) c red tr
    (fun n T => (red n).τ T) (fun n T => (tr n).τ T) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) ?_ ?_ ?_ ?_ j k h1 h2 h3
  · intro n T x
    obtain ⟨y, hy, rfl⟩ := sq_surj _ _ x
    rfl
  · intro n T y
    obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
    obtain ⟨u, hu⟩ := (mem_some Q r _ T y).1 hy
    refine ⟨sqMk _ _ _ hu, (sq_eq _ _ (Ideal.mem_sup_left hu) hy).2 ((mem_some Q _ _ T _).2 ⟨-u, ?_⟩)⟩
    rw [smul_neg, show y - c ^ n • u - y - -(c ^ n • u) = 0 by abel]
    exact zero_mem _
  · intro n T x
    obtain ⟨w, hw, rfl⟩ := sq_surj _ _ x
    have e1 : (red n).τ T (sqMk _ _ w hw) = 0 ↔ w ∈ (stdI Q (some ((r : ℤ) + 1)) (c ^ n)).S T :=
      sqMk_eq_zero (stdI Q (some (r : ℤ)) (c ^ n)) _ w (Ideal.mem_sup_left hw)
    refine e1.trans ((mem_some Q _ _ T w).trans ⟨?_, ?_⟩)
    · rintro ⟨y, hy⟩
      have hy' : y ∈ (sFil Q r).S T := pow_tf Q c r (hT r) n T y (by
        have := sub_mem hw (hle T hy)
        rwa [sub_sub_cancel] at this)
      exact ⟨sqMk _ _ y hy', (sq_eq _ _ hw (Submodule.smul_of_tower_mem _ _ hy')).2 hy⟩
    · rintro ⟨y, h⟩
      obtain ⟨y, hy, rfl⟩ := sq_surj _ _ y
      exact ⟨y, (sq_eq _ _ hw (Submodule.smul_of_tower_mem _ _ hy)).1 h⟩
  · intro T x hx
    obtain ⟨w, hw, rfl⟩ := sq_surj _ _ x
    have e2 := (sqMk_eq_zero _ _ (c • w) (Submodule.smul_of_tower_mem _ _ hw)).1 hx
    exact (sqMk_eq_zero _ _ w hw).2 (hT _ T w e2)

end Gr

theorem lift_gr (hA : AfgA) {O A : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CommRing A] [Algebra O A] {I : Ideal A}
    (γ : DividedPowers I) (l m : ℕ) (hdv : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) (hO : TFBase (dividedPowersBot O) l m)
    (hL : LatBase γ l m) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q] (U : Cov q) (r : ℕ) (hr : r < m) (j : ℕ) :
    ∃ k : ℕ, (∀ x : ∀ n, HGm (TS γ q l m {⊤}) ((l : A) ^ n) r j, (∀ n, trG (TS γ q l m {⊤}) (l : A) n r j (x (n + 1)) = x n) →
      ∃ z : HG (TS γ q l m {⊤}) r j, ∀ n, redG' (TS γ q l m {⊤}) ((l : A) ^ n) r j z = (l : A) ^ (2 * k) • x n) ∧
    ∀ z : HG (TS γ q l m {⊤}) r j, (∀ n, redG' (TS γ q l m {⊤}) ((l : A) ^ n) r j z = 0) → (l : A) ^ k • z = 0 := by
  have hf := fun j => hA γ l m m hdv hO hL le_rfl q U {⊤} sSup_singleton r ((r : ℤ) + 1) (by omega) (by omega) j
  obtain ⟨k, a, b, d⟩ := bounds hL (hf j) (hf (j + 1))
  refine ⟨k, gr_part (TS γ q l m {⊤}) (l : A) r ?_ j k a b d⟩
  intro r T x h
  have e : (l : A) • x = (l : T.obj.B) * (show T.obj.B from x) := by
    rw [Algebra.smul_def, map_natCast]
  rw [e] at h
  exact T.property.1.2 _ _ h

theorem sub_trans {O A R₁ R₂ Λ : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing R₁] [CommRing R₂] [CommRing Λ]
    {I : Ideal A} {γ : DividedPowers I} {J₁ : Ideal R₁} {J₂ : Ideal R₂} {δ₁ : DividedPowers J₁} {δ₂ : DividedPowers J₂}
    {κ₁ : O →+* R₁ ⧸ J₁} {κ₂ : O →+* R₂ ⧸ J₂} {l n : ℕ} (d₁ : RedIn δ₁ κ₁ γ l (n + 1)) (d₂ : RedIn δ₂ κ₂ γ l n) {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} (s : ℕ) (𝒱 : Set X.Opens) {σ' : R₁ →+* R₂}
    (m : GlobalTheory.LogCris.Mor (nlFun δ₁ l X q κ₁) (nlFun δ₂ l X q κ₂) σ')
    (c₁ : Λ →+* R₁) (c₂ : Λ →+* R₂) (lam : Λ →+* A) (hc₁ : ∀ a, d₁.ρ (c₁ a) = Ideal.Quotient.mk _ (lam a))
    (hc₂ : ∀ a, d₂.ρ (c₂ a) = Ideal.Quotient.mk _ (lam a)) (h₀ : ∀ a, σ' (c₁ a) = c₂ (RingHom.id Λ a))
    (hpt : ∀ (B : CommRingCat.{0}) (y : PtOver X q κ₂ B), (show PtOver X q κ₁ B from m.pt.app B y).1.2 = y.1.2)
    (hs : Function.Surjective c₁) (r j : ℕ) (x : CH.H (B.pdS (nlFun δ₁ l X q κ₁) c₁ r).fn j) :
    (redSub q s 𝒱 d₂ c₂ lam hc₂ r).pull j ((pdOm m (RingHom.id Λ) h₀ r).pull j x) =
      trG (TS γ q l s 𝒱) (l : A) n r j ((redSub q s 𝒱 d₁ c₁ lam hc₁ r).pull j x) := by
  have hρ : ∀ x, d₂.ρ (σ' x) = lnMap (RingHom.id A) l n.le_succ (d₁.ρ x) := fun x => by
    obtain ⟨a, rfl⟩ := hs x
    rw [h₀, hc₁, hc₂]; rfl
  rw [pull_pull lam]
  change _ = (sqLe (stdI_le (TS γ q l s 𝒱) (some (r : ℤ)) (l : A) n) (stdI_le (TS γ q l s 𝒱) (some ((r : ℤ) + 1)) (l : A) n)).pull j _
  rw [pull_pull lam]
  refine (CrystallineSemistableComparison.P.prism _ _ ⟨fun T => GlobalTheory.CompanionTheory.RedTrans.eta d₁ d₂ m hpt hρ T.obj T.property.1, fun T T' f => ?_⟩
    (fun T x => ?_) j x).symm
  · refine hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
  · obtain ⟨x, hx⟩ := x
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l (n + 1)) x
    rfl

end CrystallineSemistableComparison.HT.RhoA
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.HT

open Pb

namespace RhoA

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem ok_dv (a : OK l K) (ha : a ≠ 0) : ∃ k : ℕ, a ∣ (l : OK l K) ^ k := by
  have ha' : (a : K) ≠ 0 := fun e => ha (Subtype.ext e)
  have h0 : 0 < ‖((a : K) : PadicAlgCl l)‖ := norm_pos_iff.2 (by exact_mod_cast ha')
  have e : (((l : ℕ) : K) : PadicAlgCl l) = algebraMap ℚ_[l] (PadicAlgCl l) (l : ℚ_[l]) := by simp
  have h1 : ‖(((l : ℕ) : K) : PadicAlgCl l)‖ < 1 := by
    rw [e, PadicAlgCl.norm_extends]
    exact Padic.norm_p_lt_one
  obtain ⟨k, hk⟩ := exists_pow_lt_of_lt_one h0 h1
  refine ⟨k, ⟨(a : K)⁻¹ * (l : K) ^ k, (mem_OK _).2 ?_⟩, Subtype.ext ?_⟩
  · rw [IntermediateField.coe_mul, IntermediateField.coe_inv, IntermediateField.coe_pow, norm_mul, norm_inv, norm_pow]
    rw [inv_mul_le_iff₀ h0, mul_one]
    exact hk.le
  · change (((l : OK l K) ^ k : OK l K) : K) = (a : K) * ((a : K)⁻¹ * (l : K) ^ k)
    rw [mul_inv_cancel_left₀ ha']
    simp

theorem tf_dom {O : Type} [CommRing O] [IsDomain O] [CharZero O] {l : ℕ} (hl : l ≠ 0)
    (hdv : ∀ a : O, a ≠ 0 → ∃ k : ℕ, a ∣ (l : O) ^ k) {s : ℕ} (hs : 1 ≤ s) : TFBase (dividedPowersBot O) l s := by
  have hb : ∀ r, 1 ≤ r → pdP (dividedPowersBot O) r = ⊥ := fun r hr => by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hr
    refine le_bot_iff.1 (le_trans ?_ (GlobalTheory.CompanionTheory.LiftLat.dividedPowerFiltration_one_eq (dividedPowersBot O)).le)
    refine Ideal.span_mono ?_
    rintro _ ⟨L, h1, h2, rfl⟩
    exact ⟨L, h1, by omega, rfl⟩
  refine ⟨hb s hs, fun r x hx => ?_, fun n hn => ?_⟩
  · rcases Nat.eq_zero_or_pos r with rfl | hr
    · have : (1 : O) ∈ pdP (dividedPowersBot O) 0 := Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
      simpa using Ideal.mul_mem_left _ x this
    · rw [hb r hr, Ideal.mem_bot] at hx ⊢
      exact (mul_eq_zero.1 hx).resolve_left (Nat.cast_ne_zero.2 hl)
  · obtain ⟨k, u, hu⟩ := hdv n (Nat.cast_ne_zero.2 hn)
    exact ⟨k, u, hu.symm⟩

section Abs
variable {A B Λ : Type} [CommRing A] [CommRing B] [CommRing Λ] {ι : A →+* B} {Z W : Type 1} [AddCommGroup Z] [Module A Z]
  [AddCommGroup W] [Module B W] (b : Z →ₛₗ[ι] W) {Zn : ℕ → Type 1} [∀ n, AddCommGroup (Zn n)] [∀ n, Module A (Zn n)]
  (red : ∀ n, Z →ₗ[A] Zn n) (l : ℕ)

theorem b_pow (e : ℕ) (z : Z) : b ((l : A) ^ e • z) = (l : B) ^ e • b z := by
  rw [LinearMap.map_smulₛₗ, map_pow, map_natCast]

theorem exu (hu : IsUnit (l : B)) (x : ∀ n, Zn n) (e₀ : ℕ) (z₀ : Z) (h₀ : ∀ n, red n z₀ = (l : A) ^ e₀ • x n) (k : ℕ)
    (hs : ∀ z, (∀ n, red n z = 0) → (l : A) ^ k • z = 0) :
    ∃! w : W, ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z := by
  have key : ∀ (w w' : W) e z e' z', (∀ n, red n z = (l : A) ^ e • x n) → (l : B) ^ e • w = b z →
      (∀ n, red n z' = (l : A) ^ e' • x n) → (l : B) ^ e' • w' = b z' → w = w' := by
    intro w w' e z e' z' h1 h2 h3 h4
    have h5 := hs ((l : A) ^ e' • z - (l : A) ^ e • z') fun n => by
      rw [map_sub, map_smul, map_smul, h1, h3, smul_comm, sub_self]
    have h6 := congrArg b h5
    rw [b_pow, map_sub, b_pow, b_pow, ← h2, ← h4, map_zero, smul_comm ((l : B) ^ e) ((l : B) ^ e') w', ← smul_sub, ← smul_sub,
      smul_smul, smul_smul] at h6
    exact sub_eq_zero.1 (((((hu.pow k).mul (hu.pow e')).mul (hu.pow e)).smul_eq_zero).1 h6)
  obtain ⟨u, hu'⟩ := (hu.pow e₀).exists_right_inv
  have hw : (l : B) ^ e₀ • (u • b z₀) = b z₀ := by rw [smul_smul, hu', one_smul]
  exact ⟨u • b z₀, ⟨e₀, z₀, h₀, hw⟩, fun w ⟨e, z, h1, h2⟩ => key _ _ _ _ _ _ h1 h2 h₀ hw⟩

theorem add_abs (x y : ∀ n, Zn n) (w w' : W) (h : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z)
    (h' : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • y n) ∧ (l : B) ^ e • w' = b z) :
    ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • (x n + y n)) ∧ (l : B) ^ e • (w + w') = b z := by
  obtain ⟨e, z, h1, h2⟩ := h
  obtain ⟨e', z', h3, h4⟩ := h'
  refine ⟨e + e', (l : A) ^ e' • z + (l : A) ^ e • z', fun n => ?_, ?_⟩
  · rw [map_add (f := _), map_smul, map_smul, h1, h3, smul_smul, smul_smul, smul_add, pow_add, mul_comm ((l : A) ^ e')]
  · rw [map_add (f := _), b_pow, b_pow, ← h2, ← h4, smul_smul, smul_smul, smul_add, pow_add, mul_comm ((l : B) ^ e')]

theorem smul_abs (x : ∀ n, Zn n) (w : W) (a : A)
    (h : ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • x n) ∧ (l : B) ^ e • w = b z) :
    ∃ (e : ℕ) (z : Z), (∀ n, red n z = (l : A) ^ e • (a • x n)) ∧ (l : B) ^ e • (ι a • w) = b z := by
  obtain ⟨e, z, h1, h2⟩ := h
  refine ⟨e, a • z, fun n => ?_, ?_⟩
  · rw [map_smul, h1, smul_comm]
  · rw [LinearMap.map_smulₛₗ, ← h2, smul_comm]

end Abs

variable {Y : CB l K} {m : ℕ} (L : Lv Y m) (M : Model l K)

theorem unit_B : IsUnit (l : L.B) := by
  have := (isUnit_iff_ne_zero.2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero) : IsUnit (l : K)).map (algebraMap K L.B)
  rwa [map_natCast] at this

theorem rS_tr (r j n : ℕ) (x : CH.H (Y.SS M r (n + 1)).fn j) :
    (L.rS M r n).pull j ((pdOm (Y.redM M n) (RingHom.id _) (Y.rd_c n) r).pull j x) =
      trG (L.QA M) (l : L.A) n r j ((L.rS M r (n + 1)).pull j x) :=
  sub_trans (L.d (n + 1)) (L.d n) m {⊤} (Y.redM M n) (Y.c (n + 1)) (Y.c n) L.lam (L.d_lam (n + 1)) (L.d_lam n) (Y.rd_c n)
    (fun _ _ => rfl) (Y.c_surj (n + 1)) r j x

theorem ex [FiniteDimensional ℚ_[l] K] (hM : M.Sm) (r j : ℕ) (hr : r < m) (x : Y.Fam M r j) (hx : CB.Comp x) : ∃! w, L.Rho x w := by
  haveI := AdicGeo.proper_p hM.1
  haveI : IsDiscreteValuationRing (OK l K) := OK_dvr
  obtain ⟨U⟩ := (cov_ex M.p).1 hM.2
  obtain ⟨k, h1, h2⟩ := lift_gr afgA L.γ l m ok_dv (tf_dom (Fact.out : l.Prime).ne_zero ok_dv (by omega)) L.lat M.p U r hr j
  obtain ⟨z, hz⟩ := h1 (fun n => (L.rS M r n).pull j (x n)) fun n =>
    (rS_tr L M r j n (x (n + 1))).symm.trans (congrArg ((L.rS M r n).pull j) (hx n))
  exact exu (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l (unit_B L) (fun n => (L.rS M r n).pull j (x n))
    (2 * k) z hz k h2

theorem add (r j : ℕ) (x y : Y.Fam M r j) (w w' : HG (L.QB M) r j) (h : L.Rho x w) (h' : L.Rho y w') : L.Rho (x + y) (w + w') := by
  obtain ⟨e, z, h1, h2⟩ := add_abs (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l
    (fun n => (L.rS M r n).pull j (x n)) (fun n => (L.rS M r n).pull j (y n)) w w' h h'
  exact ⟨e, z, fun n => (h1 n).trans (congrArg _ (map_add ((L.rS M r n).pull j) (x n) (y n)).symm), h2⟩

theorem smul (r j : ℕ) (c : Y.Λ) (x : Y.Fam M r j) (w : HG (L.QB M) r j) (h : L.Rho x w) : L.Rho (c • x) (L.ι (L.lam c) • w) := by
  obtain ⟨e, z, h1, h2⟩ := smul_abs (L.bG M r j) (fun n => redG' (L.QA M) ((l : L.A) ^ n) r j) l
    (fun n => (L.rS M r n).pull j (x n)) w (L.lam c) h
  exact ⟨e, z, fun n => (h1 n).trans (congrArg _ (LinearMap.map_smulₛₗ ((L.rS M r n).pull j) c (x n)).symm), h2⟩

end RhoA

theorem rhoEx {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} [FiniteDimensional ℚ_[l] K] : RhoEx l K := by
  exact ⟨fun L M => RhoA.ex L M, fun L M => RhoA.add L M, fun L M => RhoA.smul L M⟩

end CrystallineSemistableComparison.HT
