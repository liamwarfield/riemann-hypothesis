module

public import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.UnipBEqUnipotent
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.SubquotientBounds.LeOfSubsingletonSubQuot
public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.UnitarisableHypotheses.NormEqOneOfUnitarisable

@[expose] public section

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.PositiveProducts.PosProdOf
section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.PositiveProducts.NontrivialOfNeBot
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.Pos

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem dpow_sc (m : ℕ) (s : ℝ) (x : kˣ) :
    ((dpow m s (sc m x) : ℂˣ) : ℂ) = ((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) := by
  have hd : Matrix.GeneralLinearGroup.det (sc m x) = x ^ m := by
    ext; simp [sc, Matrix.GeneralLinearGroup.scalar]
  have hn : nabs k (x ^ m) = nabs k x ^ m := by simp [nabs]
  rw [dpow, detChar_apply, val_absPow_ofReal, hd, hn, ← Real.rpow_natCast_mul (nabs_pos' k x).le]

theorem tw_eig {m : ℕ} (A : GRep k m) (s : ℝ) (x : kˣ) (v : A.V) :
    (A.tw s).ρ (sc m x) v = ((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) • A.ρ (sc m x) v := by
  show ((dpow m s (sc m x) : ℂˣ) : ℂ) • A.ρ (sc m x) v = _
  rw [dpow_sc]

theorem untw {m : ℕ} (A : GRep k m) (s : ℝ) (x : kˣ) (c : ℂ) (v : A.V) (h : (A.tw s).ρ (sc m x) v = c • v) :
    A.ρ (sc m x) v = (c * ((nabs k x ^ (-((m : ℝ) * s)) : ℝ) : ℂ)) • v := by
  rw [tw_eig] at h
  calc A.ρ (sc m x) v = ((nabs k x ^ (-((m : ℝ) * s)) : ℝ) : ℂ) • ((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) •
        A.ρ (sc m x) v := by
        rw [smul_smul, ← Complex.ofReal_mul, ← Real.rpow_add (nabs_pos' k x), neg_add_cancel, Real.rpow_zero,
          Complex.ofReal_one, one_smul]
    _ = _ := by rw [h, smul_smul, mul_comm]

theorem retw {m : ℕ} (A : GRep k m) (s : ℝ) (x : kˣ) (c : ℂ) (v : A.V) (h : A.ρ (sc m x) v = c • v) :
    (A.tw s).ρ (sc m x) v = (((nabs k x ^ ((m : ℝ) * s) : ℝ) : ℂ) * c) • v := by
  rw [tw_eig, h, smul_smul]

theorem isSmooth_tw {m : ℕ} {A : GRep k m} (h : IsSmooth A.ρ) (s : ℝ) : IsSmooth (A.tw s).ρ :=
  isSmooth_twist h (IsSmoothChar.detChar (isSmoothChar_absPow (k := k) _))

theorem lfin_tw {m : ℕ} {A : GRep k m} (h : LFin A) (s : ℝ) : LFin (A.tw s) := by
  intro a
  obtain ⟨U, hU, ha, hst⟩ := h a
  refine ⟨U, hU, ha, fun x u hu => ?_⟩
  exact U.smul_mem ((dpow m s (sc m x) : ℂˣ) : ℂ) (hst x u hu)

theorem isSmooth_derivB (ψ : AddChar k Circle) : ∀ (j : ℕ) {n : ℕ} (π : GRep k (n + j)), IsSmooth π.ρ →
    IsSmooth (derivB ψ j π).ρ
  | 0, _, _, h => h
  | j + 1, _, _, h => GlobalTheory.CompanionTheory.BZCuspPair.isSmooth_deriv ψ j h

theorem isAdm_cast {a b : ℕ} (h : a = b) {π : GRep k a} (hπ : IsAdmissible π.ρ) : IsAdmissible (π.cast h).ρ := by
  subst h; exact hπ

theorem irr_cast {a b : ℕ} (h : a = b) {π : GRep k a} (hπ : π.ρ.IsIrreducible) : (π.cast h).ρ.IsIrreducible := by
  subst h; exact hπ

theorem unit_cast {a b : ℕ} (h : a = b) {π : GRep k a} (hπ : IsUnitarisable π.ρ) : IsUnitarisable (π.cast h).ρ := by
  subst h; exact hπ

theorem cast_cast {a b c : ℕ} (h : a = b) (h' : b = c) (π : GRep k a) : (π.cast h).cast h' = π.cast (h.trans h') := by
  subst h; subst h'; rfl

theorem eig_cast {a b : ℕ} (h : a = b) (π : GRep k a) (x : kˣ) (c : ℂ) (v : (π.cast h).V) (hv0 : v ≠ 0)
    (hv : (π.cast h).ρ (sc b x) v = c • v) : ∃ w : π.V, w ≠ 0 ∧ π.ρ (sc a x) w = c • w := by
  subst h; exact ⟨v, hv0, hv⟩

theorem adm {n : ℕ} (π : GRep k n) (hs : IsSmooth π.ρ) (hi : π.ρ.IsIrreducible) : IsAdmissible π.ρ :=
  PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top k n π.V π.ρ hs hi

theorem norm_eig_of_unit {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (hu : IsUnitarisable ρ) {g : G} {c : ℂ} {v : V} (hv : v ≠ 0) (h : ρ g v = c • v) : ‖c‖ = 1 := by
  obtain ⟨B, -, hpos, hinv⟩ := hu
  have h1 := hinv g v v
  simp only [h, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul] at h1
  have hB : B v v ≠ 0 := fun h0 => by have := hpos v hv; rw [h0] at this; simp at this
  have h2 : c * (starRingEnd ℂ) c = 1 := by
    apply mul_right_cancel₀ hB
    linear_combination h1
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖c‖ ^ 2 = 1 := by exact_mod_cast h2
  have h4 := norm_nonneg c
  nlinarith

theorem nontrivial_of_ne_bot {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (W : Subrepresentation ρ) (hW : W ≠ ⊥) : Nontrivial W.toSubmodule := by
  by_contra hn
  rw [not_nontrivial_iff_subsingleton] at hn
  apply hW
  apply Subrepresentation.ext
  rw [Submodule.eq_bot_of_subsingleton (p := W.toSubmodule)]
  rfl

theorem subquot_sub {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
    (W : Subrepresentation ρ) : IsSubquotient W.toRepresentation ρ :=
  ⟨W, Representation.IntertwiningMap.id _, Function.surjective_id⟩

theorem pipe (hL : GlobalTheory.RgGu.Leib.LeibnizOrd k) (hLF : LFDeriv k) (hE : EigProd k) (hF : EigFilt k)
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {r t : ℕ} (π₁ : GRep k r) (π₂ : GRep k t)
    (hs₁ : IsSmooth π₁.ρ) (ha₁ : IsAdmissible π₁.ρ) (hs₂ : IsSmooth π₂.ρ) (ha₂ : IsAdmissible π₂.ρ)
    (ℓ n : ℕ) (e : r + t = n + ℓ) (x : kˣ) (c : ℂ) (v : (derivB ψ ℓ ((π₁.prod π₂).cast e)).V) (hv0 : v ≠ 0)
    (hv : (derivB ψ ℓ ((π₁.prod π₂).cast e)).ρ (sc n x) v = c • v) :
    ∃ (i : ℕ) (h : i ≤ r ∧ ℓ - i ≤ t) (cA cB : ℂ), i ≤ ℓ ∧ c = cA * cB ∧
      (∃ a : ((derivB ψ i (π₁.cast (Nat.sub_add_cancel h.1).symm)).tw (((ℓ - i : ℕ) : ℝ) / 2)).V, a ≠ 0 ∧
        ((derivB ψ i (π₁.cast (Nat.sub_add_cancel h.1).symm)).tw (((ℓ - i : ℕ) : ℝ) / 2)).ρ (sc (r - i) x) a =
          cA • a) ∧
      ∃ b : ((derivB ψ (ℓ - i) (π₂.cast (Nat.sub_add_cancel h.2).symm)).tw ((i : ℝ) / 2)).V, b ≠ 0 ∧
        ((derivB ψ (ℓ - i) (π₂.cast (Nat.sub_add_cancel h.2).symm)).tw ((i : ℝ) / 2)).ρ (sc (t - (ℓ - i)) x) b =
          cB • b := by
  obtain ⟨F, hanti, h0, hbot, hpieces⟩ := hL ψ hc h1 r t ℓ n e π₁ π₂ hs₁ hs₂
  obtain ⟨i, hi, w, hw0, hw⟩ := hF n _ (derivB ψ ℓ ((π₁.prod π₂).cast e)).ρ ℓ F hanti h0 hbot x c v hv0 hv
  have hp := hpieces i hi
  split_ifs at hp with h
  · obtain ⟨hsz, ⟨eq⟩⟩ := hp
    have hw' := GlobalTheory.CompanionTheory.LeibOrd.eint eq (sc n x) w
    rw [hw, map_smul] at hw'
    have hw0' : eq w ≠ 0 := fun h0' =>
      hw0 (eq.toLinearEquiv.injective ((show eq.toLinearEquiv w = 0 from h0').trans (map_zero _).symm))
    obtain ⟨f, hf0, hf⟩ := eig_cast hsz _ x c _ hw0' hw'.symm
    have hsA := isSmooth_tw (isSmooth_derivB ψ i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast
      (Nat.sub_add_cancel h.1).symm hs₁)) (((ℓ - i : ℕ) : ℝ) / 2)
    have hsB := isSmooth_tw (isSmooth_derivB ψ (ℓ - i) _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast
      (Nat.sub_add_cancel h.2).symm hs₂)) ((i : ℝ) / 2)
    have hlA := lfin_tw (hLF ψ hc (r - i) i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast (Nat.sub_add_cancel h.1).symm hs₁)
      (isAdm_cast (Nat.sub_add_cancel h.1).symm ha₁)) (((ℓ - i : ℕ) : ℝ) / 2)
    have hlB := lfin_tw (hLF ψ hc (t - (ℓ - i)) (ℓ - i) _
      (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast (Nat.sub_add_cancel h.2).symm hs₂)
      (isAdm_cast (Nat.sub_add_cancel h.2).symm ha₂)) ((i : ℝ) / 2)
    obtain ⟨cA, cB, hcc, ⟨a, ha0, hea⟩, b, hb0, heb⟩ := hE _ _ _ _ hsA hsB hlA hlB x c f hf0 hf
    exact ⟨i, h, cA, cB, hi, hcc, ⟨a, ha0, hea⟩, b, hb0, heb⟩
  · exfalso
    obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    apply hw0
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    show u.1 ∈ (F (i + 1)).toSubmodule
    rw [← hp]
    exact u.2

end PositivityTheory.RgUd.Prod.Pos
end
end

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.Pos

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem norm_untw (X : ℝ) (hX0 : 0 < X) (y : ℝ) (c : ℂ) : ‖c * ((X ^ (-y) : ℝ) : ℂ)‖ * X ^ y = ‖c‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hX0 _), mul_assoc,
    ← Real.rpow_add hX0, neg_add_cancel, Real.rpow_zero, mul_one]

theorem norm_combo (X : ℝ) (hX0 : 0 < X) (p y u : ℝ) (c : ℂ) (hsum : p + -y + u = 0) :
    ‖((X ^ p : ℝ) : ℂ) * (c * ((X ^ (-y) : ℝ) : ℂ))‖ * X ^ u = ‖c‖ := by
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hX0 _), abs_of_pos (Real.rpow_pos_of_pos hX0 _),
    show X ^ p * (‖c‖ * X ^ (-y)) * X ^ u = ‖c‖ * (X ^ p * X ^ (-y) * X ^ u) by ring,
    ← Real.rpow_add hX0, ← Real.rpow_add hX0, hsum, Real.rpow_zero, mul_one]

theorem fac_bound (hT : DerivTop k) (hP : DerivPos k) (hC : CentralSub k) (hLF : LFDeriv k)
    (ψ : AddChar k Circle) (hc : Continuous ψ) (h1 : ψ ≠ 1) {r : ℕ} (π : GRep k r) (hs : IsSmooth π.ρ)
    (hirr : π.ρ.IsIrreducible) (hu : IsUnitarisable π.ρ) (ha : IsAdmissible π.ρ) (i : ℕ) (hi : i ≤ r) (s : ℝ)
    (x : kˣ) (hx : nabs k x < 1) (cA : ℂ)
    (a : ((derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)).tw s).V) (ha0 : a ≠ 0)
    (hea : ((derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)).tw s).ρ (sc (r - i) x) a = cA • a) :
    ‖cA‖ ≤ nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) ∧
    (‖cA‖ = nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) →
      ∀ (n' h' : ℕ) (e : r = n' + h'), i < h' → Subsingleton (derivB ψ h' (π.cast e)).V) := by
  have hX0 : 0 < nabs k x := nabs_pos' k x
  have hd := untw (derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)) s x cA a hea
  have hm0 : (0 : ℝ) ≤ ((r - i : ℕ) : ℝ) := Nat.cast_nonneg _
  rcases Nat.eq_zero_or_pos i with rfl | hi1
  · have hu' : IsUnitarisable (derivB ψ 0 (π.cast (Nat.sub_add_cancel hi).symm)).ρ :=
      unit_cast (Nat.sub_add_cancel hi).symm hu
    have h1' := norm_eig_of_unit hu' ha0 hd
    have hcA : ‖cA‖ = nabs k x ^ (((r - 0 : ℕ) : ℝ) * s) := by
      rw [← norm_untw _ hX0 (((r - 0 : ℕ) : ℝ) * s) cA, h1', one_mul]
    have hle : ((r - 0 : ℕ) : ℝ) * (s + (((0 : ℕ) : ℝ) - 1) / 2) ≤ ((r - 0 : ℕ) : ℝ) * s := by
      simp only [Nat.cast_zero]; nlinarith
    refine ⟨hcA ▸ Real.rpow_le_rpow_of_exponent_ge hX0 hx.le hle, fun heq n' h' e hlt => ?_⟩
    exfalso
    have hr : r = 0 := by
      by_contra hr
      have hmpos : (0 : ℝ) < ((r - 0 : ℕ) : ℝ) := Nat.cast_pos.2 (by omega)
      have hlt2 : ((r - 0 : ℕ) : ℝ) * (s + (((0 : ℕ) : ℝ) - 1) / 2) < ((r - 0 : ℕ) : ℝ) * s := by
        simp only [Nat.cast_zero]; nlinarith
      have := Real.rpow_lt_rpow_of_exponent_gt hX0 hx hlt2
      rw [← hcA, ← heq] at this
      exact lt_irrefl _ this
    omega
  · have hd' := retw (derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)) ((1 - (i : ℝ)) / 2) x _ a hd
    have key := norm_combo (nabs k x) hX0 (((r - i : ℕ) : ℝ) * ((1 - (i : ℝ)) / 2)) (((r - i : ℕ) : ℝ) * s)
      (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) cA (by ring)
    have hT0 : 0 < nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) := Real.rpow_pos_of_pos hX0 _
    by_cases htop : ∃ (n' h' : ℕ) (e : (r - i) + i = n' + h'), i < h' ∧
        Nontrivial (derivB ψ h' ((π.cast (Nat.sub_add_cancel hi).symm).cast e)).V
    · have hsD := isSmooth_tw (isSmooth_derivB ψ i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast
        (Nat.sub_add_cancel hi).symm hs)) ((1 - (i : ℝ)) / 2)
      have hlD := lfin_tw (hLF ψ hc (r - i) i _ (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast (Nat.sub_add_cancel hi).symm hs)
        (isAdm_cast (Nat.sub_add_cancel hi).symm ha)) ((1 - (i : ℝ)) / 2)
      obtain ⟨W, ω, hW, hcc, hωx⟩ := hC (r - i) _ hsD hlD x _ a ha0 hd'
      have hlt := hP ψ hc h1 (r - i) i (π.cast (Nat.sub_add_cancel hi).symm) hi1
        (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ hs) (irr_cast _ hirr) (unit_cast _ hu) htop
        W.toSubmodule W.toRepresentation ω (nontrivial_of_ne_bot W hW) (subquot_sub W) hcc x hx
      rw [hωx] at hlt
      have hlt2 : ‖cA‖ < nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) := by
        rw [← key]
        nlinarith [norm_nonneg (((nabs k x ^ (((r - i : ℕ) : ℝ) * ((1 - (i : ℝ)) / 2)) : ℝ) : ℂ) *
          (cA * ((nabs k x ^ (-(((r - i : ℕ) : ℝ) * s)) : ℝ) : ℂ)))]
      exact ⟨hlt2.le, fun heq => absurd heq hlt2.ne⟩
    · have hnt : Nontrivial (derivB ψ i (π.cast (Nat.sub_add_cancel hi).symm)).V := ⟨⟨a, 0, ha0⟩⟩
      have htop' : ∀ (n' h' : ℕ) (e : (r - i) + i = n' + h'), i < h' →
          Subsingleton (derivB ψ h' ((π.cast (Nat.sub_add_cancel hi).symm).cast e)).V :=
        fun n' h' e hlt => not_nontrivial_iff_subsingleton.1 (fun hn => htop ⟨n', h', e, hlt, hn⟩)
      obtain ⟨-, hun⟩ := hT ψ hc h1 (r - i) i (π.cast (Nat.sub_add_cancel hi).symm) hi1
        (GlobalTheory.CompanionTheory.LeibOrd.Main.isSmooth_gcast _ hs) (irr_cast _ hirr) (unit_cast _ hu) hnt htop'
      have h1' := norm_eig_of_unit hun ha0 hd'
      have heq : ‖cA‖ = nabs k x ^ (((r - i : ℕ) : ℝ) * (s + ((i : ℝ) - 1) / 2)) := by
        rw [← key, h1', one_mul]
      refine ⟨heq.le, fun _ n' h' e hlt => ?_⟩
      have := htop' n' h' ((Nat.sub_add_cancel hi).trans e) hlt
      rwa [cast_cast] at this

variable (k)

theorem posProd_of : DerivTop k → DerivPos k → GlobalTheory.RgGu.Leib.LeibnizOrd k → LFDeriv k → CentralSub k → EigProd k →
    EigFilt k → PosProdD k := by
  intro hT hP hL hLF hC hE hF ψ hc h1 r t π₁ π₂ hs₁ hi₁ hu₁ hs₂ hi₂ hu₂ n h e htop n' j e' hj x hx v c hv0 hv
  have ha₁ := adm π₁ hs₁ hi₁
  have ha₂ := adm π₂ hs₂ hi₂
  obtain ⟨i, hi, cA, cB, hil, rfl, ⟨a, ha0, hea⟩, b, hb0, heb⟩ :=
    pipe hL hLF hE hF ψ hc h1 π₁ π₂ hs₁ ha₁ hs₂ ha₂ j n' e' x c v hv0 hv
  obtain ⟨b1, t1⟩ := fac_bound hT hP hC hLF ψ hc h1 π₁ hs₁ hi₁ hu₁ ha₁ i hi.1 _ x hx cA a ha0 hea
  obtain ⟨b2, t2⟩ := fac_bound hT hP hC hLF ψ hc h1 π₂ hs₂ hi₂ hu₂ ha₂ (j - i) hi.2 _ x hx cB b hb0 heb
  have hX0 : 0 < nabs k x := nabs_pos' k x
  have hsz : (r - i) + (t - (j - i)) = n' := by omega
  have hexp : ((r - i : ℕ) : ℝ) * ((((j - i : ℕ) : ℝ) / 2) + ((i : ℝ) - 1) / 2) +
      ((t - (j - i) : ℕ) : ℝ) * (((i : ℝ) / 2) + (((j - i : ℕ) : ℝ) - 1) / 2) = (n' : ℝ) * ((j : ℝ) - 1) / 2 := by
    have h3 : ((r - i : ℕ) : ℝ) + ((t - (j - i) : ℕ) : ℝ) = (n' : ℝ) := by exact_mod_cast hsz
    have h4 : ((j - i : ℕ) : ℝ) = (j : ℝ) - (i : ℝ) := Nat.cast_sub hil
    rw [h4, ← h3]; ring
  rw [← hexp, Real.rpow_add hX0, norm_mul]
  have hB1 := Real.rpow_pos_of_pos hX0 (((r - i : ℕ) : ℝ) * ((((j - i : ℕ) : ℝ) / 2) + ((i : ℝ) - 1) / 2))
  have hB2 := Real.rpow_pos_of_pos hX0 (((t - (j - i) : ℕ) : ℝ) * (((i : ℝ) / 2) + (((j - i : ℕ) : ℝ) - 1) / 2))
  by_contra hge
  have eqA : ‖cA‖ = nabs k x ^ (((r - i : ℕ) : ℝ) * ((((j - i : ℕ) : ℝ) / 2) + ((i : ℝ) - 1) / 2)) := by
    by_contra hne
    exact hge (lt_of_le_of_lt (mul_le_mul_of_nonneg_left b2 (norm_nonneg _))
      (mul_lt_mul_of_pos_right (lt_of_le_of_ne b1 hne) hB2))
  have eqB : ‖cB‖ = nabs k x ^ (((t - (j - i) : ℕ) : ℝ) * (((i : ℝ) / 2) + (((j - i : ℕ) : ℝ) - 1) / 2)) := by
    by_contra hne
    exact hge (lt_of_le_of_lt (mul_le_mul_of_nonneg_right b1 (norm_nonneg _))
      (mul_lt_mul_of_pos_left (lt_of_le_of_ne b2 hne) hB1))
  have top1 := t1 eqA
  have top2 := t2 eqB
  obtain ⟨hnt, -⟩ := htop
  obtain ⟨v', hv'⟩ := @exists_ne _ hnt 0
  have hsc : sc n (1 : kˣ) = 1 := map_one _
  have hv1 : (derivB ψ h ((π₁.prod π₂).cast e)).ρ (sc n 1) v' = (1 : ℂ) • v' := by simp [hsc]
  obtain ⟨i', hi', -, -, hil', -, ⟨a', ha', -⟩, b', hb', -⟩ :=
    pipe hL hLF hE hF ψ hc h1 π₁ π₂ hs₁ ha₁ hs₂ ha₂ h n e 1 1 v' hv' hv1
  by_cases hcase : i < i'
  · exact ha' (@Subsingleton.elim _ (top1 (r - i') i' (Nat.sub_add_cancel hi'.1).symm hcase) a' 0)
  · exact hb' (@Subsingleton.elim _ (top2 (t - (h - i')) (h - i') (Nat.sub_add_cancel hi'.2).symm (by omega)) b' 0)

end PositivityTheory.RgUd.Prod.Pos
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.LeviScalars.EmbScalarMemLevi
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.LF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def bb (n N : ℕ) : Fin N → Bool := fun i => decide (n ≤ (i : ℕ))

theorem bb_eq_true {n N : ℕ} (i : Fin N) : bb n N i = true ↔ n ≤ (i : ℕ) := by
  simp [bb]

theorem bb_eq_false {n N : ℕ} (i : Fin N) : bb n N i = false ↔ (i : ℕ) < n := by
  simp [bb]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem unip_entries {n N : ℕ} {g : GL (Fin N) k}
    (hg : g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)) (i j : Fin N)
    (hij : ¬ ((i : ℕ) < n ∧ n ≤ (j : ℕ))) :
    (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  obtain ⟨hP, hD⟩ := GroundTheory.Automorphic.Parabolic.mem_unipotentRadical.1 hg
  by_cases he : bb n N i = bb n N j
  · exact hD i j he
  · have hji : (j : ℕ) < n ∧ n ≤ (i : ℕ) := by
      by_cases hi : n ≤ (i : ℕ)
      · refine ⟨?_, hi⟩
        by_contra hj
        exact he (((bb_eq_true i).2 hi).trans ((bb_eq_true j).2 (by omega)).symm)
      · exfalso
        by_cases hj : n ≤ (j : ℕ)
        · exact hij ⟨by omega, hj⟩
        · exact he (((bb_eq_false i).2 (by omega)).trans ((bb_eq_false j).2 (by omega)).symm)
    have hlt : bb n N j < bb n N i := by
      rw [(bb_eq_false j).2 hji.1, (bb_eq_true i).2 hji.2]
      decide
    have h0 : (g : Matrix (Fin N) (Fin N) k) i j = 0 := hP hlt
    rw [h0, one_apply_ne (fun e => by rw [e] at hji; omega)]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem unip_le_derUnip {n N : ℕ} :
    GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N) ≤ derUnip k N n := by
  intro g hg
  have hE := unip_entries hg
  refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩,
    (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => hE i j (by omega)⟩
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem derChar_unip {n N : ℕ} (ψ : AddChar k Circle) (u : derUnip k N n)
    (hu : (u : GL (Fin N) k) ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)) :
    derChar k ψ N n u = 1 := by
  have hE := unip_entries hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem sub_mem_twKer {n N : ℕ} (ψ : AddChar k Circle) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (u : GL (Fin N) k)
    (hu : u ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)) (w : V) :
    π u w - w ∈ twKer π (derUnip k N n) (derChar k ψ N n) :=
  Submodule.subset_span ⟨⟨u, unip_le_derUnip hu⟩, w, by rw [derChar_unip ψ _ hu]; simp⟩

def dd (n N : ℕ) (x : kˣ) : Fin N → k := fun i => if (i : ℕ) < n then (x : k) else 1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem emb_scalar {n t N : ℕ} (h : n + t = N) (x : kˣ) :
    ((emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      diagonal (dd n N x) := by
  ext i j
  obtain ⟨a, rfl⟩ := (stdSum h).surjective i
  obtain ⟨b, rfl⟩ := (stdSum h).surjective j
  rcases a with a | a <;> rcases b with b | b
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inl_inl]
    by_cases hab : a = b
    · subst hab
      simp [dd, GeneralLinearGroup.scalar]
    · rw [diagonal_apply_ne _ (fun e => hab (Sum.inl_injective ((stdSum h).injective e)))]
      simp [GeneralLinearGroup.scalar, hab]
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inl_inr,
      diagonal_apply_ne _ (fun e => Sum.inl_ne_inr ((stdSum h).injective e))]
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inr_inl,
      diagonal_apply_ne _ (fun e => Sum.inr_ne_inl ((stdSum h).injective e))]
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inr_inr]
    by_cases hab : a = b
    · subst hab
      simp [dd]
    · rw [diagonal_apply_ne _ (fun e => hab (Sum.inr_injective ((stdSum h).injective e)))]
      simp [hab]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem emb_scalar_mem_levi {n t N : ℕ} (h : n + t = N) (x : kˣ) :
    emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) ∈ GroundTheory.Automorphic.Parabolic.levi k N (bb n N) := by
  rw [GroundTheory.Automorphic.Parabolic.mem_levi]
  intro i j hij
  have hne : i ≠ j := fun e => hij (e ▸ rfl)
  show ((emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) : GL (Fin N) k) :
    Matrix (Fin N) (Fin N) k) i j = 0
  rw [emb_scalar, diagonal_apply_ne _ hne]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem emb_scalar_comm {n t N : ℕ} (h : n + t = N) (x : kˣ) (y : GL (Fin N) k)
    (hy : y ∈ GroundTheory.Automorphic.Parabolic.levi k N (bb n N)) :
    emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) * y =
      y * emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, emb_scalar]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases he : bb n N i = bb n N j
  · have hd : dd n N x i = dd n N x j := by
      by_cases hi : (i : ℕ) < n
      · have hj : (j : ℕ) < n := (bb_eq_false j).1 (he.symm.trans ((bb_eq_false i).2 hi))
        simp [dd, hi, hj]
      · have hj : ¬ (j : ℕ) < n := fun hj =>
          hi ((bb_eq_false i).1 (he.trans ((bb_eq_false j).2 hj)))
        simp [dd, hi, hj]
    rw [hd, mul_comm]
  · have h0 : (y : Matrix (Fin N) (Fin N) k) i j = 0 := GroundTheory.Automorphic.Parabolic.mem_levi.1 hy i j he
    rw [h0, mul_zero, zero_mul]

theorem lfin_of_quot {n t N : ℕ} (h : n + t = N) (ψ : AddChar k Circle) {V X : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (GL (Fin N) k) V)
    (hπ : GlobalTheory.PRep.IsAdmissible π) (ρ : Representation ℂ (GL (Fin n) k) X) (p : V →ₗ[ℂ] X)
    (hp : Function.Surjective p) (hk : twKer π (derUnip k N n) (derChar k ψ N n) ≤ LinearMap.ker p)
    (hi : ∀ g v, p (π (emb₂ k (stdSum h) (g, 1)) v) = ρ g (p v)) (a : X) :
    ∃ U : Submodule ℂ X, FiniteDimensional ℂ U ∧ a ∈ U ∧
      ∀ (x : kˣ), ∀ u ∈ U, ρ (GeneralLinearGroup.scalar (Fin n) x) u ∈ U := by
  obtain ⟨v, rfl⟩ := hp a
  have hF : GroundTheory.Automorphic.IsAdmissible π := (PositivityTheory.rg.gu.whit.isAdmissible_iff π).1 hπ
  have hA := GroundTheory.Automorphic.Parabolic.isAdmissible_jacquetRep (β := bb n N) hF
  let J := GroundTheory.Automorphic.Parabolic.jacquetAction k N (bb n N) π
  have hpu : ∀ u : GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N),
      p ∘ₗ (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)).subtype) u = p := by
    intro u
    refine LinearMap.ext fun w => ?_
    show p (π u w) = p w
    rw [← sub_eq_zero, ← map_sub]
    exact hk (sub_mem_twKer ψ π u u.2 w)
  let pb : GroundTheory.Automorphic.Parabolic.JacquetModule k N (bb n N) π →ₗ[ℂ] X :=
    Representation.Coinvariants.lift _ p hpu
  have hpb : ∀ w, pb (Representation.Coinvariants.mk _ w) = p w := fun w =>
    Representation.Coinvariants.lift_mk _ p hpu w
  let w₀ : GroundTheory.Automorphic.Parabolic.JacquetModule k N (bb n N) π := Representation.Coinvariants.mk _ v
  let KM : ℕ → Subgroup (GroundTheory.Automorphic.Parabolic.levi k N (bb n N)) := fun m =>
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m).subgroupOf (GroundTheory.Automorphic.Parabolic.levi k N (bb n N))
  obtain ⟨m, hm⟩ := GroundTheory.Automorphic.Parabolic.exists_subgroupOf_congruenceSubgroup_subset (F := k) (n := N)
    (β := bb n N) ((hA.1 w₀).mem_nhds (one_mem (GroundTheory.Automorphic.stabilizerOf _ w₀)))
  have hfix : w₀ ∈ GroundTheory.Automorphic.fixedVectors J (KM m) := by
    have : w₀ ∈ GroundTheory.Automorphic.fixedVectors (GroundTheory.Automorphic.Parabolic.jacquetRep k N (bb n N) π) (KM m) :=
      fun x hx => hm hx
    rwa [GroundTheory.Automorphic.Parabolic.fixedVectors_jacquetRep_congruenceSubgroup] at this
  have hfin : FiniteDimensional ℂ (GroundTheory.Automorphic.fixedVectors J (KM m)) := by
    have := hA.2 (KM m)
      (GroundTheory.Automorphic.Parabolic.isCompact_subgroupOf_levi
        (GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k N m))
      (GroundTheory.Automorphic.Parabolic.isOpen_subgroupOf_levi
        (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m))
    rwa [GroundTheory.Automorphic.Parabolic.fixedVectors_jacquetRep_congruenceSubgroup] at this
  refine ⟨(GroundTheory.Automorphic.fixedVectors J (KM m)).map pb, inferInstance, ⟨w₀, hfix, hpb v⟩, ?_⟩
  rintro x _ ⟨y, hy, rfl⟩
  obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  let z : GroundTheory.Automorphic.Parabolic.levi k N (bb n N) :=
    ⟨_, emb_scalar_mem_levi h x⟩
  refine ⟨J z (Representation.Coinvariants.mk _ w), ?_, ?_⟩
  · intro g hg
    have hc : g * z = z * g := Subtype.ext (emb_scalar_comm h x g g.2).symm
    show J g (J z _) = J z _
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    exact congrArg _ (hy g hg)
  · show pb (Representation.Coinvariants.mk _ (π _ w)) = _
    rw [hpb, hpb, hi]

theorem lfin_self {n : ℕ} (A : GRep k n) (hA : GlobalTheory.PRep.IsAdmissible A.ρ) : LFin A := by
  intro v
  have hF : GroundTheory.Automorphic.IsAdmissible A.ρ := (PositivityTheory.rg.gu.whit.isAdmissible_iff A.ρ).1 hA
  have hO : {g : GL (Fin n) k | A.ρ g v = v} ∈ nhds (1 : GL (Fin n) k) :=
    (hA.1 v).mem_nhds (by simp)
  obtain ⟨m, -, hm⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k n).mem_iff.1 hO
  let K := GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k n m
  have hfin : FiniteDimensional ℂ (GroundTheory.Automorphic.fixedVectors A.ρ K) :=
    hF.2 K (GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k n m)
      (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k n m)
  refine ⟨GroundTheory.Automorphic.fixedVectors A.ρ K, hfin, fun g hg => hm hg, ?_⟩
  intro x u hu g hg
  have hc : g * sc n x = sc n x * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (g : Matrix (Fin n) (Fin n) k) * scalar (Fin n) (x : k) = scalar (Fin n) (x : k) * g
    exact ((scalar_commute (x : k) (fun r => Commute.all _ r) (g : Matrix (Fin n) (Fin n) k))).symm.eq
  show A.ρ g (A.ρ (sc n x) u) = A.ρ (sc n x) u
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hu g hg]

variable (k)

theorem lfDeriv : LFDeriv k := by
  intro ψ _ n j π _ hA
  cases j with
  | zero => exact lfin_self π hA
  | succ j =>
    intro a
    obtain ⟨p, hp, hpk, hpi⟩ := GlobalTheory.CompanionTheory.BZMirJac.iterPhi_quotient ψ n j (resM k π.ρ)
    refine lfin_of_quot (rfl : n + (j + 1) = n + j + 1) ψ π.ρ hA (deriv k ψ j π.ρ) p hp ?_ ?_ a
    · intro w hw
      have hw' : w ∈ LinearMap.ker p := by
        rw [hpk, GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM]
        exact hw
      exact hw'
    · intro g v
      rw [← GlobalTheory.CompanionTheory.BZMirJac.iotaM_eq_emb]
      exact hpi g v

end PositivityTheory.RgUd.Prod.LF
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.CentralGenerators.CentralSubGen
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.CS

variable {k : Type} [Field k]

theorem sc_one (n : ℕ) : sc n (1 : kˣ) = 1 := map_one _

theorem sc_mul (n : ℕ) (y z : kˣ) : sc n (y * z) = sc n y * sc n z := map_mul _ _ _

theorem sc_comm (n : ℕ) (y : kˣ) (g : GL (Fin n) k) : sc n y * g = g * sc n y := by
  apply Units.ext
  have h : ((sc n y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = Matrix.scalar (Fin n) (y : k) := rfl
  show ((sc n y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) * (g : Matrix (Fin n) (Fin n) k) =
    (g : Matrix (Fin n) (Fin n) k) * ((sc n y : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)
  rw [h]
  exact (Matrix.scalar_commute (y : k) (fun r => Commute.all _ _) _).eq

theorem rho_sc_comm {n : ℕ} (A : GRep k n) (y : kˣ) (g : GL (Fin n) k) (v : A.V) :
    A.ρ (sc n y) (A.ρ g v) = A.ρ g (A.ρ (sc n y) v) := by
  rw [← Module.End.mul_apply, ← map_mul, sc_comm, map_mul, Module.End.mul_apply]

theorem centralSub_gen [TopologicalSpace k] : CentralSub k := by
  classical
  intro n A _hs hLF x c a ha hxa
  obtain ⟨U, hUf, haU, hUinv⟩ := hLF a
  have := hUf
  let Good : Submodule ℂ A.V → Prop := fun S => S ≤ U ∧ S ≠ ⊥ ∧
    (∀ y : kˣ, ∀ s ∈ S, A.ρ (sc n y) s ∈ S) ∧ ∀ s ∈ S, A.ρ (sc n x) s = c • s
  have hex : ∃ d : ℕ, ∃ S : Submodule ℂ A.V, Good S ∧ Module.finrank ℂ S = d := by
    refine ⟨_, U ⊓ LinearMap.ker (A.ρ (sc n x) - c • LinearMap.id), ⟨inf_le_left, ?_, ?_, ?_⟩, rfl⟩
    · intro h
      apply ha
      have hm : a ∈ U ⊓ LinearMap.ker (A.ρ (sc n x) - c • LinearMap.id) :=
        ⟨haU, by simp [LinearMap.mem_ker, hxa]⟩
      rw [h] at hm
      exact (Submodule.mem_bot ℂ).1 hm
    · rintro y s ⟨hsU, hsk⟩
      refine ⟨hUinv y s hsU, ?_⟩
      have hsk' : A.ρ (sc n x) s = c • s := by
        simpa [LinearMap.mem_ker, sub_eq_zero] using hsk
      show A.ρ (sc n y) s ∈ LinearMap.ker (A.ρ (sc n x) - c • LinearMap.id)
      rw [LinearMap.mem_ker, LinearMap.sub_apply, rho_sc_comm A x (sc n y) s, hsk', map_smul]
      simp
    · rintro s ⟨_, hsk⟩
      simpa [LinearMap.mem_ker, sub_eq_zero] using hsk
  obtain ⟨S, ⟨hSU, hS0, hSinv, hSx⟩, hSd⟩ := Nat.find_spec hex
  have hmin : ∀ S' : Submodule ℂ A.V, Good S' → Module.finrank ℂ S ≤ Module.finrank ℂ S' := by
    intro S' hS'
    rw [hSd]
    exact Nat.find_min' hex ⟨S', hS', rfl⟩
  have : FiniteDimensional ℂ S := Submodule.finiteDimensional_of_le hSU
  have hscal : ∀ y : kˣ, ∃ μ : ℂ, ∀ s ∈ S, A.ρ (sc n y) s = μ • s := by
    intro y
    let f : Module.End ℂ S := (A.ρ (sc n y)).restrict (hSinv y)
    have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
    obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
    obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
    refine ⟨μ, ?_⟩
    have hfw : A.ρ (sc n y) (w : A.V) = μ • (w : A.V) := congrArg Subtype.val hw.apply_eq_smul
    let S' : Submodule ℂ A.V := S ⊓ LinearMap.ker (A.ρ (sc n y) - μ • LinearMap.id)
    have hmem : ∀ s, s ∈ S' ↔ s ∈ S ∧ A.ρ (sc n y) s = μ • s := by
      intro s
      simp [S', Submodule.mem_inf, LinearMap.mem_ker, sub_eq_zero]
    have hgood : Good S' := by
      refine ⟨inf_le_left.trans hSU, ?_, ?_, ?_⟩
      · intro h
        have hw' : (w : A.V) ∈ S' := (hmem _).2 ⟨w.2, hfw⟩
        rw [h] at hw'
        exact hw.2 (Subtype.ext ((Submodule.mem_bot ℂ).1 hw'))
      · intro y' s hs
        obtain ⟨hsS, hsy⟩ := (hmem s).1 hs
        refine (hmem _).2 ⟨hSinv y' s hsS, ?_⟩
        rw [rho_sc_comm A y (sc n y') s, hsy, map_smul]
      · intro s hs
        exact hSx s ((hmem s).1 hs).1
    have hEq : S' = S := Submodule.eq_of_le_of_finrank_le inf_le_left (hmin S' hgood)
    intro s hs
    rw [← hEq] at hs
    exact ((hmem s).1 hs).2
  choose lam hlam using hscal
  obtain ⟨a', ha'S, ha'0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS0
  have key : ∀ μ ν : ℂ, μ • a' = ν • a' → μ = ν := fun μ ν h => smul_left_injective ℂ ha'0 h
  have hlam1 : lam 1 = 1 := by
    apply key
    rw [← hlam 1 a' ha'S, sc_one, map_one, Module.End.one_apply, one_smul]
  have hlammul : ∀ y z : kˣ, lam (y * z) = lam y * lam z := by
    intro y z
    apply key
    rw [← hlam (y * z) a' ha'S, sc_mul, map_mul, Module.End.mul_apply, hlam z a' ha'S, map_smul,
      hlam y a' ha'S, smul_smul, mul_comm]
  let f : kˣ →* ℂ := { toFun := lam, map_one' := hlam1, map_mul' := hlammul }
  let Wm : Submodule ℂ A.V :=
    { carrier := {v | ∀ y : kˣ, A.ρ (sc n y) v = lam y • v}
      add_mem' := by
        intro u v hu hv y
        have hu' : ∀ y : kˣ, A.ρ (sc n y) u = lam y • u := hu
        have hv' : ∀ y : kˣ, A.ρ (sc n y) v = lam y • v := hv
        show A.ρ (sc n y) (u + v) = lam y • (u + v)
        rw [map_add (f := _), hu' y, hv' y, smul_add]
      zero_mem' := by
        intro y
        show A.ρ (sc n y) 0 = lam y • (0 : A.V)
        rw [map_zero, smul_zero]
      smul_mem' := by
        intro r v hv y
        have hv' : ∀ y : kˣ, A.ρ (sc n y) v = lam y • v := hv
        show A.ρ (sc n y) (r • v) = lam y • (r • v)
        rw [map_smul, hv' y, smul_comm] }
  let W : Subrepresentation A.ρ := ⟨Wm, fun g v hv y => by
    have hv' : ∀ y : kˣ, A.ρ (sc n y) v = lam y • v := hv
    show A.ρ (sc n y) (A.ρ g v) = lam y • A.ρ g v
    rw [rho_sc_comm, hv' y, map_smul]⟩
  have ha'W : a' ∈ W.toSubmodule := fun y => hlam y a' ha'S
  refine ⟨W, f.toHomUnits, ?_, ?_, ?_⟩
  · intro h
    apply ha'0
    have h2 : W.toSubmodule = (⊥ : Subrepresentation A.ρ).toSubmodule := congrArg _ h
    have h3 : a' ∈ (⊥ : Subrepresentation A.ρ).toSubmodule := h2 ▸ ha'W
    exact (Submodule.mem_bot ℂ).1 h3
  · intro z v
    apply Subtype.ext
    show A.ρ (sc n z) v.1 = ((f.toHomUnits z : ℂˣ) : ℂ) • v.1
    rw [MonoidHom.coe_toHomUnits]
    exact v.2 z
  · show ((f.toHomUnits x : ℂˣ) : ℂ) = c
    rw [MonoidHom.coe_toHomUnits]
    exact (key _ _ ((hlam x a' ha'S).symm.trans (hSx a' ha'S))).trans rfl

theorem centralSub (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CentralSub k :=
  centralSub_gen

end PositivityTheory.RgUd.Prod.CS
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.EigenInjectivity.SubInjective
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir.Leib
open scoped TensorProduct

namespace PositivityTheory.RgUd.Prod.Eig

section Lin

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem sub_injective (f : Module.End ℂ V) (α : ℂ) (h : ∀ a : V, f a = α • a → a = 0) :
    Function.Injective (f - α • (LinearMap.id : V →ₗ[ℂ] V)) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => h a ?_
  simpa [sub_eq_zero] using ha

theorem exists_fin (S : Module.End ℂ V) (T : Module.End ℂ W)
    (hA : ∀ a : V, ∃ U : Submodule ℂ V, FiniteDimensional ℂ U ∧ a ∈ U ∧ ∀ u ∈ U, S u ∈ U)
    (hB : ∀ b : W, ∃ U : Submodule ℂ W, FiniteDimensional ℂ U ∧ b ∈ U ∧ ∀ u ∈ U, T u ∈ U)
    (y : V ⊗[ℂ] W) : ∃ (U₁ : Submodule ℂ V) (U₂ : Submodule ℂ W), FiniteDimensional ℂ U₁ ∧
      FiniteDimensional ℂ U₂ ∧ (∀ u ∈ U₁, S u ∈ U₁) ∧ (∀ u ∈ U₂, T u ∈ U₂) ∧
      y ∈ LinearMap.range (TensorProduct.map U₁.subtype U₂.subtype) := by
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨⊥, ⊥, inferInstance, inferInstance, by simp, by simp, zero_mem _⟩
  | tmul a b =>
    obtain ⟨U₁, h₁, ha, s₁⟩ := hA a
    obtain ⟨U₂, h₂, hb, s₂⟩ := hB b
    exact ⟨U₁, U₂, h₁, h₂, s₁, s₂, ⟨⟨a, ha⟩ ⊗ₜ ⟨b, hb⟩, by simp⟩⟩
  | add y z hy hz =>
    obtain ⟨U₁, U₂, h₁, h₂, s₁, s₂, my⟩ := hy
    obtain ⟨U₁', U₂', h₁', h₂', s₁', s₂', mz⟩ := hz
    have st : ∀ {M : Type} [AddCommGroup M] [Module ℂ M] (F : Module.End ℂ M) (P Q : Submodule ℂ M),
        (∀ u ∈ P, F u ∈ P) → (∀ u ∈ Q, F u ∈ Q) → ∀ u ∈ P ⊔ Q, F u ∈ P ⊔ Q := by
      intro M _ _ F P Q hP hQ u hu
      obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.1 hu
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hP p hp) (hQ q hq)
    have mono : ∀ (P P' : Submodule ℂ V) (Q Q' : Submodule ℂ W), P ≤ P' → Q ≤ Q' →
        LinearMap.range (TensorProduct.map P.subtype Q.subtype) ≤
          LinearMap.range (TensorProduct.map P'.subtype Q'.subtype) := by
      intro P P' Q Q' hP hQ
      have : TensorProduct.map P.subtype Q.subtype =
          TensorProduct.map P'.subtype Q'.subtype ∘ₗ
            TensorProduct.map (Submodule.inclusion hP) (Submodule.inclusion hQ) := by
        rw [← TensorProduct.map_comp]; rfl
      rw [this]
      exact LinearMap.range_comp_le_range _ _
    exact ⟨U₁ ⊔ U₁', U₂ ⊔ U₂', inferInstance, inferInstance, st S _ _ s₁ s₁', st T _ _ s₂ s₂',
      add_mem (mono _ _ _ _ le_sup_left le_sup_left my) (mono _ _ _ _ le_sup_right le_sup_right mz)⟩

theorem tensor_eig (S : Module.End ℂ V) (T : Module.End ℂ W) (hS : Function.Injective S)
    (U₁ : Submodule ℂ V) (U₂ : Submodule ℂ W) [FiniteDimensional ℂ U₁] [FiniteDimensional ℂ U₂]
    (h₁ : ∀ u ∈ U₁, S u ∈ U₁)
    (y : V ⊗[ℂ] W) (hy : y ∈ LinearMap.range (TensorProduct.map U₁.subtype U₂.subtype))
    (hy0 : y ≠ 0) (c : ℂ) (hc : TensorProduct.map S T y = c • y) :
    ∃ α β : ℂ, c = α * β ∧ (∃ a : V, a ≠ 0 ∧ S a = α • a) ∧ ∃ b : W, b ≠ 0 ∧ T b = β • b := by
  set R := LinearMap.range (TensorProduct.map U₁.subtype U₂.subtype) with hR
  set S' := LinearMap.rTensor W S with hS'
  set T' := LinearMap.lTensor V T with hT'
  set P := TensorProduct.map S T with hP
  have hPST : ∀ z, P z = S' (T' z) := fun z => by
    rw [hP, hS', hT', ← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor]
  have hPS : ∀ z, P (S' z) = S' (P z) := fun z => by
    have : P ∘ₗ S' = S' ∘ₗ P := TensorProduct.ext' fun a b => by simp [hP, hS']
    exact LinearMap.congr_fun this z
  have hRS : ∀ z ∈ R, S' z ∈ R := by
    rintro _ ⟨z, rfl⟩
    refine ⟨TensorProduct.map (S.restrict h₁) LinearMap.id z, ?_⟩
    have : TensorProduct.map U₁.subtype U₂.subtype ∘ₗ TensorProduct.map (S.restrict h₁) LinearMap.id =
        S' ∘ₗ TensorProduct.map U₁.subtype U₂.subtype :=
      TensorProduct.ext' fun a b => by simp [hS', LinearMap.restrict_apply]
    exact LinearMap.congr_fun this z
  let E : Submodule ℂ (V ⊗[ℂ] W) := R ⊓ LinearMap.ker (P - c • LinearMap.id)
  have memE : ∀ z, z ∈ E ↔ z ∈ R ∧ P z = c • z := fun z => by
    simp [E, sub_eq_zero]
  have hES : ∀ z ∈ E, S' z ∈ E := fun z hz => by
    rw [memE] at hz ⊢
    exact ⟨hRS z hz.1, by rw [hPS, hz.2, map_smul]⟩
  have : FiniteDimensional ℂ R := LinearMap.finiteDimensional_range _
  have : FiniteDimensional ℂ E := Submodule.finiteDimensional_of_le inf_le_left
  have hyE : y ∈ E := (memE y).2 ⟨hy, hc⟩
  have : Nontrivial E := ⟨⟨⟨y, hyE⟩, 0, fun h => hy0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨α, hα⟩ := Module.End.exists_eigenvalue (S'.restrict hES)
  obtain ⟨v, hv⟩ := hα.exists_hasEigenvector
  have hv1 : S' v.1 = α • v.1 := by
    have := Module.End.mem_eigenspace_iff.1 hv.1
    exact congrArg Subtype.val this
  have hv0 : v.1 ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hv2 : P v.1 = c • v.1 := ((memE _).1 v.2).2
  have hS'inj : Function.Injective S' := Module.Flat.rTensor_preserves_injective_linearMap S hS
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact hv0 (hS'inj (by rw [hv1, zero_smul, map_zero]))
  have hT1 : T' v.1 = (c / α) • v.1 := by
    apply hS'inj
    rw [← hPST, hv2, map_smul, hv1, smul_smul, div_mul_cancel₀ _ hα0]
  refine ⟨α, c / α, (mul_div_cancel₀ _ hα0).symm, ?_, ?_⟩
  · by_contra hno
    push Not at hno
    have hinj := sub_injective S α fun a ha => by
      by_contra h0; exact hno a h0 ha
    have h3 := Module.Flat.rTensor_preserves_injective_linearMap (M := W) _ hinj
    have h4 : LinearMap.rTensor W (S - α • LinearMap.id) v.1 = 0 := by
      rw [LinearMap.rTensor_sub, LinearMap.rTensor_smul, LinearMap.rTensor_id, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, ← hS', hv1, sub_self]
    exact hv0 (h3 (by rw [h4, map_zero]))
  · by_contra hno
    push Not at hno
    have hinj := sub_injective T (c / α) fun b hb => by
      by_contra h0; exact hno b h0 hb
    have h3 := Module.Flat.lTensor_preserves_injective_linearMap (M := V) _ hinj
    have h4 : LinearMap.lTensor V (T - (c / α) • LinearMap.id) v.1 = 0 := by
      rw [LinearMap.lTensor_sub, LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.sub_apply,
        LinearMap.smul_apply, LinearMap.id_apply, ← hT', hT1, sub_self]
    exact hv0 (h3 (by rw [h4, map_zero]))

end Lin

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem eigProd : EigProd k := by
  intro r t A B _ _ hA hB x c f hf hfc
  have hinj : ∀ {n : ℕ} (C : GRep k n), Function.Injective (C.ρ (sc n x)) := fun {n} C => by
    refine Function.LeftInverse.injective (g := C.ρ (sc n x⁻¹)) fun a => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]
  have h1 : leviEmb k (two (stdSum (rfl : r + t = r + t)))
      (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) = sc (r + t) x := by
    ext i j
    obtain ⟨⟨b, y⟩, rfl⟩ := (two (stdSum (rfl : r + t = r + t))).surjective i
    obtain ⟨⟨b', y'⟩, rfl⟩ := (two (stdSum (rfl : r + t = r + t))).surjective j
    by_cases hb : b = b'
    · subst hb
      simp only [leviEmb, blockDiagonal'_apply_eq, Equiv.symm_apply_apply, Matrix.reindex_apply, Matrix.submatrix_apply, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk]
      simp [GeneralLinearGroup.scalar, diagonal_apply]
    · simp only [leviEmb, blockDiagonal'_apply, Equiv.symm_apply_apply, Matrix.reindex_apply, Matrix.submatrix_apply, MonoidHom.coe_toHomUnits, MonoidHom.coe_mk, OneHom.coe_mk, hb, ↓reduceDIte]
      simp [hb]
  obtain ⟨g, hg⟩ : ∃ g, f.1.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (Subtype.ext (Subtype.ext (funext h)))
  have hc : f.1.1 (g * sc (r + t) x) = c • f.1.1 g := congrArg (fun F : (A.prod B).V => F.1.1 g) hfc
  have hcomm : g * sc (r + t) x = sc (r + t) x * g := by
    ext i j
    simp [mul_comm]
  let e := two (stdSum (rfl : r + t = r + t))
  let d : Levi k (Two (Fin r) (Fin t)) := fun a => GeneralLinearGroup.scalar _ x
  have hp : leviEmb k e d ∈ parab k e := by
    apply mem_parab_iff.2
    intro a b i j hab
    simp [leviEmb, blockDiagonal'_apply, hab.ne']
  have hproj : leviProj k e ⟨leviEmb k e d, hp⟩ = d := by
    funext a
    ext i j
    simp [leviProj_apply, leviEmb, blockDiagonal'_apply_eq]
  have h5 := parInd_law e (piTensor (twoRep A.ρ B.ρ)) f ⟨leviEmb k e d, hp⟩ g
  rw [hproj, GlobalTheory.CentralSupport.deltaHalf_scalar] at h5
  have h6 : piTensor (twoRep A.ρ B.ρ) (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) (f.1.1 g) =
      c • f.1.1 g := by
    have h7 : f.1.1 (leviEmb k (two (stdSum (rfl : r + t = r + t)))
        (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) * g) = c • f.1.1 g := by
      rw [h1, ← hcomm]; exact hc
    rw [h5] at h7
    simpa using h7
  have htr : ∀ z, Exponents.boolTensorEquiv (X := TwoT A.V B.V)
      (piTensor (twoRep A.ρ B.ρ) (fun a => GeneralLinearGroup.scalar (Two (Fin r) (Fin t) a) x) z) =
      TensorProduct.map (A.ρ (sc r x)) (B.ρ (sc t x)) (Exponents.boolTensorEquiv (X := TwoT A.V B.V) z) := by
    intro z
    induction z using PiTensorProduct.induction_on with
    | add z w hz hw => rw [map_add (f := _), map_add (f := _), hz, hw, map_add (f := _), map_add (f := _)]
    | smul_tprod s z =>
      rw [map_smul, map_smul, map_smul, map_smul, piTensor_tprod, Exponents.boolTensorEquiv_tprod,
        Exponents.boolTensorEquiv_tprod, TensorProduct.map_tmul]
      rfl
  set y := Exponents.boolTensorEquiv (X := TwoT A.V B.V) (f.1.1 g) with hy
  have hy0 : y ≠ 0 := by
    rw [hy]; exact (LinearEquiv.map_ne_zero_iff _).2 hg
  have hyc : TensorProduct.map (A.ρ (sc r x)) (B.ρ (sc t x)) y = c • y := by
    rw [hy, ← htr, h6, map_smul]
  obtain ⟨U₁, U₂, fd₁, fd₂, s₁, -, hmem⟩ := exists_fin (A.ρ (sc r x)) (B.ρ (sc t x))
    (fun a => by obtain ⟨U, h, ha, hs⟩ := hA a; exact ⟨U, h, ha, fun u hu => hs x u hu⟩)
    (fun b => by obtain ⟨U, h, hb, hs⟩ := hB b; exact ⟨U, h, hb, fun u hu => hs x u hu⟩) y
  exact tensor_eig _ _ (hinj A) U₁ U₂ s₁ y hmem hy0 c hyc


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem eigFilt : EigFilt k := by
  intro n V _ _ ρ ℓ F hF h0 hℓ x c v hv hvc
  classical
  have hex : ∃ j, v ∉ (F (j + 1)).toSubmodule := ⟨ℓ, by
    rw [hℓ]
    intro h
    exact hv ((Submodule.mem_bot ℂ).1 h)⟩
  set j := Nat.find hex with hjdef
  have hj : v ∉ (F (j + 1)).toSubmodule := Nat.find_spec hex
  have hvj : v ∈ (F j).toSubmodule := by
    rcases hjj : j with _ | j'
    · rw [h0]; exact Submodule.mem_top
    · have := Nat.find_min hex (show j' < Nat.find hex by omega)
      push Not at this
      exact this
  refine ⟨j, Nat.find_min' hex (show v ∉ (F (ℓ + 1)).toSubmodule from ?_), ?_⟩
  · rw [hℓ]; intro h; exact hv ((Submodule.mem_bot ℂ).1 h)
  refine ⟨Submodule.Quotient.mk ⟨v, hvj⟩, fun h => hj (Submodule.mem_comap.1 ((Submodule.Quotient.mk_eq_zero _).1 h)), ?_⟩
  rw [← Submodule.Quotient.mk_smul]
  show Submodule.Quotient.mk (⟨ρ (sc n x) v, _⟩ : (F j).toSubmodule) = _
  congr 1
  exact Subtype.ext hvc

end PositivityTheory.RgUd.Prod.Eig
end
end

section -- merged from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.CentralSub
namespace PositivityTheory.RgUd.Prod.CSel

theorem centralSub (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CentralSub k := PositivityTheory.RgUd.Prod.CS.centralSub k

end PositivityTheory.RgUd.Prod.CSel
end

noncomputable section

namespace PositivityTheory.RgUd.Prod.Final

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem bern_of (hT : DerivTop k) (hP : DerivPos k) (hL : GlobalTheory.RgGu.Leib.LeibnizOrd k) : BernAt k :=
  Asm.bern_of_parts k hT
    (Pos.posProd_of k hT hP hL (LF.lfDeriv k) (CSel.centralSub k) (Eig.eigProd k) (Eig.eigFilt k))
    (Pos2.topProd_of k hT hP hL (LF.lfDeriv k) (CSel.centralSub k) (Eig.eigProd k) (Eig.eigFilt k))

end PositivityTheory.RgUd.Prod.Final
