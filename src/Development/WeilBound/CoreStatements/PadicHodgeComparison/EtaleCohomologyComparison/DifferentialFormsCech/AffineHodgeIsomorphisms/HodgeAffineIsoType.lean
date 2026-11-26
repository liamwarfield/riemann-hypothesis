module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.HdgAffIso
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineSmoothFormsBijective
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AffineFormsOfFormUniqueness
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.OmNatB
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.FormUniq

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormOne
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormOne
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.HodgeFormUnit

theorem gForm_one {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) :
    CrystallineSemistableComparison.Om.L2.gForm q 1 Fin.elim0 = oneOm K (Sec q ⊤) := by
  apply Subtype.ext
  simp [CrystallineSemistableComparison.Onto.form, oneOm]

theorem e_oneH {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0) (h : CrystallineSemistableComparison.Om.L2.IsOmT q 0 e) :
    e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤) := by
  let Λ : CrystallineSemistableComparison.Om.L2.LiftsT q :=
    { v := fun T g => Function.surjInv Ideal.Quotient.mk_surjective
        (CrystallineSemistableComparison.Pb.ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (CrystallineSemistableComparison.Om.L2.inTop q T) g)
      hv := fun T g => Function.surjInv_eq _ _ }
  obtain ⟨f, hf, hc, hz⟩ := h 1 Fin.elim0 Λ
  have hf' : f = (CrystallineSemistableComparison.Pb.toSq (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (0 : ℕ)) (CrystallineSemistableComparison.Pb.thFil (CrystallineSemistableComparison.smFun X q) (((0 : ℕ) : ℤ) + 1))
      fun T => T.pdPow_zero).pullC 0 (fun s => (1 : (CrystallineSemistableComparison.Pb.thA (CrystallineSemistableComparison.smFun X q)).obj (s.obj (Fin.last 0)))) := by
    funext s
    apply Subtype.ext
    refine (hz s).trans ?_
    have hv : (Λ.form 1 Fin.elim0 s : (s.obj (Fin.last 0)).B) = Λ.v _ 1 := by
      simp [CrystallineSemistableComparison.Om.L2.LiftsT.form]
    have hJ : Λ.v (s.obj (Fin.last 0)) 1 - 1 ∈ (s.obj (Fin.last 0)).J :=
      Ideal.Quotient.eq.1 ((Λ.hv _ 1).trans ((map_one _).trans (map_one _).symm))
    refine Ideal.Quotient.eq.2 ?_
    change Λ.form 1 Fin.elim0 s - 1 ∈ (s.obj (Fin.last 0)).pdPow 1
    rw [hv]
    exact (s.obj (Fin.last 0)).J_le_pdPow_one hJ
  have h1 : CrystallineSemistableComparison.HT.oneH q = e.symm (CrystallineSemistableComparison.Om.L2.gForm q 1 Fin.elim0) := by
    refine Eq.trans ?_ hc.symm
    exact congrArg Submodule.Quotient.mk (Subtype.ext hf'.symm)
  rw [h1, LinearEquiv.apply_symm_apply, gForm_one]

end GlobalTheory.CompanionTheory.HodgeFormUnit
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormOneStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_form_one : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0),
    CrystallineSemistableComparison.Om.L2.IsOmT q 0 e → e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤) := by
  first | exact @GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | exact GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH | (intros; apply GlobalTheory.CompanionTheory.HodgeFormUnit.e_oneH <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormIsoOfBijective
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormIsoOfBijective
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section

namespace GlobalTheory.CompanionTheory.HodgeFormTop

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2 CrystallineSemistableComparison.Pb

section
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def omEq (a : ℕ) : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a ≃ₗ[K] OmU q ⊤ a := LinearEquiv.refl K (OmU q ⊤ a)

abbrev resTop (a : ℕ) := CH.Mor.restrict (G q a) (inU q ⊤).ι

theorem resTop_pullC_bij (a n : ℕ) : Function.Bijective ((resTop q a).pullC n) :=
  (topRes_pf K _ (G q a) (inU q ⊤) ⊥ (fun T => inTop q T) n).1

theorem resTop_bij (a n : ℕ) : Function.Bijective ((resTop q a).pull n) :=
  CrystallineSemistableComparison.P.mapH_bij _ (fun m => resTop_pullC_bij q a m) n

def resTopEquiv (a : ℕ) : Hdg q a a ≃ₗ[K] HV q ⊤ a a :=
  LinearEquiv.ofBijective ((resTop q a).pull a) (resTop_bij q a a)

def LiftsT.toTop (Λ : LiftsT q) : Lifts q ⊤ where
  v T g := Λ.v T.obj g
  hv T g := Λ.hv T.obj g

theorem isFormT_of_isForm {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (c : HV q ⊤ a a)
    (h : IsForm q ⊤ (a := a) g₀ g c) : IsFormT q g₀ g ((resTopEquiv q a).symm c) := by
  intro Λ
  obtain ⟨f, hf, hc, hz⟩ := h (LiftsT.toTop q Λ)
  obtain ⟨z, rfl⟩ := (resTop_pullC_bij q a a).2 f
  have hd : CH.d (G q a) a z = 0 := by
    apply (resTop_pullC_bij q a (a + 1)).1
    rw [map_zero, ← CH.Mor.d_pullC]
    exact hf
  have hcz : (resTopEquiv q a) ((CH.cx (G q a)).cls z hd) = c := by
    rw [hc]
    exact CrystallineSemistableComparison.P.mapH_cls (resTop q a).hom a z hd _
  refine ⟨z, hd, ?_, fun t => ?_⟩
  · rw [← hcz, LinearEquiv.symm_apply_apply]
  · exact hz (t ⋙ (inU q ⊤).lift (𝟭 _) (fun T => inTop q T))

end

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e' := by
  intro K _ X q a ⟨e, he, hb⟩
  refine ⟨((resTopEquiv q a).trans (LinearEquiv.ofBijective e hb).symm).trans (omEq q a), fun g₀ g => ?_⟩
  exact isFormT_of_isForm q g₀ g _ (he g₀ g)

end GlobalTheory.CompanionTheory.HodgeFormTop
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormIsoOfBijectiveStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_form_iso_of_bijective : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e' := by
  first | exact @GlobalTheory.CompanionTheory.HodgeFormTop.main | exact GlobalTheory.CompanionTheory.HodgeFormTop.main | (intros; apply GlobalTheory.CompanionTheory.HodgeFormTop.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormCupWedge
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormCupWedge
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section
namespace GlobalTheory.CompanionTheory.OmCup
open CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem mk_carry (Λ : LiftsT q) {T T' : Thick (smFun X q)} (φ : T ⟶ T') (g : Γ(X, ⊤)) :
    Ideal.Quotient.mk T'.J (φ.φ (Λ.v T g)) = Ideal.Quotient.mk T'.J (Λ.v T' g) := by
  rw [Λ.hv T' g]
  refine Eq.trans ?_ (GlobalTheory.CompanionTheory.GrForm.ev_nat (q := q) φ (inTop q T) (inTop q T') g).symm
  rw [← Λ.hv T g]
  rfl

def up (Λ : LiftsT q) {n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (i : Fin (n + 1)) (g : Γ(X, ⊤)) :
    (s.obj (Fin.last n)).B :=
  (s.map (homOfLE (Fin.le_last i))).φ (Λ.v _ g)

theorem mk_up (Λ : LiftsT q) {n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (i : Fin (n + 1)) (g : Γ(X, ⊤)) :
    Ideal.Quotient.mk (s.obj (Fin.last n)).J (up Λ s i g) = Ideal.Quotient.mk _ (Λ.v (s.obj (Fin.last n)) g) :=
  mk_carry Λ _ g

theorem carry (Λ : LiftsT q) {m n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (p : Fin (m + 1) → Fin (n + 1))
    (hp : Monotone p) (k : Fin (m + 1)) (g : Γ(X, ⊤)) :
    (s.map (homOfLE (Fin.le_last (p (Fin.last m))))).φ (up Λ (hp.functor ⋙ s) k g) = up Λ s (p k) g := by
  have e : (hp.functor ⋙ s).map (homOfLE (Fin.le_last k)) ≫ s.map (homOfLE (Fin.le_last (p (Fin.last m)))) =
      s.map (homOfLE (Fin.le_last (p k))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]
    exact congrArg s.map (Subsingleton.elim _ _)
  exact congrArg (fun ψ : (s.obj (p k)) ⟶ (s.obj (Fin.last n)) => ψ.φ (Λ.v _ g)) e

theorem form_eq (Λ : LiftsT q) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (s : ComposableArrows (Thick (smFun X q)) a) :
    Λ.form g₀ g s = Λ.v _ g₀ * ∏ k : Fin a, (up Λ s k.succ (g k) - up Λ s k.castSucc (g k)) := rfl

theorem prod_mem (Λ : LiftsT q) {a : ℕ} (g : Fin a → Γ(X, ⊤)) (s : ComposableArrows (Thick (smFun X q)) a) :
    ∏ k : Fin a, (up Λ s k.succ (g k) - up Λ s k.castSucc (g k)) ∈ pdP (s.obj (Fin.last a)).δ a := by
  have key : ∀ (S : Finset (Fin a)), ∏ k ∈ S, (up Λ s k.succ (g k) - up Λ s k.castSucc (g k)) ∈
      pdP (s.obj (Fin.last a)).δ S.card := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty]
      exact Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
    | insert c S hc ih =>
      rw [Finset.prod_insert hc, Finset.card_insert_of_notMem hc, Nat.add_comm S.card 1]
      refine dividedPowerFiltration_mul _ 1 S.card ?_ ih
      refine (s.obj (Fin.last a)).J_le_pdPow_one ?_
      rw [← Ideal.Quotient.eq, mk_up, mk_up]
  simpa using key Finset.univ

theorem form_mem (Λ : LiftsT q) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (s : ComposableArrows (Thick (smFun X q)) a) :
    Λ.form g₀ g s ∈ pdP (s.obj (Fin.last a)).δ a :=
  Ideal.mul_mem_left _ _ (prod_mem Λ g s)

theorem carry_form (Λ : LiftsT q) {m n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (p : Fin (m + 1) → Fin (n + 1))
    (hp : Monotone p) (g₀ : Γ(X, ⊤)) (g : Fin m → Γ(X, ⊤)) :
    (s.map (homOfLE (Fin.le_last (p (Fin.last m))))).φ (Λ.form g₀ g (hp.functor ⋙ s)) =
      up Λ s (p (Fin.last m)) g₀ * ∏ k : Fin m, (up Λ s (p k.succ) (g k) - up Λ s (p k.castSucc) (g k)) := by
  rw [form_eq, map_mul, map_prod]
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_sub, carry, carry]

def someLifts (q : X ⟶ Spec (CommRingCat.of K)) : LiftsT q where
  v T g := Function.surjInv Ideal.Quotient.mk_surjective
    (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) g)
  hv T g := Function.surjInv_eq _ _

theorem isFormT_unique {a : ℕ} {g₀ : Γ(X, ⊤)} {g : Fin a → Γ(X, ⊤)} {c c' : Hdg q a a}
    (h : IsFormT q g₀ g c) (h' : IsFormT q g₀ g c') : c = c' := by
  obtain ⟨f, hf, e, hz⟩ := h (someLifts q)
  obtain ⟨f', hf', e', hz'⟩ := h' (someLifts q)
  have : f = f' := funext fun s => Subtype.ext ((hz s).trans (hz' s).symm)
  subst this
  exact e.trans e'.symm

theorem alg {B : Type} [CommRing B] (x₁ x₂ v p₁ p₂ : B) :
    (x₁ * x₂ - v) * (p₁ * p₂) = x₁ * p₁ * (x₂ * p₂) - v * (p₁ * p₂) := by ring

theorem cup_rep (Λ : LiftsT q) {a b : ℕ} (g₀ h₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (h : Fin b → Γ(X, ⊤))
    (f : CH.Cn (grT (smFun X q) a) a) (f' : CH.Cn (grT (smFun X q) b) b)
    (hf : ∀ s, (show sqM _ _ _ from f s).1 = Ideal.Quotient.mk _ (Λ.form g₀ g s))
    (hf' : ∀ s, (show sqM _ _ _ from f' s).1 = Ideal.Quotient.mk _ (Λ.form h₀ h s))
    (s : ComposableArrows (Thick (smFun X q)) (a + b)) :
    (show sqM _ _ _ from (grOk (smFun X q) (rfl : a + b = a + b)).pair.cupC (rfl : a + b = a + b) f f' s).1 =
      Ideal.Quotient.mk _ (Λ.form (g₀ * h₀) (Fin.append g h) s) := by
  have hm := CH.front_mono (rfl : a + b = a + b)
  have hb := CH.back_mono (rfl : a + b = a + b)
  have e1 : f (hm.functor ⋙ s) = sqMk (thFil (smFun X q) (a : ℤ)) (thFil (smFun X q) ((a : ℤ) + 1)) (Λ.form g₀ g (hm.functor ⋙ s))
      (form_mem Λ g₀ g _) := Subtype.ext (hf _)
  have e2 : f' (hb.functor ⋙ s) = sqMk (thFil (smFun X q) (b : ℤ)) (thFil (smFun X q) ((b : ℤ) + 1)) (Λ.form h₀ h (hb.functor ⋙ s))
      (form_mem Λ h₀ h _) := Subtype.ext (hf' _)
  have hM := grOk (smFun X q) (rfl : a + b = a + b)
  have t1 : CH.term (grT (smFun X q) a) s f (CH.front (rfl : a + b = a + b)) hm =
      sqMk (thFil (smFun X q) (a : ℤ)) (thFil (smFun X q) ((a : ℤ) + 1))
        ((s.map (homOfLE (Fin.le_last (CH.front (rfl : a + b = a + b) (Fin.last a))))).φ (Λ.form g₀ g (hm.functor ⋙ s)))
        ((thFil (smFun X q) (a : ℤ)).map_mem _ (show _ ∈ (thFil (smFun X q) (a : ℤ)).S _ from form_mem Λ g₀ g (hm.functor ⋙ s))) := by
    unfold CH.term
    rw [e1]
    rfl
  have t2 : CH.term (grT (smFun X q) b) s f' (CH.back (rfl : a + b = a + b)) hb =
      sqMk (thFil (smFun X q) (b : ℤ)) (thFil (smFun X q) ((b : ℤ) + 1))
        ((s.map (homOfLE (Fin.le_last (CH.back (rfl : a + b = a + b) (Fin.last b))))).φ (Λ.form h₀ h (hb.functor ⋙ s)))
        ((thFil (smFun X q) (b : ℤ)).map_mem _ (show _ ∈ (thFil (smFun X q) (b : ℤ)).S _ from form_mem Λ h₀ h (hb.functor ⋙ s))) := by
    unfold CH.term
    rw [e2]
    rfl
  have c : (grOk (smFun X q) (rfl : a + b = a + b)).pair.cupC (rfl : a + b = a + b) f f' s =
      (grOk (smFun X q) (rfl : a + b = a + b)).mul (CH.term (grT (smFun X q) a) s f (CH.front (rfl : a + b = a + b)) hm)
        (CH.term (grT (smFun X q) b) s f' (CH.back (rfl : a + b = a + b)) hb) := rfl
  rw [c, t1, t2, MulOk.mul_mk]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [carry_form Λ s _ hm g₀ g, carry_form Λ s _ hb h₀ h, form_eq]
  have hprod : ∏ k : Fin (a + b), (up Λ s k.succ (Fin.append g h k) - up Λ s k.castSucc (Fin.append g h k)) =
      (∏ k : Fin a, (up Λ s (CH.front (rfl : a + b = a + b) k.succ) (g k) - up Λ s (CH.front (rfl : a + b = a + b) k.castSucc) (g k))) *
      ∏ k : Fin b, (up Λ s (CH.back (rfl : a + b = a + b) k.succ) (h k) - up Λ s (CH.back (rfl : a + b = a + b) k.castSucc) (h k)) := by
    rw [Fin.prod_univ_add]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_) (Finset.prod_congr rfl fun i _ => ?_)
    · rw [Fin.append_left]
      rfl
    · rw [Fin.append_right]
      have e3 : (Fin.natAdd a i).succ = CH.back (rfl : a + b = a + b) i.succ := Fin.ext (by simp [CH.back]; omega)
      have e4 : (Fin.natAdd a i).castSucc = CH.back (rfl : a + b = a + b) i.castSucc := Fin.ext (by simp [CH.back])
      rw [e3, e4]
  have hP := prod_mem Λ (Fin.append g h) s
  rw [hprod] at hP ⊢
  rw [Ideal.Quotient.eq]
  generalize (∏ k : Fin a, (up Λ s (CH.front (rfl : a + b = a + b) k.succ) (g k) - up Λ s (CH.front (rfl : a + b = a + b) k.castSucc) (g k))) = P₁ at hP ⊢
  generalize (∏ k : Fin b, (up Λ s (CH.back (rfl : a + b = a + b) k.succ) (h k) - up Λ s (CH.back (rfl : a + b = a + b) k.castSucc) (h k))) = P₂ at hP ⊢
  have hJ : up Λ s (CH.front (rfl : a + b = a + b) (Fin.last a)) g₀ * up Λ s (CH.back (rfl : a + b = a + b) (Fin.last b)) h₀ -
      Λ.v _ (g₀ * h₀) ∈ (s.obj (Fin.last (a + b))).J := by
    rw [← Ideal.Quotient.eq, map_mul, mk_up, mk_up, Λ.hv, Λ.hv, Λ.hv, map_mul]
  have hm2 := dividedPowerFiltration_mul _ 1 (a + b) ((s.obj (Fin.last (a + b))).J_le_pdPow_one hJ) hP
  have e5 : (((a + b : ℕ) : ℤ) + 1).toNat = 1 + (a + b) := by omega
  change _ ∈ pdP _ (((a + b : ℕ) : ℤ) + 1).toNat
  rw [e5]
  rw [alg] at hm2
  exact hm2

theorem isFormT_cup {a b : ℕ} {g₀ h₀ : Γ(X, ⊤)} {g : Fin a → Γ(X, ⊤)} {h : Fin b → Γ(X, ⊤)} {x : Hdg q a a} {y : Hdg q b b}
    (hx : IsFormT q g₀ g x) (hy : IsFormT q h₀ h y) :
    IsFormT q (g₀ * h₀) (Fin.append g h) (cupH q rfl rfl x y) := by
  intro Λ
  obtain ⟨f, hf, ex, hz⟩ := hx Λ
  obtain ⟨f', hf', ey, hz'⟩ := hy Λ
  obtain ⟨hc, e⟩ := CrystallineSemistableComparison.P.cup_cls (grOk (smFun X q) (rfl : a + b = a + b)).pair (rfl : a + b = a + b) f f' hf hf'
  refine ⟨_, hc, ?_, cup_rep Λ g₀ h₀ g h f f' hz hz'⟩
  exact (congrArg₂ (fun u v => (grOk (smFun X q) (rfl : a + b = a + b)).pair.cup (rfl : a + b = a + b) u v) ex ey).trans e

theorem wedge_form {A : Type} [CommRing A] [Algebra K A] {a b : ℕ} (g₀ h₀ : A) (g : Fin a → A) (h : Fin b → A) :
    wedgeOm K A (rfl : a + b = a + b) (CrystallineSemistableComparison.Onto.form K g₀ g) (CrystallineSemistableComparison.Onto.form K h₀ h) =
      CrystallineSemistableComparison.Onto.form K (g₀ * h₀) (Fin.append g h) := by
  refine Subtype.ext ?_
  rw [coe_wedgeOm]
  simp only [CrystallineSemistableComparison.Onto.form, Submodule.coe_smul, exteriorPower.ιMulti_apply_coe]
  rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, ← List.prod_append,
    ← List.ofFn_fin_append]
  refine congrArg (fun v => (g₀ * h₀) • (List.ofFn v).prod) (funext fun i => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

theorem bilin_ext {H₁ H₂ H₃ M₁ M₂ M₃ : Type*} [AddCommGroup H₁] [AddCommGroup H₂] [AddCommGroup H₃] [AddCommGroup M₁]
    [AddCommGroup M₂] [AddCommGroup M₃] [Module K H₁] [Module K H₂] [Module K H₃] [Module K M₁] [Module K M₂] [Module K M₃]
    (e₁ : H₁ ≃ₗ[K] M₁) (e₂ : H₂ ≃ₗ[K] M₂) (e₃ : H₃ ≃ₗ[K] M₃) (B : H₁ →ₗ[K] H₂ →ₗ[K] H₃) (Wd : M₁ →ₗ[K] M₂ →ₗ[K] M₃)
    (S₁ : Set M₁) (S₂ : Set M₂) (h₁ : Submodule.span K S₁ = ⊤) (h₂ : Submodule.span K S₂ = ⊤)
    (gen : ∀ ω ∈ S₁, ∀ η ∈ S₂, e₃ (B (e₁.symm ω) (e₂.symm η)) = Wd ω η) (x : H₁) (y : H₂) :
    e₃ (B x y) = Wd (e₁ x) (e₂ y) := by
  have all : ∀ (ω : M₁) (η : M₂), e₃ (B (e₁.symm ω) (e₂.symm η)) = Wd ω η := by
    intro ω η
    have hω : ω ∈ Submodule.span K S₁ := h₁ ▸ Submodule.mem_top
    have hη : η ∈ Submodule.span K S₂ := h₂ ▸ Submodule.mem_top
    induction hω using Submodule.span_induction with
    | zero => simp
    | add u v _ _ hu hv => simp only [map_add (f := _), LinearMap.add_apply, hu, hv]
    | smul r u _ hu => simp only [map_smul, LinearMap.smul_apply, hu]
    | mem u hu =>
      induction hη using Submodule.span_induction with
      | zero => simp
      | add u v _ _ hu hv => simp only [map_add (f := _), hu, hv]
      | smul r u _ hu => simp only [map_smul, hu]
      | mem v hv => exact gen u hu v hv
  simpa using all (e₁ x) (e₂ y)

theorem exists_bil (q : X ⟶ Spec (CommRingCat.of K)) (a b : ℕ) :
    ∃ B : Hdg q a a →ₗ[K] Hdg q b b →ₗ[K] Hdg q (a + b) (a + b), ∀ u v, B u v = cupH q rfl rfl u v := by
  obtain ⟨bil, hbil⟩ := CrystallineSemistableComparison.P.cup_bilin (grOk (smFun X q) (rfl : a + b = a + b)).pair (rfl : a + b = a + b)
  exact ⟨bil, hbil⟩

theorem gen_eq {a b : ℕ} (eA : Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : Hdg q b b ≃ₗ[K] OmU q ⊤ b)
    (eC : Hdg q (a + b) (a + b) ≃ₗ[K] OmU q ⊤ (a + b)) (hA : IsOmT q a eA) (hB : IsOmT q b eB) (hC : IsOmT q (a + b) eC)
    (g₀ h₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (h : Fin b → Γ(X, ⊤)) :
    eC (cupH q rfl rfl (eA.symm (gForm q g₀ g)) (eB.symm (gForm q h₀ h))) =
      wedgeOm K (Sec q ⊤) rfl (gForm q g₀ g) (gForm q h₀ h) := by
  have e := isFormT_unique (isFormT_cup (hA g₀ g) (hB h₀ h)) (hC (g₀ * h₀) (Fin.append g h))
  rw [e, LinearEquiv.apply_symm_apply]
  exact (wedge_form (K := K) (A := Sec q ⊤) g₀ h₀ g h).symm

theorem main : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a b c : ℕ) (h : a + b = c)
    (eA : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : CrystallineSemistableComparison.HT.Hdg q b b ≃ₗ[K] OmU q ⊤ b) (eC : CrystallineSemistableComparison.HT.Hdg q c c ≃ₗ[K] OmU q ⊤ c),
    CrystallineSemistableComparison.Om.L2.IsOmT q a eA → CrystallineSemistableComparison.Om.L2.IsOmT q b eB → CrystallineSemistableComparison.Om.L2.IsOmT q c eC → ∀ x y,
      eC (CrystallineSemistableComparison.HT.cupH q h h x y) = wedgeOm K (Sec q ⊤) h (eA x) (eB y) := by
  intro K _ X q a b c h eA eB eC hA hB hC x y
  subst h
  obtain ⟨B, hB'⟩ := exists_bil q a b
  rw [← hB']
  refine bilin_ext eA eB eC B (wedgeOm K (Sec q ⊤) rfl) _ _ (GlobalTheory.CompanionTheory.OntoForms.formLaws K (Sec q ⊤) (Sec q ⊤) a).1
    (GlobalTheory.CompanionTheory.OntoForms.formLaws K (Sec q ⊤) (Sec q ⊤) b).1 ?_ x y
  rintro _ ⟨g₀, g, rfl⟩ _ ⟨h₀, h, rfl⟩
  rw [hB']
  exact gen_eq eA eB eC hA hB hC g₀ h₀ g h

end GlobalTheory.CompanionTheory.OmCup
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormCupWedgeStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_form_cup_wedge : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a b c : ℕ) (h : a + b = c)
    (eA : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : CrystallineSemistableComparison.HT.Hdg q b b ≃ₗ[K] OmU q ⊤ b) (eC : CrystallineSemistableComparison.HT.Hdg q c c ≃ₗ[K] OmU q ⊤ c),
    CrystallineSemistableComparison.Om.L2.IsOmT q a eA → CrystallineSemistableComparison.Om.L2.IsOmT q b eB → CrystallineSemistableComparison.Om.L2.IsOmT q c eC → ∀ x y,
      eC (CrystallineSemistableComparison.HT.cupH q h h x y) = wedgeOm K (Sec q ⊤) h (eA x) (eB y) := by
  first | exact @GlobalTheory.CompanionTheory.OmCup.main | exact GlobalTheory.CompanionTheory.OmCup.main | (intros; apply GlobalTheory.CompanionTheory.OmCup.main <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormPullbackCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormPullbackCompat
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace GlobalTheory.CompanionTheory.OmNatT

open CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2

universe v u

theorem rep_unique {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {A : C ⥤ CommAlgCat.{0} R} {a b : IdF A} {j : ℕ}
    {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))} {c c' : CH.H (sq a b) j}
    (h : Rep a b z c) (h' : Rep a b z c') : c = c' := by
  obtain ⟨f, hf, e, hz⟩ := h
  obtain ⟨f', hf', e', hz'⟩ := h'
  have hff : f = f' := funext fun s => Subtype.ext ((hz s).trans (hz' s).symm)
  subst hff
  exact e.trans e'.symm

section Span

variable (K A : Type) [CommRing K] [CommRing A] [Algebra K A]

theorem multi_mem {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] {a : ℕ}
    (f : (Fin a → M) →ₘₗ[A] N) (s : Set M) (hs : Submodule.span A s = ⊤) (S : Submodule A N)
    (h : ∀ v : Fin a → M, (∀ k, v k ∈ s) → f v ∈ S) (v : Fin a → M) : f v ∈ S := by
  classical
  have key : ∀ (t : Finset (Fin a)) (v : Fin a → M), (∀ k, k ∉ t → v k ∈ s) → f v ∈ S := by
    intro t
    induction t using Finset.induction_on with
    | empty => exact fun v hv => h v fun k => hv k (by simp)
    | insert i t hi ih =>
      intro v hv
      have hvi : v i ∈ Submodule.span A s := hs ▸ Submodule.mem_top
      have : ∀ x ∈ Submodule.span A s, f (Function.update v i x) ∈ S := by
        intro x hx
        induction hx using Submodule.span_induction with
        | mem x hxs =>
          refine ih _ fun k hk => ?_
          by_cases e : k = i
          · rw [e, Function.update_self]; exact hxs
          · rw [Function.update_of_ne e]
            exact hv k (by simp [e, hk])
        | zero => rw [f.map_update_zero]; exact S.zero_mem
        | add x y _ _ hx hy => rw [f.map_update_add]; exact S.add_mem hx hy
        | smul c x _ hx => rw [f.map_update_smul, RingHom.id_apply]; exact S.smul_mem _ hx
      simpa using this _ hvi
  exact key Finset.univ v fun k hk => (hk (Finset.mem_univ k)).elim

theorem span_form (a : ℕ) : Submodule.span K {ω : ⋀[A]^a Ω[A⁄K] | ∃ (g₀ : A) (g : Fin a → A), ω = CrystallineSemistableComparison.Onto.form K g₀ g} = ⊤ := by
  set S := Submodule.span K {ω : ⋀[A]^a Ω[A⁄K] | ∃ (g₀ : A) (g : Fin a → A), ω = CrystallineSemistableComparison.Onto.form K g₀ g} with hS
  have hsm : ∀ (c : A) x, x ∈ S → c • x ∈ S := by
    intro c x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g₀, g, rfl⟩ := hx
      refine Submodule.subset_span ⟨c * g₀, g, ?_⟩
      simp only [CrystallineSemistableComparison.Onto.form, mul_smul]
    | zero => rw [smul_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [smul_add]; exact S.add_mem hx hy
    | smul r x _ hx =>
      rw [← algebraMap_smul A r x, smul_comm, algebraMap_smul]
      exact S.smul_mem r hx
  let S' : Submodule A (⋀[A]^a Ω[A⁄K]) :=
    { carrier := S
      add_mem' := S.add_mem
      zero_mem' := S.zero_mem
      smul_mem' := hsm }
  have hι : ∀ v : Fin a → Ω[A⁄K], exteriorPower.ιMulti A a v ∈ S' := fun v =>
    multi_mem A (exteriorPower.ιMulti A a (M := Ω[A⁄K])).toMultilinearMap (Set.range (KaehlerDifferential.D K A))
      (KaehlerDifferential.span_range_derivation K A) S' (fun v hv => by
        choose g hg using hv
        refine Submodule.subset_span ⟨1, g, ?_⟩
        have e : v = fun k => KaehlerDifferential.D K A (g k) := (funext hg).symm
        simp only [CrystallineSemistableComparison.Onto.form, one_smul]
        rw [← e]
        rfl) v
  refine eq_top_iff.2 fun x _ => ?_
  have hx : x ∈ Submodule.span A (Set.range (exteriorPower.ιMulti A a (M := Ω[A⁄K]))) := by
    rw [exteriorPower.ιMulti_span]; trivial
  have : Submodule.span A (Set.range (exteriorPower.ιMulti A a (M := Ω[A⁄K]))) ≤ S' :=
    Submodule.span_le.2 (by rintro _ ⟨v, rfl⟩; exact hι v)
  exact this hx

end Span

section Mom

variable {R R' B B' : Type} [CommRing R] [CommRing B] [Algebra R B] [CommRing R'] [CommRing B'] [Algebra R' B']
  {σ : R →+* R'} {α : B →+* B'}

theorem mOm_form (h : SemiHom σ α) {a : ℕ} (g₀ : B) (g : Fin a → B) :
    h.mOm a (CrystallineSemistableComparison.Onto.form R g₀ g) = CrystallineSemistableComparison.Onto.form R' (α g₀) fun k => α (g k) := by
  unfold CrystallineSemistableComparison.Onto.form
  rw [h.mOm_smul]
  congr 1
  refine Subtype.ext ?_
  rw [SemiHom.coe_mOm, exteriorPower.ιMulti_apply_coe, exteriorPower.ιMulti_apply_coe, ExteriorAlgebra.ιMulti_apply,
    ExteriorAlgebra.ιMulti_apply, map_list_prod, List.map_ofFn]
  congr 2
  funext i
  exact (h.mDR_ι _).trans (congrArg (ExteriorAlgebra.ι B') (h.m1_D (g i)))

end Mom

section Pull

variable {K : Type} [CommRing K] {X Y : Scheme.{0}}

def outL (q : X ⟶ Spec (CommRingCat.of K)) : LiftsT q where
  v T g := Quotient.out (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) g)
  hv T g := Ideal.Quotient.mk_out _

variable {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}

def uS (u : X ⟶ Y) : Γ(Y, ⊤) →+* Γ(X, ⊤) := (u.appLE ⊤ ⊤ (by simp)).hom

theorem ev_pull (u : X ⟶ Y) (hu : u ≫ p = q) (T : Thick (smFun X q)) (g : Γ(Y, ⊤)) :
    ev (γ := dividedPowersBot K) (p := 0) (q := p) (κ := Ideal.Quotient.mk ⊥) ((smS u hu).G.obj T) (inTop p _) g =
      ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) (uS u g) := by
  change (Scheme.ΓSpecIso (CommRingCat.of (T.B ⧸ T.J))).hom.hom (((pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T ≫ u).appLE ⊤ ⊤ _).hom g) =
    (Scheme.ΓSpecIso (CommRingCat.of (T.B ⧸ T.J))).hom.hom (((pt (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T).appLE ⊤ ⊤ _).hom ((u.appLE ⊤ ⊤ (by simp)).hom g))
  congr 1
  rw [← Scheme.Hom.appLE_comp_appLE _ _ ⊤ ⊤ ⊤ (by simp) (by simp)]
  rfl

theorem out_pull (u : X ⟶ Y) (hu : u ≫ p = q) (T : Thick (smFun X q)) (g : Γ(Y, ⊤)) :
    (outL p).v ((smS u hu).G.obj T) g = (outL q).v T (uS u g) :=
  congrArg Quotient.out (ev_pull u hu T g)

theorem form_pull (u : X ⟶ Y) (hu : u ≫ p = q) {a : ℕ} (g₀ : Γ(Y, ⊤)) (g : Fin a → Γ(Y, ⊤))
    (s : ComposableArrows (Thick (smFun X q)) a) :
    (outL q).form (uS u g₀) (fun k => uS u (g k)) s = (outL p).form g₀ g (s ⋙ (smS u hu).G) := by
  unfold LiftsT.form
  refine congrArg₂ (· * ·) (out_pull u hu _ g₀).symm (Finset.prod_congr rfl fun k _ => ?_)
  exact congrArg₂ (· - ·) (congrArg _ (out_pull u hu _ (g k)).symm) (congrArg _ (out_pull u hu _ (g k)).symm)

theorem rep_pull (u : X ⟶ Y) (hu : u ≫ p = q) {a : ℕ}
    {z : ∀ s : ComposableArrows (Thick (smFun Y p)) a, (s.obj (Fin.last a)).B}
    {z' : ∀ s : ComposableArrows (Thick (smFun X q)) a, (s.obj (Fin.last a)).B}
    (hz : ∀ s, z' s = z (s ⋙ (smS u hu).G)) {c : Hdg p a a}
    (h : Rep (thFil (smFun Y p) (a : ℤ)) (thFil (smFun Y p) ((a : ℤ) + 1)) z (show CH.H (grT (smFun Y p) a) a from c)) :
    Rep (thFil (smFun X q) (a : ℤ)) (thFil (smFun X q) ((a : ℤ) + 1)) z'
      (show CH.H (grT (smFun X q) a) a from pullH u hu a a c) := by
  obtain ⟨f, hf, e, hfz⟩ := h
  let m : CH.Mor (grT (smFun Y p) a) (grT (smFun X q) a) (RingHom.id K) :=
    (smS u hu).sq (a := thFil _ (a : ℤ)) (b := thFil _ ((a : ℤ) + 1)) (a' := thFil _ (a : ℤ)) (b' := thFil _ ((a : ℤ) + 1))
      (fun _ _ hx => hx) fun _ _ hx => hx
  have hd : CH.d (grT (smFun X q) a) a (m.pullC a f) = 0 := by
    rw [m.d_pullC, hf, map_zero]
  refine ⟨m.pullC a f, hd, ?_, fun s => ?_⟩
  · change m.pull a c = _
    have : c = (CH.cx (grT (smFun Y p) a)).cls f hf := e
    rw [this]
    exact CrystallineSemistableComparison.P.mapH_cls m.hom a f hf hd
  · rw [hz s]
    exact congrArg (Ideal.quotientMap _ ((smS u hu).ρ _) _) (hfz (s ⋙ (smS u hu).G))

end Pull

section Main

variable {K : Type} [CommRing K] {X Y : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {p : Y ⟶ Spec (CommRingCat.of K)}

theorem res_pull_form (u : X ⟶ Y) (hu : u ≫ p = q) {a : ℕ} (g₀ : Γ(Y, ⊤)) (g : Fin a → Γ(Y, ⊤)) :
    formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (gForm p g₀ g)) =
      gForm q (uS u g₀) fun k => uS u (g k) := by
  have e1 : formPull hu ⊤ a (gForm p g₀ g) = CrystallineSemistableComparison.Onto.form K (A := Sec q (u ⁻¹ᵁ ⊤)) (appSec p q u ⊤ g₀)
      fun k => appSec p q u ⊤ (g k) := mOm_form (semiHom_appSec hu ⊤) g₀ g
  rw [e1]
  exact mOm_form (SemiHom.of_algHom (Sec.res q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp))) _ _

end Main

theorem pull_nat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (e' : CrystallineSemistableComparison.HT.Hdg p a a ≃ₗ[K] OmU p ⊤ a),
    CrystallineSemistableComparison.Om.L2.IsOmT q a e → CrystallineSemistableComparison.Om.L2.IsOmT p a e' → ∀ x : CrystallineSemistableComparison.HT.Hdg p a a,
      e (CrystallineSemistableComparison.HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e' x)) := by
  intro K _ X Y q p u hu a e e' he he' x
  have key : ∀ ω : OmU p ⊤ a, e (pullH u hu a a (e'.symm ω)) =
      formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a ω) := by
    intro ω
    have hω : ω ∈ Submodule.span K {ω : ⋀[Sec p ⊤]^a Ω[Sec p ⊤⁄K] | ∃ (g₀ : Sec p ⊤) (g : Fin a → Sec p ⊤),
        ω = CrystallineSemistableComparison.Onto.form K g₀ g} := by
      rw [span_form]; trivial
    induction hω using Submodule.span_induction with
    | mem ω hω =>
      obtain ⟨g₀, g, rfl⟩ := hω
      have h1 := he' g₀ g (outL p)
      have h2 := he (uS u g₀) (fun k => uS u (g k)) (outL q)
      have h3 := rep_pull u hu (fun s => form_pull u hu g₀ g s) h1
      have h4 : pullH u hu a a (e'.symm (gForm p g₀ g)) = e.symm (gForm q (uS u g₀) fun k => uS u (g k)) :=
        rep_unique h3 h2
      refine Eq.trans ?_ (res_pull_form u hu g₀ g).symm
      change e (pullH u hu a a (e'.symm (gForm p g₀ g))) = _
      rw [h4, LinearEquiv.apply_symm_apply]
    | zero => simp
    | add x y _ _ hx hy => simp only [map_add (f := _), hx, hy]
    | smul r x _ hx =>
      simp only [map_smul, hx]
  simpa using key (e' x)

end GlobalTheory.CompanionTheory.OmNatT
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormPullbackCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_form_pullback_compat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (e' : CrystallineSemistableComparison.HT.Hdg p a a ≃ₗ[K] OmU p ⊤ a),
    CrystallineSemistableComparison.Om.L2.IsOmT q a e → CrystallineSemistableComparison.Om.L2.IsOmT p a e' → ∀ x : CrystallineSemistableComparison.HT.Hdg p a a,
      e (CrystallineSemistableComparison.HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e' x)) := by
  first | exact @GlobalTheory.CompanionTheory.OmNatT.pull_nat | exact GlobalTheory.CompanionTheory.OmNatT.pull_nat | (intros; apply GlobalTheory.CompanionTheory.OmNatT.pull_nat <;> assumption)
end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.HdgAffIsoOnto
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.AsmOnto
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.L2

theorem asm_of
    (hEx : ∀ (K : Type) [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ),
    ∃ e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e)
    (hNat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (e' : CrystallineSemistableComparison.HT.Hdg p a a ≃ₗ[K] OmU p ⊤ a),
    CrystallineSemistableComparison.Om.L2.IsOmT q a e → CrystallineSemistableComparison.Om.L2.IsOmT p a e' → ∀ x : CrystallineSemistableComparison.HT.Hdg p a a,
      e (CrystallineSemistableComparison.HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e' x)))
    (hCup : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a b c : ℕ) (h : a + b = c)
    (eA : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : CrystallineSemistableComparison.HT.Hdg q b b ≃ₗ[K] OmU q ⊤ b) (eC : CrystallineSemistableComparison.HT.Hdg q c c ≃ₗ[K] OmU q ⊤ c),
    CrystallineSemistableComparison.Om.L2.IsOmT q a eA → CrystallineSemistableComparison.Om.L2.IsOmT q b eB → CrystallineSemistableComparison.Om.L2.IsOmT q c eC → ∀ x y,
      eC (CrystallineSemistableComparison.HT.cupH q h h x y) = wedgeOm K (Sec q ⊤) h (eA x) (eB y))
    (hOne : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0),
    CrystallineSemistableComparison.Om.L2.IsOmT q 0 e → e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤)) :
    ∀ (K : Type) [Field K] [CharZero K],
    ∃ (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ),
      HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (ε : ℕ → ℕ → ℤ), (∀ a b, ε a b = 1 ∨ ε a b = -1) ∧
    (∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q]
      [IsAffine Y] [Smooth p] (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (x : HT.Hdg p a a),
      e q a (HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e p a x))) ∧
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a b c : ℕ) (h : a + b = c)
      (x : HT.Hdg q a a) (y : HT.Hdg q b b),
      e q c (HT.cupH q h h x y) = ε a b • wedgeOm K (Sec q ⊤) h (e q a x) (e q b y)) ∧
    ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q], e q 0 (HT.oneH q) = oneOm K (Sec q ⊤) := by
  intro K _ _
  refine ⟨fun q _ _ a => Classical.choose (hEx K q a), fun _ _ => 1, fun _ _ => Or.inl rfl, ?_, ?_, ?_⟩
  · intro X Y q p _ _ _ _ u hu a x
    exact hNat q p u hu a _ _ (Classical.choose_spec (hEx K q a)) (Classical.choose_spec (hEx K p a)) x
  · intro X q _ _ a b c h x y
    simp only [one_smul]
    exact hCup q a b c h _ _ _ (Classical.choose_spec (hEx K q a)) (Classical.choose_spec (hEx K q b))
      (Classical.choose_spec (hEx K q c)) x y
  · intro X q _ _
    exact hOne q _ (Classical.choose_spec (hEx K q 0))

theorem asm_onto (hA : CrystallineSemistableComparison.Onto.AffOm) (hN : CrystallineSemistableComparison.Onto.OmNat)
    (hTop : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e')
    (hGlue : CrystallineSemistableComparison.Onto.AffOm → CrystallineSemistableComparison.Onto.OmNat → ∀ (K : Type) [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))
    [IsAffine X] [Smooth q] (a : ℕ),
    ∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e)
    (hNat : ∀ {K : Type} [CommRing K] {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K))
    (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (e : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (e' : CrystallineSemistableComparison.HT.Hdg p a a ≃ₗ[K] OmU p ⊤ a),
    CrystallineSemistableComparison.Om.L2.IsOmT q a e → CrystallineSemistableComparison.Om.L2.IsOmT p a e' → ∀ x : CrystallineSemistableComparison.HT.Hdg p a a,
      e (CrystallineSemistableComparison.HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e' x)))
    (hCup : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a b c : ℕ) (h : a + b = c)
    (eA : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : CrystallineSemistableComparison.HT.Hdg q b b ≃ₗ[K] OmU q ⊤ b) (eC : CrystallineSemistableComparison.HT.Hdg q c c ≃ₗ[K] OmU q ⊤ c),
    CrystallineSemistableComparison.Om.L2.IsOmT q a eA → CrystallineSemistableComparison.Om.L2.IsOmT q b eB → CrystallineSemistableComparison.Om.L2.IsOmT q c eC → ∀ x y,
      eC (CrystallineSemistableComparison.HT.cupH q h h x y) = wedgeOm K (Sec q ⊤) h (eA x) (eB y))
    (hOne : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (e : CrystallineSemistableComparison.HT.Hdg q 0 0 ≃ₗ[K] OmU q ⊤ 0),
    CrystallineSemistableComparison.Om.L2.IsOmT q 0 e → e (CrystallineSemistableComparison.HT.oneH q) = oneOm K (Sec q ⊤)) :
    ∀ (K : Type) [Field K] [CharZero K],
    ∃ (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ),
      HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (ε : ℕ → ℕ → ℤ), (∀ a b, ε a b = 1 ∨ ε a b = -1) ∧
    (∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q]
      [IsAffine Y] [Smooth p] (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (x : HT.Hdg p a a),
      e q a (HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e p a x))) ∧
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a b c : ℕ) (h : a + b = c)
      (x : HT.Hdg q a a) (y : HT.Hdg q b b),
      e q c (HT.cupH q h h x y) = ε a b • wedgeOm K (Sec q ⊤) h (e q a x) (e q b y)) ∧
    ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q], e q 0 (HT.oneH q) = oneOm K (Sec q ⊤) := by
  exact asm_of (fun K _ _ _ q _ _ a => hTop q a (hGlue hA hN K q a)) hNat hCup hOne

end CrystallineSemistableComparison.Om.L2
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.L2

theorem hdg_aff_iso_onto (hA : CrystallineSemistableComparison.Onto.AffOm) (hN : CrystallineSemistableComparison.Onto.OmNat) :
    ∀ (K : Type) [Field K] [CharZero K],
    ∃ (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ),
      HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (ε : ℕ → ℕ → ℤ), (∀ a b, ε a b = 1 ∨ ε a b = -1) ∧
    (∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q]
      [IsAffine Y] [Smooth p] (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (x : HT.Hdg p a a),
      e q a (HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e p a x))) ∧
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a b c : ℕ) (h : a + b = c)
      (x : HT.Hdg q a a) (y : HT.Hdg q b b),
      e q c (HT.cupH q h h x y) = ε a b • wedgeOm K (Sec q ⊤) h (e q a x) (e q b y)) ∧
    ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q], e q 0 (HT.oneH q) = oneOm K (Sec q ⊤) :=
  asm_onto hA hN GlobalTheory.T.hodge_form_iso_of_bijective GlobalTheory.T.affine_smooth_forms_bijective GlobalTheory.T.hodge_form_pullback_compat GlobalTheory.T.hodge_form_cup_wedge GlobalTheory.T.hodge_form_one

end CrystallineSemistableComparison.Om.L2
end
end

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

namespace CrystallineSemistableComparison.Om.L2

theorem hodge_affine_iso_sign :
    ∀ (K : Type) [Field K] [CharZero K],
    ∃ (e : ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a : ℕ),
      HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (ε : ℕ → ℕ → ℤ), (∀ a b, ε a b = 1 ∨ ε a b = -1) ∧
    (∀ {X Y : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (p : Y ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q]
      [IsAffine Y] [Smooth p] (u : X ⟶ Y) (hu : u ≫ p = q) (a : ℕ) (x : HT.Hdg p a a),
      e q a (HT.pullH u hu a a x) = formRes q (show (⊤ : X.Opens) ≤ u ⁻¹ᵁ ⊤ by simp) a (formPull hu ⊤ a (e p a x))) ∧
    (∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q] (a b c : ℕ) (h : a + b = c)
      (x : HT.Hdg q a a) (y : HT.Hdg q b b),
      e q c (HT.cupH q h h x y) = ε a b • wedgeOm K (Sec q ⊤) h (e q a x) (e q b y)) ∧
    ∀ {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) [IsAffine X] [Smooth q], e q 0 (HT.oneH q) = oneOm K (Sec q ⊤) :=
  hdg_aff_iso_onto (GlobalTheory.T.affine_forms_of_form_uniqueness CrystallineSemistableComparison.Onto.formUniq_pf) CrystallineSemistableComparison.Onto.omNatB_pf

end CrystallineSemistableComparison.Om.L2
