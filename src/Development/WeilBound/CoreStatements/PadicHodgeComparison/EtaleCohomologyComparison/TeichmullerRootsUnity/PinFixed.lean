module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.ResiduePadicIntegersToIntegers
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.TUnit
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PhiAIter
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.MuNu
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusWittActions.FrobeniusNormBounds.MapFrobW

@[expose] public section

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.RootsUnityPullback.IsMuMmG
section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.RootsUnityPullback.MmPull
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.crystallineComparison.PinP

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

def mm (r : Res l K) (M : Model l K) (n : ℕ) {N : ℕ} (hT : Pb.Mid.TeichmullerCongruence r N) : MuMor r M n :=
  (Pb.bWMor r M n).comp (σ'' := r.w) (Pb.Mid.muMor r M n hT)

theorem mm_pull (r : Res l K) (M : Model l K) (n j : ℕ) {N : ℕ} (hT : Pb.Mid.TeichmullerCongruence r N)
    (y : (Pb.HSW r M j).M n) : (mm r M n hT).pull j y = Pb.Mid.mu r M n j hT (Pb.bW r M n j y) :=
  (CrystallineSemistableComparison.P.pull_comp (Pb.bWMor r M n) (Pb.Mid.muMor r M n hT) j y).1

end CrystallineSemistableComparison.crystallineComparison.PinP
end
end

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.crystallineComparison.PinP

section
variable {O : Type} [CommRing O] (F : B.Fn O) {b₀ b₁ : Base} {h₀ : b₀.t = 1} {h₁ : b₁.t = 1} {κ₀ : O →+* b₀.R ⧸ b₀.I}
  {κ₁ κm : O →+* b₁.R ⧸ b₁.I} {Λ₀ Λ₁ : Type} [CommRing Λ₀] [CommRing Λ₁] {c₀ : Λ₀ →+* b₀.R} {c₁ : Λ₁ →+* b₁.R} {w : Λ₀ →+* Λ₁}

def IsMuG (wn : b₀.R →+* b₁.R) (e : ℕ) (m : CH.Mor (B.OM (F.cr b₀ h₀ κ₀) c₀) (B.OM (F.cr b₁ h₁ κ₁) c₁) w) : Prop :=
  ∃ η : ∀ T, (m.G.obj T).B ≃+* T.B, (∀ T (x : (m.G.obj T).B), (show T.B from m.τ T x) = η T x) ∧
    (∀ T, IsDPMorphism (m.G.obj T).δ T.δ (η T).toRingHom) ∧ (∀ T, (m.G.obj T).J.map (η T).toRingHom = T.J) ∧
    (∀ T w, η T ((m.G.obj T).i w) = T.i (wn w)) ∧
    ∀ T (h : (m.G.obj T).J ≤ T.J.comap (η T).toRingHom) (φ : T.B ⧸ T.J →+* T.B ⧸ T.J), (∀ x, φ x = x ^ e) →
      F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T.J (η T).toRingHom h)) (m.G.obj T).y.1.2 =
        F.Pt.map (CommRingCat.ofHom φ) T.y.1.2

theorem isMuG (wn : b₀.R →+* b₁.R) (e : ℕ) (m₁ : Mor (F.cr b₀ h₀ κ₀) (F.cr b₁ h₁ κm) wn)
    (m₂ : Mor (F.cr b₁ h₁ κm) (F.cr b₁ h₁ κ₁) (RingHom.id _)) (k₁ : ∀ a, wn (c₀ a) = c₁ (w a))
    (k₂ : ∀ a, RingHom.id _ (c₁ a) = c₁ (RingHom.id _ a))
    (p₁ : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κm).obj B₀), (show (F.ptK κ₀).obj B₀ from m₁.pt.app B₀ y).1.2 = y.1.2)
    (p₂ : ∀ (B₀ : CommRingCat.{0}) (y : (F.ptK κ₁).obj B₀) (φ : B₀ →+* B₀), (∀ x, φ x = x ^ e) →
      (show (F.ptK κm).obj B₀ from m₂.pt.app B₀ y).1.2 = F.Pt.map (CommRingCat.ofHom φ) y.1.2) :
    IsMuG F wn e ((B.omMor m₁ w k₁).comp (σ'' := w) (B.omMor m₂ (RingHom.id _) k₂)) := by
  refine ⟨fun T => RingEquiv.refl T.B, fun _ _ => rfl, fun T => ⟨le_of_eq (Ideal.map_id _), fun _ _ => rfl⟩,
    fun T => Ideal.map_id _, fun _ _ => rfl, fun T h φ hφ => ?_⟩
  have e1 : Ideal.quotientMap T.J (RingEquiv.refl T.B).toRingHom h = RingHom.id _ :=
    Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)
  have e2 := (p₁ _ (m₂.pt.app _ T.y)).trans (p₂ _ T.y φ hφ)
  refine Eq.trans ?_ e2
  refine (congrArg (fun g => F.Pt.map (CommRingCat.ofHom g) _) e1).trans ?_
  exact congrFun (congrArg (fun t => (ConcreteCategory.hom t : _ → _)) (F.Pt.map_id (CommRingCat.of (T.B ⧸ T.J)))) _

end

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem isMu_mmG (r : Res l K) (M : Model l K) (n : ℕ) {N : ℕ} (hT : Pb.Mid.TeichmullerCongruence r N) :
    IsMu r M n N (mm r M n hT) :=
  isMuG (B.schFn M.p) (b₀ := Wc.bs l r.k n) (b₁ := B.bs l true n) (h₀ := rfl) (h₁ := rfl) (Pb.Mid.wn r n) (l ^ N) _
    (Pb.Mid.mIn r M n hT) (Pb.Mid.wn_mk r n) (fun _ => rfl) (fun _ _ => rfl) (fun B₀ y φ hφ =>
      congrArg (fun g => (B.schFn M.p).Pt.map (CommRingCat.ofHom g) y.1.2)
        (RingHom.ext fun x => (Pb.Mid.frbN_apply _ N x).trans (hφ x).symm))

end CrystallineSemistableComparison.crystallineComparison.PinP

end
end

section -- merged from Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.TeichmullerRootsUnity.RootsUnityPullback.TeichDvd
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge

namespace CrystallineSemistableComparison.crystallineComparison.PinP

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem close_dvd (r : Res l K) [FiniteDimensional ℚ_[l] K] (f : ℕ) (hf : 0 < f) :
    ∃ N : ℕ, f ∣ N ∧ ∀ x : OK l K,
      ‖((okToOC l K x ^ l ^ N - PreTilt.untilt (r.s (r.ρ x)) : OC l) : ℂ_[l])‖ ≤ ‖(l : ℂ_[l])‖ := by
  obtain ⟨fr, hfr, hfz⟩ := Pb.G3.res_frob r
  obtain ⟨c, hc1, hc⟩ := Pb.G3.exists_teichmuller_close r
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0)
  have hl : (l : ℂ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (norm_pos_iff.2 hl) hc1
  have hN : ∀ (M : ℕ) (z : r.k), z ^ l ^ (fr * M) = z := by
    intro M z
    induction M with
    | zero => simp
    | succ M ih => rw [Nat.mul_succ, pow_add, pow_mul, ih, hfz]
  have hjN : j ≤ l ^ (fr * (f * j)) :=
    (Nat.lt_pow_self (Fact.out : l.Prime).one_lt).le.trans (Nat.pow_le_pow_right (Fact.out : l.Prime).pos
      ((Nat.le_mul_of_pos_left j hf).trans (Nat.le_mul_of_pos_left (f * j) hfr)))
  refine ⟨fr * (f * j), ⟨fr * j, by ring⟩, fun x => ?_⟩
  have ht : PreTilt.untilt (r.s (r.ρ x)) ^ l ^ (fr * (f * j)) = PreTilt.untilt (r.s (r.ρ x)) := by
    rw [← map_pow, ← map_pow, hN]
  have hp := Pb.G3.pow_close (okToOC l K x) (PreTilt.untilt (r.s (r.ρ x))) c (hc x) (fr * (f * j))
  rw [ht] at hp
  refine hp.trans (max_le le_rfl ?_)
  exact (pow_le_pow_of_le_one hc0 hc1.le hjN).trans hj.le

theorem teich_dvd (r : Res l K) [FiniteDimensional ℚ_[l] K] (f : ℕ) (hf : 0 < f) :
    ∃ N : ℕ, f ∣ N ∧ Pb.Mid.TeichmullerCongruence r N := by
  obtain ⟨N, hfN, hN⟩ := close_dvd r f hf
  refine ⟨N, hfN, fun n x => ?_⟩
  rw [Pb.Mid.phiQ_pow, Pb.G3.struct, ← Pb.G3.cong n _ _ (hN x)]
  rw [map_pow, map_pow]
  rfl

end CrystallineSemistableComparison.crystallineComparison.PinP
end
end

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.crystallineComparison

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem PinP.pin_of (r : Res l K) {N : ℕ} (hT : Pb.Mid.TeichmullerCongruence r N) (F : Pb.Fac r N) (M : Model l K) (j : ℕ)
    (hβ : ∀ (y : Pb.LW r M j) n, levH (F.β M j ((1 : Pb.AW r) ⊗ₜ y)) n = Pb.Mid.mu r M n j hT (Pb.bW r M n j (y.1 n))) :
    Pin F M j := fun n =>
  ⟨PinP.mm r M n hT, PinP.isMu_mmG r M n hT, fun y => (hβ y n).trans (PinP.mm_pull r M n j hT (y.1 n)).symm⟩

theorem PinP.pin_lev (r : Res l K) {N : ℕ} (hT : Pb.Mid.TeichmullerCongruence r N) (F : Pb.Fac r N) (hF : Pb.Pinned r hT F)
    (M : Model l K) (hM : M.Sm) (j : ℕ) (y : Pb.LW r M j) (n : ℕ) :
    levH (F.β M j ((1 : Pb.AW r) ⊗ₜ y)) n = Pb.Mid.mu r M n j hT (Pb.bW r M n j (y.1 n)) := by
  refine (congrArg (fun w => levH w n) ((hF M hM j).2 ((1 : Pb.AW r) ⊗ₜ y))).trans ?_
  change Pb.Mid.mu r M n j hT ((1 : Pb.AW r) • Pb.bW r M n j (y.1 n)) = _
  exact congrArg (Pb.Mid.mu r M n j hT) (one_smul _ _)

theorem PinP.pin_fixed (r : Res l K) [FiniteDimensional ℚ_[l] K] (f : ℕ) (hf : 0 < f) :
    ∃ N : ℕ, f ∣ N ∧ Pb.Mid.TeichmullerCongruence r N ∧ ∃ F : Pb.Fac r N, ∀ M : Model l K, M.Sm → ∀ j, Pin F M j := by
  obtain ⟨N, hfN, hT⟩ := PinP.teich_dvd r f hf
  obtain ⟨F, hF⟩ := Pb.fac_ex r hT (fun M n j x => Pb.Mid.mu_nu r N hT M n j x) (Pb.G3.w_phi r) (fun g w => Pb.G3.w_fix r g w)
  exact ⟨N, hfN, hT, F, fun M hM j => PinP.pin_of r hT F M j fun y n => PinP.pin_lev r hT F hF M hM j y n⟩

theorem pinEx : PinEx := fun _ _ _ _ r f hf => PinP.pin_fixed r f hf

end CrystallineSemistableComparison.crystallineComparison
