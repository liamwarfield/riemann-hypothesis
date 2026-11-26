module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSplitSupportProjectsVacuum
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThPBilinearHeis
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh

theorem theta_bilinear_heisenberg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (q0 : ℕ) (hq : X.p0 + q0 = r), ∀ x ∈ X.dom, ∀ φ : TF n g, GlobalTheory.SW.IsSB φ → ∀ P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n), (∀ φ' : TF n g, GlobalTheory.SW.IsSB φ' → ∀ a b : ℂ, thP X hq bas idx (a • φ + b • φ') P x = a * thP X hq bas idx φ P x + b * thP X hq bas idx φ' P x) ∧ (∀ (P' : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (a b : ℂ), thP X hq bas idx φ (a • P + b • P') x = a * thP X hq bas idx φ P x + b * thP X hq bas idx φ P' x) ∧ ∀ y : Matrix (Fin n) (Fin r) E, thP X hq bas idx (heisG X bas y φ) P x = ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P (letterDir X hq idx) (fun z => cexp (-(Real.pi * ∑ b, hx X bas idx x (z b + (1 / 2 : ℂ) • pv X idx x (y b)) (pv X idx x (y b)))) * thA X bas idx φ x (fun b => z b + pv X idx x (y b))) 0 := by
  intro E _ _ _ r g n X bas idx hs hn q0 hq x hd φ hφ P
  obtain ⟨h1, h2, h3⟩ := thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd φ hφ
  refine ⟨fun ψ hψ a b => ?_, fun Q a b => ?_, fun y => ?_⟩
  · have h4 := (thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd ψ hψ).2.1
    have e1 := GlobalTheory.Jet.polyDeriv_smul_fun P (letterDir X hq idx) h2 a 0
    have e2 := GlobalTheory.Jet.polyDeriv_smul_fun P (letterDir X hq idx) h4 b 0
    have e3 := GlobalTheory.Jet.polyDeriv_add_fun P (letterDir X hq idx) (h2.const_smul a) (h4.const_smul b) 0
    unfold thP
    rw [((h3 ψ hψ).1 a b).2, ← e1, ← e2]
    exact e3
  · unfold thP
    rw [ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_add, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul, ReciprocityTheory.ChartRestriction.G.I2.polyDeriv_smul]
  · unfold thP
    rw [funext fun z => (h1 y z).2]

end GlobalTheory.AdTh
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyDerivCompNeg
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.Parity

theorem polyDeriv_comp_neg {σ W : Type*} [NormedAddCommGroup W] [NormedSpace ℂ W] (P : MvPolynomial σ ℂ) (d : ℕ)
    (hP : P.IsHomogeneous d) (u : σ → W) (F : W → ℂ) :
    ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u (fun z => F (-z)) 0 = (-1) ^ d * ReciprocityTheory.ChartRestriction.G.I2.polyDeriv P u F 0 := by
  unfold ReciprocityTheory.ChartRestriction.G.I2.polyDeriv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hd : Multiset.card (Finsupp.toMultiset m) = d := by
    rw [Finsupp.card_toMultiset, ← hP (MvPolynomial.mem_support_iff.1 hm), Finsupp.weight_apply]
    simp only [Pi.one_apply, smul_eq_mul, mul_one]
    rfl
  have h := (ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W).iteratedFDerivWithin_comp_right F uniqueDiffOn_univ
    (x := 0) (Set.mem_univ _) (Multiset.card (Finsupp.toMultiset m))
  rw [Set.preimage_univ, iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at h
  have e : (fun z => F (-z)) = F ∘ (ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W) := rfl
  rw [e, h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]
  have e2 : ∀ t : W, ((ContinuousLinearEquiv.neg ℂ : W ≃L[ℂ] W) : W →L[ℂ] W) t = (-1 : ℂ) • t := fun t => by simp
  simp only [e2]
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  rw [← hd]
  ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} (idx : Fin g ≃ X.Ψ × Fin r)

def reflTF (n g : ℕ) : TF n g ≃+ TF n g where
  toFun φ := fun x => φ (-x)
  invFun φ := fun x => φ (-x)
  left_inv φ := by funext x; simp
  right_inv φ := by funext x; simp
  map_add' _ _ := rfl

theorem reflTF_smul (a : ℂ) (φ : TF n g) : reflTF n g (a • φ) = a • reflTF n g φ := rfl

theorem isSB_reflTF {φ : TF n g} (h : GlobalTheory.SW.IsSB φ) : GlobalTheory.SW.IsSB (reflTF n g φ) := by
  obtain ⟨R, hR, h1, h2⟩ := h
  refine ⟨R, hR, fun x hx k i => ?_, fun x y hy => ?_⟩
  · have := (h1 (-x) hx k i).neg
    simpa using this
  · have := h2 (-x) (-y) fun k i => (hy k i).neg
    change φ _ = φ _
    rw [← this, neg_add, smul_neg]

theorem thA_reflTF (φ : TF n g) (x : Frame X.Ψ r) (z : Fin n → Fin g → ℂ) :
    thA X bas idx (reflTF n g φ) x z = thA X bas idx φ x (-z) := by
  unfold thA thS
  congr 1
  · simp only [Pi.neg_apply, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]
  · rw [← (Equiv.neg (Matrix (Fin n) (Fin g) ℚ)).tsum_eq]
    refine tsum_congr fun y => ?_
    have e : ∀ k, qv ((-y) k) = -qv (y k) := fun k => by
      funext i
      simp [qv]
    have e' : reflTF n g φ (-y) = φ y := by
      change φ (- -y) = φ y
      rw [neg_neg]
    simp only [Equiv.neg_apply, e, e', Pi.neg_apply, mulVec_neg, neg_dotProduct, dotProduct_neg, neg_neg]

theorem reflTF_heisG (hs : IsSympl X bas) (y : Matrix (Fin n) (Fin r) E) (φ : TF n g) :
    reflTF n g (heisG X bas y φ) = heisG X bas (-y) (reflTF n g φ) := by
  have e : ∀ k, crd X bas ((-y) k) = -crd X bas (y k) := fun k => by
    have := crd_smul hs (-1) (y k)
    rw [neg_one_smul, neg_one_smul] at this
    exact this
  funext x
  change heisS _ _ φ (-x) = φ _ * _
  unfold heisS
  congr 2
  · ext k i
    simp [e]
    ring
  · congr 2
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [e, dotProduct]

theorem EF_neg_smul_neg (w : E) (u : Fin r → E) : EF X (-u) (w • -u) = EF X u (w • u) := by
  change EFBil X _ _ = EFBil X _ _
  simp

theorem epsW_neg (w : E) (y : Matrix (Fin n) (Fin r) E) : epsW X w (-y) = epsW X w y := by
  have e : ∀ k, (-y) k = -(y k) := fun _ => rfl
  simp only [epsW, e, EF_neg_smul_neg]

theorem reflTF_projA (hs : IsSympl X bas) (w : E) (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) {φ : TF n g}
    (hφ : reflTF n g φ = φ) : reflTF n g (projA X bas w A φ) = projA X bas w A φ := by
  unfold projA
  rw [reflTF_smul]
  congr 1
  have hm : Set.MapsTo (reflTF n g) ((fun y => epsW X w y • heisG X bas y φ) '' A)
      ((fun y => epsW X w y • heisG X bas y φ) '' A) := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨-y, A.neg_mem hy, by simp only [reflTF_smul, reflTF_heisG hs, hφ, epsW_neg]⟩
  have hi : ∀ ψ, reflTF n g (reflTF n g ψ) = ψ := (reflTF n g).left_inv
  rw [AddEquiv.map_finsum]
  simp only [AddEquiv.map_finsum]
  exact finsum_mem_eq_of_bijOn (reflTF n g)
    ⟨hm, (reflTF n g).injective.injOn, fun ψ hψ => ⟨_, hm hψ, hi ψ⟩⟩ fun _ _ => rfl

theorem isTheta1_neg {w : E} {x : Frame X.Ψ r} {L : Lt E r} {θ : (Fin g → ℂ) → ℂ}
    (h : IsTheta1 X bas idx w x L θ) : IsTheta1 X bas idx w x L fun z => θ (-z) := by
  refine ⟨h.1.comp differentiable_id.neg, fun v hv => ?_⟩
  funext z
  have := congrFun (h.2 (-v) (L.neg_mem hv)) (-z)
  have e : pv X idx x (-v) = -pv X idx x v := by
    unfold pv
    rw [per_neg]
    rfl
  simp only [Pi.smul_apply, fock, eps1, EF_neg_smul_neg, e] at this ⊢
  rw [← this, smul_neg, ← neg_add, ← neg_add]
  simp only [hx, mulVec_neg, star_neg, neg_dotProduct, dotProduct_neg, neg_neg]

theorem isTheta1_update (hs : IsSympl X bas) (hn : Even n) {w : E} {L : Lt E r} {v : TF n g}
    (hv : IsVac X bas w (tens (stdL E n) L) v) {x : Frame X.Ψ r} (hd : x ∈ X.dom) (z₀ : Fin n → Fin g → ℂ) (b : Fin n) :
    IsTheta1 X bas idx w x L fun t => thA X bas idx v x (Function.update z₀ b t) := by
  obtain ⟨h1, h2, h3⟩ := thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd v hv.1
  refine ⟨h2.comp (differentiable_pi.2 fun k => ?_), fun u hu => ?_⟩
  · by_cases hk : k = b
    · subst hk
      simp only [Function.update_self]
      exact differentiable_id
    · simp only [Function.update_of_ne hk]
      exact differentiable_const _
  · funext t
    set y : Matrix (Fin n) (Fin r) E := Pi.single b u with hy
    have hyb : y b = u := Pi.single_eq_same _ _
    have hyk : ∀ k, k ≠ b → y k = 0 := fun k hk => Pi.single_eq_of_ne hk _
    have hm : y ∈ tens (stdL E n) L := (TensLat.mem_tens_stdL L _).2 fun k => by
      by_cases hk : k = b
      · rw [hk, hyb]; exact hu
      · rw [hyk k hk]; exact L.zero_mem
    have hp : pv X idx x 0 = 0 := by
      unfold pv
      rw [per_zero]
      rfl
    have e1 : epsW X w y = eps1 X w u := by
      unfold epsW eps1
      rw [Finset.sum_eq_single b, hyb]
      · intro k _ hk
        rw [hyk k hk]
        change EFBil X _ _ = 0
        simp
      · simp
    have e2 := (h1 y (Function.update z₀ b t)).2
    rw [Finset.sum_eq_single b, hyb, Function.update_self] at e2
    · have e3 : (fun k => Function.update z₀ b t k + pv X idx x (y k)) = Function.update z₀ b (t + pv X idx x u) := by
        funext k
        by_cases hk : k = b
        · rw [hk, hyb, Function.update_self, Function.update_self]
        · rw [hyk k hk, hp, add_zero, Function.update_of_ne hk, Function.update_of_ne hk]
      rw [e3] at e2
      conv_rhs => rw [← hv.2.2 y hm, GlobalTheory.SW.UnAct.thA_smul]
      simp only [Pi.smul_apply, fock, e1, e2, Nat.cast_one, _root_.one_mul]
    · intro k _ hk
      rw [hyk k hk, hp]
      simp [hx]
    · simp


include idx in
theorem reflTF_vac (hs : IsSympl X bas) (hn : Even n) {w : E} (hw : IsIntegral ℤ w) (hw' : w + cc w = 1) {L : Lt E r}
    (hL : SelfD X L) {v : TF n g} (hv : IsVac X bas w (tens (stdL E n) L) v) {x : Frame X.Ψ r} (hd : x ∈ X.dom) :
    reflTF n g v = v := by
  refine (((thA_heis_entire_linear_injective E r g n X bas idx hs hn x hd v hv.1).2.2 _ (isSB_reflTF hv.1)).2 ?_).symm
  funext z
  rw [thA_reflTF]
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · rw [Subsingleton.elim (-z) z]
  by_cases h0 : thA X bas idx v x = 0
  · simp [h0]
  obtain ⟨z₀, hz₀⟩ := Function.ne_iff.1 h0
  have hθ := isTheta1_update idx hs hn hv hd z₀ ⟨0, hpos⟩
  set θ := fun t => thA X bas idx v x (Function.update z₀ ⟨0, hpos⟩ t) with hθd
  have ht : θ (z₀ ⟨0, hpos⟩) ≠ 0 := by simpa [hθd] using hz₀
  obtain ⟨a, ha⟩ := GlobalTheory.Dict.ThetaOne.exists_eq_smul_of_isTheta1 E r X g bas idx n hs hn w hw hw' L hL x hd _ θ
    (isTheta1_neg idx hθ) hθ (Function.ne_iff.2 ⟨_, ht⟩)
  have ha' : ∀ t, θ (-t) = a * θ t := congrFun ha
  have haa : a ^ 2 = 1 := by
    have := ha' (-z₀ ⟨0, hpos⟩)
    rw [neg_neg, ha'] at this
    exact mul_right_cancel₀ ht (by linear_combination -this)
  obtain ⟨κ, hκ⟩ := GlobalTheory.Dict.VacProd.prod_eq_mul_thA E r X g bas idx n hs hn w hw hw' L hL v hv x hd θ hθ
  have hκ0 : κ ≠ 0 := by
    rintro rfl
    have := hκ fun _ => z₀ ⟨0, hpos⟩
    rw [zero_mul] at this
    exact Finset.prod_ne_zero_iff.2 (fun _ _ => ht) this
  refine mul_left_cancel₀ hκ0 ?_
  rw [← hκ, ← hκ]
  obtain ⟨m, hm⟩ := hn
  have : a ^ n = 1 := by rw [hm, ← two_mul, pow_mul, haa, one_pow]
  simp only [Pi.neg_apply, ha', Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, this,
    _root_.one_mul]

theorem thP_gphi_neg : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r g n : ℕ) (X : Data E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r), IsSympl X bas → Even n → ∀ (q0 : ℕ) (hq : X.p0 + q0 = r) (w : E), IsIntegral ℤ w → w + cc w = 1 → ∀ L : Lt E r, SelfD X L → ∀ v : TF n g, IsVac X bas w (tens (stdL E n) L) v → ∀ Λ : Formalism.L2.Pj.GenLat E n, Λ.Unimod → Λ.La.FG → ∀ (Q : Type) [Fintype Q] (c : Q → ℂ) (Y : Q → Matrix (Fin n) (Fin r) E) (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) (d : ℕ), P.IsHomogeneous d → ∀ x ∈ X.dom, thP X hq bas idx (gphi X bas w Λ.La L v c (fun q => -Y q)) P x = (-1) ^ d * thP X hq bas idx (gphi X bas w Λ.La L v c Y) P x := by
  intro E _ _ _ r g n X bas idx hs hn q0 hq w hw hw' L hL v hv Λ _ _ Q _ c Y P d hP x hd
  have h1 := reflTF_projA hs w (tens Λ.La L) (reflTF_vac idx hs hn hw hw' hL hv hd)
  have h2 : gphi X bas w Λ.La L v c (fun q => -Y q) = reflTF n g (gphi X bas w Λ.La L v c Y) := by
    unfold gphi
    rw [AddEquiv.map_finsum]
    simp only [reflTF_smul, reflTF_heisG hs, h1]
  unfold thP
  rw [h2, ← polyDeriv_comp_neg P d hP]
  congr 1
  funext z
  exact thA_reflTF idx _ x z

end GlobalTheory.AdTh.Parity
end

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.ShortSeries

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem heisG_smul (y : Matrix (Fin n) (Fin r) E) (c : ℂ) (φ : TF n g) :
    heisG X bas y (c • φ) = c • heisG X bas y φ := by
  funext x
  simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem projA_smul (w : E) (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) (a : ℂ) (φ : TF n g) :
    projA X bas w A (a • φ) = a • projA X bas w A φ := by
  by_cases ha : a = 0
  · subst ha
    have h0 : ∀ y : Matrix (Fin n) (Fin r) E, heisG X bas y (0 : TF n g) = 0 := fun y => by
      have := heisG_smul (X := X) (bas := bas) y 0 (0 : TF n g)
      rwa [zero_smul, zero_smul] at this
    rw [zero_smul, zero_smul, projA, finsum_mem_eq_zero_of_forall_eq_zero, smul_zero]
    rintro _ ⟨y, -, rfl⟩
    simp only [h0, smul_zero]
  have hi : Function.Injective fun ψ : TF n g => a • ψ := smul_right_injective _ ha
  have e : (fun y => epsW X w y • heisG X bas y (a • φ)) '' A =
      (fun ψ : TF n g => a • ψ) '' ((fun y => epsW X w y • heisG X bas y φ) '' A) := by
    rw [Set.image_image]
    congr 1
    funext y
    rw [heisG_smul, smul_comm]
  unfold projA
  rw [e, Set.ncard_image_of_injective _ hi, finsum_mem_image hi.injOn, smul_comm a]
  congr 1
  rw [smul_finsum]
  simp only [smul_finsum]

theorem theta_smul₂ (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {q0 : ℕ} (hq : X.p0 + q0 = r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (c : ℂ) (φ : TF n g) (h : GlobalTheory.SW.IsSB (c • φ))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) : thP X hq bas idx (c • φ) P x = c * thP X hq bas idx φ P x := by
  have key : ∀ (a : ℂ) (ψ : TF n g), GlobalTheory.SW.IsSB ψ → thP X hq bas idx (a • ψ) P x = a * thP X hq bas idx ψ P x := by
    intro a ψ hψ
    have := (theta_bilinear_heisenberg E r g n X bas idx hs hn q0 hq x hx ψ hψ P).1 ψ hψ a 0
    rwa [zero_smul, add_zero, zero_mul, add_zero] at this
  by_cases hc : c = 0
  · have := key 0 _ h
    rw [zero_smul] at this
    rw [hc, zero_smul, this, zero_mul, zero_mul]
  · refine key c φ ?_
    have := (isSB_algebra_haar_linear ℚ _ _ _ _ h h).2.1 c⁻¹
    rwa [inv_smul_smul₀ hc] at this

theorem finite_levQ {H : Geo.Tor.Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem cmHost_idempotent_trace_eq_one (H : Geo.Tor.Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  rw [cc, ← H.bar_eq]
  exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)

end Classical

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {r g : ℕ}

theorem isInvOf_move (hr : W.rank = r) (X : Data D.host.E r) {x : Frame X.Ψ r}
    {s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hs : IsInvOf W hr X x s) (k : GA D W) :
    IsInvOf W hr X (frMove θ W hr X k x)
      fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * s τ * compAt θ τ (Formalism.L2.Theta.mt W k⁻¹) := by
  subst hr
  intro ρ τ hτ
  have h := hs ρ τ hτ
  have e : mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
    rw [← RealCoord.realM_tauE, ← hτ]
    rfl
  change s ρ * mat x τ = _ at h
  change (compAt θ ρ (Formalism.L2.Theta.mt W k) * s ρ * compAt θ ρ (Formalism.L2.Theta.mt W k⁻¹)) * _ = _
  rw [e, Matrix.mul_assoc, ← Matrix.mul_assoc (compAt θ ρ (Formalism.L2.Theta.mt W k⁻¹)),
    GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_neg, Matrix.mul_assoc]

theorem isBasOf_move (hr : W.rank = r) (X : Data D.host.E r) {q0 : ℕ} (hq : X.p0 + q0 = r) {x : Frame X.Ψ r}
    {B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hB : IsBasOf W hr X hq x B) (k : GA D W) :
    IsBasOf W hr X hq (frMove θ W hr X k x) fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * B τ := by
  subst hr
  intro ρ τ hτ j i a hi
  have e : mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
    rw [← RealCoord.realM_tauE, ← hτ]
    rfl
  refine Eq.trans ?_ (congrFun (congrFun e a) (rowIdx hq j)).symm
  simp only [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun b _ => congrArg _ (hB ρ τ hτ j i b hi)

theorem isONFr_move (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : V.gram = 1) (he : Even V.rank) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {x : Frame X.Ψ r} (hx : IsONFr X x) (k : GA D W) : IsONFr X (frMove θ W hr X k x) := by
  subst hr
  obtain ⟨X', m, hq', hq, bas', idx', hs, -, -, -, -, -, -, hfr⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hψ hθ he hV hM hS
  obtain ⟨⟨B, hB⟩, hBx⟩ := hfr x hx
  obtain ⟨-, -, -, -, -, -, -, hmv, -⟩ := hBx B hB
  exact (hmv k).1

theorem reads_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : V.gram = 1) (he : Even V.rank) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {x : Frame X.Ψ r} (hx : IsONFr X x) {f : WO V W → ℂ} {φ : TF V.rank g}
    (hf : IsThetaFunO ψ V W f) (hR : Reads θ V W hr X bas idx f φ x) {Q : Type} (c : Q → ℂ)
    (γ : Q → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : Q → WO V W) (hu : ∀ q, IsFinOf V W (γ q) (u q))
    (s : Finset Q) :
    IsThetaFunO ψ V W (∑ q ∈ s, c q • heisO ψ V W (u q) f) ∧
      Reads θ V W hr X bas idx (∑ q ∈ s, c q • heisO ψ V W (u q) f)
        (∑ q ∈ s, c q • heisG X bas (-(colsR hr (γ q))) φ) x := by
  have hlin := reads_linear_injective D ψ θ V W r g hr X bas idx hψ hθ hV he hM hS x hx
  induction s using Finset.induction_on with
  | empty =>
    have := (hlin _ _ _ _ hR hR).1 0 0
    simp only [zero_smul, add_zero] at this
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, this⟩
  | insert q s hq ih =>
    rw [Finset.sum_insert hq, Finset.sum_insert hq]
    have h1 := reads_heisO_finOf D ψ θ V W r g hr X bas idx hψ hθ hV he hM hS x hx f φ hf hR _ _ (hu q)
    have := (hlin _ _ _ _ h1 ih.2).1 (c q) 1
    rw [one_smul, one_smul] at this
    exact ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (hu q).1)) ih.1, this⟩

theorem kernel_of_reads {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {q0 : ℕ} (hq : X.p0 + q0 = r) {x : Frame X.Ψ r} (hx : IsONFr X x)
    {s B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hs : IsInvOf W hr X x s) (hB : IsBasOf W hr X hq x B)
    {vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank} (hvr : IsVarOf V W X q0 vr)
    {h : GA D V} (hh : h ∈ GfC V) (k : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) {φ : TF V.rank g}
    (hR : Reads θ V W hr X bas idx (om (h, k) f) φ (frMove θ W hr X k x))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) (d : ℕ) (hd : P.IsHomogeneous d) :
    thetaKO om h k (pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) B f (MvPolynomial.rename vr P)) =
      ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * thP X hq bas idx φ P (frMove θ W hr X k x) := by
  have h1 := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χV χW om hP.weil hP.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) s (fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * s τ * compAt θ τ (Formalism.L2.Theta.mt W k⁻¹)) B
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * B τ) h k
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.mul_one])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ V hh, Matrix.mul_one]) (fun _ => rfl) f hf
    (MvPolynomial.rename vr P)).2
  rw [thetaKO, h1]
  exact GlobalTheory.T.fock_pure_tensor_at_origin_eq_theta_series D ψ θ V W r g hr X bas idx hP.weil.std hP.inf hP.std hP.even hM hS q0 hq _ _ _ vr
    (isONFr_move hP.weil.std hP.inf hP.std hP.even hr X bas idx hM hS hx k) (isInvOf_move hr X hs k)
    (isBasOf_move hr X hq hB k) hvr _ φ (hP.weil.om_pres _ _ hf) hR P d hd

theorem exists_finOf (V W : HSp D) (hr : W.rank = r) (y : Matrix (Fin V.rank) (Fin r) D.host.E) :
    ∃ p : Matrix (Fin W.rank) (Fin V.rank) D.host.E × WO V W, colsR hr p.1 = y ∧ IsFinOf V W p.1 p.2 := by
  subst hr
  exact ⟨(yᵀ, GlobalTheory.LatVac.finTens 1 yᵀ), rfl, (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl⟩


end GlobalTheory.AdTh.ShortSeries
