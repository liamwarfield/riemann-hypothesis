module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TripleFrameBaseExists
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LsumMapDomainSome
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.HoweConditionActionCoinvariantsFock
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleMapCompInverseFinite
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaTripleIrreducibleAtRealPlace

@[expose] public section

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TripleExistsMatching
section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsMatchingTripleForThetaLift
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
namespace GlobalTheory.TripleAssembly
theorem triple_exists_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ∃ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  intro hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have sA := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D ψ θ hψ hθ true W X A B β (β / α) ωA hA
  have sB := GlobalTheory.T.fockAlgebraicThetaVectors_stable_finiteAdeles_lie D ψ θ hψ hθ false W₁ X A₁ B α (α / β) ωB hB
  obtain ⟨oA, oB⟩ := _root_.GlobalTheory.T.triple_algebra_map_surjective hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨iA, iB⟩ := _root_.GlobalTheory.T.triple_assembly_inverse_finite hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨lA, lB⟩ := _root_.GlobalTheory.T.theta_triple_lift_lie_invariant hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨fA, fB⟩ := _root_.GlobalTheory.T.theta_triple_maps_equivariant hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  obtain ⟨dA, dB⟩ := _root_.GlobalTheory.T.theta_triple_lift_lie_equivariant hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  have ir := _root_.GlobalTheory.T.theta_triple_lift_irreducible hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h hTA hTB R Rf hM
  exact ⟨ModuleCat.of ℂ (GlobalTheory.TripleAssembly.PiT R Γ Rf), _, _, _, _,
    ⟨hA, hB, ir, ⟨sA.1, sA.2, oA, iA, lA, fA, dA⟩, ⟨sB.1, sB.2, oB, iB, lB, fB, dB⟩⟩⟩
end GlobalTheory.TripleAssembly
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_matching_triple_for_theta_lift : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs →
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
    ∀ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
      (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
      (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
      (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc),
      GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) →
      GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) →
      ∀ R Rf, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
        ∃ Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  first | exact @_root_.GlobalTheory.TripleAssembly.triple_exists_matching | exact _root_.GlobalTheory.TripleAssembly.triple_exists_matching | (intros; apply _root_.GlobalTheory.TripleAssembly.triple_exists_matching <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ExistsDarbouxCoordinatesTriple
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
noncomputable section
namespace GlobalTheory.TripleDarboux
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model)
open GlobalTheory.WeilSchrodinger
end GlobalTheory.TripleDarboux
namespace GlobalTheory.TripleDarboux
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)
end GlobalTheory.TripleDarboux
namespace GlobalTheory.TripleDarboux
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model SplitsFully Chars HasExp)
theorem exists_darboux_basis_of_triple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
      ∃ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
        (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
        (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' ∧
        GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) ∧
        GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) := by
  intro _ D ψ hψ W W₁ X A A₁ B α β h ωA ωB hA hB
  classical
  let e : Fin (W.rank + W₁.rank) ≃ Fin X.rank := finCongr h.rank.symm
  choose τf hτf using (GlobalTheory.ConjTypeOverReal.conj_tauE_over_realPlace (D := D))
  choose a b ha hb hab using h.gap
  obtain ⟨mα, hα, eα⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp α a ha τf hτf
  obtain ⟨mβ, hβ, eβ⟩ := GlobalTheory.ConjInfExp.hasExp_conj_of_hasInfExp β b hb τf hτf
  obtain ⟨T, hT1, hT2, hT3⟩ := exists_ram_set h
  obtain ⟨v₁, hv₁, hv₁s, ⟨τ₁⟩⟩ := exists_good_place D T
  let Bs : Base D.host.F D.host.E :=
    ⟨ψ, fun w => ⟨_, hτf w⟩, mα, mβ, T, fun v => (hT1 v v.2).1.some, v₁, τ₁⟩
  have hBs : Bs.IsGood D.sp.cm.sig := base_isGood Bs hψ fun v hv => (hT1 v hv).2
  have hemb : ∀ w x, (Bs.emb w).1 x = conj (tauE D (τf w) x) := fun _ _ => rfl
  obtain ⟨p, q, hsig, hn1, hn2⟩ := h.sig
  have hneg : ∀ τ, gramAt D (sgn true W) τ = -gramAt D W τ := fun τ => by ext i j; simp [gramAt, neg_gram]
  obtain ⟨ΛV, basV, hV⟩ := exists_isHerm Bs τf hemb (sgn true W) (fun τ => sgnM true (A.cart τ))
    (fun τ => isCartanInv_sgn true W τ (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A τ))
    (fun τ => by rw [hneg]; exact hasSignature_neg (hsig τ).1)
  have eJ : (-1 : D.host.E) • (sgn true W).gram = (1 : D.host.E) • W.gram := by
    rw [neg_gram, neg_smul, one_smul, one_smul, neg_neg]
  have eθ : (fun w => -sgnM true (A.cart (τf w))) = fun w => A.cart (τf w) := funext fun w => neg_neg _
  rw [eJ, eθ] at hV
  obtain ⟨ΛV', basV', hV'⟩ := exists_isHerm Bs τf hemb W₁ A₁.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv A₁)
    fun τ => (hsig τ).2.1
  obtain ⟨ΛX, basX, hX⟩ := exists_isSkew Bs τf hemb X e B.cart (GlobalTheory.ArchRec.LieAtPlace.cart_isCartanInv B)
    fun τ => (hsig τ).2.2
  have e3 : X.rank - (p + q) = W.rank + W₁.rank - (p + q) := by rw [h.rank]
  rw [e3] at hX
  obtain ⟨Mo, hMo⟩ := exists_model Bs hBs W _ _ hV hX 1 one_ne_zero rfl
  obtain ⟨Mo', hMo'⟩ := exists_model Bs hBs W₁ _ _ hV' hX (-1) (neg_ne_zero.2 one_ne_zero) rfl
  obtain ⟨om, hom, htr⟩ := exists_weil Bs hBs true W X e _ _ hV hX 1 rfl (by rw [neg_gram, one_smul, neg_neg]) rfl Mo hMo hA
  obtain ⟨om', hom', htr'⟩ := exists_weil Bs hBs false W₁ X e _ _ hV' hX (-1) rfl (neg_one_smul _ _) rfl Mo' hMo' hB
  have hr := h.rank
  have hev := h.even
  have h2 : Module.finrank D.host.F D.host.E = 2 := D.sp.cm.deg2
  have hTe : (⟨α, β, T, ∅⟩ : Chars D.host.F D.host.E).T = T := by simp [Chars.T]
  refine ⟨e, Bs, ⟨p, q, _, _, _, Mo, Mo'⟩, ⟨α, β, T, ∅⟩, om, om',
    ⟨rfl, rfl, rfl, rfl, fun w => ⟨τf w, fun _ => rfl, rfl, rfl, rfl⟩, rfl, rfl⟩, ⟨hBs, ?_, ?_, hom, hom'⟩, htr, htr'⟩
  · refine ⟨by omega, hr ▸ hev, fun w => ?_, ?_, hn2, hV, hV', hX, hMo, hMo'⟩
    · have h1 := eα w
      have h3 := eβ w
      have h4 := hab (τf w)
      rw [hr] at h4
      have : (((W.rank + W₁.rank : ℕ) : ℤ) : ℚ) < ((mα w - mβ w : ℤ) : ℚ) := by
        push_cast at h4 ⊢
        rw [h1, h3]
        linarith
      exact_mod_cast this
    · obtain ⟨m, hm⟩ := hev
      show 2 * (p + q) + 1 < (W.rank - W₁.rank) / 2
      omega
  · refine ⟨h.hecA, h.hecB, GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resA),
      GlobalTheory.LFun.resEtaPow_of_resEta _ _ h2 _ _ ((GlobalTheory.LFun.resEta_iff _ _).1 h.resB), hα, hβ, Finset.disjoint_empty_right _,
      hTe.le, fun w hw => hT2 w (hTe ▸ hw), fun w hw => (hT3 w fun h0 => hw ?_).1, fun w hw => (hT3 w fun h0 => hw ?_).2,
      ⟨hTe.symm ▸ hv₁, hv₁s⟩⟩
    · rw [hTe]; exact h0
    · rw [hTe]; exact h0
end GlobalTheory.TripleDarboux
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_darboux_coordinates_triple : _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ (ωA : WRep W X) (ωB : WRep W₁ X), IsWeil ψ true W X β (β / α) ωA → IsWeil ψ false W₁ X α (α / β) ωB →
      ∃ (e : Fin (W.rank + W₁.rank) ≃ Fin X.rank) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E)
        (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo D.sp.cm.sig W.rank W₁.rank) (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars D.host.F D.host.E)
        (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W)
        (h : GlobalTheory.TripleRead.IsReading ψ A A₁ B α β e Bs Γ Xc), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ Xc om om' ∧
        GlobalTheory.TripleRead.IsTransp ψ true Γ.M om ωA e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W 1 h.JW) (GlobalTheory.TripleRead.toUX X e h.JX) ∧
        GlobalTheory.TripleRead.IsTransp ψ false Γ.M' om' ωB e (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.conjU W₁ (-1) h.JW₁) (GlobalTheory.TripleRead.toUX X e h.JX) := by
  first | exact @_root_.GlobalTheory.TripleDarboux.exists_darboux_basis_of_triple | exact _root_.GlobalTheory.TripleDarboux.exists_darboux_basis_of_triple | (intros; apply _root_.GlobalTheory.TripleDarboux.exists_darboux_basis_of_triple <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.TripleRead
theorem triple_exists_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
      ∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  intro hH hP _ hLM D ψ θ hψ hθ W W₁ X A A₁ B α β hT
  obtain ⟨ωA, ωB, hA, hB⟩ := _root_.GlobalTheory.T.weilRepresentation_square_comm hP D ψ hψ W W₁ X α β hT
  obtain ⟨e, Bs, Γ, Xc, om, om', h, hTr, htA, htB⟩ := _root_.GlobalTheory.T.exists_darboux_coordinates_triple hP D ψ hψ W W₁ X A A₁ B α β hT ωA ωB hA hB
  obtain ⟨R, Rf, hM⟩ := hLM D.host.F D.host.E D.sp.cm.sig Bs W.rank W₁.rank Γ Xc om om' hTr
  obtain ⟨Pi, rf, rl, p, p', hm⟩ :=
    _root_.GlobalTheory.T.exists_matching_triple_for_theta_lift hH hP D ψ θ hψ hθ W W₁ X A A₁ B α β hT ωA ωB hA hB e Bs Γ Xc om om' h htA htB R Rf hM
  exact ⟨ωA, ωB, Pi, rf, rl, p, p', hm⟩
end GlobalTheory.TripleRead
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twist_triple_matches : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
      ∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' := by
  first | exact @_root_.GlobalTheory.TripleRead.triple_exists_matching | exact _root_.GlobalTheory.TripleRead.triple_exists_matching | (intros; apply _root_.GlobalTheory.TripleRead.triple_exists_matching <;> assumption)
end
end

section -- merged from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedQuotientReal
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.RealQuot
theorem twist_quotient_isReal : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
    ∃ (Pr : ModuleCat.{0} ℂ) (ρ : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pr)
      (q : PolF D X.rank W.rank →ₗ[ℂ] Pr) (q' : PolF D X.rank W₁.rank →ₗ[ℂ] Pr),
      Function.Surjective q ∧ Function.Surjective q' ∧ Module.rank ℂ Pr ≤ Cardinal.aleph0 ∧
      (∀ N : Submodule ℂ Pr, (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, ρ τ Y x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
        ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
          (∀ f, IsFinF ψ θ true A B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p (fockF ψ θ true A B f P) = φ (q P)) ∧
          ∀ f, IsFinF ψ θ false A₁ B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p' (fockF ψ θ false A₁ B f P) = φ (q' P) := by
  intro hH hP _ _ D ψ θ hψ hθ W W₁ X A A₁ B a b
  classical
  let ρA : LieIx X → Module.End ℂ (PolF D X.rank W.rank) := fun i => actT true A B b i.1.1 i.1.2
  let CA := coinv true A B (fun τ => b τ - a τ)
  let ρB : LieIx X → Module.End ℂ (PolF D X.rank W₁.rank) := fun i => actT false A₁ B a i.1.1 i.1.2
  let CB := coinv false A₁ B (fun τ => a τ - b τ)
  have fam : ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
      ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
      let σ : LieIx X → Module.End ℂ Pi := fun i => rl i.1.1 i.1.2
      let βA : {f // IsFinF ψ θ true A B f} → PolF D X.rank W.rank →ₗ[ℂ] Pi := fun f => p ∘ₗ fockF ψ θ true A B f.1
      let βB : {f // IsFinF ψ θ false A₁ B f} → PolF D X.rank W₁.rank →ₗ[ℂ] Pi := fun f => p' ∘ₗ fockF ψ θ false A₁ B f.1
      ((∀ f i, βA f ∘ₗ ρA i = σ i ∘ₗ βA f) ∧ (∀ f, CA ≤ LinearMap.ker (βA f)) ∧
        (∀ (j : {h // h ∈ GfC X}) f, ∃ f', rf j.1 ∘ₗ βA f = βA f') ∧ (⨆ f, LinearMap.range (βA f)) = ⊤) ∧
      ((∀ f i, βB f ∘ₗ ρB i = σ i ∘ₗ βB f) ∧ (∀ f, CB ≤ LinearMap.ker (βB f)) ∧
        (∀ (j : {h // h ∈ GfC X}) f, ∃ f', rf j.1 ∘ₗ βB f = βB f') ∧ (⨆ f, LinearMap.range (βB f)) = ⊤) ∧
      (∀ N : Submodule ℂ Pi, IsStab σ N → IsStab (fun j : {h // h ∈ GfC X} => rf j.1) N → N = ⊥ ∨ N = ⊤) ∧
      HoweCond ρA CA ∧ HoweCond ρB CB ∧ Nontrivial Pi := by
    intro α β htr hexp ωA ωB Pi rf rl p p' hm
    have hexpA : ∀ τ, HasInfExp D β τ (b τ) ∧ HasInfExp D (β / α) τ (b τ - a τ) :=
      fun τ => ⟨(hexp τ).2, hasInfExp_div D α β τ _ _ (hexp τ).1 (hexp τ).2⟩
    have hexpB : ∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D (α / β) τ (a τ - b τ) :=
      fun τ => ⟨(hexp τ).1, hasInfExp_div D β α τ _ _ (hexp τ).2 (hexp τ).1⟩
    obtain ⟨oA1, oA2, oA3⟩ := GlobalTheory.T.orientedPair_fockMaps_lie_equivariant D ψ θ hθ true W X A B β (β / α) ωA b (fun τ => b τ - a τ) hm.weilA hexpA Pi rf rl p hm.mapA
    obtain ⟨oB1, oB2, oB3⟩ := GlobalTheory.T.orientedPair_fockMaps_lie_equivariant D ψ θ hθ false W₁ X A₁ B α (α / β) ωB a (fun τ => a τ - b τ) hm.weilB hexpB Pi rf rl p' hm.mapB
    have hspan : ∀ {M : HSp D} {ε : Bool} {A' : Fr M} (pp : (WO M X → ℂ) →ₗ[ℂ] Pi), (algF ψ θ ε A' B).map pp = ⊤ →
        (⨆ f : {f // IsFinF ψ θ ε A' B f}, LinearMap.range (pp ∘ₗ fockF ψ θ ε A' B f.1)) = ⊤ := by
      intro M ε A' pp h
      rw [eq_top_iff, ← h, algF, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨f, P, hf, rfl⟩, rfl⟩
      exact Submodule.mem_iSup_of_mem ⟨f, hf⟩ ⟨P, rfl⟩
    refine ⟨⟨fun f i => LinearMap.ext fun P => oA1 f.1 f.2 i.1.1 i.1.2 i.2 P,
        fun f P hP => oA2 f.1 f.2 P hP, fun j f => ?_, hspan p hm.mapA.onto⟩,
      ⟨fun f i => LinearMap.ext fun P => oB1 f.1 f.2 i.1.1 i.1.2 i.2 P,
        fun f P hP => oB2 f.1 f.2 P hP, fun j f => ?_, hspan p' hm.mapB.onto⟩,
      fun N h1 h2 => hm.irred.2 N (fun g hg x hx => h2 ⟨g, hg⟩ x hx) (fun τ Y hY x hx => h1 ⟨(τ, Y), hY⟩ x hx),
      _root_.GlobalTheory.T.howe_condition_of_fock_coinvariants hH hP D ψ θ hψ hθ true W X A B β (β / α) ωA b _ hm.weilA hexpA,
      _root_.GlobalTheory.T.howe_condition_of_fock_coinvariants hH hP D ψ θ hψ hθ false W₁ X A₁ B α (α / β) ωB a _ hm.weilB hexpB, hm.irred.1⟩
    · obtain ⟨f', hf', e⟩ := oA3 j.1 j.2 f.1 f.2
      exact ⟨⟨f', hf'⟩, LinearMap.ext fun P => e P⟩
    · obtain ⟨f', hf', e⟩ := oB3 j.1 j.2 f.1 f.2
      exact ⟨⟨f', hf'⟩, LinearMap.ext fun P => e P⟩
  by_cases hex : ∃ α β, IsTriple W W₁ X α β ∧ (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) ∧
      ∃ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p'
  swap
  · refine ⟨ModuleCat.of ℂ PUnit, fun _ _ => 0, 0, 0, fun _ => ⟨0, Subsingleton.elim _ _⟩,
      fun _ => ⟨0, Subsingleton.elim _ _⟩, ?_, fun N _ => Or.inl (Submodule.eq_bot_of_subsingleton), ?_⟩
    · show Module.rank ℂ PUnit ≤ _
      simp
    · intro α β htr hexp ωA ωB Pi rf rl p p' hm
      exact absurd ⟨α, β, htr, hexp, ωA, ωB, Pi, rf, rl, p, p', hm⟩ hex
  obtain ⟨α₀, β₀, htr₀, hexp₀, ωA₀, ωB₀, Pi₀, rf₀, rl₀, p₀, p₀', hm₀⟩ := hex
  obtain ⟨⟨iA, kA, cA, sA⟩, ⟨iB, kB, cB, sB⟩, irr₀, hHA, hHB, hnt⟩ := fam α₀ β₀ htr₀ hexp₀ ωA₀ ωB₀ Pi₀ rf₀ rl₀ p₀ p₀' hm₀
  set σ₀ : LieIx X → Module.End ℂ Pi₀ := fun i => rl₀ i.1.1 i.1.2
  have nz : ∀ {Fm Q : Type} [AddCommGroup Q] [Module ℂ Q] (β : Fm → Q →ₗ[ℂ] Pi₀), (⨆ f, LinearMap.range (β f)) = ⊤ →
      ∃ f, β f ≠ 0 := by
    intro Fm Q _ _ β h
    by_contra hc
    push_neg at hc
    have : (⊤ : Submodule ℂ Pi₀) = ⊥ := by
      rw [← h]; exact iSup_eq_bot.2 fun f => by rw [hc f, LinearMap.range_zero]
    exact bot_ne_top this.symm
  have wit : ∀ {Q : Type} [AddCommGroup Q] [Module ℂ Q] (ρ : LieIx X → Module.End ℂ Q) (C : Submodule ℂ Q)
      (β : Q →ₗ[ℂ] Pi₀), (∀ i, β ∘ₗ ρ i = σ₀ i ∘ₗ β) → C ≤ LinearMap.ker β → β ≠ 0 →
      IsStab ρ (LinearMap.ker β) ∧ C ≤ LinearMap.ker β ∧ LinearMap.ker β ≠ ⊤ := by
    intro Q _ _ ρ C β hi hk hne
    refine ⟨fun i x hx => ?_, hk, fun h => hne (LinearMap.ker_eq_top.1 h)⟩
    rw [LinearMap.mem_ker] at hx ⊢
    rw [← LinearMap.comp_apply, hi i, LinearMap.comp_apply, hx, map_zero]
  obtain ⟨fA, hfA⟩ := nz _ sA
  obtain ⟨fB, hfB⟩ := nz _ sB
  obtain ⟨wA1, wA2, wA3⟩ := wit ρA CA _ (iA fA) (kA fA) hfA
  obtain ⟨wB1, wB2, wB3⟩ := wit ρB CB _ (iB fB) (kB fB) hfB
  have radA : rad ρA CA ≠ ⊤ := rad_ne_top _ _ ρA CA _ hHA wA1 wA2 wA3
  have radB : rad ρB CB ≠ ⊤ := rad_ne_top _ _ ρB CB _ hHB wB1 wB2 wB3
  have CleA : CA ≤ rad ρA CA := wA2.trans (le_sSup ⟨wA1, wA2, wA3⟩)
  have CleB : CB ≤ rad ρB CB := wB2.trans (le_sSup ⟨wB1, wB2, wB3⟩)
  have simA : ∀ N, IsStab ρA N → rad ρA CA ≤ N → N = rad ρA CA ∨ N = ⊤ := by
    intro N h1 h2
    by_cases h : N = ⊤
    · exact Or.inr h
    · exact Or.inl (le_antisymm (le_sSup ⟨h1, CleA.trans h2, h⟩) h2)
  have simB : ∀ N, IsStab ρB N → rad ρB CB ≤ N → N = rad ρB CB ∨ N = ⊤ := by
    intro N h1 h2
    by_cases h : N = ⊤
    · exact Or.inr h
    · exact Or.inl (le_antisymm (le_sSup ⟨h1, CleB.trans h2, h⟩) h2)
  have ss₀ := GlobalTheory.T.exists_stable_complement_of_irreducible_span_intertwiners _ _ _ _ _ ρA CA σ₀ (fun j : {h // h ∈ GfC X} => rf₀ j.1) _ hHA iA kA cA sA irr₀
  have killA₀ : ∀ f, rad ρA CA ≤ LinearMap.ker _ := fun f => rad_le_ker _ _ _ ρA CA σ₀ _ (iA f) (kA f) radA ss₀
  have killB₀ := rad_le_ker _ _ _ ρB CB σ₀ _ (iB fB) (kB fB) radB ss₀
  obtain ⟨e, he⟩ := GlobalTheory.T.simple_quotients_iso_of_intertwined_semisimple _ _ _ _ _ ρA CA ρB CB σ₀ _ _ iA (iB fB) killA₀ killB₀ hfB sA simA simB ss₀
  let R := rad ρA CA
  let RB := rad ρB CB
  refine ⟨ModuleCat.of ℂ (PolF D X.rank W.rank ⧸ R),
    fun τ Y => if h : Y ∈ lieAt X τ then radAct ρA CA ⟨(τ, Y), h⟩ else 0,
    R.mkQ, e.symm.toLinearMap ∘ₗ RB.mkQ, R.mkQ_surjective, e.symm.surjective.comp RB.mkQ_surjective, ?_, ?_, ?_⟩
  · show Module.rank ℂ (PolF D X.rank W.rank ⧸ R) ≤ _
    refine (rank_quotient_le R).trans ?_
    rw [← (MvPolynomial.basisMonomials (FVar D X.rank W.rank) ℂ).mk_eq_rank'']
    exact Cardinal.mk_le_aleph0
  · intro N hN
    have hst : IsStab ρA (N.comap R.mkQ) := fun i x hx => by
      have h1 := hN i.1.1 i.1.2 i.2 _ hx
      simp only [dif_pos i.2] at h1
      exact h1
    have hle : R ≤ N.comap R.mkQ := fun x hx => by
      show R.mkQ x ∈ N
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero R).2 hx]
      exact N.zero_mem
    rcases simA _ hst hle with h | h
    · left
      rw [← Submodule.map_comap_eq_of_surjective R.mkQ_surjective N, h, Submodule.mkQ_map_self]
    · right
      rw [← Submodule.map_comap_eq_of_surjective R.mkQ_surjective N, h, Submodule.map_top, Submodule.range_mkQ]
  · intro α β htr hexp ωA ωB Pi rf rl p p' hm
    obtain ⟨⟨iA', kA', cA', sA'⟩, ⟨iB', kB', cB', sB'⟩, irr', -, -, -⟩ := fam α β htr hexp ωA ωB Pi rf rl p p' hm
    have ss' := GlobalTheory.T.exists_stable_complement_of_irreducible_span_intertwiners _ _ _ _ _ ρA CA (fun i : LieIx X => rl i.1.1 i.1.2) (fun j : {h // h ∈ GfC X} => rf j.1) _ hHA
      iA' kA' cA' sA' irr'
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · have hk := rad_le_ker _ _ _ ρA CA _ _ (iA' ⟨f, hf⟩) (kA' ⟨f, hf⟩) radA ss'
      refine ⟨R.liftQ (p ∘ₗ fockF ψ θ true A B f) hk, fun τ Y hY => ?_, fun P => rfl⟩
      simp only [dif_pos hY]
      refine Submodule.linearMap_qext _ (LinearMap.ext fun P => ?_)
      exact LinearMap.congr_fun (iA' ⟨f, hf⟩ ⟨(τ, Y), hY⟩) P
    · have hk := rad_le_ker _ _ _ ρB CB _ _ (iB' ⟨f, hf⟩) (kB' ⟨f, hf⟩) radB ss'
      refine ⟨RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk ∘ₗ e.toLinearMap, fun τ Y hY => ?_, fun P => ?_⟩
      · simp only [dif_pos hY]
        refine LinearMap.ext fun x => ?_
        have h1 := LinearMap.congr_fun (he ⟨(τ, Y), hY⟩) x
        simp only [LinearMap.comp_apply] at h1 ⊢
        rw [h1]
        have key : ∀ y, RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk (radAct ρB CB ⟨(τ, Y), hY⟩ y) =
            rl τ Y (RB.liftQ (p' ∘ₗ fockF ψ θ false A₁ B f) hk y) := by
          intro y
          obtain ⟨P, rfl⟩ := RB.mkQ_surjective y
          exact LinearMap.congr_fun (iB' ⟨f, hf⟩ ⟨(τ, Y), hY⟩) P
        exact key _
      · simp
end GlobalTheory.RealQuot
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_quotient_real : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching →
  ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D), IsStdChar D ψ (-1) → IsInfFam θ →
    ∀ (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (a b : D.what₂.Tau → ℚ),
    ∃ (Pr : ModuleCat.{0} ℂ) (ρ : D.what₂.Tau → Matrix (Fin X.rank) (Fin X.rank) ℂ → Module.End ℂ Pr)
      (q : PolF D X.rank W.rank →ₗ[ℂ] Pr) (q' : PolF D X.rank W₁.rank →ₗ[ℂ] Pr),
      Function.Surjective q ∧ Function.Surjective q' ∧ Module.rank ℂ Pr ≤ Cardinal.aleph0 ∧
      (∀ N : Submodule ℂ Pr, (∀ τ, ∀ Y ∈ lieAt X τ, ∀ x ∈ N, ρ τ Y x ∈ N) → N = ⊥ ∨ N = ⊤) ∧
      ∀ α β, IsTriple W W₁ X α β → (∀ τ, HasInfExp D α τ (a τ) ∧ HasInfExp D β τ (b τ)) →
        ∀ ωA ωB Pi rf rl p p', IsMatch ψ θ A A₁ B α β ωA ωB Pi rf rl p p' →
          (∀ f, IsFinF ψ θ true A B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p (fockF ψ θ true A B f P) = φ (q P)) ∧
          ∀ f, IsFinF ψ θ false A₁ B f → ∃ φ : Pr →ₗ[ℂ] Pi, (∀ τ, ∀ Y ∈ lieAt X τ, φ ∘ₗ ρ τ Y = rl τ Y ∘ₗ φ) ∧
            ∀ P, p' (fockF ψ θ false A₁ B f P) = φ (q' P) := by
  first | exact @_root_.GlobalTheory.RealQuot.twist_quotient_isReal | exact _root_.GlobalTheory.RealQuot.twist_quotient_isReal | (intros; apply _root_.GlobalTheory.RealQuot.twist_quotient_isReal <;> assumption)
end
end

section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
namespace GlobalTheory.SquareLM
theorem twisted_square_local_matching : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree →
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.LocalMatching := by
  intro hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  obtain ⟨Pr, ρ, q, q', hq, hq', hrk, hirr, hfac⟩ := _root_.GlobalTheory.T.twisted_quotient_real hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B a b
  let ι := {x : D.what₂.Tau × Matrix (Fin X.rank) (Fin X.rank) ℂ // x.2 ∈ lieAt X x.1}
  have hirr' : ∀ N : Submodule ℂ Pr, (∀ i : ι, ∀ x ∈ N, ρ i.1.1 i.1.2 x ∈ N) → N = ⊥ ∨ N = ⊤ :=
    fun N hN => hirr N fun τ Y hY x hx => hN ⟨(τ, Y), hY⟩ x hx
  have hS := GlobalTheory.dixmier_commutant_scalar ι Pr (fun i => ρ i.1.1 i.1.2) hrk hirr'
  obtain ⟨h0, hadd, hsmul, hfadd, hfsmul⟩ := GlobalTheory.FinFockLin.finF_lin D ψ θ hψ hθ true W X A B
  obtain ⟨h0', hadd', hsmul', hfadd', hfsmul'⟩ := GlobalTheory.FinFockLin.finF_lin D ψ θ hψ hθ false W₁ X A₁ B
  refine ⟨Pr, q, q', hq, hq', fun α β htr hexp => ⟨_root_.GlobalTheory.T.twist_triple_matches hH hP hT hL D ψ θ hψ hθ W W₁ X A A₁ B α β htr, ?_⟩⟩
  intro ωA ωB Pi rf rl p p' hm
  obtain ⟨hfa, hfb⟩ := hfac α β htr hexp ωA ωB Pi rf rl p p' hm
  let S : Submodule ℂ (WO W X → ℂ) :=
    { carrier := {f | IsFinF ψ θ true A B f}, add_mem' := fun hf hg => hadd _ _ hf hg, zero_mem' := h0,
      smul_mem' := fun c _ hf => hsmul c _ hf }
  let S' : Submodule ℂ (WO W₁ X → ℂ) :=
    { carrier := {f | IsFinF ψ θ false A₁ B f}, add_mem' := fun hf hg => hadd' _ _ hf hg, zero_mem' := h0',
      smul_mem' := fun c _ hf => hsmul' c _ hf }
  let βA : S →ₗ[ℂ] PolF D X.rank W.rank →ₗ[ℂ] Pi :=
    LinearMap.mk₂ ℂ (fun f P => p (fockF ψ θ true A B f.1 P)) (fun f g P => by
        rw [Submodule.coe_add, hfadd _ _ _ f.2 g.2, map_add (f := _)])
      (fun c f P => by rw [Submodule.coe_smul, hfsmul _ _ _ f.2, map_smul]) (fun f P P' => by rw [map_add (f := _), map_add (f := _)])
      (fun c f P => by rw [map_smul, map_smul])
  let βB : S' →ₗ[ℂ] PolF D X.rank W₁.rank →ₗ[ℂ] Pi :=
    LinearMap.mk₂ ℂ (fun f P => p' (fockF ψ θ false A₁ B f.1 P)) (fun f g P => by
        rw [Submodule.coe_add, hfadd' _ _ _ f.2 g.2, map_add (f := _)])
      (fun c f P => by rw [Submodule.coe_smul, hfsmul' _ _ _ f.2, map_smul]) (fun f P P' => by rw [map_add (f := _), map_add (f := _)])
      (fun c f P => by rw [map_smul, map_smul])
  have hspan : ∀ {M : HSp D} {ε : Bool} {A' : Fr M} {P : Type} [AddCommGroup P] [Module ℂ P] (pp : (WO M X → ℂ) →ₗ[ℂ] P),
      (algF ψ θ ε A' B).map pp = ⊤ →
      Submodule.span ℂ {y | ∃ f : {f // IsFinF ψ θ ε A' B f}, ∃ Q, y = pp (fockF ψ θ ε A' B f.1 Q)} = ⊤ := by
    intro M ε A' P _ _ pp h
    rw [← h, algF, Submodule.map_span]
    congr 1
    ext y
    constructor
    · rintro ⟨f, Q, rfl⟩; exact ⟨_, ⟨f.1, Q, f.2, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨f, Q, hf, rfl⟩, rfl⟩; exact ⟨⟨f, hf⟩, Q, rfl⟩
  obtain ⟨Pf, r, r', e, hr, hr', he, he'⟩ := GlobalTheory.SquareLM.productForm ι Pr Pi _ _ _ _ (fun i => ρ i.1.1 i.1.2) (fun i => rl i.1.1 i.1.2)
    q q' βA βB ⊤ ⊤ hq hq' hirr' hS
    (fun f _ => by
      obtain ⟨φ, h1, h2⟩ := hfa f.1 f.2
      exact ⟨φ, fun i => h1 i.1.1 i.1.2 i.2, LinearMap.ext fun P => h2 P⟩)
    (fun f _ => by
      obtain ⟨φ, h1, h2⟩ := hfb f.1 f.2
      exact ⟨φ, fun i => h1 i.1.1 i.1.2 i.2, LinearMap.ext fun P => h2 P⟩)
    (by
      rw [← hspan p hm.mapA.onto]
      congr 1; ext y
      exact ⟨fun ⟨f, _, Q, h⟩ => ⟨⟨f.1, f.2⟩, Q, h⟩, fun ⟨f, Q, h⟩ => ⟨⟨f.1, f.2⟩, trivial, Q, h⟩⟩)
    (by
      rw [← hspan p' hm.mapB.onto]
      congr 1; ext y
      exact ⟨fun ⟨f, _, Q, h⟩ => ⟨⟨f.1, f.2⟩, Q, h⟩, fun ⟨f, Q, h⟩ => ⟨⟨f.1, f.2⟩, trivial, Q, h⟩⟩)
  obtain ⟨r₀, hr₀⟩ := LinearMap.exists_extend r
  obtain ⟨r₀', hr₀'⟩ := LinearMap.exists_extend r'
  have e₁ : ∀ f (hf : IsFinF ψ θ true A B f), r₀ f = r ⟨f, hf⟩ := fun f hf => LinearMap.congr_fun hr₀ ⟨f, hf⟩
  have e₂ : ∀ f (hf : IsFinF ψ θ false A₁ B f), r₀' f = r' ⟨f, hf⟩ := fun f hf => LinearMap.congr_fun hr₀' ⟨f, hf⟩
  refine ⟨Pf, r₀, r₀', e, fun x => ?_, fun x => ?_, fun f hf P => ?_, fun f hf P => ?_⟩
  · obtain ⟨f, _, h⟩ := hr x; exact ⟨f.1, f.2, by rw [e₁ f.1 f.2]; exact h⟩
  · obtain ⟨f, _, h⟩ := hr' x; exact ⟨f.1, f.2, by rw [e₂ f.1 f.2]; exact h⟩
  · rw [e₁ f hf]; exact he ⟨f, hf⟩ trivial P
  · rw [e₂ f hf]; exact he' ⟨f, hf⟩ trivial P
end GlobalTheory.SquareLM
end
end

section
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_local_factors_match : GlobalTheory.Published.HoweDualityReal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.LocalMatching := by
  first | exact @_root_.GlobalTheory.SquareLM.twisted_square_local_matching | exact _root_.GlobalTheory.SquareLM.twisted_square_local_matching | (intros; apply _root_.GlobalTheory.SquareLM.twisted_square_local_matching <;> assumption)
end
