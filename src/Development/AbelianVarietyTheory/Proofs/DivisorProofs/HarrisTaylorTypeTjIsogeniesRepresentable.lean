module

public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PolKerAtPullbackOfIsGrpPullback
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsPolarizationDescentOfQuasiIsogeny
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMemberTermsIntegralUnitShift
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PolarizationDescentAlongQuasiIsogenyCompat
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.PowPolarizationIsoPullbackOfDescent
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKodairaSpencerAffineOpenAbelianPullback
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvcPowRight
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsClopenLocusOfAnnihilator

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleRosatiDescendedAction
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleRosatiDescendedAction
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem rosati_of_quasiInv_root : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ a : D.O, LBIso (P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left) (P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq P' hP' _ hIso act' hact a
  obtain ⟨e, rfl⟩ := hc
  have hpos : 0 < p ^ e := pow_pos (Fact.out : p.Prime).pos e
  have hunit : IsUnit ((p ^ e : ℕ) : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [← Nat.cast_pow, map_natCast] at this
  obtain ⟨hL', r₁, r₂⟩ := hP'
  haveI := act'.hom a
  haveI := act'.hom (D.star a).unop
  have e₁ : Hecke.sq2 ψ ≫ (lift (fst B B ≫ act'.act a) (snd B B)).left =
      (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left ≫ Hecke.sq2 ψ := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have e₂ : Hecke.sq2 ψ ≫ (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left =
      (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left ≫ Hecke.sq2 ψ := by
    simp only [Hecke.sq2, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp [hact]
  have u₁ : (lift (1 : B ⟶ B) (𝟙 B)).left ≫ (lift (fst B B ≫ act'.act a) (snd B B)).left =
      𝟙 _ ≫ (lift (1 : B ⟶ B) (𝟙 B)).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have u₂ : (lift (𝟙 B) (1 : B ⟶ B)).left ≫ (lift (fst B B ≫ act'.act a) (snd B B)).left =
      (act'.act a).left ≫ (lift (𝟙 B) (1 : B ⟶ B)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₁ : (lift (1 : B ⟶ B) (𝟙 B)).left ≫ (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left =
      (act'.act (D.star a).unop).left ≫ (lift (1 : B ⟶ B) (𝟙 B)).left := by
    rw [← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have v₂ : (lift (𝟙 B) (1 : B ⟶ B)).left ≫ (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left =
      𝟙 _ ≫ (lift (𝟙 B) (1 : B ⟶ B)).left := by
    rw [← Over.comp_left, Category.id_comp]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  have hL := o.isLB
  have hX₁ : ((P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left).pull (Hecke.sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hL' _) _
  have hX₂ : ((P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left).pull (Hecke.sq2 ψ)).IsLB :=
    pull_isLB (pull_isLB hL' _) _
  have hL₁ : (Hecke.lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left) (p ^ e)).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have hL₂ : (Hecke.lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left) (p ^ e)).IsLB :=
    ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (pull_isLB hL _) _ _
  have I₁ : LBIso (Hecke.lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left) (p ^ e))
      ((P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left).pull (Hecke.sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => Hecke.sq2 ψ) (fun _ => Hecke.sq2 ψ) (fun _ => 1) _ (fun _ => e₁)) hIso
  have I₂ : LBIso (Hecke.lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left) (p ^ e))
      ((P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left).pull (Hecke.sq2 ψ)) :=
    LBIso.chartPull (chartPullLinComb o.P _ (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 𝟙 _) (fun _ => 1) _
        (fun _ => by rw [Category.id_comp, Category.comp_id]))
      (chartPullLinComb P' _ (K := PUnit) (fun _ => Hecke.sq2 ψ) (fun _ => Hecke.sq2 ψ) (fun _ => 1) _ (fun _ => e₂)) hIso
  have Rm : LBIso (Hecke.lbPow (o.P.pull (lift (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).left) (p ^ e))
      (Hecke.lbPow (o.P.pull (lift (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).left) (p ^ e)) :=
    GlobalTheory.PowPrimitive.lbIso_linComb (o.rosati a) _ _
  have hsq := LBIso.trans hX₁ hL₁ hX₂ I₁.symm (LBIso.trans hL₁ hL₂ hX₂ Rm I₂)
  obtain ⟨t₁, ht₁⟩ := r₁
  obtain ⟨t₂, ht₂⟩ := r₂
  have A₁ : IsAxesTriv B (P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left) :=
    ⟨pull_isLB hL' _,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₁)) t₁ ht₁,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => u₂)) t₂ ht₂⟩
  have A₂ : IsAxesTriv B (P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left) :=
    ⟨pull_isLB hL' _,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₁)) t₁ ht₁,
      gen_chartPull (chartPullLinComb P' _ (K := PUnit) (fun _ => _) (fun _ => _) (fun _ => 1) _ (fun _ => v₂)) t₂ ht₂⟩
  exact GlobalTheory.QuasiInvPull.lbIso_of_pullback_quasiInverseIsogeny_trivial_axes Y o.A B (p ^ e) ψ ψ' _ _ hB hpos hunit hq A₁ A₂ hsq

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseRootBundleRosatiDescendedActionStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverse_root_bundle_rosati_descended_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ a : D.O, LBIso (P'.pull (lift (fst B B ≫ act'.act a) (snd B B)).left) (P'.pull (lift (fst B B) (snd B B ≫ act'.act (D.star a).unop)).left) := by
  first | (exact @GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root) | (exact GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root) | (intros; apply GlobalTheory.UPel.HT.ES.rosati_of_quasiInv_root  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationDescentOfQuasiIsogeny
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_polarization_descent_of_quasi_isogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) → ∃ P' : LB (G2 B).left, IsAxesTriv B P' ∧ LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) ∧ LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) := by
  first | exact @UpperTheory.Cb.exists_polarization_descent_of_quasi_isogeny | exact UpperTheory.Cb.exists_polarization_descent_of_quasi_isogeny
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagRootPullbackQuasiInverse
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmplePullOfIsFinite
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.RootDiagAmple

open GlobalTheory.CechPic

variable {S : Scheme.{0}}

theorem relAmple_pull_of_isFinite {A G : Over S} [IsProper A.hom] (χ : A ⟶ G) [IsFinite χ.left]
    {D : LB G.left} (hD : D.IsLB) (h : Out.RelAmple G D) : Out.RelAmple A (D.pull χ.left) := by
  refine relAmple_of_isAmpleLB A (pull_isLB hD _) fun V hV => ?_
  have le : A.hom ⁻¹ᵁ V ≤ χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
  have le' : χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) ≤ A.hom ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, Over.w]
  have e : A.hom ⁻¹ᵁ V = χ.left ⁻¹ᵁ (G.hom ⁻¹ᵁ V) := le_antisymm le le'
  rw [e]
  have h₁ := (isAmpleLB_of_relAmple G hD h V hV).pull_of_isFinite (χ.left ∣_ (G.hom ⁻¹ᵁ V))
  refine (isAmpleLB_congr (pull_isLB (pull_isLB hD _) _) (pull_isLB (pull_isLB hD _) _) ?_).1 h₁
  refine (cls_eq_iff (pull_isLB (pull_isLB hD _) _) (pull_isLB (pull_isLB hD _) _)).1 ?_
  rw [cls_pull (pull_isLB hD _), cls_pull (pull_isLB hD _), cls_pull hD, cls_pull hD, ← pull_comp, ← pull_comp,
    morphismRestrict_ι]

theorem relAmple_of_relAmple_pow {A : Over S} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
    (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (e : cls M hM = d • cls L hL) (h : Out.RelAmple A M) : Out.RelAmple A L := by
  rw [relAmple_iff_isAmpleLB A hM] at h
  refine relAmple_of_isAmpleLB A hL fun U hU => (isAmpleLB_pow_iff (pull_isLB hL _) hd).1 ?_
  refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)
    ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).2 (h U hU)
  rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, e, map_nsmul]

end GlobalTheory.RootDiagAmple
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagRootPullbackQuasiInverse
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

open GlobalTheory.CechPic

theorem relAmple_diag_root_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → Out.RelAmple B (P'.pull (lift (𝟙 B) (𝟙 B)).left) := by
  intro p _ D R _ b N c Y _ s o B _ _ ψ ψ' hp hc hB hq P' hP' hiso _
  obtain ⟨e, rfl⟩ := hc
  have hu : IsUnit (((p ^ e : ℕ)) : Γ(Y, ⊤)) := by
    have h := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [map_natCast] at h
    rw [Nat.cast_pow]
    exact h.pow e
  have hq' : IsQuasiInv (p ^ e) ψ' ψ := ⟨hq.2.1, hq.1, hq.2.2.2, hq.2.2.1⟩
  have hfin := (isFinite_etale_surjective_of_isQuasiInv Y B o.A (p ^ e) ψ' ψ hB o.ab hu hq').1
  have := hB.proper
  have := o.ab.proper
  have hL := hP'.1
  have hD := pull_isLB o.isLB (lift (𝟙 o.A) (𝟙 o.A)).left
  have a₁ := GlobalTheory.RootDiagAmple.relAmple_pull_of_isFinite ψ' hD o.ample
  have relAmple_of_pow {A : Over Y} [IsProper A.hom] {L M : LB A.left} (hL : L.IsLB)
      (hM : M.IsLB) {d : ℕ} (hd : 1 ≤ d) (eq : cls M hM = d • cls L hL)
      (h : Out.RelAmple A M) : Out.RelAmple A L := by
    rw [relAmple_iff_isAmpleLB A hM] at h
    refine relAmple_of_isAmpleLB A hL fun U hU => (isAmpleLB_pow_iff (pull_isLB hL _) hd).1 ?_
    refine (isAmpleLB_congr (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)
      ((cls_eq_iff (isLB_lbPow (pull_isLB hL _) d) (pull_isLB hM _)).1 ?_)).2 (h U hU)
    rw [cls_lbPow (pull_isLB hL _), cls_pull hL, cls_pull hM, eq, map_nsmul]
  refine relAmple_of_pow (pull_isLB hL _) (pull_isLB hD _)
    (d := p ^ e) (Nat.one_le_pow e p ((Fact.out : p.Prime).pos)) ?_ a₁
  have hpow : (Hecke.lbPow P' (p ^ e)).IsLB := LB.isLB_linComb hL _ _
  have ec := (cls_eq_iff (pull_isLB o.isLB _) hpow).2 hiso
  have ep : cls _ hpow = (p ^ e) • cls P' hL := by
    refine (cls_linComb hL (K := Fin (p ^ e)) (fun _ => 𝟙 _) (fun _ => 1) hpow).trans ?_
    simp [pull_id]
  rw [cls_pull hL, cls_pull hD, cls_pull o.isLB, ← pull_comp]
  have m : ψ'.left ≫ (lift (𝟙 o.A) (𝟙 o.A)).left = (lift (𝟙 B) (𝟙 B)).left ≫ Hecke.sq2 ψ' := by
    rw [Hecke.sq2, ← Over.comp_left, ← Over.comp_left]
    congr 1
    apply CartesianMonoidalCategory.hom_ext <;> simp
  rw [m, pull_comp, ← cls_pull o.isLB _ (pull_isLB o.isLB _), ec, ep, map_nsmul]

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelAmpleDiagRootPullbackQuasiInverseStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relAmple_diag_root_pullback_quasiInverse : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) [IsLocallyNoetherian Y] (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → Out.RelAmple B (P'.pull (lift (𝟙 B) (𝟙 B)).left) := by
  first | (exact @GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull) | (exact GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull) | (intros; apply GlobalTheory.UPel.HT.ES.relAmple_diag_root_pull  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderActionDescentAlongIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderActionDescentAlongIsogeny
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_oAct_desc : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → KerStableAt o ψ (𝟙 Y) → ∃ act' : OActN D.O B, ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, he⟩ hB hq hst
  have hc : IsUnit (c : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [← Nat.cast_pow, map_natCast, ← he] at this
    exact this
  obtain ⟨hfin, het, hsurj⟩ := isFinite_etale_surjective_of_isQuasiInv Y o.A B c ψ ψ' o.ab hB hc hq
  haveI : Surjective ψ.left := hsurj
  haveI : Flat ψ.left := inferInstance
  haveI : QuasiCompact ψ.left := inferInstance
  haveI : IsMonHom ψ := hq.1
  have : Epi ψ := GlobalTheory.FlatQuotient.epi_of_flat_surjective ψ
  have : Epi (ψ ⊗ₘ ψ) := GlobalTheory.FlatQuotient.epi_tensorHom ψ ψ
  have hd : ∀ a : D.O, ∃ t : B ⟶ B, ψ ≫ t = o.act.act a ≫ ψ := fun a => by
    haveI := o.act.hom a
    refine GlobalTheory.AbelianQuotient.exists_desc ψ (o.act.act a ≫ ψ) fun W x₁ x₂ h => ?_
    have h1 : (x₁ / x₂) ≫ ψ = 1 := by rw [GrpObj.div_comp, h, div_self']
    have h2 : (x₁ / x₂) ≫ o.act.act a ≫ ψ = 1 := hst W W.hom (Category.comp_id _) _ h1 a
    rwa [GrpObj.div_comp, div_eq_one] at h2
  choose t ht using hd
  refine ⟨{ act := t, hom := fun a => ?_, one := ?_, mul := fun a a' => ?_, add := fun a a' => ?_ },
    fun a => (ht a).symm⟩
  · haveI := o.act.hom a
    refine ⟨?_, ?_⟩
    · rw [← IsMonHom.one_hom (f := ψ), Category.assoc, ht, ← Category.assoc, IsMonHom.one_hom]
    · rw [← cancel_epi (ψ ⊗ₘ ψ), ← Category.assoc, ← IsMonHom.mul_hom, Category.assoc, ht,
        ← Category.assoc, IsMonHom.mul_hom, Category.assoc, IsMonHom.mul_hom, ← Category.assoc,
        ← Category.assoc, tensorHom_comp_tensorHom, tensorHom_comp_tensorHom, ht]
  · rw [← cancel_epi ψ, ht, o.act.one, Category.id_comp, Category.comp_id]
  · rw [← cancel_epi ψ, ht, o.act.mul, Category.assoc, ← ht, ← Category.assoc, ← ht, Category.assoc]
  · rw [← cancel_epi ψ, ht, o.act.add, Hom.mul_def, Hom.mul_def, comp_lift_assoc, ht, ht, ← lift_map, Category.assoc,
      Category.assoc, IsMonHom.mul_hom]

end GlobalTheory.UPel.HT.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOrderActionDescentAlongIsogenyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_orderAction_descent_along_isogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → KerStableAt o ψ (𝟙 Y) → ∃ act' : OActN D.O B, ∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a := by
  first | (exact @GlobalTheory.UPel.HT.ES.exists_oAct_desc) | (exact GlobalTheory.UPel.HT.ES.exists_oAct_desc) | (intros; apply GlobalTheory.UPel.HT.ES.exists_oAct_desc  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieOfQuasiInverseIsogeny
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieOfQuasiInverseIsogeny
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem lie_of_isQuasiInv : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ B, IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ B), (∀ i, ∀ a : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O a) (β (b.t i a)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hc hB hq act' hact
  obtain ⟨e, rfl⟩ := hc
  have hcY : IsUnit (((p ^ e : ℕ) : ℕ) : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [map_pow, map_natCast] at this
    rw [Nat.cast_pow]
    exact this
  obtain ⟨-, hEt, -⟩ := isFinite_etale_surjective_of_isQuasiInv Y o.A B (p ^ e) ψ ψ' o.ab hB hcY hq
  haveI : IsMonHom ψ := hq.1
  haveI : Etale ψ.left := hEt
  refine ⟨?_, ?_⟩
  · intro R' _ β x hx v hv
    obtain ⟨l, ⟨hl₁, hl₂⟩, -⟩ := GlobalTheory.UPel.HT.EtaleLie.existsUnique_dual_lift ψ x v.left hv.1
    let u : epsPtR x ⟶ o.A := Over.homMk l (by
      show l ≫ o.A.hom = _
      rw [← Over.w ψ, ← Category.assoc, hl₂]; exact Over.w v)
    have hu : IsTanScal o.act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) u := by
      refine ⟨hl₁, ?_⟩
      have hh : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ (spMap (epsScaleR (β b.ρ)) ≫ v.left) =
          (1 : Over.mk x ⟶ B).left := by
        rw [← Category.assoc, GlobalTheory.UPel.HT.EtaleLie.fst_spMap_epsScaleR, hv.1]
      haveI := o.act.hom (algebraMap (𝓞 D.F) D.O D.ω)
      refine (GlobalTheory.UPel.HT.EtaleLie.existsUnique_dual_lift ψ x _ hh).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
      · show _ ≫ l ≫ (o.act.act _).left = _
        rw [← Category.assoc, hl₁]
        have e : ((1 : Over.mk x ⟶ o.A) ≫ o.act.act (algebraMap (𝓞 D.F) D.O D.ω)).left =
            (1 : Over.mk x ⟶ o.A).left :=
          congrArg Over.Hom.left (MonObj.one_comp _)
        exact e
      · show (l ≫ (o.act.act _).left) ≫ ψ.left = _
        rw [Category.assoc, ← Over.comp_left, hact, Over.comp_left, ← Category.assoc, hl₂, ← hv.2]
        rfl
      · show _ ≫ spMap _ ≫ l = _
        rw [← Category.assoc, GlobalTheory.UPel.HT.EtaleLie.fst_spMap_epsScaleR, hl₁]
      · show (spMap _ ≫ l) ≫ ψ.left = _
        rw [Category.assoc, hl₂]
    obtain ⟨w, hw, hvw⟩ := o.lie R' β x hx u hu
    refine ⟨fun i => w i ≫ ψ, fun i a => ⟨?_, ?_⟩, ?_⟩
    · show _ ≫ (w i).left ≫ ψ.left = _
      rw [← Category.assoc, (hw i a).1]
      have e : ((1 : Over.mk x ⟶ o.A) ≫ ψ).left = (1 : Over.mk x ⟶ B).left :=
        congrArg Over.Hom.left (MonObj.one_comp ψ)
      exact e
    · show ((w i ≫ ψ) ≫ act'.act _).left = spMap _ ≫ (w i).left ≫ ψ.left
      rw [Category.assoc, ← hact, ← Category.assoc, Over.comp_left, (hw i a).2, Category.assoc]
    · apply Over.OverMorphism.ext
      rw [← GlobalTheory.LieEtale.ofFn_prod_comp ψ w, ← hvw]
      exact hl₂.symm
  · intro κ _ _ x β hx i
    exact (GlobalTheory.LieEtale.lieMult_iff_of_etale (𝓞 D.F) Y o.A B ψ (o.act.toF D) (act'.toF D) inferInstance hEt
      (fun a => hact _) κ x (β.comp (b.t i)) D.m).mp (o.lieRank κ x β hx i)

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorLieOfQuasiInverseIsogenyStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_lie_of_quasiInverseIsogeny : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Y), x ≫ s = spMap β → ∀ v : epsPtR x ⟶ B, IsTanScal act' x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ B), (∀ i, ∀ a : 𝓞 D.F, IsTanScal act' x (algebraMap (𝓞 D.F) D.O a) (β (b.t i a)) (w i)) ∧ v = (List.ofFn w).prod) ∧ (∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∀ i, LieMult (act'.toF D) x (β.comp (b.t i)) D.m) := by
  first | (exact @GlobalTheory.UPel.HT.ES.lie_of_isQuasiInv) | (exact GlobalTheory.UPel.HT.ES.lie_of_isQuasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.lie_of_isQuasiInv  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizationDescentAlongQuasiIsogenyCompat
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.polarization_descent_along_quasi_isogeny_compat : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → PolKerAt o ψ' c (𝟙 Y) → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∃ e : ℕ, e.Coprime p ∧ ∀ (T : Over Y) (x : T ⟶ B), (∃ t : (P'.pull (lift (snd B T ≫ x) (fst B T)).left).Gen, t.IsGen) → x ^ e = 1 := by
  first | exact @UpperTheory.Cb.polarization_descent_along_quasi_isogeny_compat | exact UpperTheory.Cb.polarization_descent_along_quasi_isogeny_compat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenySquareCompatCompQuasiInv
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenySquareCompatCompQuasiInv
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.QCompat

theorem comp_quasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ B₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] [GrpObj B₁] [IsCommMonObj B₁] (φ : A₁.left ⟶ A.left) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ → 0 < k → IsQuasiInv k ψ ψ' → IsQuasiInv k ψ₁ ψ₁' → IsGrpPullback A₁ A t φ → φ ≫ ψ.left = ψ₁.left ≫ θ → θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  intro T Y t A B _ _ _ _ k ψ ψ' A₁ B₁ _ _ _ _ φ θ ψ₁ ψ₁' hB hk hq hq₁ hφ hsq
  obtain ⟨h1, h2, -⟩ := GlobalTheory.UPel.HT.SiegUniqBase.flat_surjective_qc_pow T B₁ hB k hk
  haveI : Epi ((𝟙 B₁) ^ k).left := Flat.epi_of_flat_of_surjective _
  have e₁ : ψ₁'.left ≫ ψ₁.left = ((𝟙 B₁) ^ k).left := by rw [← Over.comp_left, hq₁.2.2.2]
  haveI : Epi (ψ₁'.left ≫ ψ₁.left) := by rw [e₁]; infer_instance
  haveI : Epi ψ₁.left := epi_of_epi ψ₁'.left ψ₁.left
  rw [← cancel_epi ψ₁.left, ← Category.assoc, ← hsq, Category.assoc, ← Over.comp_left, hq.2.2.1,
    ← Category.assoc, ← Over.comp_left, hq₁.2.2.1]
  exact (GlobalTheory.LamF.IsGrpPullback.id_pow_left hφ k).symm

end GlobalTheory.UPel.HT.ES.QCompat
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiInverseIsogenySquareCompatCompQuasiInvStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiInverseIsogeny_square_compat_comp_quasiInv : ∀ (T Y : Scheme.{0}) (t : T ⟶ Y) (A B : Over Y) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (k : ℕ) (ψ : A ⟶ B) (ψ' : B ⟶ A) (A₁ B₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] [GrpObj B₁] [IsCommMonObj B₁] (φ : A₁.left ⟶ A.left) (θ : B₁.left ⟶ B.left) (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsAbelianScheme B₁ → 0 < k → IsQuasiInv k ψ ψ' → IsQuasiInv k ψ₁ ψ₁' → IsGrpPullback A₁ A t φ → φ ≫ ψ.left = ψ₁.left ≫ θ → θ ≫ ψ'.left = ψ₁'.left ≫ φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv) | (exact GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv) | (intros; apply GlobalTheory.UPel.HT.ES.QCompat.comp_quasiInv  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackKernelLocusIsClopen
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackBundleDualHom
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackBundleDualHom
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

open GlobalTheory.AbDual GlobalTheory.CechPic

theorem pullPol_dual_hom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ' : B ⟶ o.A), IsAbelianScheme B → IsMonHom ψ' → ∃ (C : Over Y) (_ : GrpObj C) (Q : LB (B ⊗ C).left) (h : B ⟶ C), IsAbelianScheme C ∧ GlobalTheory.AbDual.IsDual B C Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (o.P.pull (ψ' ⊗ₘ ψ').left) (Q.pull (lift (fst B B) (snd B B ≫ h)).left) ∧ ∀ (T : Over Y) (x : T ⟶ B), PullPolTriv o ψ' x ↔ x ≫ h = 1 := by
  intro p _ D R _ b N Y s o B _ _ ψ' hB hψ
  obtain ⟨C, _, Q, h, hC, hQ, hQ', hh, e⟩ :=
    GlobalTheory.DualHomPull.exists_dual_hom Y B o.A ψ' o.P hB o.ab hψ o.isLB o.rig₁ o.rig₂
  refine ⟨C, inferInstance, Q, h, hC, hQ, hQ', hh, e, fun T x ↦ ?_⟩
  have eχ : ψ' ⊗ₘ ψ' = lift (fst B B ≫ ψ') (snd B B ≫ ψ') := by ext <;> simp
  rw [eχ] at e
  have hE : (ev o.P (fst B B ≫ ψ') (snd B B ≫ ψ')).IsLB := pull_isLB o.isLB _
  have hF : (ev Q (fst B B) (snd B B ≫ h)).IsLB := pull_isLB hQ.isLB _
  have c := congrArg (CechPic.pull (lift (fst B T) (snd B T ≫ x)).left) ((cls_eq_iff hE hF).2 e)
  rw [cls_ev o.isLB, cls_ev hQ.isLB, pull_evc, pull_evc, lift_fst_assoc, lift_snd_assoc, lift_fst,
    lift_snd_assoc] at c
  simp only [Category.assoc] at c
  have k : PullPolTriv o ψ' x ↔ evc o.isLB (fst B T ≫ ψ') (snd B T ≫ x ≫ ψ') = 0 :=
    triv_ev_iff o.isLB _ _
  rw [k, c]
  constructor
  · intro z
    exact hQ.eq_one (x ≫ h) ((triv_ev_iff hQ.isLB _ _).2 z)
  · intro z
    rw [z, MonObj.comp_one]
    exact evc_one_right hQ.isLB hQ.zero _

end GlobalTheory.UPel.HT.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackBundleDualHomStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_pullback_bundle_dual_hom : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ' : B ⟶ o.A), IsAbelianScheme B → IsMonHom ψ' → ∃ (C : Over Y) (_ : GrpObj C) (Q : LB (B ⊗ C).left) (h : B ⟶ C), IsAbelianScheme C ∧ GlobalTheory.AbDual.IsDual B C Q ∧ GlobalTheory.AbDual.IsAdditive (GlobalTheory.AbDual.swap Q) ∧ IsMonHom h ∧ LBIso (o.P.pull (ψ' ⊗ₘ ψ').left) (Q.pull (lift (fst B B) (snd B B ≫ h)).left) ∧ ∀ (T : Over Y) (x : T ⟶ B), PullPolTriv o ψ' x ↔ x ≫ h = 1 := by
  first | (exact @GlobalTheory.UPel.HT.ES.pullPol_dual_hom) | (exact GlobalTheory.UPel.HT.ES.pullPol_dual_hom) | (intros; apply GlobalTheory.UPel.HT.ES.pullPol_dual_hom  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackKernelLocusIsClopen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES

theorem isMonHom_id_npow {Y : Scheme.{0}} (A : Over Y) [GrpObj A] [IsCommMonObj A] (n : ℕ) :
    IsMonHom ((𝟙 A) ^ n) := by
  have h := Grp.Hom.hom_hom_zpow (G := Grp.mk A) (H := Grp.mk A) (𝟙 _) (n : ℤ)
  have h' : IsMonHom ((𝟙 (Grp.mk A) : Grp.mk A ⟶ Grp.mk A) ^ (n : ℤ)).hom.hom := inferInstance
  rw [h, zpow_natCast] at h'
  exact h'

theorem polKer_locus_clopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ PolKerAt o ψ' c t := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, hc⟩ hB hq
  have hpY : IsUnit ((p : ℕ) : Γ(Y, ⊤)) := by
    have := hp.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rwa [map_natCast] at this
  have hn : IsUnit ((c ^ 3 : ℕ) : Γ(Y, ⊤)) := by
    rw [hc, ← pow_mul, Nat.cast_pow]
    exact hpY.pow _
  obtain ⟨C, _, Q, h, hC, -, -, hh, -, hT⟩ := GlobalTheory.T.harrisTaylor_pullback_bundle_dual_hom p D R b N Y s o B ψ' hB hq.2.1
  haveI := isMonHom_id_npow B c
  have hcomp : ∀ {T : Over Y} (x : T ⟶ B), x ≫ (𝟙 B) ^ c = x ^ c := fun x => by
    rw [MonObj.comp_pow, Category.comp_id]
  obtain ⟨W₁, o₁, c₁, H₁, -⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y B (c ^ 3) Unit (fun _ => C) (fun _ => h) B ((𝟙 B) ^ c) hB
    (fun _ => hC) hB (fun _ => hh) inferInstance hn
  obtain ⟨W₂, o₂, c₂, H₂, -⟩ := GlobalTheory.T.isClopen_torsion_kernel_locus Y B (c ^ 3) Unit (fun _ => B) (fun _ => (𝟙 B) ^ c) C h hB
    (fun _ => hB) hC (fun _ => inferInstance) hh hn
  refine ⟨W₁ ∩ W₂, o₁.inter o₂, c₁.inter c₂, fun Tb t => ?_⟩
  rw [Set.subset_inter_iff, H₁, H₂]
  constructor
  · rintro ⟨h₁, h₂⟩ T σ hσ x hx
    rw [hT]
    refine ⟨fun hx' => ?_, fun hx' => ?_⟩
    · rw [← hcomp]; exact h₁ T σ hσ x hx fun _ => hx'
    · exact h₂ T σ hσ x hx fun _ => by rw [hcomp]; exact hx'
  · intro H
    refine ⟨fun T σ hσ x hx hx' => ?_, fun T σ hσ x hx hx' => ?_⟩
    · rw [hcomp]; exact ((H T σ hσ x hx).1 ((hT T x).2 (hx' ())))
    · exact (hT T x).1 ((H T σ hσ x hx).2 (by rw [← hcomp]; exact hx' ()))

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorPullbackKernelLocusIsClopenStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.harrisTaylor_pullback_kernel_locus_isClopen : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ PolKerAt o ψ' c t := by
  first | exact @GlobalTheory.UPel.HT.ES.polKer_locus_clopen | exact GlobalTheory.UPel.HT.ES.polKer_locus_clopen | exact @GlobalTheory.UPel.HT.ES.isMonHom_id_npow | exact GlobalTheory.UPel.HT.ES.isMonHom_id_npow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowPolarizationIsoPullbackOfDescent
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.pow_polarization_iso_pullback_of_descent : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ P' : LB (G2 B).left, IsAxesTriv B P' → LBIso (o.P.pull (Hecke.sq2 ψ')) (Hecke.lbPow P' c) → LBIso (Hecke.lbPow o.P c) (P'.pull (Hecke.sq2 ψ)) → ∀ act' : OActN D.O B, (∀ a : D.O, o.act.act a ≫ ψ = ψ ≫ act'.act a) → ∀ (κ : Type) [Field κ] [IsAlgClosed κ] (x : Sp κ ⟶ Y) (β : R →+* κ), x ≫ s = spMap β → ∃ I : TateIsoO D κ (Over.mk x ⟶ B) (fun a g => g ≫ act'.act a) (fun n g g' z => Out.WeilIs B (P'.pull (lift (𝟙 B) (𝟙 B)).left) n g g' (unitOn z)), ∀ y, toUnit _ ≫ (o.eta y ≫ ψ) = I.ev N y := by
  first | exact @UpperTheory.Cb.pow_polarization_iso_pullback_of_descent | exact UpperTheory.Cb.pow_polarization_iso_pullback_of_descent
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenLocusOfAnnihilator
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_clopen_locus_of_annihilator : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ TjAt r w j o ψ t := by
  first | exact @UpperTheory.Cb.exists_clopen_locus_of_annihilator | exact UpperTheory.Cb.exists_clopen_locus_of_annihilator
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenKernelStableHarrisTaylor
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenKernelStableHarrisTaylor
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem exists_clopen_kerStableAt : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ KerStableAt o ψ t := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp ⟨e, he⟩ hB hq
  have hc : IsUnit (c : Γ(Y, ⊤)) := by
    have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
    rw [← Nat.cast_pow, map_natCast, ← he] at this
    exact this
  haveI : IsMonHom ψ := hq.1
  haveI : IsMonHom ψ' := hq.2.1
  haveI := D.finO
  obtain ⟨S, hS⟩ := Module.Finite.fg_top (R := ℤ) (M := D.O)
  have key : ∀ a : D.O, ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y),
      Set.range t.base ⊆ W ↔ ∀ (T : Over Y) (σ : T.left ⟶ Tb), σ ≫ t = T.hom → ∀ g : T ⟶ o.A,
        g ^ c = 1 → g ≫ ψ = 1 → g ≫ o.act.act a ≫ ψ = 1 := by
    intro a
    haveI := o.act.hom a
    obtain ⟨W, hW1, hW2, hW, -⟩ := GlobalTheory.LevCover.kerlocus_open_closed Y o.A c Unit (fun _ => B) (fun _ => ψ) B
      (o.act.act a ≫ ψ) o.ab (fun _ => hB) hB (fun _ => inferInstance) inferInstance hc
    refine ⟨W, hW1, hW2, fun Tb t => (hW Tb t).trans ?_⟩
    simp only [forall_const]
  choose W hW1 hW2 hW using key
  have hkill : ∀ (T : Over Y) (g : T ⟶ o.A), g ≫ ψ = 1 → g ^ c = 1 := by
    intro T g hg
    have h1 : g ^ c = g ≫ (𝟙 o.A) ^ c := by rw [MonObj.comp_pow, Category.comp_id]
    rw [h1, ← hq.2.2.1, ← Category.assoc, hg, MonObj.one_comp]
  refine ⟨⋂ a ∈ S, W a, isOpen_biInter_finset (fun a _ => hW1 a),
    isClosed_iInter fun a => isClosed_iInter fun _ => hW2 a, fun Tb t => ?_⟩
  rw [Set.subset_iInter₂_iff]
  constructor
  · intro h T σ hσ g hg a
    let f : D.O →+ Additive (T ⟶ B) := AddMonoidHom.mk' (fun a => Additive.ofMul (g ≫ o.act.act a ≫ ψ))
      (fun a a' => by
        rw [o.act.add]
        haveI := o.act.hom a
        haveI := o.act.hom a'
        rw [MonObj.mul_comp, MonObj.comp_mul]
        rfl)
    have hSk : (S : Set D.O) ⊆ (f.toIntLinearMap.ker : Set D.O) := fun a ha => by
      have := (hW a Tb t).1 (h a ha) T σ hσ g (hkill T g hg) hg
      simp [f, this]
    have htop : (⊤ : Submodule ℤ D.O) ≤ LinearMap.ker f.toIntLinearMap := by
      rw [← hS]; exact Submodule.span_le.mpr hSk
    have ha : f a = 0 := htop Submodule.mem_top
    simpa [f] using ha
  · intro h a _
    exact (hW a Tb t).2 fun T σ hσ g _ hg => h T σ hσ g hg a

end GlobalTheory.UPel.HT.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClopenKernelStableHarrisTaylorStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_clopen_kernelStable_harrisTaylor : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ KerStableAt o ψ t := by
  first | exact @GlobalTheory.UPel.HT.ES.exists_clopen_kerStableAt | exact GlobalTheory.UPel.HT.ES.exists_clopen_kerStableAt
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolKerAtPullbackOfIsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.polKerAt_pullback_of_isGrpPullback : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁' : B₁ ⟶ o₁.A) (ψ' : B ⟶ o.A) (c : ℕ), IsGrpPullback B₁ B t θ → θ ≫ ψ'.left = ψ₁'.left ≫ m.φ → (PolKerAt o ψ' c t ↔ PolKerAt o₁ ψ₁' c (𝟙 T)) := by
  first | exact @UpperTheory.Cb.polKerAt_pullback_of_isGrpPullback | exact UpperTheory.Cb.polKerAt_pullback_of_isGrpPullback
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelStableIffPulledBackIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelStableIffPulledBackIdentity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace GlobalTheory.UPel.HT.ES.TrStab

theorem one_left' {S : Scheme.{0}} (G : Over S) [GrpObj G] (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  rw [Hom.one_def, Over.comp_left, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.toUnit_left']

theorem eq_one_of_push {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {θ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f θ) {T : Over S'} (x : T ⟶ G')
    (hx : x.left ≫ θ = T.hom ≫ f ≫ η[G].left) : x = 1 := by
  ext
  apply h.1.hom_ext
  · rw [hx, one_left', Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]
  · rw [Over.w x, Over.w (1 : T ⟶ G')]

theorem push_one {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']
    {θ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f θ) (T : Over S') :
    (1 : T ⟶ G').left ≫ θ = T.hom ≫ f ≫ η[G].left := by
  rw [one_left', Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]

end GlobalTheory.UPel.HT.ES.TrStab

namespace GlobalTheory.UPel.HT.ES

open TrStab

theorem kerStableAt_iff_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (KerStableAt o ψ t ↔ KerStableAt o₁ ψ₁ (𝟙 T)) := by
  intro p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁ ψ hB hψ
  constructor
  · intro h T' σ hσ g hg a
    rw [Category.comp_id] at hσ
    subst hσ
    have hG : pushPt m.cart.1.w g ≫ ψ = 1 := by
      ext
      rw [one_left', Over.comp_left]
      show (g.left ≫ m.φ) ≫ ψ.left = _
      rw [Category.assoc, hψ, ← Category.assoc, ← Over.comp_left, hg, push_one hB]
      rfl
    have h2 := h (Over.mk (T'.hom ≫ t)) T'.hom rfl (pushPt m.cart.1.w g) hG a
    apply eq_one_of_push hB
    have e := congrArg Over.Hom.left h2
    rw [one_left', Over.comp_left, Over.comp_left] at e
    simp only [Over.comp_left, Category.assoc]
    rw [← hψ, ← Category.assoc (o₁.act.act a).left, m.act a, Category.assoc]
    exact e
  · intro h T0 σ hσ g hg a
    have w : g.left ≫ o.A.hom = σ ≫ t := by rw [Over.w g, hσ]
    let g₁ : Over.mk σ ⟶ o₁.A := Over.homMk (m.cart.1.lift g.left σ w) (m.cart.1.lift_snd _ _ _)
    have hg₁ : g₁.left ≫ m.φ = g.left := m.cart.1.lift_fst _ _ _
    have h1 : g₁ ≫ ψ₁ = 1 := by
      apply eq_one_of_push hB
      rw [Over.comp_left, Category.assoc, ← hψ, ← Category.assoc, hg₁, ← Over.comp_left, hg, one_left', ← hσ, Category.assoc]
      rfl
    have h2 := h (Over.mk σ) σ (Category.comp_id σ) g₁ h1 a
    ext
    rw [one_left', Over.comp_left, Over.comp_left, ← hg₁, Category.assoc, ← Category.assoc m.φ (o.act.act a).left,
      ← m.act a]
    simp only [Category.assoc]
    rw [hψ]
    have e : (g₁ ≫ o₁.act.act a ≫ ψ₁).left ≫ θ = (1 : Over.mk σ ⟶ B₁).left ≫ θ := by rw [h2]
    rw [push_one hB] at e
    simp only [Over.comp_left, Category.assoc] at e
    rw [e, ← hσ, Category.assoc]
    rfl

end GlobalTheory.UPel.HT.ES
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelStableIffPulledBackIdentityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kernelStable_iff_pulledBack_identity : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (KerStableAt o ψ t ↔ KerStableAt o₁ ψ₁ (𝟙 T)) := by
  first | (exact @GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull) | (exact GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull) | (intros; apply GlobalTheory.UPel.HT.ES.kerStableAt_iff_pull  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeIffPulledBackIdentity
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeIffPulledBackIdentity
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES

theorem tjAt_pull_one_left {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G]
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') :
    (1 : T ⟶ G').left ≫ φ = (1 : Over.mk (T.hom ≫ f) ⟶ G).left := by
  have hw : ((1 : T ⟶ G').left ≫ φ) ≫ G.hom = (Over.mk (T.hom ≫ f)).hom := by
    rw [Category.assoc, h.1.w, ← Category.assoc, Over.w]
    rfl
  let x₀ : Over.mk (T.hom ≫ f) ⟶ G := Over.homMk ((1 : T ⟶ G').left ≫ φ) hw
  have e := h.2 T 1 1 x₀ x₀ rfl rfl
  rw [_root_.mul_one] at e
  have hxx : x₀ * x₀ = x₀ := by
    ext
    exact e
  have h1 : x₀ = 1 := mul_eq_right.mp hxx
  exact congrArg Over.Hom.left h1

theorem tjAt_iff_tjAt_pull : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B) (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (TjAt r w j o ψ t ↔ TjAt r w j o₁ ψ₁ (𝟙 T)) := by
  intro p _ D R _ b N T Y s₁ s t o₁ o m B₁ _ _ B _ _ θ ψ₁ ψ r w j hB hψ
  have key : ∀ (k : Type) [Field k] (σ : Sp k ⟶ T),
      ((∀ g : Over.mk (σ ≫ t) ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g) ∧
        Nat.card {g : Over.mk (σ ≫ t) ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} = Ideal.absNorm w ^ (D.m * j)) ↔
      ((∀ g : Over.mk σ ⟶ o₁.A, g ≫ ψ₁ = 1 → (∃ e : ℕ, KilledBy o₁ (uIdeal D r ^ e) g) → KilledBy o₁ w g) ∧
        Nat.card {g : Over.mk σ ⟶ o₁.A // g ≫ ψ₁ = 1 ∧ KilledBy o₁ w g} = Ideal.absNorm w ^ (D.m * j)) := by
    intro k _ σ
    obtain ⟨e, he, -⟩ := m.exists_ptEquiv (Over.mk (σ ≫ t)) σ rfl
    have hker : ∀ g : Over.mk σ ⟶ o₁.A, e g ≫ ψ = 1 ↔ g ≫ ψ₁ = 1 := by
      intro g
      have h1 : (e g ≫ ψ).left = (g ≫ ψ₁).left ≫ θ := by
        rw [Over.comp_left, he, Category.assoc, hψ, Over.comp_left, Category.assoc]
      have h2 : (1 : Over.mk (σ ≫ t) ⟶ B).left = (1 : Over.mk σ ⟶ B₁).left ≫ θ :=
        (tjAt_pull_one_left hB (Over.mk σ)).symm
      constructor
      · intro h
        apply Over.OverMorphism.ext
        apply hB.1.hom_ext
        · rw [← h1, ← h2, h]
        · rw [Over.w, Over.w]
      · intro h
        apply Over.OverMorphism.ext
        rw [h1, h2, h]
    have hact : ∀ (g : Over.mk σ ⟶ o₁.A) (c : D.O), e g ≫ o.act.act c = e (g ≫ o₁.act.act c) := fun g c => by
      ext
      rw [Over.comp_left, he, he, Over.comp_left, Category.assoc, Category.assoc, m.act]
    have hkill : ∀ (v : Ideal (𝓞 D.F)) (g : Over.mk σ ⟶ o₁.A), KilledBy o v (e g) ↔ KilledBy o₁ v g :=
      fun v g => forall₂_congr fun a _ => by rw [hact]; exact map_eq_one_iff _ e.injective
    refine and_congr ⟨fun h g hg hu => ?_, fun h g hg hu => ?_⟩ ?_
    · rw [← hkill]
      rw [← hker] at hg
      obtain ⟨n, hn⟩ := hu
      exact h (e g) hg ⟨n, (hkill _ g).2 hn⟩
    · obtain ⟨g₀, rfl⟩ := e.surjective g
      rw [hkill]
      rw [hker] at hg
      obtain ⟨n, hn⟩ := hu
      exact h g₀ hg ⟨n, (hkill _ g₀).1 hn⟩
    · rw [Nat.card_congr ((Equiv.subtypeEquiv e.toEquiv fun g₀ => by
        change _ ↔ e g₀ ≫ ψ = 1 ∧ KilledBy o w (e g₀)
        rw [hker, hkill]).symm)]
  constructor
  · intro h k _ _ _ x₁ _
    exact (key k x₁).1 (h k (x₁ ≫ t) ⟨x₁, rfl⟩)
  · intro h k _ _ _ x ⟨σ, hσ⟩
    subst hσ
    exact (key k σ).2 (h k σ ⟨σ, Category.comp_id σ⟩)

end GlobalTheory.UPel.HT.ES
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeIffPulledBackIdentityStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (T Y : Scheme.{0}) (s₁ : T ⟶ Sp R) (s : Y ⟶ Sp R) (t : T ⟶ Y) (o₁ : Obj b N s₁) (o : Obj b N s) (m : ObjMap o₁ o t) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (B : Over Y) [GrpObj B] [IsCommMonObj B] (θ : B₁.left ⟶ B.left) (ψ₁ : o₁.A ⟶ B₁) (ψ : o.A ⟶ B) (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), IsGrpPullback B₁ B t θ → m.φ ≫ ψ.left = ψ₁.left ≫ θ → (TjAt r w j o ψ t ↔ TjAt r w j o₁ ψ₁ (𝟙 T)) := by
  first | (exact @GlobalTheory.UPel.HT.ES.tjAt_iff_tjAt_pull) | (exact GlobalTheory.UPel.HT.ES.tjAt_iff_tjAt_pull) | (intros; apply GlobalTheory.UPel.HT.ES.tjAt_iff_tjAt_pull  <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjIsogeniesRepresentable
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogRep

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem exists_comp {S₁ S₂ S₃ : Scheme.{0}} {s₁ : S₁ ⟶ Sp R} {s₂ : S₂ ⟶ Sp R} {s₃ : S₃ ⟶ Sp R} {o₁ : Obj b N s₁}
    {o₂ : Obj b N s₂} {o₃ : Obj b N s₃} {f : S₁ ⟶ S₂} {g : S₂ ⟶ S₃} (h₁ : ObjMap o₁ o₂ f) (h₂ : ObjMap o₂ o₃ g) :
    ∃ m : ObjMap o₁ o₃ (f ≫ g), m.φ = h₁.φ ≫ h₂.φ := by
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

theorem exists_factor (hN : 3 ≤ N) (hNp : N.Coprime p) {S₀ S₁ T : Scheme.{0}} {s₀ : S₀ ⟶ Sp R} {s₁ : S₁ ⟶ Sp R}
    {t : T ⟶ Sp R} {o₀ : Obj b N s₀} {o₁ : Obj b N s₁} {o : Obj b N t} {g : S₁ ⟶ S₀} {h : T ⟶ S₁} {x : T ⟶ S₀}
    (e : h ≫ g = x) (m₁ : ObjMap o₁ o₀ g) (m : ObjMap o o₀ x) : ∃ m' : ObjMap o o₁ h, m'.φ ≫ m₁.φ = m.φ := by
  subst e
  obtain ⟨m'⟩ := GlobalTheory.T.harrisTaylorPullback_comp_factors p D R b N _ _ _ _ _ _ o₀ o₁ o g h m₁ m
  obtain ⟨n, hn⟩ := exists_comp m' m₁
  exact ⟨m', hn.symm.trans (GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ _ _ _ _ n m rfl)⟩

theorem exists_pull {S S' : Scheme.{0}} {s : S ⟶ Sp R} (f : S' ⟶ S) (o : Obj b N s) {s' : S' ⟶ Sp R}
    (e : f ≫ s = s') : ∃ o' : Obj b N s', Nonempty (ObjMap o' o f) := by
  subst e
  exact GlobalTheory.T.exists_harrisTaylorObject_pullback p D R b N S S' s f o

theorem isUnit_pow {S : Scheme.{0}} (s : S ⟶ Sp R) (hp : IsUnit ((p : ℕ) : R)) {c : ℕ} (hc : ∃ e : ℕ, c = p ^ e) :
    IsUnit (c : Γ(S, ⊤)) := by
  obtain ⟨e, rfl⟩ := hc
  have := (hp.pow e).map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom)
  rwa [← Nat.cast_pow, map_natCast] at this

theorem exists_obj {c : ℕ} {Y : Scheme.{0}} [IsLocallyNoetherian Y] {s : Y ⟶ Sp R} (o : Obj b N s) (B : Over Y)
    [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A) (hp : IsUnit ((p : ℕ) : R)) (hc : ∃ e : ℕ, c = p ^ e)
    (hB : IsAbelianScheme B) (hq : IsQuasiInv c ψ ψ') (h1 : KerStableAt o ψ (𝟙 Y)) (h2 : PolKerAt o ψ' c (𝟙 Y)) :
    ∃ (o' : Obj b N s) (χ : o.A ⟶ o'.A) (θ : o'.A.left ⟶ B.left), IsPIsog c o o' χ ∧
      IsGrpPullback o'.A B (𝟙 Y) θ ∧ ψ.left = χ.left ≫ θ := by
  obtain ⟨act', hact⟩ := GlobalTheory.T.exists_orderAction_descent_along_isogeny p D R b N c Y s o B ψ ψ' hp hc hB hq h1
  obtain ⟨P', hP', w1, w2⟩ := GlobalTheory.T.exists_polarization_descent_of_quasi_isogeny p D R b N c Y s o B ψ ψ' hp hc hB hq h2
  have hlie := GlobalTheory.T.harrisTaylor_lie_of_quasiInverseIsogeny p D R b N c Y s o B ψ ψ' hp hc hB hq act' hact
  haveI := hq.1
  let o' : Obj b N s :=
    { A := B, ab := hB, act := act', P := P', isLB := hP'.1, rig₁ := hP'.2.1, rig₂ := hP'.2.2
      symm := GlobalTheory.T.quasiInverse_root_bundle_symmetric p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2
      ample := GlobalTheory.T.relAmple_diag_root_pullback_quasiInverse p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2
      kerP := GlobalTheory.T.polarization_descent_along_quasi_isogeny_compat p D R b N c Y s o B ψ ψ' hp hc hB hq h2 P' hP' w1 w2
      rosati := GlobalTheory.T.quasiInverse_root_bundle_rosati_descended_action p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2 act' hact
      lie := hlie.1, lieRank := hlie.2
      eta := fun y => o.eta y ≫ ψ
      eta_add := fun x y => by rw [o.eta_add, MonObj.mul_comp]
      eta_lin := fun a x => by rw [o.eta_lin, Category.assoc, hact, Category.assoc]
      eta_ker := fun x => by rw [o.eta_ker, MonObj.one_comp]
      geom := GlobalTheory.T.pow_polarization_iso_pullback_of_descent p D R b N c Y s o B ψ ψ' hp hc hB hq P' hP' w1 w2 act' hact }
  exact ⟨o', ψ, 𝟙 _, ⟨hc, hq.1, hact, fun _ => rfl, ⟨w2⟩, ψ', hq.2.1, hq.2.2.1, hq.2.2.2⟩,
    GlobalTheory.SiegLower.isGrpPullback_id B, (Category.comp_id _).symm⟩

end

theorem exists_rep : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (o₀ : Obj b N (Y.hom ≫ s)) (m₀ : ObjMap o₀ o Y.hom) (o' : Obj b N (Y.hom ≫ s)) (ψ : o₀.A ⟶ o'.A), IsFinite Y.hom ∧ Etale Y.hom ∧ IsPIsog c o₀ o' ψ ∧ IsTj r w j o₀ o' ψ ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (o₁ o₁' : Obj b N (x ≫ s)) (m : ObjMap o₁ o x) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (m₀' : ObjMap o₁ o₀ y) (m₁ : ObjMap o₁' o' y), m₀'.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ := by
  intro p _ D R _ _ b N hN hNp hp r w j c _ _ _ hc0 _ S _ s o
  have hc : ∃ e : ℕ, c = p ^ e := hc0.imp fun _ h => h.1
  have hcpos : 0 < c := by
    obtain ⟨e, rfl⟩ := hc
    exact pow_pos (Fact.out : p.Prime).pos e
  obtain ⟨Z, hZf, hZe, hZ⟩ := GlobalTheory.T.isogeny_representable_finite_etale S o.A c o.ab hcpos (isUnit_pow s hp hc)
  obtain ⟨oZ, ⟨mZ⟩⟩ := exists_pull Z.hom o rfl
  obtain ⟨B, _, _, ψ, ψ', hB, hq, huniv⟩ := hZ oZ.A mZ.φ mZ.cart
  obtain ⟨W₁, a₁, c₁, H₁⟩ := GlobalTheory.T.exists_clopen_kernelStable_harrisTaylor p D R b N c _ _ oZ B ψ ψ' hp hc hB hq
  obtain ⟨W₂, a₂, c₂, H₂⟩ := GlobalTheory.T.harrisTaylor_pullback_kernel_locus_isClopen p D R b N c _ _ oZ B ψ ψ' hp hc hB hq
  obtain ⟨W₃, a₃, c₃, H₃⟩ := GlobalTheory.T.exists_clopen_locus_of_annihilator p D R b N c _ _ oZ B ψ ψ' hp hc hB hq r w j
  haveI := hZf
  haveI := hZe
  obtain ⟨Y, i, hYf, hYe, hmono, Hi⟩ := GlobalTheory.LevCover.exists_sub (Z := Z)
    ⟨W₁ ∩ W₂ ∩ W₃, (a₁.inter a₂).inter a₃⟩ ((c₁.inter c₂).inter c₃)
  haveI := hYf
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  have hi : Set.range i.left.base ⊆ W₁ ∩ W₂ ∩ W₃ := (Hi Y i).2 ⟨𝟙 Y, Category.id_comp i⟩
  obtain ⟨o₀, ⟨mi⟩⟩ := exists_pull i.left oZ (s' := Y.hom ≫ s) (by rw [← Category.assoc, Over.w i])
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ObjMap o₀ o Y.hom, m₀.φ = mi.φ ≫ mZ.φ := by
    have H : ∀ g, i.left ≫ Z.hom = g → ∃ m₀ : ObjMap o₀ o g, m₀.φ = mi.φ ≫ mZ.φ := by
      rintro _ rfl
      exact exists_comp mi mZ
    exact H _ (Over.w i)
  obtain ⟨B₀, _, _, θ₀, ψ₀, ψ₀', hB₀, hθ₀, hq₀, e₀, e₀'⟩ :=
    GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback _ _ i.left oZ.A B c ψ ψ' o₀.A mi.φ hB hq mi.cart
  obtain ⟨o', χ, θ₁, hχ, hθ₁, e₁⟩ := exists_obj o₀ B₀ ψ₀ ψ₀' hp hc hB₀ hq₀
    ((GlobalTheory.T.kernelStable_iff_pulledBack_identity p D R b N _ _ _ _ _ o₀ oZ mi B₀ B θ₀ ψ₀ ψ hθ₀ e₀).1 ((H₁ _ _).1 fun z hz => (hi hz).1.1))
    ((GlobalTheory.T.polKerAt_pullback_of_isGrpPullback p D R b N _ _ _ _ _ o₀ oZ mi B₀ B θ₀ ψ₀' ψ' c hθ₀ e₀').1 ((H₂ _ _).1 fun z hz => (hi hz).1.2))
  have hθ : IsGrpPullback o'.A B i.left (θ₁ ≫ θ₀) := (hθ₁.comp hθ₀).congr (Category.id_comp _) rfl
  have eχ : mi.φ ≫ ψ.left = χ.left ≫ θ₁ ≫ θ₀ := by rw [e₀, e₁, Category.assoc]
  have htj : IsTj r w j o₀ o' χ := (tjAt_id_iff r w j o₀ o' χ).1
    ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o₀ oZ mi o'.A B (θ₁ ≫ θ₀) χ ψ r w j hθ eχ).1
      ((H₃ _ _).1 fun z hz => (hi hz).2))
  refine ⟨Y, o₀, m₀, o', χ, hYf, hYe, hχ, htj, fun T x o₁ o₁' m ψ₁ h1 h2 => ?_⟩
  obtain ⟨ψ₁', hq₁⟩ := h1.exists_quasiInv
  obtain ⟨z, ⟨hz, θ, θ', eθ, hθa, hθb, eψ⟩, zu⟩ := huniv T x o₁.A m.φ o₁'.A ψ₁ ψ₁' m.cart o₁'.ab hq₁
  obtain ⟨mz, hmz⟩ := exists_factor hN hNp hz mZ m
  obtain rfl : θ = mz.φ := mZ.cart.1.hom_ext (eθ.trans hmz.symm) (hθa.1.w.trans mz.cart.1.w.symm)
  have eψ' := GlobalTheory.T.quasiInverseIsogeny_square_compat_comp_quasiInv _ _ z oZ.A B c ψ ψ' o₁.A o₁'.A mz.φ θ' ψ₁ ψ₁' o₁'.ab hcpos hq hq₁ mz.cart eψ
  have hr : Set.range z.base ⊆ W₁ ∩ W₂ ∩ W₃ := Set.subset_inter (Set.subset_inter
    ((H₁ _ z).2 ((GlobalTheory.T.kernelStable_iff_pulledBack_identity p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁ ψ hθb eψ).2 (h1.kerStableAt _)))
    ((H₂ _ z).2 ((GlobalTheory.T.polKerAt_pullback_of_isGrpPullback p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁' ψ' c hθb eψ').2
      (GlobalTheory.T.polarization_kernel_of_p_isogeny_quasi_inverse p D R b N c _ _ o₁ o₁' ψ₁ ψ₁' hp h1 hq₁))))
    ((H₃ _ z).2 ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o₁ oZ mz o₁'.A B θ' ψ₁ ψ r w j hθb eψ).2
      ((tjAt_id_iff r w j o₁ o₁' ψ₁).2 h2)))
  obtain ⟨y, hy⟩ := (Hi (Over.mk x) (Over.homMk z hz)).1 hr
  have hyz : y.left ≫ i.left = z := congrArg CommaMorphism.left hy
  haveI : Mono i.left := inferInstanceAs (Mono ((Over.forget S).map i))
  refine ⟨y.left, ⟨Over.w y, ?_⟩, ?_⟩
  · obtain ⟨m₀', hm⟩ := exists_factor hN hNp hyz mi mz
    let φ₁ : o₁'.A.left ⟶ o'.A.left := hθ.1.lift θ' (o₁'.A.hom ≫ y.left) (by rw [hθb.1.w, Category.assoc, hyz])
    have f1 : φ₁ ≫ θ₁ ≫ θ₀ = θ' := hθ.1.lift_fst _ _ _
    have f2 : φ₁ ≫ o'.A.hom = o₁'.A.hom ≫ y.left := hθ.1.lift_snd _ _ _
    have hφ₁ : IsGrpPullback o₁'.A o'.A y.left φ₁ := hθ.cancel (hθb.congr hyz.symm f1.symm) f2
    have e : m₀'.φ ≫ χ.left = ψ₁.left ≫ φ₁ := by
      apply hθ.1.hom_ext
      · rw [Category.assoc, ← eχ, ← Category.assoc, hm, eψ, Category.assoc, f1]
      · rw [Category.assoc, Over.w χ, m₀'.cart.1.w, Category.assoc, f2, ← Category.assoc, Over.w ψ₁]
    obtain ⟨m₁, hm₁⟩ := GlobalTheory.T.exists_objMap_of_p_isogeny_pullback p D R b N c _ _ _ _ y.left o₁ o₁' o₀ o' m₀' ψ₁ χ φ₁ hp h1 hχ hφ₁ e
    exact ⟨m₀', m₁, by rw [hm₁, e]⟩
  · rintro y' ⟨hy', n₀, n₁, e⟩
    rw [← cancel_mono i.left, hyz]
    have hx : (y' ≫ i.left) ≫ Z.hom = x := by rw [Category.assoc, Over.w i, hy']
    obtain ⟨n, hn⟩ := exists_comp n₀ mi
    obtain ⟨n', hn'⟩ := exists_comp n mZ
    refine zu _ ⟨hx, n₀.φ ≫ mi.φ, n₁.φ ≫ θ₁ ≫ θ₀, ?_, n₀.cart.comp mi.cart, n₁.cart.comp hθ, ?_⟩
    · rw [← hn, ← hn']
      exact GlobalTheory.T.harrisTaylor_pullback_abelian_map_unique_of_base_eq p D R b N hN hNp _ _ _ _ _ _ _ _ n' m hx
    · rw [Category.assoc, eχ, ← Category.assoc, e, Category.assoc]

end GlobalTheory.UPel.HT.ES.IsogRep
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjIsogeniesRepresentableStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.harrisTaylor_typeTj_isogenies_representable : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → IsUnit ((p : ℕ) : R) → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp R) (o : Obj b N s), ∃ (Y : Over S) (o₀ : Obj b N (Y.hom ≫ s)) (m₀ : ObjMap o₀ o Y.hom) (o' : Obj b N (Y.hom ≫ s)) (ψ : o₀.A ⟶ o'.A), IsFinite Y.hom ∧ Etale Y.hom ∧ IsPIsog c o₀ o' ψ ∧ IsTj r w j o₀ o' ψ ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (o₁ o₁' : Obj b N (x ≫ s)) (m : ObjMap o₁ o x) (ψ₁ : o₁.A ⟶ o₁'.A), IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (m₀' : ObjMap o₁ o₀ y) (m₁ : ObjMap o₁' o' y), m₀'.φ ≫ ψ.left = ψ₁.left ≫ m₁.φ := by
  first | (exact @GlobalTheory.UPel.HT.ES.IsogRep.exists_rep) | (exact GlobalTheory.UPel.HT.ES.IsogRep.exists_rep) | (intros; apply GlobalTheory.UPel.HT.ES.IsogRep.exists_rep  <;> assumption)
end
