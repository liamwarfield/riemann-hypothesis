module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFunctionThetaSectionIntegralPoint
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLaws
public import Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ExistsFiniteEtaleTrivializingTorsionAbelianSchem

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvcPowRight
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.UPel.HT.ES.KerFin

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

theorem evc_pow_right {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) {T : Over S} (x y : T ⟶ o.A) (n : ℕ) :
    evc o.isLB x (y ^ n) = n • evc o.isLB x y := by
  obtain ⟨-, ad⟩ := GlobalTheory.BirigidRoot.additive_of_birigid o.ab o.isLB o.rig₁ o.rig₂
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact evc_one_right o.isLB o.rig₂ x
  | succ n ih => rw [pow_succ, (GlobalTheory.BirigidLift.isAdditive_swap_iff o.isLB).1 ad, ih, succ_nsmul]

theorem evc_isog {S : Scheme.{0}} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) {T : Over S} (x y : T ⟶ o.A) :
    evc o'.isLB (x ≫ ψ) (y ≫ ψ) = c • evc o.isLB x y := by
  obtain ⟨e⟩ := h.2.2.2.2.1
  have hQ : (Hecke.lbPow o.P c).IsLB := LB.isLB_linComb o.isLB _ _
  have hP : (ev o'.P (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ)).IsLB := pull_isLB o'.isLB _
  have e₁ : cls _ hQ = cls _ hP := (cls_eq_iff hQ hP).2 e
  have e₂ : cls _ hQ = c • cls o.P o.isLB := by
    refine (cls_linComb o.isLB _ _ hQ).trans ?_
    simp [pull_id]
  have z := evc_ev o'.isLB (fst o.A o.A ≫ ψ) (snd o.A o.A ≫ ψ) hP x y
  rw [lift_fst_assoc, lift_snd_assoc] at z
  rw [← z, evc, ← e₁, e₂, map_nsmul]
  rfl

theorem evc_adj {S : Scheme.{0}} {s : S ⟶ Sp R} {c : ℕ} {o o' : Obj b N s} {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) (ψ' : o'.A ⟶ o.A) [IsMonHom ψ'] (h' : ψ' ≫ ψ = (𝟙 o'.A) ^ c) {T : Over S}
    (x : T ⟶ o.A) (y : T ⟶ o'.A) : evc o'.isLB (x ≫ ψ) y = evc o.isLB x (y ≫ ψ') := by
  haveI := h.2.1
  obtain ⟨hfl, hsu, hqc⟩ := SiegUniqBase.flat_surjective_qc_pow S o'.A o'.ab c h.pos
  have key := GlobalTheory.BirigUniq.pic_eq_zero_of_fpqc o.A o'.A o'.A o.ab ((𝟙 o'.A) ^ c) hfl hsu hqc
    (evc o'.isLB (fst o.A o'.A ≫ ψ) (snd o.A o'.A) - evc o.isLB (fst o.A o'.A) (snd o.A o'.A ≫ ψ')) (by
      rw [map_sub, pull_evc, pull_evc, lift_fst_assoc, lift_fst, MonObj.one_comp,
        evc_one_left o'.isLB o'.rig₁, evc_one_left o.isLB o.rig₁, sub_self]) (by
      rw [map_sub, pull_evc, pull_evc, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc, sub_eq_zero]
      have e₁ : (snd o.A o'.A ≫ (𝟙 o'.A) ^ c) ≫ ψ' = (snd o.A o'.A ≫ ψ') ^ c := by
        rw [MonObj.comp_pow, Category.comp_id, GlobalTheory.BirigidRoot.pow_comp_hom]
      rw [e₁, evc_pow_right, ← h', ← Category.assoc, evc_isog h])
  have z := congrArg (CechPic.pull (lift x y).left) (sub_eq_zero.1 key)
  rwa [pull_evc, pull_evc, lift_fst_assoc, lift_fst, lift_snd, lift_snd_assoc] at z

theorem evc_rosati {S : Scheme.{0}} {s : S ⟶ Sp R} (o : Obj b N s) (a : D.O) {T : Over S} (x y : T ⟶ o.A) :
    evc o.isLB (x ≫ o.act.act a) y = evc o.isLB x (y ≫ o.act.act (D.star a).unop) := by
  have h₁ : (ev o.P (fst o.A o.A ≫ o.act.act a) (snd o.A o.A)).IsLB := pull_isLB o.isLB _
  have h₂ : (ev o.P (fst o.A o.A) (snd o.A o.A ≫ o.act.act (D.star a).unop)).IsLB := pull_isLB o.isLB _
  have e := (cls_eq_iff h₁ h₂).2 (o.rosati a)
  have z₁ := evc_ev o.isLB _ _ h₁ x y
  have z₂ := evc_ev o.isLB _ _ h₂ x y
  rw [lift_fst_assoc, lift_snd] at z₁
  rw [lift_fst, lift_snd_assoc] at z₂
  rw [← z₁, ← z₂, evc, evc, e]

theorem mulN_eq_pow {S : Scheme.{0}} (A : Over S) [GrpObj A] (n : ℕ) : mulN A n = (𝟙 A) ^ n := by
  induction n with
  | zero => rw [pow_zero]; rfl
  | succ n ih => rw [pow_succ, ← ih]; rfl

theorem star_ker_le {k : Type} [CommRing k] {s : Sp k ⟶ Sp R} {c : ℕ} {o o₁ o₂ : Obj b N s} {ψ₁ : o.A ⟶ o₁.A}
    {ψ₂ : o.A ⟶ o₂.A} (h₁ : IsPIsog c o o₁ ψ₁) (h₂ : IsPIsog c o o₂ ψ₂) (a : D.O)
    (H : ∀ (T : Over (Sp k)) (x : T ⟶ o.A), x ≫ ψ₂ = 1 → (x ≫ o.act.act a) ≫ ψ₁ = 1)
    (T : Over (Sp k)) (x : T ⟶ o.A) (hx : x ≫ ψ₁ = 1) : (x ≫ o.act.act (D.star a).unop) ≫ ψ₂ = 1 := by
  haveI := h₁.2.1
  haveI := h₂.2.1
  haveI := o.act.hom a
  haveI := o.act.hom (D.star a).unop
  obtain ⟨φ₁, hφ₁, e₁, e₁'⟩ := h₁.2.2.2.2.2
  obtain ⟨φ₂, hφ₂, e₂, e₂'⟩ := h₂.2.2.2.2.2
  have hom_ext_spAlg {T B : Over (Sp k)} (a b : T ⟶ B)
      (h : ∀ (S : Type) [CommRing S] [Algebra k S] (g : GlobalTheory.PDiv.SpAlg k S ⟶ T), g ≫ a = g ≫ b) : a = b := by
    ext1
    apply T.left.affineOpenCover.openCover.hom_ext
    intro j
    let C : CommRingCat := T.left.affineOpenCover.X j
    let φ : CommRingCat.of k ⟶ C := Spec.preimage (T.left.affineOpenCover.f j ≫ T.hom)
    letI : Algebra k C := φ.hom.toAlgebra
    let g : GlobalTheory.PDiv.SpAlg k C ⟶ T := Over.homMk (T.left.affineOpenCover.f j) (by
      show _ = Spec.map (CommRingCat.ofHom (algebraMap k C))
      rw [← Spec.map_preimage (T.left.affineOpenCover.f j ≫ T.hom)]
      rfl)
    have := congrArg CommaMorphism.left (h C g)
    simp only [g, Over.comp_left, Over.homMk_left] at this
    exact this
  have factor (A B : Over (Sp k)) [GrpObj A] [GrpObj B] (hA : IsAbelianScheme A)
      (n : ℕ) (hn : 0 < n) (F : A ⟶ B) (hF : IsMonHom F)
      (hker : ∀ (S : Type) [CommRing S] [Algebra k S] (z : GlobalTheory.PDiv.SpAlg k S ⟶ A),
        z ^ n = 1 → z ≫ F = 1) : ∃ f : A ⟶ B, IsMonHom f ∧ F = mulN A n ≫ f := by
    haveI := hA.comm
    obtain ⟨hfin, hflat, hsurj⟩ := GlobalTheory.T.abelianScheme_mulN_finite_flat_surjective k A hA n hn
    haveI : IsMonHom (mulN A n) := GlobalTheory.MulEtaleDvr.isMonHom_mulN A n
    have hqc : QuasiCompact (mulN A n).left := inferInstance
    have h : ∀ (T : Over (Sp k)) (x : T ⟶ A), x ≫ mulN A n = 1 → x ≫ F = 1 := by
      intro T x hx
      apply hom_ext_spAlg
      intro S _ _ g
      have hxn : x ^ n = 1 := by
        rw [← hx, GlobalTheory.MulEtaleDvr.mulN_eq_pow, MonObj.comp_pow, Category.comp_id]
      have hz : (g ≫ x) ^ n = 1 := by
        rw [← MonObj.comp_pow, hxn, MonObj.comp_one]
      rw [← Category.assoc, hker S (g ≫ x) hz, MonObj.comp_one]
    obtain ⟨⟨ψ, hψ, hc⟩, -⟩ := exists_monHom_factor_of_flat_surjective _ A A B (mulN A n) F inferInstance hF
      hflat hsurj hqc h
    exact ⟨ψ, hψ, hc.symm⟩
  obtain ⟨β, hβ, eβ⟩ := factor o₂.A o₁.A o₂.ab c h₁.pos
    (φ₂ ≫ o.act.act a ≫ ψ₁) inferInstance (fun S _ _ z hz => by
      have := H _ (z ≫ φ₂) (by rw [Category.assoc, e₂', MonObj.comp_pow, Category.comp_id, hz])
      simpa only [Category.assoc] using this)
  rw [mulN_eq_pow] at eβ
  have hfac : φ₂ ≫ o.act.act a = β ≫ φ₁ := by
    obtain ⟨hfl, hsu, -⟩ := SiegUniqBase.flat_surjective_qc_pow _ o₂.A o₂.ab c h₁.pos
    haveI := hfl
    haveI := hsu
    haveI : Epi ((𝟙 o₂.A) ^ c).left := Flat.epi_of_flat_of_surjective _
    have e : (((𝟙 o₂.A) ^ c) ≫ φ₂ ≫ o.act.act a).left = (((𝟙 o₂.A) ^ c) ≫ β ≫ φ₁).left := by
      rw [← Category.assoc _ β, ← eβ, Category.assoc, Category.assoc, e₁, GlobalTheory.BirigidRoot.pow_comp_hom,
        Category.id_comp, ← Category.assoc, MonObj.comp_pow, Category.comp_id]
    rw [Over.comp_left, Over.comp_left] at e
    exact Over.OverMorphism.ext ((cancel_epi ((𝟙 o₂.A) ^ c).left).1 e)
  obtain ⟨e, he, hker⟩ := o₂.kerP
  set y := (x ≫ o.act.act (D.star a).unop) ≫ ψ₂ with hy
  have hye : y ^ e = 1 := by
    refine hker T y ((triv_ev_iff o₂.isLB _ _).2 ?_)
    rw [hy, ← Category.assoc, evc_adj h₂ φ₂ e₂', ← Category.assoc, evc_rosati, D.star_star, Category.assoc, hfac,
      ← Category.assoc, ← evc_adj h₁ φ₁ e₁', Category.assoc, hx, MonObj.comp_one]
    exact evc_one_left o₁.isLB o₁.rig₁ _
  have hyc : y ^ c = 1 := by
    have hxc : x ^ c = 1 := by
      rw [← Category.comp_id x, ← MonObj.comp_pow, ← e₁, ← Category.assoc, hx, MonObj.one_comp]
    rw [hy, ← GlobalTheory.BirigidRoot.pow_comp_hom, ← GlobalTheory.BirigidRoot.pow_comp_hom, hxc, MonObj.one_comp, MonObj.one_comp]
  obtain ⟨m, rfl⟩ := h₁.1
  have := pow_gcd_eq_one.2 ⟨hye, hyc⟩
  rwa [(Nat.Coprime.pow_right m he).gcd_eq_one, pow_one] at this

end GlobalTheory.UPel.HT.ES.KerFin
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyRepresentableFiniteEtale
section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsoOfSameKer
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SameKer

theorem exists_iso_of_sameKer : ∀ (Tb : Scheme.{0}) (G' B A' : Over Tb) [GrpObj G'] [GrpObj B] [GrpObj A'] (π' : G' ⟶ B) (χ₁ : A' ⟶ G') (χ₁' : G' ⟶ A') (k : ℕ), IsAbelianScheme A' → IsUnit (k : Γ(Tb, ⊤)) → IsMonHom π' → IsMonHom χ₁ → IsMonHom χ₁' → Flat π'.left → Surjective π'.left → QuasiCompact π'.left → χ₁ ≫ χ₁' = (𝟙 A') ^ k → (∀ (T : Over Tb) (x : T ⟶ G'), x ≫ χ₁' = 1 ↔ x ≫ π' = 1) → ∃ β : A' ⟶ B, IsIso β ∧ IsMonHom β ∧ χ₁' ≫ β = π' := by
  intro Tb G' B A' _ _ _ π' χ₁ χ₁' k hA hk hπ hχ hχ' fl su qc hcomp hker
  obtain ⟨⟨α, hα, hαeq⟩, -⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective Tb G' B A' π' χ₁' hπ hχ' fl su qc
    (fun T x hx => (hker T x).2 hx)
  have ker : ∀ (T : Over Tb) (x : T ⟶ B), x ≫ α = 1 → x = 1 := by
    intro T x hx
    have pb := (IsPullback.of_hasPullback x π').map (Over.forget Tb)
    have : Flat (pullback.fst x π').left := MorphismProperty.of_isPullback (P := @Flat) pb.flip fl
    have : Surjective (pullback.fst x π').left :=
      MorphismProperty.of_isPullback (P := @Surjective) pb.flip su
    have : Epi (pullback.fst x π').left := Flat.epi_of_flat_of_surjective _
    have : Epi (pullback.fst x π') := Over.epi_of_epi_left _
    have h1 : pullback.snd x π' ≫ χ₁' = 1 := by
      rw [← hαeq, ← Category.assoc, ← pullback.condition, Category.assoc, hx, MonObj.comp_one]
    have h2 := (hker _ _).1 h1
    rw [← cancel_epi (pullback.fst x π'), pullback.condition, h2, MonObj.comp_one]
  have hmono : Mono α := ⟨fun {Z} u v huv => by
    have h : (u * v⁻¹) ≫ α = 1 := by rw [MonObj.mul_comp, GrpObj.inv_comp, huv, mul_inv_cancel]
    exact mul_inv_eq_one.1 (ker _ _ h)⟩
  obtain ⟨hkm, hkf, hke, hks⟩ := GlobalTheory.abelianScheme_id_pow_finite_etale_surjective Tb A' k hA hk
  obtain ⟨⟨β, hβ, hβeq⟩, hepik⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective Tb A' A' B ((𝟙 A') ^ k)
    (χ₁ ≫ π') hkm inferInstance inferInstance hks inferInstance (fun T x hx => by
      have h := (hker T (x ≫ χ₁)).1 (by rw [Category.assoc, hcomp, hx])
      rw [Category.assoc] at h
      exact h)
  have e1 : β ≫ α = 𝟙 A' := by
    rw [← cancel_epi ((𝟙 A') ^ k), ← Category.assoc, hβeq, Category.assoc, hαeq, hcomp, Category.comp_id]
  have e2 : α ≫ β = 𝟙 B := by
    rw [← cancel_mono α, Category.assoc, e1, Category.comp_id, Category.id_comp]
  refine ⟨β, ⟨⟨α, e1, e2⟩⟩, hβ, ?_⟩
  rw [← hαeq, Category.assoc, e2, Category.comp_id]

end GlobalTheory.SameKer
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuotientPow
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT
open GlobalTheory.ZM GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.TranslQuotientPow

theorem isMonHom_id_pow {Y : Scheme.{0}} (G : Over Y) [GrpObj G] [IsCommMonObj G] (n : ℕ) :
    IsMonHom ((𝟙 G) ^ n : G ⟶ G) := by
  induction n with
  | zero => rw [pow_zero]; infer_instance
  | succ n ih => rw [pow_succ]; exact inferInstanceAs (IsMonHom (lift ((𝟙 G) ^ n) (𝟙 G) ≫ μ[G]))

theorem comp_id_pow {Y : Scheme.{0}} {G W : Over Y} [GrpObj G] (x : W ⟶ G) (n : ℕ) :
    x ≫ (𝟙 G) ^ n = x ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, comp_one]
  | succ n ih => rw [pow_succ, pow_succ, comp_mul, ih, Category.comp_id]

theorem pow_comp_hom {Y : Scheme.{0}} {G A W : Over Y} [GrpObj G] [GrpObj A] (q : G ⟶ A) [IsMonHom q]
    (x : W ⟶ G) (n : ℕ) : (x ^ n) ≫ q = (x ≫ q) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, one_comp]
  | succ n ih => rw [pow_succ, pow_succ, mul_comp, ih]

end GlobalTheory.TranslQuotientPow
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleTrivializingTorsionAbelianSchem
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.exists_finite_etale_trivializing_torsion_abelianScheme : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (H : Over Y.left) (_ : GrpObj H) (i : H ⟶ A₀), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ i ^ k = 1 ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] (f : A₁ ⟶ B₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsMonHom f → (∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 → g ^ k = 1) → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ f = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y ∧ h ≫ i.left ≫ φ₀ = g.left ≫ φ₁ := by
  first | exact @UpperTheory.Cb.exists_finite_etale_trivializing_torsion_abelianScheme | exact UpperTheory.Cb.exists_finite_etale_trivializing_torsion_abelianScheme
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyRepresentableFiniteEtale
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace GlobalTheory.UPel.HT.ES.IsogRep

theorem eq_one_iff_of_isGrpPullback {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} [GrpObj G] {G' : Over S'}
    [GrpObj G'] {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) {T : Over S'} (z : T ⟶ G') :
    z = 1 ↔ z.left ≫ φ = T.hom ≫ f ≫ η[G].left := by
  have e1 : (1 : T ⟶ G').left ≫ φ = T.hom ≫ f ≫ η[G].left := by
    show (T.hom ≫ η[G'].left) ≫ φ = _
    rw [Category.assoc, ReciprocityTheory.ChartRestriction.G.Out.PullGtPf.IsGrpPullback.one_left h]
  constructor
  · rintro rfl; exact e1
  · intro hz
    apply Over.OverMorphism.ext
    apply h.1.hom_ext
    · rw [hz, e1]
    · rw [Over.w, Over.w]

theorem comp_pow_hom {S : Scheme.{0}} {T H A : Over S} [GrpObj A] (z : T ⟶ H) (f : H ⟶ A) (n : ℕ) :
    z ≫ f ^ n = (z ≫ f) ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, comp_one]
  | succ n ih => rw [pow_succ, pow_succ, comp_mul, ih]

theorem exists_quot_quasiInv {Y : Scheme.{0}} [IsLocallyNoetherian Y] (A₀ : Over Y) [GrpObj A₀] [IsCommMonObj A₀]
    (H : Over Y) [GrpObj H] (i : H ⟶ A₀) (k : ℕ) (hA : IsAbelianScheme A₀) (hi : IsMonHom i) (hm : Mono i)
    (hf : IsFinite H.hom) (he : Etale H.hom) (hk : i ^ k = 1) :
    ∃ (B : Over Y) (_ : GrpObj B) (_ : IsCommMonObj B) (ψ : A₀ ⟶ B) (ψ' : B ⟶ A₀), IsAbelianScheme B ∧
      IsQuasiInv k ψ ψ' ∧ ∀ (T : Over Y) (x : T ⟶ A₀), x ≫ ψ = 1 ↔ ∃ z : T ⟶ H, z ≫ i = x := by
  obtain ⟨B, gB, q, hB, hqm, hqfin, hqflat, hqsurj, hq⟩ :=
    GlobalTheory.IwLevel.quotGlobal_holds Y A₀ H i hA hi hm hf inferInstance
  have hcB : IsCommMonObj B := hB.comm
  have hker : ∀ (T : Over Y) (x : T ⟶ A₀), x ≫ q = 1 ↔ ∃ z : T ⟶ H, z ≫ i = x := by
    intro T x
    constructor
    · intro h
      have h' : x ≫ q = (1 : T ⟶ A₀) ≫ q := by rw [h, MonObj.one_comp]
      refine ⟨hq.lift x 1 h' ≫ fst H A₀, ?_⟩
      have h1 := hq.lift_fst x 1 h'
      rw [comp_mul, hq.lift_snd, _root_.mul_one] at h1
      rw [Category.assoc, h1]
    · rintro ⟨y, rfl⟩
      have := lift y (1 : T ⟶ A₀) ≫= hq.w
      simpa [comp_mul, ← Category.assoc] using this
  have hK := GlobalTheory.TranslQuotientPow.isMonHom_id_pow A₀ k
  have hqc : QuasiCompact q.left := inferInstance
  obtain ⟨⟨ψ', hψ', hψ'e⟩, hepi⟩ := GlobalTheory.exists_monHom_factor_of_flat_surjective Y A₀ B A₀ q ((𝟙 A₀) ^ k)
    hqm hK hqflat hqsurj hqc (fun T x hx => by
      obtain ⟨z, rfl⟩ := (hker T x).1 hx
      rw [GlobalTheory.TranslQuotientPow.comp_id_pow, ← comp_pow_hom, hk, comp_one])
  refine ⟨B, gB, hcB, q, ψ', hB, ⟨hqm, hψ', hψ'e, ?_⟩, hker⟩
  rw [← cancel_epi q, reassoc_of% hψ'e, GlobalTheory.TranslQuotientPow.comp_id_pow q k,
    GlobalTheory.TranslQuotientPow.pow_comp_hom q (𝟙 A₀) k, Category.id_comp]

theorem ker_iff_of_pullbacks {S Y T : Scheme.{0}} {g₀ : Y ⟶ S} {A : Over S} {A₀ : Over Y}
    {φ₀ : A₀.left ⟶ A.left} (h₀ : IsPullback φ₀ A₀.hom A.hom g₀)
    {H : Over Y} {i : H ⟶ A₀} {B : Over Y} [GrpObj B] {ψ : A₀ ⟶ B}
    (hker : ∀ (T' : Over Y) (x : T' ⟶ A₀), x ≫ ψ = 1 ↔ ∃ z : T' ⟶ H, z ≫ i = x)
    {y : T ⟶ Y} {A₁ : Over T} {θ : A₁.left ⟶ A₀.left} (hθ : θ ≫ A₀.hom = A₁.hom ≫ y)
    {B₁ : Over T} [GrpObj B₁] {θ' : B₁.left ⟶ B.left} (hθ' : IsGrpPullback B₁ B y θ') {ψ₁ : A₁ ⟶ B₁}
    (hc : θ ≫ ψ.left = ψ₁.left ≫ θ') (T' : Over T) (g : T' ⟶ A₁) :
    g ≫ ψ₁ = 1 ↔ ∃ h : T'.left ⟶ H.left, h ≫ H.hom = T'.hom ≫ y ∧ h ≫ i.left ≫ φ₀ = g.left ≫ θ ≫ φ₀ := by
  have hP : (g.left ≫ θ) ≫ A₀.hom = T'.hom ≫ y := by
    rw [Category.assoc, hθ, ← Category.assoc, Over.w g]
  let P : Over.mk (T'.hom ≫ y) ⟶ A₀ := Over.homMk (g.left ≫ θ) hP
  have e : P ≫ ψ = 1 ↔ (g.left ≫ θ) ≫ ψ.left = T'.hom ≫ y ≫ η[B].left := by
    rw [← Category.assoc T'.hom]
    constructor
    · intro h; exact congrArg Over.Hom.left h
    · intro h; exact Over.OverMorphism.ext h
  rw [eq_one_iff_of_isGrpPullback hθ', Over.comp_left, Category.assoc, ← hc, ← Category.assoc, ← e, hker]
  constructor
  · rintro ⟨z, hz⟩
    refine ⟨z.left, Over.w z, ?_⟩
    have := congrArg Over.Hom.left hz
    rw [Over.comp_left] at this
    rw [← Category.assoc, this]
    rfl
  · rintro ⟨h, hH, hφ⟩
    refine ⟨Over.homMk h hH, Over.OverMorphism.ext ?_⟩
    show h ≫ i.left = g.left ≫ θ
    apply h₀.hom_ext
    · rw [Category.assoc, hφ, Category.assoc]
    · rw [Category.assoc, Over.w i, hH, Category.assoc, hθ, ← Category.assoc, Over.w g]

theorem isogeny_rep : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (B : Over Y.left) (_ : GrpObj B) (_ : IsCommMonObj B) (ψ : A₀ ⟶ B) (ψ' : B ⟶ A₀), IsAbelianScheme B ∧ IsQuasiInv k ψ ψ' ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsQuasiInv k ψ₁ ψ₁' → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (θ : A₁.left ⟶ A₀.left) (θ' : B₁.left ⟶ B.left), θ ≫ φ₀ = φ₁ ∧ IsGrpPullback A₁ A₀ y θ ∧ IsGrpPullback B₁ B y θ' ∧ θ ≫ ψ.left = ψ₁.left ≫ θ' := by
  intro S _ A _ _ k hA hk0 hk
  obtain ⟨Y, hYf, hYe, hY⟩ := GlobalTheory.T.exists_finite_etale_trivializing_torsion_abelianScheme S A k hA hk0 hk
  refine ⟨Y, hYf, hYe, ?_⟩
  intro A₀ _ _ φ₀ h₀
  haveI : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  obtain ⟨H, _, i, hi, hm, hHf, hHe, hik, hH⟩ := hY A₀ φ₀ h₀
  have hA₀ : IsAbelianScheme A₀ := by
    exact { comm := inferInstance
            smooth := MorphismProperty.of_isPullback (P := @Smooth) h₀.1 hA.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) h₀.1 hA.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h₀.1 hA.geomConnected }
  obtain ⟨B, gB, cB, ψ, ψ', hB, hq, hker⟩ := exists_quot_quasiInv A₀ H i k hA₀ hi hm hHf hHe hik
  refine ⟨B, gB, cB, ψ, ψ', hB, hq, ?_⟩
  intro T x A₁ _ _ φ₁ B₁ _ _ ψ₁ ψ₁' h₁ hB₁ hq₁
  have hkT : IsUnit (k : Γ(T, ⊤)) := by
    have := hk.map x.appTop.hom
    rwa [map_natCast] at this
  obtain ⟨hψ₁m, hψ₁'m, e₁, e₂⟩ := hq₁
  have hkill : ∀ (T' : Over T) (g : T' ⟶ A₁), g ≫ ψ₁ = 1 → g ^ k = 1 := by
    intro T' g hg
    rw [← GlobalTheory.TranslQuotientPow.comp_id_pow, ← e₁, ← Category.assoc, hg, one_comp]
  have hA₁ : IsAbelianScheme A₁ := by
    exact { comm := inferInstance
            smooth := MorphismProperty.of_isPullback (P := @Smooth) h₁.1 hA.smooth
            proper := MorphismProperty.of_isPullback (P := @IsProper) h₁.1 hA.proper
            geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h₁.1 hA.geomConnected }
  obtain ⟨y, ⟨hyx, hyker⟩, hyu⟩ := hH T x A₁ φ₁ B₁ ψ₁ h₁ hB₁ hψ₁m hkill
  have w : φ₁ ≫ A.hom = (A₁.hom ≫ y) ≫ Y.hom := by rw [h₁.1.w, Category.assoc, hyx]
  let θ := h₀.1.lift φ₁ (A₁.hom ≫ y) w
  have hθφ : θ ≫ φ₀ = φ₁ := h₀.1.lift_fst _ _ _
  have hθs : θ ≫ A₀.hom = A₁.hom ≫ y := h₀.1.lift_snd _ _ _
  have hθ : IsGrpPullback A₁ A₀ y θ := IsGrpPullback.cancel h₀ (h₁.congr hyx.symm hθφ.symm) hθs
  obtain ⟨B₂, _, _, θ₂, ψ₂, ψ₂', hB₂, hθ₂, hq₂, hc₂, -⟩ :=
    GlobalTheory.UPel.HT.ES.pullQuasiInv T Y.left y A₀ B k ψ ψ' A₁ θ hB hq hθ
  obtain ⟨hψ₂f, hψ₂e, hψ₂s⟩ := GlobalTheory.UPel.HT.ES.isFinite_etale_surjective_of_isQuasiInv T A₁ B₂ k ψ₂ ψ₂' hA₁ hB₂ hkT hq₂
  haveI := hψ₂f
  haveI := hψ₂e
  have hk₂ := ker_iff_of_pullbacks h₀.1 hker hθs hθ₂ hc₂
  obtain ⟨β, hβi, hβm, hβ⟩ := GlobalTheory.SameKer.exists_iso_of_sameKer T A₁ B₂ B₁ ψ₂ ψ₁' ψ₁ k hB₁ hkT hq₂.1
    hψ₁'m hψ₁m inferInstance hψ₂s inferInstance e₂ (fun T' g => by rw [hyker, hk₂, hθφ])
  refine ⟨y, ⟨hyx, θ, β.left ≫ θ₂, hθφ, hθ, ?_, ?_⟩, ?_⟩
  · haveI := hβi
    haveI : IsMonHom (asIso β).hom := hβm
    exact ((isGrpPullback_of_iso (asIso β)).comp hθ₂).congr (Category.id_comp _) rfl
  · rw [hc₂, ← hβ, Over.comp_left, Category.assoc]
  · rintro y' ⟨hy'x, θ', θ'', hθ'φ, hθ', hθ'', hc'⟩
    apply hyu
    refine ⟨hy'x, fun T' g => ?_⟩
    rw [ker_iff_of_pullbacks h₀.1 hker hθ'.1.w hθ'' hc', hθ'φ]

end GlobalTheory.UPel.HT.ES.IsogRep
end

section -- merged from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsogenyRepresentableFiniteEtaleStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

theorem _root_.GlobalTheory.T.isogeny_representable_finite_etale : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] [IsCommMonObj A] (k : ℕ), IsAbelianScheme A → 0 < k → IsUnit (k : Γ(S, ⊤)) → ∃ (Y : Over S), IsFinite Y.hom ∧ Etale Y.hom ∧ ∀ (A₀ : Over Y.left) [GrpObj A₀] [IsCommMonObj A₀] (φ₀ : A₀.left ⟶ A.left), IsGrpPullback A₀ A Y.hom φ₀ → ∃ (B : Over Y.left) (_ : GrpObj B) (_ : IsCommMonObj B) (ψ : A₀ ⟶ B) (ψ' : B ⟶ A₀), IsAbelianScheme B ∧ IsQuasiInv k ψ ψ' ∧ ∀ (T : Scheme.{0}) (x : T ⟶ S) (A₁ : Over T) [GrpObj A₁] [IsCommMonObj A₁] (φ₁ : A₁.left ⟶ A.left) (B₁ : Over T) [GrpObj B₁] [IsCommMonObj B₁] (ψ₁ : A₁ ⟶ B₁) (ψ₁' : B₁ ⟶ A₁), IsGrpPullback A₁ A x φ₁ → IsAbelianScheme B₁ → IsQuasiInv k ψ₁ ψ₁' → ∃! y : T ⟶ Y.left, y ≫ Y.hom = x ∧ ∃ (θ : A₁.left ⟶ A₀.left) (θ' : B₁.left ⟶ B.left), θ ≫ φ₀ = φ₁ ∧ IsGrpPullback A₁ A₀ y θ ∧ IsGrpPullback B₁ B y θ' ∧ θ ≫ ψ.left = ψ₁.left ≫ θ' := by
  first | exact @GlobalTheory.UPel.HT.ES.IsogRep.isogeny_rep | exact GlobalTheory.UPel.HT.ES.IsogRep.isogeny_rep | exact @GlobalTheory.UPel.HT.ES.IsogRep.ker_iff_of_pullbacks | exact GlobalTheory.UPel.HT.ES.IsogRep.ker_iff_of_pullbacks | exact @GlobalTheory.UPel.HT.ES.IsogRep.exists_quot_quasiInv | exact GlobalTheory.UPel.HT.ES.IsogRep.exists_quot_quasiInv
end
end
