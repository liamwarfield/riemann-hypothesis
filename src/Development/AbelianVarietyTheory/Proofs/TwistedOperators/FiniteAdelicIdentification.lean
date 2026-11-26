module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIdempotentMulNatPowOfMul

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.OpFullImp
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinAdIdent

section Groups

variable {G G' : Type} [Group G] [Group G'] {H : Subgroup G} {H' : Subgroup G'}

def Corr (φ : H ≃* H') (A : Set G) (A' : Set G') : Prop :=
  (∀ g ∈ A, g ∈ H) ∧ (∀ g ∈ A', g ∈ H') ∧ ∀ g : H, (g : G) ∈ A ↔ (φ g : G') ∈ A'

theorem Corr.symm {φ : H ≃* H'} {A : Set G} {A' : Set G'} (h : Corr φ A A') : Corr φ.symm A' A := by
  refine ⟨h.2.1, h.1, fun g => ?_⟩
  rw [h.2.2 (φ.symm g), MulEquiv.apply_symm_apply]

theorem Corr.lift {φ : H ≃* H'} {A : Set G} {A' : Set G'} (h : Corr φ A A') {x : G'} (hx : x ∈ A') :
    ∃ g : H, (g : G) ∈ A ∧ (φ g : G') = x := by
  refine ⟨φ.symm ⟨x, h.2.1 x hx⟩, ?_, by simp⟩
  rw [h.2.2, MulEquiv.apply_symm_apply]
  exact hx

theorem Corr.cosets {φ : H ≃* H'} {K R : Set G} {K' R' : Set G'} (hK : Corr φ K K') (hR : Corr φ R R') (α : H)
    (h : (∀ γ ∈ R, γ ∈ H ∧ ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) ∧
      ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * α * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ K) :
    (∀ γ ∈ R', γ ∈ H' ∧ ∃ k₁ ∈ K', ∃ k₂ ∈ K', γ = k₁ * φ α * k₂) ∧
      ∀ x : G', (∃ k₁ ∈ K', ∃ k₂ ∈ K', x = k₁ * φ α * k₂) → ∃! γ, γ ∈ R' ∧ γ⁻¹ * x ∈ K' := by
  obtain ⟨h₁, h₂⟩ := h
  have memK : ∀ g : H, (g : G) ∈ K ↔ (φ g : G') ∈ K' := hK.2.2
  refine ⟨fun γ' hγ' => ?_, fun x' hx' => ?_⟩
  · obtain ⟨γ, hγR, rfl⟩ := hR.lift hγ'
    obtain ⟨-, k₁, hk₁, k₂, hk₂, heq⟩ := h₁ γ hγR
    have e : γ = ⟨k₁, hK.1 k₁ hk₁⟩ * α * ⟨k₂, hK.1 k₂ hk₂⟩ := Subtype.ext heq
    refine ⟨hR.2.1 _ hγ', _, (memK ⟨k₁, hK.1 k₁ hk₁⟩).mp hk₁, _, (memK ⟨k₂, hK.1 k₂ hk₂⟩).mp hk₂, ?_⟩
    rw [e, map_mul, map_mul]
    rfl
  · obtain ⟨k₁', hk₁', k₂', hk₂', rfl⟩ := hx'
    obtain ⟨k₁, hk₁, rfl⟩ := hK.lift hk₁'
    obtain ⟨k₂, hk₂, rfl⟩ := hK.lift hk₂'
    obtain ⟨γ, ⟨hγR, hγK⟩, huniq⟩ := h₂ ((k₁ * α * k₂ : H) : G) ⟨k₁, hk₁, k₂, hk₂, rfl⟩
    have key : ∀ c : H, (c : G)⁻¹ * ((k₁ * α * k₂ : H) : G) ∈ K ↔
        (φ c : G')⁻¹ * ((φ k₁ : G') * (φ α : G') * (φ k₂ : G')) ∈ K' := by
      intro c
      have := memK (c⁻¹ * (k₁ * α * k₂))
      simpa only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv] using this
    let g : H := ⟨γ, (h₁ γ hγR).1⟩
    refine ⟨φ g, ⟨(hR.2.2 g).mp hγR, (key g).mp hγK⟩, ?_⟩
    rintro y' ⟨hy'R, hy'K⟩
    obtain ⟨c, hcR, rfl⟩ := hR.lift hy'R
    have hc : c = g := Subtype.ext (huniq c ⟨hcR, (key c).mpr hy'K⟩)
    rw [hc]

end Groups

variable {D : D7}

structure Link (V V' : HSp D) (M : ℕ) (φ : GfC V ≃* GfC V')
    (J : Matrix (Fin V'.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))
    (J' : Matrix (Fin V.rank) (Fin V'.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Prop where
  rank : V.rank = V'.rank
  h1 : mmul J J' = 1
  h2 : mmul J' J = 1
  hc : ∀ g : GfC V, mmul (finMat D.sp.cm.sig V'.gram (φ g : GA D V')) J = mmul J (finMat D.sp.cm.sig V.gram (g : GA D V))
  lat : ∀ f, Good (D := D) M f → ∀ y, f • y ∈ Formalism.L2.NTheta.LamHat V ↔ f • J.mulVec y ∈ Formalism.L2.NTheta.LamHat V'
  loc : ∀ f, Good (D := D) M f → ∀ y ∈ Formalism.L2.NTheta.LamHat V, f • y ∈ Formalism.L2.NTheta.LamHat V
  loc' : ∀ f, Good (D := D) M f → ∀ y ∈ Formalism.L2.NTheta.LamHat V', f • y ∈ Formalism.L2.NTheta.LamHat V'

theorem suppF_iff (f : Formalism.L2.Theta.AE D) {V : HSp D} {α : GA D V} (hα : α ∈ GfC V) :
    SuppF V f α ↔ finPart D f • (finMat D.sp.cm.sig V.gram α - 1) = finMat D.sp.cm.sig V.gram α - 1 := by
  rw [GlobalTheory.HeckeTrans.finMat_eq, GlobalTheory.HeckeTrans.supp_map_iff]
  refine ⟨fun hs i j => by rw [hs i j], fun hs i j => ?_⟩
  refine GlobalTheory.FinIsoGrp.proj_inj D _ _ ?_ (congrArg (swapAE D) ?_)
  · show infPart D _ = infPart D _
    have hij := congrFun (congrFun (GlobalTheory.HeckeTrans.inf_eq hα) i) j
    rw [Matrix.map_apply] at hij
    have h0 : infPart D ((mt V α - 1) i j) = 0 := by
      rw [Matrix.sub_apply, map_sub, hij]
      by_cases hh : i = j <;> simp [Matrix.one_apply, hh]
    rw [map_mul, h0, mul_zero]
  · exact hs i j

namespace Link

variable {V V' : HSp D} {M : ℕ} {φ : GfC V ≃* GfC V'}
  {J : Matrix (Fin V'.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)}
  {J' : Matrix (Fin V.rank) (Fin V'.rank) (Af D.host.F ⊗[D.host.F] D.host.E)} (h : Link V V' M φ J J')
include h

theorem symm : Link V' V M φ.symm J' J := by
  refine ⟨h.rank.symm, h.h2, h.h1, ?_, ?_, h.loc', h.loc⟩
  · intro g
    have e := h.hc (φ.symm g)
    rw [MulEquiv.apply_symm_apply] at e
    have e' : finMat D.sp.cm.sig V'.gram (g : GA D V') * J = J * finMat D.sp.cm.sig V.gram (φ.symm g : GA D V) := e
    have h1' : J * J' = 1 := h.h1
    have h2' : J' * J = 1 := h.h2
    show finMat D.sp.cm.sig V.gram (φ.symm g : GA D V) * J' = J' * finMat D.sp.cm.sig V'.gram (g : GA D V')
    calc finMat D.sp.cm.sig V.gram (φ.symm g : GA D V) * J'
        = (J' * J) * finMat D.sp.cm.sig V.gram (φ.symm g : GA D V) * J' := by rw [h2', Matrix.one_mul]
      _ = J' * (J * finMat D.sp.cm.sig V.gram (φ.symm g : GA D V)) * J' := by simp only [Matrix.mul_assoc]
      _ = J' * (finMat D.sp.cm.sig V'.gram (g : GA D V') * J) * J' := by rw [← e']
      _ = J' * finMat D.sp.cm.sig V'.gram (g : GA D V') * (J * J') := by simp only [Matrix.mul_assoc]
      _ = J' * finMat D.sp.cm.sig V'.gram (g : GA D V') := by rw [h1', Matrix.mul_one]
  · intro f hf y
    have h1' : J * J' = 1 := h.h1
    rw [h.lat f hf (J'.mulVec y), Matrix.mulVec_mulVec, h1', Matrix.one_mulVec]

theorem supp (f : Formalism.L2.Theta.AE D) (g : GfC V) : SuppF V f (g : GA D V) ↔ SuppF V' f (φ g : GA D V') := by
  have h1' : J * J' = 1 := h.h1
  have h2' : J' * J = 1 := h.h2
  have hc : finMat D.sp.cm.sig V'.gram (φ g : GA D V') * J = J * finMat D.sp.cm.sig V.gram (g : GA D V) := h.hc g
  rw [suppF_iff f g.2, suppF_iff f (φ g).2]
  exact ⟨fun hs => GlobalTheory.HeckeTrans.supp_conj h1' hc hs,
    fun hs => GlobalTheory.HeckeTrans.supp_conj h2' (GlobalTheory.HeckeTrans.conj_inv h1' h2' hc) hs⟩

theorem det (g : GfC V) : (Formalism.L2.Theta.mt V' (φ g : GA D V')).det = (Formalism.L2.Theta.mt V (g : GA D V)).det := by
  have h1' : J * J' = 1 := h.h1
  have h2' : J' * J = 1 := h.h2
  have hc : finMat D.sp.cm.sig V'.gram (φ g : GA D V') * J = J * finMat D.sp.cm.sig V.gram (g : GA D V) := h.hc g
  refine GlobalTheory.FinIsoGrp.proj_inj D _ _ ?_ (congrArg (swapAE D) ?_)
  · show infPart D _ = infPart D _
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      GlobalTheory.HeckeTrans.inf_eq (φ g).2, GlobalTheory.HeckeTrans.inf_eq g.2, Matrix.det_one, Matrix.det_one]
  · show finPart D _ = finPart D _
    rw [RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply,
      ← GlobalTheory.HeckeTrans.finMat_eq, ← GlobalTheory.HeckeTrans.finMat_eq]
    exact GlobalTheory.HeckeTrans.det_conj h1' h2' hc

theorem stab {f : Af D.host.F ⊗[D.host.F] D.host.E} (hf : Good M f) (g : GfC V)
    (hs : f • (finMat D.sp.cm.sig V.gram (g : GA D V) - 1) = finMat D.sp.cm.sig V.gram (g : GA D V) - 1) :
    (∀ y, y ∈ Formalism.L2.NTheta.LamHat V ↔ (finMat D.sp.cm.sig V.gram (g : GA D V)).mulVec y ∈ Formalism.L2.NTheta.LamHat V) ↔
    ∀ y, y ∈ Formalism.L2.NTheta.LamHat V' ↔
      (finMat D.sp.cm.sig V'.gram (φ g : GA D V')).mulVec y ∈ Formalism.L2.NTheta.LamHat V' := by
  have h1' : J * J' = 1 := h.h1
  have hc : finMat D.sp.cm.sig V'.gram (φ g : GA D V') * J = J * finMat D.sp.cm.sig V.gram (g : GA D V) := h.hc g
  rw [stab_part (h.loc f hf) hs, stab_part (h.loc' f hf) (GlobalTheory.HeckeTrans.supp_conj h1' hc hs)]
  exact stab_pred (p := fun y => f • y ∈ Formalism.L2.NTheta.LamHat V) (p' := fun y => f • y ∈ Formalism.L2.NTheta.LamHat V')
    h1' hc (h.lat f hf)

theorem sph_imp (S : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (hS : ∀ v : HeightOneSpectrum (𝓞 D.host.F), (M : 𝓞 D.host.F) ∈ v.asIdeal → v ∈ S) (g : GfC V)
    (hg : (g : GA D V) ∈ KsphC V S) : (φ g : GA D V') ∈ KsphC V' S := by
  obtain ⟨f₀, hf₀, hev⟩ := good_away S M hS
  have hs := supp_away S hev (finMat D.sp.cm.sig V.gram (g : GA D V)) hg.2.2
  refine ⟨(φ g).2, (h.stab hf₀ g hs).mp hg.2.1, fun v hv => ?_⟩
  let ψ := (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom
  have e1 := GlobalTheory.HeckeTrans.map_conj ψ (h.hc g)
  have e2 : J.map ψ * J'.map ψ = 1 := GlobalTheory.HeckeTrans.map_mul_one ψ h.h1
  have e3 : (finMat D.sp.cm.sig V.gram (g : GA D V)).map ψ = 1 := hg.2.2 v hv
  rw [e3, Matrix.mul_one] at e1
  show (finMat D.sp.cm.sig V'.gram (φ g : GA D V')).map ψ = 1
  calc (finMat D.sp.cm.sig V'.gram (φ g : GA D V')).map ψ
      = (finMat D.sp.cm.sig V'.gram (φ g : GA D V')).map ψ * (J.map ψ * J'.map ψ) := by rw [e2, Matrix.mul_one]
    _ = J.map ψ * J'.map ψ := by rw [← Matrix.mul_assoc, e1]
    _ = 1 := e2

theorem sphLoc {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal)
    (g : GfC V) (hs : SuppF V f (g : GA D V)) : (g : GA D V) ∈ KsphC V ∅ ↔ (φ g : GA D V') ∈ KsphC V' ∅ := by
  obtain ⟨-, hfg, -⟩ := good_of_primeIdem hP hM
  have key := h.stab hfg g ((suppF_iff f g.2).mp hs)
  constructor
  · rintro ⟨-, hl, -⟩
    exact ⟨(φ g).2, key.mp hl, fun v hv => by simp at hv⟩
  · rintro ⟨-, hl, -⟩
    exact ⟨g.2, key.mpr hl, fun v hv => by simp at hv⟩

theorem hecke_imp {P : Pl D.host.E} {e : Formalism.L2.Theta.AE D} (he : Formalism.L2.NTheta.IsIdemAt e P)
    (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal) {ϖ : D.host.E} {k : ℕ} (g : GfC V)
    (hg : Formalism.L2.NTheta.IsHeckeElt V e ϖ k (g : GA D V)) : Formalism.L2.NTheta.IsHeckeElt V' e ϖ k (φ g : GA D V') := by
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨hge, -, -⟩ := good_of_primeIdem hP hM
  exact GlobalTheory.HeckeTrans.transfer he.1 J J' h.h1 h.h2 (φ g).2 (h.hc g) (h.lat _ hge) (h.loc _ hge) (h.loc' _ hge) hg

theorem div_imp {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal)
    {ϖ : D.host.E} {d : List ℤ} (g : GfC V) (hg : DivAt V e ϖ d (g : GA D V)) : DivAt V' e ϖ d (φ g : GA D V') := by
  obtain ⟨hge, -, -⟩ := good_of_primeIdem hP hM
  obtain ⟨hlen, hdiv⟩ := hg
  have H : HasDiv (finPart D e) (intAE D) (fun i => finPart D (incA D (ϖ ^ d.getD i 0))) (Formalism.L2.NTheta.LamHat V)
      (finMat D.sp.cm.sig V.gram (g : GA D V)) := hdiv
  obtain ⟨B, b1, b2, b3, b4⟩ := H.conj h.rank hge.1 h.h1 (h.hc g) (h.lat _ hge) (h.loc _ hge) (h.loc' _ hge)
  exact ⟨hlen.trans h.rank, B, b1, b2, b3, b4⟩

variable {K : Set (GA D V)} {K' : Set (GA D V')} {χ : GA D V → ℂ} {χ' : GA D V' → ℂ} (hK : Corr φ K K')
  (hχ : ∀ g : GfC V, (g : GA D V) ∈ K → χ' (φ g : GA D V') = χ g)
include hK hχ

theorem level_imp {P : Pl D.host.E} {e f : Formalism.L2.Theta.AE D} (hP : IsPrimeIdem P e f) (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal)
    (a : ∀ g, SuppF V f g → (g ∈ K ↔ g ∈ KsphC V ∅)) (b : ∀ g ∈ K, SuppF V f g → χ g = 1) :
    (∀ g, SuppF V' f g → (g ∈ K' ↔ g ∈ KsphC V' ∅)) ∧ (∀ g ∈ K', SuppF V' f g → χ' g = 1) ∧
      Corr φ {k | k ∈ K ∧ SuppF V f k} {k | k ∈ K' ∧ SuppF V' f k} := by
  refine ⟨fun g' hs' => ?_, fun g' hg' hs' => ?_,
    ⟨fun g hg => hK.1 g hg.1, fun g hg => hK.2.1 g hg.1, fun g => and_congr (hK.2.2 g) (h.supp f g)⟩⟩
  · by_cases hG : g' ∈ GfC V'
    · obtain ⟨g, rfl⟩ : ∃ g : GfC V, (φ g : GA D V') = g' := ⟨φ.symm ⟨g', hG⟩, by simp⟩
      have hs : SuppF V f (g : GA D V) := (h.supp f g).mpr hs'
      rw [← hK.2.2 g, a _ hs]
      exact h.sphLoc hP hM g hs
    · exact iff_of_false (fun h' => hG (hK.2.1 _ h')) (fun h' => hG h'.1)
  · obtain ⟨g, hgK, rfl⟩ := hK.lift hg'
    rw [hχ g hgK]
    exact b _ hgK ((h.supp f g).mpr hs')

variable {R : Finset (GA D V)} {R' : Finset (GA D V')} (hR : Corr φ (R : Set (GA D V)) (R' : Set (GA D V')))
include hR

theorem opAt_imp (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {P : Pl D.host.E} (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal) {k : ℕ}
    (H : IsHeckeOpAt V K χ S P k R) : IsHeckeOpAt V' K' χ' S P k R' := by
  obtain ⟨e, ϖ, α, hS, he, h1, h2, hk, hJ, hχ1, hα, hRs, hcos⟩ := H
  have hP : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  obtain ⟨l1, l2, l3⟩ := h.level_imp hK hχ hP hM hJ hχ1
  have hαG : α ∈ GfC V := hα.1
  have hc := Corr.cosets l3 hR (⟨α, hαG⟩⁻¹) hcos
  rw [map_inv] at hc
  refine ⟨e, ϖ, (φ ⟨α, hαG⟩ : GA D V'), hS, he, h1, h2, hk.trans_eq h.rank, l1, l2,
    h.hecke_imp he hM ⟨α, hαG⟩ hα, ?_, hc⟩
  intro γ hγ
  obtain ⟨g, hgR, rfl⟩ := hR.lift hγ
  exact (h.supp _ g).mp (hRs _ hgR)

theorem opFull_imp (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) {P : Pl D.host.E} (hM : (M : 𝓞 D.host.E) ∉ P.asIdeal)
    {d : List ℤ} (H : Hecke₂ V K χ S P d R) : Hecke₂ V' K' χ' S P d R' := by
  obtain ⟨e, f, ϖ, α, hS, hP, h1, h2, hd, hJ, hχ1, hαs, hdiv, hRs, hcos⟩ := H
  obtain ⟨l1, l2, l3⟩ := h.level_imp hK hχ hP hM hJ hχ1
  have hs1 : SuppF V f (1 : GA D V) := by
    intro i j
    simp [Formalism.L2.Theta.mt]
  have h1K : (1 : GA D V) ∈ K := by
    rw [hJ 1 hs1]
    refine ⟨one_mem _, fun y => ?_, fun v hv => by simp at hv⟩
    rw [GlobalTheory.HeckeTrans.finMat_eq]
    simp [Formalism.L2.Theta.mt]
  have hαG : α ∈ GfC V := by
    obtain ⟨γ, ⟨hγR, hγK⟩, -⟩ := hcos.2 α ⟨1, ⟨h1K, hs1⟩, 1, ⟨h1K, hs1⟩, by simp⟩
    have hm := mul_mem (hcos.1 γ hγR).1 (hK.1 _ hγK.1)
    rwa [mul_inv_cancel_left] at hm
  have hc := Corr.cosets l3 hR ⟨α, hαG⟩ hcos
  refine ⟨e, f, ϖ, (φ ⟨α, hαG⟩ : GA D V'), hS, hP, h1, h2, hd, l1, l2, (h.supp f ⟨α, hαG⟩).mp hαs,
    h.div_imp hP hM ⟨α, hαG⟩ hdiv, ?_, hc⟩
  intro γ hγ
  obtain ⟨g, hgR, rfl⟩ := hR.lift hγ
  exact (h.supp _ g).mp (hRs _ hgR)

end Link

end GlobalTheory.FinAdIdent

end
end

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR.Lev Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.DIV GlobalTheory.IndefiniteRowSideFullHecke.IsometryCarriesCharacter
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinAdIdent

variable {D : D7}

theorem mem_iff_of_image {A : Type} [CommRing A] {m n : ℕ} {j : Matrix (Fin m) (Fin n) A} (hj : Function.Injective j.mulVec)
    {H : Set (Fin n → A)} {H' : Set (Fin m → A)} (h : j.mulVec '' H = H') (y : Fin n → A) : y ∈ H ↔ j.mulVec y ∈ H' := by
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    rwa [← hj hzy]

theorem level_conj {A B : Type} [CommRing A] [CommRing B] {m n : ℕ} (ψ : A →+* B) (σ : A →+* A) (τ : B →+* B)
    (h : ψ.comp σ = τ.comp ψ) {S : Subring B} (H : Submodule S (Fin n → B)) (H' : Submodule S (Fin m → B))
    {j : Matrix (Fin m) (Fin n) A} (hb : Function.Bijective (j.map ψ).mulVec)
    (hl : (j.map ψ).mulVec '' (H : Set _) = (H' : Set _)) {J : Matrix (Fin n) (Fin n) A} {J' : Matrix (Fin m) (Fin m) A}
    {x : GL (Fin n) A} {x' : GL (Fin m) A} (hx : x ∈ Formalism.UG.UJ σ J) (hx' : x' ∈ Formalism.UG.UJ σ J') (hc : x'.val * j = j * x.val) :
    Formalism.UG.bc ψ x ∈ Formalism.UG.level τ (J.map ψ) H ↔ Formalism.UG.bc ψ x' ∈ Formalism.UG.level τ (J'.map ψ) H' := by
  have hu : ∀ {k : ℕ} {K : Matrix (Fin k) (Fin k) A} {z : GL (Fin k) A}, z ∈ Formalism.UG.UJ σ K →
      Formalism.UG.bc ψ z ∈ Formalism.UG.UJ τ (K.map ψ) := by
    intro k K z hz
    have hz' : Formalism.UG.cT σ (z : Matrix (Fin k) (Fin k) A) * K * z = K := hz
    show Formalism.UG.cT τ ((z : Matrix (Fin k) (Fin k) A).map ψ) * K.map ψ * (z : Matrix (Fin k) (Fin k) A).map ψ = K.map ψ
    conv_rhs => rw [← hz']
    simp only [Matrix.map_mul]
    congr 2
    ext a b
    simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply]
    exact (RingHom.congr_fun h _).symm
  obtain ⟨j', hj1, -⟩ := exists_inv hb
  have hcψ : x'.val.map ψ * j.map ψ = j.map ψ * x.val.map ψ := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, hc]
  have key := stab_pred (p := fun y => y ∈ H) (p' := fun y => y ∈ H') hj1 hcψ (mem_iff_of_image hb.1 hl)
  have e1 : Formalism.UG.bc ψ x ∈ Formalism.UG.level τ (J.map ψ) H ↔ Formalism.UG.bc ψ x ∈ Formalism.UG.UJ τ (J.map ψ) ∧
      ∀ y, y ∈ H ↔ (x.val.map ψ).mulVec y ∈ H := Iff.rfl
  have e2 : Formalism.UG.bc ψ x' ∈ Formalism.UG.level τ (J'.map ψ) H' ↔ Formalism.UG.bc ψ x' ∈ Formalism.UG.UJ τ (J'.map ψ) ∧
      ∀ y, y ∈ H' ↔ (x'.val.map ψ).mulVec y ∈ H' := Iff.rfl
  rw [e1, e2]
  exact ⟨fun a => ⟨hu hx', key.1 a.2⟩, fun a => ⟨hu hx, key.2 a.2⟩⟩

theorem levelVL_conj {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {m n : ℕ} (σ : E →ₐ[F] E)
    (v : HeightOneSpectrum (𝓞 F)) (Λ : Submodule (𝓞 E) (Fin n → E)) (Λ' : Submodule (𝓞 E) (Fin m → E))
    (G : Matrix (Fin n) (Fin n) E) (G' : Matrix (Fin m) (Fin m) E) (j : Matrix (Fin m) (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hb : Function.Bijective (j.map (Formalism.UG.prV (E := E) v)).mulVec)
    (hl : (j.map (Formalism.UG.prV (E := E) v)).mulVec '' (Formalism.L2.Herm.locL v Λ : Set _) = (Formalism.L2.Herm.locL v Λ' : Set _))
    {x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)} {x' : GL (Fin m) (E ⊗[F] Formalism.L2.Herm.Af F)}
    (hx : x ∈ Formalism.UG.UPts σ G (Formalism.L2.Herm.Af F)) (hx' : x' ∈ Formalism.UG.UPts σ G' (Formalism.L2.Herm.Af F))
    (hc : x'.val * j = j * x.val) :
    Formalism.UG.bc (Formalism.UG.prV v) x ∈ Formalism.UG.levelVL σ G v Λ ↔ Formalism.UG.bc (Formalism.UG.prV v) x' ∈ Formalism.UG.levelVL σ G' v Λ' := by
  have h1 := level_conj (Formalism.UG.prV (E := E) v) (Formalism.UG.sigR σ (Formalism.L2.Herm.Af F)) (Formalism.UG.sigR σ (v.adicCompletion F))
    (Formalism.UG.P.afsplit_prV_comp_sigR σ v) (Formalism.L2.Herm.locL v Λ) (Formalism.L2.Herm.locL v Λ') hb hl hx hx' hc
  have hG : ∀ {k : ℕ} (K : Matrix (Fin k) (Fin k) E),
      (K.map (Formalism.UG.inclE (F := F) (Formalism.L2.Herm.Af F))).map (Formalism.UG.prV (E := E) v) =
        K.map (Formalism.UG.inclE (F := F) (v.adicCompletion F)) := by
    intro k K
    ext a b
    simp only [Matrix.map_apply]
    exact Formalism.UG.P.afsplit_prV_inclE v (K a b)
  rw [hG, hG] at h1
  exact h1

open GlobalTheory.HeckeTrans in
set_option maxHeartbeats 800000 in
theorem link_of_isLatIsom {V V' : HSp D} (h : V.rank = V'.rank)
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin V'.rank → D.host.E)}
    {β : GL (Fin V.rank) (EAf D)} {β' : GL (Fin V'.rank) (EAf D)} {N N' : ℕ}
    (hβ : IsSDFrame V β Λ N) (hβ' : IsSDFrame V' β' Λ' N') {j : Matrix (Fin V'.rank) (Fin V.rank) (EAf D)}
    {j' : Matrix (Fin V.rank) (Fin V'.rank) (EAf D)} (hj : IsLatIsom V V' Λ Λ' j) (h1 : mmul j j' = 1) (h2 : mmul j' j = 1)
    {φ : GfC V ≃ₜ* GfC V'} (hφ : IsConjBy V V' j φ) :
    Link V V' (N * N') φ.toMulEquiv (j.map (unswap D)) (j'.map (unswap D)) := by
  obtain ⟨c, hB⟩ := hβ
  obtain ⟨c', hB'⟩ := hβ'
  have himg : ∀ x, x ∈ (Formalism.L2.Herm.hatL (F := D.host.F) Λ : Set _) ↔
      j.mulVec x ∈ (Formalism.L2.Herm.hatL (F := D.host.F) Λ' : Set _) :=
    mem_iff_of_image hj.1.1.1 hj.2
  have hvec : ∀ (f : Af D.host.F ⊗[D.host.F] D.host.E) (y : Fin V.rank → Af D.host.F ⊗[D.host.F] D.host.E),
      (fun a => swapAE D (f * ((j.map (unswap D)).mulVec y) a)) = j.mulVec (fun b => swapAE D (f * y b)) := by
    intro f y
    funext a
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.mul_sum, map_sum, map_mul, swap_unswap]
    exact Finset.sum_congr rfl fun b _ => by ring
  have gN : ∀ f, Good (D := D) (N * N') f → Good (N ^ c) f := fun f hf => hf.pow c
  have gN' : ∀ f, Good (D := D) (N * N') f → Good (N' ^ c') f := by
    intro f hf
    rw [mul_comm] at hf
    exact hf.pow c'
  refine ⟨h, GlobalTheory.HeckeTrans.map_mul_one _ h1, GlobalTheory.HeckeTrans.map_mul_one _ h2, ?_, ?_, ?_, ?_⟩
  · intro g
    have := congrArg (fun X => X.map (unswap D)) (hφ g)
    simp only [mmul, Matrix.map_mul, finE_unswap] at this
    exact this
  · intro f hf y
    rw [(lamHat_good hB (gN f hf)).2, (lamHat_good hB' (gN' f hf)).2, hvec]
    exact himg _
  · intro f hf y hy
    exact (lamHat_good hB (gN f hf)).1 y hy
  · intro f hf y hy
    exact (lamHat_good hB' (gN' f hf)).1 y hy

theorem corr_inA {V V' : HSp D} (φ : GfC V ≃ₜ* GfC V') (R : Finset (GfC V)) :
    Corr φ.toMulEquiv (inA V R : Set (GA D V)) (imA φ R : Set (GA D V')) := by
  refine ⟨?_, ?_, fun g => ?_⟩
  · intro g hg
    simp only [inA, Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe] at hg
    obtain ⟨a, -, rfl⟩ := hg
    exact a.2
  · intro g hg
    simp only [imA, inA, Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image, Finset.mem_coe] at hg
    obtain ⟨a, -, rfl⟩ := hg
    exact a.2
  · simp [inA, imA]
    exact ⟨fun hg => ⟨g.1, g.2, hg, rfl⟩, fun ⟨a, ha, hR, hag⟩ => hag ▸ hR⟩

theorem chi_symm {G G' : Type} [Group G] [Group G'] {H : Subgroup G} {H' : Subgroup G'} {φ : H ≃* H'} {K : Set G} {K' : Set G'}
    (hK : Corr φ K K') {χ : G → ℂ} {χ' : G' → ℂ} (hχ : ∀ g : H, (g : G) ∈ K → χ' (φ g : G') = χ g) (g : H')
    (hg : (g : G') ∈ K') : χ (φ.symm g : G) = χ' g := by
  have h1 : ((φ.symm g : H) : G) ∈ K := (hK.2.2 (φ.symm g)).2 (by simpa using hg)
  have h2 := hχ (φ.symm g) h1
  simpa using h2.symm

private theorem finE_mem_UPts (V : HSp D) (g : GA D V) :
    finE V g ∈ Formalism.UG.UPts D.sp.cm.sig V.gram (Formalism.L2.Herm.Af D.host.F) := by
  have hg : Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF D.host.F) D.sp.cm.sig) ((matHom V g : GL _ _) : Matrix _ _ _) *
      JR (AF D.host.F) V.gram * ((matHom V g : GL _ _) : Matrix _ _ _) = JR (AF D.host.F) V.gram := g.2
  show Formalism.UG.cT (Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F)) ((finE V g : GL _ _) : Matrix _ _ _) *
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F)) * ((finE V g : GL _ _) : Matrix _ _ _) =
      V.gram.map (Formalism.UG.inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))
  have := congrArg (fun X => X.map (GlobalTheory.FinIsoGrp.qFin D)) hg
  simp only [Matrix.map_mul] at this
  rw [GlobalTheory.FinIsoGrp.finE_val, ← GlobalTheory.FinIsoGrp.gram_map, ← this]
  congr 2
  ext a b
  simp only [Formalism.UG.cT, Matrix.transpose_apply, Matrix.map_apply, GlobalTheory.FinIsoGrp.qFin_sig]

set_option maxHeartbeats 1600000 in
theorem inducedIso (D : D7) : InducedIso D := by
  intro V V' h Λ Λ' β β' N N' hβ hβ' T j hj hm
  obtain ⟨j', h1, h2⟩ := exists_inv hj.1.1
  obtain ⟨φ, hφ⟩ := GlobalTheory.FinIsoGrp.exists_finIso V V' j j' h1 h2 hj.1.2
  have hφ' : IsConjBy V V' j φ := hφ
  have L := link_of_isLatIsom h hβ hβ' hj h1 h2 hφ'
  have Lsymm : Link V' V (N * N') φ.toMulEquiv.symm (j'.map (GlobalTheory.HeckeTrans.unswap D)) (j.map (GlobalTheory.HeckeTrans.unswap D)) := by
    refine ⟨L.rank.symm, L.h2, L.h1, ?_, ?_, L.loc', L.loc⟩
    · intro g
      have e := L.hc (φ.toMulEquiv.symm g)
      rw [MulEquiv.apply_symm_apply] at e
      have h1' := L.h1
      have h2' := L.h2
      dsimp [mmul] at e h1' h2' ⊢
      change finMat D.sp.cm.sig V'.gram (g : GA D V') * j.map (GlobalTheory.HeckeTrans.unswap D) = j.map (GlobalTheory.HeckeTrans.unswap D) * finMat D.sp.cm.sig V.gram (φ.toMulEquiv.symm g : GA D V) at e
      calc finMat D.sp.cm.sig V.gram (φ.toMulEquiv.symm g : GA D V) * j'.map (GlobalTheory.HeckeTrans.unswap D)
          = (j'.map (GlobalTheory.HeckeTrans.unswap D) * j.map (GlobalTheory.HeckeTrans.unswap D)) * finMat D.sp.cm.sig V.gram (φ.toMulEquiv.symm g : GA D V) * j'.map (GlobalTheory.HeckeTrans.unswap D) := by rw [h2', Matrix.one_mul]
        _ = j'.map (GlobalTheory.HeckeTrans.unswap D) * (j.map (GlobalTheory.HeckeTrans.unswap D) * finMat D.sp.cm.sig V.gram (φ.toMulEquiv.symm g : GA D V)) * j'.map (GlobalTheory.HeckeTrans.unswap D) := by simp only [Matrix.mul_assoc]
        _ = j'.map (GlobalTheory.HeckeTrans.unswap D) * (finMat D.sp.cm.sig V'.gram (g : GA D V') * j.map (GlobalTheory.HeckeTrans.unswap D)) * j'.map (GlobalTheory.HeckeTrans.unswap D) := by rw [← e]
        _ = j'.map (GlobalTheory.HeckeTrans.unswap D) * finMat D.sp.cm.sig V'.gram (g : GA D V') * (j.map (GlobalTheory.HeckeTrans.unswap D) * j'.map (GlobalTheory.HeckeTrans.unswap D)) := by simp only [Matrix.mul_assoc]
        _ = j'.map (GlobalTheory.HeckeTrans.unswap D) * finMat D.sp.cm.sig V'.gram (g : GA D V') := by rw [h1', Matrix.mul_one]
    · intro f hf y
      have h1' := L.h1
      dsimp [mmul] at h1'
      rw [L.lat f hf ((j'.map (GlobalTheory.HeckeTrans.unswap D)).mulVec y), Matrix.mulVec_mulVec, h1', Matrix.one_mulVec]
  obtain ⟨c, hB⟩ := id hβ
  obtain ⟨c', hB'⟩ := id hβ'
  obtain ⟨u, hu, hT⟩ := hm
  have hl : ∀ y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ', j'.mulVec y ∈ Formalism.L2.Herm.hatL (F := D.host.F) Λ :=
    ((image_iff h1 h2 _ _).1 hj.2).2
  have e : ∀ {W : HSp D} (γ : GL (Fin W.rank) (EAf D)) (L1 : Formalism.L2.DIV.LevDat D.host.E ℂ W.rank) (κ : GA D W),
      κ ∈ levG W γ L1 ↔ κ ∈ GfC W ∧ finE W κ ∈ Formalism.L2.DIV.parLev D.sp.cm W.gram γ L1 ∧
        Formalism.L2.DIV.rTup γ L1 (finE W κ) ∈ L1.P.H := fun _ _ _ => Iff.rfl
  have hle := fun (L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank) (hL0 : ReadIn L0 T) (g : GfC V) =>
    lev_eq h V.gram V'.gram Λ Λ' β (finE V g) β' (finE V' (φ g)) hB.1 hB'.1 j j' h1 h2 hl u hu T hT (hφ g)
      (finE_mem_UPts V g) (finE_mem_UPts V' (φ g)) L0 hL0
  have hlev : ∀ L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L0 T → ∀ g : GfC V,
      (g : GA D V) ∈ levG V β L0 ↔ (φ g : GA D V') ∈ levG V' β' (castDat h L0) := by
    intro L0 hL0 g
    have H := hle L0 hL0 g
    rw [e, e]
    constructor
    · rintro ⟨-, hp, hr⟩
      exact ⟨(φ g).2, H.1.1 hp, (H.2 hp).1 ▸ hr⟩
    · rintro ⟨-, hp', hr'⟩
      have hp := H.1.2 hp'
      exact ⟨g.2, hp, (H.2 hp).1 ▸ hr'⟩
  have hchi : ∀ L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L0 T → ∀ g : GfC V, (g : GA D V) ∈ levS V β L0 →
      levChi V' β' (castDat h L0) (φ g : GA D V') = levChi V β L0 (g : GA D V) := by
    intro L0 hL0 g hg
    have hp := ((e β L0 g).1 hg).2.1
    have H := (hle L0 hL0 g).2 hp
    unfold levChi
    rw [H.2]
  have hK : ∀ L0 : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank, ReadIn L0 T →
      Corr φ.toMulEquiv (levS V β L0) (levS V' β' (castDat h L0)) := fun L0 hL0 =>
    ⟨fun g hg => ((e β L0 g).1 hg).1, fun g hg => ((e β' (castDat h L0) g).1 hg).1, fun g => hlev L0 hL0 g⟩
  refine ⟨φ, hφ', ?_⟩
  exact {
    stabLoc := fun v g => by
      obtain ⟨hb, hl'⟩ := loc_gen D.sp.cm.sig v Λ Λ' V.gram V'.gram j hj.1.1 hj.1.2 hj.2
      exact levelVL_conj D.sp.cm.sig v Λ Λ' V.gram V'.gram j hb.1 hl' (finE_mem_UPts V g) (finE_mem_UPts V' (φ g)) (hφ g)
    supp := fun f g => L.supp f g
    det := fun g => L.det g
    lev := hlev
    chi := hchi
    lift := fun L0 hL0 g0 g => by
      have H := hle L0 hL0 g
      unfold IsLevelLift
      constructor
      · rintro ⟨-, hp, hr⟩
        exact ⟨(φ g).2, H.1.1 hp, (H.2 hp).1.trans hr⟩
      · rintro ⟨-, hp', hr'⟩
        have hp := H.1.2 hp'
        exact ⟨g.2, hp, (H.2 hp).1.symm.trans hr'⟩
    sph := fun S hS g => ⟨L.sph_imp S hS g, fun hg => by simpa using Lsymm.sph_imp S hS (φ g) hg⟩
    heckeElt := fun P e ϖ k hM he g =>
      ⟨L.hecke_imp he hM g, fun hg => by simpa using Lsymm.hecke_imp he hM (φ g) hg⟩
    heckeAt := fun P k hM g => by
      unfold IsHeckeAt
      constructor
      · rintro ⟨e, ϖ, he, h1', h2', h3⟩
        exact ⟨e, ϖ, he, h1', h2', L.hecke_imp he hM g h3⟩
      · rintro ⟨e, ϖ, he, h1', h2', h3⟩
        exact ⟨e, ϖ, he, h1', h2', by simpa using Lsymm.hecke_imp he hM (φ g) h3⟩
    divAt := fun P e f ϖ d hM hP g =>
      ⟨L.div_imp hP hM g, fun hg => by simpa using Lsymm.div_imp hP hM (φ g) hg⟩
    opAt := fun L0 hL0 S P k hM R =>
      ⟨fun H => L.opAt_imp (hK L0 hL0) (hchi L0 hL0) (corr_inA φ R) S hM H,
        fun H => Lsymm.opAt_imp (hK L0 hL0).symm (chi_symm (hK L0 hL0) (hchi L0 hL0)) (corr_inA φ R).symm S hM H⟩
    opFull := fun L0 hL0 S P d hM R =>
      ⟨fun H => L.opFull_imp (hK L0 hL0) (hchi L0 hL0) (corr_inA φ R) S hM H,
        fun H => Lsymm.opFull_imp (hK L0 hL0).symm (chi_symm (hK L0 hL0) (hchi L0 hL0)) (corr_inA φ R).symm S hM H⟩ }

end GlobalTheory.FinAdIdent

end
