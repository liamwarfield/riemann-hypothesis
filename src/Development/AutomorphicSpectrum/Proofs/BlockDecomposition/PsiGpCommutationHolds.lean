module

public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishing
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConstantTermAutomorphicCriterion
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CompactInductionTwistedKernel

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HGPClosed
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HGPClosed
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

namespace GlobalTheory.CompanionTheory.MirGP

theorem isClosed_HGP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), IsClosed (MirabolicParabolic k m j : Set (Mir k (m + j))) := by
  intro k _ _ _ _ m j
  have h := GlobalTheory.SmGL.LeviInt.levi_integral_facts k Bool (Fin (m + j + 1))
    (GlobalTheory.SmGL.Two (Fin m) (Fin (j + 1))) (GlobalTheory.BZMir.Leib.eGP m j)
  exact h.2.2.2.2.2.2.1.preimage continuous_subtype_val

end GlobalTheory.CompanionTheory.MirGP
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HGPClosedStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_mirabolicParabolic : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ), IsClosed (MirabolicParabolic k m j : Set (Mir k (m + j))) := by
  first | exact @GlobalTheory.CompanionTheory.MirGP.isClosed_HGP | exact GlobalTheory.CompanionTheory.MirGP.isClosed_HGP | (intros; apply GlobalTheory.CompanionTheory.MirGP.isClosed_HGP <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjLeviFormula
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjLeviFormula
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib

noncomputable section

namespace GlobalTheory.CompanionTheory.LeibGP

section SlopeTestRemainingChoices

variable (k : Type) [Field k]

theorem blockIndex_false (m j : ℕ) (a : Fin m) :
    eGP m j ⟨false, a⟩ = Fin.castSucc (two (stdSum (rfl : m + j = m + j)) ⟨false, a⟩) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (apply Fin.ext
       simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum])

theorem blockIndex_true_castSucc (m j : ℕ) (b : Fin j) :
    eGP m j ⟨true, Fin.castSucc b⟩ = Fin.castSucc (two (stdSum (rfl : m + j = m + j)) ⟨true, b⟩) := by
  first
    | rfl
    | exact Fin.ext rfl
    | (apply Fin.ext
       simp [GlobalTheory.BZMir.Leib.eGP, GlobalTheory.SmGL.two, GlobalTheory.SmGL.stdSum])

theorem glEmbMat_castSucc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a b : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.castSucc b) = A a b := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_castSucc (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (b : Fin n) :
    glEmbMat k n A (Fin.last n) (Fin.castSucc b) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_castSucc_last (n : ℕ) (A : Matrix (Fin n) (Fin n) k) (a : Fin n) :
    glEmbMat k n A (Fin.castSucc a) (Fin.last n) = 0 := by
  simp [GlobalTheory.BZMir.glEmbMat]

theorem glEmbMat_last_last (n : ℕ) (A : Matrix (Fin n) (Fin n) k) :
    glEmbMat k n A (Fin.last n) (Fin.last n) = 1 := by
  simp [GlobalTheory.BZMir.glEmbMat]

end SlopeTestRemainingChoices

theorem gpProj_levi : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (p : GL (Fin (m + j)) k) (hp : p ∈ parab k (two (stdSum (rfl : m + j = m + j)))) (hp' : levi k (m + j) p ∈ MirabolicParabolic k m j), gpProj k m j ⟨levi k (m + j) p, hp'⟩ = (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ false, levi k j (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ true)) := by
  intro k _ _ _ _ m j p hp hp'
  refine Prod.ext ?_ ?_
  · apply Units.ext
    ext a b
    simp only [GlobalTheory.BZMir.Leib.gpProj, GlobalTheory.BZMir.Leib.hgpIncl, MonoidHom.prod_apply,
      MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    simp [GlobalTheory.SmGL.leviProj_apply, GlobalTheory.BZMir.levi, GlobalTheory.BZMir.glEmb, GlobalTheory.BZMir.glEmbHom,
        GlobalTheory.CompanionTheory.LeibGP.blockIndex_false, GlobalTheory.CompanionTheory.LeibGP.blockIndex_true_castSucc, GlobalTheory.BZMir.Leib.blockIndex_true_last,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_castSucc,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc_last, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_last,
        MonoidHom.codRestrict_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]
  · apply Subtype.ext
    apply Units.ext
    ext a b
    simp only [GlobalTheory.BZMir.Leib.gpProj, GlobalTheory.BZMir.Leib.hgpIncl, MonoidHom.prod_apply,
      MonoidHom.comp_apply, MonoidHom.codRestrict_apply, Pi.evalMonoidHom_apply, MonoidHom.coe_mk, OneHom.coe_mk]
    (try erw [GlobalTheory.SmGL.leviProj_apply])
    induction a using Fin.lastCases <;> induction b using Fin.lastCases <;>
      simp [GlobalTheory.SmGL.leviProj_apply, GlobalTheory.BZMir.levi, GlobalTheory.BZMir.glEmb, GlobalTheory.BZMir.glEmbHom,
        GlobalTheory.CompanionTheory.LeibGP.blockIndex_false, GlobalTheory.CompanionTheory.LeibGP.blockIndex_true_castSucc, GlobalTheory.BZMir.Leib.blockIndex_true_last,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_castSucc,
        GlobalTheory.CompanionTheory.LeibGP.glEmbMat_castSucc_last, GlobalTheory.CompanionTheory.LeibGP.glEmbMat_last_last,
        MonoidHom.codRestrict_apply, Units.coe_map, MonoidHom.coe_mk, OneHom.coe_mk]

end GlobalTheory.CompanionTheory.LeibGP

end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GpProjLeviFormulaStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gpProj_levi_formula : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (m j : ℕ) (p : GL (Fin (m + j)) k) (hp : p ∈ parab k (two (stdSum (rfl : m + j = m + j)))) (hp' : levi k (m + j) p ∈ MirabolicParabolic k m j), gpProj k m j ⟨levi k (m + j) p, hp'⟩ = (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ false, levi k j (leviProj k (two (stdSum (rfl : m + j = m + j))) ⟨p, hp⟩ true)) := by
  first | exact @GlobalTheory.CompanionTheory.LeibGP.gpProj_levi | exact GlobalTheory.CompanionTheory.LeibGP.gpProj_levi | (intros; apply GlobalTheory.CompanionTheory.LeibGP.gpProj_levi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoFunSmooth
open GlobalTheory.PRep GlobalTheory.SmGL

noncomputable section

namespace GlobalTheory.CompanionTheory.CIndCoinv

section Abstract

variable {G M W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
  [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def coFun (s : M →* G) (χ : M →* ℂˣ) (c : W →ₗ[ℂ] W') (f : G → W) (x : M) : W' :=
  (χ x : ℂ) • c (f (s x))

theorem coFun_mem {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hQH : ∀ p ∈ Q, s p ∈ H) (χ : M →* ℂˣ)
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) (f : indSpace H σ) :
    coFun s χ c f.1 ∈ indSpace Q σ' := by
  intro p x
  have h1 : f.1 (s p * s x) = σ ⟨s p, hQH p p.2⟩ (f.1 (s x)) := f.2 ⟨s p, hQH p p.2⟩ (s x)
  show ((χ ((p : M) * x) : ℂˣ) : ℂ) • c (f.1 (s ((p : M) * x))) = σ' p (((χ x : ℂˣ) : ℂ) • c (f.1 (s x)))
  rw [map_mul, map_mul, h1, map_smul, ← hcomp, Units.val_mul, mul_comm, mul_smul]

theorem coFun_smooth {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hs : Continuous s) (hQH : ∀ p ∈ Q, s p ∈ H)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) (f : smoothPart (ind H σ)) :
    (⟨coFun s χ c f.1.1, coFun_mem s hQH χ σ σ' c hcomp f.1⟩ : indSpace Q σ') ∈ smoothPart (ind Q σ') := by
  refine mem_smoothPart_of_nhds (Filter.mem_of_superset
    (((IsOpen.preimage hs f.2).inter hχ).mem_nhds ?_) ?_)
  · refine ⟨?_, one_mem _⟩
    simp
  · rintro x ⟨h1, h2⟩
    have h1' : ind H σ (s x) f.1 = f.1 := h1
    have h2' : χ x = 1 := h2
    apply Subtype.ext
    funext y
    show ((χ (y * x) : ℂˣ) : ℂ) • c (f.1.1 (s (y * x))) = ((χ y : ℂˣ) : ℂ) • c (f.1.1 (s y))
    have h3 : f.1.1 (s y * s x) = f.1.1 (s y) := congrFun (congrArg Subtype.val h1') (s y)
    rw [map_mul, map_mul, h2', mul_one, h3]

end Abstract

section Abstract2

variable {G M W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
  [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

def coMap {H : Subgroup G} {Q : Subgroup M} (s : M →* G) (hs : Continuous s) (hQH : ∀ p ∈ Q, s p ∈ H)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w)) :
    cIndSpace H σ →ₗ[ℂ] smoothPart (ind Q σ') where
  toFun f := ⟨⟨coFun s χ c f.1.1.1, coFun_mem s hQH χ σ σ' c hcomp f.1.1⟩, coFun_smooth s hs hQH χ hχ σ σ' c hcomp f.1⟩
  map_add' a b := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show ((χ x : ℂˣ) : ℂ) • c (a.1.1.1 (s x) + b.1.1.1 (s x)) = _
    rw [map_add (f := _), smul_add]
    rfl
  map_smul' r a := by
    apply Subtype.ext
    apply Subtype.ext
    funext x
    show ((χ x : ℂˣ) : ℂ) • c (r • a.1.1.1 (s x)) = r • (((χ x : ℂˣ) : ℂ) • c (a.1.1.1 (s x)))
    rw [map_smul, smul_comm]

theorem coinv_equiv (H U : Subgroup G) (Q : Subgroup M) (s : M →* G) (q : G →* M)
    (hH : IsClosed (H : Set G))
    (hbasis : ∀ O : Set G, O ∈ nhds (1 : G) → ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O)
    (hs : Continuous s) (hq : Continuous q) (hqs : ∀ x, q (s x) = x) (hker : ∀ g, q g = 1 ↔ g ∈ U)
    (hUH : U ≤ H) (hHQ : ∀ g ∈ H, q g ∈ Q) (hQH : ∀ p ∈ Q, s p ∈ H)
    (C : Set M) (hC : IsCompact C) (hMC : ∀ x : M, ∃ p ∈ Q, ∃ y ∈ C, x = p * y)
    (χ : M →* ℂˣ) (hχ : IsOpen (χ.ker : Set M))
    (σ : Representation ℂ H W) (hσ : IsSmooth σ) (σ' : Representation ℂ Q W')
    (c : W →ₗ[ℂ] W') (hc : Function.Surjective c) (hck : ∀ w, c w = 0 ↔ w ∈ twKer σ (U.subgroupOf H) 1)
    (hcomp : ∀ (p : Q) (w : W), (χ p : ℂ) • c (σ ⟨s p, hQH p p.2⟩ w) = σ' p (c w))
    (hK : ∀ f : cIndSpace H σ, (∀ g, f.1.1.1 g ∈ twKer σ (U.subgroupOf H) 1) → f ∈ twKer (cInd H σ) U 1) :
    ∃ E : (cIndSpace H σ ⧸ twKer (cInd H σ) U 1) ≃ₗ[ℂ] smoothPart (ind Q σ'),
      ∀ (f : cIndSpace H σ) (x : M), (E (Submodule.Quotient.mk f)).1.1 x = (χ x : ℂ) • c (f.1.1.1 (s x)) := by
  classical
  haveI hUn : U.Normal := by
    have : U = q.ker := by
      ext g
      rw [MonoidHom.mem_ker, hker]
    rw [this]
    infer_instance
  have hcu : ∀ (u : G) (hu : u ∈ U) (w : W), c (σ ⟨u, hUH hu⟩ w) = c w := by
    intro u hu w
    have : σ ⟨u, hUH hu⟩ w - w ∈ twKer σ (U.subgroupOf H) 1 :=
      Submodule.subset_span ⟨⟨⟨u, hUH hu⟩, hu⟩, w, by simp⟩
    have h2 := (hck _).2 this
    rwa [map_sub, sub_eq_zero] at h2
  have hdec : ∀ g : G, g * (s (q g))⁻¹ ∈ U := by
    intro g
    rw [← hker, map_mul, map_inv, hqs, mul_inv_cancel]
  set Φ := coMap s hs hQH χ hχ σ σ' c hcomp with hΦ
  have hkill : twKer (cInd H σ) U 1 ≤ LinearMap.ker Φ := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨u, f, rfl⟩
    show Φ _ = 0
    apply Subtype.ext
    apply Subtype.ext
    funext x
    have hn : s x * u * (s x)⁻¹ ∈ U := hUn.conj_mem _ u.2 _
    have e : (cInd H σ (u : G) f).1.1.1 (s x) = σ ⟨_, hUH hn⟩ (f.1.1.1 (s x)) := by
      have := f.1.1.2 ⟨_, hUH hn⟩ (s x)
      rw [← this]
      show f.1.1.1 (s x * u) = f.1.1.1 (s x * u * (s x)⁻¹ * s x)
      congr 1
      group
    show ((χ x : ℂˣ) : ℂ) • c ((cInd H σ (u : G) f - ((1 : U →* ℂˣ) u : ℂ) • f).1.1.1 (s x)) = 0
    have e2 : (cInd H σ (u : G) f - ((1 : U →* ℂˣ) u : ℂ) • f).1.1.1 (s x)
        = (cInd H σ (u : G) f).1.1.1 (s x) - f.1.1.1 (s x) := by
      simp
    rw [e2, e, map_sub, hcu _ hn, sub_self, smul_zero]
  have hinj : ∀ f : cIndSpace H σ, Φ f = 0 → f ∈ twKer (cInd H σ) U 1 := by
    intro f hf
    refine hK f fun g => ?_
    rw [← hck]
    have h1 : ∀ x, c (f.1.1.1 (s x)) = 0 := by
      intro x
      have h2 : ((χ x : ℂˣ) : ℂ) • c (f.1.1.1 (s x)) = 0 := by
        have := congrArg (fun F : smoothPart (ind Q σ') => F.1.1 x) hf
        exact this
      exact (smul_eq_zero.1 h2).resolve_left (Units.ne_zero _)
    have h3 : f.1.1.1 g = σ ⟨_, hUH (hdec g)⟩ (f.1.1.1 (s (q g))) := by
      rw [← f.1.1.2 ⟨_, hUH (hdec g)⟩ (s (q g))]
      congr 1
      group
    rw [h3, hcu _ (hdec g), h1]
  have hmemH : ∀ g, q g ∈ Q → g ∈ H := by
    intro g hg
    have : g = (g * (s (q g))⁻¹) * s (q g) := by group
    rw [this]
    exact mul_mem (hUH (hdec g)) (hQH _ hg)
  let qH : H →* Q := (q.comp H.subtype).codRestrict Q fun h => hHQ h h.2
  let σb : Representation ℂ H W' := SmGL.twist (σ'.comp qH) (χ.comp (q.comp H.subtype))⁻¹
  have hσb : ∀ (h : H) (w : W'), σb h w = (((χ (q h))⁻¹ : ℂˣ) : ℂ) • σ' (qH h) w := fun h w => rfl
  have hcb : ∀ (h : H) (w : W), c (σ h w) = σb h (c w) := by
    intro h w
    have hp : q h ∈ Q := hHQ h h.2
    have e : h = ⟨_, hUH (hdec h)⟩ * ⟨s (q h), hQH _ hp⟩ := by
      apply Subtype.ext
      show (h : G) = (h : G) * (s (q h))⁻¹ * s (q h)
      group
    have e1 : c (σ h w) = c (σ ⟨s (q h), hQH _ hp⟩ w) := by
      conv_lhs => rw [e, map_mul, Module.End.mul_apply]
      rw [hcu _ (hdec h)]
    rw [e1, hσb]
    have := hcomp ⟨q h, hp⟩ w
    show _ = (((χ (q h))⁻¹ : ℂˣ) : ℂ) • σ' ⟨q h, hp⟩ (c w)
    rw [← this, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  have hsurj : ∀ φ : smoothPart (ind Q σ'), ∃ f, Φ f = φ := by
    intro φ
    let b : G → W' := fun g => (((χ (q g))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q g)
    have hb : b ∈ indSpace H σb := by
      intro h g
      have h1 : φ.1.1 (q h * q g) = σ' (qH h) (φ.1.1 (q g)) := φ.1.2 (qH h) (q g)
      show (((χ (q ((h : G) * g)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q ((h : G) * g)) = σb h ((((χ (q g))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q g))
      rw [map_mul, h1, map_smul, hσb, map_mul, mul_inv, Units.val_mul, smul_smul, mul_comm]
    have hbs : (⟨b, hb⟩ : indSpace H σb) ∈ smoothPart (ind H σb) := by
      refine mem_smoothPart_of_nhds (Filter.mem_of_superset
        (((IsOpen.preimage hq φ.2).inter (IsOpen.preimage hq hχ)).mem_nhds ?_) ?_)
      · refine ⟨?_, ?_⟩
        · simp
        · simp
      · rintro x ⟨h1, h2⟩
        have h1' : ind Q σ' (q x) φ.1 = φ.1 := h1
        have h2' : χ (q x) = 1 := h2
        apply Subtype.ext
        funext y
        show (((χ (q (y * x)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q (y * x)) = (((χ (q y))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q y)
        have h3 : φ.1.1 (q y * q x) = φ.1.1 (q y) := congrFun (congrArg Subtype.val h1') (q y)
        rw [map_mul, map_mul, h2', mul_one, h3]
    have hbc : (⟨⟨b, hb⟩, hbs⟩ : smoothPart (ind H σb)) ∈ cIndSpace H σb := by
      refine ⟨s '' C, hC.image hs, fun g _ => ?_⟩
      obtain ⟨p, hp, y, hy, e⟩ := hMC (q g)
      refine ⟨g * (s y)⁻¹, hmemH _ ?_, s y, ⟨y, hy, rfl⟩, by group⟩
      rw [map_mul, map_inv, hqs, e]
      simpa using hp
    obtain ⟨F, hF⟩ := GlobalTheory.CompanionTheory.BZMirOnto.cInd_lift H hH hbasis σ σb c hc hcb (fun w _ => by
      let S : Subgroup H :=
        { carrier := {h | σ h w = w}
          one_mem' := by simp
          mul_mem' := fun {a b} ha hb => by
            simp only [Set.mem_setOf_eq, map_mul, Module.End.mul_apply] at *
            rw [hb, ha]
          inv_mem' := fun {a} ha => by
            simp only [Set.mem_setOf_eq] at *
            conv_lhs => rw [← ha]
            rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
      exact ⟨S, hσ w, fun t ht _ => ht⟩) ⟨⟨⟨b, hb⟩, hbs⟩, hbc⟩
    refine ⟨F, Subtype.ext (Subtype.ext (funext fun x => ?_))⟩
    show ((χ x : ℂˣ) : ℂ) • c (F.1.1.1 (s x)) = φ.1.1 x
    rw [hF]
    show ((χ x : ℂˣ) : ℂ) • ((((χ (q (s x)))⁻¹ : ℂˣ) : ℂ) • φ.1.1 (q (s x))) = φ.1.1 x
    rw [hqs, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let L := (twKer (cInd H σ) U 1).liftQ Φ hkill
  have hL : Function.Bijective L := by
    constructor
    · rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      exact (Submodule.Quotient.mk_eq_zero _).2 (hinj f hx)
    · intro φ
      obtain ⟨f, hf⟩ := hsurj φ
      exact ⟨Submodule.Quotient.mk f, hf⟩
  exact ⟨LinearEquiv.ofBijective L hL, fun f x => rfl⟩

end Abstract2

end GlobalTheory.CompanionTheory.CIndCoinv
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHolds
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.RgGu.PsiGP

section Tensor

variable {V₁ V Z Y : Type} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V] [Module ℂ V] [AddCommGroup Z] [Module ℂ Z]
  [AddCommGroup Y] [Module ℂ Y]

def pair (a : V) (y : Y) : ∀ x : Bool, TwoT V Y x
  | false => a
  | true => y

def cMap (i : V₁ ≃ₗ[ℂ] V) (mk : Z →ₗ[ℂ] Y) : V₁ ⊗[ℂ] Z →ₗ[ℂ] PiTensorProduct ℂ (TwoT V Y) :=
  (Exponents.boolTensorEquiv (X := TwoT V Y)).symm.toLinearMap ∘ₗ TensorProduct.map i.toLinearMap mk

theorem bool_tprod_pair (a : V) (y : Y) :
    Exponents.boolTensorEquiv (X := TwoT V Y) (PiTensorProduct.tprod ℂ (pair a y)) = (a ⊗ₜ[ℂ] y : V ⊗[ℂ] Y) :=
  Exponents.boolTensorEquiv_tprod _

theorem cMap_tmul (i : V₁ ≃ₗ[ℂ] V) (mk : Z →ₗ[ℂ] Y) (a : V₁) (b : Z) :
    cMap i mk (a ⊗ₜ[ℂ] b) = PiTensorProduct.tprod ℂ (pair (i a) (mk b)) := by
  apply (Exponents.boolTensorEquiv (X := TwoT V Y)).injective
  rw [bool_tprod_pair]
  show (Exponents.boolTensorEquiv (X := TwoT V Y)) ((Exponents.boolTensorEquiv (X := TwoT V Y)).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

theorem tprod_pair_smul (a : V) (d : ℂ) (y : Y) :
    PiTensorProduct.tprod ℂ (pair a (d • y)) = d • PiTensorProduct.tprod ℂ (pair a y) := by
  apply (Exponents.boolTensorEquiv (X := TwoT V Y)).injective
  rw [map_smul, bool_tprod_pair, bool_tprod_pair]
  exact TensorProduct.tmul_smul d a y

theorem cMap_surjective (i : V₁ ≃ₗ[ℂ] V) (mk : Z →ₗ[ℂ] Y) (h : Function.Surjective mk) :
    Function.Surjective (cMap i mk) :=
  (Exponents.boolTensorEquiv (X := TwoT V Y)).symm.surjective.comp (TensorProduct.map_surjective i.surjective h)

theorem cMap_eq_zero (i : V₁ ≃ₗ[ℂ] V) (mk : Z →ₗ[ℂ] Y) (h : Function.Surjective mk) (w : V₁ ⊗[ℂ] Z)
    (hw : cMap i mk w = 0) : w ∈ LinearMap.range (LinearMap.lTensor V₁ (LinearMap.ker mk).subtype) := by
  have h0 : TensorProduct.map i.toLinearMap mk w = 0 := by
    have : (Exponents.boolTensorEquiv (X := TwoT V Y)).symm (TensorProduct.map i.toLinearMap mk w) = 0 := hw
    simpa using this
  have h1 : LinearMap.lTensor V₁ mk w = 0 := by
    have e : ∀ w : V₁ ⊗[ℂ] Z, TensorProduct.map i.symm.toLinearMap LinearMap.id (TensorProduct.map i.toLinearMap mk w) =
        LinearMap.lTensor V₁ mk w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | add x y hx hy => simp only [map_add (f := _), hx, hy]
      | tmul a b => simp
    rw [← e, h0, map_zero]
  have hex : Function.Exact (LinearMap.ker mk).subtype mk := LinearMap.exact_subtype_ker_map mk
  exact (lTensor_exact V₁ hex h w).1 h1

end Tensor

section Intertwine

variable {G M W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M]
  [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

theorem coinv_intertwine (H U : Subgroup G) (Q : Subgroup M) (s : M →* G) (χ : M →* ℂˣ)
    (σ : Representation ℂ H W) (σ' : Representation ℂ Q W') (c : W →ₗ[ℂ] W')
    (E : (cIndSpace H σ ⧸ twKer (cInd H σ) U 1) ≃ₗ[ℂ] smoothPart (ind Q σ'))
    (hE : ∀ (f : cIndSpace H σ) (x : M), (E (Submodule.Quotient.mk f)).1.1 x = (χ x : ℂ) • c (f.1.1.1 (s x)))
    (g : M) (f : cIndSpace H σ) :
    E ((χ g : ℂ) • Submodule.Quotient.mk (cInd H σ (s g) f)) = smInd Q σ' g (E (Submodule.Quotient.mk f)) := by
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  rw [LinearEquiv.map_smul]
  show (χ g : ℂ) • (E (Submodule.Quotient.mk (cInd H σ (s g) f))).1.1 x = (E (Submodule.Quotient.mk f)).1.1 (x * g)
  rw [hE, hE, map_mul, smul_smul, Units.val_mul, mul_comm]
  show _ • c (f.1.1.1 (s x * s g)) = _ • c (f.1.1.1 (s (x * g)))
  rw [map_mul]

end Intertwine

section Concrete

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem parab_mul_KO {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) :
    ∀ g : GL n k, ∃ p ∈ parab k e, ∃ x ∈ GlobalTheory.SplitWeil.KO k n, g = p * x := by
  obtain ⟨-, -, -, -, -, -, -, -, h⟩ := GlobalTheory.SmGL.LeviInt.levi_integral_facts k α n m e
  exact h

theorem det_levi (n : ℕ) (g : GL (Fin n) k) :
    GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = GeneralLinearGroup.det g := by
  ext
  exact GlobalTheory.CompanionTheory.MirPsiPair.det_glEmbMat n _

theorem det_unip (n : ℕ) (v : Multiplicative (Fin n → k)) : GeneralLinearGroup.det (unip k n v) = 1 := by
  ext
  show (1 + colMat k n v.toAdd : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      simp [colMat]
    · simp [colMat, hi]
  · intro a b hab
    have hb : b ≠ Fin.last n := fun h => by
      subst h
      exact absurd (Fin.le_last a) (not_le.2 hab)
    have hne : a ≠ b := fun h => by
      subst h
      exact lt_irrefl _ hab
    simp [colMat, hb, Matrix.one_apply, hne]

theorem dpowM_levi (n : ℕ) (s : ℝ) (g : GL (Fin n) k) :
    dpowM n s (levi k n g) = dpow n s g := by
  show absPow k (s : ℂ) (GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k)) = absPow k (s : ℂ) _
  rw [det_levi]

theorem dpowM_of_mem (n : ℕ) (s : ℝ) (u : Mir k n) (hu : u ∈ MirUin k n) : dpowM n s u = 1 := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  show absPow k (s : ℂ) (GeneralLinearGroup.det (u : GL (Fin (n + 1)) k)) = 1
  have hv' : (u : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv', det_unip, map_one]

theorem scalar_id (m j : ℕ) (a b : kˣ) :
    absPow k ((-1 / 2 : ℝ) : ℂ) (a * b) * absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) a *
        absPow k (((-((m : ℕ) : ℝ) / 2 : ℝ)) : ℂ) b =
      absPow k ((j : ℂ) / 2) a * absPow k (-(m : ℂ) / 2) b * absPow k ((-1 / 2 : ℝ) : ℂ) b := by
  have e1 : absPow k (((((j + 1 : ℕ) : ℝ) / 2 : ℝ)) : ℂ) = absPow k ((j : ℂ) / 2) * absPow k (1 / 2) := by
    rw [← absPow_add]
    congr 1
    push_cast
    ring
  have e2 : absPow k ((-1 / 2 : ℝ) : ℂ) = (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg]
    congr 1
    push_cast
    ring
  have e3 : absPow k (((-((m : ℕ) : ℝ) / 2 : ℝ)) : ℂ) = absPow k (-(m : ℂ) / 2) := by
    congr 1
    push_cast
    ring
  rw [e1, e2, e3]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, mul_inv]
  generalize absPow k (1 / 2) a = A
  generalize absPow k (1 / 2) b = B
  generalize absPow k ((j : ℂ) / 2) a = P
  generalize absPow k (-(m : ℂ) / 2) b = R
  calc A⁻¹ * B⁻¹ * (P * A) * R = (A⁻¹ * A) * (P * R * B⁻¹) := by ac_rfl
    _ = P * R * B⁻¹ := by rw [inv_mul_cancel, one_mul]

end Concrete

section Main

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

abbrev eMJ (m j : ℕ) : (Σ x, Two (Fin m) (Fin j) x) ≃ Fin (m + j) := two (stdSum (rfl : m + j = m + j))

variable {m j : ℕ} (ρ : GRep k m) (τ : MRep k j)

abbrev Vt : Type := (ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).V

abbrev Zt (m : ℕ) : Type := (mtw τ (-((m : ℕ) : ℝ) / 2)).V

abbrev sig := (extTensor (ρ.tw (((j + 1 : ℕ) : ℝ) / 2)).ρ (mtw τ (-((m : ℕ) : ℝ) / 2)).ρ).comp (gpProj k m j)

abbrev sigP : Representation ℂ (parab k (eMJ m j)) (PiTensorProduct ℂ (TwoT ρ.V (psiN τ).V)) :=
  (SmGL.twist (piTensor (twoRep ρ.ρ (psiN τ).ρ)) (deltaHalf k (Two (Fin m) (Fin j)))).comp (leviProj k (eMJ m j))

abbrev mkY : τ.V →ₗ[ℂ] (psiN τ).V := (twKer τ.ρ (MirUin k j) 1).mkQ

abbrev mkZ (m : ℕ) : Zt τ m →ₗ[ℂ] (psiN τ).V := (twKer τ.ρ (MirUin k j) 1).mkQ

abbrev iV (j : ℕ) : Vt (j := j) ρ ≃ₗ[ℂ] ρ.V := LinearEquiv.refl ℂ ρ.V

abbrev cc : Vt (j := j) ρ ⊗[ℂ] Zt τ m →ₗ[ℂ] PiTensorProduct ℂ (TwoT ρ.V (psiN τ).V) := cMap (iV ρ j) (mkZ τ m)

theorem cc_tmul (a : ρ.V) (b : τ.V) : cc ρ τ ((a : Vt (j := j) ρ) ⊗ₜ[ℂ] (b : Zt τ m)) =
    PiTensorProduct.tprod ℂ (pair a (mkY τ b)) :=
  cMap_tmul _ _ _ _

theorem levi_mem_HGP (p : GL (Fin (m + j)) k) (hp : p ∈ parab k (eMJ m j)) : levi k (m + j) p ∈ MirabolicParabolic k m j := by
  have hproj : mirabolicProjection k (m + j) (levi k (m + j) p) = p := by
    apply Units.ext
    ext a b
    change blockMat k (m + j) (glEmbMat k (m + j) (p : Matrix (Fin (m + j)) (Fin (m + j)) k)) a b = _
    simp [blockMat, glEmbMat]
  apply (GlobalTheory.T.mem_mirabolicParabolic_iff_parabolic k m j _).2
  rwa [hproj]

theorem hcomp (p : parab k (eMJ m j)) (w : Vt (j := j) ρ ⊗[ℂ] Zt τ m) :
    ((dpow (m + j) (-1 / 2) (p : GL (Fin (m + j)) k) : ℂˣ) : ℂ) •
        cc ρ τ (sig ρ τ ⟨levi k (m + j) p, levi_mem_HGP _ p.2⟩ w) = sigP ρ τ p (cc ρ τ w) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add (f := _), smul_add, hx, hy]
  | tmul a b =>
    set g₁ : GL (Fin m) k := leviProj k (eMJ m j) p false with hg₁
    set g₂ : GL (Fin j) k := leviProj k (eMJ m j) p true with hg₂
    have hgp := GlobalTheory.T.gpProj_levi_formula k m j (p : GL (Fin (m + j)) k) p.2 (levi_mem_HGP _ p.2)
    have h1 : sig ρ τ ⟨levi k (m + j) p, levi_mem_HGP _ p.2⟩ (a ⊗ₜ[ℂ] b) =
        (((dpow m (((j + 1 : ℕ) : ℝ) / 2) g₁ : ℂˣ) : ℂ) • ρ.ρ g₁ a : Vt (j := j) ρ) ⊗ₜ[ℂ]
          (((dpow j (-((m : ℕ) : ℝ) / 2) g₂ : ℂˣ) : ℂ) • τ.ρ (levi k j g₂) b : Zt τ m) := by
      show extTensor _ _ (gpProj k m j _) _ = _
      rw [hgp]
      refine (extTensor_tmul _ _ _ a b).trans ?_
      show (((dpow m (((j + 1 : ℕ) : ℝ) / 2) g₁ : ℂˣ) : ℂ) • ρ.ρ g₁ a : Vt (j := j) ρ) ⊗ₜ[ℂ]
        (((dpowM j (-((m : ℕ) : ℝ) / 2) (levi k j g₂) : ℂˣ) : ℂ) • τ.ρ (levi k j g₂) b : Zt τ m) = _
      rw [dpowM_levi]
    have h2 : (fun x => twoRep ρ.ρ (psiN τ).ρ x (leviProj k (eMJ m j) p x) (pair a (mkY τ b) x)) =
        pair (ρ.ρ g₁ a) (((dpow j (-1 / 2) g₂ : ℂˣ) : ℂ) • mkY τ (τ.ρ (levi k j g₂) b)) := by
      funext x
      cases x
      · rfl
      · rfl
    have hlev : leviProj k (eMJ m j) p = leviTwo k (Fin m) (Fin j) (g₁, g₂) := by
      funext x
      cases x
      · rfl
      · rfl
    have hdet : GeneralLinearGroup.det (p : GL (Fin (m + j)) k) =
        GeneralLinearGroup.det g₁ * GeneralLinearGroup.det g₂ := by
      rw [det_parab, Fintype.prod_bool, mul_comm]
    have hs : ((dpow (m + j) (-1 / 2) (p : GL (Fin (m + j)) k) : ℂˣ) : ℂ) *
        (((dpow m (((j + 1 : ℕ) : ℝ) / 2) g₁ : ℂˣ) : ℂ) * ((dpow j (-((m : ℕ) : ℝ) / 2) g₂ : ℂˣ) : ℂ)) =
        ((deltaHalf k (Two (Fin m) (Fin j)) (leviProj k (eMJ m j) p) : ℂˣ) : ℂ) * ((dpow j (-1 / 2) g₂ : ℂˣ) : ℂ) := by
      rw [hlev, deltaHalf_two, ← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
      congr 1
      have := scalar_id (k := k) m j (GeneralLinearGroup.det g₁) (GeneralLinearGroup.det g₂)
      simp only [dpow, detChar_apply, hdet, Fintype.card_fin]
      rw [← mul_assoc]
      exact this
    have h3 : cc ρ τ (sig ρ τ ⟨levi k (m + j) p, levi_mem_HGP _ p.2⟩ (a ⊗ₜ[ℂ] b)) =
        (((dpow m (((j + 1 : ℕ) : ℝ) / 2) g₁ : ℂˣ) : ℂ) * ((dpow j (-((m : ℕ) : ℝ) / 2) g₂ : ℂˣ) : ℂ)) •
          PiTensorProduct.tprod ℂ (pair (ρ.ρ g₁ a) (mkY τ (τ.ρ (levi k j g₂) b))) := by
      rw [h1, TensorProduct.smul_tmul_smul]
      exact (LinearMap.map_smul (cc ρ τ) _ _).trans (congrArg _ (cc_tmul ρ τ _ _))
    have h4 : cc ρ τ (a ⊗ₜ[ℂ] b) = PiTensorProduct.tprod ℂ (pair a (mkY τ b)) := cc_tmul ρ τ a b
    rw [h3, h4, smul_smul, hs, ← smul_smul]
    show _ = ((deltaHalf k (Two (Fin m) (Fin j)) (leviProj k (eMJ m j) p) : ℂˣ) : ℂ) •
      piTensor (twoRep ρ.ρ (psiN τ).ρ) (leviProj k (eMJ m j) p) (PiTensorProduct.tprod ℂ (pair a (mkY τ b)))
    rw [piTensor_tprod]
    exact congrArg _ ((tprod_pair_smul _ _ _).symm.trans (congrArg (PiTensorProduct.tprod ℂ) h2.symm))

theorem mkZ_surjective : Function.Surjective (mkZ τ m) :=
  Submodule.mkQ_surjective (twKer τ.ρ (MirUin k j) 1)

theorem mkY_unip (u : Mir k j) (hu : u ∈ MirUin k j) (b : τ.V) : mkY τ (τ.ρ u b) = mkY τ b := by
  refine (Submodule.Quotient.eq _).2 (Submodule.subset_span ⟨⟨u, hu⟩, b, ?_⟩)
  simp

theorem sig_tmul (v : MirabolicParabolic k m j) (a : Vt (j := j) ρ) (b : Zt τ m) (hv : (gpProj k m j v).1 = 1)
    (hv2 : (gpProj k m j v).2 ∈ MirUin k j) :
    sig ρ τ v (a ⊗ₜ[ℂ] b) = a ⊗ₜ[ℂ] (τ.ρ (gpProj k m j v).2 b : Zt τ m) := by
  refine (extTensor_tmul _ _ _ a b).trans ?_
  rw [hv]
  show (((dpow m (((j + 1 : ℕ) : ℝ) / 2) 1 : ℂˣ) : ℂ) • ρ.ρ 1 a : Vt (j := j) ρ) ⊗ₜ[ℂ]
    (((dpowM j (-((m : ℕ) : ℝ) / 2) (gpProj k m j v).2 : ℂˣ) : ℂ) • τ.ρ (gpProj k m j v).2 b : Zt τ m) = _
  rw [dpowM_of_mem _ _ _ hv2, map_one, map_one]
  simp
  rfl

theorem tmul_mem_twKer (a : Vt (j := j) ρ) (t : Zt τ m) (ht : t ∈ twKer τ.ρ (MirUin k j) 1) :
    a ⊗ₜ[ℂ] t ∈ twKer (sig ρ τ) ((MirUin k (m + j)).subgroupOf (MirabolicParabolic k m j)) 1 := by
  refine Submodule.span_induction (p := fun t _ => a ⊗ₜ[ℂ] (t : Zt τ m) ∈ twKer (sig ρ τ) ((MirUin k (m + j)).subgroupOf (MirabolicParabolic k m j)) 1)
    ?_ ?_ ?_ ?_ ht
  · rintro _ ⟨n, b, rfl⟩
    obtain ⟨v, hv, hv2⟩ := GlobalTheory.T.gpProj_unipotent_surjective k m j (n : Mir k j) n.2
    refine Submodule.subset_span ⟨⟨v, hv⟩, a ⊗ₜ[ℂ] b, ?_⟩
    have h1 := sig_tmul ρ τ v a b (by rw [hv2]) (by rw [hv2]; exact n.2)
    rw [hv2] at h1
    show _ = sig ρ τ v _ - _
    rw [h1]
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    exact TensorProduct.tmul_sub _ _ _
  · show a ⊗ₜ[ℂ] (0 : Zt τ m) ∈ _
    rw [TensorProduct.tmul_zero]
    exact zero_mem _
  · intro x y _ _ hx hy
    show a ⊗ₜ[ℂ] ((x : Zt τ m) + (y : Zt τ m)) ∈ _
    rw [TensorProduct.tmul_add]
    exact add_mem hx hy
  · intro c x _ hx
    show a ⊗ₜ[ℂ] (c • (x : Zt τ m)) ∈ _
    rw [TensorProduct.tmul_smul]
    exact Submodule.smul_mem _ _ hx

theorem hck (w : Vt (j := j) ρ ⊗[ℂ] Zt τ m) :
    cc ρ τ w = 0 ↔ w ∈ twKer (sig ρ τ) ((MirUin k (m + j)).subgroupOf (MirabolicParabolic k m j)) 1 := by
  constructor
  · intro hw
    obtain ⟨y, rfl⟩ := cMap_eq_zero (iV ρ j) (mkZ τ m) (mkZ_surjective τ) w hw
    clear hw
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy =>
      rw [map_add (f := _)]
      exact Submodule.add_mem _ hx hy
    | tmul a t =>
      exact tmul_mem_twKer ρ τ a _ ((Submodule.Quotient.mk_eq_zero _).1 t.2)
  · intro hw
    have hle : twKer (sig ρ τ) ((MirUin k (m + j)).subgroupOf (MirabolicParabolic k m j)) 1 ≤ LinearMap.ker (cc ρ τ) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨u, w, rfl⟩
      have hu : ((u : MirabolicParabolic k m j) : Mir k (m + j)) ∈ MirUin k (m + j) := u.2
      obtain ⟨h1, h2⟩ := GlobalTheory.T.gpProj_unipotent k m j u hu
      have key : ∀ w, cc ρ τ (sig ρ τ (u : MirabolicParabolic k m j) w) = cc ρ τ w := by
        intro w
        induction w using TensorProduct.induction_on with
        | zero => simp
        | add x y hx hy => simp only [map_add (f := _), hx, hy]
        | tmul a b =>
          rw [sig_tmul ρ τ _ a b h1 h2]
          exact (cc_tmul ρ τ _ _).trans ((congrArg (fun y => PiTensorProduct.tprod ℂ (pair (V := ρ.V) a y)) (mkY_unip τ _ h2 b)).trans
            (cc_tmul ρ τ a b).symm)
      show cc ρ τ (sig ρ τ (u : MirabolicParabolic k m j) w - (((1 : ((MirUin k (m + j)).subgroupOf (MirabolicParabolic k m j)) →* ℂˣ) u : ℂˣ) : ℂ) • w) = 0
      simp only [MonoidHom.one_apply, Units.val_one, one_smul, map_sub]
      exact sub_eq_zero.2 (key w)
    exact hle hw

theorem isOpen_dpow_ker (n : ℕ) (s : ℝ) : IsOpen ((dpow (k := k) n s).ker : Set (GL (Fin n) k)) :=
  (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

theorem isSmooth_sig (hρ : IsSmooth ρ.ρ) (hτ : IsSmooth τ.ρ) : IsSmooth (sig ρ τ) := by
  refine isSmooth_comp (isSmooth_extTensor (isSmooth_twist hρ (isOpen_dpow_ker _ _)) ?_) _ (GlobalTheory.T.gpProj_continuous k m j)
  exact isSmooth_twist hτ (IsSmoothChar.comp (χ := dpow (j + 1) (-((m : ℕ) : ℝ) / 2)) (isOpen_dpow_ker _ _) (Mir k j).subtype
    continuous_subtype_val)

theorem exE (hρ : IsSmooth ρ.ρ) (hτ : IsSmooth τ.ρ) :
    ∃ E : (cIndSpace (MirabolicParabolic k m j) (sig ρ τ) ⧸ twKer (cInd (MirabolicParabolic k m j) (sig ρ τ)) (MirUin k (m + j)) 1) ≃ₗ[ℂ]
        smoothPart (ind (parab k (eMJ m j)) (sigP ρ τ)),
      ∀ (f : cIndSpace (MirabolicParabolic k m j) (sig ρ τ)) (x : GL (Fin (m + j)) k), (E (Submodule.Quotient.mk f)).1.1 x =
        ((dpow (m + j) (-1 / 2) x : ℂˣ) : ℂ) • cc ρ τ (f.1.1.1 (levi k (m + j) x)) := by
  have hPK := parab_mul_KO (k := k) (eMJ m j)
  have hker : ∀ g, mirabolicProjection k (m + j) g = 1 ↔ g ∈ MirUin k (m + j) := by
    intro g
    constructor
    · intro hg
      let A : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k := (g : GL (Fin (m + j + 1)) k)
      have hrow : A (Fin.last (m + j)) = eLast k (m + j) := (mem_Mir_iff k g.1).1 g.2
      have hblock (a b : Fin (m + j)) : A a.castSucc b.castSucc = (1 : Matrix (Fin (m + j)) (Fin (m + j)) k) a b :=
        congrArg (fun u : GL (Fin (m + j)) k => (u : Matrix (Fin (m + j)) (Fin (m + j)) k) a b) hg
      refine ⟨Multiplicative.ofAdd (fun a => A a.castSucc (Fin.last (m + j))), ?_⟩
      apply Units.ext
      ext a b
      change ((1 : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) +
        colMat k (m + j) (fun i => A i.castSucc (Fin.last (m + j)))) a b = A a b
      rw [Matrix.add_apply, colMat]
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a, rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b, rfl⟩ | rfl
      · simp [Matrix.one_apply, hblock]
      · simp [Matrix.one_apply, Fin.castSucc_ne_last]
      · simp [Matrix.one_apply, Fin.castSucc_ne_last, (Fin.castSucc_ne_last _).symm, hrow, eLast]
      · simp [hrow, eLast]
    · intro hg
      obtain ⟨v, hv⟩ := (hg : (g : GL (Fin (m + j + 1)) k) ∈ MirU k (m + j))
      have hv' : unip k (m + j) v = g.1 := hv
      apply Units.ext
      ext a b
      change blockMat k (m + j) (g.1 : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) a b = _
      rw [blockMat, ← hv']
      change ((1 : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) + colMat k (m + j) v.toAdd)
        a.castSucc b.castSucc = (1 : Matrix (Fin (m + j)) (Fin (m + j)) k) a b
      simp [colMat, Matrix.one_apply, Fin.castSucc_ne_last]
  have hUH : MirUin k (m + j) ≤ MirabolicParabolic k m j := fun g hg => by
    refine (GlobalTheory.T.mem_mirabolicParabolic_iff_parabolic k m j g).2 ?_
    rw [(hker g).2 hg]
    exact one_mem _
  have hN : (MirUin k (m + j)).Normal := by
    have : MirUin k (m + j) = (mirabolicProjection k (m + j)).ker := by
      ext g
      rw [MonoidHom.mem_ker, hker]
    rw [this]
    infer_instance
  have hproj_levi (g : GL (Fin (m + j)) k) : mirabolicProjection k (m + j) (levi k (m + j) g) = g := by
    apply Units.ext
    ext a b
    change blockMat k (m + j) (glEmbMat k (m + j) (g : Matrix (Fin (m + j)) (Fin (m + j)) k)) a b = _
    simp [blockMat, glEmbMat]
  have hproj_cont : Continuous (mirabolicProjection k (m + j)) := by
    have hval : Continuous fun g : Mir k (m + j) =>
        (g.1 : Matrix (Fin (m + j + 1)) (Fin (m + j + 1)) k) :=
      Units.continuous_val.comp continuous_subtype_val
    have hblock : Continuous fun g : Mir k (m + j) =>
        (mirabolicProjection k (m + j) g : Matrix (Fin (m + j)) (Fin (m + j)) k) := by
      refine continuous_pi fun a => continuous_pi fun b => ?_
      exact (continuous_apply b.castSucc).comp ((continuous_apply a.castSucc).comp hval)
    refine Units.continuous_iff.2 ⟨hblock, ?_⟩
    have hblock_inv : Continuous fun g : Mir k (m + j) =>
        (mirabolicProjection k (m + j) g⁻¹ : Matrix (Fin (m + j)) (Fin (m + j)) k) :=
      hblock.comp continuous_inv
    simpa only [map_inv] using hblock_inv
  exact GlobalTheory.CompanionTheory.CIndCoinv.coinv_equiv (MirabolicParabolic k m j) (MirUin k (m + j)) (parab k (eMJ m j)) (levi k (m + j))
    (mirabolicProjection k (m + j)) (GlobalTheory.T.isClosed_mirabolicParabolic k m j) (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k (m + j))
    (GlobalTheory.CompanionTheory.BZMirFun.continuous_levi k (m + j)) hproj_cont
    hproj_levi hker hUH (fun g hg => (GlobalTheory.T.mem_mirabolicParabolic_iff_parabolic k m j g).1 hg)
    (fun p hp => levi_mem_HGP p hp) (GlobalTheory.SplitWeil.KO k (Fin (m + j))) GlobalTheory.SplitFlip.isCompact_KO hPK
    (dpow (m + j) (-1 / 2)) (isOpen_dpow_ker _ _) (sig ρ τ) (isSmooth_sig ρ τ hρ hτ) (sigP ρ τ)
    (cc ρ τ) (cMap_surjective _ _ (mkZ_surjective τ)) (hck ρ τ) (hcomp ρ τ)
    (GlobalTheory.T.compact_induction_twisted_kernel _ _ hUH (GlobalTheory.CompanionTheory.BZMirOnto.exists_compactOpen k (m + j)) _ (isSmooth_sig ρ τ hρ hτ))

set_option synthInstance.maxHeartbeats 100000 in
theorem psiMinus_cInd_equiv_smInd (hρ : IsSmooth ρ.ρ) (hτ : IsSmooth τ.ρ) :
    Nonempty ((SmGL.twist (psiMinus k (cInd (MirabolicParabolic k m j) (sig ρ τ))) (dpow (m + j) (-1 / 2))).Equiv
      (smInd (parab k (eMJ m j)) (sigP ρ τ))) := by
  refine (exE ρ τ hρ hτ).elim fun E hE => ?_
  have key := coinv_intertwine _ _ _ (levi k (m + j)) (dpow (m + j) (-1 / 2)) _ _ _ E hE
  refine ⟨Representation.Equiv.mk E ?_⟩
  intro g
  refine LinearMap.ext fun y => ?_
  refine Submodule.Quotient.induction_on _ y fun f => ?_
  have h1 : SmGL.twist (psiMinus k (cInd (MirabolicParabolic k m j) (sig ρ τ))) (dpow (m + j) (-1 / 2)) g (Submodule.Quotient.mk f) =
      ((dpow (m + j) (-1 / 2) g : ℂˣ) : ℂ) • Submodule.Quotient.mk (cInd (MirabolicParabolic k m j) (sig ρ τ) (levi k (m + j) g) f) := rfl
  have h2 : E (SmGL.twist (psiMinus k (cInd (MirabolicParabolic k m j) (sig ρ τ))) (dpow (m + j) (-1 / 2)) g (Submodule.Quotient.mk f)) =
      smInd (parab k (eMJ m j)) (sigP ρ τ) g (E (Submodule.Quotient.mk f)) := (congrArg E h1).trans (key g f)
  exact h2

end Main

theorem psiGP : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PsiGP k := by
  intro k _ _ _ _ m j ρ τ hρ hτ
  exact psiMinus_cInd_equiv_smInd ρ τ hρ hτ

end GlobalTheory.CompanionTheory.RgGu.PsiGP
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PsiGpCommutationHoldsStatement
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.psi_gp_commutation_holds : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], PsiGP k := by
  first | exact @GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | exact GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP | (intros; apply GlobalTheory.CompanionTheory.RgGu.PsiGP.psiGP <;> assumption)
end
