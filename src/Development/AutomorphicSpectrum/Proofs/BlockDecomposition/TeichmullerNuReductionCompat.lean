module

public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.FrobeniusFactorisation.PullT
public import Lean.LibrarySuggestions.Basic
public import Lean.Elab.Command
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.LatCDefs
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonzeroLocusSecMonoConst

@[expose] public section

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuReductionCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuReductionCompat
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuRed

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem red_phiP {m n : ℕ} (h : n ≤ m) (N : ℕ) (x : (base l).Acr m) :
    (base l).red h (Mid.phiP l m N x) = Mid.phiP l n N ((base l).red h x) := by
  induction N with
  | zero => rfl
  | succ N ih => rw [Mid.phiP_succ, Mid.phiP_succ, ← ih]; exact (pdOk_frob _).red_acr h _

def redLm (r : CrystallineSemistableComparison.Res l K) (M : Model l K) {m n : ℕ} (h : n ≤ m) :
    Mor (Mid.Lm r M m) (Mid.Lm r M n) ((base l).red h) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true m) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).red h) rfl (B.dd_red true _ h) (B.basePt _ _ (red_κm r h)) fun _ _ _ => rfl

def redLc (M : Model l K) {m n : ℕ} (h : n ≤ m) :
    Mor (B.Lc (B.schFn M.p) (okToOC l K) true m) (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).red h) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true m) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
    ((base l).red h) rfl (B.dd_red true _ h) (B.basePt _ _ (B.red_κb _ true h)) fun _ _ _ => rfl

theorem ptOut_snd (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (F : B.Fn (OK l K)) (n : ℕ)
    (B₀ : CommRingCat.{0}) (y : (F.ptK (Mid.κm r n)).obj B₀) :
    ((Mid.ptOut F n hT).app B₀ y).1.2 = y.1.2 := rfl

theorem nu_pt (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (F : B.Fn (OK l K)) {m n : ℕ} (h : n ≤ m)
    (B₀ : CommRingCat.{0}) (y : (F.ptK (Mid.κm r n)).obj B₀) :
    ((Mid.ptOut F m hT).app B₀ ((B.basePt F _ (red_κm r h)).app B₀ y)).1.2 =
      ((B.basePt F _ (B.red_κb _ true h)).app B₀ ((Mid.ptOut F n hT).app B₀ y)).1.2 := by
  rw [ptOut_snd, SH.base_snd, SH.base_snd, ptOut_snd]

theorem nu_red : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ}
    (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true (n + 1) j),
    (redT r M (Nat.le_succ n)).pull j (Mid.nu r M (n + 1) j hT x) =
      Mid.nu r M n j hT (B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j x) := by
  intro l _ K r N hT M n j x
  unfold Mid.nu Mid.nuMor B.redHc B.redMor redT
  exact cr_square (Mid.mOut r M (n + 1) hT) (redLm r M (Nat.le_succ n)) (redLc M (Nat.le_succ n)) (Mid.mOut r M n hT)
    (Mid.phiP_cris _ N) (B.red_cris _ (Nat.le_succ n)) (B.red_cris _ (Nat.le_succ n)) (Mid.phiP_cris _ N)
    (red_phiP (Nat.le_succ n) N) (nu_pt r hT _ (Nat.le_succ n)) j x

end GlobalTheory.CompanionTheory.NuRed
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuReductionCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_nu_reduction_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true (n + 1) j), (redT r M (Nat.le_succ n)).pull j (Mid.nu r M (n + 1) j hT x) = Mid.nu r M n j hT (B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j x) := by
  first | exact @GlobalTheory.CompanionTheory.NuRed.nu_red | exact GlobalTheory.CompanionTheory.NuRed.nu_red | (intros; apply GlobalTheory.CompanionTheory.NuRed.nu_red <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionIsDPMorphism
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionIsDPMorphism
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat

namespace GlobalTheory.CompanionTheory.LatC

section Gen
variable {W B W' B' : Type} [CommRing W] [CommRing B] [Algebra ℚ B] [CommRing W'] [CommRing B'] [Algebra ℚ B']
  (f : W →+* B) (ξ : W) (f' : W' →+* B') (ξ' : W') (l M : ℕ)

theorem map_isDPMorphism (g : B →+* B') (h : ∀ x ∈ Lat.sub f ξ l M, g x ∈ Lat.sub f' ξ' l M)
    (hg : g (f ξ) = f' ξ')
    (hc : DPClosed (Lat.ι f ξ l M) (Lat.γB f ξ)) (hc' : DPClosed (Lat.ι f' ξ' l M) (Lat.γB f' ξ')) :
    IsDPMorphism (Lat.γ f ξ l M hc) (Lat.γ f' ξ' l M hc') (Lat.map f ξ f' ξ' l M g h) := by
  have hIB : ∀ x ∈ Lat.IB f ξ, g x ∈ Lat.IB f' ξ' := by
    intro x hx
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hx
    rw [map_mul, hg]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)
  refine ⟨?_, ?_⟩
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g h a) ∈ Lat.IB f' ξ'
    rw [Lat.ι_map]
    exact hIB _ ha
  · intro n a ha
    have ha' : Lat.ι f ξ l M a ∈ Lat.IB f ξ := ha
    have hb : Lat.map f ξ f' ξ' l M g h a ∈ Lat.I f' ξ' l M := by
      show Lat.ι f' ξ' l M (Lat.map f ξ f' ξ' l M g h a) ∈ Lat.IB f' ξ'
      rw [Lat.ι_map]
      exact hIB _ ha'
    apply Lat.ι_injective f' ξ' l M
    rw [Lat.ι_γ _ _ _ _ _ hb, Lat.ι_map, Lat.ι_map, Lat.ι_γ _ _ _ _ _ ha, DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ _ ha',
      DividedPowers.RatAlgebra.dpow_eq_inv_fact_smul _ _ (hIB _ ha'), map_rat_smul, map_pow]

end Gen

variable {l : ℕ} [Fact l.Prime]

theorem dk_fk (k : ℕ) (w : Ainf l) : dk l k (fk l (k + 1) w) = fk l k w := by
  rfl

theorem levSys_ddp {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M) (m : ℕ) :
    IsDPMorphism ((levSys h).L (m + 1)).γ ((levSys h).L m).γ ((levSys h).dA m) := by
  exact map_isDPMorphism (fk l (m + 2)) (xi0 l) (fk l (m + 1)) (xi0 l) l M (dk l (m + 1))
    (fun x hx => h.dIn (m + 1) x hx) (dk_fk (m + 1) (xi0 l)) (h.hc (m + 2)) (h.hc (m + 1))

end GlobalTheory.CompanionTheory.LatC
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LevelSystemTransitionIsDPMorphismStatement
open GroundTheory.PAdicHodge Formalism.Per6 DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.Pb.Lat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.level_system_transition_isDPMorphism : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} {M : ℕ} (h : LevHyp l K M), ∀ m, IsDPMorphism ((levSys h).L (m + 1)).γ ((levSys h).L m).γ ((levSys h).dA m) := by
  first | exact @GlobalTheory.CompanionTheory.LatC.levSys_ddp | exact GlobalTheory.CompanionTheory.LatC.levSys_ddp | (intros; apply GlobalTheory.CompanionTheory.LatC.levSys_ddp <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuFrobeniusCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuFrobeniusCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section

namespace GlobalTheory.CompanionTheory.NuPhi

theorem cr_square_semi {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1} {h₃ : b₃.t = 1}
    {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I} {κ₄ : O →+* b₄.R ⧸ b₄.I}
    {Λ : Type} [CommRing Λ] {c₁ : Λ →+* b₁.R} {c₂ : Λ →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τa τb τc τd : Λ →+* Λ} (τ : Λ →+* Λ)
    [RingHomCompTriple τa τb τ] [RingHomCompTriple τc τd τ]
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τa a)) (hb : ∀ a, σb (c₂ a) = c₄ (τb a)) (hc : ∀ a, σc (c₁ a) = c₃ (τc a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τd a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb τb hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τa ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τd hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc τc hc).pull j x) := by
  rw [pull_pull τ, pull_pull τ]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime]

instance tripleL (N : ℕ) : RingHomCompTriple (ACris.phi (K := ℂ_[l]) (p := l)) (Mid.phiA l N) (Mid.phiA l (N + 1)) :=
  ⟨by
    have e : Mid.phiA l (N + 1) = Mid.phiA l N * ACris.phi (K := ℂ_[l]) (p := l) := pow_succ _ _
    rw [e]; rfl⟩

instance tripleR (N : ℕ) : RingHomCompTriple (Mid.phiA l N) (ACris.phi (K := ℂ_[l]) (p := l)) (Mid.phiA l (N + 1)) :=
  ⟨by
    have e : Mid.phiA l (N + 1) = ACris.phi (K := ℂ_[l]) (p := l) * Mid.phiA l N := pow_succ' _ _
    rw [e]; rfl⟩

theorem phiP_phi (n N : ℕ) (x : (base l).Acr n) :
    Mid.phiP l n N ((base l).phi n x) = (base l).phi n (Mid.phiP l n N x) := by
  have e : Mid.phiP l n (N + 1) = Mid.phiP l n N * (base l).phi n := pow_succ _ _
  rw [← Mid.phiP_succ, e]; rfl

theorem nu_phi {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j) :
    Mid.nu r M n j hT (B.phiHc (B.schFn M.p) (okToOC l K) n j x) = phiM r M n j (Mid.nu r M n j hT x) := by
  exact cr_square_semi (Mid.phiA l (N + 1))
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl) ((base l).phi n) rfl
      ((base l).dpP_phi n) (B.phiPt (B.schFn M.p) (okToOC l K) n) fun _ y r =>
        ((congrArg y.1.1 (B.phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm)
    (Mid.mOut r M n hT)
    (Mid.mOut r M n hT)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).phi n) rfl ((base l).dpP_phi n) (phiPtT _ n _) fun _ y r =>
        ((congrArg y.1.1 (B.phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm)
    ((base l).phi_cris n) (Mid.phiP_cris n N) (Mid.phiP_cris n N) ((base l).phi_cris n)
    (fun x => (phiP_phi n N x)) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.NuPhi
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuFrobeniusCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_nu_frobenius_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j), Mid.nu r M n j hT (B.phiHc (B.schFn M.p) (okToOC l K) n j x) = phiM r M n j (Mid.nu r M n j hT x) := by
  first | exact @GlobalTheory.CompanionTheory.NuPhi.nu_phi | exact GlobalTheory.CompanionTheory.NuPhi.nu_phi | (intros; apply GlobalTheory.CompanionTheory.NuPhi.nu_phi <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuReductionCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuReductionCompat
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.CrysMid

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

noncomputable def trueRed (M : Model l K) (n : ℕ) :
    Mor (B.Lc (B.schFn M.p) (okToOC l K) true (n + 1)) (B.Lc (B.schFn M.p) (okToOC l K) true n) ((base l).red (Nat.le_succ n)) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n))
      (B.basePt _ _ (B.red_κb (okToOC l K) true (Nat.le_succ n))) fun _ _ _ => rfl

noncomputable def midRed (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n : ℕ) :
    Mor (Mid.Lm r M (n + 1)) (Mid.Lm r M n) ((base l).red (Nat.le_succ n)) :=
  B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true (n + 1)) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).red (Nat.le_succ n)) rfl (B.dd_red true _ (Nat.le_succ n))
      (B.basePt _ _ (red_κm r (Nat.le_succ n))) fun _ _ _ => rfl

theorem ptIn_val (F : B.Fn (OK l K)) {r : CrystallineSemistableComparison.Res l K} {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb (okToOC l K) true n)).obj B₀) (h : (l : B₀) = 0) :
    ((Mid.ptIn F n hT).app B₀ y).1.2 = F.Pt.map (CommRingCat.ofHom (Mid.frbN h N)) y.1.2 := rfl

theorem base_val {O : Type} [CommRing O] (F : B.Fn O) {k₁ k₂ : Type} [CommRing k₁] [CommRing k₂] {κ₁ : O →+* k₁} {κ₂ : O →+* k₂}
    (τ : k₁ →+* k₂) (h : τ.comp κ₁ = κ₂) (B₀ : CommRingCat.{0}) (y : (F.ptK κ₂).obj B₀) :
    ((B.basePt F τ h).app B₀ y).1.2 = y.1.2 := rfl

theorem ptIn_base (F : B.Fn (OK l K)) (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (F.ptK (B.κb (okToOC l K) true n)).obj B₀) :
    ((Mid.ptIn F (n + 1) hT).app B₀ ((B.basePt F _ (B.red_κb (okToOC l K) true (Nat.le_succ n))).app B₀ y)).1.2 =
      ((B.basePt F _ (red_κm r (Nat.le_succ n))).app B₀ ((Mid.ptIn F n hT).app B₀ y)).1.2 := by
  have h : (l : B₀) = 0 := Mid.l_zero y.1.1
  rw [ptIn_val F hT (n + 1) B₀ _ h, base_val, base_val, ptIn_val F hT n B₀ _ h]

theorem pt_sq (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n : ℕ) (B₀ : CommRingCat.{0})
    (y : (B.Lc (B.schFn M.p) (okToOC l K) true n).Pt.obj B₀) :
    ((Mid.mIn r M (n + 1) hT).pt.app B₀ ((trueRed M n).pt.app B₀ y)).1.2 =
      ((midRed r M n).pt.app B₀ ((Mid.mIn r M n hT).pt.app B₀ y)).1.2 :=
  ptIn_base (B.schFn M.p) r hT n B₀ y

theorem mid_square (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    (B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris n) (trueRed M n) (RingHom.id _) (B.red_cris _ (Nat.le_succ n))).pull j
      ((B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris (n + 1)) (Mid.mIn r M (n + 1) hT) (RingHom.id _) (Wc.idc _)).pull j t) =
    (B.omMor (c := (base l).cris n) (c' := (base l).cris n) (Mid.mIn r M n hT) (RingHom.id _) (Wc.idc _)).pull j
      ((B.omMor (c := (base l).cris (n + 1)) (c' := (base l).cris n) (midRed r M n) (RingHom.id _) (B.red_cris _ (Nat.le_succ n))).pull j t) :=
  cr_square (F₁ := B.schFn M.p) (F₂ := B.schFn M.p) (F₃ := B.schFn M.p) (F₄ := B.schFn M.p)
    (b₁ := B.bs l true (n + 1)) (b₂ := B.bs l true (n + 1)) (b₃ := B.bs l true n) (b₄ := B.bs l true n)
    (h₁ := rfl) (h₂ := rfl) (h₃ := rfl) (h₄ := rfl)
    (κ₁ := Mid.κm r (n + 1)) (κ₂ := B.κb (okToOC l K) true (n + 1)) (κ₃ := Mid.κm r n) (κ₄ := B.κb (okToOC l K) true n)
    (Λ := Acris l) (c₁ := (base l).cris (n + 1)) (c₂ := (base l).cris (n + 1)) (c₃ := (base l).cris n)
    (c₄ := (base l).cris n) (τ := RingHom.id _)
    (Mid.mIn r M (n + 1) hT) (trueRed M n) (midRed r M n) (Mid.mIn r M n hT)
    (Wc.idc _) (B.red_cris _ (Nat.le_succ n)) (B.red_cris _ (Nat.le_succ n)) (Wc.idc _) (fun x => (Wc.idc ((base l).red (Nat.le_succ n)) x).symm)
    (pt_sq r hT M n) j t

theorem mu_redHc (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j) :
    B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j (Mid.mu r M (n + 1) j hT t) = Mid.mu r M n j hT ((redT r M (Nat.le_succ n)).pull j t) :=
  mid_square r hT M n j t

end GlobalTheory.CompanionTheory.CrysMid
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerMuReductionCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_mu_reduction_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (n j : ℕ) (t : Mid.HM r M (n + 1) j), B.redHc (B.schFn M.p) (okToOC l K) true (Nat.le_succ n) j (Mid.mu r M (n + 1) j hT t) = Mid.mu r M n j hT ((redT r M (Nat.le_succ n)).pull j t) := by
  first | exact @GlobalTheory.CompanionTheory.CrysMid.mu_redHc | exact GlobalTheory.CompanionTheory.CrysMid.mu_redHc | (intros; apply GlobalTheory.CompanionTheory.CrysMid.mu_redHc <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuGaloisCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuGaloisCompat
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.NuGalSquare

theorem cr_square_semi {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1}
    {h₃ : b₃.t = 1} {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I}
    {κ₄ : O →+* b₄.R ⧸ b₄.I} {Λ : Type} [CommRing Λ] {c₁ : Λ →+* b₁.R} {c₂ : Λ →+* b₂.R} {c₃ : Λ →+* b₃.R} {c₄ : Λ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R} {τa τb τc τd : Λ →+* Λ}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τa a)) (hb : ∀ a, σb (c₂ a) = c₄ (τb a)) (hc : ∀ a, σc (c₁ a) = c₃ (τc a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τd a)) (hτ : τb.comp τa = τd.comp τc) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb τb hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τa ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τd hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc τc hc).pull j x) := by
  haveI t₁ : RingHomCompTriple τa τb (τb.comp τa) := ⟨rfl⟩
  haveI t₂ : RingHomCompTriple τc τd (τb.comp τa) := ⟨hτ.symm⟩
  rw [pull_pull (τb.comp τa), pull_pull (τb.comp τa)]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem commute_phi_gal (σ : Gal(PadicAlgCl l/K)) : Commute (ACris.phi (K := ℂ_[l]) (p := l)) (ACris.galCris σ) :=
  RingHom.ext fun a => ACris.phi_gal_smul σ a

theorem phiA_comp_gal (σ : Gal(PadicAlgCl l/K)) (N : ℕ) :
    (Mid.phiA l N).comp (ACris.galCris σ) = (ACris.galCris σ).comp (Mid.phiA l N) :=
  ((commute_phi_gal σ).pow_left N).eq

theorem commute_phi_galBase (σ : Gal(PadicAlgCl l/K)) (n : ℕ) : Commute ((base l).phi n) (galBase σ n) :=
  RingHom.ext fun r => by
    obtain ⟨a, rfl⟩ := (RL.base_acr (base l) isBase_base).2 n |>.1 r
    change (base l).phi n (galBase σ n ((base l).cris n a)) = galBase σ n ((base l).phi n ((base l).cris n a))
    rw [galBase_cris, (base l).phi_cris, (base l).phi_cris, galBase_cris]
    exact congrArg _ (ACris.phi_gal_smul σ a)

theorem phiP_galBase (σ : Gal(PadicAlgCl l/K)) (n N : ℕ) (x : (base l).Acr n) :
    Mid.phiP l n N (galBase σ n x) = galBase σ n (Mid.phiP l n N x) :=
  RingHom.congr_fun ((commute_phi_galBase σ n).pow_left N).eq x

theorem nu_gal : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j), Mid.nu r M n j hT (B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j x) = galM r M σ hσ n j (Mid.nu r M n j hT x) := by
  intro l _ K r N hT M σ hσ n j x
  exact cr_square_semi
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (B.gal_κb (okToOC l K) σ (galOC_okToOC σ) true n)) fun _ _ _ => rfl)
    (Mid.mOut r M n hT) (Mid.mOut r M n hT)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (galBase σ n) rfl (B.dd_gal true σ n) (B.basePt _ _ (gal_κm r σ hσ n)) fun _ _ _ => rfl)
    (galBase_cris σ n) (Mid.phiP_cris n N) (Mid.phiP_cris n N) (galBase_cris σ n)
    (phiA_comp_gal σ N) (phiP_galBase σ n N) (fun _ _ => rfl) j x

end GlobalTheory.CompanionTheory.NuGalSquare
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TeichmullerNuGaloisCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.teichmuller_nu_galois_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) {N : ℕ} (hT : Mid.TeichmullerCongruence r N) (M : Model l K) (σ : Gal(PadicAlgCl l/K)) (hσ : ∀ w, ACris.galCris σ (r.w w) = r.w w) (n j : ℕ) (x : B.Hc (B.schFn M.p) (okToOC l K) true n j), Mid.nu r M n j hT (B.galHc (B.schFn M.p) (okToOC l K) σ (galOC_okToOC σ) true n j x) = galM r M σ hσ n j (Mid.nu r M n j hT x) := by
  first | exact @GlobalTheory.CompanionTheory.NuGalSquare.nu_gal | exact GlobalTheory.CompanionTheory.NuGalSquare.nu_gal | (intros; apply GlobalTheory.CompanionTheory.NuGalSquare.nu_gal <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonFrobeniusCompat
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonFrobeniusCompat
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.BaseChangeFrob

theorem cr_square_gen {O : Type} [CommRing O] {F₁ F₂ F₃ F₄ : B.Fn O} {b₁ b₂ b₃ b₄ : Base} {h₁ : b₁.t = 1} {h₂ : b₂.t = 1}
    {h₃ : b₃.t = 1} {h₄ : b₄.t = 1} {κ₁ : O →+* b₁.R ⧸ b₁.I} {κ₂ : O →+* b₂.R ⧸ b₂.I} {κ₃ : O →+* b₃.R ⧸ b₃.I}
    {κ₄ : O →+* b₄.R ⧸ b₄.I} {Λ₁ Λ₂ Λ₃ Λ₄ : Type} [CommRing Λ₁] [CommRing Λ₂] [CommRing Λ₃] [CommRing Λ₄]
    {c₁ : Λ₁ →+* b₁.R} {c₂ : Λ₂ →+* b₂.R} {c₃ : Λ₃ →+* b₃.R} {c₄ : Λ₄ →+* b₄.R}
    {σa : b₁.R →+* b₂.R} {σb : b₂.R →+* b₄.R} {σc : b₁.R →+* b₃.R} {σd : b₃.R →+* b₄.R}
    {τa : Λ₁ →+* Λ₂} {τb : Λ₂ →+* Λ₄} {τc : Λ₁ →+* Λ₃} {τd : Λ₃ →+* Λ₄}
    (ma : Mor (F₁.cr b₁ h₁ κ₁) (F₂.cr b₂ h₂ κ₂) σa) (mb : Mor (F₂.cr b₂ h₂ κ₂) (F₄.cr b₄ h₄ κ₄) σb)
    (mc : Mor (F₁.cr b₁ h₁ κ₁) (F₃.cr b₃ h₃ κ₃) σc) (md : Mor (F₃.cr b₃ h₃ κ₃) (F₄.cr b₄ h₄ κ₄) σd)
    (ha : ∀ a, σa (c₁ a) = c₂ (τa a)) (hb : ∀ a, σb (c₂ a) = c₄ (τb a)) (hc : ∀ a, σc (c₁ a) = c₃ (τc a))
    (hd : ∀ a, σd (c₃ a) = c₄ (τd a)) (hτ : ∀ a, τb (τa a) = τd (τc a)) (hσ : ∀ r, σb (σa r) = σd (σc r))
    (hpt : ∀ (B₀ : CommRingCat.{0}) (y : (F₄.cr b₄ h₄ κ₄).Pt.obj B₀),
      (ma.pt.app B₀ (mb.pt.app B₀ y)).1.2 = (mc.pt.app B₀ (md.pt.app B₀ y)).1.2)
    (j : ℕ) (x : CH.H (B.OM (F₁.cr b₁ h₁ κ₁) c₁) j) :
    (B.omMor (c := c₂) (c' := c₄) mb τb hb).pull j ((B.omMor (c := c₁) (c' := c₂) ma τa ha).pull j x) =
      (B.omMor (c := c₃) (c' := c₄) md τd hd).pull j ((B.omMor (c := c₁) (c' := c₃) mc τc hc).pull j x) := by
  haveI i₁ : RingHomCompTriple τa τb (τb.comp τa) := ⟨rfl⟩
  haveI i₂ : RingHomCompTriple τc τd (τb.comp τa) := ⟨(RingHom.ext hτ).symm⟩
  rw [pull_pull (τb.comp τa), pull_pull (τb.comp τa)]
  exact cr_pull_eq _ _ (fun T => crHom (T := ma.obj (mb.obj T)) (T' := mc.obj (md.obj T)) (RingHom.id T.B)
    (fun r => congrArg T.i (hσ r)) (DPMorphism.id T.δ).isDPMorphism fun h => (pt_id _ h _).trans (hpt _ _))
    (fun _ _ => rfl) (fun _ _ => rfl) j x

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem w_frobenius (r : CrystallineSemistableComparison.Res l K) (w : WittVector l r.k) :
    ACris.phi (K := ℂ_[l]) (p := l) (r.w w) = r.w (WittVector.frobenius w) := by
  change ACris.phi (K := ℂ_[l]) (p := l) (algebraMap (Ainf l) (Acris l) (WittVector.map r.s w)) =
    algebraMap (Ainf l) (Acris l) (WittVector.map r.s (WittVector.frobenius w))
  rw [ACris.phi_algebraMap]
  congr 1
  change WittVector.frobenius (WittVector.map r.s w) = _
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.frobenius_eq_map_frobenius]
  ext n
  simp only [WittVector.map_coeff, frobenius_def, map_pow]

theorem wn_frob (r : CrystallineSemistableComparison.Res l K) (n : ℕ) (x : Wc.Wm l r.k n) :
    (base l).phi n (Mid.wn r n x) = Mid.wn r n (Wc.frob l r.k n x) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Wc.frob_mk', Mid.wn_mk, Mid.wn_mk, (base l).phi_cris, w_frobenius]

theorem phiM_bW {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ)
    (y : (HSW r M j).M n) : phiM r M n j (bW r M n j y) = bW r M n j ((Wc.phiS l (B.schFn M.p) r.ρ j).f n y) := by
  refine cr_square_gen (F₁ := B.schFn M.p) (F₂ := B.schFn M.p) (F₃ := B.schFn M.p) (F₄ := B.schFn M.p)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := B.bs l true n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      ((base l).phi n) rfl ((base l).dpP_phi n) (phiPtT _ n _) fun _ y r =>
        ((congrArg y.1.1 (B.phi_mk (base l) n r)).trans (map_pow y.1.1 _ l)).symm)
    (Wc.phiM l (B.schFn M.p) r.ρ n)
    (B.crMor (F := B.schFn M.p) (F' := B.schFn M.p) (b := Wc.bs l r.k n) (b' := B.bs l true n) (ht := rfl) (ht' := rfl)
      (Mid.wn r n) rfl (dp_wn r n) (B.basePt _ (Ideal.quotientMap _ (Mid.wn r n) (Mid.im_le r n)) rfl) fun _ _ _ => rfl)
    (Mid.wn_mk r n) ((base l).phi_cris n) (Wc.frob_mk' l r.k n) (Mid.wn_mk r n) (w_frobenius r) (wn_frob r n) ?_ j y
  intro B₀ y
  rfl

end GlobalTheory.CompanionTheory.BaseChangeFrob
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WittComparisonFrobeniusCompatStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry TensorProduct GroundTheory.PAdicHodge GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison.PAlg CrystallineSemistableComparison CrystallineSemistableComparison.Pb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_comparison_frobenius_compat : ∀ {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)} (r : CrystallineSemistableComparison.Res l K) (M : Model l K) (n j : ℕ) (y : (HSW r M j).M n), phiM r M n j (bW r M n j y) = bW r M n j ((Wc.phiS l (B.schFn M.p) r.ρ j).f n y) := by
  first | exact @GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW | exact GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW | (intros; apply GlobalTheory.CompanionTheory.BaseChangeFrob.phiM_bW <;> assumption)
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZetaSpecialValueDenominatorBound
section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZetaSpecialValueDenominatorBound
set_option autoImplicit false
noncomputable section
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel

theorem eq_at_neg_of_eq_right (k p : ℕ) (hp : p < k) (T G : ℂ → ℂ)
    (hT : DifferentiableOn ℂ T {1}ᶜ) (hG : DifferentiableOn ℂ G {s | -(k : ℝ) < s.re})
    (h : ∀ s : ℂ, 1 < s.re → T s = G s) : T (-(p : ℂ)) = G (-(p : ℂ)) := by
  have hk : (0 : ℝ) < k := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le p) hp)
  have hpk : (p : ℝ) < k := by exact_mod_cast hp
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  set C₁ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | 0 < s.im} with hC₁
  set C₂ : Set ℂ := {s | -(k : ℝ) < s.re} ∩ {s | s.re < 1} with hC₂
  have hO₁ : IsOpen C₁ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  have hO₂ : IsOpen C₂ :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hV₁ : Convex ℝ C₁ := (convex_halfSpace_re_gt _).inter (convex_halfSpace_im_gt _)
  have hV₂ : Convex ℝ C₂ := (convex_halfSpace_re_gt _).inter (convex_halfSpace_re_lt _)
  have hs₁ : C₁ ⊆ {1}ᶜ := by
    intro s hs h1
    have : s = 1 := h1
    have h2 := hs.2
    simp [this] at h2
  have hs₂ : C₂ ⊆ {1}ᶜ := by
    intro s hs h1
    have : s = 1 := h1
    have h2 := hs.2
    simp [this] at h2
  have hAT₁ : AnalyticOnNhd ℂ T C₁ := (hT.mono hs₁).analyticOnNhd hO₁
  have hAG₁ : AnalyticOnNhd ℂ G C₁ :=
    (hG.mono (show C₁ ⊆ {s | -(k : ℝ) < s.re} from fun _ hs => hs.1)).analyticOnNhd hO₁
  have hAT₂ : AnalyticOnNhd ℂ T C₂ := (hT.mono hs₂).analyticOnNhd hO₂
  have hAG₂ : AnalyticOnNhd ℂ G C₂ :=
    (hG.mono (show C₂ ⊆ {s | -(k : ℝ) < s.re} from fun _ hs => hs.1)).analyticOnNhd hO₂
  have hz₁ : (2 + Complex.I : ℂ) ∈ C₁ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hev₁ : T =ᶠ[nhds (2 + Complex.I : ℂ)] G := by
    have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [hopen.mem_nhds (by simp : (2 + Complex.I : ℂ) ∈ {s : ℂ | 1 < s.re})] with s hs
    exact h s hs
  have hE₁ : Set.EqOn T G C₁ :=
    hAT₁.eqOn_of_preconnected_of_eventuallyEq hAG₁ hV₁.isPreconnected hz₁ hev₁
  have hz₂ : (Complex.I : ℂ) ∈ C₂ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hz₂' : (Complex.I : ℂ) ∈ C₁ := by
    refine ⟨?_, ?_⟩ <;> simp <;> linarith
  have hev₂ : T =ᶠ[nhds (Complex.I : ℂ)] G := by
    filter_upwards [hO₁.mem_nhds hz₂'] with s hs
    exact hE₁ hs
  have hE₂ : Set.EqOn T G C₂ :=
    hAT₂.eqOn_of_preconnected_of_eventuallyEq hAG₂ hV₂.isPreconnected hz₂ hev₂
  refine hE₂ ?_
  refine ⟨?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]
    linarith
  · simp only [Set.mem_setOf_eq, Complex.neg_re, Complex.natCast_re]
    linarith

theorem abelValue_mem_zInv (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ)
    (w : (Fin r → ℕ) → ℚ) (hr : r ≤ Fintype.card ι) (hl : 0 < l) (ha : ∀ j i, 0 < a j i)
    (hb : ∀ j, 0 < b j) (hw : GoodWeight l w) (hz : ∀ m, ∃ z : ℤ, w m = z) (T : ℂ → ℂ)
    (hT : DifferentiableOn ℂ T {1}ᶜ)
    (hS : ∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) (p : ℕ)
    (hp : ∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) :
    ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  obtain ⟨Q, _, cs, u, K, hu, hc, hK, hid⟩ :=
    GlobalTheory.T.weighted_sum_decomposition_denominators r l (Fintype.card ι * (p + 1) + 2) w hl hw hz
  set G : ℂ → ℂ := fun s => ∑ q, ∑' m, (u q m : ℂ) * DL (cs q) (coneTerm a b s) m with hGdef
  have hG : DifferentiableOn ℂ G {s | -((p + 1 : ℕ) : ℝ) < s.re} := by
    refine DifferentiableOn.fun_sum fun q _ => ?_
    exact GlobalTheory.T.cone_series_differentiable_left_strip ι r a b ha hb (p + 1) _ (cs q) (u q) le_rfl (hu q) (hc q)
  have hTG : ∀ s : ℂ, 1 < s.re → T s = G s := by
    intro s hs
    rw [← (hS s hs).tsum_eq]
    exact hid _ (GlobalTheory.T.cone_series_summable_right_half_plane ι r a b hr ha hb s hs)
  have hval := eq_at_neg_of_eq_right (p + 1) p (Nat.lt_succ_self p) T G hT hG hTG
  choose ρ ζ hρ hζ using fun q => GlobalTheory.T.cone_series_special_value_rational ι r a b (u q) (cs q) p K l hl (hK q) hp
  refine ⟨∑ q, ρ q, K, ∑ q, ζ q, ?_, ?_⟩
  · rw [hval, hGdef]
    push_cast
    exact Finset.sum_congr rfl fun q _ => hρ q
  · rw [Finset.mul_sum]
    push_cast
    exact Finset.sum_congr rfl fun q _ => hζ q

theorem abelValue_mem_zInv' : ∀ (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ), r ≤ Fintype.card ι → 0 < l → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) → ∀ p : ℕ, (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  intro ι _ r l a b w hr hl ha hb hw hz T hT hS p hp
  exact abelValue_mem_zInv ι r l a b w hr hl ha hb hw hz T hT hS p hp

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
end
end

section -- merged from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeZetaSpecialValueDenominatorBoundStatement
open NumberField Formalism.MainNotions.ShortIntervalPrimes GlobalTheory.RayZeta GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cone_zeta_special_value_denominator_bound : ∀ (ι : Type) [Fintype ι] (r l : ℕ) (a : ι → Fin r → ℝ) (b : ι → ℝ) (w : (Fin r → ℕ) → ℚ), r ≤ Fintype.card ι → 0 < l → (∀ j i, 0 < a j i) → (∀ j, 0 < b j) → GoodWeight l w → (∀ m, ∃ z : ℤ, w m = z) → ∀ T : ℂ → ℂ, DifferentiableOn ℂ T {1}ᶜ → (∀ s : ℂ, 1 < s.re → HasSum (fun m => (w m : ℂ) * coneTerm a b s m) (T s)) → ∀ p : ℕ, (∀ m : Fin r → ℕ, ∃ z : ℤ, ∏ j, (b j + ∑ i, a j i * (m i : ℝ)) ^ p = (z : ℝ)) → ∃ (q : ℚ) (K : ℕ) (z : ℤ), T (-(p : ℂ)) = (q : ℂ) ∧ (l : ℚ) ^ K * q = z := by
  first | exact @GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelValue_mem_zInv' | exact GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelValue_mem_zInv' | (intros; apply GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Abel.abelValue_mem_zInv' <;> assumption)
end
end
