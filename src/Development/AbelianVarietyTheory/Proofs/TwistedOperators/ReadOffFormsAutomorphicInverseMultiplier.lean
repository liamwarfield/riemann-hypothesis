module

public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsPureTensors
public import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsOrthonormalisation

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsProperProjection
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.StabProper

private lemma sum_mul_conj_eq_conj_dotProduct {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) :
    ∑ a, ∑ b, x a * conj (G b a) * conj (y b) = conj (y ⬝ᵥ (G *ᵥ star x)) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [dotProduct, mulVec, map_sum, map_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [Pi.star_apply, Complex.star_def, Complex.conj_conj]
  ring

theorem unitary_iff_form {n : ℕ} (G g : Matrix (Fin n) (Fin n) ℂ) :
    gᴴ * G * g = G ↔ ∀ v w : Fin n → ℂ,
      ∑ a, ∑ b, (g.map conj *ᵥ v) a * conj (G b a) * conj ((g.map conj *ᵥ w) b) =
        ∑ a, ∑ b, v a * conj (G b a) * conj (w b) := by
  have h1 : ∀ v : Fin n → ℂ, star (g.map conj *ᵥ v) = g *ᵥ star v := by
    intro v; ext i
    simp [mulVec, dotProduct]
  have key : ∀ v w : Fin n → ℂ, ∑ a, ∑ b, (g.map conj *ᵥ v) a * conj (G b a) * conj ((g.map conj *ᵥ w) b) =
      conj (w ⬝ᵥ ((gᴴ * G * g) *ᵥ star v)) := by
    intro v w
    rw [sum_mul_conj_eq_conj_dotProduct, h1]
    congr 1
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec w gᴴ]
    congr 1
    ext j
    simp [vecMul, mulVec, dotProduct, conjTranspose_apply, mul_comm]
  constructor
  · intro h v w
    rw [key, h, sum_mul_conj_eq_conj_dotProduct]
  · intro h
    ext i j
    have hs : ∀ k : Fin n, star (Pi.single k 1 : Fin n → ℂ) = Pi.single k 1 := by
      intro k; ext l; by_cases hl : l = k <;> simp [hl]
    have := h (Pi.single j 1) (Pi.single i 1)
    rw [key, sum_mul_conj_eq_conj_dotProduct, hs] at this
    have := (starRingEnd ℂ).injective this
    simpa [mulVec, dotProduct, Pi.single_apply] using this

variable {D : D7}

theorem compAt_eq (θ : InfFam D) (τ : D.what₂.Tau) {m n : ℕ} (w : Mx D m n) :
    compAt θ τ w = w.map ((θ τ).comp (infPart D)) := rfl

theorem hermC_eq {S T : HSp D} (C : Ctx S T) (σ : C.X.Ψ) (v w : Fin T.rank → ℂ) :
    hermC σ.1 C.X.Gm v w = ∑ a, ∑ b, v a * conj (gramAt D T (C.m.e.symm σ) b a) * conj (w b) := by
  unfold hermC gramAt
  have he := C.m.e_emb (C.m.e.symm σ)
  rw [Equiv.apply_symm_apply] at he
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [C.m.gT, he]
  simp [NumberField.ComplexEmbedding.conjugate_coe_eq]

end GlobalTheory.StabProper

end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalLevelPointFinitePartMemLevelGroup
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalLevelPointFinitePartMemLevelGroup
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.LevMove.Rat

section Core

open Formalism.MainNotions.StandardLattice (latHat intAf)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem mem_of_loc (L : Submodule (𝓞 E) (Fin n → E)) (𝔪 : Ideal (𝓞 E)) (h𝔪 : 𝔪 ≠ ⊥)
    {x : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E} (hx : x ∈ latHat F E (L : Set (Fin n → E)))
    (hloc : ∀ v : HeightOneSpectrum (𝓞 F), 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal →
      ∀ α : FiniteAdeleRing (𝓞 F) F, evalV F v α = 1 → (∀ w, w ≠ v → evalV F w α = 0) →
        (α ⊗ₜ[F] (1 : E)) • x ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E))) :
    x ∈ latHat F E ((𝔪 • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  classical
  set N := Ideal.absNorm 𝔪 with hNdef
  have hN0 : N ≠ 0 := fun h => h𝔪 (Ideal.absNorm_eq_zero_iff.1 h)
  have hNE : ((N : 𝓞 E)) ∈ 𝔪 := Ideal.absNorm_mem 𝔪
  set c₁ : 𝓞 F := (N : 𝓞 F) with hc₁
  have hc₁0 : c₁ ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hc₁m : algebraMap (𝓞 F) (𝓞 E) c₁ ∈ 𝔪 := by rw [hc₁, map_natCast]; exact hNE
  have hfin : {v : HeightOneSpectrum (𝓞 F) | v.asIdeal ∣ Ideal.span {c₁}}.Finite :=
    Ideal.finite_factors (by rwa [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot])
  set P := hfin.toFinset with hP
  have hmemP : ∀ v, v ∈ P ↔ c₁ ∈ v.asIdeal := fun v => by
    rw [hP, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  choose ind hind1 hind0 using (exists_ind (F := F))
  set e₁ : FiniteAdeleRing (𝓞 F) F := ∑ v ∈ P, ind v with he₁
  have hev : ∀ w, evalV F w e₁ = if w ∈ P then 1 else 0 := fun w => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [he₁, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single w (fun b _ hb => hind0 b w (Ne.symm hb)) (fun h => absurd hw h), hind1]
    · exact Finset.sum_eq_zero fun b hb => hind0 b w (fun h => hw (h ▸ hb))
  have hsplit : x = ((1 - e₁) ⊗ₜ[F] (1 : E)) • x + ∑ v ∈ P, (ind v ⊗ₜ[F] (1 : E)) • x := by
    rw [← Finset.sum_smul, ← TensorProduct.sum_tmul, ← he₁, ← add_smul, ← TensorProduct.add_tmul, sub_add_cancel,
      Algebra.TensorProduct.one_def.symm, one_smul]
  rw [hsplit]
  refine add_mem ?_ (sum_mem fun v hv => ?_)
  · refine vanish_smul_mem L 𝔪 hc₁0 hc₁m (fun w => ?_) (fun w hw => ?_) hx
    · rw [map_sub, map_one, hev]; split_ifs
      · rw [sub_self]; exact zero_mem _
      · rw [sub_zero]; exact one_mem _
    · rw [map_sub, map_one, hev, if_pos ((hmemP w).2 hw), sub_self]
  · by_cases hI : 𝔪.comap (algebraMap (𝓞 F) (𝓞 E)) ≤ v.asIdeal
    · exact hloc v hI (ind v) (hind1 v) (hind0 v)
    · obtain ⟨c, hc, hcv⟩ := SetLike.not_le_iff_exists.1 hI
      have hc0 : c ≠ 0 := fun h => hcv (h ▸ zero_mem _)
      refine vanish_smul_mem L 𝔪 hc0 hc (ind_int (hind1 v) (hind0 v)) (fun w hw => hind0 v w ?_) hx
      rintro rfl; exact hcv hw

end Core

variable {D : D7}

theorem mov_comp {k : ℕ} {m m₂ : Matrix (Fin k) (Fin k) (AfE D)} {L L' L'' : Lt D.host.E k}
    (h : IsMov m L L') (h₂ : IsMov m₂ L' L'') : IsMov (m₂ * m) L L'' := by
  intro u
  rw [h₂ u]
  constructor
  · rintro ⟨u₁, hu₁, rfl⟩
    obtain ⟨u₀, hu₀, rfl⟩ := (h u₁).1 hu₁
    exact ⟨u₀, hu₀, by rw [Matrix.mulVec_mulVec]⟩
  · rintro ⟨u₀, hu₀, rfl⟩
    exact ⟨m *ᵥ u₀, (h _).2 ⟨u₀, hu₀, rfl⟩, by rw [Matrix.mulVec_mulVec]⟩

theorem smul_sandwich {R : Type} [CommRing R] {k : ℕ} (P : R) (A A' G B : Matrix (Fin k) (Fin k) R)
    (hA : P • A = P • 1) (hB : P • B = P • 1) (e : A * A' = 1) : P • (A' * G * B) = P • G := by
  have h' : P • A' = P • 1 := by
    calc P • A' = (P • 1) * A' := by rw [Matrix.smul_mul, one_mul]
      _ = (P • A) * A' := by rw [hA]
      _ = P • 1 := by rw [Matrix.smul_mul, e]
  rw [← Matrix.smul_mul, ← Matrix.smul_mul, h', Matrix.smul_mul, one_mul, Matrix.smul_mul, ← Matrix.mul_smul, hB,
    Matrix.mul_smul, mul_one]

theorem map_mulVec_toAf {k : ℕ} (M : Matrix (Fin k) (Fin k) D.host.E) (u : Fin k → D.host.E) :
    (M.map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x) *ᵥ toAf u = toAf (M *ᵥ u) := by
  funext i
  simp only [Matrix.mulVec, dotProduct, toAf, Matrix.map_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one,
    TensorProduct.tmul_sum]

theorem toAf_smul {k : ℕ} (c : 𝓞 D.host.E) (u : Fin k → D.host.E) :
    toAf (c • u) = ((1 : Af D.host.F) ⊗ₜ[D.host.F] (c : D.host.E) : AfE D) • toAf u := by
  funext i
  simp only [toAf, Pi.smul_apply, smul_eq_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  rfl

theorem smul_step {R : Type} [CommRing R] {k : ℕ} (P : R) (K G : Matrix (Fin k) (Fin k) R) (u w : Fin k → R)
    (h : P • K = P • G) : P • (K *ᵥ u - w) = P • (G *ᵥ u - w) := by
  rw [smul_sub, smul_sub, ← Matrix.smul_mulVec, h, Matrix.smul_mulVec]

theorem toAf_sub {k : ℕ} (u w : Fin k → D.host.E) : (toAf (u - w) : Fin k → AfE D) = toAf u - toAf w := by
  funext i
  simp only [toAf, Pi.sub_apply, TensorProduct.tmul_sub]

theorem toAf_mem {k : ℕ} {L : Lt D.host.E k} {u : Fin k → D.host.E} (hu : u ∈ L) : toAf u ∈ hatV L :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, u, hu, rfl⟩

end GlobalTheory.Ker.LevMove.Rat


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Ker.LevMove.levK_of_rat_moves : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (γ : GL (Fin T.rank) D.host.E) (κ : Lv.J), Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) κ → ∀ (a f g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), a ∈ GinfC T → f ∈ GfC T → IsRatOf T γ (a * f) → g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤ → (mapL γ L).FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ (mapL γ L) → C.LevK Lv (g₂⁻¹ * f * g₁) κ := by
  intro D S T C Lv γ κ hred a f g₁ g₂ L ha hf hrat h1 h2 t1 t2 hLfg hLs hMfg m1 m2
  set G : Matrix (Fin T.rank) (Fin T.rank) (AfE D) :=
    (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E).map fun x => (1 : Af D.host.F) ⊗ₜ[D.host.F] x with hGdef
  have hfa : fmt T a = 1 := (((GlobalTheory.Ker.Grp.rational_points_and_parts D S T C).2.2.2 T).2.2.2.1 a ha).1
  have hff : fmt T f = G := by
    have e : fmt T (a * f) = G := by
      rw [fmt, hrat, Matrix.map_map]; rfl
    rw [← e, GlobalTheory.Ker.LevMove.fmt_mul', hfa, one_mul]
  have hfull : C.X.Λ.FG ∧ Submodule.span D.host.E (C.X.Λ : Set (Fin T.rank → D.host.E)) = ⊤ :=
    ⟨C.X.Λ_fg, C.X.Λ_span⟩
  have e1 : fmt T g₁ * fmt T g₁⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  have e2 : fmt T g₂ * fmt T g₂⁻¹ = 1 := by
    rw [← GlobalTheory.Ker.LevMove.fmt_mul', mul_inv_cancel, GlobalTheory.Ker.LevMove.fmt_one']
  obtain ⟨hto, -, -, lawsΛ⟩ := GlobalTheory.Ker.isMov_laws D T.rank C.X.Λ hfull
  obtain ⟨-, -, hG, -⟩ := GlobalTheory.Ker.isMov_laws D T.rank L ⟨hLfg, hLs⟩
  obtain ⟨-, hinv2, -, -, -⟩ := (lawsΛ _ _ e2).2 (mapL γ L) hMfg m2
  have hk : IsMov (fmt T (g₂⁻¹ * f * g₁)) C.X.Λ C.X.Λ := by
    rw [GlobalTheory.Ker.LevMove.fmt_mul', GlobalTheory.Ker.LevMove.fmt_mul', hff]
    exact GlobalTheory.Ker.LevMove.Rat.mov_comp m1 (GlobalTheory.Ker.LevMove.Rat.mov_comp (hG γ) hinv2)
  obtain ⟨κ', hκ', hcong⟩ := hred
  refine ⟨mul_mem (mul_mem (inv_mem h2) hf) h1, hk, κ', hκ', fun i => ?_⟩
  have hb : toAf (Lv.β i) ∈ hatV C.X.Λ := GlobalTheory.Ker.LevMove.Rat.toAf_mem (Lv.β_mem i)
  have hw : toAf (∑ j, κ' j i • Lv.β j) ∈ hatV C.X.Λ :=
    GlobalTheory.Ker.LevMove.Rat.toAf_mem (sum_mem fun j _ => Submodule.smul_mem _ _ (Lv.β_mem j))
  refine GlobalTheory.Ker.LevMove.Rat.mem_of_loc (F := D.host.F) C.X.Λ Lv.𝔪 Lv.ne_bot
    (sub_mem ((hk _).2 ⟨_, hb, rfl⟩) hw) ?_
  intro v hv α a1 a0
  have P1 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t1 hv a1 a0
  have P2 := GlobalTheory.Ker.LevMove.smul_fmt_sub_one t2 hv a1 a0
  set P : AfE D := α ⊗ₜ[D.host.F] (1 : D.host.E) with hPdef
  have hPint : α ∈ Formalism.MainNotions.StandardLattice.intAf D.host.F := GlobalTheory.Ker.LevMove.ind_int a1 a0
  have q1 : P • fmt T g₁ = P • 1 := by rw [smul_sub] at P1; exact sub_eq_zero.1 P1
  have q2 : P • fmt T g₂ = P • 1 := by rw [smul_sub] at P2; exact sub_eq_zero.1 P2
  have qk : P • fmt T (g₂⁻¹ * f * g₁) = P • G := by
    rw [GlobalTheory.Ker.LevMove.fmt_mul', GlobalTheory.Ker.LevMove.fmt_mul', hff]
    exact GlobalTheory.Ker.LevMove.Rat.smul_sandwich P _ _ _ _ q2 q1 e2
  obtain ⟨d, hd⟩ : ∃ d : Fin T.rank → D.host.E, d = (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i -
    ∑ j, κ' j i • Lv.β j := ⟨_, rfl⟩
  have hx : P • (fmt T (g₂⁻¹ * f * g₁) *ᵥ toAf (Lv.β i) - toAf (∑ j, κ' j i • Lv.β j)) = P • toAf d := by
    rw [GlobalTheory.Ker.LevMove.Rat.smul_step P _ _ _ _ qk, GlobalTheory.Ker.LevMove.Rat.map_mulVec_toAf,
      ← GlobalTheory.Ker.LevMove.Rat.toAf_sub, hd]
  have hPd : P • toAf d ∈ hatV C.X.Λ := by
    rw [← hx]
    exact GlobalTheory.Ker.LevMove.int_smul_mem C.X.Λ hPint (sub_mem ((hk _).2 ⟨_, hb, rfl⟩) hw)
  change P • _ ∈ hatV (Lv.𝔪 • C.X.Λ)
  rw [hx]
  obtain ⟨s, hs, hsd⟩ := hcong i
  rw [← hd] at hsd
  obtain ⟨u, hu, m, hm, hum⟩ := Ideal.isCoprime_iff_exists.1 hs
  obtain ⟨t, rfl⟩ := Ideal.mem_span_singleton'.1 hu
  have hsplit : P • toAf d = P • toAf ((t * s) • d) +
      ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((m : 𝓞 D.host.E) : D.host.E) : AfE D) • (P • toAf d) := by
    have hum' : ((t * s : 𝓞 D.host.E) : D.host.E) + ((m : 𝓞 D.host.E) : D.host.E) = 1 := by
      have := congrArg (algebraMap (𝓞 D.host.E) D.host.E) hum
      simpa using this
    rw [GlobalTheory.Ker.LevMove.Rat.toAf_smul, smul_comm P, ← add_smul, ← TensorProduct.tmul_add, hum',
      Algebra.TensorProduct.one_def.symm, one_smul]
  rw [hsplit]
  refine add_mem ?_ (GlobalTheory.Ker.LevMove.ideal_smul_mem C.X.Λ Lv.𝔪 hm hPd)
  refine GlobalTheory.Ker.LevMove.int_smul_mem _ hPint (GlobalTheory.Ker.LevMove.Rat.toAf_mem ?_)
  rw [mul_smul]
  exact Submodule.smul_mem _ t hsd
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalLevelPointFinitePartMemLevelGroupStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rationalLevelPoint_finitePart_mem_levelGroup : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : SW.Level C.X) (γ : GL (Fin T.rank) D.host.E) (κ : Lv.J), Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) κ → ∀ (a f g₁ g₂ : GA D T) (L : Lt D.host.E T.rank), a ∈ GinfC T → f ∈ GfC T → IsRatOf T γ (a * f) → g₁ ∈ GfC T → g₂ ∈ GfC T → TrivAt T (C.under Lv) g₁ → TrivAt T (C.under Lv) g₂ → L.FG → Submodule.span D.host.E (L : Set (Fin T.rank → D.host.E)) = ⊤ → (mapL γ L).FG → IsMov (fmt T g₁) C.X.Λ L → IsMov (fmt T g₂) C.X.Λ (mapL γ L) → C.LevK Lv (g₂⁻¹ * f * g₁) κ := by
  first | exact @GlobalTheory.Ker.LevMove.levK_of_rat_moves | exact GlobalTheory.Ker.LevMove.levK_of_rat_moves | (intros; apply GlobalTheory.Ker.LevMove.levK_of_rat_moves <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DomainFrameEqRealTranslateMulBorel
section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DomainFrameEqRealTranslateMulBorel
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FrameDecomp

theorem hermC_mulVec {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r → ℂ) :
    hermC τ G (x *ᵥ a) (x *ᵥ b) = ∑ i, ∑ j, a i * FD.gram τ G x i j * conj (b j) := by
  unfold hermC
  calc ∑ p, ∑ q, (x *ᵥ a) p * τ (G p q) * conj ((x *ᵥ b) q)
      = ∑ p, ∑ q, ∑ i, ∑ j, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) := by
        refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
        rw [Finset.sum_mul, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ p, ∑ i, ∑ q, ∑ j, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_comm
    _ = ∑ p, ∑ i, ∑ j, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ p, ∑ j, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) := Finset.sum_comm
    _ = ∑ i, ∑ j, ∑ p, ∑ q, a i * (x p i * τ (G p q) * conj (x q j)) * conj (b j) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ i, ∑ j, a i * FD.gram τ G x i j * conj (b j) := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
        simp only [FD.gram, Matrix.of_apply, FD.col, hermC, Finset.mul_sum, Finset.sum_mul]

theorem isometry_of_gram_eq {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (x y : Matrix (Fin r) (Fin r) ℂ) (hy : y.det ≠ 0) (h : FD.gram τ G x = FD.gram τ G y) (v w : Fin r → ℂ) :
    hermC τ G ((x * y⁻¹) *ᵥ v) ((x * y⁻¹) *ᵥ w) = hermC τ G v w := by
  have hyu : IsUnit y.det := isUnit_iff_ne_zero.mpr hy
  have hback : ∀ c : Fin r → ℂ, y *ᵥ (y⁻¹ *ᵥ c) = c := fun c => by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hyu, Matrix.one_mulVec]
  calc hermC τ G ((x * y⁻¹) *ᵥ v) ((x * y⁻¹) *ᵥ w)
      = hermC τ G (x *ᵥ (y⁻¹ *ᵥ v)) (x *ᵥ (y⁻¹ *ᵥ w)) := by
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    _ = hermC τ G (y *ᵥ (y⁻¹ *ᵥ v)) (y *ᵥ (y⁻¹ *ᵥ w)) := by
        rw [hermC_mulVec, hermC_mulVec, h]
    _ = hermC τ G v w := by rw [hback, hback]

theorem exists_real_point {D : D7} {S T : HSp D} (C : Ctx S T)
    (u : C.X.Ψ → Matrix (Fin T.rank) (Fin T.rank) ℂ)
    (hu : ∀ (σ : C.X.Ψ) v w, hermC σ.1 C.X.Gm (u σ *ᵥ v) (u σ *ᵥ w) = hermC σ.1 C.X.Gm v w) :
    ∃ a ∈ GinfC T, (fun σ => (compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T a)).map conj) = u := by
  obtain ⟨σ₀, hσ₀⟩ := GlobalTheory.RealLineAt.exists_inverse_chart C.inf
  obtain ⟨k, hk, hkτ⟩ := GlobalTheory.FockCompare.LiftUnitary.lift_unitary D C.θ σ₀ hσ₀ T
    (fun τ => (u (C.m.e τ)).map conj) (fun τ => by
      have hcc : ((u (C.m.e τ)).map conj).map conj = u (C.m.e τ) := by
        ext i j
        simp
      simp only [Formalism.QuantumDeterminants.UH, Set.mem_setOf_eq]
      rw [GlobalTheory.StabProper.unitary_iff_form, hcc]
      intro v w
      have hform := hu (C.m.e τ) v w
      rw [GlobalTheory.StabProper.hermC_eq, GlobalTheory.StabProper.hermC_eq, Equiv.symm_apply_apply] at hform
      exact hform)
  refine ⟨k, hk, ?_⟩
  funext σ
  have hcomp : compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T k) = (u σ).map conj := by
    rw [GlobalTheory.StabProper.compAt_eq, ← GlobalTheory.FockCompare.RealAction.infMat_eq, hkτ, Equiv.apply_symm_apply]
  rw [hcomp]
  ext i j
  simp

theorem frame_decomp : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ x ∈ C.X.dom, ∃ a ∈ GinfC T, ∃ b ∈ Bor C.X.Ψ T.rank, x = rmul (C.xB (C.mvB a B)) b := by
  intro D S T C B hB x hx
  obtain ⟨o, b, -, -, hob, -⟩ := GlobalTheory.Ker.exists_orthonormalisation D.host.E T.rank C.X
  obtain ⟨hon, hbB, hxeq, -, -⟩ := hob x hx
  have hz : IsONFr C.X (C.xB B) := GlobalTheory.Ker.ONBasis.isONFr_xB C hB
  have hzdom : C.xB B ∈ C.X.dom := GlobalTheory.Ker.ONBasis.mem_dom C.X hz
  have hdet : ∀ σ, (FD.mat (C.xB B) σ).det ≠ 0 := fun σ => (hzdom σ).1
  obtain ⟨a, ha, hau⟩ := exists_real_point C
    (fun σ => FD.mat (o x) σ * (FD.mat (C.xB B) σ)⁻¹)
    (fun σ v w => isometry_of_gram_eq σ.1 C.X.Gm (FD.mat (o x) σ) (FD.mat (C.xB B) σ) (hdet σ)
      (by rw [hon σ, hz σ]) v w)
  refine ⟨a, ha, b x, hbB, ?_⟩
  have hmove : C.xB (C.mvB a B) = o x := by
    funext σ
    have hσ := congrFun hau σ
    have hstep : FD.mat (C.xB (C.mvB a B)) σ
        = (compAt C.θ (C.m.e.symm σ) (Formalism.L2.Theta.mt T a)).map conj * FD.mat (C.xB B) σ := by
      ext i j
      set_option synthInstance.maxHeartbeats 100000 in
        simp [GlobalTheory.Ker.Ctx.xB, GlobalTheory.Ker.Ctx.mvB, FD.mat, Matrix.mul_apply, map_sum]
    rw [hσ, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr (hdet σ)),
      Matrix.mul_one] at hstep
    exact hstep
  rw [hmove]
  exact hxeq

end GlobalTheory.FrameDecomp
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DomainFrameEqRealTranslateMulBorelStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.domain_frame_eq_real_translate_mul_borel : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (B : C.Bas), C.IsB B → ∀ x ∈ C.X.dom, ∃ a ∈ GinfC T, ∃ b ∈ Bor C.X.Ψ T.rank, x = rmul (C.xB (C.mvB a B)) b := by
  first | exact @GlobalTheory.FrameDecomp.frame_decomp | exact GlobalTheory.FrameDecomp.frame_decomp | (intros; apply GlobalTheory.FrameDecomp.frame_decomp <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReadOffFormsAutomorphicInverseMultiplier
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Ker.AutRead

theorem lact_rmul {E : Type} [Field E] {Ψ : Finset (E →+* ℂ)} {r : ℕ} (γ : GL (Fin r) E) (y b : Frame Ψ r) :
    lact γ (rmul y b) = rmul (lact γ y) b := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map ⇑(τ : E →+* ℂ) * (mat y τ * mat b τ) =
    (γ : Matrix (Fin r) (Fin r) E).map ⇑(τ : E →+* ℂ) * mat y τ * mat b τ
  rw [Matrix.mul_assoc]

theorem ip_smul_self {n g : ℕ} (t : ℂ) {v : TF n g} (hv : SW.IsSB v) :
    SW.ip (t • v) (t • v) = (t * conj t) * SW.ip v v := by
  have hc : SW.IsSB (fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v v hv hv).2.2.2.1
  have hP : SW.IsSB (v * fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) v _ hv hc).2.2.1
  have e : (fun x : Matrix (Fin n) (Fin g) ℚ => (t • v) x * conj ((t • v) x)) = (t * conj t) • (v * fun x : Matrix (Fin n) (Fin g) ℚ => conj (v x)) := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, Pi.mul_apply, map_mul]
    ring
  rw [SW.ip, SW.ip, e, (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin n) (Fin g) _ _ hP hP).2.2.2.2.2.1]
  rfl

end GlobalTheory.Ker.AutRead

namespace GlobalTheory.Ker.AutRead

theorem std_mem_Vset {D : D7} {S T : HSp D} (C : Ctx S T) (M : ℕ) (hM : 0 < M) :
    stdL D.host.E S.rank ∈ Vset D.host.E S.rank M := by
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [Red.fmtC_one]; exact Red.isMov_one _
  exact (GlobalTheory.T.self_dual_lattices_at_level D S T C).1 M 1 _ hM (Red.trivAt_one _ _) (Red.stdL_fg _) hs1

theorem wG_phi_std {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ)
    (hM : 0 < M) (hM𝔪 : (M : 𝓞 D.host.E) ∈ Lv.𝔪) (v₀ : Lt D.host.E T.rank → TF S.rank C.g)
    (hv : ∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L))
    (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ)
    (hμ : ∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L))
    (γ : GL (Fin T.rank) D.host.E) (hγ : γ ∈ Lv.grp) (L : Lt D.host.E T.rank) (hL : L ∈ Lv.lats) :
    wG C.X C.bas C.idx γ (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) =
      μ γ L • Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank) := by
  obtain ⟨-, -, hgrp, hlat, -, -, -⟩ := GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  obtain ⟨hun, k, hkJ, hred⟩ := (hgrp γ).1 hγ
  have hL' : mapL γ L ∈ Lv.lats := ((hlat L hL).2.2.2 γ hγ).1
  have e1 := hμ γ hγ L hL ⟨k, hkJ⟩ hred
  obtain ⟨-, -, hw3, -⟩ := GlobalTheory.T.weil_action_preserves_theta_and_inner_product D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even γ hun (v₀ L) (hv L hL).1
  have hip := (hw3 (v₀ L) (hv L hL).1).1
  rw [e1, ip_smul_self _ (hv _ hL').1, (hv _ hL').2.1, (hv L hL).2.1, mul_one, Complex.mul_conj] at hip
  have hn1 : ‖μ γ L * ((Lv.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)‖ = 1 := by
    have h2 : Complex.normSq (μ γ L * ((Lv.lam ⟨k, hkJ⟩ : ℂˣ) : ℂ)) = 1 := by exact_mod_cast hip
    rw [Complex.normSq_eq_norm_sq] at h2
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h2
  rw [(GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    (std_mem_Vset C M hM)).2.2.2 γ hγ ⟨k, hkJ⟩ hred _ hn1 e1, mul_inv_cancel_right₀ (Units.ne_zero _)]

theorem th_phi_ne {D : D7} {S T : HSp D} (C : Ctx S T) (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ)
    (hM : 0 < M) (hM𝔪 : (M : 𝓞 D.host.E) ∈ Lv.𝔪) (v₀ : Lt D.host.E T.rank → TF S.rank C.g)
    (hv : ∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L))
    (B : C.Bas) (hB : C.IsB B) (L : Lt D.host.E T.rank) (hL : L ∈ Lv.lats) :
    C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) ≠ 0 := by
  intro h0
  have hstd := std_mem_Vset C M hM
  have hx := ((GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2 B hB).2.1
  have hsb := (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    hstd).1
  obtain ⟨h1, h2, -⟩ := GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ hx _ hsb
  have hsb0 := (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin S.rank) (Fin C.g) _ _ hsb hsb).2.1 0
  have e : C.Th (C.xB B) ((0 : ℂ) • Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) =
      C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) := by
    rw [h2, zero_smul, h0]
  have hΦ0 : Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank) = 0 := by
    rw [(h1 _ hsb0).2 e.symm, zero_smul]
  have hip := (GlobalTheory.T.thetaTestFunction_norm_and_overlap_bound D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L hL _
    hstd).1
  rw [hΦ0, SW.ip] at hip
  have ez : (fun x : Matrix (Fin S.rank) (Fin C.g) ℚ => (0 : TF S.rank C.g) x * conj ((0 : TF S.rank C.g) x)) =
      (0 : ℂ) • (0 : TF S.rank C.g) := by
    funext x; simp
  rw [ez, (GlobalTheory.T.rationalSchwartzBruhat_algebra_integral_linear ℚ (Fin S.rank) (Fin C.g) _ _ SW.isSB_zero SW.isSB_zero).2.2.2.2.2.1, zero_mul] at hip
  haveI : Finite (𝓞 D.host.E ⧸ Lv.𝔪) := Ideal.finiteQuotientOfFreeOfNeBot _ Lv.ne_bot
  have hpos : 0 < Nat.card Lv.J := Nat.card_pos
  exact (Nat.cast_ne_zero.2 hpos.ne') hip.symm

end GlobalTheory.Ker.AutRead

namespace GlobalTheory.Ker.AutRead

theorem read_off_automorphic : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → ∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, F (mapL γ L) (lact γ x) = (μ γ L)⁻¹ * F L x := by
  intro D S T C om hW Lv hn M hw hM hM𝔪 B hB f' hbase c c' z φ hz hφQ hK v₀ μ hv hμ ep cf hep gL hgL F hFhol hFb hFφ
    γ hγ L hL
  obtain ⟨hΛl, -, hgrp, hlat, -, -, -⟩ := GlobalTheory.T.level_structure_properties D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn
  obtain ⟨hun, k0, hkJ, hred⟩ := (hgrp γ).1 hγ
  have hL' : mapL γ L ∈ Lv.lats := ((hlat L hL).2.2.2 γ hγ).1
  have hJ := (GlobalTheory.T.thetaKernel_orthonormalFrame_inDomain_periodLinear D S T C).2
  have hmv := (hJ B hB).2.2.2.2.2
  obtain ⟨e, he⟩ := (GlobalTheory.T.rational_unitary_group_structure D S T C).1
  have hγA : IsRatOf T γ (e ⟨γ, hun⟩).1 := he ⟨γ, hun⟩
  have hγAQ : (e ⟨γ, hun⟩).1 ∈ GQ T := (e ⟨γ, hun⟩).2
  have hgrpT := (GlobalTheory.T.rational_unitary_group_structure D S T C).2.2.2 T
  have hcomm := hgrpT.2.2.2.1
  obtain ⟨a₀, ha₀, f, hf, hγAe⟩ := hgrpT.2.2.1 (e ⟨γ, hun⟩).1
  set γA := (e ⟨γ, hun⟩).1 with hγAdef
  obtain ⟨g1f, g1t, g1m⟩ := hgL L hL
  obtain ⟨g2f, g2t, g2m⟩ := hgL (mapL γ L) hL'
  have hk := GlobalTheory.T.rationalLevelPoint_finitePart_mem_levelGroup D S T C Lv γ ⟨k0, hkJ⟩ hred a₀ f (gL L) (gL (mapL γ L)) L ha₀ hf (hγAe ▸ hγA) g1f g2f g1t g2t
    hL.1.1 (hlat L hL).2.1 hL'.1.1 g1m g2m
  set k := (gL (mapL γ L))⁻¹ * f * gL L with hkdef

  have hstd := std_mem_Vset C M hM
  have hs1 : IsMov (fmtC S 1) (stdL D.host.E S.rank) (stdL D.host.E S.rank) := by
    rw [Red.fmtC_one]; exact Red.isMov_one _
  obtain ⟨hbase0, hu⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).2 v₀ hv
  obtain ⟨t, ht0, hft⟩ := (GlobalTheory.T.levelDatumVector_eq_theta_of_testFunction D S T C Lv hn M hw hM hM𝔪 B hB).1 f' hbase _ (hv _ hΛl)
  have hk0 : om (1, k) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
      C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank)) := by
    have h1 := (hK k ⟨k0, hkJ⟩ hk).1
    rw [hft, hu t, map_smul] at h1
    exact smul_right_injective _ ht0 h1

  have hsb : ∀ L₁ ∈ Lv.lats, SW.IsSB (Lv.phi C.bas hn v₀ L₁ (stdL D.host.E S.rank)) := fun L₁ hL₁ =>
    (GlobalTheory.T.levelTestFunction_finite_sum_equivariant D.host.E T.rank C.X C.g C.bas C.idx S.rank C.sympl C.even Lv hn M hM hM𝔪 v₀ hv L₁ hL₁ _ hstd).1
  have hep1 : ∀ L₁ ∈ Lv.lats, ‖ep 1‖ = 1 ∧ ‖cf (gL L₁)‖ = 1 ∧ om (1, gL L₁)
      (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
      (ep 1 * cf (gL L₁)) • C.Th (C.xB B) (Lv.phi C.bas hn v₀ L₁ (stdL D.host.E S.rank)) := by
    intro L₁ hL₁
    obtain ⟨h1, h2, h3⟩ := hgL L₁ hL₁
    have := hep 1 _ (gL L₁) L₁ (one_mem _) (Red.trivAt_one _ _) (Red.stdL_fg _) hs1 h1 h2 hL₁.1.1 h3
    simpa only [Prod.mk_one_one] using this
  have key : ∀ a ∈ GinfC T, F (mapL γ L) (lact γ (C.xB (C.mvB a B))) = (μ γ L)⁻¹ * F L (C.xB (C.mvB a B)) := by
    intro a ha
    have hBa : C.IsB (C.mvB a B) := (hmv a).1
    have ha₀a : a₀ * a ∈ GinfC T := mul_mem ha₀ ha
    have hY : lact γ (C.xB (C.mvB a B)) = C.xB (C.mvB (a₀ * a) B) := by
      rw [← ((hJ _ hBa).2.2.2.2.2 γA).2.2.2.2.2 γ hγA, ← (hmv a).2.1 γA, hγAe, mul_assoc,
        ← (hcomm a ha).2.2 f hf, ← mul_assoc, (hmv f).2.1 (a₀ * a), (hmv f).2.2.1 hf]

    have hel : γA * (gL L * a) = gL (mapL γ L) * (a₀ * a) * k := by
      have c1 : a₀ * a * (gL (mapL γ L))⁻¹ = (gL (mapL γ L))⁻¹ * (a₀ * a) := (hcomm _ ha₀a).2.2 _ (inv_mem g2f)
      have c2 : a * f = f * a := (hcomm a ha).2.2 f hf
      have c3 : a * gL L = gL L * a := (hcomm a ha).2.2 _ g1f
      rw [hkdef, hγAe]
      calc a₀ * f * (gL L * a) = a₀ * (f * a) * gL L := by rw [← c3]; group
        _ = gL (mapL γ L) * (a₀ * a * (gL (mapL γ L))⁻¹) * f * gL L := by rw [c1, ← c2]; group
        _ = _ := by group
    have s1 : φ (gL L * a) = φ (gL (mapL γ L) * (a₀ * a)) := by
      rw [← hφQ γA hγAQ, hel, (hK k ⟨k0, hkJ⟩ hk).2]
    rw [hFφ L hL a ha, hFφ (mapL γ L) hL' _ ha₀a] at s1

    have hne : C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) ≠ 0 :=
      th_phi_ne C Lv hn M hM hM𝔪 v₀ hv _ (hmv _).1 _ hL'
    have hx : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ hBa).2.1
    have hX1 : om (1, γA * a * gL L) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
        (ep 1 * cf (gL L) * z a * μ γ L) •
          C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
      have p : ((1, γA * a * gL L) : GA D S × GA D T) = (1, γA) * ((1, a) * (1, gL L)) := by
        simp only [Prod.mk_mul_mk, one_mul, mul_assoc]
      rw [p, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, (hep1 L hL).2.2, map_smul,
        hz a ha _ (hsb L hL), map_smul, map_smul, ((GlobalTheory.T.weilRep_rationalPoints_thetaFunctions_fock D S T C om hW).2 γ γA hγA _ (hsb L hL)).1 _ hx,
        wG_phi_std C Lv hn M hM hM𝔪 v₀ hv μ hμ γ hγ L hL, hY,
        (GlobalTheory.T.thetaKernel_testFunction_map_linear_injective_equivariant D S T C _ ((hJ _ (hmv _).1).2.1) _ (hsb _ hL')).2.1, smul_smul, smul_smul]
    have hX2 : om (1, γA * a * gL L) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) =
        (ep 1 * cf (gL (mapL γ L)) * z (a₀ * a)) •
          C.Th (C.xB (C.mvB (a₀ * a) B)) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
      have c3 : a * gL L = gL L * a := (hcomm a ha).2.2 _ g1f
      have p : ((1, γA * a * gL L) : GA D S × GA D T) = (1, a₀ * a) * ((1, gL (mapL γ L)) * (1, k)) := by
        have eq : γA * a * gL L = a₀ * a * (gL (mapL γ L) * k) := by
          rw [mul_assoc γA, c3, hel, ← mul_assoc (a₀ * a), ← (hcomm _ ha₀a).2.2 _ g2f]
        rw [eq]
        simp only [Prod.mk_mul_mk, one_mul]
      rw [p, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hk0, (hep1 _ hL').2.2, map_smul,
        hz _ ha₀a _ (hsb _ hL'), smul_smul]
    have hsc : ep 1 * cf (gL L) * z a * μ γ L = ep 1 * cf (gL (mapL γ L)) * z (a₀ * a) :=
      smul_left_injective ℂ hne (hX1.symm.trans hX2)

    have hza : z a ≠ 0 := by
      intro h0
      have h1 := hz a ha _ (hsb L hL)
      rw [h0, zero_smul] at h1
      have h2 : om (1, a⁻¹) (om (1, a) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)))) =
          C.Th (C.xB B) (Lv.phi C.bas hn v₀ L (stdL D.host.E S.rank)) := by
        rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
          Module.End.one_apply]
      rw [h1, map_zero] at h2
      exact th_phi_ne C Lv hn M hM hM𝔪 v₀ hv B hB L hL h2.symm
    have hep0 : ep 1 ≠ 0 := fun h0 => by
      have := (hep1 L hL).1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hcf0 : cf (gL L) ≠ 0 := fun h0 => by
      have := (hep1 L hL).2.1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hμ0 : μ γ L ≠ 0 := fun h0 => by
      rw [h0, mul_zero] at hsc
      have hcf1 : cf (gL (mapL γ L)) ≠ 0 := fun h1 => by
        have := (hep1 _ hL').2.1; rw [h1, norm_zero] at this; exact zero_ne_one this
      have hz1 : z (a₀ * a) ≠ 0 := by
        intro h1
        have h3 := hz _ ha₀a _ (hsb _ hL')
        rw [h1, zero_smul] at h3
        have h2 : om (1, (a₀ * a)⁻¹) (om (1, a₀ * a) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)))) =
            C.Th (C.xB B) (Lv.phi C.bas hn v₀ (mapL γ L) (stdL D.host.E S.rank)) := by
          rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, one_mul, inv_mul_cancel, Prod.mk_one_one, map_one,
            Module.End.one_apply]
        rw [h3, map_zero] at h2
        exact th_phi_ne C Lv hn M hM hM𝔪 v₀ hv B hB _ hL' h2.symm
      exact mul_ne_zero (mul_ne_zero hep0 hcf1) hz1 hsc.symm
    rw [hY]
    have hinv : μ γ L * (μ γ L)⁻¹ = 1 := mul_inv_cancel₀ hμ0
    have hq : z a * ep 1 * cf (gL L) * μ γ L ≠ 0 := mul_ne_zero (mul_ne_zero (mul_ne_zero hza hep0) hcf0) hμ0
    apply mul_left_cancel₀ hq
    linear_combination (F (mapL γ L) (C.xB (C.mvB (a₀ * a) B))) * hsc - s1 -
      (z a * ep 1 * cf (gL L) * F L (C.xB (C.mvB a B))) * hinv
  intro x hx
  obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.T.domain_frame_eq_real_translate_mul_borel D S T C B hB x hx
  have hxa : C.xB (C.mvB a B) ∈ C.X.dom := (hJ _ (hmv a).1).2.1
  have hya : lact γ (C.xB (C.mvB a B)) ∈ C.X.dom := by
    rw [← ((hJ _ (hmv a).1).2.2.2.2.2 γA).2.2.2.2.2 γ hγA, ← (hmv a).2.1 γA]
    exact (hJ _ (hmv _).1).2.1
  rw [lact_rmul, hFb _ hL' _ hya b hb, hFb L hL _ hxa b hb, key a ha]
  ring

end GlobalTheory.Ker.AutRead
end

section -- merged from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ReadOffFormsAutomorphicInverseMultiplierStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.readOffForms_automorphic_inverse_multiplier : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeak C.ψ S T om → ∀ (Lv : SW.Level C.X) (hn : T.rank ≤ S.rank) (M : ℕ), IdemTwo Lv.w → 0 < M → (M : 𝓞 D.host.E) ∈ Lv.𝔪 → ∀ B, C.IsB B → ∀ f', C.IsBase Lv B f' → ∀ (c : C.X.Ψ → Fin C.q0 → ℕ) (c' : C.X.Ψ → Fin C.X.p0 → ℕ) (z φ : GA D T → ℂ), (∀ a ∈ GinfC T, RealScal C om B a (z a)) → (∀ γ ∈ GQ T, ∀ g, φ (γ * g) = φ g) → (∀ (k : GA D T) (κ : Lv.J), C.LevK Lv k κ → om (1, k) (C.uVec Lv hn f') = C.uVec Lv hn f' ∧ ∀ g, φ (g * k) = φ g) → ∀ (v₀ : Lt D.host.E T.rank → TF S.rank C.g) (μ : GL (Fin T.rank) D.host.E → Lt D.host.E T.rank → ℂ), (∀ L ∈ Lv.lats, IsVac C.X C.bas Lv.w (tens (stdL D.host.E S.rank) (Lv.sh L)) (v₀ L)) → (∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ k : Lv.J, Lv.Red (fun i => (γ : Matrix (Fin T.rank) (Fin T.rank) D.host.E) *ᵥ Lv.β i) k → wG C.X C.bas C.idx γ (v₀ L) = (μ γ L * (Lv.lam k : ℂˣ)) • v₀ (mapL γ L)) → ∀ (ep : GA D S → ℂ) (cf : GA D T → ℂ), (∀ (h : GA D S) (Λ : Lt D.host.E S.rank) (g : GA D T) (L : Lt D.host.E T.rank), h ∈ GfC S → TrivAt S (Ideal.span {(M : 𝓞 D.host.F)}) h → Λ.FG → IsMov (fmtC S h) (stdL D.host.E S.rank) Λ → g ∈ GfC T → TrivAt T (C.under Lv) g → L.FG → IsMov (fmt T g) C.X.Λ L → ‖ep h‖ = 1 ∧ ‖cf g‖ = 1 ∧ om (h, g) (C.Th (C.xB B) (Lv.phi C.bas hn v₀ C.X.Λ (stdL D.host.E S.rank))) = (ep h * cf g) • (C.Th (C.xB B) (Lv.phi C.bas hn v₀ L Λ))) → ∀ gL : Lt D.host.E T.rank → GA D T, (∀ L ∈ Lv.lats, gL L ∈ GfC T ∧ TrivAt T (C.under Lv) (gL L) ∧ IsMov (fmt T (gL L)) C.X.Λ L) → ∀ F : Lt D.host.E T.rank → Frame C.X.Ψ T.rank → ℂ, (∀ L ∈ Lv.lats, DifferentiableOn ℂ (F L) C.X.dom) → (∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, ∀ b ∈ Bor C.X.Ψ T.rank, F L (rmul x b) = bchar (wtOf C.X C.hr c c' S.rank) b * F L x) → (∀ L ∈ Lv.lats, ∀ a ∈ GinfC T, φ (gL L * a) = z a * (ep 1 * cf (gL L)) * F L (C.xB (C.mvB a B))) → ∀ γ ∈ Lv.grp, ∀ L ∈ Lv.lats, ∀ x ∈ C.X.dom, F (mapL γ L) (lact γ x) = (μ γ L)⁻¹ * F L x := by
  first | exact @GlobalTheory.Ker.AutRead.read_off_automorphic | exact GlobalTheory.Ker.AutRead.read_off_automorphic | (intros; apply GlobalTheory.Ker.AutRead.read_off_automorphic <;> assumption)
end
