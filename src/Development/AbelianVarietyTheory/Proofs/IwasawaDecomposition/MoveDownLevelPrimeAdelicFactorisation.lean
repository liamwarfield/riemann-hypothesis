module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEtaleOfIsEtaleCompletion

@[expose] public section

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimesNotSelfConjugateDisjointTypeTwist
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimesNotSelfConjugateDisjointTypeTwist
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
noncomputable section

namespace GlobalTheory.Mem.PrimesAtLevel

theorem not_both_mem {R : Type} [CommRing R] (P : Ideal R) [P.IsPrime] {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hne : p ≠ q) (hpP : (p : R) ∈ P) (hqP : (q : R) ∈ P) : False := by
  obtain ⟨a, b, hab⟩ : IsCoprime (p : ℤ) (q : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_primes hp hq).mpr hne)
  have h1 : ((a * p + b * q : ℤ) : R) = 1 := by rw [hab, Int.cast_one]
  push_cast at h1
  apply (inferInstance : P.IsPrime).ne_top
  rw [Ideal.eq_top_iff_one, ← h1]
  exact P.add_mem (P.mul_mem_left _ hpP) (P.mul_mem_left _ hqP)

theorem primes_atT : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (v : (I.atT l u a).vT), conjPrime₂ v.1 ≠ v.1 ∧ (∀ w ∈ (B.primes X).vGs, ¬ IsOver (v.1.under (𝓞 B.host.F)) w) ∧ (∀ P ∈ I.Q a, ¬ IsOver (v.1.under (𝓞 B.host.F)) P) ∧ Disjoint (B.primes X).vGs (I.Q a) := by
  intro B X I hI l u a v
  obtain ⟨P, hP⟩ := v
  dsimp only at hP ⊢
  have hpr := l.pr
  have hpiT : (B.primes X).piT u ∈ P.asIdeal := by
    unfold Primes.vT divs at hP
    split_ifs at hP with h
    · exact h.mem_toFinset.mp hP
    · simp at hP
  have hT : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ P.asIdeal := by
    rw [← hpr.piT_norm u]
    exact P.asIdeal.mul_mem_right _ hpiT
  have hTF : (((B.primes X).T u : ℕ) : 𝓞 B.host.F) ∈ (P.under (𝓞 B.host.F)).asIdeal := by
    show _ ∈ Ideal.comap (algebraMap _ _) _
    rw [Ideal.mem_comap, map_natCast]
    exact hT
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hc
    have h2 : B.fields.conjO ((B.primes X).piT u) ∈ P.asIdeal := by
      have h3 : (B.primes X).piT u ∈ (conjPrime₂ P).asIdeal := by rw [hc]; exact hpiT
      exact (mem_conjP P _).mp h3
    obtain ⟨x, y, hxy⟩ := hpr.piT_cop u
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hxy]
    exact P.asIdeal.add_mem (P.asIdeal.mul_mem_left _ hpiT) (P.asIdeal.mul_mem_left _ h2)
  · intro w hw hov
    have hTw : (((B.primes X).T u : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      rw [IsOver] at hov
      rw [hov, Ideal.mem_comap, map_natCast] at hTF
      exact hTF
    obtain ⟨i, hi⟩ : ∃ i, w ∈ (B.primes X).vG i := by
      classical
      rcases Finset.mem_union.mp hw with h | h
      · exact ⟨0, h⟩
      · exact ⟨1, h⟩
    have hgw : (((B.primes X).g i : ℕ) : 𝓞 B.fields.E) ∈ w.asIdeal := by
      have hc : B.fields.conjO ((B.primes X).piG i) ∈ w.asIdeal := by
        unfold Primes.vG divs at hi
        split_ifs at hi with h
        · exact h.mem_toFinset.mp hi
        · simp at hi
      rw [← hpr.piG_norm i]
      exact w.asIdeal.mul_mem_left _ hc
    exact not_both_mem w.asIdeal (hpr.T_prime u) (hpr.g_prime i) (hpr.T_ne_g u i) hTw hgw
  · intro Q hQ hov
    obtain ⟨v, -, hsel, hgood⟩ := I.exists_of_mem_Q hQ
    have hv : v.asIdeal = (P.under (𝓞 B.host.F)).asIdeal := by
      rw [hov, ← hsel]
      exact (hI.sel_ok v).symm
    have hTv : (((B.primes X).T u : ℕ) : 𝓞 B.fields.F ⧸ v.asIdeal) = 0 := by
      rw [← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem, hv]
      exact hTF
    have hd : ringChar (𝓞 B.fields.F ⧸ v.asIdeal) ∣ (B.primes X).T u := (ringChar.spec _ _).mp hTv
    rcases (Nat.dvd_prime (hpr.T_prime u)).mp hd with h1 | h1
    · exact CharP.ringChar_ne_one h1
    · apply hgood.2.2
      convert hI.T_mem u using 1
      exact h1
  · exact Finset.disjoint_right.mpr (Q_notMem_of_ok hI a)

end GlobalTheory.Mem.PrimesAtLevel
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimesNotSelfConjugateDisjointTypeTwistStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.levelPrimes_not_selfConjugate_disjoint_type_twist : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (v : (I.atT l u a).vT), conjPrime₂ v.1 ≠ v.1 ∧ (∀ w ∈ (B.primes X).vGs, ¬ IsOver (v.1.under (𝓞 B.host.F)) w) ∧ (∀ P ∈ I.Q a, ¬ IsOver (v.1.under (𝓞 B.host.F)) P) ∧ Disjoint (B.primes X).vGs (I.Q a) := by
  first | exact @GlobalTheory.Mem.PrimesAtLevel.primes_atT | exact GlobalTheory.Mem.PrimesAtLevel.primes_atT | (intros; apply GlobalTheory.Mem.PrimesAtLevel.primes_atT <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownPointPreservesIndexFrames
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownPointPreservesIndexFrames
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2

theorem PtY.mv_dn_facts {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n)
    (p : PtY ST SG Q y) (P : ST) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) (v : HeightOneSpectrum (𝓞 X.F))
    (hov : IsOver v P.1) (hne : conjPrime₂ P.1 ≠ P.1) (hconj : IsOver v (conjPrime₂ P.1)) :
    (p.mv (p.1.1.deco.dn P f')).1.2 = p.1.2 ∧ (p.mv (p.1.1.deco.dn P f')).1.1.fr = p.1.1.fr ∧
      Deco.SameOff ST SG v p.1.1.deco.1 (p.mv (p.1.1.deco.dn P f')).1.1.deco.1 := by
  classical

  have key : Deco.SameOff ST SG v p.1.1.deco.1 (p.1.1.deco.dn P f').1 := by
    unfold DecoSet.dn
    split_ifs with hok
    · refine ⟨fun Q hQ => ?_, fun Q hQ => ?_, fun _ _ => rfl⟩
      · have hQP : Q ≠ P.1 := fun h => hQ (by rw [h]; exact hov)
        have hQc : Q ≠ conjPrime₂ P.1 := fun h => hQ (by rw [h]; exact hconj)
        exact ((p.1.1.deco.2.dnN_spec P hne).2.2.1 Q hQP hQc).localization_eq.symm
      · have hQP : Q ≠ P := fun h => hQ (by rw [h]; exact hov)
        show p.1.1.deco.1.f Q = Function.update p.1.1.deco.1.f P f' Q
        rw [Function.update_of_ne hQP]
    · exact ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩

  suffices H : ∀ d : DecoSet (E := X.E) (n := n) (ST := ST) (SG := SG), Deco.SameOff ST SG v p.1.1.deco.1 d.1 →
      (p.mv d).1.2 = p.1.2 ∧ (p.mv d).1.1.fr = p.1.1.fr ∧
        Deco.SameOff ST SG v p.1.1.deco.1 (p.mv d).1.1.deco.1 from H _ key
  intro d hd
  by_cases h : (∀ (P : Q) (x : Sp X.E n), p.1.1.1.2 P x ∈ d.1.at P.1 ↔ x ∈ stdAt X.E n P.1) ∧ p.1.2 ∈ y.ys d.1.N
  · have e : (p.mv d).1 = ((⟨(d, p.1.1.1.2), h.1⟩ : DecoF X.E n ST SG Q), p.1.2) :=
      congrArg Subtype.val (dif_pos h)
    rw [e]
    exact ⟨rfl, rfl, hd⟩
  · have e : p.mv d = p := dif_neg h
    rw [e]
    exact ⟨rfl, rfl, ⟨fun _ _ => rfl, fun _ _ => rfl, fun _ _ => rfl⟩⟩

end GlobalTheory.Mem.Col2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownPointPreservesIndexFramesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moveDown_point_preserves_index_frames : ∀ {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} (y : Ys X n) (p : PtY ST SG Q y) (P : ST) (f' : Sp X.E n → 𝓞 X.E ⧸ P.1.asIdeal) (v : HeightOneSpectrum (𝓞 X.F)), IsOver v P.1 → conjPrime₂ P.1 ≠ P.1 → IsOver v (conjPrime₂ P.1) → (p.mv (p.1.1.deco.dn P f')).1.2 = p.1.2 ∧ (p.mv (p.1.1.deco.dn P f')).1.1.fr = p.1.1.fr ∧ Deco.SameOff ST SG v p.1.1.deco.1 (p.mv (p.1.1.deco.dn P f')).1.1.deco.1 := by
  first | exact @GlobalTheory.Mem.Col2.PtY.mv_dn_facts | exact GlobalTheory.Mem.Col2.PtY.mv_dn_facts | (intros; apply GlobalTheory.Mem.Col2.PtY.mv_dn_facts <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetCongrIndexFramesLocalLattices
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetCongrIndexFramesLocalLattices
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2

theorem cosetIn_congr : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p p' : PtAt R sel mu cst u j), p.1.2 = p'.1.2 → p.1.1.fr = p'.1.1.fr → (∀ w : Pr.vGs, localization₂ w.1.asIdeal p.1.1.deco.1.N = localization₂ w.1.asIdeal p'.1.1.deco.1.N ∧ p.1.1.deco.1.be w = p'.1.1.deco.1.be w) → cosetIn p = cosetIn p' := by
  intro X Pr R sel S mu cst u j p p' h2 hfr hloc
  have hF : ∀ P, frsF sel mu p.1.1 P = frsF sel mu p'.1.1 P := by
    intro P
    unfold frsF
    split_ifs with h
    · have e1 := (hloc ⟨P.1, h⟩).1
      have e2 := (hloc ⟨P.1, h⟩).2
      unfold Deco.liftFr Deco.at
      rw [e1, e2]
    · rw [hfr]
  funext P
  unfold cosetIn
  rw [h2, hF P]

end GlobalTheory.Mem.Col2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetCongrIndexFramesLocalLatticesStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCoset_congr_index_frames_localLattices : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (p p' : PtAt R sel mu cst u j), p.1.2 = p'.1.2 → p.1.1.fr = p'.1.1.fr → (∀ w : Pr.vGs, localization₂ w.1.asIdeal p.1.1.deco.1.N = localization₂ w.1.asIdeal p'.1.1.deco.1.N ∧ p.1.1.deco.1.be w = p'.1.1.deco.1.be w) → cosetIn p = cosetIn p' := by
  first | exact @GlobalTheory.Mem.Col2.cosetIn_congr | exact GlobalTheory.Mem.Col2.cosetIn_congr | (intros; apply GlobalTheory.Mem.Col2.cosetIn_congr <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesRationalActionEq
section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesRationalActionEq
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2

theorem cosetIn_act_rat : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (j : ℕ) (b : (I.stp u a j).β) (x : (I.stp u a j).G b) (p : (I.stp u a j).D b), x.2 = 1 → cosetIn ((I.stp u a j).act b x p) = cosetIn p := by
  intro B X I _ l u a j b x p hx
  obtain ⟨γ, κ⟩ := x
  simp only at hx
  subst hx
  exact _root_.GlobalTheory.Mem.Col2.cosetIn_smul_unitary _ _ _ _ _ _ _ _ _ (GlobalTheory.Mem.FieldsLaws.fields_ok B) l.pr _ _ γ rfl rfl

end GlobalTheory.Mem.Col2
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CouplingCosetInFramesRationalActionEqStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.couplingCosetInFrames_rational_action_eq : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (u : B.Word) (a : I.ι) (j : ℕ) (b : (I.stp u a j).β) (x : (I.stp u a j).G b) (p : (I.stp u a j).D b), x.2 = 1 → cosetIn ((I.stp u a j).act b x p) = cosetIn p := by
  first | exact @GlobalTheory.Mem.Col2.cosetIn_act_rat | exact GlobalTheory.Mem.Col2.cosetIn_act_rat | (intros; apply GlobalTheory.Mem.Col2.cosetIn_act_rat <;> assumption)
end
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisation
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.UG.P Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2.DnAdel

theorem grpId {G : Type*} [Group G] (a b c d : G) : a * (a⁻¹ * b * c * d⁻¹) * d = b * c := by group

theorem grpId2 {G : Type*} [Group G] (r y1 kb y0 hm m : G) (h : hm = r * (y1 * kb)) :
    r * y1 = y0 * (y0⁻¹ * hm * m⁻¹ * hm⁻¹ * y0) * (y0⁻¹ * hm * m * kb⁻¹) := by subst h; group

theorem etaFacts {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (v0 : HeightOneSpectrum (𝓞 F))
    (y0 hm g0 : GL (Fin n) (TensorProduct F E (Formalism.L2.Herm.Af F)))
    (hy0 : y0 ∈ Formalism.L2.Herm.UstdAf hc n) (hh : hm ∈ Formalism.L2.Herm.UstdAf hc n) (hg : g0 ∈ Formalism.L2.Herm.UstdAf hc n) :
    (∀ v', v' ≠ v0 → bc (prV (E := E) v') (y0⁻¹ * hm * (rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * g0)))⁻¹ * hm⁻¹ * y0) = 1) ∧
      y0⁻¹ * hm * (rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * g0)))⁻¹ * hm⁻¹ * y0 ∈ Formalism.L2.Herm.UstdAf hc n := by
  have hm0 : rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * g0)) ∈ Formalism.L2.Herm.UstdAf hc n :=
    rll_put_mem_UAd hc n v0 (afsplit_bc_mem hc.sig 1 v0 _ (mul_mem (inv_mem hh) hg))
  refine ⟨fun v' hv' => ?_, ?_⟩
  · simp only [map_mul, map_inv]
    rw [rll_put_ne n v0 v' hv']
    group
  · exact mul_mem (mul_mem (mul_mem (mul_mem (inv_mem hy0) hh) (inv_mem hm0)) (inv_mem hh)) hy0

theorem coreMove {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (J : Matrix (Fin n) (Fin n) E) (hJ : J = 1)
    (v0 : HeightOneSpectrum (𝓞 F)) (U : Subgroup (GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))))
    (chi : U →* ℂˣ) (y0 y1 : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (γ : GL (Fin n) E)
    (kb : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F))) (t s : ℂ) (hts : t = s⁻¹)
    (hk : kb ∈ Formalism.L2.Herm.UstdAf hc n)
    (hh : bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) ∈ Formalism.L2.Herm.UstdAf hc n)
    (hlev : ∀ x, y0.1 * x * kb = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) *
        rll_put n v0 (bc (prV (E := E) v0) ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb))⁻¹ * (y0.1 * kb))) → x ∈ U)
    (hchi : ∀ x : U, y0.1 * x.1 * kb = bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) *
        rll_put n v0 (bc (prV (E := E) v0) ((bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb))⁻¹ * (y0.1 * kb))) →
        ((chi x : ℂˣ) : ℂ) = t) :
    ∃ (η : UPts hc.sig J (FiniteAdeleRing (𝓞 F) F)) (κ : U), (∀ v', v' ≠ v0 → bc (prV (E := E) v') η.1 = 1) ∧
      bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * y1.1 = y0.1 * η.1 * κ.1 ∧ (((chi κ)⁻¹ : ℂˣ) : ℂ) = s := by
  subst hJ
  set hm := bc (inclE (F := F) (FiniteAdeleRing (𝓞 F) F)) γ * (y1.1 * kb) with hhm
  set m := rll_put n v0 (bc (prV (E := E) v0) (hm⁻¹ * (y0.1 * kb))) with hmdef
  have hE := etaFacts hc n v0 y0.1 hm (y0.1 * kb) y0.2 hh (mul_mem y0.2 hk)
  have hx : y0.1 * (y0.1⁻¹ * hm * m * kb⁻¹) * kb = hm * m := grpId _ _ _ _
  have hU := hlev _ hx
  refine ⟨⟨_, hE.2⟩, ⟨_, hU⟩, hE.1, grpId2 _ _ _ _ _ _ hhm, ?_⟩
  rw [Units.val_inv_eq_inv_val, hchi ⟨_, hU⟩ hx, hts, inv_inv]

theorem actSameOff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
    {ST SG : Finset (HeightOneSpectrum (𝓞 E))} (v : HeightOneSpectrum (𝓞 F)) {d d' : Deco E n ST SG}
    (h : Deco.SameOff ST SG v d d') (ga : Sp E n ≃ₗ[E] Sp E n) (hh : GLG (E := E) (n := n) (SG := SG)) :
    Deco.SameOff ST SG v (d.act ga hh) (d'.act ga hh) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Q hQ
    ext x
    show x ∈ localization₂ Q.asIdeal (gmap ga d.N) ↔ x ∈ localization₂ Q.asIdeal (gmap ga d'.N)
    rw [mem_localization_gmap, mem_localization_gmap, h.N Q hQ]
  · intro Q hQ
    funext x
    show d.f Q (ga.symm x) = d'.f Q (ga.symm x)
    rw [h.f Q hQ]
  · intro w hw
    funext x
    show (hh w).1.mulVec (d.be w (ga.symm x)) = (hh w).1.mulVec (d'.be w (ga.symm x))
    rw [h.be w hw]

theorem pointGen {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) [NeZero n] (ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 E)))
    (v0 : HeightOneSpectrum (𝓞 F)) (r0 d r' : DecoF E n ST SG Q) (a : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q)
    (hmv : a • r' = d) (hfr : d.fr = r0.fr) (hoff : Deco.SameOff ST SG v0 r0.deco.1 d.deco.1)
    (hQSQ : Q ⊆ SQ) (hdis : Disjoint SG Q) (g0 h : GL (Fin n) (TensorProduct F E (FiniteAdeleRing (𝓞 F) F)))
    (h0 : IsPtOf hc g0 (extTo SQ r0))
    (h1 : IsPtOf hc h (((a.1, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n SQ) • extTo SQ r'))
    (hQ : ∀ P ∈ Q, ¬ IsOver v0 P) (hSG : ∀ w ∈ SG, ¬ IsOver v0 w) :
    IsPtOf hc (h * rll_put n v0 (bc (prV (E := E) v0) (h⁻¹ * g0)))
      ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • r0) := by
  have e1 : (((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • d = ((a.1, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • r' := by
    rw [← hmv, smul_smul]
    congr 1
    ext1
    · simp
    · ext1 <;> simp
  refine GlobalTheory.T.isPointOf_decoratedLattice_splicedAtPlace hc n ST SG Q SQ SQ v0 g0 h (extTo SQ r0) _ _ h0 h1 hQ hSG ?_ ?_ ?_ ?_
  · have h2 := actSameOff v0 hoff (((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q)).1.1) (((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q)).2.1)
    have e2 : (((a.1, 1, 1) : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n SQ) • extTo SQ r').deco.1 = ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • d).deco.1 := by
      rw [e1]; rfl
    rw [e2]
    exact h2
  · intro P _
    ext x
    show x ∈ localization₂ P.asIdeal (gmap _ r0.deco.1.N) ↔ x ∈ localization₂ P.asIdeal r0.deco.1.N
    rw [mem_localization_gmap]
    exact Iff.rfl
  · intro P _
    funext x
    rfl
  · intro P
    refine ⟨⟨P.1, hQSQ P.2⟩, rfl, ?_⟩
    have hP : P.1 ∉ SG := Finset.disjoint_right.1 hdis P.2
    have e3 : ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • r0).fr P =
        ((((1 : UF E n), a.2)⁻¹ : UF E n × GLG (E := E) (n := n) (SG := SG) × GLQ E n Q) • d).fr P := by
      show _ * r0.1.2 P * _ = _ * d.1.2 P * _
      rw [show d.1.2 P = d.fr P from rfl, hfr]; rfl
    rw [e3, e1]
    show a.1.1 * ptFr r' P.1 * _ = a.1.1 * r'.1.2 P * _
    rw [ptFr_of_mem r' hP P.2]
    simp
    rfl

theorem ufGL_UJ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (γ : UF E n) : ufGL E n γ ∈ UJ (hc.sig : E →+* E) (1 : Matrix (Fin n) (Fin n) E) := by
  show cT _ _ * 1 * _ = 1
  rw [mul_one]
  exact GlobalTheory.Mem.Col2.StepOk.ufGL_conjTranspose_mul γ


set_option maxHeartbeats 8000000 in
theorem move_down_adelic : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ hβ : chOf ((I.fm l u a).dn i v c.1 g) = β, ∃ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)) (η : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (κ : (K β).lev.U), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) ∧ (∀ v', v' ≠ (eV v).1 → bc (prV (E := (I.rec7 l Z).host.E) v') η.1 = 1) ∧ bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) γ.1 * ((K β).y ⟨(I.fm l u a).dn i v c.1 g, hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧ ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) : B.LLˣ) : B.LL) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K eY eV L hR hY hV hL v β c g hg hβ
  obtain ⟨k, R⟩ := hR
  obtain ⟨c0, hc0⟩ := c
  subst hc0

  have hgram : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.T.trueColumn_spaces_standard_in_frameCoords I hOk hPins l Z).2.2.2 i hi).1
  haveI : NeZero (B.R.N i) := inferInstance
  have hP := GlobalTheory.T.levelPrimes_not_selfConjugate_disjoint_type_twist I hOk l u a v
  have hv0 : (eV v).1 = v.1.under (𝓞 B.host.F) := hV v
  have hd : ((I.atIn u a).A i).dnPt v c0 g = ((I.stp u a i).rep c0).mv (((I.stp u a i).rep c0).1.1.deco.dn v (TDat.extF _ v.1 g)) := rfl
  have hdn := GlobalTheory.T.moveDown_point_preserves_index_frames _ ((I.stp u a i).rep c0) v (TDat.extF _ v.1 g) (v.1.under (𝓞 B.host.F)) rfl hP.1 (IsOver.conj B.sp.cm rfl)
  rw [← hd, ← hv0] at hdn
  have hmv := (I.stp u a i).mv_smul c0.1 (((I.atIn u a).A i).dnPt v c0 g)
  have hyc' : ∀ (β' : Ch) (h : chOf ((I.fm l u a).dn i v c0 g) = β'), ((K β').y ⟨_, h⟩).1 = ((K (chOf ((I.fm l u a).dn i v c0 g))).y ⟨_, rfl⟩).1 := by rintro _ rfl; rfl
  have hk : k (chOf ((I.fm l u a).dn i v c0 g)) = k (chOf c0) := by rw [hβ]
  have hpt0 := R.pt c0
  have hpt1 := R.pt ((I.fm l u a).dn i v c0 g)
  rw [hk, ← hyc' _ hβ] at hpt1
  have hh := GlobalTheory.T.isPointOf_rational_unitary_adelic_mul _ _ B.sp.cm _ _ _ _ ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1 _ _ hpt1
  have hq := pointGen B.sp.cm (B.R.N i) _ _ _ I.SQ (eV v).1 _ _ _ (FrmG.incl _ _ ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g))) (congrArg (fun p => p.1.1) hmv) hdn.2.1 hdn.2.2 (I.Q_subset_SQ a) hP.2.2.2 _ _ hpt0 hh (hv0 ▸ hP.2.2.1) (hv0 ▸ hP.2.1)

  have hκ'mv : (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) * (I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g) = (((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1, 1) := by
    ext1
    · simp
    · simp
  have hgam1 : (I.stp u a i).gam c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) = 1 := by
    show ufGL _ _ ((1 : UF B.fields.E (B.R.N i))⁻¹) = 1
    simp
  have hchr : (I.stp u a i).chr c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) = ((I.stp u a i).chr c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)))⁻¹ := by
    rw [map_inv]; rfl

  have hc1 := GlobalTheory.T.couplingCoset_congr_index_frames_localLattices ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) ((I.stp u a i).rep c0)) ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) (((I.atIn u a).A i).dnPt v c0 g)) (by
      show (fun x => _) '' _ = (fun x => _) '' _
      rw [hdn.1]) (by
      funext P
      show _ * ((I.stp u a i).rep c0).1.1.1.2 P * _ = _ * (((I.atIn u a).A i).dnPt v c0 g).1.1.1.2 P * _
      rw [show (((I.atIn u a).A i).dnPt v c0 g).1.1.1.2 = (((I.atIn u a).A i).dnPt v c0 g).1.1.fr from rfl, hdn.2.1]
      rfl) (fun w => ⟨(actSameOff _ hdn.2.2 _ _).N w.1 (hv0 ▸ hP.2.1 w.1 w.2), (actSameOff _ hdn.2.2 _ _).be w (hv0 ▸ hP.2.1 w.1 w.2)⟩)
  have hc2 : (I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) (((I.atIn u a).A i).dnPt v c0 g) = (I.stp u a i).act c0.1 (((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1, 1) ((I.stp u a i).rep ((I.stp u a i).cl c0.1 (((I.atIn u a).A i).dnPt v c0 g))) := by
    unfold GStep.act
    rw [← hκ'mv]
    exact (congrArg (fun p => @HSMul.hSMul _ _ _ (@instHSMul _ _ ((I.stp u a i).actD c0.1).toSMul) (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) p) hmv).symm.trans (@mul_smul _ _ _ (@MulAction.toSemigroupAction _ _ _ ((I.stp u a i).actD c0.1)) _ _ _).symm
  have hc3 := GlobalTheory.T.couplingCosetInFrames_rational_action_eq I hOk l u a i c0.1 (((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1, 1) ((I.stp u a i).rep ((I.stp u a i).cl c0.1 (((I.atIn u a).A i).dnPt v c0 g))) rfl
  have hkey := ((R.key ((I.fm l u a).dn i v c0 g) c0).1 hβ).2
  have hcos : cosetIn ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) ((I.stp u a i).rep c0)) = cosetIn ((I.stp u a i).rep c0) := by
    rw [hc1, hc2, hc3]; exact hkey

  have hγU : (I.stp u a i).gam c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)) ∈ UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi) := by
    rw [hgram]; exact ufGL_UJ B.sp.cm _ ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).1
  have hts : B.embLL (((I.stp u a i).chr c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) : B.LLˣ) : B.LL) = (B.embLL (((I.stp u a i).chr c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)) : B.LLˣ) : B.LL))⁻¹ := by
    rw [hchr, Units.val_inv_eq_inv_val, map_inv₀]
  obtain ⟨kp, hkp, -⟩ := R.k_std (chOf c0)
  obtain ⟨η, κ, h1, h2, h3⟩ := coreMove B.sp.cm (B.R.N i) (gramN (I.rec7 l Z) i hi) hgram (eV v).1 ((K (chOf c0)).lev.U) ((K (chOf c0)).lev.chi) ((K (chOf c0)).y ⟨c0, rfl⟩) ((K (chOf c0)).y ⟨_, hβ⟩) ((I.stp u a i).gam c0.1 ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g))) (k (chOf c0)) _ _ hts hkp.uni hh.uni (fun x hx => (R.lev c0 x ((I.stp u a i).act c0.1 (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) ((I.stp u a i).rep c0)).1.1 (by rw [hx]; exact hq)).2 ⟨(((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1), hgam1, rfl, hcos⟩) (fun x hx => R.chr c0 x (((1 : UF B.fields.E (B.R.N i)), ((I.stp u a i).mv c0.1 (((I.atIn u a).A i).dnPt v c0 g)).2)⁻¹ : (I.stp u a i).G c0.1) hgam1 (by rw [hx]; exact hq))
  exact ⟨⟨_, hγU⟩, η, κ, rfl, h1, h2, h3⟩

end GlobalTheory.Mem.Col2.DnAdel
end

section -- merged from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeAdelicFactorisationStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.moveDown_levelPrime_adelic_factorisation : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 B.host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))) (eY : (I.chain l u a).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi) (eV : (I.atT l u a).vT ≃ {v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F) // (B.T u : 𝓞 (I.rec7 l Z).host.F) ∈ v.asIdeal}) (L : LevelCompatibleLattices (D := (I.rec7 l Z)) (I.fm l u a) (B.T u) (I.resT l u a) i hi fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c)), I.ReadsK l Z u a i hi chOf K → I.IdY l Z u a i hi eY → I.IdV l u a eV → I.IdL l Z u a i hi L → ∀ (v : (I.atT l u a).vT) (β : Ch) (c : {c // chOf c = β}) (g : Module.Dual (Res v.1) (((I.atIn u a).A i).lk v c.1)), g ≠ 0 → ∀ hβ : chOf ((I.fm l u a).dn i v c.1 g) = β, ∃ (γ : UJ (sigD (I.rec7 l Z) : (I.rec7 l Z).host.E →+* (I.rec7 l Z).host.E) (gramN (I.rec7 l Z) i hi)) (η : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) (κ : (K β).lev.U), (γ.1 : GL (Fin (B.R.N i)) B.fields.E) = (I.stp u a i).gam c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) ∧ (∀ v', v' ≠ (eV v).1 → bc (prV (E := (I.rec7 l Z).host.E) v') η.1 = 1) ∧ bc (inclE (F := (I.rec7 l Z).host.F) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F)) γ.1 * ((K β).y ⟨(I.fm l u a).dn i v c.1 g, hβ⟩).1 = ((K β).y c).1 * η.1 * κ.1 ∧ ((((K β).lev.chi κ)⁻¹ : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1.1 ((I.stp u a i).mv c.1.1 (((I.atIn u a).A i).dnPt v c.1 g)) : B.LLˣ) : B.LL) := by
  exact @GlobalTheory.Mem.Col2.DnAdel.move_down_adelic
end
