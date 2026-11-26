module

public import Formalism.LocalToGlobal.UnitaryNorms.MemFIffReal
public import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf

@[expose] public section

section -- merged from Formalism.LocalToGlobal.UnitaryNorms.RealPl
noncomputable section

open NumberField

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

theorem emb_mul_cc (g : R.GG) (x : H.E) : H.emb (g * R.cc) x = H.emb g (H.conj x) := by
  show H.φ₀ (H.sigmaOf (g * R.cc) x) = H.φ₀ (H.sigmaOf g (H.conj x))
  have : H.sigmaOf (g * R.cc) = H.sigmaOf g * H.conj := map_mul (H.gal).symm g (R.cc)
  rw [this]; rfl

theorem conj_of_mem_F {x : H.E} (hx : x ∈ H.F) : H.conj x = x :=
  (H.conjE_mem_hostF_iff x).1 hx

theorem mul_cc_mem_Psi {g : R.GG} (hg : g ∉ R.Psi) : g * R.cc ∈ R.Psi := by
  rw [Formalism.HC.Frame.mem_Psi_iff] at hg ⊢
  show g.1.2 * (-1) = 1
  rcases Int.units_eq_one_or g.1.2 with h | h
  · exact absurd h hg
  · rw [h]; rfl

theorem realPl_surjective : Function.Surjective (realPl H) := by
  intro w
  have : Algebra.IsAlgebraic H.F H.E := Algebra.IsAlgebraic.tower_top (K := ℚ) H.F
  obtain ⟨W, rfl⟩ := InfinitePlace.comap_surjective (K := H.E) w
  obtain ⟨g, hg⟩ := (factEmb R H).1.2 W.embedding
  have hW : InfinitePlace.mk (H.emb g) = W := by rw [hg]; exact InfinitePlace.mk_embedding W
  by_cases hgP : g ∈ R.Psi
  · refine ⟨⟨g, hgP⟩, ?_⟩
    rw [← hW]; exact (InfinitePlace.comap_mk _ _).symm
  · refine ⟨⟨g * R.cc, mul_cc_mem_Psi hgP⟩, ?_⟩
    have : (H.emb (g * R.cc)).comp H.F.subtype = (H.emb g).comp H.F.subtype := RingHom.ext fun x => by
      show H.emb (g * R.cc) (x : H.E) = H.emb g (x : H.E)
      rw [emb_mul_cc, conj_of_mem_F H x.2]
    rw [realPl, this, ← hW]; exact (InfinitePlace.comap_mk _ _).symm

theorem realPlBij : RealPlBij H := by
  refine (realPl_surjective H).bijective_of_nat_card_le ?_
  have h1 := IsTotallyReal.finrank (K := H.F)
  have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces H.F
  have h3 : Module.finrank ℚ H.F = R.f := H.finrank_hostF
  rw [(factCardPsi R H).1, Nat.card_eq_fintype_card, h2, ← h1, h3]
  omega

def tauPl (D : D7) : D.what₂.Tau ≃ InfinitePlace D.host.F :=
  D.eTau.trans (Equiv.ofBijective (realPl D.host) (realPlBij D.host))

end Formalism.L2.Host
end
end

section -- merged from Formalism.LocalToGlobal.UnitaryNorms.CharHost
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

variable {R : Ranks} (H : Formalism.BasicNotions.Host R)

def OverP (p : ℕ) (v : HeightOneSpectrum (𝓞 H.E)) : Prop := ((p : ℕ) : 𝓞 H.E) ∈ v.asIdeal

instance psiFintype (φ : Formalism.HC.Frame) : Fintype φ.Psi := Fintype.ofFinite _

def embPsi (g : R.Psi) : H.E →+* ℂ := H.emb (g : R.GG)

structure IsClsF (ξ : HChar H.E) : Prop where
  unitary : ξ.IsUnitary
  unr : ∀ v, ξ.UnrAt v
  inf : ∀ k, ξ.inf k = 1
  triv : ξ.TrivOn H.F

structure IsEtaT (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  res : χ.ResEta H.F
  inf : χ.HasInf (embPsi H) (fun _ => 1)

def etaAlg (χ : HChar H.E) (v : HeightOneSpectrum (𝓞 H.E)) : ℂ := χ.valTw (1 / 2) v

def EtaTExists : Prop := ∃ χ : HChar H.E, IsEtaT H χ

structure IsChiPsi (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  unr : ∀ v, χ.UnrAt v
  triv : χ.TrivOn H.F
  inf : χ.HasInf (embPsi H) (fun _ => 2)

structure PiBar where
  pb : Fin 2 → HeightOneSpectrum (𝓞 H.K)
  pb_over : ∀ k, ((H.g k : ℕ) : 𝓞 H.K) ∈ (pb k).asIdeal

def PiBar.Div {H : Formalism.BasicNotions.Host R} (P : PiBar H) (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)) : Prop :=
  w.under (𝓞 H.K) = P.pb k

structure Omg where
  om : ∀ k : Fin 2, (ZMod (H.g k))ˣ →* ℂˣ
  gen : ∀ k, Function.Injective (om k)

variable {H}

structure IsMu0 (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) (χ : HChar H.E) : Prop where
  unitary : χ.IsUnitary
  triv : χ.TrivOn H.F
  inf : χ.HasInfQ (embPsi H) (fun τ => -e τ)
  unr : ∀ v, (∀ k, ¬ OverP H (H.g k) v) → χ.UnrAt v
  tame : ∀ v, χ.TameAt v
  atg : ∀ (k : Fin 2) (w : HeightOneSpectrum (𝓞 H.E)), P.Div k w → ∀ (a : ℕ) (ha : a.Coprime (H.g k)) (x : H.Eˣ),
    (x : H.E) = (a : H.E) → χ.locK w x = (W.om k (ZMod.unitOfCoprime a ha) ^ (2 * (j + 1)))⁻¹

def Mu0Exists (P : PiBar H) (W : Omg H) (e : R.Psi → ℚ) (j : ℕ) : Prop := ∃ χ : HChar H.E, IsMu0 P W e j χ

structure IsDelta (p : ℕ) (χ : HChar H.E) : Prop where
  fin : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  unr : ∀ v, ¬ OverP H p v → χ.UnrAt v
  ine : ∀ v, OverP H p v → ∀ n : ℕ, (∀ x, IsUnitAt v x → χ.loc v x ^ n = 1) ↔ 15 ∣ n

def DeltaExists (p : ℕ) : Prop := ∃ χ : HChar H.E, IsDelta (H := H) p χ

structure IsPsi (l : ℕ) (Q : Finset (HeightOneSpectrum (𝓞 H.E))) (χ : HChar H.E) : Prop where
  ord : ∃ a : ℕ, χ.OrderDvd (l ^ a)
  triv : χ.TrivOn H.F
  tame : ∀ v, χ.TameAt v
  ram : ∀ v, χ.UnrAt v ↔ v ∉ Q
  atl : ∀ v, OverP H l v → ∀ x, χ.loc v x = 1
  split : ∀ v ∈ Q, IsSplitPl H v

def SplitsCompletely (Q : Finset (HeightOneSpectrum (𝓞 H.E))) : Prop :=
  ∀ v ∈ Q, ∀ p : ℕ, p.Prime → OverP H p v → ∀ v' : HeightOneSpectrum (𝓞 H.E), OverP H p v' →
    Ideal.absNorm v'.asIdeal = p ∧ ((p : ℕ) : 𝓞 H.E) ∉ v'.asIdeal ^ 2

end Formalism.L2.Host
end
end
