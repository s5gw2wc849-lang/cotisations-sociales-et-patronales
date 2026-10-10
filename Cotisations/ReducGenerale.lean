/-
Réduction générale dégressive unique (RGDU) — en vigueur en 2026,
qui remplace la réduction générale dite « Fillon ».

Source : Urssaf, « La réduction générale dégressive unique » (page mise
à jour le 13/07/2026) ; code de la sécurité sociale, art. L241-13 et
D241-7 et suivants ; BOSS.

Formule (2026) :
  Coef = T_min + T_delta × [(ratioSMIC × (SMIC de référence / rémunération) − 1) / diviseur]^P

avec, en métropole et Dom hors Mayotte :
- T_min = 0,0200 ;
- T_delta = 0,3781 (< 50 salariés, T_max = 0,3981) ou 0,3821 (≥ 50, T_max = 0,4021) ;
- ratioSMIC = 3 au 1er janvier 2026, 2,9293 au 1er juin 2026 ;
- diviseur = 2 (les deux exemples officiels Urssaf normalisent par (3−1),
  y compris la variante « 2,9293 SMIC » du 1er juin) ;
- P = 1,75 = 7/4 ;
- SMIC de référence = SMIC de la période + SMIC horaire × heures suppl. ou compl. ;
- éligibilité : rémunération (brut + PPV) < ratioSMIC × SMIC de référence ;
- Mayotte : ratioSMIC = 1,6, diviseur = 0,6, P = 1, T_min = 0,
  T_delta = 0,2449, réduction intégralement imputée à l'Urssaf.

Montant = coefficient × rémunération brute, imputé à hauteur de
0,0601 / T_max sur la retraite complémentaire (Agirc-Arrco) et du reste
sur les cotisations Urssaf. Avec DFS, la réduction est plafonnée à
130 % du montant calculé sans DFS.

Les exemples officiels de l'Urssaf (0,3178 pour 2 000 € en juin 2026 ;
0,2652 en régularisation progressive) sont vérifiés dans `Exemples.lean`.
-/
import Cotisations.Basic
import Cotisations.Organismes
import Cotisations.Assiette
import Cotisations.Parametres

namespace Cotisations

/-- Paramètres de la réduction générale dégressive unique. -/
structure ParametresRGDU where
  /-- Ratio plafond : 3 (1er janv. 2026), 2,9293 (1er juin 2026), 1,6 (Mayotte). -/
  ratioSMIC : Rat := 3
  tMin : Rat := 0.02
  tDelta : Rat := 0.3821
  /-- Normalisation des exemples officiels : 2 en métropole, 0,6 à Mayotte. -/
  diviseur : Rat := 2
  exposantNum : Nat := 7
  exposantDen : Nat := 4
  partIRCRatio : Rat := 0.0601 / 0.4021
  partUrssafRatio : Rat := 0.3420 / 0.4021
  plafondDFS : Rat := 1.30
  /-- SMIC de la période (mensuel pour un bulletin mensuel). -/
  smicPeriode : Eur
  /-- SMIC horaire (pour les heures supplémentaires ou complémentaires). -/
  smicHoraire : Rat
  deriving Repr, DecidableEq

/-- Construit les paramètres RGDU de la période : ratio et SMIC selon la
    date (3 × SMIC du 1er janvier, 2,9293 × SMIC du 1er juin 2026),
    T_delta selon l'effectif, régime Mayotte spécifique, imputation selon
    les taux officiels. -/
def parametresRGDU (pa : ParametresAnnee) (pe : ParametresEntreprise) : ParametresRGDU :=
  let grand := pe.effectif ≥ 50
  let tMax := pa.rgduTMin + (if grand then pa.rgduTDeltaGrand else pa.rgduTDeltaPetit)
  if pe.region == .mayotte then
    { ratioSMIC := 1.6
      tMin := 0
      tDelta := pa.rgduTDeltaMayotte
      diviseur := 0.6
      exposantNum := 1
      exposantDen := 1
      partIRCRatio := 0
      partUrssafRatio := 1
      plafondDFS := pa.rgduPlafondDFS
      smicPeriode := pa.smicMensuelMayotte
      smicHoraire := pa.smicMensuelMayotte * (12 : Rat) / (1820 : Rat) }
  else
    { ratioSMIC := pa.ratioRGDU
      tMin := pa.rgduTMin
      tDelta := if grand then pa.rgduTDeltaGrand else pa.rgduTDeltaPetit
      diviseur := 2
      exposantNum := pa.rgduExposantNum
      exposantDen := pa.rgduExposantDen
      partIRCRatio := pa.rgduPartIRCT1 / tMax
      partUrssafRatio := (if grand then pa.rgduPartUrssafGrand else pa.rgduPartUrssafPetit) / tMax
      plafondDFS := pa.rgduPlafondDFS
      smicPeriode := pa.smicHoraireRGDU * (1820 : Rat) / (12 : Rat)
      smicHoraire := pa.smicHoraireRGDU }

/-- Coefficient de réduction (0 si la rémunération dépasse le plafond). -/
def coefficientRGDU (p : ParametresRGDU) (remu : Eur) (heuresSupVal : Eur) : Rat :=
  if p.ratioSMIC ≤ 1 ∨ p.diviseur ≤ 0 then 0
  else
    let smicRef : Eur := p.smicPeriode + p.smicHoraire * heuresSupVal
    let limite : Eur := p.ratioSMIC * smicRef
    if remu ≤ 0 ∨ remu ≥ limite then 0
    else
      let ratio := smicRef / remu
      let base := (p.ratioSMIC * ratio - 1) / p.diviseur
      p.tMin + p.tDelta * puissanceRat base p.exposantNum p.exposantDen

/-- Montant de la réduction = coefficient × rémunération brute. -/
def montantRGDU (p : ParametresRGDU) (remu : Eur) (heuresSupVal : Eur) : Eur :=
  coefficientRGDU p remu heuresSupVal * remu

/-- Réduction avec DFS (déduction forfaitaire spécifique pour frais
    professionnels) : calculée sur la rémunération majorée des frais,
    plafonnée à 130 % du montant calculé sans DFS. -/
def montantRGDUavecDFS (p : ParametresRGDU) (remuHorsFrais frais : Eur) : Eur :=
  let sansDFS := montantRGDU p remuHorsFrais 0
  let avecDFS := montantRGDU p (remuHorsFrais + frais) 0
  min avecDFS (p.plafondDFS * sansDFS)

/-- Ligne de bulletin de la réduction générale (part patronale négative),
    avec le détail d'imputation Urssaf / institutions de retraite
    complémentaire et les codes DSN officiels. -/
def reductionRGDU (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (montant : Eur) : LigneCotisation :=
  let p := parametresRGDU pa pe
  { nom := "Réduction générale dégressive unique"
    organisme := .urssaf, nature := .reduction, cote := .patronale
    assiette := ps.assietteRGDU
    partSalariale := 0
    partPatronale := -montant
    imputationUrssaf := montant * p.partUrssafRatio
    imputationIRC := montant * p.partIRCRatio
    commentaire := "CTP 668 (régularisation : CTP 669)" }

/-- Déduction patronale forfaitaire sur les heures supplémentaires :
    1,50 €/h (effectif ≥ 20) ou 0,25 €/h. -/
def deductionForfaitaireHeuresSup (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) : LigneCotisation :=
  let tauxHoraire := if pe.effectif ≥ 20 then pa.deductionHSGrand else pa.deductionHSPetit
  { nom := "Déduction forfaitaire patronale heures supplémentaires"
    organisme := .urssaf, nature := .reduction, cote := .patronale
    assiette := ps.nombreHeuresSupplementaires
    partSalariale := 0
    partPatronale := -(tauxHoraire * ps.nombreHeuresSupplementaires)
    commentaire := "Déduction des cotisations patronales Urssaf" }

end Cotisations