/-
Bulletin de paie : assemblage de toutes les lignes après le brut.

Ordre des lignes : cotisations salariales, cotisations patronales,
réductions et déductions. Le bulletin donne le net avant impôt, le coût
employeur global et la ventilation des versements par organisme.
-/
import Cotisations.Assiette
import Cotisations.Organismes
import Cotisations.CotisationsLegales
import Cotisations.RetraiteComplementaire
import Cotisations.ReducGenerale
import Cotisations.Taxes
import Cotisations.Convention

namespace Cotisations

/-- Bulletin complet d'un salarié pour une période. -/
structure Bulletin where
  brut : Eur
  lignesSalariales : List LigneCotisation
  /-- Lignes mixtes de retraite complémentaire (parts salariale et
      patronale sur une même ligne, comme sur un bulletin réel). -/
  lignesRetraite : List LigneCotisation
  lignesPatronales : List LigneCotisation
  lignesReductions : List LigneCotisation
  /-- Total des retenues salariales. -/
  totalSalarial : Eur
  /-- Total des prélèvements patronaux, net des réductions. -/
  totalPatronalNet : Eur
  /-- Montant total de la réduction générale (imputée en négatif). -/
  reducGenerale : Eur
  /-- Net à payer avant impôt sur le revenu. -/
  netAvantIR : Eur
  /-- Coût global employeur (brut + patronal net des réductions). -/
  coutEmployeur : Eur
  /-- Montants versés à chaque organisme (salarial + patronal). -/
  versements : List (Organisme × Eur)
  deriving Repr, DecidableEq

/-- Intègre des lignes mixtes supplémentaires (prévoyance conventionnelle,
    cotisations d'une branche professionnelle…) dans un bulletin existant :
    les parts salariales s'ajoutent au total salarial et diminuent le net,
    les parts patronales s'ajoutent au coût employeur, et les versements
    par organisme sont recalculés. `calculeBulletinSyntech` et toute
    convention future s'appuient sur cette primitive commune. -/
def Bulletin.avecLignesSupplementaires (b : Bulletin) (lignes : List LigneCotisation) :
    Bulletin :=
  let sal := sommeSalariale lignes
  let pat := sommePatronale lignes
  { b with
    lignesPatronales := b.lignesPatronales ++ lignes.filter (fun l => !l.estNulle)
    totalSalarial := b.totalSalarial + sal
    netAvantIR := b.netAvantIR - sal
    totalPatronalNet := b.totalPatronalNet + pat
    coutEmployeur := b.coutEmployeur + pat
    versements := versementsParOrganisme
      (b.lignesSalariales ++ b.lignesRetraite ++ b.lignesPatronales
        ++ lignes ++ b.lignesReductions) }

/-- Calcule le bulletin complet d'un salarié pour une période mensuelle. -/
def calculeBulletin (pa : ParametresAnnee) (pe : ParametresEntreprise)
    (ps : ParametresSalarie) (cc : Option ConventionCollective) : Bulletin :=
  let plafond := plafondMensuelProratise pa ps
  let t := decoupeTranches ps.assietteSecu plafond
  let ppAA := parametresAgircArrco2026
  let retraite := lignesRetraiteComplementaire ps ppAA t plafond
  let salariales :=
    lignesSecuSalariales pa pe ps t
    ++ (match cc with
        | some c => lignesConventionSalariales c t
        | none => [])
  let patronales :=
    lignesSecuPatronales pa pe ps t plafond
    ++ lignesTaxesPatronales pa pe ps t plafond
    ++ (match cc with
        | some c => lignesConventionPatronales c t
        | none => [])
  let mRGDU :=
    if ps.contrat == .apprentissage then 0
    else montantRGDU (parametresRGDU pa pe) ps.assietteRGDU ps.brutHeuresSupplementaires
  let reductions :=
    (if mRGDU > 0 then [reductionRGDU pa pe ps mRGDU] else [])
    ++ (if ps.nombreHeuresSupplementaires > 0 then
          [deductionForfaitaireHeuresSup pa pe ps] else [])
  let sal := sommeSalariale salariales + sommeSalariale retraite
  let pat := sommePatronale patronales + sommePatronale retraite + sommePatronale reductions
  { brut := ps.assietteSecu
    lignesSalariales := salariales.filter (fun l => !l.estNulle)
    lignesRetraite := retraite.filter (fun l => !l.estNulle)
    lignesPatronales := patronales.filter (fun l => !l.estNulle)
    lignesReductions := reductions
    totalSalarial := sal
    totalPatronalNet := pat
    reducGenerale := mRGDU
    netAvantIR := ps.assietteSecu - sal
    coutEmployeur := ps.assietteSecu + pat
    versements := versementsParOrganisme (salariales ++ retraite ++ patronales ++ reductions) }

end Cotisations