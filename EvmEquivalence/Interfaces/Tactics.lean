/-
This file contains tactics to agilize and compress certain repetitive proofs
 -/

import EvmEquivalence.KEVM2Lean.Func

-- Tactics to perform lengthy simps for schedule
syntax "simp_schedule1" : tactic
syntax "simp_schedule2" : tactic
syntax "simp_flag"      : tactic

-- The reason for having separate simps is that otherwise
-- Lean performs too many operations at once
macro_rules
| `(tactic| simp_schedule1) =>
    `(tactic| simp [«_<_>_SCHEDULE_Int_ScheduleConst_Schedule»];
              simp [SCHEDULE_GaccesslistaddressBerlin];
              simp [SCHEDULE_GaccesslistaddressDefault];
              simp [SCHEDULE_GaccessliststoragekeyBerlin];
              simp [SCHEDULE_GaccessliststoragekeyDefault];
              simp [SCHEDULE_GbalanceDefault];
              simp [SCHEDULE_GbalanceIstanbul];
              simp [SCHEDULE_GbalanceTangerine];
              simp [SCHEDULE_GbaseDefault];
              simp [SCHEDULE_GblockhashDefault];
              simp [SCHEDULE_GcallDefault];
              simp [SCHEDULE_GcallTangerine];
              simp [SCHEDULE_GcallstipendDefault];
              simp [SCHEDULE_GcallvalueDefault];
              simp [SCHEDULE_GcodedepositDefault];
              simp [SCHEDULE_GcoldaccountaccessBerlin];
              simp [SCHEDULE_GcoldaccountaccessDefault];
              simp [SCHEDULE_GcoldsloadBerlin];
              simp [SCHEDULE_GcoldsloadDefault];
              simp [SCHEDULE_GcopyDefault];
              simp [SCHEDULE_GcreateDefault];
              simp [SCHEDULE_GecaddDefault];
              simp [SCHEDULE_GecaddIstanbul];
              simp [SCHEDULE_GecmulDefault];
              simp [SCHEDULE_GecmulIstanbul];
              simp [SCHEDULE_GecpaircoeffDefault];
              simp [SCHEDULE_GecpaircoeffIstanbul];
              simp [SCHEDULE_GecpairconstDefault];
              simp [SCHEDULE_GecpairconstIstanbul];
              simp [SCHEDULE_GexpDefault];
              simp [SCHEDULE_GexpbyteDefault];
              simp [SCHEDULE_GexpbyteDragon];
              simp [SCHEDULE_GextcodecopyDefault];
              simp [SCHEDULE_GextcodecopyTangerine];
              simp [SCHEDULE_GextcodesizeDefault];
              simp [SCHEDULE_GextcodesizeTangerine];
              simp [SCHEDULE_GfroundDefault];
              simp [SCHEDULE_GhighDefault];
              simp [SCHEDULE_GinitcodewordcostDefault];
              simp [SCHEDULE_GinitcodewordcostShanghai];
              simp [SCHEDULE_GjumpdestDefault];
              simp [SCHEDULE_GlogDefault];
              simp [SCHEDULE_GlogdataDefault];
              simp [SCHEDULE_GlogtopicDefault];
              simp [SCHEDULE_GlowDefault];
              simp [SCHEDULE_GmemoryDefault];
              simp [SCHEDULE_GmidDefault];
              simp [SCHEDULE_GnewaccountDefault];
              simp [SCHEDULE_GpointevalCancun];
              simp [SCHEDULE_GpointevalDefault];
              simp [SCHEDULE_GquadcoeffDefault];
              simp [SCHEDULE_GquaddivisorBerlin];
              simp [SCHEDULE_GquaddivisorDefault];
              simp [SCHEDULE_GselfdestructDefault];
              simp [SCHEDULE_GselfdestructTangerine];
              simp [SCHEDULE_Gsha3Default];
              simp [SCHEDULE_Gsha3wordDefault];
              (try simp [SCHEDULE_GsloadBerlin]);
              simp [SCHEDULE_GsloadDefault];
              simp [SCHEDULE_GsloadIstanbul];
              simp [SCHEDULE_GsloadTangerine];
              (try simp [SCHEDULE_GsstoreresetBerlin]);
              simp [SCHEDULE_GsstoreresetDefault];
              simp [SCHEDULE_GsstoresetDefault];
              simp [SCHEDULE_GtransactionDefault];
              simp [SCHEDULE_GtxcreateDefault];
              simp [SCHEDULE_GtxcreateFrontier];
              simp [SCHEDULE_GtxdatanonzeroDefault];
              simp [SCHEDULE_GtxdatanonzeroIstanbul];
              simp [SCHEDULE_GtxdatazeroDefault];
              simp [SCHEDULE_GverylowDefault])

-- Depending on the proofs, the rewrites finish sooner than others
-- Hence the pervasiveness of `try` in this tactic
macro_rules
| `(tactic| simp_schedule2) =>
    `(tactic| (try simp [SCHEDULE_GwarmstoragedirtystoreCancun]);
              (try simp [SCHEDULE_GwarmstoragedirtystoreDefault]);
              (try simp [SCHEDULE_GwarmstoragereadBerlin]);
              (try simp [SCHEDULE_GwarmstoragereadDefault]);
              (try simp [SCHEDULE_GzeroDefault]);
              (try simp [SCHEDULE_RbByzantium]);
              (try simp [SCHEDULE_RbConstantinople]);
              (try simp [SCHEDULE_RbDefault]);
              (try simp [SCHEDULE_RbMerge]);
              (try simp [SCHEDULE_RmaxquotientDefault]);
              (try simp [SCHEDULE_RmaxquotientLondon]);
              (try simp [SCHEDULE_RselfdestructDefault]);
              (try simp [SCHEDULE_RselfdestructLondon]);
              (try simp [SCHEDULE_RsstoreclearDefault]);
              (try simp [SCHEDULE_RsstoreclearLondon]);
              (try simp [SCHEDULE_SCHEDCONSTBerlin]);
              (try simp [SCHEDULE_SCHEDCONSTByzantium]);
              (try simp [SCHEDULE_SCHEDCONSTCancun]);
              (try simp [SCHEDULE_SCHEDCONSTConstantinople]);
              (try simp [SCHEDULE_SCHEDCONSTDragon]);
              (try simp [SCHEDULE_SCHEDCONSTFrontier]);
              (try simp [SCHEDULE_SCHEDCONSTHomestead]);
              (try simp [SCHEDULE_SCHEDCONSTIstanbul]);
              (try simp [SCHEDULE_SCHEDCONSTLondon]);
              (try simp [SCHEDULE_SCHEDCONSTMerge]);
              (try simp [SCHEDULE_SCHEDCONSTPetersburg]);
              (try simp [SCHEDULE_SCHEDCONSTShanghai]);
              (try simp [SCHEDULE_SCHEDCONSTTangerine]);
              (try simp [SCHEDULE_maxCodeSizeDefault]);
              (try simp [SCHEDULE_maxCodeSizeDragon]);
              (try simp [SCHEDULE_maxInitCodeSizeDefault]);
              (try simp [SCHEDULE_maxInitCodeSizeShanghai]))

macro_rules
| `(tactic| simp_flag) =>
  `(tactic| (try simp [«_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule»]);
            (try simp [SCHEDULE_GemptyisnonexistentDefault]);
            (try simp [SCHEDULE_GemptyisnonexistentDragon]);
            (try simp [SCHEDULE_GhasaccesslistDefault]);
            (try simp [SCHEDULE_GhasbasefeeDefault]);
            (try simp [SCHEDULE_GhasbasefeeLondon]);
            (try simp [SCHEDULE_GhasbeaconrootCancun]);
            (try simp [SCHEDULE_GhasbeaconrootDefault]);
            (try simp [SCHEDULE_GhasblobbasefeeCancun]);
            (try simp [SCHEDULE_GhasblobbasefeeDefault]);
            (try simp [SCHEDULE_GhasblobhashCancun]);
            (try simp [SCHEDULE_GhasblobhashDefault]);
            (try simp [SCHEDULE_GhaschainidDefault]);
            (try simp [SCHEDULE_GhaschainidIstanbul]);
            (try simp [SCHEDULE_Ghascreate2Constantinople]);
            (try simp [SCHEDULE_Ghascreate2Default]);
            (try simp [SCHEDULE_GhasdirtysstoreConstantinople]);
            (try simp [SCHEDULE_GhasdirtysstoreDefault]);
            (try simp [SCHEDULE_GhasdirtysstoreIstanbul]);
            (try simp [SCHEDULE_GhasdirtysstorePetersburg]);
            (try simp [SCHEDULE_Ghaseip6780Cancun]);
            (try simp [SCHEDULE_Ghaseip6780Default]);
            (try simp [SCHEDULE_GhasextcodehashConstantinople]);
            (try simp [SCHEDULE_GhasextcodehashDefault]);
            (try simp [SCHEDULE_GhasmaxinitcodesizeDefault]);
            (try simp [SCHEDULE_GhasmaxinitcodesizeShanghai]);
            (try simp [SCHEDULE_GhasmcopyCancun]);
            (try simp [SCHEDULE_GhasmcopyDefault]);
            (try simp [SCHEDULE_GhasprevrandaoDefault]);
            (try simp [SCHEDULE_GhasprevrandaoMerge]);
            (try simp [SCHEDULE_GhaspushzeroDefault]);
            (try simp [SCHEDULE_GhaspushzeroShanghai]);
            (try simp [SCHEDULE_GhasrejectedfirstbyteDefault]);
            (try simp [SCHEDULE_GhasrejectedfirstbyteLondon]);
            (try simp [SCHEDULE_GhasreturndataByzantium]);
            (try simp [SCHEDULE_GhasreturndataDefault]);
            (try simp [SCHEDULE_GhasrevertByzantium]);
            (try simp [SCHEDULE_GhasrevertDefault]);
            (try simp [SCHEDULE_GhasselfbalanceDefault]);
            (try simp [SCHEDULE_GhasselfbalanceIstanbul]);
            (try simp [SCHEDULE_GhasshiftConstantinople]);
            (try simp [SCHEDULE_GhasshiftDefault]);
            (try simp [SCHEDULE_GhassstorestipendDefault]);
            (try simp [SCHEDULE_GhassstorestipendIstanbul]);
            (try simp [SCHEDULE_GhasstaticcallByzantium]);
            (try simp [SCHEDULE_GhasstaticcallDefault]);
            (try simp [SCHEDULE_GhastransientCancun]);
            (try simp [SCHEDULE_GhastransientDefault]);
            (try simp [SCHEDULE_GhaswarmcoinbaseDefault]);
            (try simp [SCHEDULE_GhaswarmcoinbaseShanghai]);
            (try simp [SCHEDULE_GhaswithdrawalsDefault]);
            (try simp [SCHEDULE_GhaswithdrawalsShanghai]);
            (try simp [SCHEDULE_GselfdestructnewaccountDefault]);
            (try simp [SCHEDULE_GselfdestructnewaccountTangerine]);
            (try simp [SCHEDULE_GstaticcalldepthDefault]);
            (try simp [SCHEDULE_GstaticcalldepthTangerine]);
            (try simp [SCHEDULE_GzerovaluenewaccountgasDefault]);
            (try simp [SCHEDULE_GzerovaluenewaccountgasDragon]);
            (try simp [SCHEDULE_SCHEDFLAGBerlin]);
            (try simp [SCHEDULE_SCHEDFLAGByzantium]);
            (try simp [SCHEDULE_SCHEDFLAGCancun]);
            (try simp [SCHEDULE_SCHEDFLAGConstantinople]);
            (try simp [SCHEDULE_SCHEDFLAGDragon]);
            (try simp [SCHEDULE_SCHEDFLAGFrontier]);
            (try simp [SCHEDULE_SCHEDFLAGHomestead]);
            (try simp [SCHEDULE_SCHEDFLAGIstanbul]);
            (try simp [SCHEDULE_SCHEDFLAGLondon]);
            (try simp [SCHEDULE_SCHEDFLAGMerge]);
            (try simp [SCHEDULE_SCHEDFLAGPetersburg]);
            (try simp [SCHEDULE_SCHEDFLAGShanghai]);
            (try simp [SCHEDULE_SCHEDFLAGTangerine]);
            (try simp [SCHEDULE_hasaccesslistBerlin]))
