/-
This file contains tactics to agilize and compress certain repetitive proofs
 -/

import EvmEquivalence.KEVM2Lean.Func

-- Tactics to perform lengthy simps for schedule
syntax "simp_schedule1"     : tactic
syntax "simp_schedule2"     : tactic

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
--              try simp [_fc2d477])
