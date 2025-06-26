import EvmEquivalence.KEVM2Lean.Inj
import EvmEquivalence.KEVM2Lean.ScheduleOrdering

def _4bd3e13 : SortBool → Option SortInt
  | true => some 1
  | _ => none

def _cb4e96d : SortBool → Option SortInt
  | false => some 0
  | _ => none

def _61fbef3 : SortBool → SortBool → Option SortBool
  | false, _Gen0 => some false
  | _, _ => none

def _5b9db8d : SortBool → SortBool → Option SortBool
  | true, B => some B
  | _, _ => none

axiom «_==K_» (x0 : SortK) (x1 : SortK) : Option SortBool

def _991a329 : SortBool → SortBool → Option SortBool
  | false, B => some B
  | _, _ => none

def _7174452 : SortBool → SortBool → Option SortBool
  | true, _Gen0 => some true
  | _, _ => none

def SCHEDULE_GhasselfbalanceDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasselfbalance_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GstaticcalldepthTangerine : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Gstaticcalldepth_SCHEDULE_ScheduleFlag, SortSchedule.TANGERINE_WHISTLE_EVM => some false
  | _, _ => none

def SCHEDULE_GlogdataDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glogdata_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 8
  | _, _ => none

def SCHEDULE_GhasmcopyDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasmcopy_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GhasrevertDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasrevert_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GhasblobbasefeeCancun : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasblobbasefee_SCHEDULE_ScheduleFlag, SortSchedule.CANCUN_EVM => some true
  | _, _ => none

def SCHEDULE_GsloadTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 200
  | _, _ => none

def SCHEDULE_GcallTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcall_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 700
  | _, _ => none

def SCHEDULE_GhasbeaconrootCancun : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasbeaconroot_SCHEDULE_ScheduleFlag, SortSchedule.CANCUN_EVM => some true
  | _, _ => none

def _17ebc68 : SortBool → Option SortBool
  | false => some true
  | _ => none

def _53fc758 : SortBool → Option SortBool
  | true => some false
  | _ => none

def SCHEDULE_GhasdirtysstoreDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasdirtysstore_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

axiom «_<<Int_» (x0 : SortInt) (x1 : SortInt) : Option SortInt

def SCHEDULE_GzerovaluenewaccountgasDragon : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Gzerovaluenewaccountgas_SCHEDULE_ScheduleFlag, SortSchedule.SPURIOUS_DRAGON_EVM => some false
  | _, _ => none

def SCHEDULE_GcopyDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcopy_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 3
  | _, _ => none

def SCHEDULE_GhasmaxinitcodesizeShanghai : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasmaxinitcodesize_SCHEDULE_ScheduleFlag, SortSchedule.SHANGHAI_EVM => some true
  | _, _ => none

def SCHEDULE_GtxcreateFrontier : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxcreate_SCHEDULE_ScheduleConst, SortSchedule.FRONTIER_EVM => some 21000
  | _, _ => none

def SCHEDULE_RbMerge : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.MERGE_EVM => some 0
  | _, _ => none

def SCHEDULE_GextcodecopyDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodecopy_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GzerovaluenewaccountgasDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Gzerovaluenewaccountgas_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some true
  | _, _ => none

def SCHEDULE_GhighDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Ghigh_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 10
  | _, _ => none

def SCHEDULE_Ghascreate2Default : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghascreate2_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GtxdatanonzeroDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxdatanonzero_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 68
  | _, _ => none

def SCHEDULE_GexpbyteDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 10
  | _, _ => none

def SCHEDULE_Ghaseip6780Cancun : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghaseip6780_SCHEDULE_ScheduleFlag, SortSchedule.CANCUN_EVM => some true
  | _, _ => none

def SCHEDULE_GhasbasefeeLondon : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasbasefee_SCHEDULE_ScheduleFlag, SortSchedule.LONDON_EVM => some true
  | _, _ => none

def SCHEDULE_GlowDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glow_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 5
  | _, _ => none

def SCHEDULE_GhaschainidIstanbul : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghaschainid_SCHEDULE_ScheduleFlag, SortSchedule.ISTANBUL_EVM => some true
  | _, _ => none

def SCHEDULE_GselfdestructTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 5000
  | _, _ => none

def SCHEDULE_GwarmstoragereadBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 100
  | _, _ => none

def SCHEDULE_GhaswithdrawalsDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghaswithdrawals_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GhastransientDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghastransient_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GpointevalDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gpointeval_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_RmaxquotientLondon : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rmaxquotient_SCHEDULE_ScheduleConst, SortSchedule.LONDON_EVM => some 5
  | _, _ => none

def SCHEDULE_GhasprevrandaoDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasprevrandao_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GtxdatanonzeroIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxdatanonzero_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 16
  | _, _ => none

def SCHEDULE_GcallstipendDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcallstipend_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 2300
  | _, _ => none

def SCHEDULE_Ghascreate2Constantinople : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghascreate2_SCHEDULE_ScheduleFlag, SortSchedule.CONSTANTINOPLE_EVM => some true
  | _, _ => none

def SCHEDULE_GjumpdestDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gjumpdest_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 1
  | _, _ => none

def SCHEDULE_GhastransientCancun : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghastransient_SCHEDULE_ScheduleFlag, SortSchedule.CANCUN_EVM => some true
  | _, _ => none

def SCHEDULE_RselfdestructLondon : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.LONDON_EVM => some 0
  | _, _ => none

def SCHEDULE_GecpairconstDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpairconst_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 100000
  | _, _ => none

def SCHEDULE_GquaddivisorDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gquaddivisor_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GexpDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gexp_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 10
  | _, _ => none

def SCHEDULE_GhaswarmcoinbaseShanghai : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghaswarmcoinbase_SCHEDULE_ScheduleFlag, SortSchedule.SHANGHAI_EVM => some true
  | _, _ => none

def SCHEDULE_GhasstaticcallDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasstaticcall_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GverylowDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gverylow_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 3
  | _, _ => none

def SCHEDULE_GhasdirtysstoreConstantinople : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasdirtysstore_SCHEDULE_ScheduleFlag, SortSchedule.CONSTANTINOPLE_EVM => some true
  | _, _ => none

def SCHEDULE_GsloadDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 50
  | _, _ => none

def SCHEDULE_GhasaccesslistDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasaccesslist_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GcallDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcall_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 40
  | _, _ => none

def SCHEDULE_hasaccesslistBerlin : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasaccesslist_SCHEDULE_ScheduleFlag, SortSchedule.BERLIN_EVM => some true
  | _, _ => none

def SCHEDULE_GhassstorestipendIstanbul : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghassstorestipend_SCHEDULE_ScheduleFlag, SortSchedule.ISTANBUL_EVM => some true
  | _, _ => none

def SCHEDULE_GecmulIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecmul_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 6000
  | _, _ => none

def SCHEDULE_RbDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 5000000000000000000
  | _, _ => none

def SCHEDULE_GhasshiftConstantinople : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasshift_SCHEDULE_ScheduleFlag, SortSchedule.CONSTANTINOPLE_EVM => some true
  | _, _ => none

def SCHEDULE_GhasreturndataByzantium : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasreturndata_SCHEDULE_ScheduleFlag, SortSchedule.BYZANTIUM_EVM => some true
  | _, _ => none

def SCHEDULE_RsstoreclearDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 15000
  | _, _ => none

def SCHEDULE_GquadcoeffDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gquadcoeff_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 512
  | _, _ => none

def SCHEDULE_GhasmaxinitcodesizeDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasmaxinitcodesize_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GinitcodewordcostDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Ginitcodewordcost_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GcreateDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcreate_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 32000
  | _, _ => none

def SCHEDULE_GsstoreresetDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 5000
  | _, _ => none

def SCHEDULE_GsstoresetDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsstoreset_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20000
  | _, _ => none

def SCHEDULE_GhasshiftDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasshift_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GcoldsloadBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 2100
  | _, _ => none

def SCHEDULE_GselfdestructnewaccountTangerine : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Gselfdestructnewaccount_SCHEDULE_ScheduleFlag, SortSchedule.TANGERINE_WHISTLE_EVM => some true
  | _, _ => none

def SCHEDULE_GbalanceDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GhaspushzeroShanghai : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghaspushzero_SCHEDULE_ScheduleFlag, SortSchedule.SHANGHAI_EVM => some true
  | _, _ => none

def SCHEDULE_GnewaccountDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gnewaccount_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 25000
  | _, _ => none

def SCHEDULE_GecpaircoeffDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpaircoeff_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 80000
  | _, _ => none

def SCHEDULE_GaccesslistaddressDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccesslistaddress_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GemptyisnonexistentDragon : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Gemptyisnonexistent_SCHEDULE_ScheduleFlag, SortSchedule.SPURIOUS_DRAGON_EVM => some true
  | _, _ => none

def SCHEDULE_GquaddivisorBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gquaddivisor_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 3
  | _, _ => none

def SCHEDULE_GhasbeaconrootDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasbeaconroot_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GhasrejectedfirstbyteLondon : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasrejectedfirstbyte_SCHEDULE_ScheduleFlag, SortSchedule.LONDON_EVM => some true
  | _, _ => none

def SCHEDULE_GhasprevrandaoMerge : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasprevrandao_SCHEDULE_ScheduleFlag, SortSchedule.MERGE_EVM => some true
  | _, _ => none

def SCHEDULE_GhasblobhashDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasblobhash_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GzeroDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gzero_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GselfdestructDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GecpaircoeffIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpaircoeff_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 34000
  | _, _ => none

def SCHEDULE_maxCodeSizeDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 4294967295
  | _, _ => none

def SCHEDULE_GecaddDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecadd_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 500
  | _, _ => none

def SCHEDULE_GextcodesizeTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodesize_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 700
  | _, _ => none

def SCHEDULE_GinitcodewordcostShanghai : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Ginitcodewordcost_SCHEDULE_ScheduleConst, SortSchedule.SHANGHAI_EVM => some 2
  | _, _ => none

def SCHEDULE_GbaseDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbase_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 2
  | _, _ => none

def SCHEDULE_GhassstorestipendDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghassstorestipend_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_RmaxquotientDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rmaxquotient_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 2
  | _, _ => none

def SCHEDULE_GhaswithdrawalsShanghai : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghaswithdrawals_SCHEDULE_ScheduleFlag, SortSchedule.SHANGHAI_EVM => some true
  | _, _ => none

def SCHEDULE_GtxcreateDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxcreate_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 53000
  | _, _ => none

def SCHEDULE_GhasrejectedfirstbyteDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasrejectedfirstbyte_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GhaswarmcoinbaseDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghaswarmcoinbase_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GextcodecopyTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodecopy_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 700
  | _, _ => none

def SCHEDULE_GecmulDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecmul_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 40000
  | _, _ => none

def SCHEDULE_GhasmcopyCancun : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasmcopy_SCHEDULE_ScheduleFlag, SortSchedule.CANCUN_EVM => some true
  | _, _ => none

def SCHEDULE_GaccesslistaddressBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccesslistaddress_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 2400
  | _, _ => none

def SCHEDULE_GstaticcalldepthDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Gstaticcalldepth_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some true
  | _, _ => none

def SCHEDULE_GbalanceIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 700
  | _, _ => none

def SCHEDULE_GselfdestructnewaccountDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Gselfdestructnewaccount_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GextcodesizeDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gextcodesize_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GcoldsloadDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_maxInitCodeSizeDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.maxInitCodeSize_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GhasselfbalanceIstanbul : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasselfbalance_SCHEDULE_ScheduleFlag, SortSchedule.ISTANBUL_EVM => some true
  | _, _ => none

def SCHEDULE_Gsha3Default : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsha3_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 30
  | _, _ => none

def SCHEDULE_GecpairconstIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecpairconst_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 45000
  | _, _ => none

def SCHEDULE_GhaspushzeroDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghaspushzero_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GcoldaccountaccessDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldaccountaccess_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GhasrevertByzantium : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasrevert_SCHEDULE_ScheduleFlag, SortSchedule.BYZANTIUM_EVM => some true
  | _, _ => none

def SCHEDULE_GcallvalueDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcallvalue_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 9000
  | _, _ => none

def SCHEDULE_GhasbasefeeDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasbasefee_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GhasreturndataDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasreturndata_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GhasstaticcallByzantium : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasstaticcall_SCHEDULE_ScheduleFlag, SortSchedule.BYZANTIUM_EVM => some true
  | _, _ => none

def SCHEDULE_Ghaseip6780Default : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghaseip6780_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GaccessliststoragekeyBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccessliststoragekey_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 1900
  | _, _ => none

def SCHEDULE_maxCodeSizeDragon : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst, SortSchedule.SPURIOUS_DRAGON_EVM => some 24576
  | _, _ => none

def SCHEDULE_GexpbyteDragon : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst, SortSchedule.SPURIOUS_DRAGON_EVM => some 50
  | _, _ => none

def SCHEDULE_GaccessliststoragekeyDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gaccessliststoragekey_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GhaschainidDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghaschainid_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GmidDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gmid_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 8
  | _, _ => none

def SCHEDULE_Gsha3wordDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsha3word_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 6
  | _, _ => none

def SCHEDULE_GhasblobbasefeeDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasblobbasefee_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GblockhashDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gblockhash_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 20
  | _, _ => none

def SCHEDULE_GhasdirtysstorePetersburg : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasdirtysstore_SCHEDULE_ScheduleFlag, SortSchedule.PETERSBURG_EVM => some false
  | _, _ => none

def SCHEDULE_GhasblobhashCancun : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasblobhash_SCHEDULE_ScheduleFlag, SortSchedule.CANCUN_EVM => some true
  | _, _ => none

def SCHEDULE_GemptyisnonexistentDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Gemptyisnonexistent_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GwarmstoragereadDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def SCHEDULE_GfroundDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gfround_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 1
  | _, _ => none

def SCHEDULE_GhasextcodehashDefault : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasextcodehash_SCHEDULE_ScheduleFlag, SortSchedule.DEFAULT_EVM => some false
  | _, _ => none

def SCHEDULE_GcoldaccountaccessBerlin : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcoldaccountaccess_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => some 2600
  | _, _ => none

def SCHEDULE_GtransactionDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtransaction_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 21000
  | _, _ => none

def SCHEDULE_GhasdirtysstoreIstanbul : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasdirtysstore_SCHEDULE_ScheduleFlag, SortSchedule.ISTANBUL_EVM => some true
  | _, _ => none

def SCHEDULE_GhasextcodehashConstantinople : SortScheduleFlag → SortSchedule → Option SortBool
  | SortScheduleFlag.Ghasextcodehash_SCHEDULE_ScheduleFlag, SortSchedule.CONSTANTINOPLE_EVM => some true
  | _, _ => none

def SCHEDULE_GbalanceTangerine : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst, SortSchedule.TANGERINE_WHISTLE_EVM => some 400
  | _, _ => none

def SCHEDULE_RselfdestructDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rselfdestruct_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 24000
  | _, _ => none

def SCHEDULE_GmemoryDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gmemory_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 3
  | _, _ => none

def SCHEDULE_GlogtopicDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glogtopic_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 375
  | _, _ => none

def SCHEDULE_GecaddIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gecadd_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 150
  | _, _ => none

def SCHEDULE_GtxdatazeroDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gtxdatazero_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 4
  | _, _ => none

def SCHEDULE_GsloadIstanbul : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.ISTANBUL_EVM => some 800
  | _, _ => none

def SCHEDULE_GwarmstoragedirtystoreDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gwarmstoragedirtystore_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 0
  | _, _ => none

def _1ff8f4d {SortSort : Type} : SortBool → SortSort → SortSort → Option SortSort
  | C, B1, _Gen0 => do
    guard C
    return B1

def SCHEDULE_GlogDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Glog_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 375
  | _, _ => none

def SCHEDULE_GcodedepositDefault : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gcodedeposit_SCHEDULE_ScheduleConst, SortSchedule.DEFAULT_EVM => some 200
  | _, _ => none

def SCHEDULE_GpointevalCancun : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Gpointeval_SCHEDULE_ScheduleConst, SortSchedule.CANCUN_EVM => some 50000
  | _, _ => none

axiom ListItem (x0 : SortKItem) : Option SortList

axiom «_in_keys(_)_MAP_Bool_KItem_Map» (x0 : SortKItem) (x1 : SortMap) : Option SortBool

def _9aad883 : SortInt → SortInt → Option SortInt
  | _Gen0, _Gen1 => some 0

def _8d90a32 : SortMap → SortAccount → SortInt → Option SortBool
  | _Gen0, _Gen1, _Gen2 => some false

def _432e4e6 : SortSet → SortInt → Option SortBool
  | _Gen0, _Gen1 => some false

axiom _MessageCellMap_ (x0 : SortMessageCellMap) (x1 : SortMessageCellMap) : Option SortMessageCellMap

axiom WithdrawalCellMapItem (x0 : SortWithdrawalIDCell) (x1 : SortWithdrawalCell) : Option SortWithdrawalCellMap

axiom «.MessageCellMap» : Option SortMessageCellMap

axiom _Map_ (x0 : SortMap) (x1 : SortMap) : Option SortMap

axiom MessageCellMapItem (x0 : SortMsgIDCell) (x1 : SortMessageCell) : Option SortMessageCellMap

def _a3e3b07 : SortKItem → SortInt → Option SortBool
  | _Gen0, _Gen1 => some false

axiom «Set:in» (x0 : SortKItem) (x1 : SortSet) : Option SortBool

axiom «Map:lookup» (x0 : SortMap) (x1 : SortKItem) : Option SortKItem

def _50d266e : SortInt → SortInt → Option SortInt
  | I1, 1 => some I1
  | _, _ => none

def _5321d80 : SortInt → SortInt → Option SortInt
  | _I1, 0 => some 0
  | _, _ => none

axiom _List_ (x0 : SortList) (x1 : SortList) : Option SortList

axiom «.List» : Option SortList

axiom «Set:difference» (x0 : SortSet) (x1 : SortSet) : Option SortSet

def _75897fa : SortWordStack → SortInt → Option SortInt
  | SortWordStack.«.WordStack_EVM-TYPES_WordStack», SIZE => some SIZE
  | _, _ => none

axiom «_&Int_» (x0 : SortInt) (x1 : SortInt) : Option SortInt

axiom _WithdrawalCellMap_ (x0 : SortWithdrawalCellMap) (x1 : SortWithdrawalCellMap) : Option SortWithdrawalCellMap

axiom «Map:update» (x0 : SortMap) (x1 : SortKItem) (x2 : SortKItem) : Option SortMap

axiom «_|Int_» (x0 : SortInt) (x1 : SortInt) : Option SortInt

def _0e7f507 : SortK → Option SortSet
  | SortK.kseq (SortKItem.inj_SortSet K) SortK.dotk => some K
  | _ => none

axiom «_>>Int_» (x0 : SortInt) (x1 : SortInt) : Option SortInt

axiom _xorInt_ (x0 : SortInt) (x1 : SortInt) : Option SortInt

def _92664aa : SortK → Option SortBool
  | SortK.kseq (SortKItem.inj_SortInt Int) SortK.dotk => some true
  | _ => none

def _105572a : SortK → Option SortBool
  | K => some false

axiom «_|->_» (x0 : SortKItem) (x1 : SortKItem) : Option SortMap

axiom «.Map» : Option SortMap

axiom «_^Int_» (x0 : SortInt) (x1 : SortInt) : Option SortInt

axiom «_%Int_» (x0 : SortInt) (x1 : SortInt) : Option SortInt

axiom _Set_ (x0 : SortSet) (x1 : SortSet) : Option SortSet

def _da5d3b6 : SortInt → SortInt → Option SortInt
  | _Gen0, _Gen1 => some 0

axiom «Map:lookupOrDefault» (x0 : SortMap) (x1 : SortKItem) (x2 : SortKItem) : Option SortKItem

axiom SetItem (x0 : SortKItem) : Option SortSet

axiom AccountCellMapItem (x0 : SortAcctIDCell) (x1 : SortAccountCell) : Option SortAccountCellMap

axiom «.AccountCellMap» : Option SortAccountCellMap

def _6bb6445 : SortInt → SortInt → Option SortInt
  | _Gen0, _Gen1 => some 0

axiom «.Set» : Option SortSet

axiom «.WithdrawalCellMap» : Option SortWithdrawalCellMap

axiom _AccountCellMap_ (x0 : SortAccountCellMap) (x1 : SortAccountCellMap) : Option SortAccountCellMap

def bool2Word (x0 : SortBool) : Option SortInt := (_4bd3e13 x0) <|> (_cb4e96d x0)

def _091b7da : SortInt → SortInt → Option SortInt
  | _I1, I2 => do
    let _Val0 <- «_<=Int_» I2 0
    guard _Val0
    return 0

def _andBool_ (x0 : SortBool) (x1 : SortBool) : Option SortBool := (_5b9db8d x0 x1) <|> (_61fbef3 x0 x1)

def _orBool_ (x0 : SortBool) (x1 : SortBool) : Option SortBool := (_7174452 x0 x1) <|> (_991a329 x0 x1)

def _524eb33 : SortInt → SortInt → Option SortBytes
  | _SIZE, _Gen0 => do
    let _Val0 <- «.Bytes_BYTES-HOOKED_Bytes»
    return _Val0

def _a656ca7 : SortBytes → SortInt → SortBytes → Option SortBytes
  | _Gen0, START, _Gen1 => do
    let _Val0 <- «_<Int_» START 0
    let _Val1 <- «.Bytes_BYTES-HOOKED_Bytes»
    guard _Val0
    return _Val1

def _ea9648a : SortInt → SortEndianness → SortSignedness → Option SortBytes
  | I, _Gen0, _Gen1 => do
    let _Val0 <- «_==Int_» I 0
    let _Val1 <- «.Bytes_BYTES-HOOKED_Bytes»
    guard _Val0
    return _Val1

def _72d6664 : SortInt → SortInt → Option SortInt
  | _Gen0, W1 => do
    let _Val0 <- «_==Int_» W1 0
    guard _Val0
    return 0

def EVM_TYPES_powmod_zero : SortInt → SortInt → SortInt → Option SortInt
  | _Gen0, _Gen1, W2 => do
    let _Val0 <- «_==Int_» W2 0
    guard _Val0
    return 0

def _9bb4fc4 : SortInt → Option SortBool
  | W => do
    let _Val0 <- «_==Int_» W 0
    guard _Val0
    return false

def _952a14b : SortInt → SortInt → Option SortInt
  | _Gen0, W1 => do
    let _Val0 <- «_==Int_» W1 0
    guard _Val0
    return 0

def _f005287 : SortBytes → SortInt → SortInt → Option SortBytes
  | _Gen0, _Gen1, WIDTH => do
    let _Val0 <- «.Bytes_BYTES-HOOKED_Bytes»
    let _Val1 <- «padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» _Val0 WIDTH 0
    return _Val1

def notBool_ (x0 : SortBool) : Option SortBool := (_17ebc68 x0) <|> (_53fc758 x0)

def _85aa67b : SortInt → Option SortInt
  | I => do
    let _Val0 <- _modInt_ I 115792089237316195423570985008687907853269984665640564039457584007913129639936
    return _Val0

def SCHEDULE_RbByzantium : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.BYZANTIUM_EVM => do
    let _Val0 <- «_*Int_» 3 1000000000000000000
    return _Val0
  | _, _ => none

def SCHEDULE_RbConstantinople : SortScheduleConst → SortSchedule → Option SortInt
  | SortScheduleConst.Rb_SCHEDULE_ScheduleConst, SortSchedule.CONSTANTINOPLE_EVM => do
    let _Val0 <- «_*Int_» 2 1000000000000000000
    return _Val0
  | _, _ => none

noncomputable def _9fa39ea : SortInt → SortInt → Option SortInt
  | N, M => do
    let _Val0 <- «_*Int_» 8 M
    let _Val1 <- «_<<Int_» N _Val0
    return _Val1

def _6c109c0 : SortInt → SortEndianness → SortSignedness → Option SortBytes
  | I, E, SortSignedness.signedBytes => do
    let _Val0 <- «_==Int_» I (-1)
    let _Val1 <- «Int2Bytes(_,_,_)_BYTES-HOOKED_Bytes_Int_Int_Endianness» 1 (-1) E
    guard _Val0
    return _Val1
  | _, _, _ => none

noncomputable def _666287e : SortInt → Option SortInt
  | N => do
    let _Val0 <- «_>=Int_» N 0
    let _Val1 <- «_<<Int_» 1 N
    let _Val2 <- «_-Int_» _Val1 1
    guard _Val0
    return _Val2

def _20f05d9 : SortInt → SortEndianness → SortSignedness → Option SortBytes
  | I, E, SortSignedness.signedBytes => do
    let _Val0 <- «_>Int_» I 0
    let _Val1 <- «log2Int(_)_INT-COMMON_Int_Int» I
    let _Val2 <- «_+Int_» _Val1 9
    let _Val3 <- «_/Int_» _Val2 8
    let _Val4 <- «Int2Bytes(_,_,_)_BYTES-HOOKED_Bytes_Int_Int_Endianness» _Val3 I E
    guard _Val0
    return _Val4
  | _, _, _ => none

def _e985b28 : SortInt → SortInt → Option SortInt
  | I1, I2 => do
    let _Val0 <- «_<Int_» 1 I2
    let _Val1 <- «_-Int_» I2 1
    let _Val2 <- «_+Int_» I1 _Val1
    let _Val3 <- «_/Int_» _Val2 I2
    guard _Val0
    return _Val3

def _e9743d5 : SortInt → SortEndianness → SortSignedness → Option SortBytes
  | I, E, SortSignedness.unsignedBytes => do
    let _Val0 <- «_>Int_» I 0
    let _Val1 <- «log2Int(_)_INT-COMMON_Int_Int» I
    let _Val2 <- «_+Int_» _Val1 8
    let _Val3 <- «_/Int_» _Val2 8
    let _Val4 <- «Int2Bytes(_,_,_)_BYTES-HOOKED_Bytes_Int_Int_Endianness» _Val3 I E
    guard _Val0
    return _Val4
  | _, _, _ => none

def _43f856e : SortInt → SortEndianness → SortSignedness → Option SortBytes
  | I, E, SortSignedness.signedBytes => do
    let _Val0 <- «_<Int_» I (-1)
    let _Val1 <- «~Int_» I
    let _Val2 <- «log2Int(_)_INT-COMMON_Int_Int» _Val1
    let _Val3 <- «_+Int_» _Val2 9
    let _Val4 <- «_/Int_» _Val3 8
    let _Val5 <- «Int2Bytes(_,_,_)_BYTES-HOOKED_Bytes_Int_Int_Endianness» _Val4 I E
    guard _Val0
    return _Val5
  | _, _, _ => none

noncomputable def _42ba953 : SortSet → SortInt → Option SortBool
  | KEYS, KEY => do
    let _Val0 <- «Set:in» ((@inj SortInt SortKItem) KEY) KEYS
    guard _Val0
    return true

def _ebfe294 : SortInt → SortBytes → Option SortBytes
  | N, BS => do
    let _Val0 <- «_<=Int_» 0 N
    let _Val1 <- «padLeftBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» BS N 0
    guard _Val0
    return _Val1

mutual
  def _432555e : SortWordStack → SortInt → Option SortInt
    | SortWordStack.«_:__EVM-TYPES_WordStack_Int_WordStack» _Gen0 WS, SIZE => do
      let _Val0 <- «_+Int_» SIZE 1
      let _Val1 <- sizeWordStackAux WS _Val0
      return _Val1
    | _, _ => none

  def sizeWordStackAux (x0 : SortWordStack) (x1 : SortInt) : Option SortInt := (_432555e x0 x1) <|> (_75897fa x0 x1)
end

def «project:Set» (x0 : SortK) : Option SortSet := _0e7f507 x0

noncomputable def _147fc15 : SortInt → SortInt → SortInt → Option SortInt
  | I, IDX, LEN => do
    let _Val0 <- «_>>Int_» I IDX
    let _Val1 <- «_<<Int_» 1 LEN
    let _Val2 <- _modInt_ _Val0 _Val1
    return _Val2

def isInt (x0 : SortK) : Option SortBool := (_92664aa x0) <|> (_105572a x0)

noncomputable def «EVM_TYPES_#lookup_some» : SortMap → SortInt → Option SortInt
  | _Pat0, KEY => match (MapHook SortKItem SortKItem).split _Pat0.coll [SortKItem.inj_SortInt KEY] with
    | some ([SortKItem.inj_SortInt VAL], _M) => do
      let _Val0 <- _modInt_ VAL 115792089237316195423570985008687907853269984665640564039457584007913129639936
      return _Val0
    | _ => none

noncomputable def _c384edb : SortSet → SortSet → Option SortSet
  | S1, S2 => do
    let _Val0 <- «Set:difference» S2 S1
    let _Val1 <- _Set_ S1 _Val0
    return _Val1

def _2b97336 : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- «_<Int_» W0 W1
    let _Val1 <- bool2Word _Val0
    return _Val1

def _296813d : SortInt → Option SortInt
  | I => do
    let _Val0 <- «_<=Int_» 0 I
    let _Val1 <- «_<Int_» I 57896044618658097711785492504343953926634992332820282019728792003956564819968
    let _Val2 <- _andBool_ _Val0 _Val1
    guard _Val2
    return 1

def EVM_TYPES_bytesRange : SortBytes → SortInt → SortInt → Option SortBytes
  | WS, START, WIDTH => do
    let _Val0 <- «_>=Int_» WIDTH 0
    let _Val1 <- «_>=Int_» START 0
    let _Val2 <- _andBool_ _Val0 _Val1
    let _Val3 <- «lengthBytes(_)_BYTES-HOOKED_Int_Bytes» WS
    let _Val4 <- «_<Int_» START _Val3
    let _Val5 <- _andBool_ _Val2 _Val4
    let _Val6 <- «_+Int_» START WIDTH
    let _Val7 <- «padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» WS _Val6 0
    let _Val8 <- «_+Int_» START WIDTH
    let _Val9 <- «substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» _Val7 START _Val8
    guard _Val5
    return _Val9

def _f03fd7e : SortBytes → SortInt → SortBytes → Option SortBytes
  | WS, START, WS' => do
    let _Val0 <- «_<=Int_» 0 START
    let _Val1 <- «lengthBytes(_)_BYTES-HOOKED_Int_Bytes» WS'
    let _Val2 <- «_==Int_» _Val1 0
    let _Val3 <- _andBool_ _Val0 _Val2
    guard _Val3
    return WS

noncomputable def _1102025 : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- «_<=Int_» 0 W0
    let _Val1 <- «_<=Int_» 0 W1
    let _Val2 <- _andBool_ _Val0 _Val1
    let _Val3 <- «_>>Int_» W0 W1
    guard _Val2
    return _Val3

def _7288650 : SortInt → Option SortInt
  | I => do
    let _Val0 <- «_<=Int_» 57896044618658097711785492504343953926634992332820282019728792003956564819968 I
    let _Val1 <- «_<Int_» I 115792089237316195423570985008687907853269984665640564039457584007913129639936
    let _Val2 <- _andBool_ _Val0 _Val1
    guard _Val2
    return (-1)

def _e5bcea9 : SortInt → Option SortInt
  | I => do
    let _Val0 <- «_<Int_» I 0
    let _Val1 <- «_<=Int_» 115792089237316195423570985008687907853269984665640564039457584007913129639936 I
    let _Val2 <- _orBool_ _Val0 _Val1
    guard _Val2
    return 0

-- Necessary to have the following `mutual` block passing without a `decreasing_by` proof
attribute [local simp] SortScheduleFlag.toNat SortSchedule.toNat
def EVM_TYPES_signextend_invalid : SortInt → SortInt → Option SortInt
  | N, W => do
    let _Val0 <- «_>=Int_» N 32
    let _Val1 <- «_<Int_» N 0
    let _Val2 <- _orBool_ _Val0 _Val1
    guard _Val2
    return W

def _8096892 : SortInt → SortInt → SortInt → Option SortInt
  | MU, _Gen0, WIDTH => do
    let _Val0 <- «_<Int_» 0 WIDTH
    let _Val1 <- notBool_ _Val0
    guard _Val1
    return MU

noncomputable def «EVM_TYPES_#lookup_none» : SortMap → SortInt → Option SortInt
  | M, KEY => do
    let _Val0 <- «_in_keys(_)_MAP_Bool_KItem_Map» ((@inj SortInt SortKItem) KEY) M
    let _Val1 <- notBool_ _Val0
    guard _Val1
    return 0

def _91eab34 : SortInt → SortInt → Option SortInt
  | N, _Gen0 => do
    let _Val0 <- «_>=Int_» N 0
    let _Val1 <- «_<Int_» N 256
    let _Val2 <- _andBool_ _Val0 _Val1
    let _Val3 <- notBool_ _Val2
    guard _Val3
    return 0

mutual
  noncomputable def SCHEDULE_SCHEDFLAGTangerine : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.TANGERINE_WHISTLE_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Gselfdestructnewaccount_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Gstaticcalldepth_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- notBool_ _Val2
      let _Val4 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.HOMESTEAD_EVM
      guard _Val3
      return _Val4
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDFLAGConstantinople : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.CONSTANTINOPLE_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasshift_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasdirtysstore_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghascreate2_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasextcodehash_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val6 <- _orBool_ _Val4 _Val5
      let _Val7 <- notBool_ _Val6
      let _Val8 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.BYZANTIUM_EVM
      guard _Val7
      return _Val8
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDFLAGHomestead : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.HOMESTEAD_EVM => do
      let _Val0 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.DEFAULT_EVM
      return _Val0
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDFLAGShanghai : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.SHANGHAI_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasmaxinitcodesize_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghaspushzero_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghaswarmcoinbase_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghaswithdrawals_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val6 <- _orBool_ _Val4 _Val5
      let _Val7 <- notBool_ _Val6
      let _Val8 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.MERGE_EVM
      guard _Val7
      return _Val8
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDFLAGPetersburg : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.PETERSBURG_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasdirtysstore_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.CONSTANTINOPLE_EVM
      guard _Val1
      return _Val2
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDFLAGByzantium : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.BYZANTIUM_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasrevert_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasreturndata_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasstaticcall_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- notBool_ _Val4
      let _Val6 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.SPURIOUS_DRAGON_EVM
      guard _Val5
      return _Val6
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDFLAGIstanbul : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.ISTANBUL_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasselfbalance_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasdirtysstore_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghassstorestipend_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghaschainid_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val6 <- _orBool_ _Val4 _Val5
      let _Val7 <- notBool_ _Val6
      let _Val8 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.PETERSBURG_EVM
      guard _Val7
      return _Val8
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDFLAGDragon : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.SPURIOUS_DRAGON_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Gemptyisnonexistent_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Gzerovaluenewaccountgas_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- notBool_ _Val2
      let _Val4 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.TANGERINE_WHISTLE_EVM
      guard _Val3
      return _Val4
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDFLAGMerge : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.MERGE_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasprevrandao_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.LONDON_EVM
      guard _Val1
      return _Val2
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDFLAGFrontier : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.FRONTIER_EVM => do
      let _Val0 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.DEFAULT_EVM
      return _Val0
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» (x0 : SortScheduleFlag) (x1 : SortSchedule) : Option SortBool := (SCHEDULE_GemptyisnonexistentDefault x0 x1) <|> (SCHEDULE_GemptyisnonexistentDragon x0 x1) <|> (SCHEDULE_GhasaccesslistDefault x0 x1) <|> (SCHEDULE_GhasbasefeeDefault x0 x1) <|> (SCHEDULE_GhasbasefeeLondon x0 x1) <|> (SCHEDULE_GhasbeaconrootCancun x0 x1) <|> (SCHEDULE_GhasbeaconrootDefault x0 x1) <|> (SCHEDULE_GhasblobbasefeeCancun x0 x1) <|> (SCHEDULE_GhasblobbasefeeDefault x0 x1) <|> (SCHEDULE_GhasblobhashCancun x0 x1) <|> (SCHEDULE_GhasblobhashDefault x0 x1) <|> (SCHEDULE_GhaschainidDefault x0 x1) <|> (SCHEDULE_GhaschainidIstanbul x0 x1) <|> (SCHEDULE_Ghascreate2Constantinople x0 x1) <|> (SCHEDULE_Ghascreate2Default x0 x1) <|> (SCHEDULE_GhasdirtysstoreConstantinople x0 x1) <|> (SCHEDULE_GhasdirtysstoreDefault x0 x1) <|> (SCHEDULE_GhasdirtysstoreIstanbul x0 x1) <|> (SCHEDULE_GhasdirtysstorePetersburg x0 x1) <|> (SCHEDULE_Ghaseip6780Cancun x0 x1) <|> (SCHEDULE_Ghaseip6780Default x0 x1) <|> (SCHEDULE_GhasextcodehashConstantinople x0 x1) <|> (SCHEDULE_GhasextcodehashDefault x0 x1) <|> (SCHEDULE_GhasmaxinitcodesizeDefault x0 x1) <|> (SCHEDULE_GhasmaxinitcodesizeShanghai x0 x1) <|> (SCHEDULE_GhasmcopyCancun x0 x1) <|> (SCHEDULE_GhasmcopyDefault x0 x1) <|> (SCHEDULE_GhasprevrandaoDefault x0 x1) <|> (SCHEDULE_GhasprevrandaoMerge x0 x1) <|> (SCHEDULE_GhaspushzeroDefault x0 x1) <|> (SCHEDULE_GhaspushzeroShanghai x0 x1) <|> (SCHEDULE_GhasrejectedfirstbyteDefault x0 x1) <|> (SCHEDULE_GhasrejectedfirstbyteLondon x0 x1) <|> (SCHEDULE_GhasreturndataByzantium x0 x1) <|> (SCHEDULE_GhasreturndataDefault x0 x1) <|> (SCHEDULE_GhasrevertByzantium x0 x1) <|> (SCHEDULE_GhasrevertDefault x0 x1) <|> (SCHEDULE_GhasselfbalanceDefault x0 x1) <|> (SCHEDULE_GhasselfbalanceIstanbul x0 x1) <|> (SCHEDULE_GhasshiftConstantinople x0 x1) <|> (SCHEDULE_GhasshiftDefault x0 x1) <|> (SCHEDULE_GhassstorestipendDefault x0 x1) <|> (SCHEDULE_GhassstorestipendIstanbul x0 x1) <|> (SCHEDULE_GhasstaticcallByzantium x0 x1) <|> (SCHEDULE_GhasstaticcallDefault x0 x1) <|> (SCHEDULE_GhastransientCancun x0 x1) <|> (SCHEDULE_GhastransientDefault x0 x1) <|> (SCHEDULE_GhaswarmcoinbaseDefault x0 x1) <|> (SCHEDULE_GhaswarmcoinbaseShanghai x0 x1) <|> (SCHEDULE_GhaswithdrawalsDefault x0 x1) <|> (SCHEDULE_GhaswithdrawalsShanghai x0 x1) <|> (SCHEDULE_GselfdestructnewaccountDefault x0 x1) <|> (SCHEDULE_GselfdestructnewaccountTangerine x0 x1) <|> (SCHEDULE_GstaticcalldepthDefault x0 x1) <|> (SCHEDULE_GstaticcalldepthTangerine x0 x1) <|> (SCHEDULE_GzerovaluenewaccountgasDefault x0 x1) <|> (SCHEDULE_GzerovaluenewaccountgasDragon x0 x1) <|> (SCHEDULE_SCHEDFLAGBerlin x0 x1) <|> (SCHEDULE_SCHEDFLAGByzantium x0 x1) <|> (SCHEDULE_SCHEDFLAGCancun x0 x1) <|> (SCHEDULE_SCHEDFLAGConstantinople x0 x1) <|> (SCHEDULE_SCHEDFLAGDragon x0 x1) <|> (SCHEDULE_SCHEDFLAGFrontier x0 x1) <|> (SCHEDULE_SCHEDFLAGHomestead x0 x1) <|> (SCHEDULE_SCHEDFLAGIstanbul x0 x1) <|> (SCHEDULE_SCHEDFLAGLondon x0 x1) <|> (SCHEDULE_SCHEDFLAGMerge x0 x1) <|> (SCHEDULE_SCHEDFLAGPetersburg x0 x1) <|> (SCHEDULE_SCHEDFLAGShanghai x0 x1) <|> (SCHEDULE_SCHEDFLAGTangerine x0 x1) <|> (SCHEDULE_hasaccesslistBerlin x0 x1)
  termination_by (x1.toNat, x0.toNat + 1)

  noncomputable def SCHEDULE_SCHEDFLAGBerlin : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.BERLIN_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasaccesslist_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.ISTANBUL_EVM
      guard _Val1
      return _Val2
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDFLAGLondon : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.LONDON_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasbasefee_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasrejectedfirstbyte_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- notBool_ _Val2
      let _Val4 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.BERLIN_EVM
      guard _Val3
      return _Val4
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDFLAGCancun : SortScheduleFlag → SortSchedule → Option SortBool
    | SCHEDFLAG, SortSchedule.CANCUN_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghastransient_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasmcopy_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasbeaconroot_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghaseip6780_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val6 <- _orBool_ _Val4 _Val5
      let _Val7 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasblobbasefee_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val8 <- _orBool_ _Val6 _Val7
      let _Val9 <- «_==K_» (SortK.kseq ((@inj SortScheduleFlag SortKItem) SCHEDFLAG) SortK.dotk) (SortK.kseq ((@inj SortScheduleFlag SortKItem) SortScheduleFlag.Ghasblobhash_SCHEDULE_ScheduleFlag) SortK.dotk)
      let _Val10 <- _orBool_ _Val8 _Val9
      let _Val11 <- notBool_ _Val10
      let _Val12 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SCHEDFLAG SortSchedule.SHANGHAI_EVM
      guard _Val11
      return _Val12
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)
end

def _67678cd : SortInt → SortBytes → Option SortBytes
  | N, BS => do
    let _Val0 <- «_<=Int_» 0 N
    let _Val1 <- notBool_ _Val0
    guard _Val1
    return BS

def _2f3f58a {SortSort : Type} : SortBool → SortSort → SortSort → Option SortSort
  | C, _Gen0, B2 => do
    let _Val0 <- notBool_ C
    guard _Val0
    return B2

def _4ddfe21 : SortInt → SortInt → Option SortInt
  | N, _Gen0 => do
    let _Val0 <- «_>=Int_» N 0
    let _Val1 <- «_<Int_» N 32
    let _Val2 <- _andBool_ _Val0 _Val1
    let _Val3 <- notBool_ _Val2
    guard _Val3
    return 0

noncomputable def _bccaba7 : SortK → SortK → Option SortBool
  | K1, K2 => do
    let _Val0 <- «_==K_» K1 K2
    let _Val1 <- notBool_ _Val0
    return _Val1

def _4de6e05 : SortInt → SortInt → Option SortBool
  | I1, I2 => do
    let _Val0 <- «_==Int_» I1 I2
    let _Val1 <- notBool_ _Val0
    return _Val1

def _ecc9011 : SortBytes → SortInt → SortInt → Option SortBytes
  | _Gen0, START, WIDTH => do
    let _Val0 <- «_>=Int_» WIDTH 0
    let _Val1 <- «_>=Int_» START 0
    let _Val2 <- _andBool_ _Val0 _Val1
    let _Val3 <- notBool_ _Val2
    let _Val4 <- «.Bytes_BYTES-HOOKED_Bytes»
    guard _Val3
    return _Val4

def chop (x0 : SortInt) : Option SortInt := _85aa67b x0

noncomputable def «_<<Byte__WORD_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := _9fa39ea x0 x1

noncomputable def «#nBits» (x0 : SortInt) : Option SortInt := _666287e x0

def «_up/Int__EVM-TYPES_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := (_091b7da x0 x1) <|> (_50d266e x0 x1) <|> (_5321d80 x0 x1) <|> (_e985b28 x0 x1)

def Int2BytesNoLen (x0 : SortInt) (x1 : SortEndianness) (x2 : SortSignedness) : Option SortBytes := (_20f05d9 x0 x1 x2) <|> (_43f856e x0 x1 x2) <|> (_6c109c0 x0 x1 x2) <|> (_e9743d5 x0 x1 x2) <|> (_ea9648a x0 x1 x2)

noncomputable def «#inStorageAux2» (x0 : SortSet) (x1 : SortInt) : Option SortBool := (_42ba953 x0 x1) <|> (_432e4e6 x0 x1)

noncomputable def «bitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) (x2 : SortInt) : Option SortInt := _147fc15 x0 x1 x2

noncomputable def «EVM_TYPES_#lookup_notInt» : SortMap → SortInt → Option SortInt
  | _Pat0, KEY => match (MapHook SortKItem SortKItem).split _Pat0.coll [SortKItem.inj_SortInt KEY] with
    | some ([VAL], _M) => do
      let _Val0 <- isInt (SortK.kseq VAL SortK.dotk)
      let _Val1 <- notBool_ _Val0
      guard _Val1
      return 0
    | _ => none

noncomputable def «_|Set__SET_Set_Set_Set» (x0 : SortSet) (x1 : SortSet) : Option SortSet := _c384edb x0 x1

def «_<Word__EVM-TYPES_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := _2b97336 x0 x1

noncomputable def «_>>Word__EVM-TYPES_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := (_1102025 x0 x1) <|> (_da5d3b6 x0 x1)

def sgn (x0 : SortInt) : Option SortInt := (_296813d x0) <|> (_7288650 x0) <|> (_e5bcea9 x0)

def «#padToWidth» (x0 : SortInt) (x1 : SortBytes) : Option SortBytes := (_67678cd x0 x1) <|> (_ebfe294 x0 x1)

def kite {SortSort : Type} (x0 : SortBool) (x1 : SortSort) (x2 : SortSort) : Option SortSort := (_1ff8f4d x0 x1 x2) <|> (_2f3f58a x0 x1 x2)

noncomputable def «_=/=K_» (x0 : SortK) (x1 : SortK) : Option SortBool := _bccaba7 x0 x1

def «_=/=Int_» (x0 : SortInt) (x1 : SortInt) : Option SortBool := _4de6e05 x0 x1

def «#range» (x0 : SortBytes) (x1 : SortInt) (x2 : SortInt) : Option SortBytes := (EVM_TYPES_bytesRange x0 x1 x2) <|> (_ecc9011 x0 x1 x2) <|> (_f005287 x0 x1 x2)

noncomputable def _ead1b39 : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- «_<=Int_» 0 W0
    let _Val1 <- «_<=Int_» 0 W1
    let _Val2 <- _andBool_ _Val0 _Val1
    let _Val3 <- «_<Int_» W1 256
    let _Val4 <- _andBool_ _Val2 _Val3
    let _Val5 <- «_<<Int_» W0 W1
    let _Val6 <- chop _Val5
    guard _Val4
    return _Val6

def _6d530d5 : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- «_-Int_» W0 W1
    let _Val1 <- chop _Val0
    return _Val1

def _ef5332a : SortBytes → Option SortInt
  | WS => do
    let _Val0 <- «Bytes2Int(_,_,_)_BYTES-HOOKED_Int_Bytes_Endianness_Signedness» WS SortEndianness.bigEndianBytes SortSignedness.unsignedBytes
    let _Val1 <- chop _Val0
    return _Val1

noncomputable def _b7189da : SortInt → Option SortInt
  | N => do
    let _Val0 <- «_>=Int_» N 0
    let _Val1 <- «_*Int_» 8 N
    let _Val2 <- «#nBits» _Val1
    guard _Val0
    return _Val2

def _86ca6df : SortInt → SortInt → SortInt → Option SortInt
  | MU, START, WIDTH => do
    let _Val0 <- «_<Int_» 0 WIDTH
    let _Val1 <- «_+Int_» START WIDTH
    let _Val2 <- «_up/Int__EVM-TYPES_Int_Int_Int» _Val1 32
    let _Val3 <- «maxInt(_,_)_INT-COMMON_Int_Int_Int» MU _Val2
    guard _Val0
    return _Val3

def _fdd6ce1 : SortInt → Option SortBytes
  | W => do
    let _Val0 <- Int2BytesNoLen W SortEndianness.bigEndianBytes SortSignedness.unsignedBytes
    return _Val0

noncomputable def _c44ca69 : SortKItem → SortInt → Option SortBool
  | SortKItem.inj_SortSet KEYS, KEY => do
    let _Val0 <- «#inStorageAux2» KEYS KEY
    return _Val0
  | _, _ => none

noncomputable def _40c7ccb : SortInt → SortInt → Option SortInt
  | N, W => do
    let _Val0 <- «_>=Int_» N 0
    let _Val1 <- «_<Int_» N 32
    let _Val2 <- _andBool_ _Val0 _Val1
    let _Val3 <- «_-Int_» 31 N
    let _Val4 <- «_*Int_» 8 _Val3
    let _Val5 <- «bitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int» W _Val4 8
    guard _Val2
    return _Val5

noncomputable def _685a458 : SortInt → SortInt → Option SortInt
  | N, W => do
    let _Val0 <- «_>=Int_» N 0
    let _Val1 <- «_<Int_» N 256
    let _Val2 <- _andBool_ _Val0 _Val1
    let _Val3 <- «_-Int_» 255 N
    let _Val4 <- «bitRangeInt(_,_,_)_INT-COMMON_Int_Int_Int_Int» W _Val3 1
    guard _Val2
    return _Val4

noncomputable def lookup (x0 : SortMap) (x1 : SortInt) : Option SortInt := («EVM_TYPES_#lookup_none» x0 x1) <|> («EVM_TYPES_#lookup_notInt» x0 x1) <|> («EVM_TYPES_#lookup_some» x0 x1)

noncomputable def «EVM_TYPES_s<Word_pp» : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- sgn W0
    let _Val1 <- «_==K_» (SortK.kseq ((@inj SortInt SortKItem) _Val0) SortK.dotk) (SortK.kseq ((@inj SortInt SortKItem) 1) SortK.dotk)
    let _Val2 <- sgn W1
    let _Val3 <- «_==K_» (SortK.kseq ((@inj SortInt SortKItem) _Val2) SortK.dotk) (SortK.kseq ((@inj SortInt SortKItem) 1) SortK.dotk)
    let _Val4 <- _andBool_ _Val1 _Val3
    let _Val5 <- «_<Word__EVM-TYPES_Int_Int_Int» W0 W1
    guard _Val4
    return _Val5

def _504aa89 : SortInt → Option SortInt
  | I => do
    let _Val0 <- sgn I
    let _Val1 <- «_==Int_» _Val0 1
    guard _Val1
    return I

noncomputable def «EVM_TYPES_s<Word_np» : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- sgn W0
    let _Val1 <- «_==K_» (SortK.kseq ((@inj SortInt SortKItem) _Val0) SortK.dotk) (SortK.kseq ((@inj SortInt SortKItem) (-1)) SortK.dotk)
    let _Val2 <- sgn W1
    let _Val3 <- «_==K_» (SortK.kseq ((@inj SortInt SortKItem) _Val2) SortK.dotk) (SortK.kseq ((@inj SortInt SortKItem) 1) SortK.dotk)
    let _Val4 <- _andBool_ _Val1 _Val3
    let _Val5 <- bool2Word true
    guard _Val4
    return _Val5

noncomputable def «EVM_TYPES_s<Word_pn» : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- sgn W0
    let _Val1 <- «_==K_» (SortK.kseq ((@inj SortInt SortKItem) _Val0) SortK.dotk) (SortK.kseq ((@inj SortInt SortKItem) 1) SortK.dotk)
    let _Val2 <- sgn W1
    let _Val3 <- «_==K_» (SortK.kseq ((@inj SortInt SortKItem) _Val2) SortK.dotk) (SortK.kseq ((@inj SortInt SortKItem) (-1)) SortK.dotk)
    let _Val4 <- _andBool_ _Val1 _Val3
    let _Val5 <- bool2Word false
    guard _Val4
    return _Val5

def _4dc3a9c : SortInt → Option SortInt
  | I => do
    let _Val0 <- sgn I
    let _Val1 <- «_==Int_» _Val0 0
    guard _Val1
    return 0

-- Necessary to have the following `mutual` block passing without a `decreasing_by` proof
attribute [local simp] SortScheduleConst.toNat
mutual
  noncomputable def SCHEDULE_GsstoreresetBerlin : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst SortSchedule.BERLIN_EVM
      let _Val1 <- «_-Int_» 5000 _Val0
      return _Val1
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTMerge : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.MERGE_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rb_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.LONDON_EVM
      guard _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTTangerine : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.TANGERINE_WHISTLE_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gsload_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gcall_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gselfdestruct_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val6 <- _orBool_ _Val4 _Val5
      let _Val7 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gextcodesize_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val8 <- _orBool_ _Val6 _Val7
      let _Val9 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gextcodecopy_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val10 <- _orBool_ _Val8 _Val9
      let _Val11 <- notBool_ _Val10
      let _Val12 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.HOMESTEAD_EVM
      guard _Val11
      return _Val12
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTByzantium : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.BYZANTIUM_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rb_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.SPURIOUS_DRAGON_EVM
      guard _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTDragon : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.SPURIOUS_DRAGON_EVM => do
      let _Val0 <- «_=/=K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gexpbyte_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_=/=K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _andBool_ _Val0 _Val1
      let _Val3 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.TANGERINE_WHISTLE_EVM
      guard _Val2
      return _Val3
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_GsloadBerlin : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Gsload_SCHEDULE_ScheduleConst, SortSchedule.BERLIN_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SortSchedule.BERLIN_EVM
      return _Val0
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTBerlin : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.BERLIN_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gcoldsload_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gcoldaccountaccess_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gsload_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val6 <- _orBool_ _Val4 _Val5
      let _Val7 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val8 <- _orBool_ _Val6 _Val7
      let _Val9 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gquaddivisor_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val10 <- _orBool_ _Val8 _Val9
      let _Val11 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gaccessliststoragekey_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val12 <- _orBool_ _Val10 _Val11
      let _Val13 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gaccesslistaddress_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val14 <- _orBool_ _Val12 _Val13
      let _Val15 <- notBool_ _Val14
      let _Val16 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.ISTANBUL_EVM
      guard _Val15
      return _Val16
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_GwarmstoragedirtystoreCancun : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Gwarmstoragedirtystore_SCHEDULE_ScheduleConst, SortSchedule.CANCUN_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gwarmstorageread_SCHEDULE_ScheduleConst SortSchedule.CANCUN_EVM
      return _Val0
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTPetersburg : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.PETERSBURG_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.CONSTANTINOPLE_EVM
      return _Val0
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTLondon : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.LONDON_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rselfdestruct_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rmaxquotient_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- notBool_ _Val4
      let _Val6 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.BERLIN_EVM
      guard _Val5
      return _Val6
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTIstanbul : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.ISTANBUL_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gecadd_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gecmul_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gecpairconst_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val4 <- _orBool_ _Val2 _Val3
      let _Val5 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gecpaircoeff_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val6 <- _orBool_ _Val4 _Val5
      let _Val7 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gtxdatanonzero_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val8 <- _orBool_ _Val6 _Val7
      let _Val9 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gsload_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val10 <- _orBool_ _Val8 _Val9
      let _Val11 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gbalance_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val12 <- _orBool_ _Val10 _Val11
      let _Val13 <- notBool_ _Val12
      let _Val14 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.PETERSBURG_EVM
      guard _Val13
      return _Val14
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» (x0 : SortScheduleConst) (x1 : SortSchedule) : Option SortInt := (SCHEDULE_GaccesslistaddressBerlin x0 x1) <|> (SCHEDULE_GaccesslistaddressDefault x0 x1) <|> (SCHEDULE_GaccessliststoragekeyBerlin x0 x1) <|> (SCHEDULE_GaccessliststoragekeyDefault x0 x1) <|> (SCHEDULE_GbalanceDefault x0 x1) <|> (SCHEDULE_GbalanceIstanbul x0 x1) <|> (SCHEDULE_GbalanceTangerine x0 x1) <|> (SCHEDULE_GbaseDefault x0 x1) <|> (SCHEDULE_GblockhashDefault x0 x1) <|> (SCHEDULE_GcallDefault x0 x1) <|> (SCHEDULE_GcallTangerine x0 x1) <|> (SCHEDULE_GcallstipendDefault x0 x1) <|> (SCHEDULE_GcallvalueDefault x0 x1) <|> (SCHEDULE_GcodedepositDefault x0 x1) <|> (SCHEDULE_GcoldaccountaccessBerlin x0 x1) <|> (SCHEDULE_GcoldaccountaccessDefault x0 x1) <|> (SCHEDULE_GcoldsloadBerlin x0 x1) <|> (SCHEDULE_GcoldsloadDefault x0 x1) <|> (SCHEDULE_GcopyDefault x0 x1) <|> (SCHEDULE_GcreateDefault x0 x1) <|> (SCHEDULE_GecaddDefault x0 x1) <|> (SCHEDULE_GecaddIstanbul x0 x1) <|> (SCHEDULE_GecmulDefault x0 x1) <|> (SCHEDULE_GecmulIstanbul x0 x1) <|> (SCHEDULE_GecpaircoeffDefault x0 x1) <|> (SCHEDULE_GecpaircoeffIstanbul x0 x1) <|> (SCHEDULE_GecpairconstDefault x0 x1) <|> (SCHEDULE_GecpairconstIstanbul x0 x1) <|> (SCHEDULE_GexpDefault x0 x1) <|> (SCHEDULE_GexpbyteDefault x0 x1) <|> (SCHEDULE_GexpbyteDragon x0 x1) <|> (SCHEDULE_GextcodecopyDefault x0 x1) <|> (SCHEDULE_GextcodecopyTangerine x0 x1) <|> (SCHEDULE_GextcodesizeDefault x0 x1) <|> (SCHEDULE_GextcodesizeTangerine x0 x1) <|> (SCHEDULE_GfroundDefault x0 x1) <|> (SCHEDULE_GhighDefault x0 x1) <|> (SCHEDULE_GinitcodewordcostDefault x0 x1) <|> (SCHEDULE_GinitcodewordcostShanghai x0 x1) <|> (SCHEDULE_GjumpdestDefault x0 x1) <|> (SCHEDULE_GlogDefault x0 x1) <|> (SCHEDULE_GlogdataDefault x0 x1) <|> (SCHEDULE_GlogtopicDefault x0 x1) <|> (SCHEDULE_GlowDefault x0 x1) <|> (SCHEDULE_GmemoryDefault x0 x1) <|> (SCHEDULE_GmidDefault x0 x1) <|> (SCHEDULE_GnewaccountDefault x0 x1) <|> (SCHEDULE_GpointevalCancun x0 x1) <|> (SCHEDULE_GpointevalDefault x0 x1) <|> (SCHEDULE_GquadcoeffDefault x0 x1) <|> (SCHEDULE_GquaddivisorBerlin x0 x1) <|> (SCHEDULE_GquaddivisorDefault x0 x1) <|> (SCHEDULE_GselfdestructDefault x0 x1) <|> (SCHEDULE_GselfdestructTangerine x0 x1) <|> (SCHEDULE_Gsha3Default x0 x1) <|> (SCHEDULE_Gsha3wordDefault x0 x1) <|> (SCHEDULE_GsloadBerlin x0 x1) <|> (SCHEDULE_GsloadDefault x0 x1) <|> (SCHEDULE_GsloadIstanbul x0 x1) <|> (SCHEDULE_GsloadTangerine x0 x1) <|> (SCHEDULE_GsstoreresetBerlin x0 x1) <|> (SCHEDULE_GsstoreresetDefault x0 x1) <|> (SCHEDULE_GsstoresetDefault x0 x1) <|> (SCHEDULE_GtransactionDefault x0 x1) <|> (SCHEDULE_GtxcreateDefault x0 x1) <|> (SCHEDULE_GtxcreateFrontier x0 x1) <|> (SCHEDULE_GtxdatanonzeroDefault x0 x1) <|> (SCHEDULE_GtxdatanonzeroIstanbul x0 x1) <|> (SCHEDULE_GtxdatazeroDefault x0 x1) <|> (SCHEDULE_GverylowDefault x0 x1) <|> (SCHEDULE_GwarmstoragedirtystoreCancun x0 x1) <|> (SCHEDULE_GwarmstoragedirtystoreDefault x0 x1) <|> (SCHEDULE_GwarmstoragereadBerlin x0 x1) <|> (SCHEDULE_GwarmstoragereadDefault x0 x1) <|> (SCHEDULE_GzeroDefault x0 x1) <|> (SCHEDULE_RbByzantium x0 x1) <|> (SCHEDULE_RbConstantinople x0 x1) <|> (SCHEDULE_RbDefault x0 x1) <|> (SCHEDULE_RbMerge x0 x1) <|> (SCHEDULE_RmaxquotientDefault x0 x1) <|> (SCHEDULE_RmaxquotientLondon x0 x1) <|> (SCHEDULE_RselfdestructDefault x0 x1) <|> (SCHEDULE_RselfdestructLondon x0 x1) <|> (SCHEDULE_RsstoreclearDefault x0 x1) <|> (SCHEDULE_RsstoreclearLondon x0 x1) <|> (SCHEDULE_SCHEDCONSTBerlin x0 x1) <|> (SCHEDULE_SCHEDCONSTByzantium x0 x1) <|> (SCHEDULE_SCHEDCONSTCancun x0 x1) <|> (SCHEDULE_SCHEDCONSTConstantinople x0 x1) <|> (SCHEDULE_SCHEDCONSTDragon x0 x1) <|> (SCHEDULE_SCHEDCONSTFrontier x0 x1) <|> (SCHEDULE_SCHEDCONSTHomestead x0 x1) <|> (SCHEDULE_SCHEDCONSTIstanbul x0 x1) <|> (SCHEDULE_SCHEDCONSTLondon x0 x1) <|> (SCHEDULE_SCHEDCONSTMerge x0 x1) <|> (SCHEDULE_SCHEDCONSTPetersburg x0 x1) <|> (SCHEDULE_SCHEDCONSTShanghai x0 x1) <|> (SCHEDULE_SCHEDCONSTTangerine x0 x1) <|> (SCHEDULE_maxCodeSizeDefault x0 x1) <|> (SCHEDULE_maxCodeSizeDragon x0 x1) <|> (SCHEDULE_maxInitCodeSizeDefault x0 x1) <|> (SCHEDULE_maxInitCodeSizeShanghai x0 x1)
  termination_by (x1.toNat, x0.toNat + 1)

  noncomputable def SCHEDULE_RsstoreclearLondon : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst, SortSchedule.LONDON_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst SortSchedule.LONDON_EVM
      let _Val1 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gaccessliststoragekey_SCHEDULE_ScheduleConst SortSchedule.LONDON_EVM
      let _Val2 <- «_+Int_» _Val0 _Val1
      return _Val2
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_maxInitCodeSizeShanghai : SortScheduleConst → SortSchedule → Option SortInt
    | SortScheduleConst.maxInitCodeSize_SCHEDULE_ScheduleConst, SortSchedule.SHANGHAI_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.maxCodeSize_SCHEDULE_ScheduleConst SortSchedule.SHANGHAI_EVM
      let _Val1 <- «_*Int_» 2 _Val0
      return _Val1
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTShanghai : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.SHANGHAI_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.maxInitCodeSize_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Ginitcodewordcost_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- notBool_ _Val2
      let _Val4 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.MERGE_EVM
      guard _Val3
      return _Val4
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTFrontier : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.FRONTIER_EVM => do
      let _Val0 <- «_=/=K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gtxcreate_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.DEFAULT_EVM
      guard _Val0
      return _Val1
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTCancun : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.CANCUN_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gwarmstoragedirtystore_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Gpointeval_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val2 <- _orBool_ _Val0 _Val1
      let _Val3 <- notBool_ _Val2
      let _Val4 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.SHANGHAI_EVM
      guard _Val3
      return _Val4
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTConstantinople : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.CONSTANTINOPLE_EVM => do
      let _Val0 <- «_==K_» (SortK.kseq ((@inj SortScheduleConst SortKItem) SCHEDCONST) SortK.dotk) (SortK.kseq ((@inj SortScheduleConst SortKItem) SortScheduleConst.Rb_SCHEDULE_ScheduleConst) SortK.dotk)
      let _Val1 <- notBool_ _Val0
      let _Val2 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.BYZANTIUM_EVM
      guard _Val1
      return _Val2
    | _, _ => none
  termination_by sc s => (s.toNat, sc.toNat)

  noncomputable def SCHEDULE_SCHEDCONSTHomestead : SortScheduleConst → SortSchedule → Option SortInt
    | SCHEDCONST, SortSchedule.HOMESTEAD_EVM => do
      let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SCHEDCONST SortSchedule.DEFAULT_EVM
      return _Val0
    | _, _ => none
    termination_by sc s => (s.toNat, sc.toNat)
end

def _8391694 : SortBytes → SortInt → SortBytes → Option SortBytes
  | WS, START, WS' => do
    let _Val0 <- «_<=Int_» 0 START
    let _Val1 <- «lengthBytes(_)_BYTES-HOOKED_Int_Bytes» WS'
    let _Val2 <- «_=/=Int_» _Val1 0
    let _Val3 <- _andBool_ _Val0 _Val2
    let _Val4 <- «lengthBytes(_)_BYTES-HOOKED_Int_Bytes» WS'
    let _Val5 <- «_+Int_» START _Val4
    let _Val6 <- «padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int» WS _Val5 0
    let _Val7 <- «replaceAtBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Bytes» _Val6 START WS'
    guard _Val3
    return _Val7

def _08b1484 : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- «_=/=Int_» W1 0
    let _Val1 <- _modInt_ W0 W1
    guard _Val0
    return _Val1

def EVM_TYPES_powmod_nonzero : SortInt → SortInt → SortInt → Option SortInt
  | W0, W1, W2 => do
    let _Val0 <- «_=/=Int_» W2 0
    let _Val1 <- «_^%Int__» W0 W1 W2
    guard _Val0
    return _Val1

def _19cae79 : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- «_=/=Int_» W1 0
    let _Val1 <- «_/Int_» W0 W1
    guard _Val0
    return _Val1

def _209173a : SortInt → Option SortBool
  | W => do
    let _Val0 <- «_=/=Int_» W 0
    guard _Val0
    return true

noncomputable def «_<<Word__EVM-TYPES_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := (_ead1b39 x0 x1) <|> (_6bb6445 x0 x1)

def «_-Word__EVM-TYPES_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := _6d530d5 x0 x1

def asWord (x0 : SortBytes) : Option SortInt := _ef5332a x0

noncomputable def «#nBytes» (x0 : SortInt) : Option SortInt := _b7189da x0

def «#memoryUsageUpdate» (x0 : SortInt) (x1 : SortInt) (x2 : SortInt) : Option SortInt := (_8096892 x0 x1 x2) <|> (_86ca6df x0 x1 x2)

def «#asByteStack» (x0 : SortInt) : Option SortBytes := _fdd6ce1 x0

noncomputable def «#inStorageAux1» (x0 : SortKItem) (x1 : SortInt) : Option SortBool := (_c44ca69 x0 x1) <|> (_a3e3b07 x0 x1)

noncomputable def byte (x0 : SortInt) (x1 : SortInt) : Option SortInt := (_40c7ccb x0 x1) <|> (_4ddfe21 x0 x1)

noncomputable def bit (x0 : SortInt) (x1 : SortInt) : Option SortInt := (_685a458 x0 x1) <|> (_91eab34 x0 x1)

noncomputable def GAS_FEES_Csstore_old : SortSchedule → SortInt → SortInt → SortInt → Option SortInt
  | SCHED, NEW, CURR, _ORIG => do
    let _Val0 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SortScheduleFlag.Ghasdirtysstore_SCHEDULE_ScheduleFlag SCHED
    let _Val1 <- notBool_ _Val0
    let _Val2 <- «_==Int_» CURR 0
    let _Val3 <- «_=/=Int_» NEW 0
    let _Val4 <- _andBool_ _Val2 _Val3
    let _Val5 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gsstoreset_SCHEDULE_ScheduleConst SCHED
    let _Val6 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst SCHED
    let _Val7 <- kite _Val4 _Val5 _Val6
    guard _Val1
    return _Val7

noncomputable def GAS_FEES_Rsstore_old : SortSchedule → SortInt → SortInt → SortInt → Option SortInt
  | SCHED, NEW, CURR, _ORIG => do
    let _Val0 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SortScheduleFlag.Ghasdirtysstore_SCHEDULE_ScheduleFlag SCHED
    let _Val1 <- notBool_ _Val0
    let _Val2 <- «_=/=Int_» CURR 0
    let _Val3 <- «_==Int_» NEW 0
    let _Val4 <- _andBool_ _Val2 _Val3
    let _Val5 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst SCHED
    let _Val6 <- kite _Val4 _Val5 0
    guard _Val1
    return _Val6

noncomputable def GAS_FEES_Rsstore_new : SortSchedule → SortInt → SortInt → SortInt → Option SortInt
  | SCHED, NEW, CURR, ORIG => do
    let _Val0 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SortScheduleFlag.Ghasdirtysstore_SCHEDULE_ScheduleFlag SCHED
    let _Val1 <- «_=/=Int_» CURR NEW
    let _Val2 <- «_==Int_» ORIG CURR
    let _Val3 <- _andBool_ _Val1 _Val2
    let _Val4 <- «_==Int_» NEW 0
    let _Val5 <- _andBool_ _Val3 _Val4
    let _Val6 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst SCHED
    let _Val7 <- «_=/=Int_» CURR NEW
    let _Val8 <- «_=/=Int_» ORIG CURR
    let _Val9 <- _andBool_ _Val7 _Val8
    let _Val10 <- «_=/=Int_» ORIG 0
    let _Val11 <- _andBool_ _Val9 _Val10
    let _Val12 <- «_==Int_» CURR 0
    let _Val13 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst SCHED
    let _Val14 <- «_-Int_» 0 _Val13
    let _Val15 <- «_==Int_» NEW 0
    let _Val16 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Rsstoreclear_SCHEDULE_ScheduleConst SCHED
    let _Val17 <- kite _Val15 _Val16 0
    let _Val18 <- kite _Val12 _Val14 _Val17
    let _Val19 <- kite _Val11 _Val18 0
    let _Val20 <- «_=/=Int_» CURR NEW
    let _Val21 <- «_==Int_» ORIG NEW
    let _Val22 <- _andBool_ _Val20 _Val21
    let _Val23 <- «_==Int_» ORIG 0
    let _Val24 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gsstoreset_SCHEDULE_ScheduleConst SCHED
    let _Val25 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst SCHED
    let _Val26 <- kite _Val23 _Val24 _Val25
    let _Val27 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gsload_SCHEDULE_ScheduleConst SCHED
    let _Val28 <- «_-Int_» _Val26 _Val27
    let _Val29 <- kite _Val22 _Val28 0
    let _Val30 <- «_+Int_» _Val19 _Val29
    let _Val31 <- kite _Val5 _Val6 _Val30
    guard _Val0
    return _Val31

noncomputable def GAS_FEES_Csstore_new : SortSchedule → SortInt → SortInt → SortInt → Option SortInt
  | SCHED, NEW, CURR, ORIG => do
    let _Val0 <- «_<<_>>_SCHEDULE_Bool_ScheduleFlag_Schedule» SortScheduleFlag.Ghasdirtysstore_SCHEDULE_ScheduleFlag SCHED
    let _Val1 <- «_==Int_» CURR NEW
    let _Val2 <- «_=/=Int_» ORIG CURR
    let _Val3 <- _orBool_ _Val1 _Val2
    let _Val4 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gsload_SCHEDULE_ScheduleConst SCHED
    let _Val5 <- «_==Int_» ORIG 0
    let _Val6 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gsstoreset_SCHEDULE_ScheduleConst SCHED
    let _Val7 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gsstorereset_SCHEDULE_ScheduleConst SCHED
    let _Val8 <- kite _Val5 _Val6 _Val7
    let _Val9 <- kite _Val3 _Val4 _Val8
    guard _Val0
    return _Val9

noncomputable def GAS_FEES_Cmem : SortSchedule → SortInt → Option SortInt
  | SCHED, N => do
    let _Val0 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gmemory_SCHEDULE_ScheduleConst SCHED
    let _Val1 <- «_*Int_» N _Val0
    let _Val2 <- «_*Int_» N N
    let _Val3 <- «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» SortScheduleConst.Gquadcoeff_SCHEDULE_ScheduleConst SCHED
    let _Val4 <- «_/Int_» _Val2 _Val3
    let _Val5 <- «_+Int_» _Val1 _Val4
    return _Val5

def mapWriteRange (x0 : SortBytes) (x1 : SortInt) (x2 : SortBytes) : Option SortBytes := (_8391694 x0 x1 x2) <|> (_a656ca7 x0 x1 x2) <|> (_f03fd7e x0 x1 x2)

def «_%Word__EVM-TYPES_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := (_08b1484 x0 x1) <|> (_952a14b x0 x1)

def powmod (x0 : SortInt) (x1 : SortInt) (x2 : SortInt) : Option SortInt := (EVM_TYPES_powmod_nonzero x0 x1 x2) <|> (EVM_TYPES_powmod_zero x0 x1 x2)

def «_/Word__EVM-TYPES_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := (_19cae79 x0 x1) <|> (_72d6664 x0 x1)

def word2Bool (x0 : SortInt) : Option SortBool := (_209173a x0) <|> (_9bb4fc4 x0)

def _64e87c1 : SortInt → Option SortInt
  | I => do
    let _Val0 <- sgn I
    let _Val1 <- «_==Int_» _Val0 (-1)
    let _Val2 <- «_-Word__EVM-TYPES_Int_Int_Int» 0 I
    guard _Val1
    return _Val2

noncomputable def _23563a4 : SortInt → SortInt → Option SortBytes
  | SIZE, DATA => do
    let _Val0 <- «_<Int_» 0 SIZE
    let _Val1 <- «_*Int_» 8 SIZE
    let _Val2 <- «_^Int_» 2 _Val1
    let _Val3 <- «_%Int_» DATA _Val2
    let _Val4 <- «#asByteStack» _Val3
    let _Val5 <- «#padToWidth» SIZE _Val4
    guard _Val0
    return _Val5

noncomputable def _dbb1f9e : SortMap → SortAccount → SortInt → Option SortBool
  | TS, ACCT, KEY => do
    let _Val0 <- «_in_keys(_)_MAP_Bool_KItem_Map» ((@inj SortAccount SortKItem) ACCT) TS
    let _Val1 <- «Map:lookup» TS ((@inj SortAccount SortKItem) ACCT)
    let _Val2 <- «#inStorageAux1» _Val1 KEY
    guard _Val0
    return _Val2

noncomputable def Rsstore (x0 : SortSchedule) (x1 : SortInt) (x2 : SortInt) (x3 : SortInt) : Option SortInt := (GAS_FEES_Rsstore_new x0 x1 x2 x3) <|> (GAS_FEES_Rsstore_old x0 x1 x2 x3)

noncomputable def Csstore (x0 : SortSchedule) (x1 : SortInt) (x2 : SortInt) (x3 : SortInt) : Option SortInt := (GAS_FEES_Csstore_new x0 x1 x2 x3) <|> (GAS_FEES_Csstore_old x0 x1 x2 x3)

noncomputable def Cmem (x0 : SortSchedule) (x1 : SortInt) : Option SortInt := GAS_FEES_Cmem x0 x1

noncomputable def EVM_TYPES_signextend_negative : SortInt → SortInt → Option SortInt
  | N, W => do
    let _Val0 <- «_<Int_» N 32
    let _Val1 <- «_>=Int_» N 0
    let _Val2 <- _andBool_ _Val0 _Val1
    let _Val3 <- «_+Int_» N 1
    let _Val4 <- «_*Int_» 8 _Val3
    let _Val5 <- «_-Int_» 256 _Val4
    let _Val6 <- bit _Val5 W
    let _Val7 <- word2Bool _Val6
    let _Val8 <- _andBool_ _Val2 _Val7
    let _Val9 <- «_-Int_» 31 N
    let _Val10 <- «#nBytes» _Val9
    let _Val11 <- «_+Int_» N 1
    let _Val12 <- «_<<Byte__WORD_Int_Int_Int» _Val10 _Val11
    let _Val13 <- «_|Int_» _Val12 W
    let _Val14 <- chop _Val13
    guard _Val8
    return _Val14

noncomputable def EVM_TYPES_signextend_positive : SortInt → SortInt → Option SortInt
  | N, W => do
    let _Val0 <- «_<Int_» N 32
    let _Val1 <- «_>=Int_» N 0
    let _Val2 <- _andBool_ _Val0 _Val1
    let _Val3 <- «_+Int_» N 1
    let _Val4 <- «_*Int_» 8 _Val3
    let _Val5 <- «_-Int_» 256 _Val4
    let _Val6 <- bit _Val5 W
    let _Val7 <- word2Bool _Val6
    let _Val8 <- notBool_ _Val7
    let _Val9 <- _andBool_ _Val2 _Val8
    let _Val10 <- «_+Int_» N 1
    let _Val11 <- «#nBytes» _Val10
    let _Val12 <- «_&Int_» _Val11 W
    let _Val13 <- chop _Val12
    guard _Val9
    return _Val13

def kabs (x0 : SortInt) : Option SortInt := (_4dc3a9c x0) <|> (_504aa89 x0) <|> (_64e87c1 x0)

noncomputable def buf (x0 : SortInt) (x1 : SortInt) : Option SortBytes := (_23563a4 x0 x1) <|> (_524eb33 x0 x1)

noncomputable def «#inStorage» (x0 : SortMap) (x1 : SortAccount) (x2 : SortInt) : Option SortBool := (_dbb1f9e x0 x1 x2) <|> (_8d90a32 x0 x1 x2)

noncomputable def signextend (x0 : SortInt) (x1 : SortInt) : Option SortInt := (EVM_TYPES_signextend_invalid x0 x1) <|> (EVM_TYPES_signextend_negative x0 x1) <|> (EVM_TYPES_signextend_positive x0 x1)

def EVM_TYPES_modSWord_pos : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- sgn W0
    let _Val1 <- «_==Int_» _Val0 1
    let _Val2 <- kabs W0
    let _Val3 <- kabs W1
    let _Val4 <- «_%Word__EVM-TYPES_Int_Int_Int» _Val2 _Val3
    guard _Val1
    return _Val4

def EVM_TYPES_modSWord_neg : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- sgn W0
    let _Val1 <- «_==Int_» _Val0 (-1)
    let _Val2 <- kabs W0
    let _Val3 <- kabs W1
    let _Val4 <- «_%Word__EVM-TYPES_Int_Int_Int» _Val2 _Val3
    let _Val5 <- «_-Word__EVM-TYPES_Int_Int_Int» 0 _Val4
    guard _Val1
    return _Val5

def EVM_TYPES_divSWord_diff : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- sgn W0
    let _Val1 <- sgn W1
    let _Val2 <- «_*Int_» _Val0 _Val1
    let _Val3 <- «_==Int_» _Val2 (-1)
    let _Val4 <- kabs W0
    let _Val5 <- kabs W1
    let _Val6 <- «_/Word__EVM-TYPES_Int_Int_Int» _Val4 _Val5
    let _Val7 <- «_-Word__EVM-TYPES_Int_Int_Int» 0 _Val6
    guard _Val3
    return _Val7

noncomputable def _d40d616 : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- «_<=Int_» 0 W0
    let _Val1 <- «_<=Int_» 0 W1
    let _Val2 <- _andBool_ _Val0 _Val1
    let _Val3 <- kabs W0
    let _Val4 <- sgn W0
    let _Val5 <- «_*Int_» _Val3 _Val4
    let _Val6 <- «_>>Int_» _Val5 W1
    let _Val7 <- chop _Val6
    guard _Val2
    return _Val7

noncomputable def «EVM_TYPES_s<Word_nn» : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- sgn W0
    let _Val1 <- «_==K_» (SortK.kseq ((@inj SortInt SortKItem) _Val0) SortK.dotk) (SortK.kseq ((@inj SortInt SortKItem) (-1)) SortK.dotk)
    let _Val2 <- sgn W1
    let _Val3 <- «_==K_» (SortK.kseq ((@inj SortInt SortKItem) _Val2) SortK.dotk) (SortK.kseq ((@inj SortInt SortKItem) (-1)) SortK.dotk)
    let _Val4 <- _andBool_ _Val1 _Val3
    let _Val5 <- kabs W1
    let _Val6 <- kabs W0
    let _Val7 <- «_<Word__EVM-TYPES_Int_Int_Int» _Val5 _Val6
    guard _Val4
    return _Val7

def EVM_TYPES_divSWord_same : SortInt → SortInt → Option SortInt
  | W0, W1 => do
    let _Val0 <- sgn W0
    let _Val1 <- sgn W1
    let _Val2 <- «_*Int_» _Val0 _Val1
    let _Val3 <- «_==Int_» _Val2 1
    let _Val4 <- kabs W0
    let _Val5 <- kabs W1
    let _Val6 <- «_/Word__EVM-TYPES_Int_Int_Int» _Val4 _Val5
    guard _Val3
    return _Val6

def «_%sWord__EVM-TYPES_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := (EVM_TYPES_modSWord_neg x0 x1) <|> (EVM_TYPES_modSWord_pos x0 x1)

noncomputable def «_>>sWord__EVM-TYPES_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := (_d40d616 x0 x1) <|> (_9aad883 x0 x1)

noncomputable def «_s<Word__EVM-TYPES_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := («EVM_TYPES_s<Word_nn» x0 x1) <|> («EVM_TYPES_s<Word_np» x0 x1) <|> («EVM_TYPES_s<Word_pn» x0 x1) <|> («EVM_TYPES_s<Word_pp» x0 x1)

def «_/sWord__EVM-TYPES_Int_Int_Int» (x0 : SortInt) (x1 : SortInt) : Option SortInt := (EVM_TYPES_divSWord_diff x0 x1) <|> (EVM_TYPES_divSWord_same x0 x1)