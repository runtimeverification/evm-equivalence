import EvmEquivalence.KEVM2Lean.Sorts

namespace SortSchedule

def toNat (s : SortSchedule) : Nat :=
  match s with
  | DEFAULT_EVM           => 0
  | FRONTIER_EVM          => 1
  | HOMESTEAD_EVM         => 2
  | TANGERINE_WHISTLE_EVM => 3
  | SPURIOUS_DRAGON_EVM   => 4
  | BYZANTIUM_EVM         => 5
  | CONSTANTINOPLE_EVM    => 6
  | PETERSBURG_EVM        => 7
  | ISTANBUL_EVM          => 8
  | BERLIN_EVM            => 9
  | LONDON_EVM            => 10
  | MERGE_EVM             => 11
  | SHANGHAI_EVM          => 12
  | CANCUN_EVM            => 13

end SortSchedule

namespace SortScheduleConst

def toNat (sc : SortScheduleConst) : Nat :=
  match sc with
  | Gaccesslistaddress_SCHEDULE_ScheduleConst     => 4
  | Gaccessliststoragekey_SCHEDULE_ScheduleConst  => 2
  | Gbalance_SCHEDULE_ScheduleConst               => 4
  | Gbase_SCHEDULE_ScheduleConst                  => 4
  | Gblockhash_SCHEDULE_ScheduleConst             => 4
  | Gcall_SCHEDULE_ScheduleConst                  => 4
  | Gcallstipend_SCHEDULE_ScheduleConst           => 4
  | Gcallvalue_SCHEDULE_ScheduleConst             => 4
  | Gcodedeposit_SCHEDULE_ScheduleConst           => 4
  | Gcoldaccountaccess_SCHEDULE_ScheduleConst     => 4
  | Gcoldsload_SCHEDULE_ScheduleConst             => 0
  | Gcopy_SCHEDULE_ScheduleConst                  => 4
  | Gcreate_SCHEDULE_ScheduleConst                => 4
  | Gecadd_SCHEDULE_ScheduleConst                 => 4
  | Gecmul_SCHEDULE_ScheduleConst                 => 4
  | Gecpaircoeff_SCHEDULE_ScheduleConst           => 4
  | Gecpairconst_SCHEDULE_ScheduleConst           => 4
  | Gexp_SCHEDULE_ScheduleConst                   => 4
  | Gexpbyte_SCHEDULE_ScheduleConst               => 4
  | Gextcodecopy_SCHEDULE_ScheduleConst           => 4
  | Gextcodesize_SCHEDULE_ScheduleConst           => 4
  | Gfround_SCHEDULE_ScheduleConst                => 4
  | Ghigh_SCHEDULE_ScheduleConst                  => 4
  | Ginitcodewordcost_SCHEDULE_ScheduleConst      => 4
  | Gjumpdest_SCHEDULE_ScheduleConst              => 4
  | Glog_SCHEDULE_ScheduleConst                   => 4
  | Glogdata_SCHEDULE_ScheduleConst               => 4
  | Glogtopic_SCHEDULE_ScheduleConst              => 4
  | Glow_SCHEDULE_ScheduleConst                   => 4
  | Gmemory_SCHEDULE_ScheduleConst                => 4
  | Gmid_SCHEDULE_ScheduleConst                   => 4
  | Gnewaccount_SCHEDULE_ScheduleConst            => 4
  | Gquadcoeff_SCHEDULE_ScheduleConst             => 4
  | Gquaddivisor_SCHEDULE_ScheduleConst           => 4
  | Gselfdestruct_SCHEDULE_ScheduleConst          => 4
  | Gsha3_SCHEDULE_ScheduleConst                  => 4
  | Gsha3word_SCHEDULE_ScheduleConst              => 4
  | Gsload_SCHEDULE_ScheduleConst                 => 4
  | Gsstorereset_SCHEDULE_ScheduleConst           => 2
  | Gsstoreset_SCHEDULE_ScheduleConst             => 4
  | Gtransaction_SCHEDULE_ScheduleConst           => 4
  | Gtxcreate_SCHEDULE_ScheduleConst              => 4
  | Gtxdatanonzero_SCHEDULE_ScheduleConst         => 4
  | Gtxdatazero_SCHEDULE_ScheduleConst            => 4
  | Gverylow_SCHEDULE_ScheduleConst               => 4
  | Gwarmstoragedirtystore_SCHEDULE_ScheduleConst => 4
  | Gwarmstorageread_SCHEDULE_ScheduleConst       => 2
  | Gzero_SCHEDULE_ScheduleConst                  => 4
  | Rb_SCHEDULE_ScheduleConst                     => 4
  | Rmaxquotient_SCHEDULE_ScheduleConst           => 4
  | Rselfdestruct_SCHEDULE_ScheduleConst          => 4
  | Rsstoreclear_SCHEDULE_ScheduleConst           => 4
  | maxCodeSize_SCHEDULE_ScheduleConst            => 2
  | maxInitCodeSize_SCHEDULE_ScheduleConst        => 4
  | Gpointeval_SCHEDULE_ScheduleConst             => 4

end SortScheduleConst

namespace SortScheduleFlag

def toNat (sf : SortScheduleFlag) : Nat :=
  match sf with
  | Gemptyisnonexistent_SCHEDULE_ScheduleFlag     => 1
  | Ghasaccesslist_SCHEDULE_ScheduleFlag          => 1
  | Ghasbasefee_SCHEDULE_ScheduleFlag             => 1
  | Ghasbeaconroot_SCHEDULE_ScheduleFlag          => 1
  | Ghasblobbasefee_SCHEDULE_ScheduleFlag         => 1
  | Ghasblobhash_SCHEDULE_ScheduleFlag            => 1
  | Ghaschainid_SCHEDULE_ScheduleFlag             => 1
  | Ghascreate2_SCHEDULE_ScheduleFlag             => 1
  | Ghasdirtysstore_SCHEDULE_ScheduleFlag         => 1
  | Ghaseip6780_SCHEDULE_ScheduleFlag             => 1
  | Ghasextcodehash_SCHEDULE_ScheduleFlag         => 1
  | Ghasmaxinitcodesize_SCHEDULE_ScheduleFlag     => 1
  | Ghasmcopy_SCHEDULE_ScheduleFlag               => 1
  | Ghasprevrandao_SCHEDULE_ScheduleFlag          => 1
  | Ghaspushzero_SCHEDULE_ScheduleFlag            => 1
  | Ghasrejectedfirstbyte_SCHEDULE_ScheduleFlag   => 1
  | Ghasreturndata_SCHEDULE_ScheduleFlag          => 1
  | Ghasrevert_SCHEDULE_ScheduleFlag              => 1
  | Ghasselfbalance_SCHEDULE_ScheduleFlag         => 1
  | Ghasshift_SCHEDULE_ScheduleFlag               => 1
  | Ghassstorestipend_SCHEDULE_ScheduleFlag       => 1
  | Ghasstaticcall_SCHEDULE_ScheduleFlag          => 1
  | Ghastransient_SCHEDULE_ScheduleFlag           => 1
  | Ghaswarmcoinbase_SCHEDULE_ScheduleFlag        => 1
  | Ghaswithdrawals_SCHEDULE_ScheduleFlag         => 1
  | Gselfdestructnewaccount_SCHEDULE_ScheduleFlag => 1
  | Gstaticcalldepth_SCHEDULE_ScheduleFlag        => 1
  | Gzerovaluenewaccountgas_SCHEDULE_ScheduleFlag => 1

end SortScheduleFlag
