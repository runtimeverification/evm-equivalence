/-
Interface for the `«_<_>_SCHEDULE_Int_ScheduleConst_Schedule»` function
 -/
import EvmEquivalence.Interfaces.FuncInterface
import EvmEquivalence.Interfaces.Tactics

namespace GasInterface

open KEVMInterface

attribute [local simp] Option.bind.eq_def
attribute [local simp] plusIntIsSome mulIntIsSome subIntIsSome
attribute [local simp] Keq_def Kneq_def
attribute [local simp] orBool_def andBool_def notBool_def

variable (const : SortScheduleConst)

-- These should be temporary axioms
instance: DecidableEq SortK := fun
  | .dotk => sorry
  | .kseq x0 x1 => sorry
instance: LawfulBEq SortK where
  eq_of_beq := sorry
  rfl := sorry

@[local simp]
theorem neq_gconst_fls (c₁ c₂ : SortScheduleConst) : c₁ ≠ c₂ →
  (SortK.kseq (inj c₁) SortK.dotk == SortK.kseq (inj c₂) SortK.dotk) = false := by
  simp [ne_eq, beq_eq_false_iff_ne, SortK.kseq.injEq, and_true, inj, Inj.inj]

@[local simp]
theorem neq_gconst_true (c₁ c₂ : SortScheduleConst) : c₁ ≠ c₂ →
  (SortK.kseq (inj c₁) SortK.dotk != SortK.kseq (inj c₂) SortK.dotk) := by
    aesop (add simp [bne])

set_option maxRecDepth 100000

@[local simp]
theorem sched_default_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .DEFAULT_EVM =
  match const with
  | .Gzero_SCHEDULE_ScheduleConst                  => some 0
  | .Gbase_SCHEDULE_ScheduleConst                  => some 2
  | .Gverylow_SCHEDULE_ScheduleConst               => some 3
  | .Glow_SCHEDULE_ScheduleConst                   => some 5
  | .Gmid_SCHEDULE_ScheduleConst                   => some 8
  | .Ghigh_SCHEDULE_ScheduleConst                  => some 10
  | .Gexp_SCHEDULE_ScheduleConst                   => some 10
  | .Gexpbyte_SCHEDULE_ScheduleConst               => some 10
  | .Gsha3_SCHEDULE_ScheduleConst                  => some 30
  | .Gsha3word_SCHEDULE_ScheduleConst              => some 6
  | .Gsload_SCHEDULE_ScheduleConst                 => some 50
  | .Gsstoreset_SCHEDULE_ScheduleConst             => some 20000
  | .Gsstorereset_SCHEDULE_ScheduleConst           => some 5000
  | .Rsstoreclear_SCHEDULE_ScheduleConst           => some 15000
  | .Glog_SCHEDULE_ScheduleConst                   => some 375
  | .Glogdata_SCHEDULE_ScheduleConst               => some 8
  | .Glogtopic_SCHEDULE_ScheduleConst              => some 375
  | .Gcall_SCHEDULE_ScheduleConst                  => some 40
  | .Gcallstipend_SCHEDULE_ScheduleConst           => some 2300
  | .Gcallvalue_SCHEDULE_ScheduleConst             => some 9000
  | .Gnewaccount_SCHEDULE_ScheduleConst            => some 25000
  | .Gcreate_SCHEDULE_ScheduleConst                => some 32000
  | .Gcodedeposit_SCHEDULE_ScheduleConst           => some 200
  | .Gselfdestruct_SCHEDULE_ScheduleConst          => some 0
  | .Rselfdestruct_SCHEDULE_ScheduleConst          => some 24000
  | .Gmemory_SCHEDULE_ScheduleConst                => some 3
  | .Gquadcoeff_SCHEDULE_ScheduleConst             => some 512
  | .Gcopy_SCHEDULE_ScheduleConst                  => some 3
  | .Gquaddivisor_SCHEDULE_ScheduleConst           => some 20
  | .Gtransaction_SCHEDULE_ScheduleConst           => some 21000
  | .Gtxcreate_SCHEDULE_ScheduleConst              => some 53000
  | .Gtxdatazero_SCHEDULE_ScheduleConst            => some 4
  | .Gtxdatanonzero_SCHEDULE_ScheduleConst         => some 68
  | .Gjumpdest_SCHEDULE_ScheduleConst              => some 1
  | .Gbalance_SCHEDULE_ScheduleConst               => some 20
  | .Gblockhash_SCHEDULE_ScheduleConst             => some 20
  | .Gextcodesize_SCHEDULE_ScheduleConst           => some 20
  | .Gextcodecopy_SCHEDULE_ScheduleConst           => some 20
  | .Gecadd_SCHEDULE_ScheduleConst                 => some 500
  | .Gecmul_SCHEDULE_ScheduleConst                 => some 40000
  | .Gecpairconst_SCHEDULE_ScheduleConst           => some 100000
  | .Gecpaircoeff_SCHEDULE_ScheduleConst           => some 80000
  | .Gfround_SCHEDULE_ScheduleConst                => some 1
  | .maxCodeSize_SCHEDULE_ScheduleConst            => some 4294967295 --2 ^ 32 - 1
  | .Rb_SCHEDULE_ScheduleConst                     => some 5000000000000000000 --5 *Int (10 ^Int   18)
  | .Gcoldsload_SCHEDULE_ScheduleConst             => some 0
  | .Gcoldaccountaccess_SCHEDULE_ScheduleConst     => some 0
  | .Gwarmstorageread_SCHEDULE_ScheduleConst       => some 0
  | .Gwarmstoragedirtystore_SCHEDULE_ScheduleConst => some 0
  | .Gaccessliststoragekey_SCHEDULE_ScheduleConst  => some 0
  | .Gaccesslistaddress_SCHEDULE_ScheduleConst     => some 0
  | .maxInitCodeSize_SCHEDULE_ScheduleConst        => some 0
  | .Ginitcodewordcost_SCHEDULE_ScheduleConst      => some 0
  | .Rmaxquotient_SCHEDULE_ScheduleConst           => some 2
  | .Gpointeval_SCHEDULE_ScheduleConst => some 0
  := by
  simp_schedule1; cases const <;> simp_schedule2

@[local simp]
theorem sched_frontier_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .FRONTIER_EVM =
  match const with
  | .Gtxcreate_SCHEDULE_ScheduleConst => some 21000
  | const => «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .DEFAULT_EVM := by
  simp_schedule1; cases const <;> simp_schedule2

@[local simp]
theorem sched_homestead_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .HOMESTEAD_EVM =
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .DEFAULT_EVM := by
  simp_schedule1; cases const <;> simp_schedule2

@[local simp]
theorem sched_tangerine_whistle_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .TANGERINE_WHISTLE_EVM =
  match const with
  | .Gbalance_SCHEDULE_ScheduleConst      => some 400
  | .Gsload_SCHEDULE_ScheduleConst        => some 200
  | .Gcall_SCHEDULE_ScheduleConst         => some 700
  | .Gselfdestruct_SCHEDULE_ScheduleConst => some 5000
  | .Gextcodesize_SCHEDULE_ScheduleConst  => some 700
  | .Gextcodecopy_SCHEDULE_ScheduleConst  => some 700
  | const => «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .HOMESTEAD_EVM := by
  simp_schedule1; cases const <;> simp_schedule2

@[local simp]
theorem sched_spurious_dragon_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .SPURIOUS_DRAGON_EVM =
  match const with
  | .Gexpbyte_SCHEDULE_ScheduleConst      => some 50
  | .maxCodeSize_SCHEDULE_ScheduleConst   => some 24576
  | const => «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .TANGERINE_WHISTLE_EVM := by
  simp_schedule1; cases const <;> simp_schedule2

@[local simp]
theorem sched_bythantium_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .BYZANTIUM_EVM =
  match const with
  | .Rb_SCHEDULE_ScheduleConst => some 3000000000000000000
  | const => «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .SPURIOUS_DRAGON_EVM := by
  simp_schedule1; cases const <;> simp_schedule2

@[local simp]
theorem sched_constantinople_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .CONSTANTINOPLE_EVM =
  match const with
  | .Rb_SCHEDULE_ScheduleConst => some 2000000000000000000
  | const => «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .BYZANTIUM_EVM := by
  simp_schedule1; cases const <;> simp_schedule2

@[local simp]
theorem sched_petersburg_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .PETERSBURG_EVM =
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .CONSTANTINOPLE_EVM := by
  simp_schedule1; cases const <;> simp_schedule2

@[local simp]
theorem sched_istanbul_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .ISTANBUL_EVM =
  match const with
  | .Gecadd_SCHEDULE_ScheduleConst         => some 150
  | .Gecmul_SCHEDULE_ScheduleConst         => some 6000
  | .Gecpairconst_SCHEDULE_ScheduleConst   => some 45000
  | .Gecpaircoeff_SCHEDULE_ScheduleConst   => some 34000
  | .Gtxdatanonzero_SCHEDULE_ScheduleConst => some 16
  | .Gsload_SCHEDULE_ScheduleConst         => some 800
  | .Gbalance_SCHEDULE_ScheduleConst       => some 700
  | const => «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .PETERSBURG_EVM := by
  simp_schedule1; cases const <;> simp_schedule2

attribute [local simp] SCHEDULE_GsloadBerlin SCHEDULE_GsstoreresetBerlin

@[local simp]
theorem sched_berlin_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .BERLIN_EVM =
  match const with
  | .Gcoldsload_SCHEDULE_ScheduleConst            => some 2100
  | .Gcoldaccountaccess_SCHEDULE_ScheduleConst    => some 2600
  | .Gwarmstorageread_SCHEDULE_ScheduleConst      => some 100
  | .Gsload_SCHEDULE_ScheduleConst                => some 100
  | .Gsstorereset_SCHEDULE_ScheduleConst          => some 2900
  | .Gquaddivisor_SCHEDULE_ScheduleConst          => some 3
  | .Gaccessliststoragekey_SCHEDULE_ScheduleConst => some 1900
  | .Gaccesslistaddress_SCHEDULE_ScheduleConst    => some 2400
  | const => «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .ISTANBUL_EVM := by
  simp_schedule1; cases const <;> simp_schedule2
  simp_schedule1; simp_schedule2
  simp [«_<_>_SCHEDULE_Int_ScheduleConst_Schedule»];
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
  simp [SCHEDULE_GcoldsloadBerlin]

@[local simp]
theorem sched_london_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .LONDON_EVM =
  match const with
  | .Rselfdestruct_SCHEDULE_ScheduleConst => some 0
  | .Rsstoreclear_SCHEDULE_ScheduleConst  => some 4800
  | .Rmaxquotient_SCHEDULE_ScheduleConst  => some 5
  | const => «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .BERLIN_EVM := by
  simp_schedule1; cases const <;> simp_schedule2
  simp_schedule1; simp_schedule2

@[local simp]
theorem sched_merge_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .MERGE_EVM =
  match const with
  | .Rb_SCHEDULE_ScheduleConst => some 0
  | const => «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .LONDON_EVM := by
  simp_schedule1; cases const <;> simp_schedule2

@[local simp]
theorem sched_shanghai_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .SHANGHAI_EVM =
  match const with
  | .maxInitCodeSize_SCHEDULE_ScheduleConst   => some 49152
  | .Ginitcodewordcost_SCHEDULE_ScheduleConst => some 2
  | const => «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .MERGE_EVM := by
  simp_schedule1; cases const <;> simp_schedule2
  simp_schedule1; simp_schedule2

@[local simp]
theorem sched_cancun_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .CANCUN_EVM =
  match const with
  | .Gwarmstoragedirtystore_SCHEDULE_ScheduleConst => some 100
  | .Gpointeval_SCHEDULE_ScheduleConst => some 50000
  | const => «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .SHANGHAI_EVM := by
  simp_schedule1; cases const <;> simp_schedule2
  simp_schedule1; simp_schedule2

@[simp]
theorem cancun_def :
  «_<_>_SCHEDULE_Int_ScheduleConst_Schedule» const .CANCUN_EVM =
  match const with
  | .Gzero_SCHEDULE_ScheduleConst                  => some 0
  | .Gbase_SCHEDULE_ScheduleConst                  => some 2
  | .Gverylow_SCHEDULE_ScheduleConst               => some 3
  | .Glow_SCHEDULE_ScheduleConst                   => some 5
  | .Gmid_SCHEDULE_ScheduleConst                   => some 8
  | .Ghigh_SCHEDULE_ScheduleConst                  => some 10
  | .Gexp_SCHEDULE_ScheduleConst                   => some 10
  | .Gexpbyte_SCHEDULE_ScheduleConst               => some 50
  | .Gsha3_SCHEDULE_ScheduleConst                  => some 30
  | .Gsha3word_SCHEDULE_ScheduleConst              => some 6
  | .Gsload_SCHEDULE_ScheduleConst                 => some 100
  | .Gsstoreset_SCHEDULE_ScheduleConst             => some 20000
  | .Gsstorereset_SCHEDULE_ScheduleConst           => some 2900
  | .Rsstoreclear_SCHEDULE_ScheduleConst           => some 4800
  | .Glog_SCHEDULE_ScheduleConst                   => some 375
  | .Glogdata_SCHEDULE_ScheduleConst               => some 8
  | .Glogtopic_SCHEDULE_ScheduleConst              => some 375
  | .Gcall_SCHEDULE_ScheduleConst                  => some 700
  | .Gcallstipend_SCHEDULE_ScheduleConst           => some 2300
  | .Gcallvalue_SCHEDULE_ScheduleConst             => some 9000
  | .Gnewaccount_SCHEDULE_ScheduleConst            => some 25000
  | .Gcreate_SCHEDULE_ScheduleConst                => some 32000
  | .Gcodedeposit_SCHEDULE_ScheduleConst           => some 200
  | .Gselfdestruct_SCHEDULE_ScheduleConst          => some 5000
  | .Rselfdestruct_SCHEDULE_ScheduleConst          => some 0
  | .Gmemory_SCHEDULE_ScheduleConst                => some 3
  | .Gquadcoeff_SCHEDULE_ScheduleConst             => some 512
  | .Gcopy_SCHEDULE_ScheduleConst                  => some 3
  | .Gquaddivisor_SCHEDULE_ScheduleConst           => some 3
  | .Gtransaction_SCHEDULE_ScheduleConst           => some 21000
  | .Gtxcreate_SCHEDULE_ScheduleConst              => some 53000
  | .Gtxdatazero_SCHEDULE_ScheduleConst            => some 4
  | .Gtxdatanonzero_SCHEDULE_ScheduleConst         => some 16
  | .Gjumpdest_SCHEDULE_ScheduleConst              => some 1
  | .Gbalance_SCHEDULE_ScheduleConst               => some 700
  | .Gblockhash_SCHEDULE_ScheduleConst             => some 20
  | .Gextcodesize_SCHEDULE_ScheduleConst           => some 700
  | .Gextcodecopy_SCHEDULE_ScheduleConst           => some 700
  | .Gecadd_SCHEDULE_ScheduleConst                 => some 150
  | .Gecmul_SCHEDULE_ScheduleConst                 => some 6000
  | .Gecpairconst_SCHEDULE_ScheduleConst           => some 45000
  | .Gecpaircoeff_SCHEDULE_ScheduleConst           => some 34000
  | .Gfround_SCHEDULE_ScheduleConst                => some 1
  | .maxCodeSize_SCHEDULE_ScheduleConst            => some 24576
  | .Rb_SCHEDULE_ScheduleConst                     => some 0
  | .Gcoldsload_SCHEDULE_ScheduleConst             => some 2100
  | .Gcoldaccountaccess_SCHEDULE_ScheduleConst     => some 2600
  | .Gwarmstorageread_SCHEDULE_ScheduleConst       => some 100
  | .Gwarmstoragedirtystore_SCHEDULE_ScheduleConst => some 100
  | .Gaccessliststoragekey_SCHEDULE_ScheduleConst  => some 1900
  | .Gaccesslistaddress_SCHEDULE_ScheduleConst     => some 2400
  | .maxInitCodeSize_SCHEDULE_ScheduleConst        => some 49152
  | .Ginitcodewordcost_SCHEDULE_ScheduleConst      => some 2
  | .Rmaxquotient_SCHEDULE_ScheduleConst           => some 5
  | .Gpointeval_SCHEDULE_ScheduleConst => some 50000
  := by
  simp [«_<_>_SCHEDULE_Int_ScheduleConst_Schedule»]
  cases const <;> simp

end GasInterface
