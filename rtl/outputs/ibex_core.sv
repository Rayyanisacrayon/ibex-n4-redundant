// Copyright lowRISC contributors.
// Copyright 2018 ETH Zurich and University of Bologna, see also CREDITS.md.
// Licensed under the Apache License, Version 2.0, see LICENSE for details.
// SPDX-License-Identifier: Apache-2.0

`ifdef RISCV_FORMAL
  `define RVFI
`endif

`include "prim_assert.sv"
`include "dv_fcov_macros.svh"

/**
 * Top level module of the ibex RISC-V core
 */
module ibex_core import ibex_pkg::*; #(
  parameter bit                     PMPEnable        = 1'b0,
  parameter int unsigned            PMPGranularity   = 0,
  parameter int unsigned            PMPNumRegions    = 4,
  parameter ibex_pkg::pmp_cfg_t     PMPRstCfg[16]    = ibex_pkg::PmpCfgRst,
  parameter logic [33:0]            PMPRstAddr[16]   = ibex_pkg::PmpAddrRst,
  parameter ibex_pkg::pmp_mseccfg_t PMPRstMsecCfg    = ibex_pkg::PmpMseccfgRst,
  parameter int unsigned            MHPMCounterNum   = 0,
  parameter int unsigned            MHPMCounterWidth = 40,
  parameter bit                     RV32E            = 1'b0,
  parameter rv32m_e                 RV32M            = RV32MFast,
  parameter rv32b_e                 RV32B            = RV32BNone,
  parameter bit                     BranchTargetALU  = 1'b0,
  parameter bit                     WritebackStage   = 1'b0,
  parameter bit                     ICache           = 1'b0,
  parameter bit                     ICacheECC        = 1'b0,
  parameter int unsigned            BusSizeECC       = BUS_SIZE,
  parameter int unsigned            TagSizeECC       = IC_TAG_SIZE,
  parameter int unsigned            LineSizeECC      = IC_LINE_SIZE,
  parameter bit                     BranchPredictor  = 1'b0,
  parameter bit                     DbgTriggerEn     = 1'b0,
  parameter int unsigned            DbgHwBreakNum    = 1,
  parameter bit                     ResetAll         = 1'b0,
  parameter lfsr_seed_t             RndCnstLfsrSeed  = RndCnstLfsrSeedDefault,
  parameter lfsr_perm_t             RndCnstLfsrPerm  = RndCnstLfsrPermDefault,
  parameter bit                     SecureIbex       = 1'b0,
  parameter bit                     DummyInstructions= 1'b0,
  parameter bit                     RegFileECC       = 1'b0,
  parameter int unsigned            RegFileDataWidth = 32,
  parameter bit                     MemECC           = 1'b0,
  parameter int unsigned            MemDataWidth     = MemECC ? 32 + 7 : 32,
  parameter int unsigned            DmBaseAddr       = 32'h1A110000,
  parameter int unsigned            DmAddrMask       = 32'h00000FFF,
  parameter int unsigned            DmHaltAddr       = 32'h1A110800,
  parameter int unsigned            DmExceptionAddr  = 32'h1A110808,
  // mvendorid: encoding of manufacturer/provider
  parameter logic [31:0]            CsrMvendorId     = 32'b0,
  // marchid: encoding of base microarchitecture
  parameter logic [31:0]            CsrMimpId        = 32'b0
) (
  // Clock and Reset
  input  logic                         clk_i,
  input  logic                         rst_ni,

  input  logic [31:0]                  hart_id_i,
  input  logic [31:0]                  boot_addr_i,

  // Instruction memory interface
  output logic                         instr_req_o,
  input  logic                         instr_gnt_i,
  input  logic                         instr_rvalid_i,
  output logic [31:0]                  instr_addr_o,
  input  logic [MemDataWidth-1:0]      instr_rdata_i,
  input  logic                         instr_err_i,

  // Data memory interface
  output logic                         data_req_o,
  input  logic                         data_gnt_i,
  input  logic                         data_rvalid_i,
  output logic                         data_we_o,
  output logic [3:0]                   data_be_o,
  output logic [31:0]                  data_addr_o,
  output logic [MemDataWidth-1:0]      data_wdata_o,
  input  logic [MemDataWidth-1:0]      data_rdata_i,
  input  logic                         data_err_i,

  // Register file interface
  output logic                         dummy_instr_id_o,
  output logic                         dummy_instr_wb_o,
  output logic [4:0]                   rf_raddr_a_o,
  output logic [4:0]                   rf_raddr_b_o,
  output logic [4:0]                   rf_waddr_wb_o,
  output logic                         rf_we_wb_o,
  output logic [RegFileDataWidth-1:0]  rf_wdata_wb_ecc_o,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_a_ecc_i,
  input  logic [RegFileDataWidth-1:0]  rf_rdata_b_ecc_i,

  // RAMs interface
  output logic [IC_NUM_WAYS-1:0]       ic_tag_req_o,
  output logic                         ic_tag_write_o,
  output logic [IC_INDEX_W-1:0]        ic_tag_addr_o,
  output logic [TagSizeECC-1:0]        ic_tag_wdata_o,
  input  logic [TagSizeECC-1:0]        ic_tag_rdata_i [IC_NUM_WAYS],
  output logic [IC_NUM_WAYS-1:0]       ic_data_req_o,
  output logic                         ic_data_write_o,
  output logic [IC_INDEX_W-1:0]        ic_data_addr_o,
  output logic [LineSizeECC-1:0]       ic_data_wdata_o,
  input  logic [LineSizeECC-1:0]       ic_data_rdata_i [IC_NUM_WAYS],
  input  logic                         ic_scr_key_valid_i,
  output logic                         ic_scr_key_req_o,


  // Interrupt inputs
  input  logic                         irq_software_i,
  input  logic                         irq_timer_i,
  input  logic                         irq_external_i,
  input  logic [14:0]                  irq_fast_i,
  input  logic                         irq_nm_i,       // non-maskable interrupt
  output logic                         irq_pending_o,

  // Debug Interface
  input  logic                         debug_req_i,
  output crash_dump_t                  crash_dump_o,
  // SEC_CM: EXCEPTION.CTRL_FLOW.LOCAL_ESC
  // SEC_CM: EXCEPTION.CTRL_FLOW.GLOBAL_ESC
  output logic                         double_fault_seen_o,

  ///REDUNDANCY MUX SELECT SIGNALS
    // Mux selection signals (0 = primary, 1 = redundant)
  input logic redundancy_sel_if,
  input logic redundancy_sel_id,
  input logic redundancy_sel_ex,
  input logic redundancy_sel_lsu,
  input logic redundancy_sel_wb,
  input logic redundancy_sel_rf,     // Register file selector
  input logic redundancy_sel_icache, // Instruction cache selector
  input logic redundancy_sel_csr,    // CSR registers selector
  
  // selection signals for the pipeline registers
  input logic redundancy_sel_if_reg,
  input logic redundancy_sel_id_reg,
  input logic redundancy_sel_ex_reg,
  input logic redundancy_sel_lsu_reg,
  input logic redundancy_sel_wb_reg,
  input logic redundancy_sel_rf_reg,     
  input logic redundancy_sel_icache_reg, 

  // RISC-V Formal Interface
  // Does not comply with the coding standards of _i/_o suffixes, but follows
  // the convention of RISC-V Formal Interface Specification.
`ifdef RVFI
  output logic                         rvfi_valid,
  output logic [63:0]                  rvfi_order,
  output logic [31:0]                  rvfi_insn,
  output logic                         rvfi_trap,
  output logic                         rvfi_halt,
  output logic                         rvfi_intr,
  output logic [ 1:0]                  rvfi_mode,
  output logic [ 1:0]                  rvfi_ixl,
  output logic [ 4:0]                  rvfi_rs1_addr,
  output logic [ 4:0]                  rvfi_rs2_addr,
  output logic [ 4:0]                  rvfi_rs3_addr,
  output logic [31:0]                  rvfi_rs1_rdata,
  output logic [31:0]                  rvfi_rs2_rdata,
  output logic [31:0]                  rvfi_rs3_rdata,
  output logic [ 4:0]                  rvfi_rd_addr,
  output logic [31:0]                  rvfi_rd_wdata,
  output logic [31:0]                  rvfi_pc_rdata,
  output logic [31:0]                  rvfi_pc_wdata,
  output logic [31:0]                  rvfi_mem_addr,
  output logic [ 3:0]                  rvfi_mem_rmask,
  output logic [ 3:0]                  rvfi_mem_wmask,
  output logic [31:0]                  rvfi_mem_rdata,
  output logic [31:0]                  rvfi_mem_wdata,
  output logic [31:0]                  rvfi_ext_pre_mip,
  output logic [31:0]                  rvfi_ext_post_mip,
  output logic                         rvfi_ext_nmi,
  output logic                         rvfi_ext_nmi_int,
  output logic                         rvfi_ext_debug_req,
  output logic                         rvfi_ext_debug_mode,
  output logic                         rvfi_ext_rf_wr_suppress,
  output logic [63:0]                  rvfi_ext_mcycle,
  output logic [31:0]                  rvfi_ext_mhpmcounters [10],
  output logic [31:0]                  rvfi_ext_mhpmcountersh [10],
  output logic                         rvfi_ext_ic_scr_key_valid,
  output logic                         rvfi_ext_irq_valid,
  `endif

  // CPU Control Signals
  // SEC_CM: FETCH.CTRL.LC_GATED
  input  ibex_mubi_t                   fetch_enable_i,
  output logic                         alert_minor_o,
  output logic                         alert_major_internal_o,
  output logic                         alert_major_bus_o,
  output ibex_mubi_t                   core_busy_o
);

  localparam int unsigned PMPNumChan      = 3;
  // SEC_CM: CORE.DATA_REG_SW.SCA
  localparam bit          DataIndTiming     = SecureIbex;
  localparam bit          PCIncrCheck       = SecureIbex;
  localparam bit          ShadowCSR         = 1'b0;

  // IF/ID signals
  logic        dummy_instr_id;
  logic        instr_valid_id;
  logic        instr_new_id;
  logic [31:0] instr_rdata_id;                 // Instruction sampled inside IF stage
  logic [31:0] instr_rdata_alu_id;             // Instruction sampled inside IF stage (replicated to
                                               // ease fan-out)
  logic [15:0] instr_rdata_c_id;               // Compressed instruction sampled inside IF stage
  logic        instr_is_compressed_id;
  logic        instr_perf_count_id;
  logic        instr_bp_taken_id;
  logic        instr_fetch_err;                // Bus error on instr fetch
  logic        instr_fetch_err_plus2;          // Instruction error is misaligned
  logic        illegal_c_insn_id;              // Illegal compressed instruction sent to ID stage
  logic [31:0] pc_if;                          // Program counter in IF stage
  logic [31:0] pc_id;                          // Program counter in ID stage
  logic [31:0] pc_wb;                          // Program counter in WB stage
  logic [33:0] imd_val_d_ex[2];                // Intermediate register for multicycle Ops
  logic [33:0] imd_val_q_ex[2];                // Intermediate register for multicycle Ops
  logic [1:0]  imd_val_we_ex;

  logic        data_ind_timing;
  logic        dummy_instr_en;
  logic [2:0]  dummy_instr_mask;
  logic        dummy_instr_seed_en;
  logic [31:0] dummy_instr_seed;
  logic        icache_enable;
  logic        icache_inval;
  logic        icache_ecc_error;
  logic        pc_mismatch_alert;
  logic        csr_shadow_err;

  logic        instr_first_cycle_id;
  logic        instr_valid_clear;
  logic        pc_set;
  logic        nt_branch_mispredict;
  logic [31:0] nt_branch_addr;
  pc_sel_e     pc_mux_id;                      // Mux selector for next PC
  exc_pc_sel_e exc_pc_mux_id;                  // Mux selector for exception PC
  exc_cause_t  exc_cause;                      // Exception cause

  logic        instr_intg_err;
  logic        lsu_load_err, lsu_load_err_raw;
  logic        lsu_store_err, lsu_store_err_raw;
  logic        lsu_load_resp_intg_err;
  logic        lsu_store_resp_intg_err;

  logic        expecting_load_resp_id;
  logic        expecting_store_resp_id;

  // LSU signals
  logic        lsu_addr_incr_req;
  logic [31:0] lsu_addr_last;

  // Jump and branch target and decision (EX->IF)
  logic [31:0] branch_target_ex;
  logic        branch_decision;

  // Core busy signals
  logic        ctrl_busy;
  logic        if_busy;
  logic        lsu_busy;

  // Register File
  logic [4:0]  rf_raddr_a;
  logic [31:0] rf_rdata_a;
  logic [4:0]  rf_raddr_b;
  logic [31:0] rf_rdata_b;
  logic        rf_ren_a;
  logic        rf_ren_b;
  logic [4:0]  rf_waddr_wb;
  logic [31:0] rf_wdata_wb;
  // Writeback register write data that can be used on the forwarding path (doesn't factor in memory
  // read data as this is too late for the forwarding path)
  logic [31:0] rf_wdata_fwd_wb;
  logic [31:0] rf_wdata_lsu;
  logic        rf_we_wb;
  logic        rf_we_lsu;
  logic        rf_ecc_err_comb;

  logic [4:0]  rf_waddr_id;
  logic [31:0] rf_wdata_id;
  logic        rf_we_id;
  logic        rf_rd_a_wb_match;
  logic        rf_rd_b_wb_match;

  // Redundant Register File signals
  logic [31:0] rf_rdata_a_primary;
  logic [31:0] rf_rdata_b_primary;
  logic        rf_ecc_err_comb_primary;

  logic [31:0] rf_rdata_a_r;
  logic [31:0] rf_rdata_b_r;
  logic        rf_ecc_err_comb_r;



  
  // Muxed Register File outputs
  logic [31:0] rf_rdata_a_mux;
  logic [31:0] rf_rdata_b_mux;
  logic        rf_ecc_err_comb_mux;

  logic [31:0] rf_rdata_a_reg_a;
  logic [31:0] rf_rdata_b_reg_a;
  logic        rf_ecc_err_comb_reg_a;

  logic [31:0] rf_rdata_a_reg_b;
  logic [31:0] rf_rdata_b_reg_b;
  logic        rf_ecc_err_comb_reg_b;

 



  // ALU Control
  alu_op_e     alu_operator_ex;
  logic [31:0] alu_operand_a_ex;
  logic [31:0] alu_operand_b_ex;

  logic [31:0] bt_a_operand;
  logic [31:0] bt_b_operand;

  logic [31:0] alu_adder_result_ex;    // Used to forward computed address to LSU
  logic [31:0] result_ex;

  // Multiplier Control
  logic        mult_en_ex;
  logic        div_en_ex;
  logic        mult_sel_ex;
  logic        div_sel_ex;
  md_op_e      multdiv_operator_ex;
  logic [1:0]  multdiv_signed_mode_ex;
  logic [31:0] multdiv_operand_a_ex;
  logic [31:0] multdiv_operand_b_ex;
  logic        multdiv_ready_id;

  // CSR control
  logic        csr_access;
  csr_op_e     csr_op;
  logic        csr_op_en;
  csr_num_e    csr_addr;
  logic [31:0] csr_rdata;
  logic [31:0] csr_wdata;
  logic        illegal_csr_insn_id;    // CSR access to non-existent register,
                                       // with wrong privilege level,
                                       // or missing write permissions

  // Data Memory Control
  logic        lsu_we;
  logic [1:0]  lsu_type;
  logic        lsu_sign_ext;
  logic        lsu_req;
  logic        lsu_rdata_valid;
  logic [31:0] lsu_wdata;
  logic        lsu_req_done;

  // stall control
  logic        id_in_ready;
  logic        ex_valid;

  logic        lsu_resp_valid;
  logic        lsu_resp_err;

  // Signals between instruction core interface and pipe (if and id stages)
  logic        instr_req_int;          // Id stage asserts a req to instruction core interface
  logic        instr_req_gated;
  logic        instr_exec;

  // Writeback stage
  logic           en_wb;
  wb_instr_type_e instr_type_wb;
  logic           ready_wb;
  logic           rf_write_wb;
  logic           outstanding_load_wb;
  logic           outstanding_store_wb;
  logic           dummy_instr_wb;

  // Interrupts
  logic        nmi_mode;
  irqs_t       irqs;
  logic        csr_mstatus_mie;
  logic [31:0] csr_mepc, csr_depc;

  // PMP signals
  logic [33:0]  csr_pmp_addr [PMPNumRegions];
  pmp_cfg_t     csr_pmp_cfg  [PMPNumRegions];
  pmp_mseccfg_t csr_pmp_mseccfg;
  logic         pmp_req_err  [PMPNumChan];
  logic         data_req_out;

  logic        csr_save_if;
  logic        csr_save_id;
  logic        csr_save_wb;
  logic        csr_restore_mret_id;
  logic        csr_restore_dret_id;
  logic        csr_save_cause;
  logic        csr_mtvec_init;
  logic [31:0] csr_mtvec;
  logic [31:0] csr_mtval;
  logic        csr_mstatus_tw;
  priv_lvl_e   priv_mode_id;
  priv_lvl_e   priv_mode_lsu;

  // debug mode and dcsr configuration
  logic        debug_mode;
  logic        debug_mode_entering;
  dbg_cause_e  debug_cause;
  logic        debug_csr_save;
  logic        debug_single_step;
  logic        debug_ebreakm;
  logic        debug_ebreaku;
  logic        trigger_match;

  // Redundant CSR signals
  logic [31:0] csr_rdata_primary;
  logic [31:0] csr_mepc_primary, csr_depc_primary;
  logic [33:0] csr_pmp_addr_primary [PMPNumRegions];
  pmp_cfg_t    csr_pmp_cfg_primary  [PMPNumRegions];
  pmp_mseccfg_t csr_pmp_mseccfg_primary;
  logic [31:0] csr_mtvec_primary;
  logic        csr_mstatus_mie_primary;
  logic        csr_mstatus_tw_primary;
  priv_lvl_e   priv_mode_id_primary;
  priv_lvl_e   priv_mode_lsu_primary;
  logic        debug_single_step_primary;
  logic        debug_ebreakm_primary;
  logic        debug_ebreaku_primary;
  logic        trigger_match_primary;
  logic        csr_shadow_err_primary;
  logic        data_ind_timing_primary;
  logic        dummy_instr_en_primary;
  logic [2:0]  dummy_instr_mask_primary;
  logic        dummy_instr_seed_en_primary;
  logic [31:0] dummy_instr_seed_primary;
  logic        icache_enable_primary;
  logic        irq_pending_o_primary;
  logic        irqs_primary;
  logic [31:0] crash_dump_mtval_primary;


  logic [31:0] csr_rdata_r;
  logic [31:0] csr_mepc_r, csr_depc_r;
  logic [33:0] csr_pmp_addr_r [PMPNumRegions];
  pmp_cfg_t    csr_pmp_cfg_r  [PMPNumRegions];
  pmp_mseccfg_t csr_pmp_mseccfg_r;
  logic [31:0] csr_mtvec_r;
  logic        csr_mstatus_mie_r;
  logic        csr_mstatus_tw_r;
  priv_lvl_e   priv_mode_id_r;
  priv_lvl_e   priv_mode_lsu_r;
  logic        debug_single_step_r;
  logic        debug_ebreakm_r;
  logic        debug_ebreaku_r;
  logic        trigger_match_r;
  logic        csr_shadow_err_r;
  logic        data_ind_timing_r;
  logic        dummy_instr_en_r;
  logic [2:0]  dummy_instr_mask_r;
  logic        dummy_instr_seed_en_r;
  logic [31:0] dummy_instr_seed_r;
  logic        icache_enable_r;
  logic        irq_pending_o_r;
  logic        irqs_r;
  logic [31:0] crash_dump_mtval_r;
  
  // Muxed CSR outputs
  logic [31:0] csr_rdata_mux;
  logic [31:0] csr_mepc_mux, csr_depc_mux;
  logic [33:0] csr_pmp_addr_mux [PMPNumRegions];
  pmp_cfg_t    csr_pmp_cfg_mux  [PMPNumRegions];
  pmp_mseccfg_t csr_pmp_mseccfg_mux;
  logic [31:0] csr_mtvec_mux_csr;
  logic        csr_mstatus_mie_mux;
  logic        csr_mstatus_tw_mux;
  priv_lvl_e   priv_mode_id_mux_csr;
  priv_lvl_e   priv_mode_lsu_mux_csr;
  logic        debug_single_step_mux;
  logic        debug_ebreakm_mux;
  logic        debug_ebreaku_mux;
  logic        trigger_match_mux;
  logic        csr_shadow_err_mux;
  logic        data_ind_timing_mux;
  logic        dummy_instr_en_mux;
  logic [2:0]  dummy_instr_mask_mux;
  logic        dummy_instr_seed_en_mux;
  logic [31:0] dummy_instr_seed_mux;
  logic        icache_enable_mux;
  logic        irq_pending_o_mux;
  logic        irqs_mux;
  logic [31:0] crash_dump_mtval_mux;

  logic [31:0] csr_rdata_reg_a;
  logic [31:0] csr_mepc_reg_a, csr_depc_reg_a;
  logic [33:0] csr_pmp_addr_reg_a [PMPNumRegions];
  pmp_cfg_t    csr_pmp_cfg_reg_a  [PMPNumRegions];
  pmp_mseccfg_t csr_pmp_mseccfg_reg_a;
  logic [31:0] csr_mtvec_reg_a_csr;
  logic        csr_mstatus_mie_reg_a;
  logic        csr_mstatus_tw_reg_a;
  priv_lvl_e   priv_mode_id_reg_a_csr;
  priv_lvl_e   priv_mode_lsu_reg_a_csr;
  logic        debug_single_step_reg_a;
  logic        debug_ebreakm_reg_a;
  logic        debug_ebreaku_reg_a;
  logic        trigger_match_reg_a;
  logic        csr_shadow_err_reg_a;
  logic        data_ind_timing_reg_a;
  logic        dummy_instr_en_reg_a;
  logic [2:0]  dummy_instr_mask_reg_a;
  logic        dummy_instr_seed_en_reg_a;
  logic [31:0] dummy_instr_seed_reg_a;
  logic        icache_enable_reg_a;
  logic        irq_pending_o_reg_a;
  logic        irqs_reg_a;
  logic [31:0] crash_dump_mtval_reg_a;


  logic [31:0] csr_rdata_reg_b;
  logic [31:0] csr_mepc_reg_b, csr_depc_reg_b;
  logic [33:0] csr_pmp_addr_reg_b [PMPNumRegions];
  pmp_cfg_t    csr_pmp_cfg_reg_b  [PMPNumRegions];
  pmp_mseccfg_t csr_pmp_mseccfg_reg_b;
  logic [31:0] csr_mtvec_reg_b_csr;
  logic        csr_mstatus_mie_reg_b;
  logic        csr_mstatus_tw_reg_b;
  priv_lvl_e   priv_mode_id_reg_b_csr;
  priv_lvl_e   priv_mode_lsu_reg_b_csr;
  logic        debug_single_step_reg_b;
  logic        debug_ebreakm_reg_b;
  logic        debug_ebreaku_reg_b;
  logic        trigger_match_reg_b;
  logic        csr_shadow_err_reg_b;
  logic        data_ind_timing_reg_b;
  logic        dummy_instr_en_reg_b;
  logic [2:0]  dummy_instr_mask_reg_b;
  logic        dummy_instr_seed_en_reg_b;
  logic [31:0] dummy_instr_seed_reg_b;
  logic        icache_enable_reg_b;
  logic        irq_pending_o_reg_b;
  logic        irqs_reg_b;
  logic [31:0] crash_dump_mtval_reg_b;


  // signals relating to instruction movements between pipeline stages
  // used by performance counters and RVFI
  logic        instr_id_done;
  logic        instr_done_wb;

  logic        perf_instr_ret_wb;
  logic        perf_instr_ret_compressed_wb;
  logic        perf_instr_ret_wb_spec;
  logic        perf_instr_ret_compressed_wb_spec;
  logic        perf_iside_wait;
  logic        perf_dside_wait;
  logic        perf_mul_wait;
  logic        perf_div_wait;
  logic        perf_jump;
  logic        perf_branch;
  logic        perf_tbranch;
  logic        perf_load;
  logic        perf_store;

  // for RVFI
  logic        illegal_insn_id, unused_illegal_insn_id; // ID stage sees an illegal instruction

  ///////////////////////////////////////////////
  // Redundancy signals - for dual modular redundancy
  ///////////////////////////////////////////////



  // Redundant IF stage signals
  logic        instr_valid_id_primary;
  logic        instr_new_id_primary;
  logic [31:0] instr_rdata_id_primary;
  logic [31:0] instr_rdata_alu_id_primary;
  logic [15:0] instr_rdata_c_id_primary;
  logic        instr_is_compressed_id_primary;
  logic        instr_bp_taken_id_primary;
  logic        instr_fetch_err_primary;
  logic        instr_fetch_err_plus2_primary;
  logic        illegal_c_insn_id_primary;
  logic        dummy_instr_id_primary;
  logic [31:0] pc_if_primary;
  logic [31:0] pc_id_primary;
  logic        csr_mtvec_init_primary;
  logic        pc_mismatch_alert_primary;
  logic        if_busy_primary;
  logic        instr_intg_err_primary;
  logic        icache_ecc_error_primary;
  logic        instr_req_o_primary;
  logic [31:0] instr_addr_o_primary;
  logic [IC_NUM_WAYS-1:0]      ic_tag_req_o_primary;
  logic        ic_tag_write_o_primary;
  logic [IC_INDEX_W-1:0] ic_tag_addr_o_primary;
  logic [TagSizeECC-1:0] ic_tag_wdata_o_primary;
  logic [IC_NUM_WAYS-1:0]       ic_data_req_o_primary;
  logic        ic_data_write_o_primary;
  logic [IC_INDEX_W-1:0] ic_data_addr_o_primary;
  logic [LineSizeECC-1:0] ic_data_wdata_o_primary;
  logic        ic_scr_key_req_o_primary;

  logic        instr_valid_id_r;
  logic        instr_new_id_r;
  logic [31:0] instr_rdata_id_r;
  logic [31:0] instr_rdata_alu_id_r;
  logic [15:0] instr_rdata_c_id_r;
  logic        instr_is_compressed_id_r;
  logic        instr_bp_taken_id_r;
  logic        instr_fetch_err_r;
  logic        instr_fetch_err_plus2_r;
  logic        illegal_c_insn_id_r;
  logic        dummy_instr_id_r;
  logic [31:0] pc_if_r;
  logic [31:0] pc_id_r;
  logic        csr_mtvec_init_r;
  logic        pc_mismatch_alert_r;
  logic        if_busy_r;
  logic        instr_intg_err_r;
  logic        icache_ecc_error_r;
  logic        instr_req_o_r;
  logic [31:0] instr_addr_o_r;
  logic [IC_NUM_WAYS-1:0]      ic_tag_req_o_r;
  logic        ic_tag_write_o_r;
  logic [IC_INDEX_W-1:0] ic_tag_addr_o_r;
  logic [TagSizeECC-1:0] ic_tag_wdata_o_r;
  logic [IC_NUM_WAYS-1:0]       ic_data_req_o_r;
  logic        ic_data_write_o_r;
  logic [IC_INDEX_W-1:0] ic_data_addr_o_r;
  logic [LineSizeECC-1:0] ic_data_wdata_o_r;
  logic        ic_scr_key_req_o_r;

  
  // Muxed IF outputs
  logic        instr_valid_id_mux;
  logic        instr_new_id_mux;
  logic [31:0] instr_rdata_id_mux;
  logic [31:0] instr_rdata_alu_id_mux;
  logic [15:0] instr_rdata_c_id_mux;
  logic        instr_is_compressed_id_mux;
  logic        instr_bp_taken_id_mux;
  logic        instr_fetch_err_mux;
  logic        instr_fetch_err_plus2_mux;
  logic        illegal_c_insn_id_mux;
  logic        dummy_instr_id_mux;
  logic [31:0] pc_if_mux;
  logic [31:0] pc_id_mux;
  logic        csr_mtvec_init_mux;
  logic        pc_mismatch_alert_mux;
  logic        if_busy_mux;
  logic        instr_intg_err_mux;
  logic        icache_ecc_error_mux;
  logic        instr_req_o_mux;
  logic [31:0] instr_addr_o_mux;
  logic [IC_NUM_WAYS-1:0]      ic_tag_req_o_mux;
  logic        ic_tag_write_o_mux;
  logic [IC_INDEX_W-1:0] ic_tag_addr_o_mux;
  logic [TagSizeECC-1:0] ic_tag_wdata_o_mux;
  logic [IC_NUM_WAYS-1:0]       ic_data_req_o_mux;
  logic        ic_data_write_o_mux;
  logic [IC_INDEX_W-1:0] ic_data_addr_o_mux;
  logic [LineSizeECC-1:0] ic_data_wdata_o_mux;
  logic        ic_scr_key_req_o_mux;
  



  logic        instr_valid_id_reg_a;
  logic        instr_new_id_reg_a;
  logic [31:0] instr_rdata_id_reg_a;
  logic [31:0] instr_rdata_alu_id_reg_a;
  logic [15:0] instr_rdata_c_id_reg_a;
  logic        instr_is_compressed_id_reg_a;
  logic        instr_bp_taken_id_reg_a;
  logic        instr_fetch_err_reg_a;
  logic        instr_fetch_err_plus2_reg_a;
  logic        illegal_c_insn_id_reg_a;
  logic        dummy_instr_id_reg_a;
  logic [31:0] pc_if_reg_a;
  logic [31:0] pc_id_reg_a;
  logic        csr_mtvec_init_reg_a;
  logic        pc_mismatch_alert_reg_a;
  logic        if_busy_reg_a;
  logic        instr_intg_err_reg_a;
  logic        icache_ecc_error_reg_a;
  logic        instr_req_o_reg_a;
  logic [31:0] instr_addr_o_reg_a;
  logic [IC_NUM_WAYS-1:0]      ic_tag_req_o_reg_a;
  logic        ic_tag_write_o_reg_a;
  logic [IC_INDEX_W-1:0] ic_tag_addr_o_reg_a;
  logic [TagSizeECC-1:0] ic_tag_wdata_o_reg_a;
  logic [IC_NUM_WAYS-1:0]       ic_data_req_o_reg_a;
  logic        ic_data_write_o_reg_a;
  logic [IC_INDEX_W-1:0] ic_data_addr_o_reg_a;
  logic [LineSizeECC-1:0] ic_data_wdata_o_reg_a;
  logic        ic_scr_key_req_o_reg_a;
  

  logic        instr_valid_id_reg_b;
  logic        instr_new_id_reg_b;
  logic [31:0] instr_rdata_id_reg_b;
  logic [31:0] instr_rdata_alu_id_reg_b;
  logic [15:0] instr_rdata_c_id_reg_b;
  logic        instr_is_compressed_id_reg_b;
  logic        instr_bp_taken_id_reg_b;
  logic        instr_fetch_err_reg_b;
  logic        instr_fetch_err_plus2_reg_b;
  logic        illegal_c_insn_id_reg_b;
  logic        dummy_instr_id_reg_b;
  logic [31:0] pc_if_reg_b;
  logic [31:0] pc_id_reg_b;
  logic        csr_mtvec_init_reg_b;
  logic        pc_mismatch_alert_reg_b;
  logic        if_busy_reg_b;
  logic        instr_intg_err_reg_b;
  logic        icache_ecc_error_reg_b;
  logic        instr_req_o_reg_b;
  logic [31:0] instr_addr_o_reg_b;
  logic [IC_NUM_WAYS-1:0]      ic_tag_req_o_reg_b;
  logic        ic_tag_write_o_reg_b;
  logic [IC_INDEX_W-1:0] ic_tag_addr_o_reg_b;
  logic [TagSizeECC-1:0] ic_tag_wdata_o_reg_b;
  logic [IC_NUM_WAYS-1:0]       ic_data_req_o_reg_b;
  logic        ic_data_write_o_reg_b;
  logic [IC_INDEX_W-1:0] ic_data_addr_o_reg_b;
  logic [LineSizeECC-1:0] ic_data_wdata_o_reg_b;
  logic        ic_scr_key_req_o_reg_b;

  // Redundant ID stage signals
  logic        ctrl_busy_primary;
  logic        illegal_insn_id_primary;
  logic        instr_first_cycle_id_primary;
  logic        instr_valid_clear_primary;
  logic        id_in_ready_primary;
  logic        instr_req_int_primary;
  logic        pc_set_primary;
  pc_sel_e     pc_mux_id_primary;
  logic        nt_branch_mispredict_primary;
  logic [31:0] nt_branch_addr_primary;
  exc_pc_sel_e exc_pc_mux_id_primary;
  exc_cause_t  exc_cause_primary;
  logic        icache_inval_primary;
  
  alu_op_e     alu_operator_ex_primary;
  logic [31:0] alu_operand_a_ex_primary;
  logic [31:0] alu_operand_b_ex_primary;
  logic [31:0] bt_a_operand_primary;
  logic [31:0] bt_b_operand_primary;
  logic [33:0] imd_val_q_ex_primary[2];
  
  logic        mult_en_ex_primary;
  logic        div_en_ex_primary;
  logic        mult_sel_ex_primary;
  logic        div_sel_ex_primary;
  md_op_e      multdiv_operator_ex_primary;
  logic [1:0]  multdiv_signed_mode_ex_primary;
  logic [31:0] multdiv_operand_a_ex_primary;
  logic [31:0] multdiv_operand_b_ex_primary;
  logic        multdiv_ready_id_primary;
  
  logic        csr_access_primary;
  csr_op_e     csr_op_primary;
  csr_num_e    csr_addr_primary;
  logic        csr_op_en_primary;
  logic        csr_save_if_primary;
  logic        csr_save_id_primary;
  logic        csr_save_wb_primary;
  logic        csr_restore_mret_id_primary;
  logic        csr_restore_dret_id_primary;
  logic        csr_save_cause_primary;
  logic [31:0] csr_mtval_primary;
  logic        illegal_csr_insn_id_primary;
  
  logic        lsu_req_primary;
  logic        lsu_we_primary;
  logic [1:0]  lsu_type_primary;
  logic        lsu_sign_ext_primary;
  logic [31:0] lsu_wdata_primary;
  logic        lsu_req_done_primary;
  logic        lsu_addr_incr_req_primary;
  logic [31:0] lsu_addr_last_primary;
  logic        expecting_load_resp_id_primary;
  logic        expecting_store_resp_id_primary;
  
  logic        nmi_mode_primary;
  logic        debug_mode_primary;
  logic        debug_mode_entering_primary;
  dbg_cause_e  debug_cause_primary;
  logic        debug_csr_save_primary;
  
  logic [4:0]  rf_raddr_a_primary;
  logic [4:0]  rf_raddr_b_primary;
  logic        rf_ren_a_primary;
  logic        rf_ren_b_primary;
  logic [4:0]  rf_waddr_id_primary;
  logic [31:0] rf_wdata_id_primary;
  logic        rf_we_id_primary;
  logic        rf_rd_a_wb_match_primary;
  logic        rf_rd_b_wb_match_primary;
  
  logic        en_wb_primary;
  wb_instr_type_e instr_type_wb_primary;
  logic        perf_jump_primary;
  logic        perf_branch_primary;
  logic        perf_tbranch_primary;
  logic        perf_dside_wait_primary;
  logic        perf_mul_wait_primary;
  logic        perf_div_wait_primary;
  logic        instr_id_done_primary;
  logic        instr_perf_count_id_primary;



  logic        ctrl_busy_r;
  logic        illegal_insn_id_r;
  logic        instr_first_cycle_id_r;
  logic        instr_valid_clear_r;
  logic        id_in_ready_r;
  logic        instr_req_int_r;
  logic        pc_set_r;
  pc_sel_e     pc_mux_id_r;
  logic        nt_branch_mispredict_r;
  logic [31:0] nt_branch_addr_r;
  exc_pc_sel_e exc_pc_mux_id_r;
  exc_cause_t  exc_cause_r;
  logic        icache_inval_r;
  
  alu_op_e     alu_operator_ex_r;
  logic [31:0] alu_operand_a_ex_r;
  logic [31:0] alu_operand_b_ex_r;
  logic [31:0] bt_a_operand_r;
  logic [31:0] bt_b_operand_r;
  logic [33:0] imd_val_q_ex_r[2];
  
  logic        mult_en_ex_r;
  logic        div_en_ex_r;
  logic        mult_sel_ex_r;
  logic        div_sel_ex_r;
  md_op_e      multdiv_operator_ex_r;
  logic [1:0]  multdiv_signed_mode_ex_r;
  logic [31:0] multdiv_operand_a_ex_r;
  logic [31:0] multdiv_operand_b_ex_r;
  logic        multdiv_ready_id_r;
  
  logic        csr_access_r;
  csr_op_e     csr_op_r;
  csr_num_e    csr_addr_r;
  logic        csr_op_en_r;
  logic        csr_save_if_r;
  logic        csr_save_id_r;
  logic        csr_save_wb_r;
  logic        csr_restore_mret_id_r;
  logic        csr_restore_dret_id_r;
  logic        csr_save_cause_r;
  logic [31:0] csr_mtval_r;
  logic        illegal_csr_insn_id_r;
  
  logic        lsu_req_r;
  logic        lsu_we_r;
  logic [1:0]  lsu_type_r;
  logic        lsu_sign_ext_r;
  logic [31:0] lsu_wdata_r;
  logic        lsu_req_done_r;
  logic        lsu_addr_incr_req_r;
  logic [31:0] lsu_addr_last_r;
  logic        expecting_load_resp_id_r;
  logic        expecting_store_resp_id_r;
  
  logic        nmi_mode_r;
  logic        debug_mode_r;
  logic        debug_mode_entering_r;
  dbg_cause_e  debug_cause_r;
  logic        debug_csr_save_r;
  
  logic [4:0]  rf_raddr_a_r;
  logic [4:0]  rf_raddr_b_r;
  logic        rf_ren_a_r;
  logic        rf_ren_b_r;
  logic [4:0]  rf_waddr_id_r;
  logic [31:0] rf_wdata_id_r;
  logic        rf_we_id_r;
  logic        rf_rd_a_wb_match_r;
  logic        rf_rd_b_wb_match_r;
  
  logic        en_wb_r;
  wb_instr_type_e instr_type_wb_r;
  logic        perf_jump_r;
  logic        perf_branch_r;
  logic        perf_tbranch_r;
  logic        perf_dside_wait_r;
  logic        perf_mul_wait_r;
  logic        perf_div_wait_r;
  logic        instr_id_done_r;
  logic        instr_perf_count_id_r;

  
  // Muxed ID outputs
  logic        ctrl_busy_mux;
  logic        illegal_insn_id_mux;
  logic        instr_first_cycle_id_mux;
  logic        instr_valid_clear_mux;
  logic        id_in_ready_mux;
  logic        instr_req_int_mux;
  logic        pc_set_mux;
  pc_sel_e     pc_mux_id_mux;
  logic        nt_branch_mispredict_mux;
  logic [31:0] nt_branch_addr_mux;
  exc_pc_sel_e exc_pc_mux_id_mux;
  exc_cause_t  exc_cause_mux;
  logic        icache_inval_mux;
  
  alu_op_e     alu_operator_ex_mux;
  logic [31:0] alu_operand_a_ex_mux;
  logic [31:0] alu_operand_b_ex_mux;
  logic [31:0] bt_a_operand_mux;
  logic [31:0] bt_b_operand_mux;
  logic [33:0] imd_val_q_ex_mux[2];
  
  logic        mult_en_ex_mux;
  logic        div_en_ex_mux;
  logic        mult_sel_ex_mux;
  logic        div_sel_ex_mux;
  md_op_e      multdiv_operator_ex_mux;
  logic [1:0]  multdiv_signed_mode_ex_mux;
  logic [31:0] multdiv_operand_a_ex_mux;
  logic [31:0] multdiv_operand_b_ex_mux;
  logic        multdiv_ready_id_mux;
  
  logic        csr_access_mux;
  csr_op_e     csr_op_mux;
  csr_num_e    csr_addr_mux;
  logic        csr_op_en_mux;
  logic        csr_save_if_mux;
  logic        csr_save_id_mux;
  logic        csr_save_wb_mux;
  logic        csr_restore_mret_id_mux;
  logic        csr_restore_dret_id_mux;
  logic        csr_save_cause_mux;
  logic [31:0] csr_mtval_mux;
  logic        illegal_csr_insn_id_mux;
  
  logic        lsu_req_mux;
  logic        lsu_we_mux;
  logic [1:0]  lsu_type_mux;
  logic        lsu_sign_ext_mux;
  logic [31:0] lsu_wdata_mux;
  logic        lsu_req_done_mux;
  logic        lsu_addr_incr_req_mux;
  logic [31:0] lsu_addr_last_mux;
  logic        expecting_load_resp_id_mux;
  logic        expecting_store_resp_id_mux;
  
  logic        nmi_mode_mux;
  logic        debug_mode_mux;
  logic        debug_mode_entering_mux;
  dbg_cause_e  debug_cause_mux;
  logic        debug_csr_save_mux;
  
  logic [4:0]  rf_raddr_a_mux;
  logic [4:0]  rf_raddr_b_mux;
  logic        rf_ren_a_mux;
  logic        rf_ren_b_mux;
  logic [4:0]  rf_waddr_id_mux;
  logic [31:0] rf_wdata_id_mux;
  logic        rf_we_id_mux;
  logic        rf_rd_a_wb_match_mux;
  logic        rf_rd_b_wb_match_mux;
  
  logic        en_wb_mux;
  wb_instr_type_e instr_type_wb_mux;
  logic        perf_jump_mux;
  logic        perf_branch_mux;
  logic        perf_tbranch_mux;
  logic        perf_dside_wait_mux;
  logic        perf_mul_wait_mux;
  logic        perf_div_wait_mux;
  logic        instr_id_done_mux;
  logic        instr_perf_count_id_mux;
  

  logic        ctrl_busy_reg_a;
  logic        illegal_insn_id_reg_a;
  logic        instr_first_cycle_id_reg_a;
  logic        instr_valid_clear_reg_a;
  logic        id_in_ready_reg_a;
  logic        instr_req_int_reg_a;
  logic        pc_set_reg_a;
  pc_sel_e     pc_mux_id_reg_a;
  logic        nt_branch_mispredict_reg_a;
  logic [31:0] nt_branch_addr_reg_a;
  exc_pc_sel_e exc_pc_mux_id_reg_a;
  exc_cause_t  exc_cause_reg_a;
  logic        icache_inval_reg_a;
  
  alu_op_e     alu_operator_ex_reg_a;
  logic [31:0] alu_operand_a_ex_reg_a;
  logic [31:0] alu_operand_b_ex_reg_a;
  logic [31:0] bt_a_operand_reg_a;
  logic [31:0] bt_b_operand_reg_a;
  logic [33:0] imd_val_q_ex_reg_a[2];
  
  logic        mult_en_ex_reg_a;
  logic        div_en_ex_reg_a;
  logic        mult_sel_ex_reg_a;
  logic        div_sel_ex_reg_a;
  md_op_e      multdiv_operator_ex_reg_a;
  logic [1:0]  multdiv_signed_mode_ex_reg_a;
  logic [31:0] multdiv_operand_a_ex_reg_a;
  logic [31:0] multdiv_operand_b_ex_reg_a;
  logic        multdiv_ready_id_reg_a;
  
  logic        csr_access_reg_a;
  csr_op_e     csr_op_reg_a;
  csr_num_e    csr_addr_reg_a;
  logic        csr_op_en_reg_a;
  logic        csr_save_if_reg_a;
  logic        csr_save_id_reg_a;
  logic        csr_save_wb_reg_a;
  logic        csr_restore_mret_id_reg_a;
  logic        csr_restore_dret_id_reg_a;
  logic        csr_save_cause_reg_a;
  logic [31:0] csr_mtval_reg_a;
  logic        illegal_csr_insn_id_reg_a;
  
  logic        lsu_req_reg_a;
  logic        lsu_we_reg_a;
  logic [1:0]  lsu_type_reg_a;
  logic        lsu_sign_ext_reg_a;
  logic [31:0] lsu_wdata_reg_a;
  logic        lsu_req_done_reg_a;
  logic        lsu_addr_incr_req_reg_a;
  logic [31:0] lsu_addr_last_reg_a;
  logic        expecting_load_resp_id_reg_a;
  logic        expecting_store_resp_id_reg_a;
  
  logic        nmi_mode_reg_a;
  logic        debug_mode_reg_a;
  logic        debug_mode_entering_reg_a;
  dbg_cause_e  debug_cause_reg_a;
  logic        debug_csr_save_reg_a;
  
  logic [4:0]  rf_raddr_a_reg_a;
  logic [4:0]  rf_raddr_b_reg_a;
  logic        rf_ren_a_reg_a;
  logic        rf_ren_b_reg_a;
  logic [4:0]  rf_waddr_id_reg_a;
  logic [31:0] rf_wdata_id_reg_a;
  logic        rf_we_id_reg_a;
  logic        rf_rd_a_wb_match_reg_a;
  logic        rf_rd_b_wb_match_reg_a;
  
  logic        en_wb_reg_a;
  wb_instr_type_e instr_type_wb_reg_a;
  logic        perf_jump_reg_a;
  logic        perf_branch_reg_a;
  logic        perf_tbranch_reg_a;
  logic        perf_dside_wait_reg_a;
  logic        perf_mul_wait_reg_a;
  logic        perf_div_wait_reg_a;
  logic        instr_id_done_reg_a;
  logic        instr_perf_count_id_reg_a;

  logic        ctrl_busy_reg_b;
  logic        illegal_insn_id_reg_b;
  logic        instr_first_cycle_id_reg_b;
  logic        instr_valid_clear_reg_b;
  logic        id_in_ready_reg_b;
  logic        instr_req_int_reg_b;
  logic        pc_set_reg_b;
  pc_sel_e     pc_mux_id_reg_b;
  logic        nt_branch_mispredict_reg_b;
  logic [31:0] nt_branch_addr_reg_b;
  exc_pc_sel_e exc_pc_mux_id_reg_b;
  exc_cause_t  exc_cause_reg_b;
  logic        icache_inval_reg_b;
  
  alu_op_e     alu_operator_ex_reg_b;
  logic [31:0] alu_operand_a_ex_reg_b;
  logic [31:0] alu_operand_b_ex_reg_b;
  logic [31:0] bt_a_operand_reg_b;
  logic [31:0] bt_b_operand_reg_b;
  logic [33:0] imd_val_q_ex_reg_b[2];
  
  logic        mult_en_ex_reg_b;
  logic        div_en_ex_reg_b;
  logic        mult_sel_ex_reg_b;
  logic        div_sel_ex_reg_b;
  md_op_e      multdiv_operator_ex_reg_b;
  logic [1:0]  multdiv_signed_mode_ex_reg_b;
  logic [31:0] multdiv_operand_a_ex_reg_b;
  logic [31:0] multdiv_operand_b_ex_reg_b;
  logic        multdiv_ready_id_reg_b;
  
  logic        csr_access_reg_b;
  csr_op_e     csr_op_reg_b;
  csr_num_e    csr_addr_reg_b;
  logic        csr_op_en_reg_b;
  logic        csr_save_if_reg_b;
  logic        csr_save_id_reg_b;
  logic        csr_save_wb_reg_b;
  logic        csr_restore_mret_id_reg_b;
  logic        csr_restore_dret_id_reg_b;
  logic        csr_save_cause_reg_b;
  logic [31:0] csr_mtval_reg_b;
  logic        illegal_csr_insn_id_reg_b;
  
  logic        lsu_req_reg_b;
  logic        lsu_we_reg_b;
  logic [1:0]  lsu_type_reg_b;
  logic        lsu_sign_ext_reg_b;
  logic [31:0] lsu_wdata_reg_b;
  logic        lsu_req_done_reg_b;
  logic        lsu_addr_incr_req_reg_b;
  logic [31:0] lsu_addr_last_reg_b;
  logic        expecting_load_resp_id_reg_b;
  logic        expecting_store_resp_id_reg_b;
  
  logic        nmi_mode_reg_b;
  logic        debug_mode_reg_b;
  logic        debug_mode_entering_reg_b;
  dbg_cause_e  debug_cause_reg_b;
  logic        debug_csr_save_reg_b;
  
  logic [4:0]  rf_raddr_a_reg_b;
  logic [4:0]  rf_raddr_b_reg_b;
  logic        rf_ren_a_reg_b;
  logic        rf_ren_b_reg_b;
  logic [4:0]  rf_waddr_id_reg_b;
  logic [31:0] rf_wdata_id_reg_b;
  logic        rf_we_id_reg_b;
  logic        rf_rd_a_wb_match_reg_b;
  logic        rf_rd_b_wb_match_reg_b;
  
  logic        en_wb_reg_b;
  wb_instr_type_e instr_type_wb_reg_b;
  logic        perf_jump_reg_b;
  logic        perf_branch_reg_b;
  logic        perf_tbranch_reg_b;
  logic        perf_dside_wait_reg_b;
  logic        perf_mul_wait_reg_b;
  logic        perf_div_wait_reg_b;
  logic        instr_id_done_reg_b;
  logic        instr_perf_count_id_reg_b;

  // Redundant EX stage signals
  logic [31:0] alu_adder_result_ex_primary;
  logic [31:0] result_ex_primary;
  logic [31:0] branch_target_ex_primary;
  logic        branch_decision_primary;
  logic        ex_valid_primary;
  logic [33:0] imd_val_d_ex_primary[2];
  logic [1:0]  imd_val_we_ex_primary;


  logic [31:0] alu_adder_result_ex_r;
  logic [31:0] result_ex_r;
  logic [31:0] branch_target_ex_r;
  logic        branch_decision_r;
  logic        ex_valid_r;
  logic [33:0] imd_val_d_ex_r[2];
  logic [1:0]  imd_val_we_ex_r;
  
  // Muxed EX outputs
  logic [31:0] alu_adder_result_ex_mux;
  logic [31:0] result_ex_mux;
  logic [31:0] branch_target_ex_mux;
  logic        branch_decision_mux;
  logic        ex_valid_mux;
  logic [33:0] imd_val_d_ex_mux[2];
  logic [1:0]  imd_val_we_ex_mux;

  logic [31:0] alu_adder_result_ex_reg_a;
  logic [31:0] result_ex_reg_a;
  logic [31:0] branch_target_ex_reg_a;
  logic        branch_decision_reg_a;
  logic        ex_valid_reg_a;
  logic [33:0] imd_val_d_ex_reg_a[2];
  logic [1:0]  imd_val_we_ex_reg_a;
  
  logic [31:0] alu_adder_result_ex_reg_b;
  logic [31:0] result_ex_reg_b;
  logic [31:0] branch_target_ex_reg_b;
  logic        branch_decision_reg_b;
  logic        ex_valid_reg_b;
  logic [33:0] imd_val_d_ex_reg_b[2];
  logic [1:0]  imd_val_we_ex_reg_b;

  // Redundant LSU signals
  logic        data_req_out_primary;
  logic [31:0] rf_wdata_lsu_primary;
  logic        lsu_rdata_valid_primary;
  logic        lsu_req_done_lsu_primary;
  logic        lsu_addr_incr_req_lsu_primary;
  logic [31:0] lsu_addr_last_lsu_primary;
  logic        lsu_resp_valid_primary;
  logic        lsu_load_err_raw_primary;
  logic        lsu_load_resp_intg_err_primary;
  logic        lsu_store_err_raw_primary;
  logic        lsu_store_resp_intg_err_primary;
  logic        lsu_busy_primary;
  logic        perf_load_primary;
  logic        perf_store_primary;
  logic [31:0] data_addr_o_primary;
  logic        data_we_o_primary;
  logic [3:0]  data_be_o_primary;
  logic [31:0] data_wdata_o_primary;

  logic        data_req_out_r;
  logic [31:0] rf_wdata_lsu_r;
  logic        lsu_rdata_valid_r;
  logic        lsu_req_done_lsu_r;
  logic        lsu_addr_incr_req_lsu_r;
  logic [31:0] lsu_addr_last_lsu_r;
  logic        lsu_resp_valid_r;
  logic        lsu_load_err_raw_r;
  logic        lsu_load_resp_intg_err_r;
  logic        lsu_store_err_raw_r;
  logic        lsu_store_resp_intg_err_r;
  logic        lsu_busy_r;
  logic        perf_load_r;
  logic        perf_store_r;
  logic [31:0] data_addr_o_r;
  logic        data_we_o_r;
  logic [3:0]  data_be_o_r;
  logic [31:0] data_wdata_o_r;
  
  // Muxed LSU outputs 
  logic        data_req_out_mux;
  logic [31:0] rf_wdata_lsu_mux;
  logic        lsu_rdata_valid_mux;
  logic        lsu_req_done_lsu_mux;
  logic        lsu_addr_incr_req_lsu_mux;
  logic [31:0] lsu_addr_last_lsu_mux;
  logic        lsu_resp_valid_mux;
  logic        lsu_load_err_raw_mux;
  logic        lsu_load_resp_intg_err_mux;
  logic        lsu_store_err_raw_mux;
  logic        lsu_store_resp_intg_err_mux;
  logic        lsu_busy_mux;
  logic        perf_load_mux;
  logic        perf_store_mux;
  logic [31:0] data_addr_o_mux;
  logic        data_we_o_mux;
  logic [3:0]  data_be_o_mux;
  logic [31:0] data_wdata_o_mux;

  logic        data_req_out_reg_a;
  logic [31:0] rf_wdata_lsu_reg_a;
  logic        lsu_rdata_valid_reg_a;
  logic        lsu_req_done_lsu_reg_a;
  logic        lsu_addr_incr_req_lsu_reg_a;
  logic [31:0] lsu_addr_last_lsu_reg_a;
  logic        lsu_resp_valid_reg_a;
  logic        lsu_load_err_raw_reg_a;
  logic        lsu_load_resp_intg_err_reg_a;
  logic        lsu_store_err_raw_reg_a;
  logic        lsu_store_resp_intg_err_reg_a;
  logic        lsu_busy_reg_a;
  logic        perf_load_reg_a;
  logic        perf_store_reg_a;
  logic [31:0] data_addr_o_reg_a;
  logic        data_we_o_reg_a;
  logic [3:0]  data_be_o_reg_a;
  logic [31:0] data_wdata_o_reg_a;

  logic        data_req_out_reg_b;
  logic [31:0] rf_wdata_lsu_reg_b;
  logic        lsu_rdata_valid_reg_b;
  logic        lsu_req_done_lsu_reg_b;
  logic        lsu_addr_incr_req_lsu_reg_b;
  logic [31:0] lsu_addr_last_lsu_reg_b;
  logic        lsu_resp_valid_reg_b;
  logic        lsu_load_err_raw_reg_b;
  logic        lsu_load_resp_intg_err_reg_b;
  logic        lsu_store_err_raw_reg_b;
  logic        lsu_store_resp_intg_err_reg_b;
  logic        lsu_busy_reg_b;
  logic        perf_load_reg_b;
  logic        perf_store_reg_b;
  logic [31:0] data_addr_o_reg_b;
  logic        data_we_o_reg_b;
  logic [3:0]  data_be_o_reg_b;
  logic [31:0] data_wdata_o_reg_b;
  
  // Redundant WB stage signals
  logic        ready_wb_mux;
  logic        rf_write_wb_mux;
  logic        outstanding_load_wb_mux;
  logic        outstanding_store_wb_mux;
  logic [31:0] pc_wb_mux;
  logic        perf_instr_ret_wb_mux;
  logic        perf_instr_ret_compressed_wb_mux;
  logic        perf_instr_ret_wb_spec_mux;
  logic        perf_instr_ret_compressed_wb_spec_mux;
  logic [31:0] rf_wdata_fwd_wb_mux;
  logic [4:0]  rf_waddr_wb_mux;
  logic [31:0] rf_wdata_wb_mux;
  logic        rf_we_wb_mux;
  logic        dummy_instr_wb_mux;
  logic        instr_done_wb_mux;


  logic        ready_wb_primary;
  logic        rf_write_wb_primary;
  logic        outstanding_load_wb_primary;
  logic        outstanding_store_wb_primary;
  logic [31:0] pc_wb_primary;
  logic        perf_instr_ret_wb_primary;
  logic        perf_instr_ret_compressed_wb_primary;
  logic        perf_instr_ret_wb_spec_primary;
  logic        perf_instr_ret_compressed_wb_spec_primary;
  logic [31:0] rf_wdata_fwd_wb_primary;
  logic [4:0]  rf_waddr_wb_primary;
  logic [31:0] rf_wdata_wb_primary;
  logic        rf_we_wb_primary;
  logic        dummy_instr_wb_primary;
  logic        instr_done_wb_primary;


  logic        ready_wb_r;
  logic        rf_write_wb_r;
  logic        outstanding_load_wb_r;
  logic        outstanding_store_wb_r;
  logic [31:0] pc_wb_r;
  logic        perf_instr_ret_wb_r;
  logic        perf_instr_ret_compressed_wb_r;
  logic        perf_instr_ret_wb_spec_r;
  logic        perf_instr_ret_compressed_wb_spec_r;
  logic [31:0] rf_wdata_fwd_wb_r;
  logic [4:0]  rf_waddr_wb_r;
  logic [31:0] rf_wdata_wb_r;
  logic        rf_we_wb_r;
  logic        dummy_instr_wb_r;
  logic        instr_done_wb_r;
  
  // Muxed WB outputs
  logic        ready_wb_reg_a;
  logic        rf_write_wb_reg_a;
  logic        outstanding_load_wb_reg_a;
  logic        outstanding_store_wb_reg_a;
  logic [31:0] pc_wb_reg_a;
  logic        perf_instr_ret_wb_reg_a;
  logic        perf_instr_ret_compressed_wb_reg_a;
  logic        perf_instr_ret_wb_spec_reg_a;
  logic        perf_instr_ret_compressed_wb_spec_reg_a;
  logic [31:0] rf_wdata_fwd_wb_reg_a;
  logic [4:0]  rf_waddr_wb_reg_a;
  logic [31:0] rf_wdata_wb_reg_a;
  logic        rf_we_wb_reg_a;
  logic        dummy_instr_wb_reg_a;
  logic        instr_done_wb_reg_a;

  logic        ready_wb_reg_b;
  logic        rf_write_wb_reg_b;
  logic        outstanding_load_wb_reg_b;
  logic        outstanding_store_wb_reg_b;
  logic [31:0] pc_wb_reg_b;
  logic        perf_instr_ret_wb_reg_b;
  logic        perf_instr_ret_compressed_wb_reg_b;
  logic        perf_instr_ret_wb_spec_reg_b;
  logic        perf_instr_ret_compressed_wb_spec_reg_b;
  logic [31:0] rf_wdata_fwd_wb_reg_b;
  logic [4:0]  rf_waddr_wb_reg_b;
  logic [31:0] rf_wdata_wb_reg_b;
  logic        rf_we_wb_reg_b;
  logic        dummy_instr_wb_reg_b;
  logic        instr_done_wb_reg_b;

  //////////////////////
  // Clock management //
  //////////////////////

  // Before going to sleep, wait for I- and D-side
  // interfaces to finish ongoing operations.
  if (SecureIbex) begin : g_core_busy_secure
    // For secure Ibex, the individual bits of core_busy_o are generated from different copies of
    // the various busy signal.
    localparam int unsigned NumBusySignals = 3;
    localparam int unsigned NumBusyBits = $bits(ibex_mubi_t) * NumBusySignals;
    logic [NumBusyBits-1:0] busy_bits_buf;
    prim_buf #(
      .Width(NumBusyBits)
    ) u_fetch_enable_buf (
      .in_i ({$bits(ibex_mubi_t){ctrl_busy, if_busy, lsu_busy}}),
      .out_o(busy_bits_buf)
    );

    // Set core_busy_o to IbexMuBiOn if even a single input is high.
    for (genvar i = 0; i < $bits(ibex_mubi_t); i++) begin : g_core_busy_bits
      if (IbexMuBiOn[i] == 1'b1) begin : g_pos
        assign core_busy_o[i] =  |busy_bits_buf[i*NumBusySignals +: NumBusySignals];
      end else begin : g_neg
        assign core_busy_o[i] = ~|busy_bits_buf[i*NumBusySignals +: NumBusySignals];
      end
    end
  end else begin : g_core_busy_non_secure
    // For non secure Ibex, synthesis is allowed to optimize core_busy_o.
    assign core_busy_o = (ctrl_busy || if_busy || lsu_busy) ? IbexMuBiOn : IbexMuBiOff;
  end

  //////////////
  // PRIMARY IF stage //
  //////////////

  ibex_if_stage #(
    .DmHaltAddr       (DmHaltAddr),
    .DmExceptionAddr  (DmExceptionAddr),
    .DummyInstructions(DummyInstructions),
    .ICache           (ICache),
    .ICacheECC        (ICacheECC),
    .BusSizeECC       (BusSizeECC),
    .TagSizeECC       (TagSizeECC),
    .LineSizeECC      (LineSizeECC),
    .PCIncrCheck      (PCIncrCheck),
    .ResetAll         (ResetAll),
    .RndCnstLfsrSeed  (RndCnstLfsrSeed),
    .RndCnstLfsrPerm  (RndCnstLfsrPerm),
    .BranchPredictor  (BranchPredictor),
    .MemECC           (MemECC),
    .MemDataWidth     (MemDataWidth)
  ) if_stage_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .boot_addr_i(boot_addr_i),
    .req_i      (instr_req_gated),  // instruction request control

    // instruction cache interface 
    .instr_req_o       (instr_req_o_primary),
    .instr_addr_o      (instr_addr_o_primary),
    .instr_gnt_i       (instr_gnt_i),
    .instr_rvalid_i    (instr_rvalid_i),
    .instr_rdata_i     (instr_rdata_i),
    .instr_bus_err_i   (instr_err_i),
    .instr_intg_err_o  (instr_intg_err_primary),

    .ic_tag_req_o      (ic_tag_req_o_primary),
    .ic_tag_write_o    (ic_tag_write_o_primary),
    .ic_tag_addr_o     (ic_tag_addr_o_primary),
    .ic_tag_wdata_o    (ic_tag_wdata_o_primary),
    .ic_tag_rdata_i    (ic_tag_rdata_i),
    .ic_data_req_o     (ic_data_req_o_primary),
    .ic_data_write_o   (ic_data_write_o_primary),
    .ic_data_addr_o    (ic_data_addr_o_primary),
    .ic_data_wdata_o   (ic_data_wdata_o_primary),
    .ic_data_rdata_i   (ic_data_rdata_i),
    .ic_scr_key_valid_i(ic_scr_key_valid_i),
    .ic_scr_key_req_o  (ic_scr_key_req_o_primary),

    // outputs to ID stage
    .instr_valid_id_o        (instr_valid_id_primary),
    .instr_new_id_o          (instr_new_id_primary),
    .instr_rdata_id_o        (instr_rdata_id_primary),
    .instr_rdata_alu_id_o    (instr_rdata_alu_id_primary),
    .instr_rdata_c_id_o      (instr_rdata_c_id_primary),
    .instr_is_compressed_id_o(instr_is_compressed_id_primary),
    .instr_bp_taken_o        (instr_bp_taken_id_primary),
    .instr_fetch_err_o       (instr_fetch_err_primary),
    .instr_fetch_err_plus2_o (instr_fetch_err_plus2_primary),
    .illegal_c_insn_id_o     (illegal_c_insn_id_primary),
    .dummy_instr_id_o        (dummy_instr_id_primary),
    .pc_if_o                 (pc_if_primary),
    .pc_id_o                 (pc_id_primary),
    .pmp_err_if_i            (pmp_req_err[PMP_I]),
    .pmp_err_if_plus2_i      (pmp_req_err[PMP_I2]),

    // control signals
    .instr_valid_clear_i   (instr_valid_clear),
    .pc_set_i              (pc_set),
    .pc_mux_i              (pc_mux_id),
    .nt_branch_mispredict_i(nt_branch_mispredict),
    .exc_pc_mux_i          (exc_pc_mux_id),
    .exc_cause             (exc_cause),
    .dummy_instr_en_i      (dummy_instr_en),
    .dummy_instr_mask_i    (dummy_instr_mask),
    .dummy_instr_seed_en_i (dummy_instr_seed_en),
    .dummy_instr_seed_i    (dummy_instr_seed),
    .icache_enable_i       (icache_enable),
    .icache_inval_i        (icache_inval),
    .icache_ecc_error_o    (icache_ecc_error_primary),

    // branch targets
    .branch_target_ex_i(branch_target_ex),
    .nt_branch_addr_i  (nt_branch_addr),

    // CSRs
    .csr_mepc_i      (csr_mepc),  // exception return address
    .csr_depc_i      (csr_depc),  // debug return address
    .csr_mtvec_i     (csr_mtvec),  // trap-vector base address
    .csr_mtvec_init_o(csr_mtvec_init_primary),

    // pipeline stalls
    .id_in_ready_i(id_in_ready),

    .pc_mismatch_alert_o(pc_mismatch_alert_primary),
    .if_busy_o          (if_busy_primary)
  );

  // Core is waiting for the ISide when ID/EX stage is ready for a new instruction but none are
  // available
  assign perf_iside_wait = id_in_ready & ~instr_valid_id;
  
  ///////////////////////////////////////////////////////////////
  // REDUNDANT IF stage - duplicate for redundancy
  ///////////////////////////////////////////////////////////////
  
  ibex_if_stage #(
    .DmHaltAddr       (DmHaltAddr),
    .DmExceptionAddr  (DmExceptionAddr),
    .DummyInstructions(DummyInstructions),
    .ICache           (ICache),
    .ICacheECC        (ICacheECC),
    .BusSizeECC       (BusSizeECC),
    .TagSizeECC       (TagSizeECC),
    .LineSizeECC      (LineSizeECC),
    .PCIncrCheck      (PCIncrCheck),
    .ResetAll         (ResetAll),
    .RndCnstLfsrSeed  (RndCnstLfsrSeed),
    .RndCnstLfsrPerm  (RndCnstLfsrPerm),
    .BranchPredictor  (BranchPredictor),
    .MemECC           (MemECC),
    .MemDataWidth     (MemDataWidth)
  ) if_stage_i_redundant (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    .boot_addr_i(boot_addr_i),
    .req_i      (instr_req_gated),

    // instruction cache interface - connect to redundant icache
    .instr_req_o       (instr_req_o_r),  
    .instr_gnt_i       (instr_gnt_i),
    .instr_rvalid_i    (instr_rvalid_i),
    .instr_rdata_i     (instr_rdata_i),
    .instr_bus_err_i   (instr_err_i),
    .instr_intg_err_o  (instr_intg_err_r),

    .ic_tag_req_o      (ic_tag_req_o_r),
    .ic_tag_write_o    (ic_tag_write_o_r),
    .ic_tag_addr_o     (ic_tag_addr_o_r),
    .ic_tag_wdata_o    (ic_tag_wdata_o_r),
    .ic_tag_rdata_i    (ic_tag_rdata_i),
    .ic_data_req_o     (ic_data_req_o_r),
    .ic_data_write_o   (ic_data_write_o_r),
    .ic_data_addr_o    (ic_data_addr_o_r),
    .ic_data_wdata_o   (ic_data_wdata_o_r),
    .ic_data_rdata_i   (ic_data_rdata_i),
    .ic_scr_key_valid_i(ic_scr_key_valid_i),
    .ic_scr_key_req_o  (ic_scr_key_req_o_r),

    // outputs to ID stage
    .instr_valid_id_o        (instr_valid_id_r),
    .instr_new_id_o          (instr_new_id_r),
    .instr_rdata_id_o        (instr_rdata_id_r),
    .instr_rdata_alu_id_o    (instr_rdata_alu_id_r),
    .instr_rdata_c_id_o      (instr_rdata_c_id_r),
    .instr_is_compressed_id_o(instr_is_compressed_id_r),
    .instr_bp_taken_o        (instr_bp_taken_id_r),
    .instr_fetch_err_o       (instr_fetch_err_r),
    .instr_fetch_err_plus2_o (instr_fetch_err_plus2_r),
    .illegal_c_insn_id_o     (illegal_c_insn_id_r),
    .dummy_instr_id_o        (dummy_instr_id_r),
    .pc_if_o                 (pc_if_r),
    .pc_id_o                 (pc_id_r),
    .pmp_err_if_i            (pmp_req_err[PMP_I]),
    .pmp_err_if_plus2_i      (pmp_req_err[PMP_I2]),

    // control signals
    .instr_valid_clear_i   (instr_valid_clear),
    .pc_set_i              (pc_set),
    .pc_mux_i              (pc_mux_id),
    .nt_branch_mispredict_i(nt_branch_mispredict),
    .exc_pc_mux_i          (exc_pc_mux_id),
    .exc_cause             (exc_cause),
    .dummy_instr_en_i      (dummy_instr_en),
    .dummy_instr_mask_i    (dummy_instr_mask),
    .dummy_instr_seed_en_i (dummy_instr_seed_en),
    .dummy_instr_seed_i    (dummy_instr_seed),
    .icache_enable_i       (icache_enable),
    .icache_inval_i        (icache_inval),
    .icache_ecc_error_o    (icache_ecc_error_r),

    // branch targets
    .branch_target_ex_i(branch_target_ex),
    .nt_branch_addr_i  (nt_branch_addr),

    // CSRs
    .csr_mepc_i      (csr_mepc),
    .csr_depc_i      (csr_depc),
    .csr_mtvec_i     (csr_mtvec),
    .csr_mtvec_init_o(csr_mtvec_init_r),

    // pipeline stalls
    .id_in_ready_i(id_in_ready),

    .pc_mismatch_alert_o(pc_mismatch_alert_r),
    .if_busy_o          (if_busy_r)
  );
  ///////////////////////////////////////////////////////////////
  // IF stage output muxes
  ///////////////////////////////////////////////////////////////

    redundancy_mux #(.WIDTH(1)) instr_valid_id_red_mux (
      .operand_a(instr_valid_id_primary),
      .operand_b(instr_valid_id_r),
      .result(instr_valid_id_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) instr_new_id_red_mux (
      .operand_a(instr_new_id_primary),
      .operand_b(instr_new_id_r),
      .result(instr_new_id_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(32)) instr_rdata_id_red_mux (
      .operand_a(instr_rdata_id_primary),
      .operand_b(instr_rdata_id_r),
      .result(instr_rdata_id_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(32)) instr_rdata_alu_id_red_mux (
      .operand_a(instr_rdata_alu_id_primary),
      .operand_b(instr_rdata_alu_id_r),
      .result(instr_rdata_alu_id_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(32)) instr_rdata_c_id_red_mux (
      .operand_a(instr_rdata_c_id_primary),
      .operand_b(instr_rdata_c_id_r),
      .result(instr_rdata_c_id_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) instr_is_compressed_id_red_mux (
      .operand_a(instr_is_compressed_id_primary),
      .operand_b(instr_is_compressed_id_r),
      .result(instr_is_compressed_id_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) instr_bp_taken_id_red_mux (
      .operand_a(instr_bp_taken_id_primary),
      .operand_b(instr_bp_taken_id_r),
      .result(instr_bp_taken_id_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) instr_fetch_err_red_mux (
      .operand_a(instr_fetch_err_primary),
      .operand_b(instr_fetch_err_r),
      .result(instr_fetch_err_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) instr_fetch_err_plus2_red_mux (
      .operand_a(instr_fetch_err_plus2_primary),
      .operand_b(instr_fetch_err_plus2_r),
      .result(instr_fetch_err_plus2_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) illegal_c_insn_id_red_mux (
      .operand_a(illegal_c_insn_id_primary),
      .operand_b(illegal_c_insn_id_r),
      .result(illegal_c_insn_id_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) dummy_instr_id_red_mux (
      .operand_a(dummy_instr_id_primary),
      .operand_b(dummy_instr_id_r),
      .result(dummy_instr_id_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(32)) pc_if_red_mux (
      .operand_a(pc_if_primary),
      .operand_b(pc_if_r),
      .result(pc_if_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(32)) pc_id_red_mux (
      .operand_a(pc_id_primary),
      .operand_b(pc_id_r),
      .result(pc_id_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(32)) csr_mtvec_init_red_mux (
      .operand_a(csr_mtvec_init_primary),
      .operand_b(csr_mtvec_init_r),
      .result(csr_mtvec_init_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) pc_mismatch_alert_red_mux (
      .operand_a(pc_mismatch_alert_primary),
      .operand_b(pc_mismatch_alert_r),
      .result(pc_mismatch_alert_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(32)) if_busy_red_mux (
      .operand_a(if_busy_primary),
      .operand_b(if_busy_r),
      .result(if_busy_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) instr_intg_err_red_mux (
      .operand_a(instr_intg_err_primary),
      .operand_b(instr_intg_err_r),
      .result(instr_intg_err_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) icache_ecc_error_red_mux (
      .operand_a(icache_ecc_error_primary),
      .operand_b(icache_ecc_error_r),
      .result(icache_ecc_error_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) instr_req_o_red_mux (
      .operand_a(instr_req_o_primary),
      .operand_b(instr_req_o_r),
      .result(instr_req_o_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(32)) instr_addr_o_red_mux (
      .operand_a(instr_addr_o_primary),
      .operand_b(instr_addr_o_r),
      .result(instr_addr_o_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(IC_NUM_WAYS)) ic_tag_req_o_red_mux (
      .operand_a(ic_tag_req_o_primary),
      .operand_b(ic_tag_req_o_r),
      .result(ic_tag_req_o_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) ic_tag_write_o_red_mux (
      .operand_a(ic_tag_write_o_primary),
      .operand_b(ic_tag_write_o_r),
      .result(ic_tag_write_o_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(IC_INDEX_W)) ic_tag_addr_o_red_mux (
      .operand_a(ic_tag_addr_o_primary),
      .operand_b(ic_tag_addr_o_r),
      .result(ic_tag_addr_o_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(TagSizeECC)) ic_tag_wdata_o_red_mux (
      .operand_a(ic_tag_wdata_o_primary),
      .operand_b(ic_tag_wdata_o_r),
      .result(ic_tag_wdata_o_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(IC_NUM_WAYS)) ic_data_req_o_red_mux (
      .operand_a(ic_data_req_o_primary),
      .operand_b(ic_data_req_o_r),
      .result(ic_data_req_o_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) ic_data_write_o_red_mux (
      .operand_a(ic_data_write_o_primary),
      .operand_b(ic_data_write_o_r),
      .result(ic_data_write_o_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(IC_INDEX_W)) ic_data_addr_o_red_mux (
      .operand_a(ic_data_addr_o_primary),
      .operand_b(ic_data_addr_o_r),
      .result(ic_data_addr_o_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(32*(1<<IC_LINE_SIZE))) ic_data_wdata_o_red_mux (
      .operand_a(ic_data_wdata_o_primary),
      .operand_b(ic_data_wdata_o_r),
      .result(ic_data_wdata_o_mux),
      .select(redundancy_sel_if)
    );

    redundancy_mux #(.WIDTH(1)) ic_scr_key_req_o_red_mux (
      .operand_a(ic_scr_key_req_o_primary),
      .operand_b(ic_scr_key_req_o_r),
      .result(ic_scr_key_req_o_mux),
      .select(redundancy_sel_if)
    );
 
    assign instr_valid_id_reg_a = instr_valid_id_mux;
    assign instr_new_id_reg_a   = instr_new_id_mux;
    assign instr_rdata_id_reg_a = instr_rdata_id_mux;
    assign instr_rdata_alu_id_reg_a = instr_rdata_alu_id_mux;
    assign instr_rdata_c_id_reg_a   = instr_rdata_c_id_mux;
    assign instr_is_compressed_id_reg_a = instr_is_compressed_id_mux;
    assign instr_bp_taken_id_reg_a = instr_bp_taken_id_mux;
    assign instr_fetch_err_reg_a = instr_fetch_err_mux;
    assign instr_fetch_err_plus2_reg_a = instr_fetch_err_plus2_mux;
    assign illegal_c_insn_id_reg_a = illegal_c_insn_id_mux;
    assign dummy_instr_id_reg_a = dummy_instr_id_mux;
    assign pc_if_reg_a = pc_if_mux;
    assign pc_id_reg_a = pc_id_mux;
    assign csr_mtvec_init_reg_a = csr_mtvec_init_mux;
    assign pc_mismatch_alert_reg_a = pc_mismatch_alert_mux;
    assign if_busy_reg_a = if_busy_mux;
    assign instr_intg_err_reg_a = instr_intg_err_mux;
    assign icache_ecc_error_reg_a = icache_ecc_error_mux;
    assign instr_req_o_reg_a = instr_req_o_mux;
    assign instr_addr_o_reg_a = instr_addr_o_mux;
    assign ic_tag_req_o_reg_a = ic_tag_req_o_mux;
    assign ic_tag_write_o_reg_a = ic_tag_write_o_mux;
    assign ic_tag_addr_o_reg_a = ic_tag_addr_o_mux;
    assign ic_tag_wdata_o_reg_a = ic_tag_wdata_o_mux;
    assign ic_data_req_o_reg_a = ic_data_req_o_mux;
    assign ic_data_write_o_reg_a = ic_data_write_o_mux;
    assign ic_data_addr_o_reg_a = ic_data_addr_o_mux;
    assign ic_data_wdata_o_reg_a = ic_data_wdata_o_mux;
    assign ic_scr_key_req_o_reg_a = ic_scr_key_req_o_mux;

    assign instr_valid_id_reg_b = instr_valid_id_mux;
    assign instr_new_id_reg_b   = instr_new_id_mux;
    assign instr_rdata_id_reg_b = instr_rdata_id_mux;
    assign instr_rdata_alu_id_reg_b = instr_rdata_alu_id_mux;
    assign instr_rdata_c_id_reg_b   = instr_rdata_c_id_mux;
    assign instr_is_compressed_id_reg_b = instr_is_compressed_id_mux;
    assign instr_bp_taken_id_reg_b = instr_bp_taken_id_mux;
    assign instr_fetch_err_reg_b = instr_fetch_err_mux;
    assign instr_fetch_err_plus2_reg_b = instr_fetch_err_plus2_mux;
    assign illegal_c_insn_id_reg_b = illegal_c_insn_id_mux;
    assign dummy_instr_id_reg_b = dummy_instr_id_mux;
    assign pc_if_reg_b = pc_if_mux;
    assign pc_id_reg_b = pc_id_mux;
    assign csr_mtvec_init_reg_b = csr_mtvec_init_mux;
    assign pc_mismatch_alert_reg_b = pc_mismatch_alert_mux;
    assign if_busy_reg_b = if_busy_mux;
    assign instr_intg_err_reg_b = instr_intg_err_mux;
    assign icache_ecc_error_reg_b = icache_ecc_error_mux;
    assign instr_req_o_reg_b = instr_req_o_mux;
    assign instr_addr_o_reg_b = instr_addr_o_mux;
    assign ic_tag_req_o_reg_b = ic_tag_req_o_mux;
    assign ic_tag_write_o_reg_b = ic_tag_write_o_mux;
    assign ic_tag_addr_o_reg_b = ic_tag_addr_o_mux;
    assign ic_tag_wdata_o_reg_b = ic_tag_wdata_o_mux;
    assign ic_data_req_o_reg_b = ic_data_req_o_mux;
    assign ic_data_write_o_reg_b = ic_data_write_o_mux;
    assign ic_data_addr_o_reg_b = ic_data_addr_o_mux;
    assign ic_data_wdata_o_reg_b = ic_data_wdata_o_mux;
    assign ic_scr_key_req_o_reg_b = ic_scr_key_req_o_mux;

    redundancy_mux #(.WIDTH(1)) instr_valid_id_red_mux_reg (
      .operand_a(instr_valid_id_reg_a),
      .operand_b(instr_valid_id_reg_b),
      .result(instr_valid_id),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) instr_new_id_red_mux_reg (
      .operand_a(instr_new_id_reg_a),
      .operand_b(instr_new_id_reg_b),
      .result(instr_new_id),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(32)) instr_rdata_id_red_mux_reg (
      .operand_a(instr_rdata_id_reg_a),
      .operand_b(instr_rdata_id_reg_b),
      .result(instr_rdata_id),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(32)) instr_rdata_alu_id_red_mux_reg (
      .operand_a(instr_rdata_alu_id_reg_a),
      .operand_b(instr_rdata_alu_id_reg_b),
      .result(instr_rdata_alu_id),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(32)) instr_rdata_c_id_red_mux_reg (
      .operand_a(instr_rdata_c_id_reg_a),
      .operand_b(instr_rdata_c_id_reg_b),
      .result(instr_rdata_c_id),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) instr_is_compressed_id_red_mux_reg (
      .operand_a(instr_is_compressed_id_reg_a),
      .operand_b(instr_is_compressed_id_reg_b),
      .result(instr_is_compressed_id),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) instr_bp_taken_id_red_mux_reg (
      .operand_a(instr_bp_taken_id_reg_a),
      .operand_b(instr_bp_taken_id_reg_b),
      .result(instr_bp_taken_id),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) instr_fetch_err_red_mux_reg (
      .operand_a(instr_fetch_err_reg_a),
      .operand_b(instr_fetch_err_reg_b),
      .result(instr_fetch_err),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) instr_fetch_err_plus2_red_mux_reg (
      .operand_a(instr_fetch_err_plus2_reg_a),
      .operand_b(instr_fetch_err_plus2_reg_b),
      .result(instr_fetch_err_plus2),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) illegal_c_insn_id_red_mux_reg (
      .operand_a(illegal_c_insn_id_reg_a),
      .operand_b(illegal_c_insn_id_reg_b),
      .result(illegal_c_insn_id),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) dummy_instr_id_red_mux_reg (
      .operand_a(dummy_instr_id_reg_a),
      .operand_b(dummy_instr_id_reg_b),
      .result(dummy_instr_id),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(32)) pc_if_red_mux_reg (
      .operand_a(pc_if_reg_a),
      .operand_b(pc_if_reg_b),
      .result(pc_if),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(32)) pc_id_red_mux_reg (
      .operand_a(pc_id_primary_reg_a),
      .operand_b(pc_id_reg_b),
      .result(pc_id),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(32)) csr_mtvec_init_red_mux_reg (
      .operand_a(csr_mtvec_init_primary_reg_a),
      .operand_b(csr_mtvec_init_reg_b),
      .result(csr_mtvec_init),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) pc_mismatch_alert_red_mux_reg (
      .operand_a(pc_mismatch_alert_reg_a),
      .operand_b(pc_mismatch_alert_reg_b),
      .result(pc_mismatch_alert),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) if_busy_red_mux_reg (
      .operand_a(if_busy_reg_a),
      .operand_b(if_busy_reg_b),
      .result(if_busy),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) instr_intg_err_red_mux_reg (
      .operand_a(instr_intg_err_reg_a),
      .operand_b(instr_intg_err_reg_b),
      .result(instr_intg_err),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) icache_ecc_error_red_mux_reg (
      .operand_a(icache_ecc_error_reg_a),
      .operand_b(icache_ecc_error_reg_b),
      .result(icache_ecc_error),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) instr_req_o_red_mux_reg (
      .operand_a(instr_req_o_reg_a),
      .operand_b(instr_req_o_reg_b),
      .result(instr_req_o),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(32)) instr_addr_o_red_mux_reg (
      .operand_a(instr_addr_o_reg_a),
      .operand_b(instr_addr_o_reg_b),
      .result(instr_addr_o),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(IC_NUM_WAYS)) ic_tag_req_o_red_mux_reg (
      .operand_a(ic_tag_req_o_reg_a),
      .operand_b(ic_tag_req_o_reg_b),
      .result(ic_tag_req_o),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) ic_tag_write_o_red_mux_reg (
      .operand_a(ic_tag_write_o_reg_a),
      .operand_b(ic_tag_write_o_reg_b),
      .result(ic_tag_write_o),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(IC_INDEX_W)) ic_tag_addr_o_red_mux_reg (
      .operand_a(ic_tag_addr_o_reg_a),
      .operand_b(ic_tag_addr_o_reg_b),
      .result(ic_tag_addr_o),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(TagSizeECC)) ic_tag_wdata_o_red_mux_reg (
      .operand_a(ic_tag_wdata_o_reg_a),
      .operand_b(ic_tag_wdata_o_reg_b),
      .result(ic_tag_wdata_o),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(IC_NUM_WAYS)) ic_data_req_o_red_mux_reg (
      .operand_a(ic_data_req_o_reg_a),
      .operand_b(ic_data_req_o_reg_b),
      .result(ic_data_req_o),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) ic_data_write_o_red_mux_reg (
      .operand_a(ic_data_write_o_reg_a),
      .operand_b(ic_data_write_o_reg_b),
      .result(ic_data_write_o),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(IC_INDEX_W)) ic_data_addr_o_red_mux_reg (
      .operand_a(ic_data_addr_o_reg_a),
      .operand_b(ic_data_addr_o_reg_b),
      .result(ic_data_addr_o),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(32*(1<<IC_LINE_SIZE))) ic_data_wdata_o_red_mux_reg (
      .operand_a(ic_data_wdata_o_reg_a),
      .operand_b(ic_data_wdata_o_reg_b),
      .result(ic_data_wdata_o),
      .select(redundancy_sel_if_reg)
    );

    redundancy_mux #(.WIDTH(1)) ic_scr_key_req_o_red_mux_reg (
      .operand_a(ic_scr_key_req_o_reg_a),
      .operand_b(ic_scr_key_req_o_reg_b),
      .result(ic_scr_key_req_o),
      .select(redundancy_sel_if_reg)
    );

  // Multi-bit fetch enable used when SecureIbex == 1. When SecureIbex == 0 only use the bottom-bit
  // of fetch_enable_i. Ensure the multi-bit encoding has the bottom bit set for on and unset for
  // off so IbexMuBiOn/IbexMuBiOff can be used without needing to know the value of SecureIbex.
  `ASSERT_INIT(IbexMuBiSecureOnBottomBitSet,    IbexMuBiOn[0] == 1'b1)
  `ASSERT_INIT(IbexMuBiSecureOffBottomBitClear, IbexMuBiOff[0] == 1'b0)

  // fetch_enable_i can be used to stop the core fetching new instructions
  if (SecureIbex) begin : g_instr_req_gated_secure
    // For secure Ibex fetch_enable_i must be a specific multi-bit pattern to enable instruction
    // fetch
    // SEC_CM: FETCH.CTRL.LC_GATED
    assign instr_req_gated = instr_req_int & (fetch_enable_i == IbexMuBiOn);
    assign instr_exec      = fetch_enable_i == IbexMuBiOn;
  end else begin : g_instr_req_gated_non_secure
    // For non secure Ibex only the bottom bit of fetch enable is considered
    logic unused_fetch_enable;
    assign unused_fetch_enable = ^fetch_enable_i[$bits(ibex_mubi_t)-1:1];

    assign instr_req_gated = instr_req_int & fetch_enable_i[0];
    assign instr_exec      = fetch_enable_i[0];
  end

  //////////////
  // ID stage //
  //////////////

  ibex_id_stage #(
    .RV32E          (RV32E),
    .RV32M          (RV32M),
    .RV32B          (RV32B),
    .BranchTargetALU(BranchTargetALU),
    .DataIndTiming  (DataIndTiming),
    .WritebackStage (WritebackStage),
    .BranchPredictor(BranchPredictor),
    .MemECC         (MemECC)
  ) id_stage_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // Processor Enable
    .ctrl_busy_o   (ctrl_busy_primary),
    .illegal_insn_o(illegal_insn_id_primary),

    // from/to IF-ID pipeline register
    .instr_valid_i        (instr_valid_id),
    .instr_rdata_i        (instr_rdata_id),
    .instr_rdata_alu_i    (instr_rdata_alu_id),
    .instr_rdata_c_i      (instr_rdata_c_id),
    .instr_is_compressed_i(instr_is_compressed_id),
    .instr_bp_taken_i     (instr_bp_taken_id),

    // Jumps and branches
    .branch_decision_i(branch_decision),

    // IF and ID control signals
    .instr_first_cycle_id_o(instr_first_cycle_id_primary),
    .instr_valid_clear_o   (instr_valid_clear_primary),
    .id_in_ready_o         (id_in_ready_primary),
    .instr_exec_i          (instr_exec),
    .instr_req_o           (instr_req_int_primary),
    .pc_set_o              (pc_set_primary),
    .pc_mux_o              (pc_mux_id_primary),
    .nt_branch_mispredict_o(nt_branch_mispredict_primary),
    .nt_branch_addr_o      (nt_branch_addr_primary),
    .exc_pc_mux_o          (exc_pc_mux_id_primary),
    .exc_cause_o           (exc_cause_primary),
    .icache_inval_o        (icache_inval_primary),

    .instr_fetch_err_i      (instr_fetch_err),
    .instr_fetch_err_plus2_i(instr_fetch_err_plus2),
    .illegal_c_insn_i       (illegal_c_insn_id),

    .pc_id_i(pc_id),

    // Stalls
    .ex_valid_i      (ex_valid),
    .lsu_resp_valid_i(lsu_resp_valid),

    .alu_operator_ex_o (alu_operator_ex_primary),
    .alu_operand_a_ex_o(alu_operand_a_ex_primary),
    .alu_operand_b_ex_o(alu_operand_b_ex_primary),

    .imd_val_q_ex_o (imd_val_q_ex_primary),
    .imd_val_d_ex_i (imd_val_d_ex),
    .imd_val_we_ex_i(imd_val_we_ex),

    .bt_a_operand_o(bt_a_operand_primary),
    .bt_b_operand_o(bt_b_operand_primary),

    .mult_en_ex_o            (mult_en_ex_primary),
    .div_en_ex_o             (div_en_ex_primary),
    .mult_sel_ex_o           (mult_sel_ex_primary),
    .div_sel_ex_o            (div_sel_ex_primary),
    .multdiv_operator_ex_o   (multdiv_operator_ex_primary),
    .multdiv_signed_mode_ex_o(multdiv_signed_mode_ex_primary),
    .multdiv_operand_a_ex_o  (multdiv_operand_a_ex_primary),
    .multdiv_operand_b_ex_o  (multdiv_operand_b_ex_primary),
    .multdiv_ready_id_o      (multdiv_ready_id_primary),

    // CSR ID/EX
    .csr_access_o         (csr_access_primary),
    .csr_op_o             (csr_op_primary),
    .csr_addr_o           (csr_addr_primary),
    .csr_op_en_o          (csr_op_en_primary),
    .csr_save_if_o        (csr_save_if_primary),  // control signal to save PC
    .csr_save_id_o        (csr_save_id_primary),  // control signal to save PC
    .csr_save_wb_o        (csr_save_wb_primary),  // control signal to save PC
    .csr_restore_mret_id_o(csr_restore_mret_id_primary),  // restore mstatus upon MRET
    .csr_restore_dret_id_o(csr_restore_dret_id_primary),  // restore mstatus upon MRET
    .csr_save_cause_o     (csr_save_cause_primary),
    .csr_mtval_o          (csr_mtval_primary),
    .priv_mode_i          (priv_mode_id),
    .csr_mstatus_tw_i     (csr_mstatus_tw),
    .illegal_csr_insn_i   (illegal_csr_insn_id),
    .data_ind_timing_i    (data_ind_timing),

    // LSU
    .lsu_req_o     (lsu_req_primary),  // to load store unit
    .lsu_we_o      (lsu_we_primary),  // to load store unit
    .lsu_type_o    (lsu_type_primary),  // to load store unit
    .lsu_sign_ext_o(lsu_sign_ext_primary),  // to load store unit
    .lsu_wdata_o   (lsu_wdata_primary),  // to load store unit
    .lsu_req_done_i(lsu_req_done),  // from load store unit

    .lsu_addr_incr_req_i(lsu_addr_incr_req),
    .lsu_addr_last_i    (lsu_addr_last),

    .lsu_load_err_i           (lsu_load_err),
    .lsu_load_resp_intg_err_i (lsu_load_resp_intg_err),
    .lsu_store_err_i          (lsu_store_err),
    .lsu_store_resp_intg_err_i(lsu_store_resp_intg_err),

    .expecting_load_resp_o (expecting_load_resp_id_primary),
    .expecting_store_resp_o(expecting_store_resp_id_primary),

    // Interrupt Signals
    .csr_mstatus_mie_i(csr_mstatus_mie),
    .irq_pending_i    (irq_pending_o),
    .irqs_i           (irqs),
    .irq_nm_i         (irq_nm_i),
    .nmi_mode_o       (nmi_mode_primary),

    // Debug Signal
    .debug_mode_o         (debug_mode_primary),
    .debug_mode_entering_o(debug_mode_entering_primary),
    .debug_cause_o        (debug_cause_primary),
    .debug_csr_save_o     (debug_csr_save_primary),
    .debug_req_i          (debug_req_i),
    .debug_single_step_i  (debug_single_step),
    .debug_ebreakm_i      (debug_ebreakm),
    .debug_ebreaku_i      (debug_ebreaku),
    .trigger_match_i      (trigger_match),

    // write data to commit in the register file
    .result_ex_i(result_ex),
    .csr_rdata_i(csr_rdata),

    .rf_raddr_a_o      (rf_raddr_a_primary),
    .rf_rdata_a_i      (rf_rdata_a),
    .rf_raddr_b_o      (rf_raddr_b_primary),
    .rf_rdata_b_i      (rf_rdata_b),
    .rf_ren_a_o        (rf_ren_a_primary),
    .rf_ren_b_o        (rf_ren_b_primary),
    .rf_waddr_id_o     (rf_waddr_id_primary),
    .rf_wdata_id_o     (rf_wdata_id_primary),
    .rf_we_id_o        (rf_we_id_primary),
    .rf_rd_a_wb_match_o(rf_rd_a_wb_match_primary),
    .rf_rd_b_wb_match_o(rf_rd_b_wb_match_primary),

    .rf_waddr_wb_i    (rf_waddr_wb),
    .rf_wdata_fwd_wb_i(rf_wdata_fwd_wb),
    .rf_write_wb_i    (rf_write_wb),

    .en_wb_o               (en_wb_primary),
    .instr_type_wb_o       (instr_type_wb_primary),
    .instr_perf_count_id_o (instr_perf_count_id_primary),
    .ready_wb_i            (ready_wb),
    .outstanding_load_wb_i (outstanding_load_wb),
    .outstanding_store_wb_i(outstanding_store_wb),

    // Performance Counters
    .perf_jump_o      (perf_jump_primary),
    .perf_branch_o    (perf_branch_primary),
    .perf_tbranch_o   (perf_tbranch_primary),
    .perf_dside_wait_o(perf_dside_wait_primary),
    .perf_mul_wait_o  (perf_mul_wait_primary),
    .perf_div_wait_o  (perf_div_wait_primary),
    .instr_id_done_o  (instr_id_done_primary)
  );

  // for RVFI only
  assign unused_illegal_insn_id = illegal_insn_id;

  ///////////////////////////////////////////////////////////////
  // REDUNDANT ID stage - duplicate for redundancy
  ///////////////////////////////////////////////////////////////
  
  ibex_id_stage #(
    .RV32E          (RV32E),
    .RV32M          (RV32M),
    .RV32B          (RV32B),
    .BranchTargetALU(BranchTargetALU),
    .DataIndTiming  (DataIndTiming),
    .WritebackStage (WritebackStage),
    .BranchPredictor(BranchPredictor),
    .MemECC         (MemECC)
  ) id_stage_i_redundant (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // Processor Enable
    .ctrl_busy_o   (ctrl_busy_r),
    .illegal_insn_o(illegal_insn_id_r),

    // from/to IF-ID pipeline register
    .instr_valid_i        (instr_valid_id),
    .instr_rdata_i        (instr_rdata_id),
    .instr_rdata_alu_i    (instr_rdata_alu_id),
    .instr_rdata_c_i      (instr_rdata_c_id),
    .instr_is_compressed_i(instr_is_compressed_id),
    .instr_bp_taken_i     (instr_bp_taken_id),

    // Jumps and branches
    .branch_decision_i(branch_decision),

    // IF and ID control signals
    .instr_first_cycle_id_o(instr_first_cycle_id_r),
    .instr_valid_clear_o   (instr_valid_clear_r),
    .id_in_ready_o         (id_in_ready_r),
    .instr_exec_i          (instr_exec),
    .instr_req_o           (instr_req_int_r),
    .pc_set_o              (pc_set_r),
    .pc_mux_o              (pc_mux_id_r),
    .nt_branch_mispredict_o(nt_branch_mispredict_r),
    .nt_branch_addr_o      (nt_branch_addr_r),
    .exc_pc_mux_o          (exc_pc_mux_id_r),
    .exc_cause_o           (exc_cause_r),
    .icache_inval_o        (icache_inval_r),

    .instr_fetch_err_i      (instr_fetch_err),
    .instr_fetch_err_plus2_i(instr_fetch_err_plus2),
    .illegal_c_insn_i       (illegal_c_insn_id),

    .pc_id_i(pc_id),

    // Stalls
    .ex_valid_i      (ex_valid),
    .lsu_resp_valid_i(lsu_resp_valid),

    .alu_operator_ex_o (alu_operator_ex_r),
    .alu_operand_a_ex_o(alu_operand_a_ex_r),
    .alu_operand_b_ex_o(alu_operand_b_ex_r),

    .imd_val_q_ex_o (imd_val_q_ex_r),
    .imd_val_d_ex_i (imd_val_d_ex),
    .imd_val_we_ex_i(imd_val_we_ex),

    .bt_a_operand_o(bt_a_operand_r),
    .bt_b_operand_o(bt_b_operand_r),

    .mult_en_ex_o            (mult_en_ex_r),
    .div_en_ex_o             (div_en_ex_r),
    .mult_sel_ex_o           (mult_sel_ex_r),
    .div_sel_ex_o            (div_sel_ex_r),
    .multdiv_operator_ex_o   (multdiv_operator_ex_r),
    .multdiv_signed_mode_ex_o(multdiv_signed_mode_ex_r),
    .multdiv_operand_a_ex_o  (multdiv_operand_a_ex_r),
    .multdiv_operand_b_ex_o  (multdiv_operand_b_ex_r),
    .multdiv_ready_id_o      (multdiv_ready_id_r),

    // CSR ID/EX
    .csr_access_o         (csr_access_r),
    .csr_op_o             (csr_op_r),
    .csr_addr_o           (csr_addr_r),
    .csr_op_en_o          (csr_op_en_r),
    .csr_save_if_o        (csr_save_if_r),
    .csr_save_id_o        (csr_save_id_r),
    .csr_save_wb_o        (csr_save_wb_r),
    .csr_restore_mret_id_o(csr_restore_mret_id_r),
    .csr_restore_dret_id_o(csr_restore_dret_id_r),
    .csr_save_cause_o     (csr_save_cause_r),
    .csr_mtval_o          (csr_mtval_r),
    .priv_mode_i          (priv_mode_id),
    .csr_mstatus_tw_i     (csr_mstatus_tw),
    .illegal_csr_insn_i   (illegal_csr_insn_id),
    .data_ind_timing_i    (data_ind_timing),

    // LSU
    .lsu_req_o     (lsu_req_r),
    .lsu_we_o      (lsu_we_r),
    .lsu_type_o    (lsu_type_r),
    .lsu_sign_ext_o(lsu_sign_ext_r),
    .lsu_wdata_o   (lsu_wdata_r),
    .lsu_req_done_i(lsu_req_done),

    .lsu_addr_incr_req_i(lsu_addr_incr_req),
    .lsu_addr_last_i    (lsu_addr_last),

    .lsu_load_err_i           (lsu_load_err),
    .lsu_load_resp_intg_err_i (lsu_load_resp_intg_err),
    .lsu_store_err_i          (lsu_store_err),
    .lsu_store_resp_intg_err_i(lsu_store_resp_intg_err),

    .expecting_load_resp_o (expecting_load_resp_id_r),
    .expecting_store_resp_o(expecting_store_resp_id_r),

    // Interrupt Signals
    .csr_mstatus_mie_i(csr_mstatus_mie),
    .irq_pending_i    (irq_pending_o),
    .irqs_i           (irqs),
    .irq_nm_i         (irq_nm_i),
    .nmi_mode_o       (nmi_mode_r),

    // Debug Signal
    .debug_mode_o         (debug_mode_r),
    .debug_mode_entering_o(debug_mode_entering_r),
    .debug_cause_o        (debug_cause_r),
    .debug_csr_save_o     (debug_csr_save_r),
    .debug_req_i          (debug_req_i),
    .debug_single_step_i  (debug_single_step),
    .debug_ebreakm_i      (debug_ebreakm),
    .debug_ebreaku_i      (debug_ebreaku),
    .trigger_match_i      (trigger_match),

    // write data to commit in the register file
    .result_ex_i(result_ex),
    .csr_rdata_i(csr_rdata),

    .rf_raddr_a_o      (rf_raddr_a_r),
    .rf_rdata_a_i      (rf_rdata_a),
    .rf_raddr_b_o      (rf_raddr_b_r),
    .rf_rdata_b_i      (rf_rdata_b),
    .rf_ren_a_o        (rf_ren_a_r),
    .rf_ren_b_o        (rf_ren_b_r),
    .rf_waddr_id_o     (rf_waddr_id_r),
    .rf_wdata_id_o     (rf_wdata_id_r),
    .rf_we_id_o        (rf_we_id_r),
    .rf_rd_a_wb_match_o(rf_rd_a_wb_match_r),
    .rf_rd_b_wb_match_o(rf_rd_b_wb_match_r),

    .rf_waddr_wb_i    (rf_waddr_wb),
    .rf_wdata_fwd_wb_i(rf_wdata_fwd_wb),
    .rf_write_wb_i    (rf_write_wb),

    .en_wb_o               (en_wb_r),
    .instr_type_wb_o       (instr_type_wb_r),
    .instr_perf_count_id_o (instr_perf_count_id_r),
    .ready_wb_i            (ready_wb),
    .outstanding_load_wb_i (outstanding_load_wb),
    .outstanding_store_wb_i(outstanding_store_wb),

    // Performance Counters
    .perf_jump_o      (perf_jump_r),
    .perf_branch_o    (perf_branch_r),
    .perf_tbranch_o   (perf_tbranch_r),
    .perf_dside_wait_o(perf_dside_wait_r),
    .perf_mul_wait_o  (perf_mul_wait_r),
    .perf_div_wait_o  (perf_div_wait_r),
    .instr_id_done_o  (instr_id_done_r)
  );
  
  // Mux ID stage outputs - First stage: select between primary and redundant
  redundancy_mux #(.WIDTH(1)) ctrl_busy_red_mux (
    .operand_a(ctrl_busy_primary),
    .operand_b(ctrl_busy_r),
    .result(ctrl_busy_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) illegal_insn_id_red_mux (
    .operand_a(illegal_insn_id_primary),
    .operand_b(illegal_insn_id_r),
    .result(illegal_insn_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) instr_first_cycle_id_red_mux (
    .operand_a(instr_first_cycle_id_primary),
    .operand_b(instr_first_cycle_id_r),
    .result(instr_first_cycle_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) instr_valid_clear_red_mux (
    .operand_a(instr_valid_clear_primary),
    .operand_b(instr_valid_clear_r),
    .result(instr_valid_clear_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) id_in_ready_red_mux (
    .operand_a(id_in_ready_primary),
    .operand_b(id_in_ready_r),
    .result(id_in_ready_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) instr_req_int_red_mux (
    .operand_a(instr_req_int_primary),
    .operand_b(instr_req_int_r),
    .result(instr_req_int_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) pc_set_red_mux (
    .operand_a(pc_set_primary),
    .operand_b(pc_set_r),
    .result(pc_set_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH($bits(pc_sel_e))) pc_mux_id_red_mux (
    .operand_a(pc_mux_id_primary),
    .operand_b(pc_mux_id_r),
    .result(pc_mux_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) nt_branch_mispredict_red_mux (
    .operand_a(nt_branch_mispredict_primary),
    .operand_b(nt_branch_mispredict_r),
    .result(nt_branch_mispredict_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(32)) nt_branch_addr_red_mux (
    .operand_a(nt_branch_addr_primary),
    .operand_b(nt_branch_addr_r),
    .result(nt_branch_addr_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH($bits(exc_pc_sel_e))) exc_pc_mux_id_red_mux (
    .operand_a(exc_pc_mux_id_primary),
    .operand_b(exc_pc_mux_id_r),
    .result(exc_pc_mux_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH($bits(exc_cause_t))) exc_cause_red_mux (
    .operand_a(exc_cause_primary),
    .operand_b(exc_cause_r),
    .result(exc_cause_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) icache_inval_red_mux (
    .operand_a(icache_inval_primary),
    .operand_b(icache_inval_r),
    .result(icache_inval_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH($bits(alu_op_e))) alu_operator_ex_red_mux (
    .operand_a(alu_operator_ex_primary),
    .operand_b(alu_operator_ex_r),
    .result(alu_operator_ex_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(32)) alu_operand_a_ex_red_mux (
    .operand_a(alu_operand_a_ex_primary),
    .operand_b(alu_operand_a_ex_r),
    .result(alu_operand_a_ex_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(32)) alu_operand_b_ex_red_mux (
    .operand_a(alu_operand_b_ex_primary),
    .operand_b(alu_operand_b_ex_r),
    .result(alu_operand_b_ex_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(32)) bt_a_operand_red_mux (
    .operand_a(bt_a_operand_primary),
    .operand_b(bt_a_operand_r),
    .result(bt_a_operand_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(32)) bt_b_operand_red_mux (
    .operand_a(bt_b_operand_primary),
    .operand_b(bt_b_operand_r),
    .result(bt_b_operand_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(34)) imd_val_q_ex_0_red_mux (
    .operand_a(imd_val_q_ex_primary[0]),
    .operand_b(imd_val_q_ex_r[0]),
    .result(imd_val_q_ex_mux[0]),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(34)) imd_val_q_ex_1_red_mux (
    .operand_a(imd_val_q_ex_primary[1]),
    .operand_b(imd_val_q_ex_r[1]),
    .result(imd_val_q_ex_mux[1]),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) mult_en_ex_red_mux (
    .operand_a(mult_en_ex_primary),
    .operand_b(mult_en_ex_r),
    .result(mult_en_ex_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) div_en_ex_red_mux (
    .operand_a(div_en_ex_primary),
    .operand_b(div_en_ex_r),
    .result(div_en_ex_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) mult_sel_ex_red_mux (
    .operand_a(mult_sel_ex_primary),
    .operand_b(mult_sel_ex_r),
    .result(mult_sel_ex_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) div_sel_ex_red_mux (
    .operand_a(div_sel_ex_primary),
    .operand_b(div_sel_ex_r),
    .result(div_sel_ex_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH($bits(md_op_e))) multdiv_operator_ex_red_mux (
    .operand_a(multdiv_operator_ex_primary),
    .operand_b(multdiv_operator_ex_r),
    .result(multdiv_operator_ex_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(2)) multdiv_signed_mode_ex_red_mux (
    .operand_a(multdiv_signed_mode_ex_primary),
    .operand_b(multdiv_signed_mode_ex_r),
    .result(multdiv_signed_mode_ex_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(32)) multdiv_operand_a_ex_red_mux (
    .operand_a(multdiv_operand_a_ex_primary),
    .operand_b(multdiv_operand_a_ex_r),
    .result(multdiv_operand_a_ex_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(32)) multdiv_operand_b_ex_red_mux (
    .operand_a(multdiv_operand_b_ex_primary),
    .operand_b(multdiv_operand_b_ex_r),
    .result(multdiv_operand_b_ex_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) multdiv_ready_id_red_mux (
    .operand_a(multdiv_ready_id_primary),
    .operand_b(multdiv_ready_id_r),
    .result(multdiv_ready_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) csr_access_red_mux (
    .operand_a(csr_access_primary),
    .operand_b(csr_access_r),
    .result(csr_access_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH($bits(csr_op_e))) csr_op_red_mux (
    .operand_a(csr_op_primary),
    .operand_b(csr_op_r),
    .result(csr_op_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH($bits(csr_num_e))) csr_addr_red_mux (
    .operand_a(csr_addr_primary),
    .operand_b(csr_addr_r),
    .result(csr_addr_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) csr_op_en_red_mux (
    .operand_a(csr_op_en_primary),
    .operand_b(csr_op_en_r),
    .result(csr_op_en_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) csr_save_if_red_mux (
    .operand_a(csr_save_if_primary),
    .operand_b(csr_save_if_r),
    .result(csr_save_if_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) csr_save_id_red_mux (
    .operand_a(csr_save_id_primary),
    .operand_b(csr_save_id_r),
    .result(csr_save_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) csr_save_wb_red_mux (
    .operand_a(csr_save_wb_primary),
    .operand_b(csr_save_wb_r),
    .result(csr_save_wb_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) csr_restore_mret_id_red_mux (
    .operand_a(csr_restore_mret_id_primary),
    .operand_b(csr_restore_mret_id_r),
    .result(csr_restore_mret_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) csr_restore_dret_id_red_mux (
    .operand_a(csr_restore_dret_id_primary),
    .operand_b(csr_restore_dret_id_r),
    .result(csr_restore_dret_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) csr_save_cause_red_mux (
    .operand_a(csr_save_cause_primary),
    .operand_b(csr_save_cause_r),
    .result(csr_save_cause_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(32)) csr_mtval_red_mux (
    .operand_a(csr_mtval_primary),
    .operand_b(csr_mtval_r),
    .result(csr_mtval_mux),
    .select(redundancy_sel_id)
  );

    redundancy_mux #(.WIDTH(32)) illegal_csr_insn_id_red_mux (
    .operand_a(illegal_csr_insn_id_primary),
    .operand_b(illegal_csr_insn_id_r),
    .result(illegal_csr_insn_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) lsu_req_red_mux (
    .operand_a(lsu_req_primary),
    .operand_b(lsu_req_r),
    .result(lsu_req_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) lsu_we_red_mux (
    .operand_a(lsu_we_primary),
    .operand_b(lsu_we_r),
    .result(lsu_we_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(2)) lsu_type_red_mux (
    .operand_a(lsu_type_primary),
    .operand_b(lsu_type_r),
    .result(lsu_type_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) lsu_sign_ext_red_mux (
    .operand_a(lsu_sign_ext_primary),
    .operand_b(lsu_sign_ext_r),
    .result(lsu_sign_ext_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(32)) lsu_wdata_red_mux (
    .operand_a(lsu_wdata_primary),
    .operand_b(lsu_wdata_r),
    .result(lsu_wdata_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) lsu_req_done_red_mux (
    .operand_a(lsu_req_done_primary),
    .operand_b(lsu_req_done_r),
    .result(lsu_req_done_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) lsu_addr_incr_req_red_mux (
    .operand_a(lsu_addr_incr_req_primary),
    .operand_b(lsu_addr_incr_req_r),
    .result(lsu_addr_incr_req_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(32)) lsu_addr_last_red_mux (
    .operand_a(lsu_addr_last_primary),
    .operand_b(lsu_addr_last_r),
    .result(lsu_addr_last_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) expecting_load_resp_id_red_mux (
    .operand_a(expecting_load_resp_id_primary),
    .operand_b(expecting_load_resp_id_r),
    .result(expecting_load_resp_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) expecting_store_resp_id_red_mux (
    .operand_a(expecting_store_resp_id_primary),
    .operand_b(expecting_store_resp_id_r),
    .result(expecting_store_resp_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) nmi_mode_red_mux (
    .operand_a(nmi_mode_primary),
    .operand_b(nmi_mode_r),
    .result(nmi_mode_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) debug_mode_red_mux (
    .operand_a(debug_mode_primary),
    .operand_b(debug_mode_r),
    .result(debug_mode_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) debug_mode_entering_red_mux (
    .operand_a(debug_mode_entering_primary),
    .operand_b(debug_mode_entering_r),
    .result(debug_mode_entering_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH($bits(dbg_cause_e))) debug_cause_red_mux (
    .operand_a(debug_cause_primary),
    .operand_b(debug_cause_r),
    .result(debug_cause_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) debug_csr_save_red_mux (
    .operand_a(debug_csr_save_primary),
    .operand_b(debug_csr_save_r),
    .result(debug_csr_save_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(5)) rf_raddr_a_red_mux (
    .operand_a(rf_raddr_a_primary),
    .operand_b(rf_raddr_a_r),
    .result(rf_raddr_a_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(5)) rf_raddr_b_red_mux (
    .operand_a(rf_raddr_b_primary),
    .operand_b(rf_raddr_b_r),
    .result(rf_raddr_b_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) rf_ren_a_red_mux (
    .operand_a(rf_ren_a_primary),
    .operand_b(rf_ren_a_r),
    .result(rf_ren_a_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) rf_ren_b_red_mux (
    .operand_a(rf_ren_b_primary),
    .operand_b(rf_ren_b_r),
    .result(rf_ren_b_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(5)) rf_waddr_id_red_mux (
    .operand_a(rf_waddr_id_primary),
    .operand_b(rf_waddr_id_r),
    .result(rf_waddr_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(32)) rf_wdata_id_red_mux (
    .operand_a(rf_wdata_id_primary),
    .operand_b(rf_wdata_id_r),
    .result(rf_wdata_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) rf_we_id_red_mux (
    .operand_a(rf_we_id_primary),
    .operand_b(rf_we_id_r),
    .result(rf_we_id_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) rf_rd_a_wb_match_red_mux (
    .operand_a(rf_rd_a_wb_match_primary),
    .operand_b(rf_rd_a_wb_match_r),
    .result(rf_rd_a_wb_match_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) rf_rd_b_wb_match_red_mux (
    .operand_a(rf_rd_b_wb_match_primary),
    .operand_b(rf_rd_b_wb_match_r),
    .result(rf_rd_b_wb_match_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) en_wb_red_mux (
    .operand_a(en_wb_primary),
    .operand_b(en_wb_r),
    .result(en_wb_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH($bits(wb_instr_type_e))) instr_type_wb_red_mux (
    .operand_a(instr_type_wb_primary),
    .operand_b(instr_type_wb_r),
    .result(instr_type_wb_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) perf_jump_red_mux (
    .operand_a(perf_jump_primary),
    .operand_b(perf_jump_r),
    .result(perf_jump_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) perf_branch_red_mux (
    .operand_a(perf_branch_primary),
    .operand_b(perf_branch_r),
    .result(perf_branch_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) perf_tbranch_red_mux (
    .operand_a(perf_tbranch_primary),
    .operand_b(perf_tbranch_r),
    .result(perf_tbranch_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) perf_dside_wait_red_mux (
    .operand_a(perf_dside_wait_primary),
    .operand_b(perf_dside_wait_r),
    .result(perf_dside_wait_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) perf_mul_wait_red_mux (
    .operand_a(perf_mul_wait_primary),
    .operand_b(perf_mul_wait_r),
    .result(perf_mul_wait_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) perf_div_wait_red_mux (
    .operand_a(perf_div_wait_primary),
    .operand_b(perf_div_wait_r),
    .result(perf_div_wait_mux),
    .select(redundancy_sel_id)
  );

  redundancy_mux #(.WIDTH(1)) instr_id_done_red_mux (
    .operand_a(instr_id_done_primary),
    .operand_b(instr_id_done_r),
    .result(instr_id_done_mux),
    .select(redundancy_sel_id)
  );
   redundancy_mux #(.WIDTH(1)) instr_perf_count_id_red_mux (
    .operand_a(instr_perf_count_id_primary),
    .operand_b(instr_perf_count_id_r),
    .result(instr_perf_count_id_mux),
    .select(redundancy_sel_id)
  );

  // Assign ID stage mux outputs to reg_a
  assign ctrl_busy_reg_a = ctrl_busy_mux;
  assign illegal_insn_id_reg_a = illegal_insn_id_mux;
  assign instr_first_cycle_id_reg_a = instr_first_cycle_id_mux;
  assign instr_valid_clear_reg_a = instr_valid_clear_mux;
  assign id_in_ready_reg_a = id_in_ready_mux;
  assign instr_req_int_reg_a = instr_req_int_mux;
  assign pc_set_reg_a = pc_set_mux;
  assign pc_mux_id_reg_a = pc_mux_id_mux;
  assign nt_branch_mispredict_reg_a = nt_branch_mispredict_mux;
  assign nt_branch_addr_reg_a = nt_branch_addr_mux;
  assign exc_pc_mux_id_reg_a = exc_pc_mux_id_mux;
  assign exc_cause_reg_a = exc_cause_mux;
  assign icache_inval_reg_a = icache_inval_mux;
  assign alu_operator_ex_reg_a = alu_operator_ex_mux;
  assign alu_operand_a_ex_reg_a = alu_operand_a_ex_mux;
  assign alu_operand_b_ex_reg_a = alu_operand_b_ex_mux;
  assign bt_a_operand_reg_a = bt_a_operand_mux;
  assign bt_b_operand_reg_a = bt_b_operand_mux;
  assign imd_val_q_ex_reg_a[0] = imd_val_q_ex_mux[0];
  assign imd_val_q_ex_reg_a[1] = imd_val_q_ex_mux[1];
  assign mult_en_ex_reg_a = mult_en_ex_mux;
  assign div_en_ex_reg_a = div_en_ex_mux;
  assign mult_sel_ex_reg_a = mult_sel_ex_mux;
  assign div_sel_ex_reg_a = div_sel_ex_mux;
  assign multdiv_operator_ex_reg_a = multdiv_operator_ex_mux;
  assign multdiv_signed_mode_ex_reg_a = multdiv_signed_mode_ex_mux;
  assign multdiv_operand_a_ex_reg_a = multdiv_operand_a_ex_mux;
  assign multdiv_operand_b_ex_reg_a = multdiv_operand_b_ex_mux;
  assign multdiv_ready_id_reg_a = multdiv_ready_id_mux;
  assign csr_access_reg_a = csr_access_mux;
  assign csr_op_reg_a = csr_op_mux;
  assign csr_addr_reg_a = csr_addr_mux;
  assign csr_op_en_reg_a = csr_op_en_mux;
  assign csr_save_if_reg_a = csr_save_if_mux;
  assign csr_save_id_reg_a = csr_save_id_mux;
  assign csr_save_wb_reg_a = csr_save_wb_mux;
  assign csr_restore_mret_id_reg_a = csr_restore_mret_id_mux;
  assign csr_restore_dret_id_reg_a = csr_restore_dret_id_mux;
  assign csr_save_cause_reg_a = csr_save_cause_mux;
  assign csr_mtval_reg_a = csr_mtval_mux;
  assign illegal_csr_insn_id_reg_a = illegal_csr_insn_id_mux;
  assign lsu_req_reg_a = lsu_req_mux;
  assign lsu_we_reg_a = lsu_we_mux;
  assign lsu_type_reg_a = lsu_type_mux;
  assign lsu_sign_ext_reg_a = lsu_sign_ext_mux;
  assign lsu_wdata_reg_a = lsu_wdata_mux;
  assign lsu_req_done_reg_a = lsu_req_done_mux;
  assign lsu_addr_incr_req_reg_a = lsu_addr_incr_req_mux;
  assign lsu_addr_last_reg_a = lsu_addr_last_mux;
  assign expecting_load_resp_id_reg_a = expecting_load_resp_id_mux;
  assign expecting_store_resp_id_reg_a = expecting_store_resp_id_mux;
  assign nmi_mode_reg_a = nmi_mode_mux;
  assign debug_mode_reg_a = debug_mode_mux;
  assign debug_mode_entering_reg_a = debug_mode_entering_mux;
  assign debug_cause_reg_a = debug_cause_mux;
  assign debug_csr_save_reg_a = debug_csr_save_mux;
  assign rf_raddr_a_reg_a = rf_raddr_a_mux;
  assign rf_raddr_b_reg_a = rf_raddr_b_mux;
  assign rf_ren_a_reg_a = rf_ren_a_mux;
  assign rf_ren_b_reg_a = rf_ren_b_mux;
  assign rf_waddr_id_reg_a = rf_waddr_id_mux;
  assign rf_wdata_id_reg_a = rf_wdata_id_mux;
  assign rf_we_id_reg_a = rf_we_id_mux;
  assign rf_rd_a_wb_match_reg_a = rf_rd_a_wb_match_mux;
  assign rf_rd_b_wb_match_reg_a = rf_rd_b_wb_match_mux;
  assign en_wb_reg_a = en_wb_mux;
  assign instr_type_wb_reg_a = instr_type_wb_mux;
  assign perf_jump_reg_a = perf_jump_mux;
  assign perf_branch_reg_a = perf_branch_mux;
  assign perf_tbranch_reg_a = perf_tbranch_mux;
  assign perf_dside_wait_reg_a = perf_dside_wait_mux;
  assign perf_mul_wait_reg_a = perf_mul_wait_mux;
  assign perf_div_wait_reg_a = perf_div_wait_mux;
  assign instr_id_done_reg_a = instr_id_done_mux;
  assign instr_perf_count_id_reg_a = instr_perf_count_id_mux;

  // Assign ID stage mux outputs to reg_b
  assign ctrl_busy_reg_b = ctrl_busy_mux;
  assign illegal_insn_id_reg_b = illegal_insn_id_mux;
  assign instr_first_cycle_id_reg_b = instr_first_cycle_id_mux;
  assign instr_valid_clear_reg_b = instr_valid_clear_mux;
  assign id_in_ready_reg_b = id_in_ready_mux;
  assign instr_req_int_reg_b = instr_req_int_mux;
  assign pc_set_reg_b = pc_set_mux;
  assign pc_mux_id_reg_b = pc_mux_id_mux;
  assign nt_branch_mispredict_reg_b = nt_branch_mispredict_mux;
  assign nt_branch_addr_reg_b = nt_branch_addr_mux;
  assign exc_pc_mux_id_reg_b = exc_pc_mux_id_mux;
  assign exc_cause_reg_b = exc_cause_mux;
  assign icache_inval_reg_b = icache_inval_mux;
  assign alu_operator_ex_reg_b = alu_operator_ex_mux;
  assign alu_operand_a_ex_reg_b = alu_operand_a_ex_mux;
  assign alu_operand_b_ex_reg_b = alu_operand_b_ex_mux;
  assign bt_a_operand_reg_b = bt_a_operand_mux;
  assign bt_b_operand_reg_b = bt_b_operand_mux;
  assign imd_val_q_ex_reg_b[0] = imd_val_q_ex_mux[0];
  assign imd_val_q_ex_reg_b[1] = imd_val_q_ex_mux[1];
  assign mult_en_ex_reg_b = mult_en_ex_mux;
  assign div_en_ex_reg_b = div_en_ex_mux;
  assign mult_sel_ex_reg_b = mult_sel_ex_mux;
  assign div_sel_ex_reg_b = div_sel_ex_mux;
  assign multdiv_operator_ex_reg_b = multdiv_operator_ex_mux;
  assign multdiv_signed_mode_ex_reg_b = multdiv_signed_mode_ex_mux;
  assign multdiv_operand_a_ex_reg_b = multdiv_operand_a_ex_mux;
  assign multdiv_operand_b_ex_reg_b = multdiv_operand_b_ex_mux;
  assign multdiv_ready_id_reg_b = multdiv_ready_id_mux;
  assign csr_access_reg_b = csr_access_mux;
  assign csr_op_reg_b = csr_op_mux;
  assign csr_addr_reg_b = csr_addr_mux;
  assign csr_op_en_reg_b = csr_op_en_mux;
  assign csr_save_if_reg_b = csr_save_if_mux;
  assign csr_save_id_reg_b = csr_save_id_mux;
  assign csr_save_wb_reg_b = csr_save_wb_mux;
  assign csr_restore_mret_id_reg_b = csr_restore_mret_id_mux;
  assign csr_restore_dret_id_reg_b = csr_restore_dret_id_mux;
  assign csr_save_cause_reg_b = csr_save_cause_mux;
  assign csr_mtval_reg_b = csr_mtval_mux;
  assign illegal_csr_insn_id_reg_b = illegal_csr_insn_id_mux;
  assign lsu_req_reg_b = lsu_req_mux;
  assign lsu_we_reg_b = lsu_we_mux;
  assign lsu_type_reg_b = lsu_type_mux;
  assign lsu_sign_ext_reg_b = lsu_sign_ext_mux;
  assign lsu_wdata_reg_b = lsu_wdata_mux;
  assign lsu_req_done_reg_b = lsu_req_done_mux;
  assign lsu_addr_incr_req_reg_b = lsu_addr_incr_req_mux;
  assign lsu_addr_last_reg_b = lsu_addr_last_mux;
  assign expecting_load_resp_id_reg_b = expecting_load_resp_id_mux;
  assign expecting_store_resp_id_reg_b = expecting_store_resp_id_mux;
  assign nmi_mode_reg_b = nmi_mode_mux;
  assign debug_mode_reg_b = debug_mode_mux;
  assign debug_mode_entering_reg_b = debug_mode_entering_mux;
  assign debug_cause_reg_b = debug_cause_mux;
  assign debug_csr_save_reg_b = debug_csr_save_mux;
  assign rf_raddr_a_reg_b = rf_raddr_a_mux;
  assign rf_raddr_b_reg_b = rf_raddr_b_mux;
  assign rf_ren_a_reg_b = rf_ren_a_mux;
  assign rf_ren_b_reg_b = rf_ren_b_mux;
  assign rf_waddr_id_reg_b = rf_waddr_id_mux;
  assign rf_wdata_id_reg_b = rf_wdata_id_mux;
  assign rf_we_id_reg_b = rf_we_id_mux;
  assign rf_rd_a_wb_match_reg_b = rf_rd_a_wb_match_mux;
  assign rf_rd_b_wb_match_reg_b = rf_rd_b_wb_match_mux;
  assign en_wb_reg_b = en_wb_mux;
  assign instr_type_wb_reg_b = instr_type_wb_mux;
  assign perf_jump_reg_b = perf_jump_mux;
  assign perf_branch_reg_b = perf_branch_mux;
  assign perf_tbranch_reg_b = perf_tbranch_mux;
  assign perf_dside_wait_reg_b = perf_dside_wait_mux;
  assign perf_mul_wait_reg_b = perf_mul_wait_mux;
  assign perf_div_wait_reg_b = perf_div_wait_mux;
  assign instr_id_done_reg_b = instr_id_done_mux;
  assign instr_perf_count_id_reg_b = instr_perf_count_id_mux;

  // Second layer of muxes: select between reg_a and reg_b
  redundancy_mux #(.WIDTH(1)) ctrl_busy_red_mux_reg (
    .operand_a(ctrl_busy_reg_a),
    .operand_b(ctrl_busy_reg_b),
    .result(ctrl_busy),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) illegal_insn_id_red_mux_reg (
    .operand_a(illegal_insn_id_reg_a),
    .operand_b(illegal_insn_id_reg_b),
    .result(illegal_insn_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) instr_first_cycle_id_red_mux_reg (
    .operand_a(instr_first_cycle_id_reg_a),
    .operand_b(instr_first_cycle_id_reg_b),
    .result(instr_first_cycle_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) instr_valid_clear_red_mux_reg (
    .operand_a(instr_valid_clear_reg_a),
    .operand_b(instr_valid_clear_reg_b),
    .result(instr_valid_clear),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) id_in_ready_red_mux_reg (
    .operand_a(id_in_ready_reg_a),
    .operand_b(id_in_ready_reg_b),
    .result(id_in_ready),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) instr_req_int_red_mux_reg (
    .operand_a(instr_req_int_reg_a),
    .operand_b(instr_req_int_reg_b),
    .result(instr_req_int),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) pc_set_red_mux_reg (
    .operand_a(pc_set_reg_a),
    .operand_b(pc_set_reg_b),
    .result(pc_set),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH($bits(pc_sel_e))) pc_mux_id_red_mux_reg (
    .operand_a(pc_mux_id_reg_a),
    .operand_b(pc_mux_id_reg_b),
    .result(pc_mux_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) nt_branch_mispredict_red_mux_reg (
    .operand_a(nt_branch_mispredict_reg_a),
    .operand_b(nt_branch_mispredict_reg_b),
    .result(nt_branch_mispredict),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(32)) nt_branch_addr_red_mux_reg (
    .operand_a(nt_branch_addr_reg_a),
    .operand_b(nt_branch_addr_reg_b),
    .result(nt_branch_addr),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH($bits(exc_pc_sel_e))) exc_pc_mux_id_red_mux_reg (
    .operand_a(exc_pc_mux_id_reg_a),
    .operand_b(exc_pc_mux_id_reg_b),
    .result(exc_pc_mux_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH($bits(exc_cause_t))) exc_cause_red_mux_reg (
    .operand_a(exc_cause_reg_a),
    .operand_b(exc_cause_reg_b),
    .result(exc_cause),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) icache_inval_red_mux_reg (
    .operand_a(icache_inval_reg_a),
    .operand_b(icache_inval_reg_b),
    .result(icache_inval),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH($bits(alu_op_e))) alu_operator_ex_red_mux_reg (
    .operand_a(alu_operator_ex_reg_a),
    .operand_b(alu_operator_ex_reg_b),
    .result(alu_operator_ex),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(32)) alu_operand_a_ex_red_mux_reg (
    .operand_a(alu_operand_a_ex_reg_a),
    .operand_b(alu_operand_a_ex_reg_b),
    .result(alu_operand_a_ex),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(32)) alu_operand_b_ex_red_mux_reg (
    .operand_a(alu_operand_b_ex_reg_a),
    .operand_b(alu_operand_b_ex_reg_b),
    .result(alu_operand_b_ex),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(32)) bt_a_operand_red_mux_reg (
    .operand_a(bt_a_operand_reg_a),
    .operand_b(bt_a_operand_reg_b),
    .result(bt_a_operand),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(32)) bt_b_operand_red_mux_reg (
    .operand_a(bt_b_operand_reg_a),
    .operand_b(bt_b_operand_reg_b),
    .result(bt_b_operand),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(34)) imd_val_q_ex_0_red_mux_reg (
    .operand_a(imd_val_q_ex_reg_a[0]),
    .operand_b(imd_val_q_ex_reg_b[0]),
    .result(imd_val_q_ex[0]),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(34)) imd_val_q_ex_1_red_mux_reg (
    .operand_a(imd_val_q_ex_reg_a[1]),
    .operand_b(imd_val_q_ex_reg_b[1]),
    .result(imd_val_q_ex[1]),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) mult_en_ex_red_mux_reg (
    .operand_a(mult_en_ex_reg_a),
    .operand_b(mult_en_ex_reg_b),
    .result(mult_en_ex),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) div_en_ex_red_mux_reg (
    .operand_a(div_en_ex_reg_a),
    .operand_b(div_en_ex_reg_b),
    .result(div_en_ex),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) mult_sel_ex_red_mux_reg (
    .operand_a(mult_sel_ex_reg_a),
    .operand_b(mult_sel_ex_reg_b),
    .result(mult_sel_ex),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) div_sel_ex_red_mux_reg (
    .operand_a(div_sel_ex_reg_a),
    .operand_b(div_sel_ex_reg_b),
    .result(div_sel_ex),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH($bits(md_op_e))) multdiv_operator_ex_red_mux_reg (
    .operand_a(multdiv_operator_ex_reg_a),
    .operand_b(multdiv_operator_ex_reg_b),
    .result(multdiv_operator_ex),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(2)) multdiv_signed_mode_ex_red_mux_reg (
    .operand_a(multdiv_signed_mode_ex_reg_a),
    .operand_b(multdiv_signed_mode_ex_reg_b),
    .result(multdiv_signed_mode_ex),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(32)) multdiv_operand_a_ex_red_mux_reg (
    .operand_a(multdiv_operand_a_ex_reg_a),
    .operand_b(multdiv_operand_a_ex_reg_b),
    .result(multdiv_operand_a_ex),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(32)) multdiv_operand_b_ex_red_mux_reg (
    .operand_a(multdiv_operand_b_ex_reg_a),
    .operand_b(multdiv_operand_b_ex_reg_b),
    .result(multdiv_operand_b_ex),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) multdiv_ready_id_red_mux_reg (
    .operand_a(multdiv_ready_id_reg_a),
    .operand_b(multdiv_ready_id_reg_b),
    .result(multdiv_ready_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) csr_access_red_mux_reg (
    .operand_a(csr_access_reg_a),
    .operand_b(csr_access_reg_b),
    .result(csr_access),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH($bits(csr_op_e))) csr_op_red_mux_reg (
    .operand_a(csr_op_reg_a),
    .operand_b(csr_op_reg_b),
    .result(csr_op),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH($bits(csr_num_e))) csr_addr_red_mux_reg (
    .operand_a(csr_addr_reg_a),
    .operand_b(csr_addr_reg_b),
    .result(csr_addr),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) csr_op_en_red_mux_reg (
    .operand_a(csr_op_en_reg_a),
    .operand_b(csr_op_en_reg_b),
    .result(csr_op_en),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) csr_save_if_red_mux_reg (
    .operand_a(csr_save_if_reg_a),
    .operand_b(csr_save_if_reg_b),
    .result(csr_save_if),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) csr_save_id_red_mux_reg (
    .operand_a(csr_save_id_reg_a),
    .operand_b(csr_save_id_reg_b),
    .result(csr_save_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) csr_save_wb_red_mux_reg (
    .operand_a(csr_save_wb_reg_a),
    .operand_b(csr_save_wb_reg_b),
    .result(csr_save_wb),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) csr_restore_mret_id_red_mux_reg (
    .operand_a(csr_restore_mret_id_reg_a),
    .operand_b(csr_restore_mret_id_reg_b),
    .result(csr_restore_mret_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) csr_restore_dret_id_red_mux_reg (
    .operand_a(csr_restore_dret_id_reg_a),
    .operand_b(csr_restore_dret_id_reg_b),
    .result(csr_restore_dret_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) csr_save_cause_red_mux_reg (
    .operand_a(csr_save_cause_reg_a),
    .operand_b(csr_save_cause_reg_b),
    .result(csr_save_cause),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(32)) csr_mtval_red_mux_reg (
    .operand_a(csr_mtval_reg_a),
    .operand_b(csr_mtval_reg_b),
    .result(csr_mtval),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) illegal_csr_insn_id_red_mux_reg (
    .operand_a(illegal_csr_insn_id_reg_a),
    .operand_b(illegal_csr_insn_id_reg_b),
    .result(illegal_csr_insn_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_req_red_mux_reg (
    .operand_a(lsu_req_reg_a),
    .operand_b(lsu_req_reg_b),
    .result(lsu_req),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_we_red_mux_reg (
    .operand_a(lsu_we_reg_a),
    .operand_b(lsu_we_reg_b),
    .result(lsu_we),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(2)) lsu_type_red_mux_reg (
    .operand_a(lsu_type_reg_a),
    .operand_b(lsu_type_reg_b),
    .result(lsu_type),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_sign_ext_red_mux_reg (
    .operand_a(lsu_sign_ext_reg_a),
    .operand_b(lsu_sign_ext_reg_b),
    .result(lsu_sign_ext),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(32)) lsu_wdata_red_mux_reg (
    .operand_a(lsu_wdata_reg_a),
    .operand_b(lsu_wdata_reg_b),
    .result(lsu_wdata),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_req_done_red_mux_reg (
    .operand_a(lsu_req_done_reg_a),
    .operand_b(lsu_req_done_reg_b),
    .result(lsu_req_done),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_addr_incr_req_red_mux_reg (
    .operand_a(lsu_addr_incr_req_reg_a),
    .operand_b(lsu_addr_incr_req_reg_b),
    .result(lsu_addr_incr_req),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(32)) lsu_addr_last_red_mux_reg (
    .operand_a(lsu_addr_last_reg_a),
    .operand_b(lsu_addr_last_reg_b),
    .result(lsu_addr_last),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) expecting_load_resp_id_red_mux_reg (
    .operand_a(expecting_load_resp_id_reg_a),
    .operand_b(expecting_load_resp_id_reg_b),
    .result(expecting_load_resp_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) expecting_store_resp_id_red_mux_reg (
    .operand_a(expecting_store_resp_id_reg_a),
    .operand_b(expecting_store_resp_id_reg_b),
    .result(expecting_store_resp_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) nmi_mode_red_mux_reg (
    .operand_a(nmi_mode_reg_a),
    .operand_b(nmi_mode_reg_b),
    .result(nmi_mode),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) debug_mode_red_mux_reg (
    .operand_a(debug_mode_reg_a),
    .operand_b(debug_mode_reg_b),
    .result(debug_mode),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) debug_mode_entering_red_mux_reg (
    .operand_a(debug_mode_entering_reg_a),
    .operand_b(debug_mode_entering_reg_b),
    .result(debug_mode_entering),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH($bits(dbg_cause_e))) debug_cause_red_mux_reg (
    .operand_a(debug_cause_reg_a),
    .operand_b(debug_cause_reg_b),
    .result(debug_cause),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) debug_csr_save_red_mux_reg (
    .operand_a(debug_csr_save_reg_a),
    .operand_b(debug_csr_save_reg_b),
    .result(debug_csr_save),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(5)) rf_raddr_a_red_mux_reg (
    .operand_a(rf_raddr_a_reg_a),
    .operand_b(rf_raddr_a_reg_b),
    .result(rf_raddr_a),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(5)) rf_raddr_b_red_mux_reg (
    .operand_a(rf_raddr_b_reg_a),
    .operand_b(rf_raddr_b_reg_b),
    .result(rf_raddr_b),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) rf_ren_a_red_mux_reg (
    .operand_a(rf_ren_a_reg_a),
    .operand_b(rf_ren_a_reg_b),
    .result(rf_ren_a),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) rf_ren_b_red_mux_reg (
    .operand_a(rf_ren_b_reg_a),
    .operand_b(rf_ren_b_reg_b),
    .result(rf_ren_b),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(5)) rf_waddr_id_red_mux_reg (
    .operand_a(rf_waddr_id_reg_a),
    .operand_b(rf_waddr_id_reg_b),
    .result(rf_waddr_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(32)) rf_wdata_id_red_mux_reg (
    .operand_a(rf_wdata_id_reg_a),
    .operand_b(rf_wdata_id_reg_b),
    .result(rf_wdata_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) rf_we_id_red_mux_reg (
    .operand_a(rf_we_id_reg_a),
    .operand_b(rf_we_id_reg_b),
    .result(rf_we_id),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) rf_rd_a_wb_match_red_mux_reg (
    .operand_a(rf_rd_a_wb_match_reg_a),
    .operand_b(rf_rd_a_wb_match_reg_b),
    .result(rf_rd_a_wb_match),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) rf_rd_b_wb_match_red_mux_reg (
    .operand_a(rf_rd_b_wb_match_reg_a),
    .operand_b(rf_rd_b_wb_match_reg_b),
    .result(rf_rd_b_wb_match),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) en_wb_red_mux_reg (
    .operand_a(en_wb_reg_a),
    .operand_b(en_wb_reg_b),
    .result(en_wb),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH($bits(wb_instr_type_e))) instr_type_wb_red_mux_reg (
    .operand_a(instr_type_wb_reg_a),
    .operand_b(instr_type_wb_reg_b),
    .result(instr_type_wb),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_jump_red_mux_reg (
    .operand_a(perf_jump_reg_a),
    .operand_b(perf_jump_reg_b),
    .result(perf_jump),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_branch_red_mux_reg (
    .operand_a(perf_branch_reg_a),
    .operand_b(perf_branch_reg_b),
    .result(perf_branch),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_tbranch_red_mux_reg (
    .operand_a(perf_tbranch_reg_a),
    .operand_b(perf_tbranch_reg_b),
    .result(perf_tbranch),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_dside_wait_red_mux_reg (
    .operand_a(perf_dside_wait_reg_a),
    .operand_b(perf_dside_wait_reg_b),
    .result(perf_dside_wait),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_mul_wait_red_mux_reg (
    .operand_a(perf_mul_wait_reg_a),
    .operand_b(perf_mul_wait_reg_b),
    .result(perf_mul_wait),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_div_wait_red_mux_reg (
    .operand_a(perf_div_wait_reg_a),
    .operand_b(perf_div_wait_reg_b),
    .result(perf_div_wait),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) instr_id_done_red_mux_reg (
    .operand_a(instr_id_done_reg_a),
    .operand_b(instr_id_done_reg_b),
    .result(instr_id_done),
    .select(redundancy_sel_id_reg)
  );

  redundancy_mux #(.WIDTH(1)) instr_perf_count_id_red_mux_reg (
    .operand_a(instr_perf_count_id_reg_a),
    .operand_b(instr_perf_count_id_reg_b),
    .result(instr_perf_count_id),
    .select(redundancy_sel_id_reg)
  );

  ibex_ex_block #(
    .RV32M          (RV32M),
    .RV32B          (RV32B),
    .BranchTargetALU(BranchTargetALU)
  ) ex_block_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // ALU signal from ID stage
    .alu_operator_i         (alu_operator_ex),
    .alu_operand_a_i        (alu_operand_a_ex),
    .alu_operand_b_i        (alu_operand_b_ex),
    .alu_instr_first_cycle_i(instr_first_cycle_id),

    // Branch target ALU signal from ID stage
    .bt_a_operand_i(bt_a_operand),
    .bt_b_operand_i(bt_b_operand),

    // Multipler/Divider signal from ID stage
    .multdiv_operator_i   (multdiv_operator_ex),
    .mult_en_i            (mult_en_ex),
    .div_en_i             (div_en_ex),
    .mult_sel_i           (mult_sel_ex),
    .div_sel_i            (div_sel_ex),
    .multdiv_signed_mode_i(multdiv_signed_mode_ex),
    .multdiv_operand_a_i  (multdiv_operand_a_ex),
    .multdiv_operand_b_i  (multdiv_operand_b_ex),
    .multdiv_ready_id_i   (multdiv_ready_id),
    .data_ind_timing_i    (data_ind_timing),

    // Intermediate value register
    .imd_val_we_o(imd_val_we_ex_primary),
    .imd_val_d_o (imd_val_d_ex_primary),
    .imd_val_q_i (imd_val_q_ex_primary),

    // Outputs
    .alu_adder_result_ex_o(alu_adder_result_ex_primary),  // to LSU
    .result_ex_o          (result_ex_primary),  // to ID

    .branch_target_o  (branch_target_ex_primary),  // to IF
    .branch_decision_o(branch_decision_primary),  // to ID

    .ex_valid_o(ex_valid)
  );
  
  ///////////////////////////////////////////////////////////////
  // REDUNDANT EX stage - duplicate for redundancy
  ///////////////////////////////////////////////////////////////
  
  ibex_ex_block #(
    .RV32M          (RV32M),
    .RV32B          (RV32B),
    .BranchTargetALU(BranchTargetALU)
  ) ex_block_i_redundant (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // ALU signal from ID stage
    .alu_operator_i         (alu_operator_ex),
    .alu_operand_a_i        (alu_operand_a_ex),
    .alu_operand_b_i        (alu_operand_b_ex),
    .alu_instr_first_cycle_i(instr_first_cycle_id),

    // Branch target ALU signal from ID stage
    .bt_a_operand_i(bt_a_operand),
    .bt_b_operand_i(bt_b_operand),

    // Multipler/Divider signal from ID stage
    .multdiv_operator_i   (multdiv_operator_ex),
    .mult_en_i            (mult_en_ex),
    .div_en_i             (div_en_ex),
    .mult_sel_i           (mult_sel_ex),
    .div_sel_i            (div_sel_ex),
    .multdiv_signed_mode_i(multdiv_signed_mode_ex),
    .multdiv_operand_a_i  (multdiv_operand_a_ex),
    .multdiv_operand_b_i  (multdiv_operand_b_ex),
    .multdiv_ready_id_i   (multdiv_ready_id),
    .data_ind_timing_i    (data_ind_timing),

    // Intermediate value register
    .imd_val_we_o(imd_val_we_ex_r),
    .imd_val_d_o (imd_val_d_ex_r),
    .imd_val_q_i (imd_val_q_ex),

    // Outputs
    .alu_adder_result_ex_o(alu_adder_result_ex_r),
    .result_ex_o          (result_ex_r),

    .branch_target_o  (branch_target_ex_r),
    .branch_decision_o(branch_decision_r),

    .ex_valid_o(ex_valid_r)
  );
  
  // Mux EX stage outputs - First stage: select between primary and redundant
  redundancy_mux #(.WIDTH(32)) alu_adder_result_ex_red_mux (
    .operand_a(alu_adder_result_ex_primary),
    .operand_b(alu_adder_result_ex_r),
    .result(alu_adder_result_ex_mux),
    .select(redundancy_sel_ex)
  );

  redundancy_mux #(.WIDTH(32)) result_ex_red_mux (
    .operand_a(result_ex_primary),
    .operand_b(result_ex_r),
    .result(result_ex_mux),
    .select(redundancy_sel_ex)
  );

  redundancy_mux #(.WIDTH(32)) branch_target_ex_red_mux (
    .operand_a(branch_target_ex_primary),
    .operand_b(branch_target_ex_r),
    .result(branch_target_ex_mux),
    .select(redundancy_sel_ex)
  );

  redundancy_mux #(.WIDTH(1)) branch_decision_red_mux (
    .operand_a(branch_decision_primary),
    .operand_b(branch_decision_r),
    .result(branch_decision_mux),
    .select(redundancy_sel_ex)
  );

  redundancy_mux #(.WIDTH(34)) imd_val_d_ex_0_red_mux (
    .operand_a(imd_val_d_ex_primary[0]),
    .operand_b(imd_val_d_ex_r[0]),
    .result(imd_val_d_ex_mux[0]),
    .select(redundancy_sel_ex)
  );

  redundancy_mux #(.WIDTH(34)) imd_val_d_ex_1_red_mux (
    .operand_a(imd_val_d_ex_primary[1]),
    .operand_b(imd_val_d_ex_r[1]),
    .result(imd_val_d_ex_mux[1]),
    .select(redundancy_sel_ex)
  );

  redundancy_mux #(.WIDTH(2)) imd_val_we_ex_red_mux (
    .operand_a(imd_val_we_ex_primary),
    .operand_b(imd_val_we_ex_r),
    .result(imd_val_we_ex_mux),
    .select(redundancy_sel_ex)
  );

  redundancy_mux #(.WIDTH(1)) ex_valid_red_mux (
    .operand_a(ex_valid_primary),
    .operand_b(ex_valid_r),
    .result(ex_valid_mux),
    .select(redundancy_sel_ex)
  );

  // Assign EX stage mux outputs to reg_a
  assign alu_adder_result_ex_reg_a = alu_adder_result_ex_mux;
  assign result_ex_reg_a = result_ex_mux;
  assign branch_target_ex_reg_a = branch_target_ex_mux;
  assign branch_decision_reg_a = branch_decision_mux;
  assign imd_val_d_ex_reg_a[0] = imd_val_d_ex_mux[0];
  assign imd_val_d_ex_reg_a[1] = imd_val_d_ex_mux[1];
  assign imd_val_we_ex_reg_a = imd_val_we_ex_mux;
  assign ex_valid_reg_a = ex_valid_mux;

  // Assign EX stage mux outputs to reg_b
  assign alu_adder_result_ex_reg_b = alu_adder_result_ex_mux;
  assign result_ex_reg_b = result_ex_mux;
  assign branch_target_ex_reg_b = branch_target_ex_mux;
  assign branch_decision_reg_b = branch_decision_mux;
  assign imd_val_d_ex_reg_b[0] = imd_val_d_ex_mux[0];
  assign imd_val_d_ex_reg_b[1] = imd_val_d_ex_mux[1];
  assign imd_val_we_ex_reg_b = imd_val_we_ex_mux;
  assign ex_valid_reg_b = ex_valid_mux;

  // Second layer of muxes: select between reg_a and reg_b
  redundancy_mux #(.WIDTH(32)) alu_adder_result_ex_red_mux_reg (
    .operand_a(alu_adder_result_ex_reg_a),
    .operand_b(alu_adder_result_ex_reg_b),
    .result(alu_adder_result_ex),
    .select(redundancy_sel_ex_reg)
  );

  redundancy_mux #(.WIDTH(32)) result_ex_red_mux_reg (
    .operand_a(result_ex_reg_a),
    .operand_b(result_ex_reg_b),
    .result(result_ex),
    .select(redundancy_sel_ex_reg)
  );

  redundancy_mux #(.WIDTH(32)) branch_target_ex_red_mux_reg (
    .operand_a(branch_target_ex_reg_a),
    .operand_b(branch_target_ex_reg_b),
    .result(branch_target_ex),
    .select(redundancy_sel_ex_reg)
  );

  redundancy_mux #(.WIDTH(1)) branch_decision_red_mux_reg (
    .operand_a(branch_decision_reg_a),
    .operand_b(branch_decision_reg_b),
    .result(branch_decision),
    .select(redundancy_sel_ex_reg)
  );

  redundancy_mux #(.WIDTH(34)) imd_val_d_ex_0_red_mux_reg (
    .operand_a(imd_val_d_ex_reg_a[0]),
    .operand_b(imd_val_d_ex_reg_b[0]),
    .result(imd_val_d_ex[0]),
    .select(redundancy_sel_ex_reg)
  );

  redundancy_mux #(.WIDTH(34)) imd_val_d_ex_1_red_mux_reg (
    .operand_a(imd_val_d_ex_reg_a[1]),
    .operand_b(imd_val_d_ex_reg_b[1]),
    .result(imd_val_d_ex[1]),
    .select(redundancy_sel_ex_reg)
  );

  redundancy_mux #(.WIDTH(2)) imd_val_we_ex_red_mux_reg (
    .operand_a(imd_val_we_ex_reg_a),
    .operand_b(imd_val_we_ex_reg_b),
    .result(imd_val_we_ex),
    .select(redundancy_sel_ex_reg)
  );

  redundancy_mux #(.WIDTH(1)) ex_valid_red_mux_reg (
    .operand_a(ex_valid_reg_a),
    .operand_b(ex_valid_reg_b),
    .result(ex_valid),
    .select(redundancy_sel_ex_reg)
  );


  /////////////////////
  // Load/store unit //
  /////////////////////

  assign data_req_o   = data_req_out & ~pmp_req_err[PMP_D];
  assign lsu_resp_err = lsu_load_err | lsu_store_err;

  ibex_load_store_unit #(
    .MemECC(MemECC),
    .MemDataWidth(MemDataWidth)
  ) load_store_unit_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // data interface
    .data_req_o    (data_req_out_primary),
    .data_gnt_i    (data_gnt_i),
    .data_rvalid_i (data_rvalid_i),
    .data_bus_err_i(data_err_i),
    .data_pmp_err_i(pmp_req_err[PMP_D]),

    .data_addr_o      (data_addr_o_primary),
    .data_we_o        (data_we_o_primary),
    .data_be_o        (data_be_o_primary),
    .data_wdata_o     (data_wdata_o_primary),
    .data_rdata_i     (data_rdata_i),

    // signals to/from ID/EX stage
    .lsu_we_i      (lsu_we),
    .lsu_type_i    (lsu_type),
    .lsu_wdata_i   (lsu_wdata),
    .lsu_sign_ext_i(lsu_sign_ext),

    .lsu_rdata_o      (rf_wdata_lsu_primary),
    .lsu_rdata_valid_o(lsu_rdata_valid_primary),
    .lsu_req_i        (lsu_req),
    .lsu_req_done_o   (lsu_req_done_primary),

    .adder_result_ex_i(alu_adder_result_ex),

    .addr_incr_req_o(lsu_addr_incr_req_primary),
    .addr_last_o    (lsu_addr_last_primary),


    .lsu_resp_valid_o(lsu_resp_valid_primary),

    // exception signals
    .load_err_o           (lsu_load_err_raw_primary),
    .load_resp_intg_err_o (lsu_load_resp_intg_err_primary),
    .store_err_o          (lsu_store_err_raw_primary),
    .store_resp_intg_err_o(lsu_store_resp_intg_err_primary),

    .busy_o(lsu_busy_primary),

    .perf_load_o (perf_load_primary),
    .perf_store_o(perf_store_primary)
  );
  
  ///////////////////////////////////////////////////////////////
  // REDUNDANT LSU - duplicate for redundancy
  ///////////////////////////////////////////////////////////////
  
  ibex_load_store_unit #(
    .MemECC(MemECC),
    .MemDataWidth(MemDataWidth)
  ) load_store_unit_i_redundant (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // data interface - share inputs, don't drive outputs
    .data_req_o    (data_req_out_r),
    .data_gnt_i    (data_gnt_i),
    .data_rvalid_i (data_rvalid_i),
    .data_bus_err_i(data_err_i),
    .data_pmp_err_i(pmp_req_err[PMP_D]),

    .data_addr_o      (data_addr_o_r),
    .data_we_o        (data_we_o_r),
    .data_be_o        (data_be_o_r),
    .data_wdata_o     (data_wdata_o_r),
    .data_rdata_i     (data_rdata_i),

    // signals to/from ID/EX stage
    .lsu_we_i      (lsu_we),
    .lsu_type_i    (lsu_type),
    .lsu_wdata_i   (lsu_wdata),
    .lsu_sign_ext_i(lsu_sign_ext),

    .lsu_rdata_o      (rf_wdata_r),
    .lsu_rdata_valid_o(lsu_rdata_valid_r),
    .lsu_req_i        (lsu_req),
    .lsu_req_done_o   (lsu_req_done_r),

    .adder_result_ex_i(alu_adder_result_ex),

    .addr_incr_req_o(lsu_addr_incr_req_r),
    .addr_last_o    (lsu_addr_last_r),

    .lsu_resp_valid_o(lsu_resp_valid_r),

    // exception signals
    .load_err_o           (lsu_load_err_raw_r),
    .load_resp_intg_err_o (lsu_load_resp_intg_err_r),
    .store_err_o          (lsu_store_err_raw_r),
    .store_resp_intg_err_o(lsu_store_resp_intg_err_r),

    .busy_o(lsu_busy_r),

    .perf_load_o (perf_load_r),
    .perf_store_o(perf_store_r)
  );
  
  // Mux LSU outputs - First stage: select between primary and redundant
  redundancy_mux #(.WIDTH(1)) data_req_out_red_mux (
    .operand_a(data_req_out_primary),
    .operand_b(data_req_out_r),
    .result(data_req_out_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(32)) rf_wdata_lsu_red_mux (
    .operand_a(rf_wdata_lsu_primary),
    .operand_b(rf_wdata_lsu_r),
    .result(rf_wdata_lsu_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) lsu_rdata_valid_red_mux (
    .operand_a(lsu_rdata_valid_primary),
    .operand_b(lsu_rdata_valid_r),
    .result(lsu_rdata_valid_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) lsu_req_done_lsu_red_mux (
    .operand_a(lsu_req_done_lsu_primary),
    .operand_b(lsu_req_done_lsu_r),
    .result(lsu_req_done_lsu_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) lsu_addr_incr_req_lsu_red_mux (
    .operand_a(lsu_addr_incr_req_lsu_primary),
    .operand_b(lsu_addr_incr_req_lsu_r),
    .result(lsu_addr_incr_req_lsu_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(32)) lsu_addr_last_lsu_red_mux (
    .operand_a(lsu_addr_last_lsu_primary),
    .operand_b(lsu_addr_last_lsu_r),
    .result(lsu_addr_last_lsu_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) lsu_resp_valid_red_mux (
    .operand_a(lsu_resp_valid_primary),
    .operand_b(lsu_resp_valid_r),
    .result(lsu_resp_valid_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) lsu_load_err_raw_red_mux (
    .operand_a(lsu_load_err_raw_primary),
    .operand_b(lsu_load_err_raw_r),
    .result(lsu_load_err_raw_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) lsu_load_resp_intg_err_red_mux (
    .operand_a(lsu_load_resp_intg_err_primary),
    .operand_b(lsu_load_resp_intg_err_r),
    .result(lsu_load_resp_intg_err_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) lsu_store_err_raw_red_mux (
    .operand_a(lsu_store_err_raw_primary),
    .operand_b(lsu_store_err_raw_r),
    .result(lsu_store_err_raw_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) lsu_store_resp_intg_err_red_mux (
    .operand_a(lsu_store_resp_intg_err_primary),
    .operand_b(lsu_store_resp_intg_err_r),
    .result(lsu_store_resp_intg_err_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) lsu_busy_red_mux (
    .operand_a(lsu_busy_primary),
    .operand_b(lsu_busy_r),
    .result(lsu_busy_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) perf_load_red_mux (
    .operand_a(perf_load_primary),
    .operand_b(perf_load_r),
    .result(perf_load_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) perf_store_red_mux (
    .operand_a(perf_store_primary),
    .operand_b(perf_store_r),
    .result(perf_store_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(32)) data_addr_o_red_mux (
    .operand_a(data_addr_o_primary),
    .operand_b(data_addr_o_r),
    .result(data_addr_o_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(1)) data_we_o_red_mux (
    .operand_a(data_we_o_primary),
    .operand_b(data_we_o_r),
    .result(data_we_o_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(4)) data_be_o_red_mux (
    .operand_a(data_be_o_primary),
    .operand_b(data_be_o_r),
    .result(data_be_o_mux),
    .select(redundancy_sel_lsu)
  );

  redundancy_mux #(.WIDTH(32)) data_wdata_o_red_mux (
    .operand_a(data_wdata_o_primary),
    .operand_b(data_wdata_o_r),
    .result(data_wdata_o_mux),
    .select(redundancy_sel_lsu)
  );

  // Assign LSU mux outputs to reg_a
  assign data_req_out_reg_a = data_req_out_mux;
  assign rf_wdata_lsu_reg_a = rf_wdata_lsu_mux;
  assign lsu_rdata_valid_reg_a = lsu_rdata_valid_mux;
  assign lsu_req_done_lsu_reg_a = lsu_req_done_lsu_mux;
  assign lsu_addr_incr_req_lsu_reg_a = lsu_addr_incr_req_lsu_mux;
  assign lsu_addr_last_lsu_reg_a = lsu_addr_last_lsu_mux;
  assign lsu_resp_valid_reg_a = lsu_resp_valid_mux;
  assign lsu_load_err_raw_reg_a = lsu_load_err_raw_mux;
  assign lsu_load_resp_intg_err_reg_a = lsu_load_resp_intg_err_mux;
  assign lsu_store_err_raw_reg_a = lsu_store_err_raw_mux;
  assign lsu_store_resp_intg_err_reg_a = lsu_store_resp_intg_err_mux;
  assign lsu_busy_reg_a = lsu_busy_mux;
  assign perf_load_reg_a = perf_load_mux;
  assign perf_store_reg_a = perf_store_mux;
  assign data_addr_o_reg_a = data_addr_o_mux;
  assign data_we_o_reg_a = data_we_o_mux;
  assign data_be_o_reg_a = data_be_o_mux;
  assign data_wdata_o_reg_a = data_wdata_o_mux;

  // Assign LSU mux outputs to reg_b
  assign data_req_out_reg_b = data_req_out_mux;
  assign rf_wdata_lsu_reg_b = rf_wdata_lsu_mux;
  assign lsu_rdata_valid_reg_b = lsu_rdata_valid_mux;
  assign lsu_req_done_lsu_reg_b = lsu_req_done_lsu_mux;
  assign lsu_addr_incr_req_lsu_reg_b = lsu_addr_incr_req_lsu_mux;
  assign lsu_addr_last_lsu_reg_b = lsu_addr_last_lsu_mux;
  assign lsu_resp_valid_reg_b = lsu_resp_valid_mux;
  assign lsu_load_err_raw_reg_b = lsu_load_err_raw_mux;
  assign lsu_load_resp_intg_err_reg_b = lsu_load_resp_intg_err_mux;
  assign lsu_store_err_raw_reg_b = lsu_store_err_raw_mux;
  assign lsu_store_resp_intg_err_reg_b = lsu_store_resp_intg_err_mux;
  assign lsu_busy_reg_b = lsu_busy_mux;
  assign perf_load_reg_b = perf_load_mux;
  assign perf_store_reg_b = perf_store_mux;
  assign data_addr_o_reg_b = data_addr_o_mux;
  assign data_we_o_reg_b = data_we_o_mux;
  assign data_be_o_reg_b = data_be_o_mux;
  assign data_wdata_o_reg_b = data_wdata_o_mux;

  // Second layer of muxes: select between reg_a and reg_b
  redundancy_mux #(.WIDTH(1)) data_req_out_red_mux_reg (
    .operand_a(data_req_out_reg_a),
    .operand_b(data_req_out_reg_b),
    .result(data_req_out),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(32)) rf_wdata_lsu_red_mux_reg (
    .operand_a(rf_wdata_lsu_reg_a),
    .operand_b(rf_wdata_lsu_reg_b),
    .result(rf_wdata_lsu),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_rdata_valid_red_mux_reg (
    .operand_a(lsu_rdata_valid_reg_a),
    .operand_b(lsu_rdata_valid_reg_b),
    .result(lsu_rdata_valid),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_req_done_lsu_red_mux_reg (
    .operand_a(lsu_req_done_lsu_reg_a),
    .operand_b(lsu_req_done_lsu_reg_b),
    .result(lsu_req_done),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_addr_incr_req_lsu_red_mux_reg (
    .operand_a(lsu_addr_incr_req_lsu_reg_a),
    .operand_b(lsu_addr_incr_req_lsu_reg_b),
    .result(lsu_addr_incr_req),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(32)) lsu_addr_last_lsu_red_mux_reg (
    .operand_a(lsu_addr_last_lsu_reg_a),
    .operand_b(lsu_addr_last_lsu_reg_b),
    .result(lsu_addr_last),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_resp_valid_red_mux_reg (
    .operand_a(lsu_resp_valid_reg_a),
    .operand_b(lsu_resp_valid_reg_b),
    .result(lsu_resp_valid),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_load_err_raw_red_mux_reg (
    .operand_a(lsu_load_err_raw_reg_a),
    .operand_b(lsu_load_err_raw_reg_b),
    .result(lsu_load_err),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_load_resp_intg_err_red_mux_reg (
    .operand_a(lsu_load_resp_intg_err_reg_a),
    .operand_b(lsu_load_resp_intg_err_reg_b),
    .result(lsu_load_resp_intg_err),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_store_err_raw_red_mux_reg (
    .operand_a(lsu_store_err_raw_reg_a),
    .operand_b(lsu_store_err_raw_reg_b),
    .result(lsu_store_err),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_store_resp_intg_err_red_mux_reg (
    .operand_a(lsu_store_resp_intg_err_reg_a),
    .operand_b(lsu_store_resp_intg_err_reg_b),
    .result(lsu_store_resp_intg_err),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) lsu_busy_red_mux_reg (
    .operand_a(lsu_busy_reg_a),
    .operand_b(lsu_busy_reg_b),
    .result(lsu_busy),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_load_red_mux_reg (
    .operand_a(perf_load_reg_a),
    .operand_b(perf_load_reg_b),
    .result(perf_load),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_store_red_mux_reg (
    .operand_a(perf_store_reg_a),
    .operand_b(perf_store_reg_b),
    .result(perf_store),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(32)) data_addr_o_red_mux_reg (
    .operand_a(data_addr_o_reg_a),
    .operand_b(data_addr_o_reg_b),
    .result(data_addr_o),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(1)) data_we_o_red_mux_reg (
    .operand_a(data_we_o_reg_a),
    .operand_b(data_we_o_reg_b),
    .result(data_we_o),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(4)) data_be_o_red_mux_reg (
    .operand_a(data_be_o_reg_a),
    .operand_b(data_be_o_reg_b),
    .result(data_be_o),
    .select(redundancy_sel_lsu_reg)
  );

  redundancy_mux #(.WIDTH(32)) data_wdata_o_red_mux_reg (
    .operand_a(data_wdata_o_reg_a),
    .operand_b(data_wdata_o_reg_b),
    .result(data_wdata_o),
    .select(redundancy_sel_lsu_reg)
  );

 ///////////////////////////////////////////////////////////////
  // Primary WB stage 
  ///////////////////////////////////////////////////////////////
  
  ibex_wb_stage #(
    .ResetAll         (ResetAll),
    .WritebackStage   (WritebackStage),
    .DummyInstructions(DummyInstructions)
  ) wb_stage_i (
    .clk_i                   (clk_i),
    .rst_ni                  (rst_ni),
    .en_wb_i                 (en_wb),
    .instr_type_wb_i         (instr_type_wb),
    .pc_id_i                 (pc_id),
    .instr_is_compressed_id_i(instr_is_compressed_id),
    .instr_perf_count_id_i   (instr_perf_count_id),

    .ready_wb_o                         (ready_wb_primary),
    .rf_write_wb_o                      (rf_write_wb_primary),
    .outstanding_load_wb_o              (outstanding_load_wb_primary),
    .outstanding_store_wb_o             (outstanding_store_wb_primary),
    .pc_wb_o                            (pc_wb_primary),
    .perf_instr_ret_wb_o                (perf_instr_ret_wb_primary),
    .perf_instr_ret_compressed_wb_o     (perf_instr_ret_compressed_wb_primary),
    .perf_instr_ret_wb_spec_o           (perf_instr_ret_wb_spec_primary),
    .perf_instr_ret_compressed_wb_spec_o(perf_instr_ret_compressed_wb_spec_primary),

    .rf_waddr_id_i(rf_waddr_id),
    .rf_wdata_id_i(rf_wdata_id),
    .rf_we_id_i   (rf_we_id),

    .dummy_instr_id_i(dummy_instr_id),

    .rf_wdata_lsu_i(rf_wdata_lsu),
    .rf_we_lsu_i   (rf_we_lsu),

    .rf_wdata_fwd_wb_o(rf_wdata_fwd_wb_primary),

    .rf_waddr_wb_o(rf_waddr_wb_primary),
    .rf_wdata_wb_o(rf_wdata_wb_primary),
    .rf_we_wb_o   (rf_we_wb_primary),

    .dummy_instr_wb_o(dummy_instr_wb_primary),

    .lsu_resp_valid_i(lsu_resp_valid),
    .lsu_resp_err_i  (lsu_resp_err),

    .instr_done_wb_o(instr_done_wb_primary)
  );
  
  ///////////////////////////////////////////////////////////////
  // REDUNDANT WB stage - duplicate for redundancy
  ///////////////////////////////////////////////////////////////
  
  ibex_wb_stage #(
    .ResetAll         (ResetAll),
    .WritebackStage   (WritebackStage),
    .DummyInstructions(DummyInstructions)
  ) wb_stage_i_redundant (
    .clk_i                   (clk_i),
    .rst_ni                  (rst_ni),
    .en_wb_i                 (en_wb),
    .instr_type_wb_i         (instr_type_wb),
    .pc_id_i                 (pc_id),
    .instr_is_compressed_id_i(instr_is_compressed_id),
    .instr_perf_count_id_i   (instr_perf_count_id),

    .ready_wb_o                         (ready_wb_r),
    .rf_write_wb_o                      (rf_write_wb_r),
    .outstanding_load_wb_o              (outstanding_load_wb_r),
    .outstanding_store_wb_o             (outstanding_store_wb_r),
    .pc_wb_o                            (pc_wb_r),
    .perf_instr_ret_wb_o                (perf_instr_ret_wb_r),
    .perf_instr_ret_compressed_wb_o     (perf_instr_ret_compressed_wb_r),
    .perf_instr_ret_wb_spec_o           (perf_instr_ret_wb_spec_r),
    .perf_instr_ret_compressed_wb_spec_o(perf_instr_ret_compressed_wb_spec_r),

    .rf_waddr_id_i(rf_waddr_id),
    .rf_wdata_id_i(rf_wdata_id),
    .rf_we_id_i   (rf_we_id),

    .dummy_instr_id_i(dummy_instr_id),

    .rf_wdata_lsu_i(rf_wdata_lsu),
    .rf_we_lsu_i   (rf_we_lsu),

    .rf_wdata_fwd_wb_o(rf_wdata_fwd_wb_r),

    .rf_waddr_wb_o(rf_waddr_wb_r),
    .rf_wdata_wb_o(rf_wdata_wb_r),
    .rf_we_wb_o   (rf_we_wb_r),

    .dummy_instr_wb_o(dummy_instr_wb_r),

    .lsu_resp_valid_i(lsu_resp_valid),
    .lsu_resp_err_i  (lsu_resp_err),

    .instr_done_wb_o(instr_done_wb_r)
  );
  
  // Mux WB stage outputs - First stage: select between primary and redundant
  redundancy_mux #(.WIDTH(1)) ready_wb_red_mux (
    .operand_a(ready_wb_primary),
    .operand_b(ready_wb_r),
    .result(ready_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(1)) rf_write_wb_red_mux (
    .operand_a(rf_write_wb_primary),
    .operand_b(rf_write_wb_r),
    .result(rf_write_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(1)) outstanding_load_wb_red_mux (
    .operand_a(outstanding_load_wb_primary),
    .operand_b(outstanding_load_wb_r),
    .result(outstanding_load_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(1)) outstanding_store_wb_red_mux (
    .operand_a(outstanding_store_wb_primary),
    .operand_b(outstanding_store_wb_r),
    .result(outstanding_store_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(32)) pc_wb_red_mux (
    .operand_a(pc_wb_primary),
    .operand_b(pc_wb_r),
    .result(pc_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(1)) perf_instr_ret_wb_red_mux (
    .operand_a(perf_instr_ret_wb_primary),
    .operand_b(perf_instr_ret_wb_r),
    .result(perf_instr_ret_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(1)) perf_instr_ret_compressed_wb_red_mux (
    .operand_a(perf_instr_ret_compressed_wb_primary),
    .operand_b(perf_instr_ret_compressed_wb_r),
    .result(perf_instr_ret_compressed_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(1)) perf_instr_ret_wb_spec_red_mux (
    .operand_a(perf_instr_ret_wb_spec_primary),
    .operand_b(perf_instr_ret_wb_spec_r),
    .result(perf_instr_ret_wb_spec_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(1)) perf_instr_ret_compressed_wb_spec_red_mux (
    .operand_a(perf_instr_ret_compressed_wb_spec_primary),
    .operand_b(perf_instr_ret_compressed_wb_spec_r),
    .result(perf_instr_ret_compressed_wb_spec_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(32)) rf_wdata_fwd_wb_red_mux (
    .operand_a(rf_wdata_fwd_wb_primary),
    .operand_b(rf_wdata_fwd_wb_r),
    .result(rf_wdata_fwd_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(5)) rf_waddr_wb_red_mux (
    .operand_a(rf_waddr_wb_primary),
    .operand_b(rf_waddr_wb_r),
    .result(rf_waddr_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(32)) rf_wdata_wb_red_mux (
    .operand_a(rf_wdata_wb_primary),
    .operand_b(rf_wdata_wb_r),
    .result(rf_wdata_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(1)) rf_we_wb_red_mux (
    .operand_a(rf_we_wb_primary),
    .operand_b(rf_we_wb_r),
    .result(rf_we_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(1)) dummy_instr_wb_red_mux (
    .operand_a(dummy_instr_wb_primary),
    .operand_b(dummy_instr_wb_r),
    .result(dummy_instr_wb_mux),
    .select(redundancy_sel_wb)
  );

  redundancy_mux #(.WIDTH(1)) instr_done_wb_red_mux (
    .operand_a(instr_done_wb_primary),
    .operand_b(instr_done_wb_r),
    .result(instr_done_wb_mux),
    .select(redundancy_sel_wb)
  );

  // Assign WB stage mux outputs to reg_a
  assign ready_wb_reg_a = ready_wb_mux;
  assign rf_write_wb_reg_a = rf_write_wb_mux;
  assign outstanding_load_wb_reg_a = outstanding_load_wb_mux;
  assign outstanding_store_wb_reg_a = outstanding_store_wb_mux;
  assign pc_wb_reg_a = pc_wb_mux;
  assign perf_instr_ret_wb_reg_a = perf_instr_ret_wb_mux;
  assign perf_instr_ret_compressed_wb_reg_a = perf_instr_ret_compressed_wb_mux;
  assign perf_instr_ret_wb_spec_reg_a = perf_instr_ret_wb_spec_mux;
  assign perf_instr_ret_compressed_wb_spec_reg_a = perf_instr_ret_compressed_wb_spec_mux;
  assign rf_wdata_fwd_wb_reg_a = rf_wdata_fwd_wb_mux;
  assign rf_waddr_wb_reg_a = rf_waddr_wb_mux;
  assign rf_wdata_wb_reg_a = rf_wdata_wb_mux;
  assign rf_we_wb_reg_a = rf_we_wb_mux;
  assign dummy_instr_wb_reg_a = dummy_instr_wb_mux;
  assign instr_done_wb_reg_a = instr_done_wb_mux;

  // Assign WB stage mux outputs to reg_b
  assign ready_wb_reg_b = ready_wb_mux;
  assign rf_write_wb_reg_b = rf_write_wb_mux;
  assign outstanding_load_wb_reg_b = outstanding_load_wb_mux;
  assign outstanding_store_wb_reg_b = outstanding_store_wb_mux;
  assign pc_wb_reg_b = pc_wb_mux;
  assign perf_instr_ret_wb_reg_b = perf_instr_ret_wb_mux;
  assign perf_instr_ret_compressed_wb_reg_b = perf_instr_ret_compressed_wb_mux;
  assign perf_instr_ret_wb_spec_reg_b = perf_instr_ret_wb_spec_mux;
  assign perf_instr_ret_compressed_wb_spec_reg_b = perf_instr_ret_compressed_wb_spec_mux;
  assign rf_wdata_fwd_wb_reg_b = rf_wdata_fwd_wb_mux;
  assign rf_waddr_wb_reg_b = rf_waddr_wb_mux;
  assign rf_wdata_wb_reg_b = rf_wdata_wb_mux;
  assign rf_we_wb_reg_b = rf_we_wb_mux;
  assign dummy_instr_wb_reg_b = dummy_instr_wb_mux;
  assign instr_done_wb_reg_b = instr_done_wb_mux;

  // Second layer of muxes: select between reg_a and reg_b
  redundancy_mux #(.WIDTH(1)) ready_wb_red_mux_reg (
    .operand_a(ready_wb_reg_a),
    .operand_b(ready_wb_reg_b),
    .result(ready_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(1)) rf_write_wb_red_mux_reg (
    .operand_a(rf_write_wb_reg_a),
    .operand_b(rf_write_wb_reg_b),
    .result(rf_write_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(1)) outstanding_load_wb_red_mux_reg (
    .operand_a(outstanding_load_wb_reg_a),
    .operand_b(outstanding_load_wb_reg_b),
    .result(outstanding_load_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(1)) outstanding_store_wb_red_mux_reg (
    .operand_a(outstanding_store_wb_reg_a),
    .operand_b(outstanding_store_wb_reg_b),
    .result(outstanding_store_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(32)) pc_wb_red_mux_reg (
    .operand_a(pc_wb_reg_a),
    .operand_b(pc_wb_reg_b),
    .result(pc_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_instr_ret_wb_red_mux_reg (
    .operand_a(perf_instr_ret_wb_reg_a),
    .operand_b(perf_instr_ret_wb_reg_b),
    .result(perf_instr_ret_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_instr_ret_compressed_wb_red_mux_reg (
    .operand_a(perf_instr_ret_compressed_wb_reg_a),
    .operand_b(perf_instr_ret_compressed_wb_reg_b),
    .result(perf_instr_ret_compressed_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_instr_ret_wb_spec_red_mux_reg (
    .operand_a(perf_instr_ret_wb_spec_reg_a),
    .operand_b(perf_instr_ret_wb_spec_reg_b),
    .result(perf_instr_ret_wb_spec),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(1)) perf_instr_ret_compressed_wb_spec_red_mux_reg (
    .operand_a(perf_instr_ret_compressed_wb_spec_reg_a),
    .operand_b(perf_instr_ret_compressed_wb_spec_reg_b),
    .result(perf_instr_ret_compressed_wb_spec),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(32)) rf_wdata_fwd_wb_red_mux_reg (
    .operand_a(rf_wdata_fwd_wb_reg_a),
    .operand_b(rf_wdata_fwd_wb_reg_b),
    .result(rf_wdata_fwd_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(5)) rf_waddr_wb_red_mux_reg (
    .operand_a(rf_waddr_wb_reg_a),
    .operand_b(rf_waddr_wb_reg_b),
    .result(rf_waddr_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(32)) rf_wdata_wb_red_mux_reg (
    .operand_a(rf_wdata_wb_reg_a),
    .operand_b(rf_wdata_wb_reg_b),
    .result(rf_wdata_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(1)) rf_we_wb_red_mux_reg (
    .operand_a(rf_we_wb_reg_a),
    .operand_b(rf_we_wb_reg_b),
    .result(rf_we_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(1)) dummy_instr_wb_red_mux_reg (
    .operand_a(dummy_instr_wb_reg_a),
    .operand_b(dummy_instr_wb_reg_b),
    .result(dummy_instr_wb),
    .select(redundancy_sel_wb_reg)
  );

  redundancy_mux #(.WIDTH(1)) instr_done_wb_red_mux_reg (
    .operand_a(instr_done_wb_reg_a),
    .operand_b(instr_done_wb_reg_b),
    .result(instr_done_wb),
    .select(redundancy_sel_wb_reg)
  );

  if (SecureIbex) begin : g_check_mem_response
    // For secure configurations only process load/store responses if we're expecting them to guard
    // against false responses being injected on to the bus
    assign lsu_load_err  = lsu_load_err_raw  & (outstanding_load_wb  | expecting_load_resp_id);
    assign lsu_store_err = lsu_store_err_raw & (outstanding_store_wb | expecting_store_resp_id);
    assign rf_we_lsu     = lsu_rdata_valid   & (outstanding_load_wb  | expecting_load_resp_id);
  end else begin : g_no_check_mem_response
    // For non-secure configurations trust the bus protocol is being followed and we'll only ever
    // see a response if we have an outstanding request.
    assign lsu_load_err  = lsu_load_err_raw;
    assign lsu_store_err = lsu_store_err_raw;
    assign rf_we_lsu     = lsu_rdata_valid;

    // expected_load_resp_id/expected_store_resp_id signals are only used to guard against false
    // responses so they are unused in non-secure configurations
    logic unused_expecting_load_resp_id;
    logic unused_expecting_store_resp_id;

    assign unused_expecting_load_resp_id  = expecting_load_resp_id;
    assign unused_expecting_store_resp_id = expecting_store_resp_id;
  end

  
  /////////////////////////////
  // Register file interface //
  /////////////////////////////

  assign dummy_instr_id_o = dummy_instr_id;
  assign dummy_instr_wb_o = dummy_instr_wb;
  assign rf_raddr_a_o     = rf_raddr_a;
  assign rf_waddr_wb_o    = rf_waddr_wb;
  assign rf_we_wb_o       = rf_we_wb;
  assign rf_raddr_b_o     = rf_raddr_b;

  if (RegFileECC) begin : gen_regfile_ecc

    // SEC_CM: DATA_REG_SW.INTEGRITY
    logic [1:0] rf_ecc_err_a_primary, rf_ecc_err_b_primary;
    logic [1:0] rf_ecc_err_a_r, rf_ecc_err_b_r;
    logic       rf_ecc_err_a_id_primary, rf_ecc_err_b_id_primary;
    logic       rf_ecc_err_a_id_r, rf_ecc_err_b_id_r;

    // ECC checkbit generation for register file wdata
    prim_secded_inv_39_32_enc regfile_ecc_enc (
      .data_i(rf_wdata_wb),
      .data_o(rf_wdata_wb_ecc_o)
    );

    // ECC checking on primary register file rdata
    prim_secded_inv_39_32_dec regfile_ecc_dec_a_primary (
      .data_i    (rf_rdata_a_ecc_i),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rf_ecc_err_a_primary)
    );
    prim_secded_inv_39_32_dec regfile_ecc_dec_b_primary (
      .data_i    (rf_rdata_b_ecc_i),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rf_ecc_err_b_primary)
    );

    // ECC checking on redundant register file rdata
    prim_secded_inv_39_32_dec regfile_ecc_dec_a_r (
      .data_i    (rf_rdata_a_ecc_i),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rf_ecc_err_a_r)
    );
    prim_secded_inv_39_32_dec regfile_ecc_dec_b_r (
      .data_i    (rf_rdata_b_ecc_i),
      .data_o    (),
      .syndrome_o(),
      .err_o     (rf_ecc_err_b_r)
    );

    // Assign primary read outputs - no error correction, just trigger an alert
    assign rf_rdata_a_primary = rf_rdata_a_ecc_i[31:0];
    assign rf_rdata_b_primary = rf_rdata_b_ecc_i[31:0];

    // Assign redundant read outputs - no error correction, just trigger an alert
    assign rf_rdata_a_r = rf_rdata_a_ecc_i[31:0];
    assign rf_rdata_b_r = rf_rdata_b_ecc_i[31:0];

    // Calculate primary errors - qualify with WB forwarding to avoid xprop into the alert signal
    assign rf_ecc_err_a_id_primary = |rf_ecc_err_a_primary & rf_ren_a & ~(rf_rd_a_wb_match & rf_write_wb);
    assign rf_ecc_err_b_id_primary = |rf_ecc_err_b_primary & rf_ren_b & ~(rf_rd_b_wb_match & rf_write_wb);

    // Calculate redundant errors - qualify with WB forwarding to avoid xprop into the alert signal
    assign rf_ecc_err_a_id_r = |rf_ecc_err_a_r & rf_ren_a & ~(rf_rd_a_wb_match & rf_write_wb);
    assign rf_ecc_err_b_id_r = |rf_ecc_err_b_r & rf_ren_b & ~(rf_rd_b_wb_match & rf_write_wb);

    // Combined primary error
    assign rf_ecc_err_comb_primary = instr_valid_id & (rf_ecc_err_a_id_primary | rf_ecc_err_b_id_primary);

    // Combined redundant error
    assign rf_ecc_err_comb_r = instr_valid_id & (rf_ecc_err_a_id_r | rf_ecc_err_b_id_r);

  end else begin : gen_no_regfile_ecc
    logic unused_rf_ren_a, unused_rf_ren_b;
    logic unused_rf_rd_a_wb_match, unused_rf_rd_b_wb_match;

    assign unused_rf_ren_a         = rf_ren_a;
    assign unused_rf_ren_b         = rf_ren_b;
    assign unused_rf_rd_a_wb_match = rf_rd_a_wb_match;
    assign unused_rf_rd_b_wb_match = rf_rd_b_wb_match;
    assign rf_wdata_wb_ecc_o       = rf_wdata_wb;
    assign rf_rdata_a_primary      = rf_rdata_a_ecc_i;
    assign rf_rdata_b_primary      = rf_rdata_b_ecc_i;
    assign rf_rdata_a_r            = rf_rdata_a_ecc_i;
    assign rf_rdata_b_r            = rf_rdata_b_ecc_i;
    assign rf_ecc_err_comb_primary = 1'b0;
    assign rf_ecc_err_comb_r       = 1'b0;
  end

  // Register File output muxing - First stage: select between primary and redundant
  redundancy_mux #(.WIDTH(32)) rf_rdata_a_red_mux (
    .operand_a(rf_rdata_a_primary),
    .operand_b(rf_rdata_a_r),
    .result(rf_rdata_a_mux),
    .select(redundancy_sel_rf)
  );

  redundancy_mux #(.WIDTH(32)) rf_rdata_b_red_mux (
    .operand_a(rf_rdata_b_primary),
    .operand_b(rf_rdata_b_r),
    .result(rf_rdata_b_mux),
    .select(redundancy_sel_rf)
  );

  redundancy_mux #(.WIDTH(1)) rf_ecc_err_comb_red_mux (
    .operand_a(rf_ecc_err_comb_primary),
    .operand_b(rf_ecc_err_comb_r),
    .result(rf_ecc_err_comb_mux),
    .select(redundancy_sel_rf)
  );

  // Assign RF mux outputs to reg_a
  assign rf_rdata_a_reg_a = rf_rdata_a_mux;
  assign rf_rdata_b_reg_a = rf_rdata_b_mux;
  assign rf_ecc_err_comb_reg_a = rf_ecc_err_comb_mux;

  // Assign RF mux outputs to reg_b
  assign rf_rdata_a_reg_b = rf_rdata_a_mux;
  assign rf_rdata_b_reg_b = rf_rdata_b_mux;
  assign rf_ecc_err_comb_reg_b = rf_ecc_err_comb_mux;

  // Second layer of muxes: select between reg_a and reg_b
  redundancy_mux #(.WIDTH(32)) rf_rdata_a_red_mux_reg (
    .operand_a(rf_rdata_a_reg_a),
    .operand_b(rf_rdata_a_reg_b),
    .result(rf_rdata_a),
    .select(redundancy_sel_rf_reg)
  );

  redundancy_mux #(.WIDTH(32)) rf_rdata_b_red_mux_reg (
    .operand_a(rf_rdata_b_reg_a),
    .operand_b(rf_rdata_b_reg_b),
    .result(rf_rdata_b),
    .select(redundancy_sel_rf_reg)
  );

  redundancy_mux #(.WIDTH(1)) rf_ecc_err_comb_red_mux_reg (
    .operand_a(rf_ecc_err_comb_reg_a),
    .operand_b(rf_ecc_err_comb_reg_b),
    .result(rf_ecc_err_comb),
    .select(redundancy_sel_rf_reg)
  );


  ///////////////////////
  // Crash dump output //
  ///////////////////////

  logic [31:0] crash_dump_mtval;
  assign crash_dump_o.current_pc     = pc_id;
  assign crash_dump_o.next_pc        = pc_if;
  assign crash_dump_o.last_data_addr = lsu_addr_last;
  assign crash_dump_o.exception_pc   = csr_mepc;
  assign crash_dump_o.exception_addr = crash_dump_mtval;

  ///////////////////
  // Alert outputs //
  ///////////////////

  // Minor alert - core is in a recoverable state
  assign alert_minor_o = icache_ecc_error;

  // Major internal alert - core is unrecoverable
  assign alert_major_internal_o = rf_ecc_err_comb | pc_mismatch_alert | csr_shadow_err;
  // Major bus alert
  assign alert_major_bus_o = lsu_load_resp_intg_err | lsu_store_resp_intg_err | instr_intg_err;

  // Explict INC_ASSERT block to avoid unused signal lint warnings were asserts are not included
  `ifdef INC_ASSERT
  // Signals used for assertions only
  logic outstanding_load_resp;
  logic outstanding_store_resp;

  logic outstanding_load_id;
  logic outstanding_store_id;

  assign outstanding_load_id  = id_stage_i.instr_executing & id_stage_i.lsu_req_dec &
                                ~id_stage_i.lsu_we;
  assign outstanding_store_id = id_stage_i.instr_executing & id_stage_i.lsu_req_dec &
                                id_stage_i.lsu_we;

  if (WritebackStage) begin : gen_wb_stage
    // When the writeback stage is present a load/store could be in ID or WB. A Load/store in ID can
    // see a response before it moves to WB when it is unaligned otherwise we should only see
    // a response when load/store is in WB.
    assign outstanding_load_resp  = outstanding_load_wb |
      (outstanding_load_id  & load_store_unit_i.split_misaligned_access);

    assign outstanding_store_resp = outstanding_store_wb |
      (outstanding_store_id & load_store_unit_i.split_misaligned_access);

    // When writing back the result of a load, the load must have made it to writeback
    `ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu |-> outstanding_load_wb, clk_i, !rst_ni)
  end else begin : gen_no_wb_stage
    // Without writeback stage only look into whether load or store is in ID to determine if
    // a response is expected.
    assign outstanding_load_resp  = outstanding_load_id;
    assign outstanding_store_resp = outstanding_store_id;

    `ASSERT(NoMemRFWriteWithoutPendingLoad, rf_we_lsu |-> outstanding_load_id, clk_i, !rst_ni)
  end

  `ASSERT(NoMemResponseWithoutPendingAccess,
    data_rvalid_i |-> outstanding_load_resp | outstanding_store_resp, clk_i, !rst_ni)


  // Keep track of the PC last seen in the ID stage when fetch is disabled
  logic [31:0]   pc_at_fetch_disable;
  ibex_mubi_t    last_fetch_enable;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      pc_at_fetch_disable <= '0;
      last_fetch_enable   <= '0;
    end else begin
      last_fetch_enable <= fetch_enable_i;

      if ((fetch_enable_i != IbexMuBiOn) && (last_fetch_enable == IbexMuBiOn)) begin
        pc_at_fetch_disable <= pc_id;
      end
    end
  end

  // A 1-bit encoding of fetch_enable_i to avoid polluting the NoExecWhenFetchEnableNotOn assertion
  // with notes about SecureIbex and mubi values.
  logic fetch_enable_raw;
  assign fetch_enable_raw = SecureIbex ? (fetch_enable_i == IbexMuBiOn) : fetch_enable_i[0];

  // When fetch is disabled, no instructions should be executed. Once fetch is disabled either the
  // ID/EX stage is not valid or the PC of the ID/EX stage must remain as it was at disable. The
  // ID/EX valid should not ressert once it has been cleared.
  `ASSERT(NoExecWhenFetchEnableNotOn,
          !fetch_enable_raw |=>
          (~instr_valid_id || (pc_id == pc_at_fetch_disable)) && ~$rose(instr_valid_id))

  `endif // INC_ASSERT

  ////////////////////////
  // RF (Register File) //
  ////////////////////////
`ifdef RVFI
`endif


  /////////////////////////////////////////
  // CSRs (Control and Status Registers) //
  /////////////////////////////////////////

  assign csr_wdata  = alu_operand_a_ex;

  ibex_cs_registers #(
    .DbgTriggerEn     (DbgTriggerEn),
    .DbgHwBreakNum    (DbgHwBreakNum),
    .DataIndTiming    (DataIndTiming),
    .DummyInstructions(DummyInstructions),
    .ShadowCSR        (ShadowCSR),
    .ICache           (ICache),
    .MHPMCounterNum   (MHPMCounterNum),
    .MHPMCounterWidth (MHPMCounterWidth),
    .PMPEnable        (PMPEnable),
    .PMPGranularity   (PMPGranularity),
    .PMPNumRegions    (PMPNumRegions),
    .PMPRstCfg        (PMPRstCfg),
    .PMPRstAddr       (PMPRstAddr),
    .PMPRstMsecCfg    (PMPRstMsecCfg),
    .RV32E            (RV32E),
    .RV32M            (RV32M),
    .RV32B            (RV32B),
    .CsrMvendorId     (CsrMvendorId),
    .CsrMimpId        (CsrMimpId)
  ) cs_registers_i (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // Hart ID from outside
    .hart_id_i      (hart_id_i),
    .priv_mode_id_o (priv_mode_id_primary),
    .priv_mode_lsu_o(priv_mode_lsu_primary),

    // mtvec
    .csr_mtvec_o     (csr_mtvec_primary),
    .csr_mtvec_init_i(csr_mtvec_init),
    .boot_addr_i     (boot_addr_i),

    // Interface to CSRs     ( SRAM like                    )
    .csr_access_i(csr_access),
    .csr_addr_i  (csr_addr),
    .csr_wdata_i (csr_wdata),
    .csr_op_i    (csr_op),
    .csr_op_en_i (csr_op_en),
    .csr_rdata_o (csr_rdata_primary),

    // Interrupt related control signals
    .irq_software_i   (irq_software_i),
    .irq_timer_i      (irq_timer_i),
    .irq_external_i   (irq_external_i),
    .irq_fast_i       (irq_fast_i),
    .nmi_mode_i       (nmi_mode),
    .irq_pending_o    (irq_pending_o_primary),
    .irqs_o           (irqs_primary),
    .csr_mstatus_mie_o(csr_mstatus_mie_primary),
    .csr_mstatus_tw_o (csr_mstatus_tw_primary),
    .csr_mepc_o       (csr_mepc_primary),
    .csr_mtval_o      (crash_dump_mtval_primary),

    // PMP
    .csr_pmp_cfg_o    (csr_pmp_cfg_primary),
    .csr_pmp_addr_o   (csr_pmp_addr_primary),
    .csr_pmp_mseccfg_o(csr_pmp_mseccfg_primary),

    // debug
    .csr_depc_o           (csr_depc_primary), 
    .debug_mode_i         (debug_mode),
    .debug_mode_entering_i(debug_mode_entering),
    .debug_cause_i        (debug_cause),
    .debug_csr_save_i     (debug_csr_save),
    .debug_single_step_o  (debug_single_step_primary),
    .debug_ebreakm_o      (debug_ebreakm_primary),
    .debug_ebreaku_o      (debug_ebreaku_primary),
    .trigger_match_o      (trigger_matc_primary),

    .pc_if_i(pc_if),
    .pc_id_i(pc_id),
    .pc_wb_i(pc_wb),

    .data_ind_timing_o    (data_ind_timing_primary),
    .dummy_instr_en_o     (dummy_instr_en_primary),
    .dummy_instr_mask_o   (dummy_instr_mask_primary),
    .dummy_instr_seed_en_o(dummy_instr_seed_en_primary),
    .dummy_instr_seed_o   (dummy_instr_seed_primary),
    .icache_enable_o      (icache_enable_primary),
    .csr_shadow_err_o     (csr_shadow_err_primary),
    .ic_scr_key_valid_i   (ic_scr_key_valid_i),

    .csr_save_if_i     (csr_save_if),
    .csr_save_id_i     (csr_save_id),
    .csr_save_wb_i     (csr_save_wb),
    .csr_restore_mret_i(csr_restore_mret_id),
    .csr_restore_dret_i(csr_restore_dret_id),
    .csr_save_cause_i  (csr_save_cause),
    .csr_mcause_i      (exc_cause),
    .csr_mtval_i       (csr_mtval),
    .illegal_csr_insn_o(illegal_csr_insn_id_primary),

    .double_fault_seen_o,

    // performance counter related signals
    .instr_ret_i                (perf_instr_ret_wb),
    .instr_ret_compressed_i     (perf_instr_ret_compressed_wb),
    .instr_ret_spec_i           (perf_instr_ret_wb_spec),
    .instr_ret_compressed_spec_i(perf_instr_ret_compressed_wb_spec),
    .iside_wait_i               (perf_iside_wait),
    .jump_i                     (perf_jump),
    .branch_i                   (perf_branch),
    .branch_taken_i             (perf_tbranch),
    .mem_load_i                 (perf_load),
    .mem_store_i                (perf_store),
    .dside_wait_i               (perf_dside_wait),
    .mul_wait_i                 (perf_mul_wait),
    .div_wait_i                 (perf_div_wait)
  );

  // Redundant CSR module
  ibex_cs_registers #(
    .DbgTriggerEn     (DbgTriggerEn),
    .DbgHwBreakNum    (DbgHwBreakNum),
    .DataIndTiming    (DataIndTiming),
    .DummyInstructions(DummyInstructions),
    .ShadowCSR        (ShadowCSR),
    .ICache           (ICache),
    .MHPMCounterNum   (MHPMCounterNum),
    .MHPMCounterWidth (MHPMCounterWidth),
    .PMPEnable        (PMPEnable),
    .PMPGranularity   (PMPGranularity),
    .PMPNumRegions    (PMPNumRegions),
    .PMPRstCfg        (PMPRstCfg),
    .PMPRstAddr       (PMPRstAddr),
    .PMPRstMsecCfg    (PMPRstMsecCfg),
    .RV32E            (RV32E),
    .RV32M            (RV32M),
    .RV32B            (RV32B),
    .CsrMvendorId     (CsrMvendorId),
    .CsrMimpId        (CsrMimpId)
  ) cs_registers_i_redundant (
    .clk_i (clk_i),
    .rst_ni(rst_ni),

    // Hart ID from outside
    .hart_id_i      (hart_id_i),
    .priv_mode_id_o (priv_mode_id_r),
    .priv_mode_lsu_o(priv_mode_lsu_r),

    // mtvec
    .csr_mtvec_o     (csr_mtvec_r),
    .csr_mtvec_init_i(csr_mtvec_init),
    .boot_addr_i     (boot_addr_i),

    // Interface to CSRs
    .csr_access_i(csr_access),
    .csr_addr_i  (csr_addr),
    .csr_wdata_i (csr_wdata),
    .csr_op_i    (csr_op),
    .csr_op_en_i (csr_op_en),
    .csr_rdata_o (csr_rdata_r),

    // Interrupt related control signals
    .irq_software_i   (irq_software_i),
    .irq_timer_i      (irq_timer_i),
    .irq_external_i   (irq_external_i),
    .irq_fast_i       (irq_fast_i),
    .nmi_mode_i       (nmi_mode_mux),
    .irq_pending_o    (irq_pending_o_r),
    .irqs_o           (irqs_r),
    .csr_mstatus_mie_o(csr_mstatus_mie_r),
    .csr_mstatus_tw_o (csr_mstatus_tw_r),
    .csr_mepc_o       (csr_mepc_r),
    .csr_mtval_o      (crash_dump_mtval_r),

    // PMP
    .csr_pmp_cfg_o    (csr_pmp_cfg_r),
    .csr_pmp_addr_o   (csr_pmp_addr_r),
    .csr_pmp_mseccfg_o(csr_pmp_mseccfg_r),

    // debug
    .csr_depc_o           (csr_depc_r),
    .debug_mode_i         (debug_mode),
    .debug_mode_entering_i(debug_mode_entering),
    .debug_cause_i        (debug_cause),
    .debug_csr_save_i     (debug_csr_save),
    .debug_single_step_o  (debug_single_step_r),
    .debug_ebreakm_o      (debug_ebreakm_r),
    .debug_ebreaku_o      (debug_ebreaku_r),
    .trigger_match_o      (trigger_match_r),

    .pc_if_i(pc_if),
    .pc_id_i(pc_id),
    .pc_wb_i(pc_wb),

    .data_ind_timing_o    (data_ind_timing_r),
    .dummy_instr_en_o     (dummy_instr_en_r),
    .dummy_instr_mask_o   (dummy_instr_mask_r),
    .dummy_instr_seed_en_o(dummy_instr_seed_en_r),
    .dummy_instr_seed_o   (dummy_instr_seed_r),
    .icache_enable_o      (icache_enable_r),
    .csr_shadow_err_o     (csr_shadow_err_r),
    .ic_scr_key_valid_i   (ic_scr_key_valid_r_i),

    .csr_save_if_i     (csr_save_if),
    .csr_save_id_i     (csr_save_id),
    .csr_save_wb_i     (csr_save_wb),
    .csr_restore_mret_i(csr_restore_mret_id),
    .csr_restore_dret_i(csr_restore_dret_id),
    .csr_save_cause_i  (csr_save_cause),
    .csr_mcause_i      (exc_cause),
    .csr_mtval_i       (csr_mtval),
    .illegal_csr_insn_o(illegal_csr_insn_id_r),

    .double_fault_seen_o(double_fault_seen_r),

    // performance counter related signals
    .instr_ret_i                (perf_instr_ret_wb),
    .instr_ret_compressed_i     (perf_instr_ret_compressed_wb),
    .instr_ret_spec_i           (perf_instr_ret_wb_spec),
    .instr_ret_compressed_spec_i(perf_instr_ret_compressed_wb_spec),
    .iside_wait_i               (perf_iside_wait),
    .jump_i                     (perf_jump),
    .branch_i                   (perf_branch),
    .branch_taken_i             (perf_tbranch),
    .mem_load_i                 (perf_load),
    .mem_store_i                (perf_store),
    .dside_wait_i               (perf_dside_wait),
    .mul_wait_i                 (perf_mul_wait),
    .div_wait_i                 (perf_div_wait)
  );

  // CSR output muxing - First stage: select between primary and redundant
  redundancy_mux #(.WIDTH(32)) csr_rdata_red_mux (
    .operand_a(csr_rdata_primary),
    .operand_b(csr_rdata_r),
    .result(csr_rdata_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(32)) csr_mepc_red_mux (
    .operand_a(csr_mepc_primary),
    .operand_b(csr_mepc_r),
    .result(csr_mepc_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(32)) csr_depc_red_mux (
    .operand_a(csr_depc_primary),
    .operand_b(csr_depc_r),
    .result(csr_depc_mux),
    .select(redundancy_sel_csr)
  );

  // PMP address array muxes
  genvar pmp_i;
  generate
    for (pmp_i = 0; pmp_i < PMPNumRegions; pmp_i++) begin : g_csr_pmp_addr_mux
      redundancy_mux #(.WIDTH(34)) csr_pmp_addr_red_mux (
        .operand_a(csr_pmp_addr_primary[pmp_i]),
        .operand_b(csr_pmp_addr_r[pmp_i]),
        .result(csr_pmp_addr_mux[pmp_i]),
        .select(redundancy_sel_csr)
      );
    end
  endgenerate

  // PMP config array muxes
  generate
    for (pmp_i = 0; pmp_i < PMPNumRegions; pmp_i++) begin : g_csr_pmp_cfg_mux
      redundancy_mux #(.WIDTH($bits(pmp_cfg_t))) csr_pmp_cfg_red_mux (
        .operand_a(csr_pmp_cfg_primary[pmp_i]),
        .operand_b(csr_pmp_cfg_r[pmp_i]),
        .result(csr_pmp_cfg_mux[pmp_i]),
        .select(redundancy_sel_csr)
      );
    end
  endgenerate

  redundancy_mux #(.WIDTH($bits(pmp_mseccfg_t))) csr_pmp_mseccfg_red_mux (
    .operand_a(csr_pmp_mseccfg_primary),
    .operand_b(csr_pmp_mseccfg_r),
    .result(csr_pmp_mseccfg_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(32)) csr_mtvec_red_mux (
    .operand_a(csr_mtvec_primary),
    .operand_b(csr_mtvec_r),
    .result(csr_mtvec_mux_csr),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) csr_mstatus_mie_red_mux (
    .operand_a(csr_mstatus_mie_primary),
    .operand_b(csr_mstatus_mie_r),
    .result(csr_mstatus_mie_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) csr_mstatus_tw_red_mux (
    .operand_a(csr_mstatus_tw_primary),
    .operand_b(csr_mstatus_tw_r),
    .result(csr_mstatus_tw_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH($bits(priv_lvl_e))) priv_mode_id_red_mux (
    .operand_a(priv_mode_id_primary),
    .operand_b(priv_mode_id_r),
    .result(priv_mode_id_mux_csr),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH($bits(priv_lvl_e))) priv_mode_lsu_red_mux (
    .operand_a(priv_mode_lsu_primary),
    .operand_b(priv_mode_lsu_r),
    .result(priv_mode_lsu_mux_csr),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) debug_single_step_red_mux (
    .operand_a(debug_single_step_primary),
    .operand_b(debug_single_step_r),
    .result(debug_single_step_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) debug_ebreakm_red_mux (
    .operand_a(debug_ebreakm_primary),
    .operand_b(debug_ebreakm_r),
    .result(debug_ebreakm_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) debug_ebreaku_red_mux (
    .operand_a(debug_ebreaku_primary),
    .operand_b(debug_ebreaku_r),
    .result(debug_ebreaku_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) trigger_match_red_mux (
    .operand_a(trigger_match_primary),
    .operand_b(trigger_match_r),
    .result(trigger_match_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) csr_shadow_err_red_mux (
    .operand_a(csr_shadow_err_primary),
    .operand_b(csr_shadow_err_r),
    .result(csr_shadow_err_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) data_ind_timing_red_mux (
    .operand_a(data_ind_timing_primary),
    .operand_b(data_ind_timing_r),
    .result(data_ind_timing_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) dummy_instr_en_red_mux (
    .operand_a(dummy_instr_en_primary),
    .operand_b(dummy_instr_en_r),
    .result(dummy_instr_en_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(3)) dummy_instr_mask_red_mux (
    .operand_a(dummy_instr_mask_primary),
    .operand_b(dummy_instr_mask_r),
    .result(dummy_instr_mask_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) dummy_instr_seed_en_red_mux (
    .operand_a(dummy_instr_seed_en_primary),
    .operand_b(dummy_instr_seed_en_r),
    .result(dummy_instr_seed_en_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(32)) dummy_instr_seed_red_mux (
    .operand_a(dummy_instr_seed_primary),
    .operand_b(dummy_instr_seed_r),
    .result(dummy_instr_seed_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) icache_enable_red_mux (
    .operand_a(icache_enable_primary),
    .operand_b(icache_enable_r),
    .result(icache_enable_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) irq_pending_o_red_mux (
    .operand_a(irq_pending_o_primary),
    .operand_b(irq_pending_o_r),
    .result(irq_pending_o_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(1)) irqs_red_mux (
    .operand_a(irqs_primary),
    .operand_b(irqs_r),
    .result(irqs_mux),
    .select(redundancy_sel_csr)
  );

  redundancy_mux #(.WIDTH(32)) crash_dump_mtval_red_mux (
    .operand_a(crash_dump_mtval_primary),
    .operand_b(crash_dump_mtval_r),
    .result(crash_dump_mtval_mux),
    .select(redundancy_sel_csr)
  );

  // Assign CSR mux outputs to reg_a
  assign csr_rdata_reg_a = csr_rdata_mux;
  assign csr_mepc_reg_a = csr_mepc_mux;
  assign csr_depc_reg_a = csr_depc_mux;
  assign csr_pmp_mseccfg_reg_a = csr_pmp_mseccfg_mux;
  assign csr_mtvec_reg_a_csr = csr_mtvec_mux_csr;
  assign csr_mstatus_mie_reg_a = csr_mstatus_mie_mux;
  assign csr_mstatus_tw_reg_a = csr_mstatus_tw_mux;
  assign priv_mode_id_reg_a_csr = priv_mode_id_mux_csr;
  assign priv_mode_lsu_reg_a_csr = priv_mode_lsu_mux_csr;
  assign debug_single_step_reg_a = debug_single_step_mux;
  assign debug_ebreakm_reg_a = debug_ebreakm_mux;
  assign debug_ebreaku_reg_a = debug_ebreaku_mux;
  assign trigger_match_reg_a = trigger_match_mux;
  assign csr_shadow_err_reg_a = csr_shadow_err_mux;
  assign data_ind_timing_reg_a = data_ind_timing_mux;
  assign dummy_instr_en_reg_a = dummy_instr_en_mux;
  assign dummy_instr_mask_reg_a = dummy_instr_mask_mux;
  assign dummy_instr_seed_en_reg_a = dummy_instr_seed_en_mux;
  assign dummy_instr_seed_reg_a = dummy_instr_seed_mux;
  assign icache_enable_reg_a = icache_enable_mux;
  assign irq_pending_o_reg_a = irq_pending_o_mux;
  assign irqs_reg_a = irqs_mux;
  assign crash_dump_mtval_reg_a = crash_dump_mtval_mux;

  generate
    for (pmp_i = 0; pmp_i < PMPNumRegions; pmp_i++) begin : g_csr_pmp_addr_reg_a
      assign csr_pmp_addr_reg_a[pmp_i] = csr_pmp_addr_mux[pmp_i];
      assign csr_pmp_cfg_reg_a[pmp_i] = csr_pmp_cfg_mux[pmp_i];
    end
  endgenerate

  // Assign CSR mux outputs to reg_b
  assign csr_rdata_reg_b = csr_rdata_mux;
  assign csr_mepc_reg_b = csr_mepc_mux;
  assign csr_depc_reg_b = csr_depc_mux;
  assign csr_pmp_mseccfg_reg_b = csr_pmp_mseccfg_mux;
  assign csr_mtvec_reg_b_csr = csr_mtvec_mux_csr;
  assign csr_mstatus_mie_reg_b = csr_mstatus_mie_mux;
  assign csr_mstatus_tw_reg_b = csr_mstatus_tw_mux;
  assign priv_mode_id_reg_b_csr = priv_mode_id_mux_csr;
  assign priv_mode_lsu_reg_b_csr = priv_mode_lsu_mux_csr;
  assign debug_single_step_reg_b = debug_single_step_mux;
  assign debug_ebreakm_reg_b = debug_ebreakm_mux;
  assign debug_ebreaku_reg_b = debug_ebreaku_mux;
  assign trigger_match_reg_b = trigger_match_mux;
  assign csr_shadow_err_reg_b = csr_shadow_err_mux;
  assign data_ind_timing_reg_b = data_ind_timing_mux;
  assign dummy_instr_en_reg_b = dummy_instr_en_mux;
  assign dummy_instr_mask_reg_b = dummy_instr_mask_mux;
  assign dummy_instr_seed_en_reg_b = dummy_instr_seed_en_mux;
  assign dummy_instr_seed_reg_b = dummy_instr_seed_mux;
  assign icache_enable_reg_b = icache_enable_mux;
  assign irq_pending_o_reg_b = irq_pending_o_mux;
  assign irqs_reg_b = irqs_mux;
  assign crash_dump_mtval_reg_b = crash_dump_mtval_mux;

  generate
    for (pmp_i = 0; pmp_i < PMPNumRegions; pmp_i++) begin : g_csr_pmp_addr_reg_b
      assign csr_pmp_addr_reg_b[pmp_i] = csr_pmp_addr_mux[pmp_i];
      assign csr_pmp_cfg_reg_b[pmp_i] = csr_pmp_cfg_mux[pmp_i];
    end
  endgenerate

  // Second layer of muxes: select between reg_a and reg_b
  redundancy_mux #(.WIDTH(32)) csr_rdata_red_mux_reg (
    .operand_a(csr_rdata_reg_a),
    .operand_b(csr_rdata_reg_b),
    .result(csr_rdata),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(32)) csr_mepc_red_mux_reg (
    .operand_a(csr_mepc_reg_a),
    .operand_b(csr_mepc_reg_b),
    .result(csr_mepc),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(32)) csr_depc_red_mux_reg (
    .operand_a(csr_depc_reg_a),
    .operand_b(csr_depc_reg_b),
    .result(csr_depc),
    .select(redundancy_sel_csr_reg)
  );

  // PMP address array muxes (second layer)
  generate
    for (pmp_i = 0; pmp_i < PMPNumRegions; pmp_i++) begin : g_csr_pmp_addr_mux_reg
      redundancy_mux #(.WIDTH(34)) csr_pmp_addr_red_mux_reg (
        .operand_a(csr_pmp_addr_reg_a[pmp_i]),
        .operand_b(csr_pmp_addr_reg_b[pmp_i]),
        .result(csr_pmp_addr[pmp_i]),
        .select(redundancy_sel_csr_reg)
      );
    end
  endgenerate

  // PMP config array muxes (second layer)
  generate
    for (pmp_i = 0; pmp_i < PMPNumRegions; pmp_i++) begin : g_csr_pmp_cfg_mux_reg
      redundancy_mux #(.WIDTH($bits(pmp_cfg_t))) csr_pmp_cfg_red_mux_reg (
        .operand_a(csr_pmp_cfg_reg_a[pmp_i]),
        .operand_b(csr_pmp_cfg_reg_b[pmp_i]),
        .result(csr_pmp_cfg[pmp_i]),
        .select(redundancy_sel_csr_reg)
      );
    end
  endgenerate

  redundancy_mux #(.WIDTH($bits(pmp_mseccfg_t))) csr_pmp_mseccfg_red_mux_reg (
    .operand_a(csr_pmp_mseccfg_reg_a),
    .operand_b(csr_pmp_mseccfg_reg_b),
    .result(csr_pmp_mseccfg),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(32)) csr_mtvec_red_mux_reg (
    .operand_a(csr_mtvec_reg_a_csr),
    .operand_b(csr_mtvec_reg_b_csr),
    .result(csr_mtvec),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) csr_mstatus_mie_red_mux_reg (
    .operand_a(csr_mstatus_mie_reg_a),
    .operand_b(csr_mstatus_mie_reg_b),
    .result(csr_mstatus_mie),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) csr_mstatus_tw_red_mux_reg (
    .operand_a(csr_mstatus_tw_reg_a),
    .operand_b(csr_mstatus_tw_reg_b),
    .result(csr_mstatus_tw),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH($bits(priv_lvl_e))) priv_mode_id_red_mux_reg (
    .operand_a(priv_mode_id_reg_a_csr),
    .operand_b(priv_mode_id_reg_b_csr),
    .result(priv_mode_id),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH($bits(priv_lvl_e))) priv_mode_lsu_red_mux_reg (
    .operand_a(priv_mode_lsu_reg_a_csr),
    .operand_b(priv_mode_lsu_reg_b_csr),
    .result(priv_mode_lsu),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) debug_single_step_red_mux_reg (
    .operand_a(debug_single_step_reg_a),
    .operand_b(debug_single_step_reg_b),
    .result(debug_single_step),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) debug_ebreakm_red_mux_reg (
    .operand_a(debug_ebreakm_reg_a),
    .operand_b(debug_ebreakm_reg_b),
    .result(debug_ebreakm),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) debug_ebreaku_red_mux_reg (
    .operand_a(debug_ebreaku_reg_a),
    .operand_b(debug_ebreaku_reg_b),
    .result(debug_ebreaku),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) trigger_match_red_mux_reg (
    .operand_a(trigger_match_reg_a),
    .operand_b(trigger_match_reg_b),
    .result(trigger_match),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) csr_shadow_err_red_mux_reg (
    .operand_a(csr_shadow_err_reg_a),
    .operand_b(csr_shadow_err_reg_b),
    .result(csr_shadow_err),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) data_ind_timing_red_mux_reg (
    .operand_a(data_ind_timing_reg_a),
    .operand_b(data_ind_timing_reg_b),
    .result(data_ind_timing),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) dummy_instr_en_red_mux_reg (
    .operand_a(dummy_instr_en_reg_a),
    .operand_b(dummy_instr_en_reg_b),
    .result(dummy_instr_en),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(3)) dummy_instr_mask_red_mux_reg (
    .operand_a(dummy_instr_mask_reg_a),
    .operand_b(dummy_instr_mask_reg_b),
    .result(dummy_instr_mask),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) dummy_instr_seed_en_red_mux_reg (
    .operand_a(dummy_instr_seed_en_reg_a),
    .operand_b(dummy_instr_seed_en_reg_b),
    .result(dummy_instr_seed_en),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(32)) dummy_instr_seed_red_mux_reg (
    .operand_a(dummy_instr_seed_reg_a),
    .operand_b(dummy_instr_seed_reg_b),
    .result(dummy_instr_seed),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) icache_enable_red_mux_reg (
    .operand_a(icache_enable_reg_a),
    .operand_b(icache_enable_reg_b),
    .result(icache_enable),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) irq_pending_o_red_mux_reg (
    .operand_a(irq_pending_o_reg_a),
    .operand_b(irq_pending_o_reg_b),
    .result(irq_pending_o),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(1)) irqs_red_mux_reg (
    .operand_a(irqs_reg_a),
    .operand_b(irqs_reg_b),
    .result(irqs),
    .select(redundancy_sel_csr_reg)
  );

  redundancy_mux #(.WIDTH(32)) crash_dump_mtval_red_mux_reg (
    .operand_a(crash_dump_mtval_reg_a),
    .operand_b(crash_dump_mtval_reg_b),
    .result(crash_dump_mtval),
    .select(redundancy_sel_csr_reg)
  );

  // These assertions are in top-level as instr_valid_id required as the enable term
  `ASSERT(IbexCsrOpValid, instr_valid_id |-> csr_op inside {
      CSR_OP_READ,
      CSR_OP_WRITE,
      CSR_OP_SET,
      CSR_OP_CLEAR
      })
  `ASSERT_KNOWN_IF(IbexCsrWdataIntKnown, cs_registers_i.csr_wdata_int, csr_op_en)

  if (PMPEnable) begin : g_pmp
    logic [31:0] pc_if_inc;
    logic [33:0] pmp_req_addr [PMPNumChan];
    pmp_req_e    pmp_req_type [PMPNumChan];
    priv_lvl_e   pmp_priv_lvl [PMPNumChan];

    assign pc_if_inc            = pc_if + 32'd2;
    assign pmp_req_addr[PMP_I]  = {2'b00, pc_if};
    assign pmp_req_type[PMP_I]  = PMP_ACC_EXEC;
    assign pmp_priv_lvl[PMP_I]  = priv_mode_id;
    assign pmp_req_addr[PMP_I2] = {2'b00, pc_if_inc};
    assign pmp_req_type[PMP_I2] = PMP_ACC_EXEC;
    assign pmp_priv_lvl[PMP_I2] = priv_mode_id;
    assign pmp_req_addr[PMP_D]  = {2'b00, data_addr_o[31:0]};
    assign pmp_req_type[PMP_D]  = data_we_o ? PMP_ACC_WRITE : PMP_ACC_READ;
    assign pmp_priv_lvl[PMP_D]  = priv_mode_lsu;

    ibex_pmp #(
      .DmBaseAddr    (DmBaseAddr),
      .DmAddrMask    (DmAddrMask),
      .PMPGranularity(PMPGranularity),
      .PMPNumChan    (PMPNumChan),
      .PMPNumRegions (PMPNumRegions)
    ) pmp_i (
      // Interface to CSRs
      .csr_pmp_cfg_i    (csr_pmp_cfg),
      .csr_pmp_addr_i   (csr_pmp_addr),
      .csr_pmp_mseccfg_i(csr_pmp_mseccfg),
      .debug_mode_i     (debug_mode),
      .priv_mode_i      (pmp_priv_lvl),
      // Access checking channels
      .pmp_req_addr_i   (pmp_req_addr),
      .pmp_req_type_i   (pmp_req_type),
      .pmp_req_err_o    (pmp_req_err)
    );
  end else begin : g_no_pmp
    // Unused signal tieoff
    priv_lvl_e unused_priv_lvl_ls;
    logic [33:0] unused_csr_pmp_addr [PMPNumRegions];
    pmp_cfg_t    unused_csr_pmp_cfg  [PMPNumRegions];
    pmp_mseccfg_t unused_csr_pmp_mseccfg;
    assign unused_priv_lvl_ls = priv_mode_lsu;
    assign unused_csr_pmp_addr = csr_pmp_addr;
    assign unused_csr_pmp_cfg = csr_pmp_cfg;
    assign unused_csr_pmp_mseccfg = csr_pmp_mseccfg;

    // Output tieoff
    assign pmp_req_err[PMP_I]  = 1'b0;
    assign pmp_req_err[PMP_I2] = 1'b0;
    assign pmp_req_err[PMP_D]  = 1'b0;
  end

`ifdef RVFI
  // When writeback stage is present RVFI information is emitted when instruction is finished in
  // third stage but some information must be captured whilst the instruction is in the second
  // stage. Without writeback stage RVFI information is all emitted when instruction retires in
  // second stage. RVFI outputs are all straight from flops. So 2 stage pipeline requires a single
  // set of flops (instr_info => RVFI_out), 3 stage pipeline requires two sets (instr_info => wb
  // => RVFI_out)
  localparam int RVFI_STAGES = WritebackStage ? 2 : 1;

  logic        rvfi_stage_valid     [RVFI_STAGES];
  logic [63:0] rvfi_stage_order     [RVFI_STAGES];
  logic [31:0] rvfi_stage_insn      [RVFI_STAGES];
  logic        rvfi_stage_trap      [RVFI_STAGES];
  logic        rvfi_stage_halt      [RVFI_STAGES];
  logic        rvfi_stage_intr      [RVFI_STAGES];
  logic [ 1:0] rvfi_stage_mode      [RVFI_STAGES];
  logic [ 1:0] rvfi_stage_ixl       [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs1_addr  [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs2_addr  [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rs3_addr  [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs1_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs2_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_rs3_rdata [RVFI_STAGES];
  logic [ 4:0] rvfi_stage_rd_addr   [RVFI_STAGES];
  logic [31:0] rvfi_stage_rd_wdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_pc_rdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_pc_wdata  [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_addr  [RVFI_STAGES];
  logic [ 3:0] rvfi_stage_mem_rmask [RVFI_STAGES];
  logic [ 3:0] rvfi_stage_mem_wmask [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_rdata [RVFI_STAGES];
  logic [31:0] rvfi_stage_mem_wdata [RVFI_STAGES];

  logic        rvfi_instr_new_wb;
  logic        rvfi_intr_d;
  logic        rvfi_intr_q;
  logic        rvfi_set_trap_pc_d;
  logic        rvfi_set_trap_pc_q;
  logic [31:0] rvfi_insn_id;
  logic [4:0]  rvfi_rs1_addr_d;
  logic [4:0]  rvfi_rs1_addr_q;
  logic [4:0]  rvfi_rs2_addr_d;
  logic [4:0]  rvfi_rs2_addr_q;
  logic [4:0]  rvfi_rs3_addr_d;
  logic [31:0] rvfi_rs1_data_d;
  logic [31:0] rvfi_rs1_data_q;
  logic [31:0] rvfi_rs2_data_d;
  logic [31:0] rvfi_rs2_data_q;
  logic [31:0] rvfi_rs3_data_d;
  logic [4:0]  rvfi_rd_addr_wb;
  logic [4:0]  rvfi_rd_addr_q;
  logic [4:0]  rvfi_rd_addr_d;
  logic [31:0] rvfi_rd_wdata_wb;
  logic [31:0] rvfi_rd_wdata_d;
  logic [31:0] rvfi_rd_wdata_q;
  logic        rvfi_rd_we_wb;
  logic [3:0]  rvfi_mem_mask_int;
  logic [31:0] rvfi_mem_rdata_d;
  logic [31:0] rvfi_mem_rdata_q;
  logic [31:0] rvfi_mem_wdata_d;
  logic [31:0] rvfi_mem_wdata_q;
  logic [31:0] rvfi_mem_addr_d;
  logic [31:0] rvfi_mem_addr_q;
  logic        rvfi_trap_id;
  logic        rvfi_trap_wb;
  logic        rvfi_irq_valid;
  logic [63:0] rvfi_stage_order_d;
  logic        rvfi_id_done;
  logic        rvfi_wb_done;

  logic            new_debug_req;
  logic            new_nmi;
  logic            new_nmi_int;
  logic            new_irq;
  ibex_pkg::irqs_t captured_mip;
  logic            captured_nmi;
  logic            captured_nmi_int;
  logic            captured_debug_req;
  logic            captured_valid;

  // RVFI extension for co-simulation support
  // debug_req and MIP captured at IF -> ID transition so one extra stage
  ibex_pkg::irqs_t rvfi_ext_stage_pre_mip          [RVFI_STAGES+1];
  ibex_pkg::irqs_t rvfi_ext_stage_post_mip         [RVFI_STAGES];
  logic            rvfi_ext_stage_nmi              [RVFI_STAGES+1];
  logic            rvfi_ext_stage_nmi_int          [RVFI_STAGES+1];
  logic            rvfi_ext_stage_debug_req        [RVFI_STAGES+1];
  logic            rvfi_ext_stage_debug_mode       [RVFI_STAGES];
  logic [63:0]     rvfi_ext_stage_mcycle           [RVFI_STAGES];
  logic [31:0]     rvfi_ext_stage_mhpmcounters     [RVFI_STAGES][10];
  logic [31:0]     rvfi_ext_stage_mhpmcountersh    [RVFI_STAGES][10];
  logic            rvfi_ext_stage_ic_scr_key_valid [RVFI_STAGES];
  logic            rvfi_ext_stage_irq_valid        [RVFI_STAGES+1];


  logic        rvfi_stage_valid_d   [RVFI_STAGES];

  assign rvfi_valid     = rvfi_stage_valid    [RVFI_STAGES-1];
  assign rvfi_order     = rvfi_stage_order    [RVFI_STAGES-1];
  assign rvfi_insn      = rvfi_stage_insn     [RVFI_STAGES-1];
  assign rvfi_trap      = rvfi_stage_trap     [RVFI_STAGES-1];
  assign rvfi_halt      = rvfi_stage_halt     [RVFI_STAGES-1];
  assign rvfi_intr      = rvfi_stage_intr     [RVFI_STAGES-1];
  assign rvfi_mode      = rvfi_stage_mode     [RVFI_STAGES-1];
  assign rvfi_ixl       = rvfi_stage_ixl      [RVFI_STAGES-1];
  assign rvfi_rs1_addr  = rvfi_stage_rs1_addr [RVFI_STAGES-1];
  assign rvfi_rs2_addr  = rvfi_stage_rs2_addr [RVFI_STAGES-1];
  assign rvfi_rs3_addr  = rvfi_stage_rs3_addr [RVFI_STAGES-1];
  assign rvfi_rs1_rdata = rvfi_stage_rs1_rdata[RVFI_STAGES-1];
  assign rvfi_rs2_rdata = rvfi_stage_rs2_rdata[RVFI_STAGES-1];
  assign rvfi_rs3_rdata = rvfi_stage_rs3_rdata[RVFI_STAGES-1];
  assign rvfi_rd_addr   = rvfi_stage_rd_addr  [RVFI_STAGES-1];
  assign rvfi_rd_wdata  = rvfi_stage_rd_wdata [RVFI_STAGES-1];
  assign rvfi_pc_rdata  = rvfi_stage_pc_rdata [RVFI_STAGES-1];
  assign rvfi_pc_wdata  = rvfi_stage_pc_wdata [RVFI_STAGES-1];
  assign rvfi_mem_addr  = rvfi_stage_mem_addr [RVFI_STAGES-1];
  assign rvfi_mem_rmask = rvfi_stage_mem_rmask[RVFI_STAGES-1];
  assign rvfi_mem_wmask = rvfi_stage_mem_wmask[RVFI_STAGES-1];
  assign rvfi_mem_rdata = rvfi_stage_mem_rdata[RVFI_STAGES-1];
  assign rvfi_mem_wdata = rvfi_stage_mem_wdata[RVFI_STAGES-1];

  assign rvfi_rd_addr_wb  = rf_waddr_wb;
  assign rvfi_rd_wdata_wb = rf_we_wb ? rf_wdata_wb : rf_wdata_lsu;
  assign rvfi_rd_we_wb    = rf_we_wb | rf_we_lsu;

  always_comb begin
    // Use always_comb instead of continuous assign so first assign can set 0 as default everywhere
    // that is overridden by more specific settings.
    rvfi_ext_pre_mip               = '0;
    rvfi_ext_pre_mip[CSR_MSIX_BIT] = rvfi_ext_stage_pre_mip[RVFI_STAGES].irq_software;
    rvfi_ext_pre_mip[CSR_MTIX_BIT] = rvfi_ext_stage_pre_mip[RVFI_STAGES].irq_timer;
    rvfi_ext_pre_mip[CSR_MEIX_BIT] = rvfi_ext_stage_pre_mip[RVFI_STAGES].irq_external;

    rvfi_ext_pre_mip[CSR_MFIX_BIT_HIGH:CSR_MFIX_BIT_LOW] =
      rvfi_ext_stage_pre_mip[RVFI_STAGES].irq_fast;

    rvfi_ext_post_mip               = '0;
    rvfi_ext_post_mip[CSR_MSIX_BIT] = rvfi_ext_stage_post_mip[RVFI_STAGES-1].irq_software;
    rvfi_ext_post_mip[CSR_MTIX_BIT] = rvfi_ext_stage_post_mip[RVFI_STAGES-1].irq_timer;
    rvfi_ext_post_mip[CSR_MEIX_BIT] = rvfi_ext_stage_post_mip[RVFI_STAGES-1].irq_external;

    rvfi_ext_post_mip[CSR_MFIX_BIT_HIGH:CSR_MFIX_BIT_LOW] =
      rvfi_ext_stage_post_mip[RVFI_STAGES-1].irq_fast;
  end

  assign rvfi_ext_nmi              = rvfi_ext_stage_nmi              [RVFI_STAGES];
  assign rvfi_ext_nmi_int          = rvfi_ext_stage_nmi_int          [RVFI_STAGES];
  assign rvfi_ext_debug_req        = rvfi_ext_stage_debug_req        [RVFI_STAGES];
  assign rvfi_ext_debug_mode       = rvfi_ext_stage_debug_mode       [RVFI_STAGES-1];
  assign rvfi_ext_mcycle           = rvfi_ext_stage_mcycle           [RVFI_STAGES-1];
  assign rvfi_ext_mhpmcounters     = rvfi_ext_stage_mhpmcounters     [RVFI_STAGES-1];
  assign rvfi_ext_mhpmcountersh    = rvfi_ext_stage_mhpmcountersh    [RVFI_STAGES-1];
  assign rvfi_ext_ic_scr_key_valid = rvfi_ext_stage_ic_scr_key_valid [RVFI_STAGES-1];
  assign rvfi_ext_irq_valid        = rvfi_ext_stage_irq_valid        [RVFI_STAGES];

  // When an instruction takes a trap the `rvfi_trap` signal will be set. Instructions that take
  // traps flush the pipeline so ordinarily wouldn't be seen to be retire. The RVFI tracking
  // pipeline is kept going for flushed instructions that trapped so they are still visible on the
  // RVFI interface.

  // Factor in exceptions taken in ID so RVFI tracking picks up flushed instructions that took
  // a trap
  assign rvfi_id_done = instr_id_done | (id_stage_i.controller_i.rvfi_flush_next &
                                         id_stage_i.controller_i.id_exception_o);

  if (WritebackStage) begin : gen_rvfi_wb_stage
    logic unused_instr_new_id;

    assign unused_instr_new_id = instr_new_id;

    // With writeback stage first RVFI stage buffers instruction information captured in ID/EX
    // awaiting instruction retirement and RF Write data/Mem read data whilst instruction is in WB
    // So first stage becomes valid when instruction leaves ID/EX stage and remains valid until
    // instruction leaves WB
    assign rvfi_stage_valid_d[0] = (rvfi_id_done & ~dummy_instr_id) |
                                   (rvfi_stage_valid[0] & ~rvfi_wb_done);
    // Second stage is output stage so simple valid cycle after instruction leaves WB (and so has
    // retired)
    assign rvfi_stage_valid_d[1] = rvfi_wb_done;

    // Signal new instruction in WB cycle after instruction leaves ID/EX (to enter WB)
    logic rvfi_instr_new_wb_q;

    // Signal new instruction in WB either when one has just entered or when a trap is progressing
    // through the tracking pipeline
    assign rvfi_instr_new_wb = rvfi_instr_new_wb_q | (rvfi_stage_valid[0] & rvfi_stage_trap[0]);

    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rvfi_instr_new_wb_q <= 0;
      end else begin
        rvfi_instr_new_wb_q <= rvfi_id_done;
      end
    end

    assign rvfi_trap_id = id_stage_i.controller_i.id_exception_o &
      ~(id_stage_i.ebrk_insn & id_stage_i.controller_i.ebreak_into_debug);

    assign rvfi_trap_wb = id_stage_i.controller_i.exc_req_lsu;
    // WB is instantly done in the tracking pipeline when a trap is progress through the pipeline
    assign rvfi_wb_done = rvfi_stage_valid[0] & (instr_done_wb | rvfi_stage_trap[0]);
  end else begin : gen_rvfi_no_wb_stage
    // Without writeback stage first RVFI stage is output stage so simply valid the cycle after
    // instruction leaves ID/EX (and so has retired)
    assign rvfi_stage_valid_d[0] = rvfi_id_done & ~dummy_instr_id;
    // Without writeback stage signal new instr_new_wb when instruction enters ID/EX to correctly
    // setup register write signals
    assign rvfi_instr_new_wb = instr_new_id;
    assign rvfi_trap_id =
      (id_stage_i.controller_i.exc_req_d | id_stage_i.controller_i.exc_req_lsu) &
      ~(id_stage_i.ebrk_insn & id_stage_i.controller_i.ebreak_into_debug);
    assign rvfi_trap_wb = 1'b0;
    assign rvfi_wb_done = instr_done_wb;
  end

  assign rvfi_stage_order_d = dummy_instr_id ? rvfi_stage_order[0] : rvfi_stage_order[0] + 64'd1;

  // For interrupts and debug Ibex will take the relevant trap as soon as whatever instruction in ID
  // finishes or immediately if the ID stage is empty. The rvfi_ext interface provides the DV
  // environment with information about the irq/debug_req/nmi state that applies to a particular
  // instruction.
  //
  // When a irq/debug_req/nmi appears the ID stage will finish whatever instruction it is currently
  // executing (if any) then take the trap the cycle after that instruction leaves the ID stage. The
  // trap taken depends upon the state of irq/debug_req/nmi on that cycle. In the cycles following
  // that before the first instruction of the trap handler enters the ID stage the state of
  // irq/debug_req/nmi could change but this has no effect on the trap handler (e.g. a higher
  // priority interrupt might appear but this wouldn't stop the lower priority interrupt trap
  // handler executing first as it's already being fetched). To provide the DV environment with the
  // correct information for it to verify execution we need to capture the irq/debug_req/nmi state
  // the cycle the trap decision is made. Which the captured_X signals below do.
  //
  // The new_X signals take the raw irq/debug_req/nmi inputs and factor in the enable terms required
  // to determine if a trap will actually happen.
  //
  // These signals and the comment above are referred to in the documentation (cosim.rst). If
  // altering the names or meanings of these signals or this comment please adjust the documentation
  // appropriately.
  assign new_debug_req = (debug_req_i & ~debug_mode);
  assign new_nmi = irq_nm_i & ~nmi_mode & ~debug_mode;
  assign new_nmi_int = id_stage_i.controller_i.irq_nm_int & ~nmi_mode & ~debug_mode;
  assign new_irq = irq_pending_o & (csr_mstatus_mie || (priv_mode_id == PRIV_LVL_U)) & ~nmi_mode &
                   ~debug_mode;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      captured_valid     <= 1'b0;
      captured_mip       <= '0;
      captured_nmi       <= 1'b0;
      captured_nmi_int   <= 1'b0;
      captured_debug_req <= 1'b0;
      rvfi_irq_valid     <= 1'b0;
    end else  begin
      // Capture when ID stage has emptied out and something occurs that will cause a trap and we
      // haven't yet captured
      //
      // When we already captured a trap, and there is upcoming nmi interrupt or
      // a debug request then recapture as nmi or debug request are supposed to
      // be serviced.
      if (~instr_valid_id & (new_debug_req | new_irq | new_nmi | new_nmi_int) &
          ((~captured_valid) |
           (new_debug_req & ~captured_debug_req) |
           (new_nmi & ~captured_nmi & ~captured_debug_req))) begin
        captured_valid     <= 1'b1;
        captured_nmi       <= irq_nm_i;
        captured_nmi_int   <= id_stage_i.controller_i.irq_nm_int;
        captured_mip       <= cs_registers_i.mip;
        captured_debug_req <= debug_req_i;
      end

      // When the pipeline has emptied in preparation for handling a new interrupt send
      // a notification up the RVFI pipeline. This is used by the cosim to deal with cases where an
      // interrupt occurs before another interrupt or debug request but both occur before the first
      // instruction of the handler is executed and retired (where the cosim will see all the
      // interrupts and debug requests at once with no way to determine which occurred first).
      if (~instr_valid_id & ~new_debug_req & (new_irq | new_nmi | new_nmi_int) & ready_wb &
          ~captured_valid) begin
        rvfi_irq_valid <= 1'b1;
      end else begin
        rvfi_irq_valid <= 1'b0;
      end

      // Capture cleared out as soon as a new instruction appears in ID
      if (if_stage_i.instr_valid_id_d) begin
        captured_valid <= 1'b0;
      end
    end
  end

  // Pass the captured irq/debug_req/nmi state to the rvfi_ext interface tracking pipeline.
  //
  // To correctly capture we need to factor in various enable terms, should there be a fault in this
  // logic we won't tell the DV environment about a trap that should have been taken. So if there's
  // no valid capture we grab the raw values of the irq/debug_req/nmi inputs whatever they are and
  // the DV environment will see if a trap should have been taken but wasn't.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_ext_stage_pre_mip[0]       <= '0;
      rvfi_ext_stage_nmi[0]       <= '0;
      rvfi_ext_stage_nmi_int[0]   <= '0;
      rvfi_ext_stage_debug_req[0] <= '0;
    end else if ((if_stage_i.instr_valid_id_d & if_stage_i.instr_new_id_d) | rvfi_irq_valid) begin
      rvfi_ext_stage_pre_mip[0]   <= instr_valid_id | ~captured_valid ? cs_registers_i.mip :
                                                                        captured_mip;
      rvfi_ext_stage_nmi[0]       <= instr_valid_id | ~captured_valid ? irq_nm_i :
                                                                        captured_nmi;
      rvfi_ext_stage_nmi_int[0]   <=
        instr_valid_id | ~captured_valid ? id_stage_i.controller_i.irq_nm_int :
                                           captured_nmi_int;
      rvfi_ext_stage_debug_req[0] <= instr_valid_id | ~captured_valid ? debug_req_i        :
                                                                        captured_debug_req;
    end
  end


  // rvfi_irq_valid signals an interrupt event to the cosim. These should only occur when the RVFI
  // pipe is empty so just send it straight through.
  for (genvar i = 0; i < RVFI_STAGES + 1; i = i + 1) begin : g_rvfi_irq_valid
    if (i == 0) begin : g_rvfi_irq_valid_first_stage
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rvfi_ext_stage_irq_valid[i] <= 1'b0;
        end else begin
          rvfi_ext_stage_irq_valid[i] <= rvfi_irq_valid;
        end
      end
    end else begin : g_rvfi_irq_valid_other_stages
      always_ff @(posedge clk_i or negedge rst_ni) begin
        if (!rst_ni) begin
          rvfi_ext_stage_irq_valid[i] <= 1'b0;
        end else begin
          rvfi_ext_stage_irq_valid[i] <= rvfi_ext_stage_irq_valid[i-1];
        end
      end
    end
  end

  for (genvar i = 0; i < RVFI_STAGES; i = i + 1) begin : g_rvfi_stages
    always_ff @(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rvfi_stage_halt[i]                 <= '0;
        rvfi_stage_trap[i]                 <= '0;
        rvfi_stage_intr[i]                 <= '0;
        rvfi_stage_order[i]                <= '0;
        rvfi_stage_insn[i]                 <= '0;
        rvfi_stage_mode[i]                 <= {PRIV_LVL_M};
        rvfi_stage_ixl[i]                  <= CSR_MISA_MXL;
        rvfi_stage_rs1_addr[i]             <= '0;
        rvfi_stage_rs2_addr[i]             <= '0;
        rvfi_stage_rs3_addr[i]             <= '0;
        rvfi_stage_pc_rdata[i]             <= '0;
        rvfi_stage_pc_wdata[i]             <= '0;
        rvfi_stage_mem_rmask[i]            <= '0;
        rvfi_stage_mem_wmask[i]            <= '0;
        rvfi_stage_valid[i]                <= '0;
        rvfi_stage_rs1_rdata[i]            <= '0;
        rvfi_stage_rs2_rdata[i]            <= '0;
        rvfi_stage_rs3_rdata[i]            <= '0;
        rvfi_stage_rd_wdata[i]             <= '0;
        rvfi_stage_rd_addr[i]              <= '0;
        rvfi_stage_mem_rdata[i]            <= '0;
        rvfi_stage_mem_wdata[i]            <= '0;
        rvfi_stage_mem_addr[i]             <= '0;
        rvfi_ext_stage_pre_mip[i+1]        <= '0;
        rvfi_ext_stage_post_mip[i]         <= '0;
        rvfi_ext_stage_nmi[i+1]            <= '0;
        rvfi_ext_stage_nmi_int[i+1]        <= '0;
        rvfi_ext_stage_debug_req[i+1]      <= '0;
        rvfi_ext_stage_debug_mode[i]       <= '0;
        rvfi_ext_stage_mcycle[i]           <= '0;
        rvfi_ext_stage_ic_scr_key_valid[i] <= '0;
        // DSim does not properly support array assignment in for loop, so unroll
        rvfi_ext_stage_mhpmcounters[i][0]  <= '0;
        rvfi_ext_stage_mhpmcountersh[i][0] <= '0;
        rvfi_ext_stage_mhpmcounters[i][1]  <= '0;
        rvfi_ext_stage_mhpmcountersh[i][1] <= '0;
        rvfi_ext_stage_mhpmcounters[i][2]  <= '0;
        rvfi_ext_stage_mhpmcountersh[i][2] <= '0;
        rvfi_ext_stage_mhpmcounters[i][3]  <= '0;
        rvfi_ext_stage_mhpmcountersh[i][3] <= '0;
        rvfi_ext_stage_mhpmcounters[i][4]  <= '0;
        rvfi_ext_stage_mhpmcountersh[i][4] <= '0;
        rvfi_ext_stage_mhpmcounters[i][5]  <= '0;
        rvfi_ext_stage_mhpmcountersh[i][5] <= '0;
        rvfi_ext_stage_mhpmcounters[i][6]  <= '0;
        rvfi_ext_stage_mhpmcountersh[i][6] <= '0;
        rvfi_ext_stage_mhpmcounters[i][7]  <= '0;
        rvfi_ext_stage_mhpmcountersh[i][7] <= '0;
        rvfi_ext_stage_mhpmcounters[i][8]  <= '0;
        rvfi_ext_stage_mhpmcountersh[i][8] <= '0;
        rvfi_ext_stage_mhpmcounters[i][9]  <= '0;
        rvfi_ext_stage_mhpmcountersh[i][9] <= '0;
      end else begin
        rvfi_stage_valid[i] <= rvfi_stage_valid_d[i];

        if (i == 0) begin
          if (rvfi_id_done) begin
            rvfi_stage_halt[i]                 <= '0;
            rvfi_stage_trap[i]                 <= rvfi_trap_id;
            rvfi_stage_intr[i]                 <= rvfi_intr_d;
            rvfi_stage_order[i]                <= rvfi_stage_order_d;
            rvfi_stage_insn[i]                 <= rvfi_insn_id;
            rvfi_stage_mode[i]                 <= {priv_mode_id};
            rvfi_stage_ixl[i]                  <= CSR_MISA_MXL;
            rvfi_stage_rs1_addr[i]             <= rvfi_rs1_addr_d;
            rvfi_stage_rs2_addr[i]             <= rvfi_rs2_addr_d;
            rvfi_stage_rs3_addr[i]             <= rvfi_rs3_addr_d;
            rvfi_stage_pc_rdata[i]             <= pc_id;
            rvfi_stage_pc_wdata[i]             <= pc_set ? branch_target_ex : pc_if;
            rvfi_stage_mem_rmask[i]            <= rvfi_mem_mask_int;
            rvfi_stage_mem_wmask[i]            <= data_we_o ? rvfi_mem_mask_int : 4'b0000;
            rvfi_stage_rs1_rdata[i]            <= rvfi_rs1_data_d;
            rvfi_stage_rs2_rdata[i]            <= rvfi_rs2_data_d;
            rvfi_stage_rs3_rdata[i]            <= rvfi_rs3_data_d;
            rvfi_stage_rd_addr[i]              <= rvfi_rd_addr_d;
            rvfi_stage_rd_wdata[i]             <= rvfi_rd_wdata_d;
            rvfi_stage_mem_rdata[i]            <= rvfi_mem_rdata_d;
            rvfi_stage_mem_wdata[i]            <= rvfi_mem_wdata_d;
            rvfi_stage_mem_addr[i]             <= rvfi_mem_addr_d;
            rvfi_ext_stage_debug_mode[i]       <= debug_mode;
            rvfi_ext_stage_mcycle[i]           <= cs_registers_i.mcycle_counter_i.counter_val_o;
            rvfi_ext_stage_ic_scr_key_valid[i] <= cs_registers_i.cpuctrlsts_ic_scr_key_valid_q;
            // DSim does not properly support array assignment in for loop, so unroll
            rvfi_ext_stage_mhpmcounters[i][0]  <= cs_registers_i.mhpmcounter[3][31:0];
            rvfi_ext_stage_mhpmcountersh[i][0] <= cs_registers_i.mhpmcounter[3][63:32];
            rvfi_ext_stage_mhpmcounters[i][1]  <= cs_registers_i.mhpmcounter[4][31:0];
            rvfi_ext_stage_mhpmcountersh[i][1] <= cs_registers_i.mhpmcounter[4][63:32];
            rvfi_ext_stage_mhpmcounters[i][2]  <= cs_registers_i.mhpmcounter[5][31:0];
            rvfi_ext_stage_mhpmcountersh[i][2] <= cs_registers_i.mhpmcounter[5][63:32];
            rvfi_ext_stage_mhpmcounters[i][3]  <= cs_registers_i.mhpmcounter[6][31:0];
            rvfi_ext_stage_mhpmcountersh[i][3] <= cs_registers_i.mhpmcounter[6][63:32];
            rvfi_ext_stage_mhpmcounters[i][4]  <= cs_registers_i.mhpmcounter[7][31:0];
            rvfi_ext_stage_mhpmcountersh[i][4] <= cs_registers_i.mhpmcounter[7][63:32];
            rvfi_ext_stage_mhpmcounters[i][5]  <= cs_registers_i.mhpmcounter[8][31:0];
            rvfi_ext_stage_mhpmcountersh[i][5] <= cs_registers_i.mhpmcounter[8][63:32];
            rvfi_ext_stage_mhpmcounters[i][6]  <= cs_registers_i.mhpmcounter[9][31:0];
            rvfi_ext_stage_mhpmcountersh[i][6] <= cs_registers_i.mhpmcounter[9][63:32];
            rvfi_ext_stage_mhpmcounters[i][7]  <= cs_registers_i.mhpmcounter[10][31:0];
            rvfi_ext_stage_mhpmcountersh[i][7] <= cs_registers_i.mhpmcounter[10][63:32];
            rvfi_ext_stage_mhpmcounters[i][8]  <= cs_registers_i.mhpmcounter[11][31:0];
            rvfi_ext_stage_mhpmcountersh[i][8] <= cs_registers_i.mhpmcounter[11][63:32];
            rvfi_ext_stage_mhpmcounters[i][9]  <= cs_registers_i.mhpmcounter[12][31:0];
            rvfi_ext_stage_mhpmcountersh[i][9] <= cs_registers_i.mhpmcounter[12][63:32];
          end

          // Some of the rvfi_ext_* signals are used to provide an interrupt notification (signalled
          // via rvfi_ext_irq_valid) when there isn't a valid retired instruction as well as
          // providing information along with a retired instruction. Move these up the rvfi pipeline
          // for both cases.
          if (rvfi_id_done | rvfi_ext_stage_irq_valid[i]) begin
            rvfi_ext_stage_pre_mip[i+1]   <= rvfi_ext_stage_pre_mip[i];
            rvfi_ext_stage_post_mip[i]    <= cs_registers_i.mip;
            rvfi_ext_stage_nmi[i+1]       <= rvfi_ext_stage_nmi[i];
            rvfi_ext_stage_nmi_int[i+1]   <= rvfi_ext_stage_nmi_int[i];
            rvfi_ext_stage_debug_req[i+1] <= rvfi_ext_stage_debug_req[i];
          end
        end else begin
          if (rvfi_wb_done) begin
            rvfi_stage_halt[i]      <= rvfi_stage_halt[i-1];
            rvfi_stage_trap[i]      <= rvfi_stage_trap[i-1] | rvfi_trap_wb;
            rvfi_stage_intr[i]      <= rvfi_stage_intr[i-1];
            rvfi_stage_order[i]     <= rvfi_stage_order[i-1];
            rvfi_stage_insn[i]      <= rvfi_stage_insn[i-1];
            rvfi_stage_mode[i]      <= rvfi_stage_mode[i-1];
            rvfi_stage_ixl[i]       <= rvfi_stage_ixl[i-1];
            rvfi_stage_rs1_addr[i]  <= rvfi_stage_rs1_addr[i-1];
            rvfi_stage_rs2_addr[i]  <= rvfi_stage_rs2_addr[i-1];
            rvfi_stage_rs3_addr[i]  <= rvfi_stage_rs3_addr[i-1];
            rvfi_stage_pc_rdata[i]  <= rvfi_stage_pc_rdata[i-1];
            rvfi_stage_pc_wdata[i]  <= rvfi_stage_pc_wdata[i-1];
            rvfi_stage_mem_rmask[i] <= rvfi_stage_mem_rmask[i-1];
            rvfi_stage_mem_wmask[i] <= rvfi_stage_mem_wmask[i-1];
            rvfi_stage_rs1_rdata[i] <= rvfi_stage_rs1_rdata[i-1];
            rvfi_stage_rs2_rdata[i] <= rvfi_stage_rs2_rdata[i-1];
            rvfi_stage_rs3_rdata[i] <= rvfi_stage_rs3_rdata[i-1];
            rvfi_stage_mem_wdata[i] <= rvfi_stage_mem_wdata[i-1];
            rvfi_stage_mem_addr[i]  <= rvfi_stage_mem_addr[i-1];

            // For 2 RVFI_STAGES/Writeback Stage ignore first stage flops for rd_addr, rd_wdata and
            // mem_rdata. For RF write addr/data actual write happens in writeback so capture
            // address/data there. For mem_rdata that is only available from the writeback stage.
            // Previous stage flops still exist in RTL as they are used by the non writeback config
            rvfi_stage_rd_addr[i]   <= rvfi_rd_addr_d;
            rvfi_stage_rd_wdata[i]  <= rvfi_rd_wdata_d;
            rvfi_stage_mem_rdata[i] <= rvfi_mem_rdata_d;

            rvfi_ext_stage_debug_mode[i]       <= rvfi_ext_stage_debug_mode[i-1];
            rvfi_ext_stage_mcycle[i]           <= rvfi_ext_stage_mcycle[i-1];
            rvfi_ext_stage_ic_scr_key_valid[i] <= rvfi_ext_stage_ic_scr_key_valid[i-1];
            rvfi_ext_stage_mhpmcounters[i]     <= rvfi_ext_stage_mhpmcounters[i-1];
            rvfi_ext_stage_mhpmcountersh[i]    <= rvfi_ext_stage_mhpmcountersh[i-1];
          end

          // Some of the rvfi_ext_* signals are used to provide an interrupt notification (signalled
          // via rvfi_ext_irq_valid) when there isn't a valid retired instruction as well as
          // providing information along with a retired instruction. Move these up the rvfi pipeline
          // for both cases.
          if (rvfi_wb_done | rvfi_ext_stage_irq_valid[i]) begin
            rvfi_ext_stage_pre_mip[i+1]   <= rvfi_ext_stage_pre_mip[i];
            rvfi_ext_stage_post_mip[i]    <= rvfi_ext_stage_post_mip[i-1];
            rvfi_ext_stage_nmi[i+1]       <= rvfi_ext_stage_nmi[i];
            rvfi_ext_stage_nmi_int[i+1]   <= rvfi_ext_stage_nmi_int[i];
            rvfi_ext_stage_debug_req[i+1] <= rvfi_ext_stage_debug_req[i];
          end
        end
      end
    end
  end


  // Memory address/write data available first cycle of ld/st instruction from register read
  always_comb begin
    if (instr_first_cycle_id) begin
      rvfi_mem_addr_d  = alu_adder_result_ex;
      rvfi_mem_wdata_d = lsu_wdata;
    end else begin
      rvfi_mem_addr_d  = rvfi_mem_addr_q;
      rvfi_mem_wdata_d = rvfi_mem_wdata_q;
    end
  end

  // Capture read data from LSU when it becomes valid
  always_comb begin
    if (lsu_resp_valid) begin
      rvfi_mem_rdata_d = rf_wdata_lsu;
    end else begin
      rvfi_mem_rdata_d = rvfi_mem_rdata_q;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_mem_addr_q  <= '0;
      rvfi_mem_rdata_q <= '0;
      rvfi_mem_wdata_q <= '0;
    end else begin
      rvfi_mem_addr_q  <= rvfi_mem_addr_d;
      rvfi_mem_rdata_q <= rvfi_mem_rdata_d;
      rvfi_mem_wdata_q <= rvfi_mem_wdata_d;
    end
  end
  // Byte enable based on data type
  always_comb begin
    unique case (lsu_type)
      2'b00:   rvfi_mem_mask_int = 4'b1111;
      2'b01:   rvfi_mem_mask_int = 4'b0011;
      2'b10:   rvfi_mem_mask_int = 4'b0001;
      default: rvfi_mem_mask_int = 4'b0000;
    endcase
  end

  always_comb begin
    if (instr_is_compressed_id) begin
      rvfi_insn_id = {16'b0, instr_rdata_c_id};
    end else begin
      rvfi_insn_id = instr_rdata_id;
    end
  end

  // Source registers 1 and 2 are read in the first instruction cycle
  // Source register 3 is read in the second instruction cycle.
  always_comb begin
    if (instr_first_cycle_id) begin
      rvfi_rs1_data_d = rf_ren_a ? multdiv_operand_a_ex : '0;
      rvfi_rs1_addr_d = rf_ren_a ? rf_raddr_a : '0;
      rvfi_rs2_data_d = rf_ren_b ? multdiv_operand_b_ex : '0;
      rvfi_rs2_addr_d = rf_ren_b ? rf_raddr_b : '0;
      rvfi_rs3_data_d = '0;
      rvfi_rs3_addr_d = '0;
    end else begin
      rvfi_rs1_data_d = rvfi_rs1_data_q;
      rvfi_rs1_addr_d = rvfi_rs1_addr_q;
      rvfi_rs2_data_d = rvfi_rs2_data_q;
      rvfi_rs2_addr_d = rvfi_rs2_addr_q;
      rvfi_rs3_data_d = multdiv_operand_a_ex;
      rvfi_rs3_addr_d = rf_raddr_a;
    end
  end
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_rs1_data_q <= '0;
      rvfi_rs1_addr_q <= '0;
      rvfi_rs2_data_q <= '0;
      rvfi_rs2_addr_q <= '0;

    end else begin
      rvfi_rs1_data_q <= rvfi_rs1_data_d;
      rvfi_rs1_addr_q <= rvfi_rs1_addr_d;
      rvfi_rs2_data_q <= rvfi_rs2_data_d;
      rvfi_rs2_addr_q <= rvfi_rs2_addr_d;
    end
  end

  always_comb begin
    if (rvfi_rd_we_wb) begin
      // Capture address/data of write to register file
      rvfi_rd_addr_d = rvfi_rd_addr_wb;
      // If writing to x0 zero write data as required by RVFI specification
      if (rvfi_rd_addr_wb == 5'b0) begin
        rvfi_rd_wdata_d = '0;
      end else begin
        rvfi_rd_wdata_d = rvfi_rd_wdata_wb;
      end
    end else if (rvfi_instr_new_wb) begin
      // If no RF write but new instruction in Writeback (when present) or ID/EX (when no writeback
      // stage present) then zero RF write address/data as required by RVFI specification
      rvfi_rd_addr_d  = '0;
      rvfi_rd_wdata_d = '0;
    end else begin
      // Otherwise maintain previous value
      rvfi_rd_addr_d  = rvfi_rd_addr_q;
      rvfi_rd_wdata_d = rvfi_rd_wdata_q;
    end
  end

  // RD write register is refreshed only once per cycle and
  // then it is kept stable for the cycle.
  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_rd_addr_q    <= '0;
      rvfi_rd_wdata_q   <= '0;
    end else begin
      rvfi_rd_addr_q    <= rvfi_rd_addr_d;
      rvfi_rd_wdata_q   <= rvfi_rd_wdata_d;
    end
  end

  if (WritebackStage) begin : g_rvfi_rf_wr_suppress_wb
    logic rvfi_stage_rf_wr_suppress_wb;
    logic rvfi_rf_wr_suppress_wb;

    // Set when RF write from load data is suppressed due to an integrity error
    assign rvfi_rf_wr_suppress_wb =
      instr_done_wb & ~rf_we_wb_o & outstanding_load_wb & lsu_load_resp_intg_err;

    always@(posedge clk_i or negedge rst_ni) begin
      if (!rst_ni) begin
        rvfi_stage_rf_wr_suppress_wb <= 1'b0;
      end else if (rvfi_wb_done) begin
        rvfi_stage_rf_wr_suppress_wb <= rvfi_rf_wr_suppress_wb;
      end
    end

    assign rvfi_ext_rf_wr_suppress = rvfi_stage_rf_wr_suppress_wb;
  end else begin : g_rvfi_no_rf_wr_suppress_wb
    assign rvfi_ext_rf_wr_suppress = 1'b0;
  end

  // rvfi_intr must be set for first instruction that is part of a trap handler.
  // On the first cycle of a new instruction see if a trap PC was set by the previous instruction,
  // otherwise maintain value.
  assign rvfi_intr_d = instr_first_cycle_id ? rvfi_set_trap_pc_q : rvfi_intr_q;

  always_comb begin
    rvfi_set_trap_pc_d = rvfi_set_trap_pc_q;

    if (pc_set && pc_mux_id == PC_EXC &&
        (exc_pc_mux_id == EXC_PC_EXC || exc_pc_mux_id == EXC_PC_IRQ)) begin
      // PC is set to enter a trap handler
      rvfi_set_trap_pc_d = 1'b1;
    end else if (rvfi_set_trap_pc_q && rvfi_id_done) begin
      // first instruction has been executed after PC is set to trap handler
      rvfi_set_trap_pc_d = 1'b0;
    end
  end

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      rvfi_set_trap_pc_q <= 1'b0;
      rvfi_intr_q        <= 1'b0;
    end else begin
      rvfi_set_trap_pc_q <= rvfi_set_trap_pc_d;
      rvfi_intr_q        <= rvfi_intr_d;
    end
  end

`else
  logic unused_instr_new_id, unused_instr_id_done, unused_instr_done_wb;
  assign unused_instr_id_done = instr_id_done;
  assign unused_instr_new_id = instr_new_id;
  assign unused_instr_done_wb = instr_done_wb;
`endif

  // Certain parameter combinations are not supported
  `ASSERT_INIT(IllegalParamSecure, !(SecureIbex && (RV32M == RV32MNone)))

  // If the ID stage signals its ready the mult/div FSMs must be idle in the following cycle
  `ASSERT(MultDivFSMIdleOnIdReady, id_in_ready |=> ex_block_i.sva_multdiv_fsm_idle)

  //////////
  // FCOV //
  //////////

`ifndef SYNTHESIS
  // fcov signals for V2S
  `DV_FCOV_SIGNAL_GEN_IF(logic, rf_ecc_err_a_id, gen_regfile_ecc.rf_ecc_err_a_id, RegFileECC)
  `DV_FCOV_SIGNAL_GEN_IF(logic, rf_ecc_err_b_id, gen_regfile_ecc.rf_ecc_err_b_id, RegFileECC)

  // fcov signals for CSR access. These are complicated by illegal accesses. Where an access is
  // legal `csr_op_en` signals the operation occurring, but this is deasserted where an access is
  // illegal. Instead `illegal_insn_id` confirms the instruction is taking an illegal instruction
  // exception.
  // All CSR operations perform a read, `CSR_OP_READ` is the only one that only performs a read
  `DV_FCOV_SIGNAL(logic, csr_read_only,
      (csr_op == CSR_OP_READ) && csr_access && (csr_op_en || illegal_insn_id))
  `DV_FCOV_SIGNAL(logic, csr_write,
      cs_registers_i.csr_wr && csr_access && (csr_op_en || illegal_insn_id))

  if (PMPEnable) begin : g_pmp_fcov_signals
    logic [PMPNumRegions-1:0] fcov_pmp_region_ichan_priority;
    logic [PMPNumRegions-1:0] fcov_pmp_region_ichan2_priority;
    logic [PMPNumRegions-1:0] fcov_pmp_region_dchan_priority;

    logic unused_fcov_pmp_region_priority;

    assign unused_fcov_pmp_region_priority = ^{fcov_pmp_region_ichan_priority,
                                               fcov_pmp_region_ichan2_priority,
                                               fcov_pmp_region_dchan_priority};

    for (genvar i_region = 0; i_region < PMPNumRegions; i_region += 1) begin : g_pmp_region_fcov
      `DV_FCOV_SIGNAL(logic, pmp_region_ichan_access,
          g_pmp.pmp_i.region_match_all[PMP_I][i_region] & if_stage_i.if_id_pipe_reg_we)
      `DV_FCOV_SIGNAL(logic, pmp_region_ichan2_access,
          g_pmp.pmp_i.region_match_all[PMP_I2][i_region] & if_stage_i.if_id_pipe_reg_we)
      `DV_FCOV_SIGNAL(logic, pmp_region_dchan_access,
          g_pmp.pmp_i.region_match_all[PMP_D][i_region] & data_req_out)
      // pmp_cfg[5:6] is reserved and because of that the width of it inside cs_registers module
      // is 6-bit.
      `DV_FCOV_SIGNAL(logic, warl_check_pmpcfg,
          fcov_csr_write &&
          (cs_registers_i.g_pmp_registers.g_pmp_csrs[i_region].u_pmp_cfg_csr.wr_data_i !=
          {cs_registers_i.csr_wdata_int[(i_region%4)*PMP_CFG_W+:5],
           cs_registers_i.csr_wdata_int[(i_region%4)*PMP_CFG_W+7]}))

      if (i_region > 0) begin : g_region_priority
        assign fcov_pmp_region_ichan_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_I][i_region] &
          ~|g_pmp.pmp_i.region_match_all[PMP_I][i_region-1:0];

        assign fcov_pmp_region_ichan2_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_I2][i_region] &
          ~|g_pmp.pmp_i.region_match_all[PMP_I2][i_region-1:0];

        assign fcov_pmp_region_dchan_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_D][i_region] &
          ~|g_pmp.pmp_i.region_match_all[PMP_D][i_region-1:0];
      end else begin : g_region_highest_priority
        assign fcov_pmp_region_ichan_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_I][i_region];

        assign fcov_pmp_region_ichan2_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_I2][i_region];

        assign fcov_pmp_region_dchan_priority[i_region] =
          g_pmp.pmp_i.region_match_all[PMP_D][i_region];
      end
    end
  end
`endif

endmodule
