#=========================================================================
# read-design.tcl
#=========================================================================
# Author : Alex Carsello
# Date   : September 28, 2020

set files {
inputs/prim_assert.sv
inputs/prim_assert_dummy_macros.svh
inputs/prim_pkg.sv
inputs/ibex_pkg.sv
inputs/prim_ram_1p_pkg.sv
inputs/prim_secded_pkg.sv
inputs/prim_secded_inv_39_32_dec.sv
inputs/prim_clock_gating.sv
inputs/ibex_alu.sv
inputs/ibex_compressed_decoder.sv
inputs/ibex_controller.sv
inputs/ibex_counter.sv
inputs/ibex_cs_registers.sv
inputs/ibex_csr.sv
inputs/ibex_decoder.sv
inputs/ibex_ex_block.sv
inputs/ibex_fetch_fifo.sv
inputs/ibex_id_stage.sv
inputs/ibex_if_stage.sv
inputs/ibex_load_store_unit.sv
inputs/ibex_multdiv_fast.sv
inputs/ibex_multdiv_slow.sv
inputs/ibex_pmp.sv
inputs/ibex_prefetch_buffer.sv
inputs/ibex_register_file_ff.sv
inputs/ibex_wb_stage.sv
inputs/ibex_core.sv
inputs/ibex_top.sv
}

# set svh_files [glob -directory inputs -type f *.svh]
# read_hdl -define $read_hdl_defines -sv $svh_files
read_hdl -define $read_hdl_defines -sv $files


# Prevent backslashes from being prepended to signal names...
# this causes SAIF files to be invalid...needs to be before elaboration.

set_attribute hdl_array_naming_style %s_%d
set_attribute hdl_bus_wire_naming_style %s_%d
set_attribute bit_blasted_port_style %s_%d /

elaborate $design_name