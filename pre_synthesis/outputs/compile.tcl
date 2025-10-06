#=========================================================================
# compile.tcl
#=========================================================================
# Author : Alex Carsello
# Date   : September 28, 2020

set_attr uniquify_naming_style "%s_%d"
# Removing uniquify to potentially reduce design effort
# uniquify $design_name

# Obey flattening effort of mflowgen graph
set_attribute auto_ungroup $auto_ungroup_val

syn_gen
#write_snapshot -directory results_syn -tag gen
#write_design -innovus -basename results_syn/syn_gen

set_attr syn_map_effort low
syn_map
write_snapshot -directory results_syn -tag map
write_design -innovus -basename results_syn/syn_map

syn_opt
