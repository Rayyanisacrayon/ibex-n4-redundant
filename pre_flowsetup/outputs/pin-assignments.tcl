#=========================================================================
# pin-assignments.tcl
#=========================================================================
# The ports of this design become physical pins along the perimeter of the
# design. The commands below will spread the pins along the left and right
# perimeters of the core area. This will work for most designs, but a
# detail-oriented project should customize or replace this section.
#
# Author : Christopher Torng
# Date   : March 26, 2018

#-------------------------------------------------------------------------
# Pin Assignments
#-------------------------------------------------------------------------

# Allow placing pins all the way up to met5
setPinAssignMode -maxLayer 18
setDesignMode -topRoutingLayer 18

# Take all ports and split into halves

set all_ports       [dbGet top.terms.name -v *clk*]

set num_ports       [llength $all_ports]
set half_ports_idx  [expr $num_ports / 2]

set pins_left_half  [lrange $all_ports 0               [expr $half_ports_idx - 1]]
set pins_right_half [lrange $all_ports $half_ports_idx [expr $num_ports - 1]     ]

# Take all clock ports and place them center-left

set clock_ports     [dbGet top.terms.name *clk*]
set half_left_idx   [expr [llength $pins_left_half] / 2]

if { $clock_ports != 0 } {
  for {set i 0} {$i < [llength $clock_ports]} {incr i} {
    set pins_left_half \
      [linsert $pins_left_half $half_left_idx [lindex $clock_ports $i]]
  }
}

# Calculate offset for pin placement to not overlap with power rings
set pwr_net_list {vpwr vgnd}; # List of power nets in the core power ring

set M1_min_width   [dbGet [dbGetLayerByZ 1].minWidth]
set M1_min_spacing [dbGet [dbGetLayerByZ 1].minSpacing]

set savedvars(p_ring_width)   [expr 48 * $M1_min_width];   # Arbitrary!
set savedvars(p_ring_spacing) [expr 24 * $M1_min_spacing]; # Arbitrary!

# Core bounding box margins

set core_margin [expr ([llength $pwr_net_list] * ($savedvars(p_ring_width) + $savedvars(p_ring_spacing))) + $savedvars(p_ring_spacing)]

# Spread the pins evenly across the left and right sides of the block

set ports_layer_top $ADK_PORT_LAYER_H_TOP
set ports_layer_bot $ADK_PORT_LAYER_H_BOT

#editPin -layer $ports_layer -pin $pins_left_half  -side LEFT  -spreadType SIDE
#editPin -layer $ports_layer -pin $pins_right_half -side RIGHT -spreadType SIDE
editPin -layer $ports_layer_bot -pin $pins_left_half  -spreadType SIDE -edge 0 -offsetStart $core_margin -offsetEnd $core_margin
editPin -layer $ports_layer_bot -pin $pins_right_half -spreadType SIDE -edge 2 -offsetStart $core_margin -offsetEnd $core_margin
if { $clock_ports != 0 } {
  for {set i 0} {$i < [llength $clock_ports]} {incr i} {
    editPin -layer $ports_layer_top -pin [lindex $clock_ports $i]
  }
}