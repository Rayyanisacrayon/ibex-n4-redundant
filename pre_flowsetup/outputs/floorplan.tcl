#=========================================================================
# floorplan.tcl
#=========================================================================
# Author : Christopher Torng
# Date   : March 26, 2018

#-------------------------------------------------------------------------
# Floorplan variables
#-------------------------------------------------------------------------

# Set the floorplan to target a reasonable placement density with a good
# aspect ratio (height:width). An aspect ratio of 2.0 here will make a
# rectangular chip with a height that is twice the width.

set core_aspect_ratio   1.00; # Aspect ratio 1.0 for a square chip
set core_density_target 0.70; # Placement density of 70% is reasonable

# Make room in the floorplan for the core power ring

set pwr_net_list {vpwr vgnd}; # List of power nets in the core power ring

set M1_min_width   [dbGet [dbGetLayerByZ 1].minWidth]
set M1_min_spacing [dbGet [dbGetLayerByZ 1].minSpacing]

set savedvars(p_ring_width)   [expr 48 * $M1_min_width];   # Arbitrary!
set savedvars(p_ring_spacing) [expr 24 * $M1_min_spacing]; # Arbitrary!

# Core bounding box margins

set core_margin_t [expr ([llength $pwr_net_list] * ($savedvars(p_ring_width) + $savedvars(p_ring_spacing))) + $savedvars(p_ring_spacing)]
set core_margin_b [expr ([llength $pwr_net_list] * ($savedvars(p_ring_width) + $savedvars(p_ring_spacing))) + $savedvars(p_ring_spacing)]
set core_margin_r [expr ([llength $pwr_net_list] * ($savedvars(p_ring_width) + $savedvars(p_ring_spacing))) + $savedvars(p_ring_spacing)]
set core_margin_l [expr ([llength $pwr_net_list] * ($savedvars(p_ring_width) + $savedvars(p_ring_spacing))) + $savedvars(p_ring_spacing)]

#-------------------------------------------------------------------------
# Floorplan
#-------------------------------------------------------------------------

# Calling floorPlan with the "-r" flag sizes the floorplan according to
# the core aspect ratio and a density target (70% is a reasonable
# density).
#

floorPlan -r $core_aspect_ratio $core_density_target \
             $core_margin_l $core_margin_b $core_margin_r $core_margin_t \
          -site unithd3

setFlipping s

# Create route blockage for all C# internal layers
# May need to remove the ones from c1tm and c2bm if routing congestion
# Causing issues with ccopt having no usable cells - TODO: figure out cause and resolve
# create_route_blockage -rects {0 0 200 200} -layers {c1g c1psd c1tm c2bm c2g c2psd}
# create_route_blockage -rects {0 0 5000 5000} -layers {c1g c1psd c2g c2psd}

# Create blockage around the core but not overlapping
set dx [get_db [get_db designs] .bbox.dx]
set dy [get_db [get_db designs] .bbox.dy]
create_route_blockage -rects [list 0 0 $dx $core_margin_b] -layers {c1g c1psd c1tm c2bm c2g c2psd}
create_route_blockage -rects [list 0 [expr $dy-$core_margin_t] $dx $dy] -layers {c1g c1psd c1tm c2bm c2g c2psd}
create_route_blockage -rects [list 0 $core_margin_b $core_margin_l [expr $dy-$core_margin_t]] -layers {c1g c1psd c1tm c2bm c2g c2psd}
create_route_blockage -rects [list [expr $dx-$core_margin_r] $core_margin_b $dx [expr $dy-$core_margin_t]] -layers {c1g c1psd c1tm c2bm c2g c2psd}


# Prevent routing on r# layers (see it this works out, or modify techlef+lvs)
# RESULT: IT DOES NOT WORK - NEED TO MODIFY TECHLEF (AND ALL SUPPORTING FILES: CAPTABLE/QRC, LVS,..)
# create_route_blockage -rects {0 0 5000 5000} -layers {r1bm r1tm r2bm r2tm}


# Use automatic floorplan synthesis to pack macros (e.g., SRAMs) together

planDesign


