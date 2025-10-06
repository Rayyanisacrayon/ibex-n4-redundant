#=========================================================================
# power-strategy-singlemesh.tcl
#=========================================================================
# This script implements a single power mesh on the upper metal layers.
# Note that M2 is expected to be vertical, and the lower metal layer of
# the power mesh is expected to be horizontal.
#
# Author : Christopher Torng
# Date   : January 20, 2019

#-------------------------------------------------------------------------
# Stdcell power rail preroute
#-------------------------------------------------------------------------
# Generate horizontal stdcell preroutes

# Done later using explict commands
#sroute -nets {vpwr vgnd}

#-------------------------------------------------------------------------
# Shorter names from the ADK
#-------------------------------------------------------------------------

set pmesh_bot $ADK_POWER_MESH_BOT_LAYER
set pmesh_top $ADK_POWER_MESH_TOP_LAYER
set pmesh_rails [expr $ADK_BASE_LAYER_IDX + 1]

#-------------------------------------------------------------------------
# Power ring
#-------------------------------------------------------------------------

addRing -nets {vpwr vgnd} -type core_rings -follow core   \
        -layer [list top  $pmesh_top bottom $pmesh_top  \
                     left $pmesh_bot right  $pmesh_bot] \
        -width $savedvars(p_ring_width)                 \
        -spacing $savedvars(p_ring_spacing)             \
        -offset $savedvars(p_ring_spacing)              \
        -extend_corner {tl tr bl br lt lb rt rb}

#-------------------------------------------------------------------------
# Power mesh bottom settings (vertical)
#-------------------------------------------------------------------------
# - pmesh_bot_str_width            : 8X thickness compared to 3 * C2TM width
# - pmesh_bot_str_pitch            : Arbitrarily choosing the stripe pitch
# - pmesh_bot_str_intraset_spacing : Space between vgnd/vpwr, choosing
#                                    constant pitch across vgnd/vpwr stripes
# - pmesh_bot_str_interset_pitch   : Pitch between same-signal stripes

# Get C2TM min width and signal routing pitch as defined in the LEF

set C2TM_min_width    [dbGet [dbGetLayerByZ [expr $ADK_BASE_LAYER_IDX + 1]].minWidth]
set C2TM_route_pitchX [dbGet [dbGetLayerByZ [expr $ADK_BASE_LAYER_IDX + 1]].pitchX]
set C2TM_route_pitchY [dbGet [dbGetLayerByZ [expr $ADK_BASE_LAYER_IDX + 1]].pitchY]

# Bottom stripe params

set pmesh_bot_str_width [expr  8 *  3 * $C2TM_min_width   ]
set pmesh_bot_str_pitch [expr 4 * 10 * $C2TM_route_pitchX]

set pmesh_bot_str_intraset_spacing [expr $pmesh_bot_str_pitch - $pmesh_bot_str_width]
set pmesh_bot_str_interset_pitch   [expr 2*$pmesh_bot_str_pitch]

setViaGenMode -reset
setViaGenMode -viarule_preference default
setViaGenMode -ignore_DRC false

setAddStripeMode -reset
setAddStripeMode -stacked_via_bottom_layer [expr $ADK_BASE_LAYER_IDX + 1] \
                 -stacked_via_top_layer    $pmesh_top

# Add the stripes
#
# Use -start to offset the stripes slightly away from the core edge.
# Allow same-layer jogs to connect stripes to the core ring if some
# blockage is in the way (e.g., connections from core ring to pads).
# Restrict any routing around blockages to use only layers for power.

addStripe -nets {vgnd vpwr} -layer $pmesh_bot -direction vertical \
    -width $pmesh_bot_str_width                                 \
    -spacing $pmesh_bot_str_intraset_spacing                    \
    -set_to_set_distance $pmesh_bot_str_interset_pitch          \
    -max_same_layer_jog_length $pmesh_bot_str_pitch             \
    -padcore_ring_bottom_layer_limit $pmesh_bot                 \
    -padcore_ring_top_layer_limit $pmesh_top                    \
    -start [expr $pmesh_bot_str_pitch]

#-------------------------------------------------------------------------
# Power mesh top settings (horizontal)
#-------------------------------------------------------------------------
# - pmesh_top_str_width            : 8X thickness compared to 3 * C2TM width
# - pmesh_top_str_pitch            : Arbitrarily choosing the stripe pitch
# - pmesh_top_str_intraset_spacing : Space between vgnd/vpwr, choosing
#                                    constant pitch across vgnd/vpwr stripes
# - pmesh_top_str_interset_pitch   : Pitch between same-signal stripes

set pmesh_top_str_width [expr  8 *  3 * $C2TM_min_width   ]
set pmesh_top_str_pitch [expr 4 * 10 * $C2TM_route_pitchX]

set pmesh_top_str_intraset_spacing [expr $pmesh_top_str_pitch - $pmesh_top_str_width]
set pmesh_top_str_interset_pitch   [expr 2*$pmesh_top_str_pitch]

setViaGenMode -reset
setViaGenMode -viarule_preference default
setViaGenMode -ignore_DRC false

setAddStripeMode -reset
#setAddStripeMode -stacked_via_bottom_layer $pmesh_bot \
#                 -stacked_via_top_layer    $pmesh_top
setAddStripeMode -stacked_via_bottom_layer $pmesh_rails \
                 -stacked_via_top_layer    $pmesh_top


# Add the stripes
#
# Use -start to offset the stripes slightly away from the core edge.
# Allow same-layer jogs to connect stripes to the core ring if some
# blockage is in the way (e.g., connections from core ring to pads).
# Restrict any routing around blockages to use only layers for power.

addStripe -nets {vgnd vpwr} -layer $pmesh_top -direction horizontal \
    -width $pmesh_top_str_width                                   \
    -spacing $pmesh_top_str_intraset_spacing                      \
    -set_to_set_distance $pmesh_top_str_interset_pitch            \
    -max_same_layer_jog_length $pmesh_top_str_pitch               \
    -padcore_ring_bottom_layer_limit $pmesh_bot                   \
    -padcore_ring_top_layer_limit $pmesh_top                      \
    -start [expr $pmesh_top_str_pitch]


setSrouteMode -viaConnectToShape { ring stripe } -extendNearestTarget true
sroute -connect { blockPin padPin corePin } -layerChangeRange { M1 M18 } \
   -blockPinTarget { ring } -padPinPortConnect { allPort oneGeom } \
   -padPinTarget { nearestTarget } -corePinTarget { ring } -allowJogging 1 \
   -crossoverViaLayerRange { M1 M18 } -nets { vpwr vgnd } -allowLayerChange 1 \
   -blockPin useLef -targetViaLayerRange { M1 M18 }

# Since power rails not being added automatically, manually add stripes on C1TM
# Calculate offset for stripe to align with stdcell rails
set pwr_net_list {vpwr vgnd}; # List of power nets in the core power ring

set M1_min_width   [dbGet [dbGetLayerByZ 1].minWidth]
set M1_min_spacing [dbGet [dbGetLayerByZ 1].minSpacing]

set savedvars(p_ring_width)   [expr 48 * $M1_min_width];   # Arbitrary!
set savedvars(p_ring_spacing) [expr 24 * $M1_min_spacing]; # Arbitrary!

# Core bounding box margins

set core_margin [expr ([llength $pwr_net_list] * ($savedvars(p_ring_width) + $savedvars(p_ring_spacing))) + $savedvars(p_ring_spacing)]

# The spacing and diatance will depend on the stdcell height; which is currently 8.16
# The power rail width also depends on the stdcell design
set pmesh_rails_width 0.48
addStripe -nets {vgnd vpwr} -layer $pmesh_rails -direction horizontal \
    -width $pmesh_rails_width                                     \
    -spacing [expr 8.16-$pmesh_rails_width]                       \
    -set_to_set_distance 16.32                                    \
    -padcore_ring_bottom_layer_limit $pmesh_bot                   \
    -padcore_ring_top_layer_limit $pmesh_top                      \
    -start [expr $core_margin-$pmesh_rails_width/2]

