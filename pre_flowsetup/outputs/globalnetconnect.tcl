#=========================================================================
# globalnetconnect.tcl
#=========================================================================
# Author : Christopher Torng
# Date   : January 13, 2020

#-------------------------------------------------------------------------
# Global net connections for PG pins
#-------------------------------------------------------------------------

# Connect vpwr / vgnd if any cells have these pins

if { [ lindex [dbGet top.insts.cell.pgterms.name vpwr] 0 ] != 0x0 } {
  globalNetConnect vpwr -type pgpin -pin vpwr -inst * -verbose
} 
if { [ lindex [dbGet top.insts.cell.pgterms.name vgnd] 0 ] != 0x0 } {
  globalNetConnect vgnd -type pgpin -pin vgnd -inst * -verbose
}

# Connect VDD / VSS if any cells have these pins

if { [ lindex [dbGet top.insts.cell.pgterms.name VDD] 0 ] != 0x0 } {
  globalNetConnect vpwr -type pgpin -pin VDD -inst * -verbose
}

if { [ lindex [dbGet top.insts.cell.pgterms.name VSS] 0 ] != 0x0 } {
  globalNetConnect vgnd -type pgpin -pin VSS -inst * -verbose
}

# Connect VNW / VPW if any cells have these pins

if { [ lindex [dbGet top.insts.cell.pgterms.name VNW] 0 ] != 0x0 } {
  globalNetConnect vpwr -type pgpin -pin VNW -inst * -verbose
}

if { [ lindex [dbGet top.insts.cell.pgterms.name VPW] 0 ] != 0x0 } {
  globalNetConnect vgnd -type pgpin -pin VPW -inst * -verbose
}

# Connect vnb / vpb if any cells have these pins

if { [ lindex [dbGet top.insts.cell.pgterms.name vnb] 0 ] != 0x0 } {
  globalNetConnect vgnd -type pgpin -pin vnb -inst * -verbose
}

if { [ lindex [dbGet top.insts.cell.pgterms.name vpb] 0 ] != 0x0 } {
  globalNetConnect vpwr -type pgpin -pin vpb -inst * -verbose
}

# Connect vcc / vssx if any cells have these pins
if { [ lindex [dbGet top.insts.cell.pgterms.name vssx] 0 ] != 0x0 } {
  globalNetConnect vgnd -type pgpin -pin vssx -inst * -verbose
}

if { [ lindex [dbGet top.insts.cell.pgterms.name vcc] 0 ] != 0x0 } {
  globalNetConnect vpwr -type pgpin -pin vcc -inst * -verbose
}
