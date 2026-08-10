# conring_read.tcl -- read the in-guest console rings LIVE over JTAG (no A9 DAP
# switch, no network). Shares the TAP with the running servicer via the bus
# arbiter (wr 55 / rd 20 bit 3), reads via the mini HP master (bulk_gread).
# Ring: [u32 magic=0xc0ffee01][u32 wptr(bytes)][packed bytes]. wptr is a BYTE
# count; bytes are 4-per-u32 / 8-per-64bit-word, LSB first. Render raw + a
# collapse-runs view (the guest may broadcast each char across the word).
set DB 0x10000000
connect -url tcp:127.0.0.1:3121
after 300
source [file join [file dirname [info script]] jtag_lib.tcl]
proc bacq {} { wr 55 1; for {set i 0} {$i<400} {incr i} { if {([rd 20]>>3)&1} return }; puts "WARN: no bus grant" }
proc brel {} { wr 55 0 }
bacq
if {[catch {gread_health} he]} { puts "GREAD_HEALTH FAILED: $he"; brel; exit 1 }
foreach cr {0 1} {
  set base [expr {0x3000000 + $cr*0x100000}]
  set hdr [lindex [bulk_gread $base 1] 0]
  set magic [expr {$hdr & 0xffffffff}]
  set wptr  [expr {($hdr >> 32) & 0xffffffff}]
  if {$magic != 0xc0ffee01} { puts "=== core$cr: NO RING (magic=[format 0x%x $magic]) ==="; continue }
  set nb [expr {$wptr & 0xffff}]
  if {$nb > 6000} { set nb 6000 }
  puts "=== core$cr console: wptr=$wptr, $nb bytes ==="
  if {$nb <= 0} { puts "(empty)"; continue }
  set nwords [expr {($nb + 7) / 8}]
  set bytes {}
  foreach w [bulk_gread [expr {$base + 8}] $nwords] {
    for {set b 0} {$b < 8} {incr b} { lappend bytes [expr {($w >> ($b*8)) & 0xff}] }
  }
  set bytes [lrange $bytes 0 [expr {$nb-1}]]
  # raw
  set raw ""; foreach c $bytes { append raw [expr {($c>=32 && $c<127)||$c==10 ? [format %c $c] : "."}] }
  puts "-- raw --"; puts $raw
  # collapse consecutive duplicates (undo per-char broadcast)
  set coll ""; set prev -1
  foreach c $bytes { if {$c != $prev} { append coll [expr {($c>=32 && $c<127)||$c==10 ? [format %c $c] : "."}]; set prev $c } }
  puts "-- collapsed --"; puts $coll
}
brel
