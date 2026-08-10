# domain_demo.tcl -- Goal 2 mechanism on silicon: a driver context runs in a
# protected domain entered only via a gate, holding a capability it received
# from its own in-memory inbox. Both the domain entry and the capability are
# load-bearing. Runs on the loaded dual bit via BSCAN; no NetBSD boot needed.
#
# Program: domain 0 mints the NIC token (0xCAFE) into domain 2's inbox
# (CAP_SEND), then GATE_CALLs gate 2 to enter domain 2. The domain-2 handler
# CAP_RECVs -- the receive index is the RUNNING domain, so only domain 2 can
# take it -- into r7, then returns. r7=0xCAFE means the driver got its cap in
# its own domain; r8=0 means the send landed.
source [file join [file dirname [info script]] board_env.tcl]
source $LOOM_JTAG_LIB
connect
targets -set -filter {name =~ "xc7z*"}
set DB 0x10000000
set GTB 0x2000
set CTB 0x3000
puts "ID=[format 0x%08x [rd 0]]"
proc wd {addr hi lo} { wr 40 [expr {$addr-8}]; wr 41 $lo; wr 42 $hi }
proc load_prog {} {
  wd 0x10001000 0x48080000 0x32bf8000
  wd 0x10001008 0x48100000 0x00008000
  wd 0x10001010 0xf8404400 0x00000000
  wd 0x10001018 0x48500000 0x00008000
  wd 0x10001020 0xfa028000 0x00000000
  wd 0x10001028 0x48300000 0x037bc000
  wd 0x10001030 0xfc000000 0x00000000
  wd 0x10001038 0xf7380000 0x00000000
  wd 0x10001040 0xf9000000 0x00000000
}
# gate 2 -> domain 2 handler at 0x1038; cap table domain-2 inbox valid+empty
proc load_gate2 {flags}   { wd 0x10002020 0x00000000 0x00001038; wd 0x10002028 0x00000000 $flags }
proc load_cap2  {flags}   { wd 0x10003020 0x00000000 0x00000000; wd 0x10003028 0x00000000 $flags }
proc run_once {tag} {
  wr 13 1 ; after 300
  load_prog
  wr 53 0x1000
  wr 74 $::GTB ; wr 75 $::CTB
  wr 13 2 ; after 800
  set r7 [regv 7]; set r8 [regv 8]; set r6 [regv 6]
  puts [format "%-11s r8=0x%x(send 0=ok) r7=0x%x(recv;0xcafe=cap in dom2) r6=0x%x(ran) retire=%d" \
        $tag $r8 $r7 $r6 [rd 21]]
  return [list $r7 $r8]
}

puts "== POSITIVE: gate 2 valid, domain-2 inbox valid =="
load_gate2 0x00000102 ; load_cap2 0x00000100
set pos [run_once "positive"]

puts "== NEG-A: revoke gate 2 (driver cannot ENTER its domain) =="
load_gate2 0x00000000 ; load_cap2 0x00000100
set nega [run_once "no-gate2"]

puts "== NEG-B: gate 2 valid but domain-2 inbox revoked (no capability) =="
load_gate2 0x00000102 ; load_cap2 0x00000000
set negb [run_once "no-cap"]

set p7 [lindex $pos 0]; set a7 [lindex $nega 0]; set b7 [lindex $negb 0]
if {$p7 == 0xcafe && $a7 != 0xcafe && $b7 != 0xcafe} {
  puts "DOMAIN_SANDBOX_OK: driver gets its cap in domain 2 (0xcafe); revoking the"
  puts "  gate blocks entry, revoking the inbox denies the capability"
} else {
  puts "DOMAIN_SANDBOX_FAIL: pos=$p7 no-gate=$a7 no-cap=$b7"
}
