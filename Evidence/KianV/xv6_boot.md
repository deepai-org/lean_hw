# KianV Loom-emitted xv6 boot

Status: **PASS**

- KianV fork commit: `c30ba47d23c926be5dceae275416c7635bd05c58`
- Elaboration defines: `SIM SYNTHESIS`
- Imported package SHA-256: `697a99ad4c8cdc322f7ff1c2e0bd41e283042cc5e38f9ad134ed9daa7b78e280`
- Package manifest SHA-256: `f31d443e796fde0bf33a7861cc732f2e06dc57ef06b2885ed27b76773fbf923a`
- Raw Loom RTL SHA-256: `ce46f64cd0104b765c5563b20c3d4c14f8e97e11ad4ca2f07115faab08cceb34`
- Yosys-cleaned Loom RTL SHA-256: `97f1852f9c2b03c1c82a8d5509166299072f94685fa1fb60555b7cc841fb4d41`
- xv6 kernel SHA-256: `f1541dcac2591686f7459e4185c52a8282ef79fe76c2758a90efe972692d9503`
- xv6 filesystem SHA-256: `688b04cf9070ffbaea38a0a5a5e943a6d910b597ce296345c3f930aa03645667`
- UART transcript SHA-256: `a377a7c9cb1f1321a2d76d6e5dbf12239fccf2135a72c28800a4907b1f26d8fc`
- Shell reached after: `222410634` modeled clocks

The pin-level Verilator harness uses KianV's SDRAM, SPI, and UART models. It
observed `xv6 kernel is booting`, `init: starting sh`, and the `$ ` shell
prompt. The cycle count exactly matches the corresponding upstream-RTL run.

Reproduce with:

```sh
scripts/boot_kianv_xv6.sh \
  ../kianv/gf180mcu-kianv-rv32ima-sv32 build/kianv-xv6-loom
```
