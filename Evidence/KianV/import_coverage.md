# Neutral import coverage

This report executes the fail-closed Yosys-to-neutral-IR translator over
every module in one exact elaborated artifact. Acceptance means neutral IR
translation only; it does not imply emitted RTL equivalence or signoff.

- Modules: 74
- Accepted neutral imports: 42
- Blocked neutral imports: 32
- Elaborated JSON SHA-256: `8898eac9eba9975b617b9741cfd96210790f63cf694bcb07cb87f01641dad0f9`

## Blocker classes

- `four_state_constant`: 32 module(s)
- `four_state_memory_out_of_range`: 2 module(s)
- `four_state_variable_part_select`: 5 module(s)
- `multiple_clock_domains`: 1 module(s)

## Unclassified four-state sites

These stable identifiers are the exact units selected by an explicit refinement policy.

| Module | Site | Pattern | Source |
|---|---|---|---|
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_682d489152435fd72d33c455` | `288'x` | `src/kianv_harris_edition/associative_cache.v:56` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_3b3105663243e0ed90185983` | `32'x` | `src/kianv_harris_edition/associative_cache.v:58` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_f3069b8bdd8061cf09eba4e8` | `1024'x` | `src/kianv_harris_edition/associative_cache.v:57` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_d859aa4c51f2675a3e9afa8b` | `32'x` | `src/kianv_harris_edition/associative_cache.v:54` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_bbe9570f09abcb4b0580746f` | `640'x` | `src/kianv_harris_edition/associative_cache.v:55` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_70c19b4f3361f8283681ea1e` | `9'x` | `src/kianv_harris_edition/associative_cache.v:156` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_0738f6a55053f25b9d2e7b9e` | `32'x` | `src/kianv_harris_edition/associative_cache.v:166` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_a139ce9beb812cb3bab9b752` | `32'x` | `src/kianv_harris_edition/associative_cache.v:178` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_c1da5c0dddb306a5189fec00` | `1'dynamic-x` | `src/kianv_harris_edition/associative_cache.v:54` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_bbdd1aed918e90c84385dcef` | `20'dynamic-x` | `src/kianv_harris_edition/associative_cache.v:55` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_cd2fffd116be42640f2fffd7` | `1'dynamic-x` | `src/kianv_harris_edition/associative_cache.v:58` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_edf44e69edcadf9dd88dc68f` | `9'dynamic-x` | `src/kianv_harris_edition/associative_cache.v:56` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_6ef7919235ae299f4c55c097` | `32'x` | `src/kianv_harris_edition/associative_cache.v:156` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_0357ca3505aa137cd61471a4` | `9'x` | `src/kianv_harris_edition/associative_cache.v:166` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_fe6b39083885aac7d259e7d5` | `9'x` | `src/kianv_harris_edition/associative_cache.v:178` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_bc11c2792c808d71b165dfcf` | `1'x` | `src/kianv_harris_edition/associative_cache.v:156` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_3fc54b25156abe0c5d1fa4c8` | `1'x` | `src/kianv_harris_edition/associative_cache.v:166` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_36242a82ddd5ede0efc15a4b` | `1'x` | `src/kianv_harris_edition/associative_cache.v:178` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_e0d6d23685c8b937370d4be9` | `20'x` | `src/kianv_harris_edition/associative_cache.v:156` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_b5ec2914f7aa391282dd938a` | `20'x` | `src/kianv_harris_edition/associative_cache.v:166` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_ea781fcf1d728dab4b7369a0` | `20'x` | `src/kianv_harris_edition/associative_cache.v:178` |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | `four_state_c2ba39550fab21e1cfcd73ca` | `32'dynamic-x` | `src/kianv_harris_edition/associative_cache.v:57` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_b0253858b7b5b5dc2d3c68fd` | `1'x` | `src/sdram/mt48lc16m16a2_ctrl.v:675` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_37f8f0c31effad3db8c79a70` | `1'x` | `src/sdram/mt48lc16m16a2_ctrl.v:1` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_fed35ec1633f51ac5b35f81d` | `5'x` | `src/sdram/mt48lc16m16a2_ctrl.v:1` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_8d974a8c11ec7f7a5f2a9a20` | `5'x` | `src/sdram/mt48lc16m16a2_ctrl.v:500` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_330a9d0104644492a1c9e5d4` | `5'x` | `src/sdram/mt48lc16m16a2_ctrl.v:508` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_620ea3f1ce9542336ea8f4b3` | `5'x` | `src/sdram/mt48lc16m16a2_ctrl.v:521` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_882aabff0147cb8ef4a7a36b` | `5'x` | `src/sdram/mt48lc16m16a2_ctrl.v:542` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_13922c7cdcca8c3d9a9eb162` | `1'dynamic-x` | `src/sdram/mt48lc16m16a2_ctrl.v:1` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_d4b1ed0342f2269a7b3d3a88` | `5'x` | `src/sdram/mt48lc16m16a2_ctrl.v:541` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_9c6b5bdea81554b4d0eee795` | `5'x` | `src/sdram/mt48lc16m16a2_ctrl.v:538` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_1b2f3d43291007db003b2fff` | `1'dynamic-x` | `src/sdram/mt48lc16m16a2_ctrl.v:1` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_31f7ec18da20d0101aff75e8` | `4'x` | `src/sdram/mt48lc16m16a2_ctrl.v:500` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_3336c8f7907cfe4981cf450d` | `4'x` | `src/sdram/mt48lc16m16a2_ctrl.v:508` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_2ce1228c52322a5d18fe1220` | `4'x` | `src/sdram/mt48lc16m16a2_ctrl.v:1` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_8b4005a7cfd303d0808b82f3` | `4'x` | `src/sdram/mt48lc16m16a2_ctrl.v:521` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_f45577ca1703f47112cca7ab` | `4'x` | `src/sdram/mt48lc16m16a2_ctrl.v:542` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_8097dc5d4ef85726288da8ed` | `4'x` | `src/sdram/mt48lc16m16a2_ctrl.v:541` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_6e7ed589e08fc3069630056a` | `4'x` | `src/sdram/mt48lc16m16a2_ctrl.v:538` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_a6ad8eecab4792726439a983` | `1'x` | `src/sdram/mt48lc16m16a2_ctrl.v:500` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_a99331b6f515a3afecc2e880` | `1'x` | `src/sdram/mt48lc16m16a2_ctrl.v:508` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_2eb69f2c198600fc5c7533fd` | `1'x` | `src/sdram/mt48lc16m16a2_ctrl.v:521` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_f1c98b0ffce3369eddc052e6` | `1'x` | `src/sdram/mt48lc16m16a2_ctrl.v:542` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_929fb1dbc344ff3a8d465416` | `1'x` | `src/sdram/mt48lc16m16a2_ctrl.v:541` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_ca3175877b3ffc69728760ce` | `1'x` | `src/sdram/mt48lc16m16a2_ctrl.v:538` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_1cbfec7c7107f261bcfc498f` | `2'x` | `src/sdram/mt48lc16m16a2_ctrl.v:500` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_c057ab36a2f1df79a88cc52b` | `2'x` | `src/sdram/mt48lc16m16a2_ctrl.v:508` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_0518c51ed45f81c7ddf942e7` | `2'x` | `src/sdram/mt48lc16m16a2_ctrl.v:521` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_ef3d9a28201afa3dbb1aeba5` | `2'x` | `src/sdram/mt48lc16m16a2_ctrl.v:542` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_8f86353ed6194bfdb865c0f8` | `2'x` | `src/sdram/mt48lc16m16a2_ctrl.v:541` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_f071063a2fed87a6e6b25aaf` | `2'x` | `src/sdram/mt48lc16m16a2_ctrl.v:538` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_b91d986231fad7ad08dd4eaf` | `2'x` | `src/sdram/mt48lc16m16a2_ctrl.v:1` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_081c3faf78bb1e3961648542` | `3'x` | `src/sdram/mt48lc16m16a2_ctrl.v:405` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_4a337db360ef049452e1cb89` | `1'x` | `src/sdram/mt48lc16m16a2_ctrl.v:405` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_db50890c9a3b2b01fba187e8` | `4'x` | `src/sdram/mt48lc16m16a2_ctrl.v:405` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_7edcd9b6c9739440aaebbb75` | `16'x` | `src/sdram/mt48lc16m16a2_ctrl.v:500` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_75a061e0ea1afc4089667941` | `16'x` | `src/sdram/mt48lc16m16a2_ctrl.v:508` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_4b7596e349486380852dee79` | `16'x` | `src/sdram/mt48lc16m16a2_ctrl.v:1` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_cc7871ec4b3489eca351376e` | `16'x` | `src/sdram/mt48lc16m16a2_ctrl.v:521` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_46798827ba3217e0dc9e4bd7` | `16'x` | `src/sdram/mt48lc16m16a2_ctrl.v:542` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_c259435a043d2ca2d7d9cddb` | `16'x` | `src/sdram/mt48lc16m16a2_ctrl.v:541` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_7eb8c41093e3ec83fb3cbaf2` | `16'x` | `src/sdram/mt48lc16m16a2_ctrl.v:538` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_d6e1a23de5b45819e80f91aa` | `4'x` | `src/sdram/mt48lc16m16a2_ctrl.v:378` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_e8975016863c246a4eecf81e` | `1'x` | `src/sdram/mt48lc16m16a2_ctrl.v:577` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_ad96b00e79fd66b6a110a452` | `1'x` | `src/sdram/mt48lc16m16a2_ctrl.v:546` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_fce0b9d10400329e3934b74a` | `13'x` | `src/sdram/mt48lc16m16a2_ctrl.v:577` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_7098c3bf90ef9f69e2551be8` | `13'x` | `src/sdram/mt48lc16m16a2_ctrl.v:1` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | `four_state_4e65370a87d4bade7d4ace7b` | `16'x` | `src/sdram/mt48lc16m16a2_ctrl.v:405` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_0cf629610508df877a57ae1e` | `1'x` | `src/kianv_harris_edition/sv32_table_walk.v:163` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_edd941d05150a6e591a53e5d` | `1'x` | `src/kianv_harris_edition/sv32_table_walk.v:159` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_66ac68d64c3f16280d9e8a62` | `32'x` | `src/kianv_harris_edition/sv32_table_walk.v:249` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_45b633c87a48b1f0ed7316b3` | `32'x` | `src/kianv_harris_edition/sv32_table_walk.v:243` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_36edc1b00f5ea0f1e1ab76f6` | `32'x` | `src/kianv_harris_edition/sv32_table_walk.v:1` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_a2fa2f71befa88836579ed8d` | `32'x` | `src/kianv_harris_edition/sv32_table_walk.v:210` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_2e74fa8a77b96ba7a317cb43` | `32'x` | `src/kianv_harris_edition/sv32_table_walk.v:216` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_dd2251d1f5591b2e05326af4` | `1'x` | `src/kianv_harris_edition/sv32_table_walk.v:249` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_07cad52594fa59fdbdc7951e` | `1'x` | `src/kianv_harris_edition/sv32_table_walk.v:243` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_66a643bf9d4f4bd17994fc04` | `1'x` | `src/kianv_harris_edition/sv32_table_walk.v:1` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_f51af8d638836149f694ee12` | `1'x` | `src/kianv_harris_edition/sv32_table_walk.v:210` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_40997911fc44f47150dd4015` | `1'x` | `src/kianv_harris_edition/sv32_table_walk.v:216` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_48869b106aa46d8f07fd9d2f` | `2'x` | `src/kianv_harris_edition/sv32_table_walk.v:173` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_08176059330a13c71031d37f` | `2'x` | `src/kianv_harris_edition/sv32_table_walk.v:174` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_ec681391b2f6b5382647fd34` | `2'x` | `src/kianv_harris_edition/sv32_table_walk.v:1` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_a4773800db11a07e91681181` | `2'x` | `src/kianv_harris_edition/sv32_table_walk.v:249` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_000bb172e49bc0a845a5d5a7` | `2'x` | `src/kianv_harris_edition/sv32_table_walk.v:243` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_5ed9c25cc367856602461be9` | `2'x` | `src/kianv_harris_edition/sv32_table_walk.v:210` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_216f099027855e571bbc666c` | `2'x` | `src/kianv_harris_edition/sv32_table_walk.v:216` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_a52b7ea92bacc225294b215e` | `32'x` | `src/kianv_harris_edition/sv32_table_walk.v:254` |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | `four_state_3f3a43401c9498682f2e3860` | `1'x` | `src/kianv_harris_edition/sv32_table_walk.v:254` |
| `$paramod$6e553a45e44facf149505def5cdbbf99f283bb05\lru_replacement` | `four_state_ae5079e3c7f3a11fb6e9cd45` | `24'x` | `src/kianv_harris_edition/associative_cache.v:225` |
| `$paramod$6e553a45e44facf149505def5cdbbf99f283bb05\lru_replacement` | `four_state_89bad559519acdd65a7aff1d` | `3'x` | `src/kianv_harris_edition/associative_cache.v:228` |
| `$paramod$6e553a45e44facf149505def5cdbbf99f283bb05\lru_replacement` | `four_state_48e02c3b851ed647b19db34d` | `3'x` | `src/kianv_harris_edition/associative_cache.v:232` |
| `$paramod$6e553a45e44facf149505def5cdbbf99f283bb05\lru_replacement` | `four_state_a900c913678ef1595021957d` | `3'x` | `src/kianv_harris_edition/associative_cache.v:1` |
| `$paramod$6e553a45e44facf149505def5cdbbf99f283bb05\lru_replacement` | `four_state_318850b8254c9cdece75d72b` | `3'x` | `src/kianv_harris_edition/associative_cache.v:236` |
| `$paramod$6e553a45e44facf149505def5cdbbf99f283bb05\lru_replacement` | `four_state_865ce562cf84ee7168b3fee4` | `3'dynamic-x` | `src/kianv_harris_edition/associative_cache.v:225` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_D$` | `four_state_daf17c7d51947666fdde7438` | `512'x` | `src/cache_sram_D$.v:98` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_D$` | `four_state_e5e5eea7df9212d7b3923e57` | `512'x` | `src/cache_sram_D$.v:96` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_D$` | `four_state_c3f8be6f665d820bea97cff9` | `1'dynamic-x` | `src/cache_sram_D$.v:1` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | `four_state_ca45526fc401988fbf77dc7c` | `512'x` | `src/cache_sram_I$.v:140` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | `four_state_ed2212a0ddd1b4633f8ce4c3` | `1'dynamic-x` | `src/cache_sram_I$.v:1` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | `four_state_a3c4605eea60e3980de3cb41` | `1'dynamic-x` | `src/cache_sram_I$.v:1` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | `four_state_388e186818e8d597d380e8f2` | `1'dynamic-x` | `src/cache_sram_I$.v:1` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | `four_state_4eb2a0cdd4a856c616f1f7bb` | `1'dynamic-x` | `src/cache_sram_I$.v:1` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | `four_state_3338e09ecba984f2825fe35b` | `1'dynamic-x` | `src/cache_sram_I$.v:1` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | `four_state_d915ab1eec92e714a0e598b2` | `1'dynamic-x` | `src/cache_sram_I$.v:1` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | `four_state_a00c569b63a1b284043a6f1f` | `512'x` | `src/cache_sram_I$.v:136` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | `four_state_47ac609d577d41920af882e3` | `512'x` | `src/cache_sram_I$.v:149` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | `four_state_54ef6bd571c60cb7ad8d0b14` | `32'x` | `src/cache_sram_I$.v:130` |
| `$paramod$9b7a6de76a656f235265b36ced3b9a85d704f591\fifo` | `four_state_64396877abbb7c578603f783` | `128'x` | `src/fifo.v:39` |
| `$paramod$9b7a6de76a656f235265b36ced3b9a85d704f591\fifo` | `four_state_ca3175f4b29e624455fff6cc` | `4'x` | `src/fifo.v:88` |
| `$paramod$9b7a6de76a656f235265b36ced3b9a85d704f591\fifo` | `four_state_a6d251523a1891f624785803` | `8'x` | `src/fifo.v:88` |
| `$paramod$9b7a6de76a656f235265b36ced3b9a85d704f591\fifo` | `four_state_e4f499f5c4d7ca3c36915859` | `5'x` | `src/fifo.v:1` |
| `$paramod$a16ae7440305347911693e8e0f29ccf27deb10d1\sv32` | `four_state_28c6468cb65e949d9101a779` | `1'x` | `src/kianv_harris_edition/sv32.v:136` |
| `$paramod$a16ae7440305347911693e8e0f29ccf27deb10d1\sv32` | `four_state_3c4fe0db1fc203f67fb9b53c` | `1'x` | `src/kianv_harris_edition/sv32.v:1` |
| `$paramod$a16ae7440305347911693e8e0f29ccf27deb10d1\sv32` | `four_state_c380c5f539754d087c5cdece` | `32'x` | `src/kianv_harris_edition/sv32.v:1` |
| `$paramod$a16ae7440305347911693e8e0f29ccf27deb10d1\sv32` | `four_state_06f26a8457a28cabd2a2ba03` | `4'x` | `src/kianv_harris_edition/sv32.v:1` |
| `$paramod$a16ae7440305347911693e8e0f29ccf27deb10d1\sv32` | `four_state_9398976d89118c116c1cea43` | `34'x` | `src/kianv_harris_edition/sv32.v:1` |
| `$paramod$eb5ad0419ee7e371a55381f60d86c18c54bf32dc\uart_if` | `four_state_c084475bb7bc640c238167d2` | `1'x` | `src/soc.v:673` |
| `$paramod$eb5ad0419ee7e371a55381f60d86c18c54bf32dc\uart_if` | `four_state_1e0497fef4d2b93a83d53862` | `32'x` | `src/soc.v:693` |
| `$paramod$eb5ad0419ee7e371a55381f60d86c18c54bf32dc\uart_if` | `four_state_223a9b0160a236fd81d469e3` | `32'x` | `src/soc.v:696` |
| `$paramod$eb5ad0419ee7e371a55381f60d86c18c54bf32dc\uart_if` | `four_state_91804141be7550e811d32d83` | `1'x` | `src/soc.v:693` |
| `$paramod$eb5ad0419ee7e371a55381f60d86c18c54bf32dc\uart_if` | `four_state_d175cd544ac80dba1fe8d412` | `1'x` | `src/soc.v:696` |
| `alu_decoder` | `four_state_9726ab289ab681961f159ddc` | `width=80 unknown=25 pattern_sha256=cfb2b7b018b3c3c9` | `src/kianv_harris_edition/alu_decoder.v:57` |
| `alu_decoder` | `four_state_eabb3d517ea4f4fbb2930273` | `5'x` | `src/kianv_harris_edition/alu_decoder.v:1` |
| `csr_unit` | `four_state_5b75638997ac0208d1bf8d34` | `32'x` | `src/kianv_harris_edition/csr_unit.v:369` |
| `csr_unit` | `four_state_89d106b6329db5356952bb74` | `32'x` | `src/kianv_harris_edition/csr_unit.v:404` |
| `csr_unit` | `four_state_f158c360a07fe2d3b7fd701a` | `32'x` | `src/kianv_harris_edition/csr_unit.v:418` |
| `csr_unit` | `four_state_3224874c035262e8ea625476` | `32'x` | `src/kianv_harris_edition/csr_unit.v:432` |
| `csr_unit` | `four_state_42e66e61ba54b0ae091b8a40` | `1'x` | `src/kianv_harris_edition/csr_unit.v:369` |
| `csr_unit` | `four_state_26b0a2ce4c1ffb9bcd3584e3` | `1'x` | `src/kianv_harris_edition/csr_unit.v:404` |
| `csr_unit` | `four_state_97a660923ab89891ec7f4a0a` | `32'x` | `src/kianv_harris_edition/csr_unit.v:373` |
| `csr_unit` | `four_state_fc552bbd82e2e71ee29b3917` | `2'x` | `src/kianv_harris_edition/csr_unit.v:369` |
| `csr_unit` | `four_state_dab989c1fad01e8bc9b5500f` | `2'x` | `src/kianv_harris_edition/csr_unit.v:404` |
| `csr_unit` | `four_state_f39a2a404aa97a8f85aa74cf` | `1'x` | `src/kianv_harris_edition/csr_unit.v:418` |
| `csr_unit` | `four_state_a912274cbabec643765205ec` | `1'x` | `src/kianv_harris_edition/csr_unit.v:432` |
| `dcache` | `four_state_89956a8251dbef9424cbaf7b` | `3'x` | `src/dcache.v:1` |
| `dcache` | `four_state_8571509ee96b57e7c9b28ad9` | `3'x` | `src/dcache.v:217` |
| `dcache` | `four_state_654ea80c511a22eb3a7ca851` | `3'x` | `src/dcache.v:220` |
| `dcache` | `four_state_5e3bd56363dedb6db4bb96d0` | `32'x` | `src/dcache.v:274` |
| `dcache` | `four_state_e33fe500a10ab5c9255d15d2` | `32'x` | `src/dcache.v:258` |
| `dcache` | `four_state_86ed01e217e1a92e8689cf28` | `32'x` | `src/dcache.v:266` |
| `dcache` | `four_state_013cb1a79c4e2c2785a29c54` | `1'x` | `src/dcache.v:1` |
| `dcache` | `four_state_826f5b9f29b6a617e153dd7f` | `32'x` | `src/dcache.v:315` |
| `dcache` | `four_state_cc3bc7ced2cc684c02e8c52e` | `32'x` | `src/dcache.v:1` |
| `dcache` | `four_state_b6e1365f496672eb8022698a` | `1'x` | `src/dcache.v:315` |
| `divider` | `four_state_fe60d1f05c7d808a48a557f7` | `6'x` | `src/kianv_harris_edition/design_func.vh:59` |
| `divider` | `four_state_ace61abd955ebe96661f4b67` | `32'x` | `src/kianv_harris_edition/design_func.vh:59` |
| `divider` | `four_state_c6d12d2b361ec2907aa59ec9` | `6'x` | `src/kianv_harris_edition/design_func.vh:26` |
| `divider` | `four_state_edc1ec69ea6205a173398628` | `32'x` | `src/kianv_harris_edition/design_func.vh:26` |
| `divider` | `four_state_afd7745aeaa4ed4c0dc4d447` | `5'x` | `src/kianv_harris_edition/divider.v:124` |
| `divider` | `four_state_457d1a1fffe3599b78f42bbc` | `4'x` | `src/kianv_harris_edition/divider.v:173` |
| `divider` | `four_state_ba14f0892dc77675b4f50e02` | `4'x` | `src/kianv_harris_edition/divider.v:124` |
| `divider` | `four_state_0a44ca2b2dfd1a67ca2ce60f` | `6'x` | `src/kianv_harris_edition/divider.v:124` |
| `divider` | `four_state_5713948b5f974d85abee0498` | `32'x` | `src/kianv_harris_edition/divider.v:185` |
| `divider` | `four_state_0f020498efc5d5977bce57cd` | `1'dynamic-x` | `src/kianv_harris_edition/divider.v:1` |
| `divider` | `four_state_cf5cbcdbfc5767590733feee` | `32'x` | `src/kianv_harris_edition/divider.v:124` |
| `divider` | `four_state_da0207fdd978d84f811220c0` | `32'x` | `src/kianv_harris_edition/divider.v:188` |
| `divider_decoder` | `four_state_6e9c3a99232f140c4f0273ad` | `2'x` | `src/kianv_harris_edition/divider_decoder.v:1` |
| `gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper` | `four_state_ae563c02badc73ee45adef73` | `4096'x` | `src/gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper.v:57` |
| `gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper` | `four_state_b2c58a7bc14737b07719e37f` | `9'x` | `src/gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper.v:63` |
| `gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper` | `four_state_d47bc4d9ca64937523e1ef46` | `9'x` | `src/gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper.v:65` |
| `gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper` | `four_state_8bb576b3a4aa33459959a864` | `9'x` | `src/gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper.v:67` |
| `gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper` | `four_state_272149da8d92ba066fe3ad99` | `8'x` | `src/gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper.v:63` |
| `gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper` | `four_state_6b55f757ec3870c92341403b` | `8'x` | `src/gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper.v:65` |
| `gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper` | `four_state_650a8acba11fc2750512b00e` | `8'x` | `src/gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper.v:67` |
| `gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper` | `four_state_ff3e941d3d863ed033542f97` | `1'x` | `src/gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper.v:67` |
| `gpio` | `four_state_a2b5547488913f579fc482b8` | `32'x` | `src/gpio.v:65` |
| `gpio` | `four_state_b33ce2d8a916443a27f02387` | `32'x` | `src/gpio.v:60` |
| `gpio` | `four_state_93588ba610885a1e1abe3d5b` | `32'x` | `src/gpio.v:55` |
| `icache` | `four_state_1b4f920a473fee1369a4842b` | `3'x` | `src/icache.v:1` |
| `icache` | `four_state_32c64468f25105533ee1e5a4` | `1'x` | `src/icache.v:1` |
| `icache` | `four_state_c8593405f7984c9ad5ed8461` | `32'x` | `src/icache.v:1` |
| `load_alignment` | `four_state_cdd1094c3be0d4b43316a1d4` | `16'x` | `src/kianv_harris_edition/load_alignment.v:51` |
| `load_alignment` | `four_state_103df1ca4fce8b770fe5f665` | `8'x` | `src/kianv_harris_edition/load_alignment.v:46` |
| `load_decoder` | `four_state_4be746292ce06e3d5773b0e3` | `3'x` | `src/kianv_harris_edition/load_decoder.v:39` |
| `load_decoder` | `four_state_a17d3dd3d8cc62ce2847cef1` | `1'x` | `src/kianv_harris_edition/load_decoder.v:39` |
| `main_fsm` | `four_state_aaf2364ab951008fac2cbfc5` | `6'x` | `src/kianv_harris_edition/main_fsm.v:1` |
| `main_fsm` | `four_state_b43ef0b7a8b70a0e1f5095e5` | `4'x` | `src/kianv_harris_edition/main_fsm.v:1` |
| `main_fsm` | `four_state_e6d5a5b3b9041580ec907ded` | `3'x` | `src/kianv_harris_edition/main_fsm.v:1` |
| `main_fsm` | `four_state_786ef775664c5b09c9b8cac5` | `32'x` | `src/kianv_harris_edition/main_fsm.v:1` |
| `mtime_source` | `four_state_f4bf76b895c65f63832aa07c` | `16'x` | `src/soc.v:1166` |
| `multiplier` | `four_state_cf348a2a68a3745429325193` | `6'x` | `src/kianv_harris_edition/design_func.vh:59` |
| `multiplier` | `four_state_f527dd1fe4092b5ca10566c0` | `32'x` | `src/kianv_harris_edition/design_func.vh:59` |
| `multiplier` | `four_state_0112e4f2f3373624f57861ba` | `32'x` | `src/kianv_harris_edition/multiplier.v:1` |
| `multiplier` | `four_state_c8bd4819c2fe3aeea7231df0` | `64'x` | `src/kianv_harris_edition/multiplier.v:1` |
| `multiplier` | `four_state_74cf75dab7644cfbdb39ff7a` | `64'x` | `src/kianv_harris_edition/multiplier.v:147` |
| `multiplier` | `four_state_be97ce5eefacd9b164c5a72b` | `6'x` | `src/kianv_harris_edition/multiplier.v:113` |
| `multiplier` | `four_state_1b620b1944434a245ce9b356` | `6'x` | `src/kianv_harris_edition/multiplier.v:150` |
| `multiplier` | `four_state_931846c9bfb3f3cc2e20acbe` | `6'x` | `src/kianv_harris_edition/multiplier.v:1` |
| `multiplier` | `four_state_9332fe0c737ad28cbb127fdf` | `6'x` | `src/kianv_harris_edition/multiplier.v:170` |
| `multiplier_decoder` | `four_state_9fe20d78f5a3f1f59e6fe1f7` | `2'x` | `src/kianv_harris_edition/multiplier_decoder.v:1` |
| `register_file` | `four_state_c1b778828cd2c173331d5db9` | `1024'x` | `src/kianv_harris_edition/register_file.v:33` |
| `register_file` | `four_state_d9cf106b0c6059eb056a184c` | `5'x` | `src/kianv_harris_edition/register_file.v:37` |
| `register_file` | `four_state_ec23cd5dc77673f8d8fc972b` | `32'x` | `src/kianv_harris_edition/register_file.v:37` |
| `rx_uart` | `four_state_ed28fb382da5567f2140ed45` | `1'x` | `src/rx_uart.v:114` |
| `rx_uart` | `four_state_fff07ae39a425f42a49ff861` | `3'x` | `src/rx_uart.v:127` |
| `rx_uart` | `four_state_c806be631b423149ce0440c5` | `3'x` | `src/rx_uart.v:88` |
| `rx_uart` | `four_state_dd9bd5bfddacd11bb22d46da` | `3'x` | `src/rx_uart.v:114` |
| `rx_uart` | `four_state_be9878c03bf70453a3d0ab78` | `3'x` | `src/rx_uart.v:96` |
| `rx_uart` | `four_state_6acfea38463fae1f8d612148` | `8'x` | `src/rx_uart.v:72` |
| `rx_uart` | `four_state_bc88ef2aa2ea04a98e9cdd73` | `17'x` | `src/rx_uart.v:127` |
| `rx_uart` | `four_state_2d460376338699e08bec6236` | `17'x` | `src/rx_uart.v:114` |
| `rx_uart` | `four_state_ddedc555eaa68da22fc9c2d5` | `17'x` | `src/rx_uart.v:96` |
| `rx_uart` | `four_state_546e8dbc16dcc5e8a69cd518` | `17'x` | `src/rx_uart.v:88` |
| `soc` | `four_state_1566d0b727b5ad502ec09909` | `32'x` | `src/soc.v:498` |
| `soc` | `four_state_7c86db0c25a1f1c7348dcc42` | `32'x` | `src/soc.v:501` |
| `soc` | `four_state_8bc567374960785a7b7a97d7` | `32'x` | `src/soc.v:504` |
| `soc` | `four_state_2c9b6ac9c9acdc88e578758a` | `32'x` | `src/soc.v:507` |
| `soc` | `four_state_d57e36db5b09ab7088ff6194` | `32'x` | `src/soc.v:510` |
| `soc` | `four_state_b8cfdbf1a555ed66d228e5c8` | `32'x` | `src/soc.v:513` |
| `soc` | `four_state_effb56cf0e4a06e07cdea46d` | `32'x` | `src/soc.v:516` |
| `soc` | `four_state_9576dcdb93568b42f3153d71` | `32'x` | `src/soc.v:519` |
| `soc` | `four_state_e57b51dfd15c0e525fb4b2ad` | `32'x` | `src/soc.v:522` |
| `soc` | `four_state_fb47d17bdc7c74af354e02d6` | `32'x` | `src/soc.v:497` |
| `soc` | `four_state_70478b04ea47e496a57f57dc` | `1'x` | `src/soc.v:498` |
| `soc` | `four_state_d2cb5afc8a42221e6865e67e` | `1'x` | `src/soc.v:501` |
| `soc` | `four_state_8f9ad0586046aac68f0d4839` | `1'x` | `src/soc.v:504` |
| `soc` | `four_state_612c4790325b86f64166c241` | `1'x` | `src/soc.v:507` |
| `soc` | `four_state_11e4a6c902450b1c7f450e03` | `1'x` | `src/soc.v:510` |
| `soc` | `four_state_aa08e6fd770f7af12539505b` | `1'x` | `src/soc.v:513` |
| `soc` | `four_state_42ce56409e5ea53498e54212` | `1'x` | `src/soc.v:516` |
| `soc` | `four_state_2f3c90e2bd618dcd65b1853a` | `1'x` | `src/soc.v:519` |
| `soc` | `four_state_4b26756077a07a20573cc3af` | `1'x` | `src/soc.v:522` |
| `soc` | `four_state_95535da35fe9cb1e1c918171` | `1'x` | `src/soc.v:497` |
| `spi_nor_flash` | `four_state_3787637d22ebfc1946ec6850` | `1'x` | `src/spi_nor_flash.v:121` |
| `spi_nor_flash` | `four_state_abadc7cedacc8ceee695b0c0` | `1'x` | `src/spi_nor_flash.v:107` |
| `spi_nor_flash` | `four_state_1e7e4afb42733b0a09c5f7e8` | `6'x` | `src/spi_nor_flash.v:121` |
| `spi_nor_flash` | `four_state_43573a372b7e5cc03a61d897` | `6'x` | `src/spi_nor_flash.v:125` |
| `spi_nor_flash` | `four_state_e4469dd26599c60b4ce8275c` | `6'x` | `src/spi_nor_flash.v:107` |
| `spi_nor_flash` | `four_state_fc7e340b486035bed7ebae05` | `3'x` | `src/spi_nor_flash.v:140` |
| `spi_nor_flash` | `four_state_a15394bcc168a135fbefa75c` | `3'x` | `src/spi_nor_flash.v:158` |
| `spi_nor_flash` | `four_state_7bf6cab557095b5b74f5b03d` | `3'x` | `src/spi_nor_flash.v:142` |
| `spi_nor_flash` | `four_state_5ac2b527856d66cae36d7abc` | `3'x` | `src/spi_nor_flash.v:121` |
| `spi_nor_flash` | `four_state_7e30b1fedea5512d93c08a21` | `3'x` | `src/spi_nor_flash.v:125` |
| `spi_nor_flash` | `four_state_96f3fbe1bce5c411af03daa4` | `3'x` | `src/spi_nor_flash.v:107` |
| `spi_nor_flash` | `four_state_c6e9d2e12ed770f60831e6ec` | `32'x` | `src/spi_nor_flash.v:121` |
| `spi_nor_flash` | `four_state_27a09dcea7b3467823db3d19` | `32'x` | `src/spi_nor_flash.v:107` |
| `spi_nor_flash` | `four_state_35273838ec98e675eabc0e77` | `2'x` | `src/spi_nor_flash.v:140` |
| `spi_nor_flash` | `four_state_2e68d56113c518e860127919` | `2'x` | `src/spi_nor_flash.v:158` |
| `spi_nor_flash` | `four_state_1fdd8fbba3e6d9ec645cc323` | `2'x` | `src/spi_nor_flash.v:142` |
| `spi_nor_flash` | `four_state_0aabfcf59ad371d1db4c0479` | `2'x` | `src/spi_nor_flash.v:121` |
| `spi_nor_flash` | `four_state_f5df9ff95c6db81bd463e6dd` | `2'x` | `src/spi_nor_flash.v:125` |
| `store_alignment` | `four_state_eb9859f891b612aeb07284c5` | `16'x` | `src/kianv_harris_edition/store_alignment.v:49` |
| `store_alignment` | `four_state_79ef793a127b7730a96f3609` | `8'x` | `src/kianv_harris_edition/store_alignment.v:42` |
| `store_alignment` | `four_state_ced5bb435011eaf40e61f7d3` | `8'x` | `src/kianv_harris_edition/store_alignment.v:41` |
| `store_alignment` | `four_state_16c317fcecda1feb008cbba3` | `16'x` | `src/kianv_harris_edition/store_alignment.v:48` |
| `store_alignment` | `four_state_df3e31a208b80519f1a4e287` | `8'x` | `src/kianv_harris_edition/store_alignment.v:40` |
| `store_alignment` | `four_state_921877dd674942dc2287b82d` | `8'x` | `src/kianv_harris_edition/store_alignment.v:39` |
| `store_decoder` | `four_state_1312559826853adb326fcdb8` | `2'x` | `src/kianv_harris_edition/store_decoder.v:38` |
| `store_decoder` | `four_state_acb0d57ddb3f83dc579a572e` | `1'x` | `src/kianv_harris_edition/store_decoder.v:38` |
| `sv32_translate_data_to_physical` | `four_state_a2031c16413d2dfce613708e` | `34'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:1` |
| `sv32_translate_data_to_physical` | `four_state_585d9a0f18d95712a90f4669` | `34'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:104` |
| `sv32_translate_data_to_physical` | `four_state_6b090ba0229e8ea57581fc5d` | `2'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:1` |
| `sv32_translate_data_to_physical` | `four_state_e0ba177273940108141eb260` | `34'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:103` |
| `sv32_translate_data_to_physical` | `four_state_4f221c916aa5fd3ca8c4b834` | `1'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:1` |
| `sv32_translate_data_to_physical` | `four_state_2f446cdcda59528a9779f804` | `1'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:120` |
| `sv32_translate_data_to_physical` | `four_state_2d90471cdf7c5cdeb788ceb9` | `1'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:124` |
| `sv32_translate_data_to_physical` | `four_state_dce0b5eb8640d7ab00b6759f` | `1'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:128` |
| `sv32_translate_data_to_physical` | `four_state_feff4c3eaceb7288770ebf03` | `1'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:122` |
| `sv32_translate_data_to_physical` | `four_state_ed6b59cfe2054571d57d0f7c` | `1'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:112` |
| `sv32_translate_data_to_physical` | `four_state_94f815e4ff13804ce4f9a946` | `1'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:104` |
| `sv32_translate_data_to_physical` | `four_state_832ad59ae0225ffd294689a5` | `1'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:103` |
| `sv32_translate_data_to_physical` | `four_state_b4f0dfd290a2707a8f5685b3` | `1'x` | `src/kianv_harris_edition/sv32_translate_data_to_physical.v:136` |
| `sv32_translate_instruction_to_physical` | `four_state_83231c883d1b43e383f78803` | `1'x` | `src/kianv_harris_edition/sv32_translate_instruction_to_physical.v:1` |
| `sv32_translate_instruction_to_physical` | `four_state_1b48827b3be484ae32ede7a3` | `1'x` | `src/kianv_harris_edition/sv32_translate_instruction_to_physical.v:95` |
| `sv32_translate_instruction_to_physical` | `four_state_7c512a33ef9c4dfed9194c65` | `1'x` | `src/kianv_harris_edition/sv32_translate_instruction_to_physical.v:94` |
| `sv32_translate_instruction_to_physical` | `four_state_986abd29065365c6d4a743b7` | `34'x` | `src/kianv_harris_edition/sv32_translate_instruction_to_physical.v:1` |
| `sv32_translate_instruction_to_physical` | `four_state_d71ca5df745f6ff1058d0324` | `34'x` | `src/kianv_harris_edition/sv32_translate_instruction_to_physical.v:95` |
| `sv32_translate_instruction_to_physical` | `four_state_b2a2f8296bac51ae70ecb426` | `34'x` | `src/kianv_harris_edition/sv32_translate_instruction_to_physical.v:94` |
| `sv32_translate_instruction_to_physical` | `four_state_cec1e62f952a6f515ff7cd41` | `1'x` | `src/kianv_harris_edition/sv32_translate_instruction_to_physical.v:101` |
| `sv32_translate_instruction_to_physical` | `four_state_f81ce2ed8e77648941aba0ed` | `1'x` | `src/kianv_harris_edition/sv32_translate_instruction_to_physical.v:116` |
| `sv32_translate_instruction_to_physical` | `four_state_e604530fd23ecc54ae546418` | `1'x` | `src/kianv_harris_edition/sv32_translate_instruction_to_physical.v:115` |
| `sv32_translate_instruction_to_physical` | `four_state_67ad424bf4d8ccf855319453` | `1'x` | `src/kianv_harris_edition/sv32_translate_instruction_to_physical.v:99` |
| `tx_uart` | `four_state_b92faa1cbecb74336ee4ee49` | `3'x` | `src/tx_uart.v:142` |
| `tx_uart` | `four_state_9dd2fffe4acba6ec10bdb6f1` | `3'x` | `src/tx_uart.v:92` |
| `tx_uart` | `four_state_f4478415ec444c9346632023` | `17'x` | `src/tx_uart.v:142` |
| `tx_uart` | `four_state_13f3b488b09fe80841c0396d` | `1'x` | `src/tx_uart.v:1` |
| `tx_uart` | `four_state_545df7c6ef0e93a29bbd83b1` | `1'dynamic-x` | `src/tx_uart.v:1` |

## Per-module status

| Module | Status | Blocker classes |
|---|---|---|
| `$paramod$07648fe22cda1c5887fba6b98d56d491849e8d4b\sdram_cfg_if` | ACCEPTED | — |
| `$paramod$24edb32283c2798b1a9de01e5e8a5775f3de8d6d\spi_if` | ACCEPTED | — |
| `$paramod$2c2a78eaab39f077d28c359da24eea1bb3ee72ca\sysinfo_if` | ACCEPTED | — |
| `$paramod$492cad6cc1c94f976b64f48c1b13281f93ce86b9\associative_cache` | BLOCKED | `four_state_constant`, `four_state_memory_out_of_range` |
| `$paramod$51b325c0bf7af6fa0361c6c967cd6867c5a2030e\mt48lc16m16a2_ctrl` | BLOCKED | `four_state_constant`, `four_state_variable_part_select`, `multiple_clock_domains` |
| `$paramod$530c0f32123495a95a65ef2dee5adb9a30a708f6\spi_if` | ACCEPTED | — |
| `$paramod$570b38d59ef2758ddb45cb679c2a1a19cf0ab83f\sv32_table_walk` | BLOCKED | `four_state_constant` |
| `$paramod$6e553a45e44facf149505def5cdbbf99f283bb05\lru_replacement` | BLOCKED | `four_state_constant`, `four_state_memory_out_of_range` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_D$` | BLOCKED | `four_state_constant`, `four_state_variable_part_select` |
| `$paramod$7478c16320694f6488495fa2a1d26fc9b2532d6c\cache_sram_I$` | BLOCKED | `four_state_constant`, `four_state_variable_part_select` |
| `$paramod$7639c2062dbcb83ce6fca4673452b1d6f11c5802\dff_kianV` | ACCEPTED | — |
| `$paramod$80b52c6771af61c058960d8e594f8fa1878424bc\div_if` | ACCEPTED | — |
| `$paramod$97c33ce1f197c7d09a6065d46e5aec5f4fa18127\Word_Reducer` | ACCEPTED | — |
| `$paramod$9b7a6de76a656f235265b36ced3b9a85d704f591\fifo` | BLOCKED | `four_state_constant` |
| `$paramod$9e9c3eac67bdfcffcee59edb9321066a49ebd9bc\gpio_if` | ACCEPTED | — |
| `$paramod$a16ae7440305347911693e8e0f29ccf27deb10d1\sv32` | BLOCKED | `four_state_constant` |
| `$paramod$a39b4da5cbc02a0ba8e2c33f3a070905ed9e4012\kianv_harris_mc_edition` | ACCEPTED | — |
| `$paramod$b21d8177f76650034fcf5c651716b86b29dd0174\spi_nor_if` | ACCEPTED | — |
| `$paramod$e0de9e5afae9227897f68c4fd4bf06762d640101\Bit_Reducer` | ACCEPTED | — |
| `$paramod$e990c30bcd7893b07a35da62716c79724dd6c561\dff_kianV` | ACCEPTED | — |
| `$paramod$eb5ad0419ee7e371a55381f60d86c18c54bf32dc\uart_if` | BLOCKED | `four_state_constant` |
| `$paramod\Bitmask_Isolate_Rightmost_1_Bit\WORD_WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\Logarithm_of_Powers_of_Two\WORD_WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\Priority_Encoder\WORD_WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\cache\BYPASS_CACHES=1'0` | ACCEPTED | — |
| `$paramod\clint_if\BASE_HI=8'00000010` | ACCEPTED | — |
| `$paramod\counter\WIDTH=s32'00000000000000000000000001000000` | ACCEPTED | — |
| `$paramod\datapath_unit\RESET_ADDR=32'00100000000100000000000000000000` | ACCEPTED | — |
| `$paramod\dff_kianV\WIDTH=s32'00000000000000000000000000000001` | ACCEPTED | — |
| `$paramod\dff_kianV\WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\dlatch_kianV\WIDTH=s32'00000000000000000000000000000010` | ACCEPTED | — |
| `$paramod\dlatch_kianV\WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\mux2\WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\mux4\WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\mux5\WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\mux6\WIDTH=s32'00000000000000000000000000100000` | ACCEPTED | — |
| `$paramod\plic_if\BASE_HI=8'00001100` | ACCEPTED | — |
| `$paramod\spi\CPOL=1'0` | ACCEPTED | — |
| `alu` | ACCEPTED | — |
| `alu_decoder` | BLOCKED | `four_state_constant` |
| `chip_core` | ACCEPTED | — |
| `clint` | ACCEPTED | — |
| `control_unit` | ACCEPTED | — |
| `csr_decoder` | ACCEPTED | — |
| `csr_exception_handler` | ACCEPTED | — |
| `csr_unit` | BLOCKED | `four_state_constant` |
| `dcache` | BLOCKED | `four_state_constant` |
| `divider` | BLOCKED | `four_state_constant`, `four_state_variable_part_select` |
| `divider_decoder` | BLOCKED | `four_state_constant` |
| `extend` | ACCEPTED | — |
| `gf180mcu_fd_ip_sram__sram512x8m8wm1_wrapper` | BLOCKED | `four_state_constant` |
| `gpio` | BLOCKED | `four_state_constant` |
| `icache` | BLOCKED | `four_state_constant` |
| `interrupt_controller` | ACCEPTED | — |
| `load_alignment` | BLOCKED | `four_state_constant` |
| `load_decoder` | BLOCKED | `four_state_constant` |
| `main_fsm` | BLOCKED | `four_state_constant` |
| `mtime_source` | BLOCKED | `four_state_constant` |
| `multiplier` | BLOCKED | `four_state_constant` |
| `multiplier_decoder` | BLOCKED | `four_state_constant` |
| `multiplier_extension_decoder` | ACCEPTED | — |
| `mux2` | ACCEPTED | — |
| `plic` | ACCEPTED | — |
| `register_file` | BLOCKED | `four_state_constant` |
| `rx_uart` | BLOCKED | `four_state_constant` |
| `soc` | BLOCKED | `four_state_constant` |
| `spi_nor_flash` | BLOCKED | `four_state_constant` |
| `sram_sp_gf180_512x56` | ACCEPTED | — |
| `store_alignment` | BLOCKED | `four_state_constant` |
| `store_decoder` | BLOCKED | `four_state_constant` |
| `sv32_translate_data_to_physical` | BLOCKED | `four_state_constant` |
| `sv32_translate_instruction_to_physical` | BLOCKED | `four_state_constant` |
| `sync_2ff` | ACCEPTED | — |
| `tx_uart` | BLOCKED | `four_state_constant`, `four_state_variable_part_select` |
