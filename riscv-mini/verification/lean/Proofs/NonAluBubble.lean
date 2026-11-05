import Proofs.Forwarding
namespace RiscvMiniProofs
open nCoreSoc
set_option linter.unusedSimpArgs false
private theorem nonalu_suffix_v8219 (s : State) (i : Inputs) :
    v8219 s i ≠ 0 → v7464 s i = 1 → v7473 s i = 1 := by
  intro _ en
  simp [v7473, en, v512]
private theorem nonalu_suffix_v8220 (s : State) (i : Inputs) :
    v8220 s i ≠ 0 → v8268 s i = 1 → v7474 s i = 1 := by
  by_cases hc : v7460 s i = 1
  · simp [v8220, v7474, v8268, hc, v155, v512, v512]
  · simpa only [v8220, v7474, v8268, hc, if_false] using nonalu_suffix_v8219 s i
private theorem nonalu_suffix_v8221 (s : State) (i : Inputs) :
    v8221 s i ≠ 0 → v8269 s i = 1 → v7475 s i = 1 := by
  by_cases hc : v7456 s i = 1
  · simp [v8221, v7475, v8269, hc, v155, v512, v512]
  · simpa only [v8221, v7475, v8269, hc, if_false] using nonalu_suffix_v8220 s i
private theorem nonalu_suffix_v8222 (s : State) (i : Inputs) :
    v8222 s i ≠ 0 → v8270 s i = 1 → v7476 s i = 1 := by
  by_cases hc : v7452 s i = 1
  · simp [v8222, v7476, v8270, hc, v155, v512, v512]
  · simpa only [v8222, v7476, v8270, hc, if_false] using nonalu_suffix_v8221 s i
private theorem nonalu_suffix_v8223 (s : State) (i : Inputs) :
    v8223 s i ≠ 0 → v8271 s i = 1 → v7477 s i = 1 := by
  by_cases hc : v7448 s i = 1
  · simp [v8223, v7477, v8271, hc, v155, v512, v512]
  · simpa only [v8223, v7477, v8271, hc, if_false] using nonalu_suffix_v8222 s i
private theorem nonalu_suffix_v8224 (s : State) (i : Inputs) :
    v8224 s i ≠ 0 → v8272 s i = 1 → v7478 s i = 1 := by
  by_cases hc : v7444 s i = 1
  · simp [v8224, v7478, v8272, hc, v155, v512, v512]
  · simpa only [v8224, v7478, v8272, hc, if_false] using nonalu_suffix_v8223 s i
private theorem nonalu_suffix_v8225 (s : State) (i : Inputs) :
    v8225 s i ≠ 0 → v8273 s i = 1 → v7479 s i = 1 := by
  by_cases hc : v7440 s i = 1
  · simp [v8225, v7479, v8273, hc, v32, v512, v4]
  · simpa only [v8225, v7479, v8273, hc, if_false] using nonalu_suffix_v8224 s i
private theorem nonalu_suffix_v8226 (s : State) (i : Inputs) :
    v8226 s i ≠ 0 → v8274 s i = 1 → v7480 s i = 1 := by
  by_cases hc : v7438 s i = 1
  · simp [v8226, v7480, v8274, hc, v32, v4, v4]
  · simpa only [v8226, v7480, v8274, hc, if_false] using nonalu_suffix_v8225 s i
private theorem nonalu_suffix_v8227 (s : State) (i : Inputs) :
    v8227 s i ≠ 0 → v8275 s i = 1 → v7481 s i = 1 := by
  by_cases hc : v7434 s i = 1
  · simp [v8227, v7481, v8275, hc, v32, v4, v512]
  · simpa only [v8227, v7481, v8275, hc, if_false] using nonalu_suffix_v8226 s i
private theorem nonalu_suffix_v8228 (s : State) (i : Inputs) :
    v8228 s i ≠ 0 → v8276 s i = 1 → v7482 s i = 1 := by
  by_cases hc : v7431 s i = 1
  · simp [v8228, v7482, v8276, hc, v32, v4, v512]
  · simpa only [v8228, v7482, v8276, hc, if_false] using nonalu_suffix_v8227 s i
private theorem nonalu_suffix_v8229 (s : State) (i : Inputs) :
    v8229 s i ≠ 0 → v8277 s i = 1 → v7483 s i = 1 := by
  by_cases hc : v7428 s i = 1
  · simp [v8229, v7483, v8277, hc, v32, v4, v512]
  · simpa only [v8229, v7483, v8277, hc, if_false] using nonalu_suffix_v8228 s i
private theorem nonalu_suffix_v8230 (s : State) (i : Inputs) :
    v8230 s i ≠ 0 → v8278 s i = 1 → v7484 s i = 1 := by
  by_cases hc : v7425 s i = 1
  · simp [v8230, v7484, v8278, hc, v32, v4, v512]
  · simpa only [v8230, v7484, v8278, hc, if_false] using nonalu_suffix_v8229 s i
private theorem nonalu_suffix_v8231 (s : State) (i : Inputs) :
    v8231 s i ≠ 0 → v8279 s i = 1 → v7485 s i = 1 := by
  by_cases hc : v7422 s i = 1
  · simp [v8231, v7485, v8279, hc, v32, v4, v512]
  · simpa only [v8231, v7485, v8279, hc, if_false] using nonalu_suffix_v8230 s i
private theorem nonalu_suffix_v8232 (s : State) (i : Inputs) :
    v8232 s i ≠ 0 → v8280 s i = 1 → v7486 s i = 1 := by
  by_cases hc : v7419 s i = 1
  · simp [v8232, v7486, v8280, hc, v32, v4, v512]
  · simpa only [v8232, v7486, v8280, hc, if_false] using nonalu_suffix_v8231 s i
private theorem nonalu_suffix_v8233 (s : State) (i : Inputs) :
    v8233 s i ≠ 0 → v8281 s i = 1 → v7487 s i = 1 := by
  by_cases hc : v7416 s i = 1
  · simp [v8233, v7487, v8281, hc, v32, v4, v512]
  · simpa only [v8233, v7487, v8281, hc, if_false] using nonalu_suffix_v8232 s i
private theorem nonalu_suffix_v8234 (s : State) (i : Inputs) :
    v8234 s i ≠ 0 → v8282 s i = 1 → v7488 s i = 1 := by
  by_cases hc : v7413 s i = 1
  · simp [v8234, v7488, v8282, hc, v32, v4, v512]
  · simpa only [v8234, v7488, v8282, hc, if_false] using nonalu_suffix_v8233 s i
private theorem nonalu_suffix_v8235 (s : State) (i : Inputs) :
    v8235 s i ≠ 0 → v8283 s i = 1 → v7489 s i = 1 := by
  by_cases hc : v7410 s i = 1
  · simp [v8235, v7489, v8283, hc, v32, v4, v512]
  · simpa only [v8235, v7489, v8283, hc, if_false] using nonalu_suffix_v8234 s i
private theorem nonalu_suffix_v8236 (s : State) (i : Inputs) :
    v8236 s i ≠ 0 → v8284 s i = 1 → v7490 s i = 1 := by
  by_cases hc : v7407 s i = 1
  · simp [v8236, v7490, v8284, hc, v32, v4, v512]
  · simpa only [v8236, v7490, v8284, hc, if_false] using nonalu_suffix_v8235 s i
private theorem nonalu_suffix_v8237 (s : State) (i : Inputs) :
    v8237 s i ≠ 0 → v8285 s i = 1 → v7491 s i = 1 := by
  by_cases hc : v7404 s i = 1
  · simp [v8237, v7491, v8285, hc, v32, v4, v512]
  · simpa only [v8237, v7491, v8285, hc, if_false] using nonalu_suffix_v8236 s i
private theorem nonalu_suffix_v8238 (s : State) (i : Inputs) :
    v8238 s i ≠ 0 → v8286 s i = 1 → v7492 s i = 1 := by
  by_cases hc : v7401 s i = 1
  · simp [v8238, v7492, v8286, hc, v32, v4, v512]
  · simpa only [v8238, v7492, v8286, hc, if_false] using nonalu_suffix_v8237 s i
private theorem nonalu_suffix_v8239 (s : State) (i : Inputs) :
    v8239 s i ≠ 0 → v8287 s i = 1 → v7493 s i = 1 := by
  by_cases hc : v7398 s i = 1
  · simp [v8239, v7493, v8287, hc, v32, v4, v512]
  · simpa only [v8239, v7493, v8287, hc, if_false] using nonalu_suffix_v8238 s i
private theorem nonalu_suffix_v8240 (s : State) (i : Inputs) :
    v8240 s i ≠ 0 → v8288 s i = 1 → v7494 s i = 1 := by
  by_cases hc : v7395 s i = 1
  · simp [v8240, v7494, v8288, hc, v32, v4, v512]
  · simpa only [v8240, v7494, v8288, hc, if_false] using nonalu_suffix_v8239 s i
private theorem nonalu_suffix_v8241 (s : State) (i : Inputs) :
    v8241 s i ≠ 0 → v8289 s i = 1 → v7495 s i = 1 := by
  by_cases hc : v7391 s i = 1
  · simp [v8241, v7495, v8289, hc, v32, v4, v512]
  · simpa only [v8241, v7495, v8289, hc, if_false] using nonalu_suffix_v8240 s i
private theorem nonalu_suffix_v8242 (s : State) (i : Inputs) :
    v8242 s i ≠ 0 → v8290 s i = 1 → v7496 s i = 1 := by
  by_cases hc : v7387 s i = 1
  · simp [v8242, v7496, v8290, hc, v32, v4, v512]
  · simpa only [v8242, v7496, v8290, hc, if_false] using nonalu_suffix_v8241 s i
private theorem nonalu_suffix_v8243 (s : State) (i : Inputs) :
    v8243 s i ≠ 0 → v8291 s i = 1 → v7497 s i = 1 := by
  by_cases hc : v7383 s i = 1
  · simp [v8243, v7497, v8291, hc, v32, v4, v512]
  · simpa only [v8243, v7497, v8291, hc, if_false] using nonalu_suffix_v8242 s i
private theorem nonalu_suffix_v8244 (s : State) (i : Inputs) :
    v8244 s i ≠ 0 → v8292 s i = 1 → v7498 s i = 1 := by
  by_cases hc : v7379 s i = 1
  · simp [v8244, v7498, v8292, hc, v32, v4, v512]
  · simpa only [v8244, v7498, v8292, hc, if_false] using nonalu_suffix_v8243 s i
private theorem nonalu_suffix_v8245 (s : State) (i : Inputs) :
    v8245 s i ≠ 0 → v8293 s i = 1 → v7499 s i = 1 := by
  by_cases hc : v7375 s i = 1
  · simp [v8245, v7499, v8293, hc, v32, v4, v512]
  · simpa only [v8245, v7499, v8293, hc, if_false] using nonalu_suffix_v8244 s i
private theorem nonalu_suffix_v8246 (s : State) (i : Inputs) :
    v8246 s i ≠ 0 → v8294 s i = 1 → v7500 s i = 1 := by
  by_cases hc : v7371 s i = 1
  · simp [v8246, v7500, v8294, hc, v32, v4, v4]
  · simpa only [v8246, v7500, v8294, hc, if_false] using nonalu_suffix_v8245 s i
private theorem nonalu_suffix_v8247 (s : State) (i : Inputs) :
    v8247 s i ≠ 0 → v8295 s i = 1 → v7501 s i = 1 := by
  by_cases hc : v7367 s i = 1
  · simp [v8247, v7501, v8295, hc, v32, v4, v4]
  · simpa only [v8247, v7501, v8295, hc, if_false] using nonalu_suffix_v8246 s i
private theorem nonalu_suffix_v8248 (s : State) (i : Inputs) :
    v8248 s i ≠ 0 → v8296 s i = 1 → v7502 s i = 1 := by
  by_cases hc : v7363 s i = 1
  · simp [v8248, v7502, v8296, hc, v32, v4, v4]
  · simpa only [v8248, v7502, v8296, hc, if_false] using nonalu_suffix_v8247 s i
private theorem nonalu_suffix_v8249 (s : State) (i : Inputs) :
    v8249 s i ≠ 0 → v8297 s i = 1 → v7503 s i = 1 := by
  by_cases hc : v7359 s i = 1
  · simp [v8249, v7503, v8297, hc, v42, v512, v512]
  · simpa only [v8249, v7503, v8297, hc, if_false] using nonalu_suffix_v8248 s i
private theorem nonalu_suffix_v8250 (s : State) (i : Inputs) :
    v8250 s i ≠ 0 → v8298 s i = 1 → v7504 s i = 1 := by
  by_cases hc : v7355 s i = 1
  · simp [v8250, v7504, v8298, hc, v42, v512, v512]
  · simpa only [v8250, v7504, v8298, hc, if_false] using nonalu_suffix_v8249 s i
private theorem nonalu_suffix_v8251 (s : State) (i : Inputs) :
    v8251 s i ≠ 0 → v8299 s i = 1 → v7505 s i = 1 := by
  by_cases hc : v7351 s i = 1
  · simp [v8251, v7505, v8299, hc, v42, v512, v512]
  · simpa only [v8251, v7505, v8299, hc, if_false] using nonalu_suffix_v8250 s i
private theorem nonalu_suffix_v8252 (s : State) (i : Inputs) :
    v8252 s i ≠ 0 → v8300 s i = 1 → v7506 s i = 1 := by
  by_cases hc : v7347 s i = 1
  · simp [v8252, v7506, v8300, hc, v42, v512, v512]
  · simpa only [v8252, v7506, v8300, hc, if_false] using nonalu_suffix_v8251 s i
private theorem nonalu_suffix_v8253 (s : State) (i : Inputs) :
    v8253 s i ≠ 0 → v8301 s i = 1 → v7507 s i = 1 := by
  by_cases hc : v7343 s i = 1
  · simp [v8253, v7507, v8301, hc, v42, v512, v512]
  · simpa only [v8253, v7507, v8301, hc, if_false] using nonalu_suffix_v8252 s i
private theorem nonalu_suffix_v8254 (s : State) (i : Inputs) :
    v8254 s i ≠ 0 → v8302 s i = 1 → v7508 s i = 1 := by
  by_cases hc : v7339 s i = 1
  · simp [v8254, v7508, v8302, hc, v32, v4, v4]
  · simpa only [v8254, v7508, v8302, hc, if_false] using nonalu_suffix_v8253 s i
private theorem nonalu_suffix_v8255 (s : State) (i : Inputs) :
    v8255 s i ≠ 0 → v8303 s i = 1 → v7509 s i = 1 := by
  by_cases hc : v7335 s i = 1
  · simp [v8255, v7509, v8303, hc, v32, v4, v4]
  · simpa only [v8255, v7509, v8303, hc, if_false] using nonalu_suffix_v8254 s i
private theorem nonalu_suffix_v8256 (s : State) (i : Inputs) :
    v8256 s i ≠ 0 → v8304 s i = 1 → v7510 s i = 1 := by
  by_cases hc : v7331 s i = 1
  · simp [v8256, v7510, v8304, hc, v32, v4, v4]
  · simpa only [v8256, v7510, v8304, hc, if_false] using nonalu_suffix_v8255 s i
private theorem nonalu_suffix_v8257 (s : State) (i : Inputs) :
    v8257 s i ≠ 0 → v8305 s i = 1 → v7511 s i = 1 := by
  by_cases hc : v7327 s i = 1
  · simp [v8257, v7511, v8305, hc, v32, v4, v4]
  · simpa only [v8257, v7511, v8305, hc, if_false] using nonalu_suffix_v8256 s i
private theorem nonalu_suffix_v8258 (s : State) (i : Inputs) :
    v8258 s i ≠ 0 → v8306 s i = 1 → v7512 s i = 1 := by
  by_cases hc : v7323 s i = 1
  · simp [v8258, v7512, v8306, hc, v32, v4, v4]
  · simpa only [v8258, v7512, v8306, hc, if_false] using nonalu_suffix_v8257 s i
private theorem nonalu_suffix_v8259 (s : State) (i : Inputs) :
    v8259 s i ≠ 0 → v8307 s i = 1 → v7513 s i = 1 := by
  by_cases hc : v7319 s i = 1
  · simp [v8259, v7513, v8307, hc, v32, v4, v4]
  · simpa only [v8259, v7513, v8307, hc, if_false] using nonalu_suffix_v8258 s i
private theorem nonalu_suffix_v8260 (s : State) (i : Inputs) :
    v8260 s i ≠ 0 → v8308 s i = 1 → v7514 s i = 1 := by
  by_cases hc : v7315 s i = 1
  · simp [v8260, v7514, v8308, hc, v38, v512, v512]
  · simpa only [v8260, v7514, v8308, hc, if_false] using nonalu_suffix_v8259 s i
private theorem nonalu_suffix_v8261 (s : State) (i : Inputs) :
    v8261 s i ≠ 0 → v8309 s i = 1 → v7515 s i = 1 := by
  by_cases hc : v7311 s i = 1
  · simp [v8261, v7515, v8309, hc, v38, v512, v512]
  · simpa only [v8261, v7515, v8309, hc, if_false] using nonalu_suffix_v8260 s i
private theorem nonalu_suffix_v8262 (s : State) (i : Inputs) :
    v8262 s i ≠ 0 → v8310 s i = 1 → v7516 s i = 1 := by
  by_cases hc : v7307 s i = 1
  · simp [v8262, v7516, v8310, hc, v32, v4, v512]
  · simpa only [v8262, v7516, v8310, hc, if_false] using nonalu_suffix_v8261 s i
private theorem nonalu_suffix_v8263 (s : State) (i : Inputs) :
    v8263 s i ≠ 0 → v8311 s i = 1 → v7517 s i = 1 := by
  by_cases hc : v7303 s i = 1
  · simp [v8263, v7517, v8311, hc, v32, v4, v512]
  · simpa only [v8263, v7517, v8311, hc, if_false] using nonalu_suffix_v8262 s i
theorem nonalu_decode_kills (s : State) (i : Inputs) (h : v8265 s i ≠ 0)
    (en : v8313 s i = 1) : v7519 s i = 1 := nonalu_suffix_v8263 s i h en
#print axioms nonalu_decode_kills
end RiscvMiniProofs
