From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [src/check_pkvm_pgtables.c]. *)
Section code.
  Definition file_0 : string := "src/check_pkvm_pgtables.c".
  Definition loc_2 : location_info := LocationInfo file_0 209 8 246 9.
  Definition loc_3 : location_info := LocationInfo file_0 248 8 248 24.
  Definition loc_4 : location_info := LocationInfo file_0 248 15 248 23.
  Definition loc_5 : location_info := LocationInfo file_0 209 22 246 9.
  Definition loc_6 : location_info := LocationInfo file_0 209 23 232 9.
  Definition loc_8 : location_info := LocationInfo file_0 210 15 232 9.
  Definition loc_10 : location_info := LocationInfo file_0 211 15 232 9.
  Definition loc_12 : location_info := LocationInfo file_0 213 8 232 9.
  Definition loc_13 : location_info := LocationInfo file_0 214 16 231 17.
  Definition loc_14 : location_info := LocationInfo file_0 232 9 242 17.
  Definition loc_16 : location_info := LocationInfo file_0 234 16 242 17.
  Definition loc_17 : location_info := LocationInfo file_0 242 17 245 32.
  Definition loc_19 : location_info := LocationInfo file_0 245 16 245 32.
  Definition loc_20 : location_info := LocationInfo file_0 245 23 245 31.
  Definition loc_21 : location_info := LocationInfo file_0 234 88 242 17.
  Definition loc_22 : location_info := LocationInfo file_0 234 89 237 42.
  Definition loc_24 : location_info := LocationInfo file_0 235 23 237 42.
  Definition loc_26 : location_info := LocationInfo file_0 237 24 237 42.
  Definition loc_27 : location_info := LocationInfo file_0 237 42 239 43.
  Definition loc_29 : location_info := LocationInfo file_0 239 24 239 43.
  Definition loc_30 : location_info := LocationInfo file_0 239 43 241 50.
  Definition loc_32 : location_info := LocationInfo file_0 241 24 241 50.
  Definition loc_33 : location_info := LocationInfo file_0 241 31 241 49.
  Definition loc_34 : location_info := LocationInfo file_0 239 31 239 42.
  Definition loc_35 : location_info := LocationInfo file_0 237 31 237 41.
  Definition loc_36 : location_info := LocationInfo file_0 234 24 234 86.
  Definition loc_37 : location_info := LocationInfo file_0 234 24 234 27.
  Definition loc_38 : location_info := LocationInfo file_0 234 24 234 27.
  Definition loc_39 : location_info := LocationInfo file_0 234 30 234 86.
  Definition loc_40 : location_info := LocationInfo file_0 234 31 234 58.
  Definition loc_41 : location_info := LocationInfo file_0 234 32 234 53.
  Definition loc_42 : location_info := LocationInfo file_0 234 32 234 38.
  Definition loc_43 : location_info := LocationInfo file_0 234 34 234 37.
  Definition loc_44 : location_info := LocationInfo file_0 234 41 234 53.
  Definition loc_45 : location_info := LocationInfo file_0 234 42 234 45.
  Definition loc_46 : location_info := LocationInfo file_0 234 49 234 52.
  Definition loc_47 : location_info := LocationInfo file_0 234 56 234 57.
  Definition loc_48 : location_info := LocationInfo file_0 234 61 234 85.
  Definition loc_49 : location_info := LocationInfo file_0 234 62 234 66.
  Definition loc_50 : location_info := LocationInfo file_0 234 63 234 66.
  Definition loc_51 : location_info := LocationInfo file_0 234 70 234 84.
  Definition loc_52 : location_info := LocationInfo file_0 234 71 234 77.
  Definition loc_53 : location_info := LocationInfo file_0 234 71 234 73.
  Definition loc_54 : location_info := LocationInfo file_0 234 76 234 77.
  Definition loc_55 : location_info := LocationInfo file_0 234 80 234 83.
  Definition loc_56 : location_info := LocationInfo file_0 214 88 231 17.
  Definition loc_57 : location_info := LocationInfo file_0 214 89 217 42.
  Definition loc_59 : location_info := LocationInfo file_0 215 23 217 42.
  Definition loc_61 : location_info := LocationInfo file_0 217 24 217 42.
  Definition loc_62 : location_info := LocationInfo file_0 217 42 226 25.
  Definition loc_64 : location_info := LocationInfo file_0 219 24 226 25.
  Definition loc_65 : location_info := LocationInfo file_0 226 25 228 40.
  Definition loc_67 : location_info := LocationInfo file_0 228 24 228 40.
  Definition loc_68 : location_info := LocationInfo file_0 228 40 230 40.
  Definition loc_70 : location_info := LocationInfo file_0 230 24 230 40.
  Definition loc_71 : location_info := LocationInfo file_0 230 31 230 39.
  Definition loc_72 : location_info := LocationInfo file_0 228 31 228 39.
  Definition loc_73 : location_info := LocationInfo file_0 220 24 226 25.
  Definition loc_74 : location_info := LocationInfo file_0 220 25 222 62.
  Definition loc_76 : location_info := LocationInfo file_0 222 32 222 62.
  Definition loc_77 : location_info := LocationInfo file_0 222 62 225 48.
  Definition loc_79 : location_info := LocationInfo file_0 223 31 225 48.
  Definition loc_81 : location_info := LocationInfo file_0 225 32 225 48.
  Definition loc_82 : location_info := LocationInfo file_0 225 39 225 47.
  Definition loc_83 : location_info := LocationInfo file_0 222 39 222 61.
  Definition loc_84 : location_info := LocationInfo file_0 219 32 219 37.
  Definition loc_85 : location_info := LocationInfo file_0 219 32 219 37.
  Definition loc_86 : location_info := LocationInfo file_0 217 31 217 41.
  Definition loc_87 : location_info := LocationInfo file_0 214 24 214 86.
  Definition loc_88 : location_info := LocationInfo file_0 214 24 214 27.
  Definition loc_89 : location_info := LocationInfo file_0 214 24 214 27.
  Definition loc_90 : location_info := LocationInfo file_0 214 30 214 86.
  Definition loc_91 : location_info := LocationInfo file_0 214 31 214 58.
  Definition loc_92 : location_info := LocationInfo file_0 214 32 214 53.
  Definition loc_93 : location_info := LocationInfo file_0 214 32 214 38.
  Definition loc_94 : location_info := LocationInfo file_0 214 34 214 37.
  Definition loc_95 : location_info := LocationInfo file_0 214 41 214 53.
  Definition loc_96 : location_info := LocationInfo file_0 214 42 214 45.
  Definition loc_97 : location_info := LocationInfo file_0 214 49 214 52.
  Definition loc_98 : location_info := LocationInfo file_0 214 56 214 57.
  Definition loc_99 : location_info := LocationInfo file_0 214 61 214 85.
  Definition loc_100 : location_info := LocationInfo file_0 214 62 214 66.
  Definition loc_101 : location_info := LocationInfo file_0 214 63 214 66.
  Definition loc_102 : location_info := LocationInfo file_0 214 70 214 84.
  Definition loc_103 : location_info := LocationInfo file_0 214 71 214 77.
  Definition loc_104 : location_info := LocationInfo file_0 214 71 214 73.
  Definition loc_105 : location_info := LocationInfo file_0 214 76 214 77.
  Definition loc_106 : location_info := LocationInfo file_0 214 80 214 83.
  Definition loc_107 : location_info := LocationInfo file_0 209 15 209 20.
  Definition loc_108 : location_info := LocationInfo file_0 209 15 209 20.
  Definition loc_111 : location_info := LocationInfo file_0 343 2 343 55.
  Definition loc_112 : location_info := LocationInfo file_0 344 2 344 39.
  Definition loc_113 : location_info := LocationInfo file_0 345 2 345 34.
  Definition loc_114 : location_info := LocationInfo file_0 346 2 346 38.
  Definition loc_115 : location_info := LocationInfo file_0 348 2 348 16.
  Definition loc_116 : location_info := LocationInfo file_0 348 9 348 15.
  Definition loc_117 : location_info := LocationInfo file_0 348 9 348 15.
  Definition loc_118 : location_info := LocationInfo file_0 346 2 346 26.
  Definition loc_119 : location_info := LocationInfo file_0 346 2 346 17.
  Definition loc_120 : location_info := LocationInfo file_0 346 2 346 8.
  Definition loc_121 : location_info := LocationInfo file_0 346 29 346 37.
  Definition loc_122 : location_info := LocationInfo file_0 346 29 346 37.
  Definition loc_123 : location_info := LocationInfo file_0 345 2 345 29.
  Definition loc_124 : location_info := LocationInfo file_0 345 2 345 26.
  Definition loc_125 : location_info := LocationInfo file_0 345 2 345 17.
  Definition loc_126 : location_info := LocationInfo file_0 345 2 345 8.
  Definition loc_127 : location_info := LocationInfo file_0 345 32 345 33.
  Definition loc_128 : location_info := LocationInfo file_0 344 2 344 34.
  Definition loc_129 : location_info := LocationInfo file_0 344 2 344 26.
  Definition loc_130 : location_info := LocationInfo file_0 344 2 344 17.
  Definition loc_131 : location_info := LocationInfo file_0 344 2 344 8.
  Definition loc_132 : location_info := LocationInfo file_0 344 37 344 38.
  Definition loc_133 : location_info := LocationInfo file_0 343 2 343 34.
  Definition loc_134 : location_info := LocationInfo file_0 343 2 343 23.
  Definition loc_135 : location_info := LocationInfo file_0 343 2 343 17.
  Definition loc_136 : location_info := LocationInfo file_0 343 2 343 8.
  Definition loc_137 : location_info := LocationInfo file_0 343 37 343 54.
  Definition loc_140 : location_info := LocationInfo file_0 385 8 385 69.
  Definition loc_141 : location_info := LocationInfo file_0 385 15 385 68.
  Definition loc_142 : location_info := LocationInfo file_0 385 24 385 67.
  Definition loc_143 : location_info := LocationInfo file_0 385 25 385 44.
  Definition loc_144 : location_info := LocationInfo file_0 385 38 385 44.
  Definition loc_145 : location_info := LocationInfo file_0 385 38 385 44.
  Definition loc_146 : location_info := LocationInfo file_0 385 47 385 66.
  Definition loc_147 : location_info := LocationInfo file_0 385 47 385 66.
  Definition loc_150 : location_info := LocationInfo file_0 398 8 398 38.
  Definition loc_151 : location_info := LocationInfo file_0 399 8 405 9.
  Definition loc_152 : location_info := LocationInfo file_0 408 8 408 60.
  Definition loc_153 : location_info := LocationInfo file_0 410 8 453 9.
  Definition loc_154 : location_info := LocationInfo file_0 410 22 453 9.
  Definition loc_155 : location_info := LocationInfo file_0 410 23 420 17.
  Definition loc_157 : location_info := LocationInfo file_0 412 16 420 17.
  Definition loc_158 : location_info := LocationInfo file_0 420 17 451 9.
  Definition loc_160 : location_info := LocationInfo file_0 422 15 451 9.
  Definition loc_162 : location_info := LocationInfo file_0 423 15 451 9.
  Definition loc_164 : location_info := LocationInfo file_0 426 8 451 9.
  Definition loc_165 : location_info := LocationInfo file_0 427 16 450 17.
  Definition loc_166 : location_info := LocationInfo file_0 451 9 452 40.
  Definition loc_168 : location_info := LocationInfo file_0 452 17 452 40.
  Definition loc_169 : location_info := LocationInfo file_0 452 24 452 39.
  Definition loc_170 : location_info := LocationInfo file_0 452 25 452 27.
  Definition loc_171 : location_info := LocationInfo file_0 452 26 452 27.
  Definition loc_172 : location_info := LocationInfo file_0 452 30 452 38.
  Definition loc_173 : location_info := LocationInfo file_0 452 30 452 38.
  Definition loc_174 : location_info := LocationInfo file_0 427 88 450 17.
  Definition loc_175 : location_info := LocationInfo file_0 427 89 430 47.
  Definition loc_177 : location_info := LocationInfo file_0 428 23 430 47.
  Definition loc_179 : location_info := LocationInfo file_0 430 24 430 47.
  Definition loc_180 : location_info := LocationInfo file_0 430 47 439 25.
  Definition loc_182 : location_info := LocationInfo file_0 432 24 439 25.
  Definition loc_183 : location_info := LocationInfo file_0 439 25 448 17.
  Definition loc_185 : location_info := LocationInfo file_0 441 16 448 17.
  Definition loc_186 : location_info := LocationInfo file_0 442 24 442 112.
  Definition loc_187 : location_info := LocationInfo file_0 443 24 445 64.
  Definition loc_188 : location_info := LocationInfo file_0 447 24 447 101.
  Definition loc_189 : location_info := LocationInfo file_0 448 17 449 48.
  Definition loc_191 : location_info := LocationInfo file_0 449 25 449 48.
  Definition loc_192 : location_info := LocationInfo file_0 449 32 449 47.
  Definition loc_193 : location_info := LocationInfo file_0 449 33 449 35.
  Definition loc_194 : location_info := LocationInfo file_0 449 34 449 35.
  Definition loc_195 : location_info := LocationInfo file_0 449 38 449 46.
  Definition loc_196 : location_info := LocationInfo file_0 449 38 449 46.
  Definition loc_197 : location_info := LocationInfo file_0 447 31 447 100.
  Definition loc_198 : location_info := LocationInfo file_0 447 31 447 59.
  Definition loc_199 : location_info := LocationInfo file_0 447 31 447 59.
  Definition loc_200 : location_info := LocationInfo file_0 447 60 447 80.
  Definition loc_201 : location_info := LocationInfo file_0 447 60 447 80.
  Definition loc_202 : location_info := LocationInfo file_0 447 82 447 89.
  Definition loc_203 : location_info := LocationInfo file_0 447 82 447 87.
  Definition loc_204 : location_info := LocationInfo file_0 447 82 447 87.
  Definition loc_205 : location_info := LocationInfo file_0 447 88 447 89.
  Definition loc_206 : location_info := LocationInfo file_0 447 91 447 99.
  Definition loc_207 : location_info := LocationInfo file_0 447 91 447 99.
  Definition loc_208 : location_info := LocationInfo file_0 443 24 443 44.
  Definition loc_209 : location_info := LocationInfo file_0 444 28 445 63.
  Definition loc_210 : location_info := LocationInfo file_0 444 48 445 63.
  Definition loc_211 : location_info := LocationInfo file_0 444 48 444 64.
  Definition loc_212 : location_info := LocationInfo file_0 444 48 444 64.
  Definition loc_213 : location_info := LocationInfo file_0 445 29 445 62.
  Definition loc_214 : location_info := LocationInfo file_0 445 42 445 62.
  Definition loc_215 : location_info := LocationInfo file_0 445 42 445 62.
  Definition loc_216 : location_info := LocationInfo file_0 442 24 442 44.
  Definition loc_217 : location_info := LocationInfo file_0 442 47 442 111.
  Definition loc_218 : location_info := LocationInfo file_0 442 47 442 50.
  Definition loc_219 : location_info := LocationInfo file_0 442 47 442 50.
  Definition loc_220 : location_info := LocationInfo file_0 442 53 442 111.
  Definition loc_221 : location_info := LocationInfo file_0 442 54 442 82.
  Definition loc_222 : location_info := LocationInfo file_0 442 55 442 77.
  Definition loc_223 : location_info := LocationInfo file_0 442 55 442 61.
  Definition loc_224 : location_info := LocationInfo file_0 442 57 442 60.
  Definition loc_225 : location_info := LocationInfo file_0 442 64 442 77.
  Definition loc_226 : location_info := LocationInfo file_0 442 65 442 68.
  Definition loc_227 : location_info := LocationInfo file_0 442 72 442 76.
  Definition loc_228 : location_info := LocationInfo file_0 442 80 442 81.
  Definition loc_229 : location_info := LocationInfo file_0 442 85 442 110.
  Definition loc_230 : location_info := LocationInfo file_0 442 86 442 90.
  Definition loc_231 : location_info := LocationInfo file_0 442 87 442 90.
  Definition loc_232 : location_info := LocationInfo file_0 442 94 442 109.
  Definition loc_233 : location_info := LocationInfo file_0 442 95 442 101.
  Definition loc_234 : location_info := LocationInfo file_0 442 95 442 97.
  Definition loc_235 : location_info := LocationInfo file_0 442 100 442 101.
  Definition loc_236 : location_info := LocationInfo file_0 442 104 442 108.
  Definition loc_237 : location_info := LocationInfo file_0 432 39 439 25.
  Definition loc_238 : location_info := LocationInfo file_0 432 40 434 55.
  Definition loc_240 : location_info := LocationInfo file_0 434 32 434 55.
  Definition loc_241 : location_info := LocationInfo file_0 434 55 436 181.
  Definition loc_243 : location_info := LocationInfo file_0 436 32 436 181.
  Definition loc_244 : location_info := LocationInfo file_0 436 181 438 181.
  Definition loc_246 : location_info := LocationInfo file_0 438 32 438 181.
  Definition loc_247 : location_info := LocationInfo file_0 438 39 438 180.
  Definition loc_248 : location_info := LocationInfo file_0 438 40 438 106.
  Definition loc_249 : location_info := LocationInfo file_0 438 41 438 44.
  Definition loc_250 : location_info := LocationInfo file_0 438 41 438 44.
  Definition loc_251 : location_info := LocationInfo file_0 438 47 438 105.
  Definition loc_252 : location_info := LocationInfo file_0 438 48 438 76.
  Definition loc_253 : location_info := LocationInfo file_0 438 49 438 71.
  Definition loc_254 : location_info := LocationInfo file_0 438 49 438 55.
  Definition loc_255 : location_info := LocationInfo file_0 438 51 438 54.
  Definition loc_256 : location_info := LocationInfo file_0 438 58 438 71.
  Definition loc_257 : location_info := LocationInfo file_0 438 59 438 62.
  Definition loc_258 : location_info := LocationInfo file_0 438 66 438 70.
  Definition loc_259 : location_info := LocationInfo file_0 438 74 438 75.
  Definition loc_260 : location_info := LocationInfo file_0 438 79 438 104.
  Definition loc_261 : location_info := LocationInfo file_0 438 80 438 84.
  Definition loc_262 : location_info := LocationInfo file_0 438 81 438 84.
  Definition loc_263 : location_info := LocationInfo file_0 438 88 438 103.
  Definition loc_264 : location_info := LocationInfo file_0 438 89 438 95.
  Definition loc_265 : location_info := LocationInfo file_0 438 89 438 91.
  Definition loc_266 : location_info := LocationInfo file_0 438 94 438 95.
  Definition loc_267 : location_info := LocationInfo file_0 438 98 438 102.
  Definition loc_268 : location_info := LocationInfo file_0 438 109 438 179.
  Definition loc_269 : location_info := LocationInfo file_0 438 110 438 118.
  Definition loc_270 : location_info := LocationInfo file_0 438 110 438 118.
  Definition loc_271 : location_info := LocationInfo file_0 438 121 438 178.
  Definition loc_272 : location_info := LocationInfo file_0 438 122 438 149.
  Definition loc_273 : location_info := LocationInfo file_0 438 123 438 144.
  Definition loc_274 : location_info := LocationInfo file_0 438 123 438 129.
  Definition loc_275 : location_info := LocationInfo file_0 438 125 438 128.
  Definition loc_276 : location_info := LocationInfo file_0 438 132 438 144.
  Definition loc_277 : location_info := LocationInfo file_0 438 133 438 136.
  Definition loc_278 : location_info := LocationInfo file_0 438 140 438 143.
  Definition loc_279 : location_info := LocationInfo file_0 438 147 438 148.
  Definition loc_280 : location_info := LocationInfo file_0 438 152 438 177.
  Definition loc_281 : location_info := LocationInfo file_0 438 153 438 157.
  Definition loc_282 : location_info := LocationInfo file_0 438 154 438 157.
  Definition loc_283 : location_info := LocationInfo file_0 438 161 438 176.
  Definition loc_284 : location_info := LocationInfo file_0 438 162 438 168.
  Definition loc_285 : location_info := LocationInfo file_0 438 162 438 164.
  Definition loc_286 : location_info := LocationInfo file_0 438 167 438 168.
  Definition loc_287 : location_info := LocationInfo file_0 438 171 438 175.
  Definition loc_288 : location_info := LocationInfo file_0 436 39 436 180.
  Definition loc_289 : location_info := LocationInfo file_0 436 40 436 106.
  Definition loc_290 : location_info := LocationInfo file_0 436 41 436 44.
  Definition loc_291 : location_info := LocationInfo file_0 436 41 436 44.
  Definition loc_292 : location_info := LocationInfo file_0 436 47 436 105.
  Definition loc_293 : location_info := LocationInfo file_0 436 48 436 76.
  Definition loc_294 : location_info := LocationInfo file_0 436 49 436 71.
  Definition loc_295 : location_info := LocationInfo file_0 436 49 436 55.
  Definition loc_296 : location_info := LocationInfo file_0 436 51 436 54.
  Definition loc_297 : location_info := LocationInfo file_0 436 58 436 71.
  Definition loc_298 : location_info := LocationInfo file_0 436 59 436 62.
  Definition loc_299 : location_info := LocationInfo file_0 436 66 436 70.
  Definition loc_300 : location_info := LocationInfo file_0 436 74 436 75.
  Definition loc_301 : location_info := LocationInfo file_0 436 79 436 104.
  Definition loc_302 : location_info := LocationInfo file_0 436 80 436 84.
  Definition loc_303 : location_info := LocationInfo file_0 436 81 436 84.
  Definition loc_304 : location_info := LocationInfo file_0 436 88 436 103.
  Definition loc_305 : location_info := LocationInfo file_0 436 89 436 95.
  Definition loc_306 : location_info := LocationInfo file_0 436 89 436 91.
  Definition loc_307 : location_info := LocationInfo file_0 436 94 436 95.
  Definition loc_308 : location_info := LocationInfo file_0 436 98 436 102.
  Definition loc_309 : location_info := LocationInfo file_0 436 109 436 179.
  Definition loc_310 : location_info := LocationInfo file_0 436 110 436 118.
  Definition loc_311 : location_info := LocationInfo file_0 436 110 436 118.
  Definition loc_312 : location_info := LocationInfo file_0 436 121 436 178.
  Definition loc_313 : location_info := LocationInfo file_0 436 122 436 149.
  Definition loc_314 : location_info := LocationInfo file_0 436 123 436 144.
  Definition loc_315 : location_info := LocationInfo file_0 436 123 436 129.
  Definition loc_316 : location_info := LocationInfo file_0 436 125 436 128.
  Definition loc_317 : location_info := LocationInfo file_0 436 132 436 144.
  Definition loc_318 : location_info := LocationInfo file_0 436 133 436 136.
  Definition loc_319 : location_info := LocationInfo file_0 436 140 436 143.
  Definition loc_320 : location_info := LocationInfo file_0 436 147 436 148.
  Definition loc_321 : location_info := LocationInfo file_0 436 152 436 177.
  Definition loc_322 : location_info := LocationInfo file_0 436 153 436 157.
  Definition loc_323 : location_info := LocationInfo file_0 436 154 436 157.
  Definition loc_324 : location_info := LocationInfo file_0 436 161 436 176.
  Definition loc_325 : location_info := LocationInfo file_0 436 162 436 168.
  Definition loc_326 : location_info := LocationInfo file_0 436 162 436 164.
  Definition loc_327 : location_info := LocationInfo file_0 436 167 436 168.
  Definition loc_328 : location_info := LocationInfo file_0 436 171 436 175.
  Definition loc_329 : location_info := LocationInfo file_0 434 39 434 54.
  Definition loc_330 : location_info := LocationInfo file_0 434 40 434 42.
  Definition loc_331 : location_info := LocationInfo file_0 434 41 434 42.
  Definition loc_332 : location_info := LocationInfo file_0 434 45 434 53.
  Definition loc_333 : location_info := LocationInfo file_0 434 45 434 53.
  Definition loc_334 : location_info := LocationInfo file_0 432 32 432 37.
  Definition loc_335 : location_info := LocationInfo file_0 432 32 432 37.
  Definition loc_336 : location_info := LocationInfo file_0 430 31 430 46.
  Definition loc_337 : location_info := LocationInfo file_0 430 32 430 34.
  Definition loc_338 : location_info := LocationInfo file_0 430 33 430 34.
  Definition loc_339 : location_info := LocationInfo file_0 430 37 430 45.
  Definition loc_340 : location_info := LocationInfo file_0 430 37 430 45.
  Definition loc_341 : location_info := LocationInfo file_0 427 24 427 86.
  Definition loc_342 : location_info := LocationInfo file_0 427 24 427 27.
  Definition loc_343 : location_info := LocationInfo file_0 427 24 427 27.
  Definition loc_344 : location_info := LocationInfo file_0 427 30 427 86.
  Definition loc_345 : location_info := LocationInfo file_0 427 31 427 58.
  Definition loc_346 : location_info := LocationInfo file_0 427 32 427 53.
  Definition loc_347 : location_info := LocationInfo file_0 427 32 427 38.
  Definition loc_348 : location_info := LocationInfo file_0 427 34 427 37.
  Definition loc_349 : location_info := LocationInfo file_0 427 41 427 53.
  Definition loc_350 : location_info := LocationInfo file_0 427 42 427 45.
  Definition loc_351 : location_info := LocationInfo file_0 427 49 427 52.
  Definition loc_352 : location_info := LocationInfo file_0 427 56 427 57.
  Definition loc_353 : location_info := LocationInfo file_0 427 61 427 85.
  Definition loc_354 : location_info := LocationInfo file_0 427 62 427 66.
  Definition loc_355 : location_info := LocationInfo file_0 427 63 427 66.
  Definition loc_356 : location_info := LocationInfo file_0 427 70 427 84.
  Definition loc_357 : location_info := LocationInfo file_0 427 71 427 77.
  Definition loc_358 : location_info := LocationInfo file_0 427 71 427 73.
  Definition loc_359 : location_info := LocationInfo file_0 427 76 427 77.
  Definition loc_360 : location_info := LocationInfo file_0 427 80 427 83.
  Definition loc_361 : location_info := LocationInfo file_0 412 88 420 17.
  Definition loc_362 : location_info := LocationInfo file_0 412 89 417 47.
  Definition loc_364 : location_info := LocationInfo file_0 413 23 417 47.
  Definition loc_366 : location_info := LocationInfo file_0 414 23 417 47.
  Definition loc_368 : location_info := LocationInfo file_0 417 24 417 47.
  Definition loc_369 : location_info := LocationInfo file_0 417 47 419 173.
  Definition loc_371 : location_info := LocationInfo file_0 419 24 419 173.
  Definition loc_372 : location_info := LocationInfo file_0 419 31 419 172.
  Definition loc_373 : location_info := LocationInfo file_0 419 32 419 98.
  Definition loc_374 : location_info := LocationInfo file_0 419 33 419 36.
  Definition loc_375 : location_info := LocationInfo file_0 419 33 419 36.
  Definition loc_376 : location_info := LocationInfo file_0 419 39 419 97.
  Definition loc_377 : location_info := LocationInfo file_0 419 40 419 68.
  Definition loc_378 : location_info := LocationInfo file_0 419 41 419 63.
  Definition loc_379 : location_info := LocationInfo file_0 419 41 419 47.
  Definition loc_380 : location_info := LocationInfo file_0 419 43 419 46.
  Definition loc_381 : location_info := LocationInfo file_0 419 50 419 63.
  Definition loc_382 : location_info := LocationInfo file_0 419 51 419 54.
  Definition loc_383 : location_info := LocationInfo file_0 419 58 419 62.
  Definition loc_384 : location_info := LocationInfo file_0 419 66 419 67.
  Definition loc_385 : location_info := LocationInfo file_0 419 71 419 96.
  Definition loc_386 : location_info := LocationInfo file_0 419 72 419 76.
  Definition loc_387 : location_info := LocationInfo file_0 419 73 419 76.
  Definition loc_388 : location_info := LocationInfo file_0 419 80 419 95.
  Definition loc_389 : location_info := LocationInfo file_0 419 81 419 87.
  Definition loc_390 : location_info := LocationInfo file_0 419 81 419 83.
  Definition loc_391 : location_info := LocationInfo file_0 419 86 419 87.
  Definition loc_392 : location_info := LocationInfo file_0 419 90 419 94.
  Definition loc_393 : location_info := LocationInfo file_0 419 101 419 171.
  Definition loc_394 : location_info := LocationInfo file_0 419 102 419 110.
  Definition loc_395 : location_info := LocationInfo file_0 419 102 419 110.
  Definition loc_396 : location_info := LocationInfo file_0 419 113 419 170.
  Definition loc_397 : location_info := LocationInfo file_0 419 114 419 141.
  Definition loc_398 : location_info := LocationInfo file_0 419 115 419 136.
  Definition loc_399 : location_info := LocationInfo file_0 419 115 419 121.
  Definition loc_400 : location_info := LocationInfo file_0 419 117 419 120.
  Definition loc_401 : location_info := LocationInfo file_0 419 124 419 136.
  Definition loc_402 : location_info := LocationInfo file_0 419 125 419 128.
  Definition loc_403 : location_info := LocationInfo file_0 419 132 419 135.
  Definition loc_404 : location_info := LocationInfo file_0 419 139 419 140.
  Definition loc_405 : location_info := LocationInfo file_0 419 144 419 169.
  Definition loc_406 : location_info := LocationInfo file_0 419 145 419 149.
  Definition loc_407 : location_info := LocationInfo file_0 419 146 419 149.
  Definition loc_408 : location_info := LocationInfo file_0 419 153 419 168.
  Definition loc_409 : location_info := LocationInfo file_0 419 154 419 160.
  Definition loc_410 : location_info := LocationInfo file_0 419 154 419 156.
  Definition loc_411 : location_info := LocationInfo file_0 419 159 419 160.
  Definition loc_412 : location_info := LocationInfo file_0 419 163 419 167.
  Definition loc_413 : location_info := LocationInfo file_0 417 31 417 46.
  Definition loc_414 : location_info := LocationInfo file_0 417 32 417 34.
  Definition loc_415 : location_info := LocationInfo file_0 417 33 417 34.
  Definition loc_416 : location_info := LocationInfo file_0 417 37 417 45.
  Definition loc_417 : location_info := LocationInfo file_0 417 37 417 45.
  Definition loc_418 : location_info := LocationInfo file_0 412 24 412 86.
  Definition loc_419 : location_info := LocationInfo file_0 412 24 412 27.
  Definition loc_420 : location_info := LocationInfo file_0 412 24 412 27.
  Definition loc_421 : location_info := LocationInfo file_0 412 30 412 86.
  Definition loc_422 : location_info := LocationInfo file_0 412 31 412 58.
  Definition loc_423 : location_info := LocationInfo file_0 412 32 412 53.
  Definition loc_424 : location_info := LocationInfo file_0 412 32 412 38.
  Definition loc_425 : location_info := LocationInfo file_0 412 34 412 37.
  Definition loc_426 : location_info := LocationInfo file_0 412 41 412 53.
  Definition loc_427 : location_info := LocationInfo file_0 412 42 412 45.
  Definition loc_428 : location_info := LocationInfo file_0 412 49 412 52.
  Definition loc_429 : location_info := LocationInfo file_0 412 56 412 57.
  Definition loc_430 : location_info := LocationInfo file_0 412 61 412 85.
  Definition loc_431 : location_info := LocationInfo file_0 412 62 412 66.
  Definition loc_432 : location_info := LocationInfo file_0 412 63 412 66.
  Definition loc_433 : location_info := LocationInfo file_0 412 70 412 84.
  Definition loc_434 : location_info := LocationInfo file_0 412 71 412 77.
  Definition loc_435 : location_info := LocationInfo file_0 412 71 412 73.
  Definition loc_436 : location_info := LocationInfo file_0 412 76 412 77.
  Definition loc_437 : location_info := LocationInfo file_0 412 80 412 83.
  Definition loc_438 : location_info := LocationInfo file_0 410 15 410 20.
  Definition loc_439 : location_info := LocationInfo file_0 410 15 410 20.
  Definition loc_440 : location_info := LocationInfo file_0 408 8 408 11.
  Definition loc_441 : location_info := LocationInfo file_0 408 14 408 59.
  Definition loc_442 : location_info := LocationInfo file_0 408 14 408 59.
  Definition loc_443 : location_info := LocationInfo file_0 408 15 408 59.
  Definition loc_444 : location_info := LocationInfo file_0 408 37 408 58.
  Definition loc_445 : location_info := LocationInfo file_0 408 38 408 48.
  Definition loc_446 : location_info := LocationInfo file_0 408 38 408 48.
  Definition loc_447 : location_info := LocationInfo file_0 408 51 408 57.
  Definition loc_448 : location_info := LocationInfo file_0 408 51 408 57.
  Definition loc_449 : location_info := LocationInfo file_0 399 23 405 9.
  Definition loc_450 : location_info := LocationInfo file_0 399 24 400 107.
  Definition loc_452 : location_info := LocationInfo file_0 400 16 400 107.
  Definition loc_453 : location_info := LocationInfo file_0 400 108 400 114.
  Definition loc_454 : location_info := LocationInfo file_0 400 114 401 107.
  Definition loc_456 : location_info := LocationInfo file_0 401 16 401 107.
  Definition loc_457 : location_info := LocationInfo file_0 401 108 401 114.
  Definition loc_458 : location_info := LocationInfo file_0 401 114 402 107.
  Definition loc_460 : location_info := LocationInfo file_0 402 16 402 107.
  Definition loc_461 : location_info := LocationInfo file_0 402 108 402 114.
  Definition loc_462 : location_info := LocationInfo file_0 402 114 403 107.
  Definition loc_464 : location_info := LocationInfo file_0 403 16 403 107.
  Definition loc_465 : location_info := LocationInfo file_0 403 108 403 114.
  Definition loc_466 : location_info := LocationInfo file_0 403 114 404 40.
  Definition loc_468 : location_info := LocationInfo file_0 404 17 404 40.
  Definition loc_469 : location_info := LocationInfo file_0 404 24 404 39.
  Definition loc_470 : location_info := LocationInfo file_0 404 25 404 27.
  Definition loc_471 : location_info := LocationInfo file_0 404 26 404 27.
  Definition loc_472 : location_info := LocationInfo file_0 404 30 404 38.
  Definition loc_473 : location_info := LocationInfo file_0 404 30 404 38.
  Definition loc_474 : location_info := LocationInfo file_0 403 16 403 22.
  Definition loc_475 : location_info := LocationInfo file_0 403 25 403 106.
  Definition loc_476 : location_info := LocationInfo file_0 403 25 403 96.
  Definition loc_477 : location_info := LocationInfo file_0 403 26 403 34.
  Definition loc_478 : location_info := LocationInfo file_0 403 26 403 34.
  Definition loc_479 : location_info := LocationInfo file_0 403 37 403 95.
  Definition loc_480 : location_info := LocationInfo file_0 403 38 403 66.
  Definition loc_481 : location_info := LocationInfo file_0 403 39 403 61.
  Definition loc_482 : location_info := LocationInfo file_0 403 39 403 45.
  Definition loc_483 : location_info := LocationInfo file_0 403 41 403 44.
  Definition loc_484 : location_info := LocationInfo file_0 403 48 403 61.
  Definition loc_485 : location_info := LocationInfo file_0 403 49 403 52.
  Definition loc_486 : location_info := LocationInfo file_0 403 56 403 60.
  Definition loc_487 : location_info := LocationInfo file_0 403 64 403 65.
  Definition loc_488 : location_info := LocationInfo file_0 403 69 403 94.
  Definition loc_489 : location_info := LocationInfo file_0 403 70 403 74.
  Definition loc_490 : location_info := LocationInfo file_0 403 71 403 74.
  Definition loc_491 : location_info := LocationInfo file_0 403 78 403 93.
  Definition loc_492 : location_info := LocationInfo file_0 403 79 403 85.
  Definition loc_493 : location_info := LocationInfo file_0 403 79 403 81.
  Definition loc_494 : location_info := LocationInfo file_0 403 84 403 85.
  Definition loc_495 : location_info := LocationInfo file_0 403 88 403 92.
  Definition loc_496 : location_info := LocationInfo file_0 403 100 403 106.
  Definition loc_497 : location_info := LocationInfo file_0 403 101 403 103.
  Definition loc_498 : location_info := LocationInfo file_0 403 104 403 105.
  Definition loc_499 : location_info := LocationInfo file_0 402 16 402 22.
  Definition loc_500 : location_info := LocationInfo file_0 402 25 402 106.
  Definition loc_501 : location_info := LocationInfo file_0 402 25 402 96.
  Definition loc_502 : location_info := LocationInfo file_0 402 26 402 34.
  Definition loc_503 : location_info := LocationInfo file_0 402 26 402 34.
  Definition loc_504 : location_info := LocationInfo file_0 402 37 402 95.
  Definition loc_505 : location_info := LocationInfo file_0 402 38 402 66.
  Definition loc_506 : location_info := LocationInfo file_0 402 39 402 61.
  Definition loc_507 : location_info := LocationInfo file_0 402 39 402 45.
  Definition loc_508 : location_info := LocationInfo file_0 402 41 402 44.
  Definition loc_509 : location_info := LocationInfo file_0 402 48 402 61.
  Definition loc_510 : location_info := LocationInfo file_0 402 49 402 52.
  Definition loc_511 : location_info := LocationInfo file_0 402 56 402 60.
  Definition loc_512 : location_info := LocationInfo file_0 402 64 402 65.
  Definition loc_513 : location_info := LocationInfo file_0 402 69 402 94.
  Definition loc_514 : location_info := LocationInfo file_0 402 70 402 74.
  Definition loc_515 : location_info := LocationInfo file_0 402 71 402 74.
  Definition loc_516 : location_info := LocationInfo file_0 402 78 402 93.
  Definition loc_517 : location_info := LocationInfo file_0 402 79 402 85.
  Definition loc_518 : location_info := LocationInfo file_0 402 79 402 81.
  Definition loc_519 : location_info := LocationInfo file_0 402 84 402 85.
  Definition loc_520 : location_info := LocationInfo file_0 402 88 402 92.
  Definition loc_521 : location_info := LocationInfo file_0 402 100 402 106.
  Definition loc_522 : location_info := LocationInfo file_0 402 101 402 103.
  Definition loc_523 : location_info := LocationInfo file_0 402 104 402 105.
  Definition loc_524 : location_info := LocationInfo file_0 401 16 401 22.
  Definition loc_525 : location_info := LocationInfo file_0 401 25 401 106.
  Definition loc_526 : location_info := LocationInfo file_0 401 25 401 96.
  Definition loc_527 : location_info := LocationInfo file_0 401 26 401 34.
  Definition loc_528 : location_info := LocationInfo file_0 401 26 401 34.
  Definition loc_529 : location_info := LocationInfo file_0 401 37 401 95.
  Definition loc_530 : location_info := LocationInfo file_0 401 38 401 66.
  Definition loc_531 : location_info := LocationInfo file_0 401 39 401 61.
  Definition loc_532 : location_info := LocationInfo file_0 401 39 401 45.
  Definition loc_533 : location_info := LocationInfo file_0 401 41 401 44.
  Definition loc_534 : location_info := LocationInfo file_0 401 48 401 61.
  Definition loc_535 : location_info := LocationInfo file_0 401 49 401 52.
  Definition loc_536 : location_info := LocationInfo file_0 401 56 401 60.
  Definition loc_537 : location_info := LocationInfo file_0 401 64 401 65.
  Definition loc_538 : location_info := LocationInfo file_0 401 69 401 94.
  Definition loc_539 : location_info := LocationInfo file_0 401 70 401 74.
  Definition loc_540 : location_info := LocationInfo file_0 401 71 401 74.
  Definition loc_541 : location_info := LocationInfo file_0 401 78 401 93.
  Definition loc_542 : location_info := LocationInfo file_0 401 79 401 85.
  Definition loc_543 : location_info := LocationInfo file_0 401 79 401 81.
  Definition loc_544 : location_info := LocationInfo file_0 401 84 401 85.
  Definition loc_545 : location_info := LocationInfo file_0 401 88 401 92.
  Definition loc_546 : location_info := LocationInfo file_0 401 100 401 106.
  Definition loc_547 : location_info := LocationInfo file_0 401 101 401 103.
  Definition loc_548 : location_info := LocationInfo file_0 401 104 401 105.
  Definition loc_549 : location_info := LocationInfo file_0 400 16 400 22.
  Definition loc_550 : location_info := LocationInfo file_0 400 25 400 106.
  Definition loc_551 : location_info := LocationInfo file_0 400 25 400 96.
  Definition loc_552 : location_info := LocationInfo file_0 400 26 400 34.
  Definition loc_553 : location_info := LocationInfo file_0 400 26 400 34.
  Definition loc_554 : location_info := LocationInfo file_0 400 37 400 95.
  Definition loc_555 : location_info := LocationInfo file_0 400 38 400 66.
  Definition loc_556 : location_info := LocationInfo file_0 400 39 400 61.
  Definition loc_557 : location_info := LocationInfo file_0 400 39 400 45.
  Definition loc_558 : location_info := LocationInfo file_0 400 41 400 44.
  Definition loc_559 : location_info := LocationInfo file_0 400 48 400 61.
  Definition loc_560 : location_info := LocationInfo file_0 400 49 400 52.
  Definition loc_561 : location_info := LocationInfo file_0 400 56 400 60.
  Definition loc_562 : location_info := LocationInfo file_0 400 64 400 65.
  Definition loc_563 : location_info := LocationInfo file_0 400 69 400 94.
  Definition loc_564 : location_info := LocationInfo file_0 400 70 400 74.
  Definition loc_565 : location_info := LocationInfo file_0 400 71 400 74.
  Definition loc_566 : location_info := LocationInfo file_0 400 78 400 93.
  Definition loc_567 : location_info := LocationInfo file_0 400 79 400 85.
  Definition loc_568 : location_info := LocationInfo file_0 400 79 400 81.
  Definition loc_569 : location_info := LocationInfo file_0 400 84 400 85.
  Definition loc_570 : location_info := LocationInfo file_0 400 88 400 92.
  Definition loc_571 : location_info := LocationInfo file_0 400 100 400 106.
  Definition loc_572 : location_info := LocationInfo file_0 400 101 400 103.
  Definition loc_573 : location_info := LocationInfo file_0 400 104 400 105.
  Definition loc_574 : location_info := LocationInfo file_0 399 16 399 21.
  Definition loc_575 : location_info := LocationInfo file_0 399 16 399 21.
  Definition loc_576 : location_info := LocationInfo file_0 398 36 398 37.
  Definition loc_581 : location_info := LocationInfo file_0 461 2 461 11.
  Definition loc_582 : location_info := LocationInfo file_0 462 2 462 12.
  Definition loc_583 : location_info := LocationInfo file_0 464 2 464 46.
  Definition loc_584 : location_info := LocationInfo file_0 468 2 468 11.
  Definition loc_585 : location_info := LocationInfo file_0 468 9 468 10.
  Definition loc_586 : location_info := LocationInfo file_0 464 23 464 45.
  Definition loc_587 : location_info := LocationInfo file_0 464 23 464 33.
  Definition loc_588 : location_info := LocationInfo file_0 464 23 464 33.
  Definition loc_589 : location_info := LocationInfo file_0 464 34 464 37.
  Definition loc_590 : location_info := LocationInfo file_0 464 34 464 37.
  Definition loc_591 : location_info := LocationInfo file_0 464 39 464 44.
  Definition loc_592 : location_info := LocationInfo file_0 464 39 464 44.
  Definition loc_595 : location_info := LocationInfo file_0 462 2 462 7.
  Definition loc_596 : location_info := LocationInfo file_0 462 10 462 11.
  Definition loc_597 : location_info := LocationInfo file_0 461 2 461 5.
  Definition loc_598 : location_info := LocationInfo file_0 461 8 461 10.

  (* Definition of struct [FaultRecord]. *)
  Program Definition struct_FaultRecord := {|
    sl_members := [
      (Some "statuscode", it_layout u32)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [FullAddress]. *)
  Program Definition struct_FullAddress := {|
    sl_members := [
      (Some "address", it_layout u64);
      (Some "NS", it_layout i32);
      (None, Layout 4%nat 0%nat)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [AddressDescriptor]. *)
  Program Definition struct_AddressDescriptor := {|
    sl_members := [
      (Some "fault", layout_of struct_FaultRecord);
      (None, Layout 4%nat 0%nat);
      (Some "paddress", layout_of struct_FullAddress);
      (Some "vaddress", it_layout u64)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of struct [TLBRecord]. *)
  Program Definition struct_TLBRecord := {|
    sl_members := [
      (Some "addrdesc", layout_of struct_AddressDescriptor)
    ];
  |}.
  Solve Obligations with solve_struct_obligations.

  (* Definition of function [entry_kind]. *)
  Definition impl_entry_kind : function := {|
    f_args := [
      ("pte", it_layout u64);
      ("level", it_layout u8)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_2 ;
        Switch u8
          (LocInfoE loc_107 (use{it_layout u8} (LocInfoE loc_108 ("level"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_6 ;
            Goto "#2") ::
            (locinfo: loc_8 ;
            Goto "#3") ::
            (locinfo: loc_10 ;
            Goto "#4") ::
            (locinfo: loc_14 ;
            Goto "#5") :: []
          )
          (locinfo: loc_17 ;
          Goto "#6")
      ]> $
      <[ "#1" :=
        locinfo: loc_3 ;
        Return (LocInfoE loc_4 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_4 (i2v 6 i32))))
      ]> $
      <[ "#11" :=
        locinfo: loc_24 ;
        Goto "#12"
      ]> $
      <[ "#12" :=
        locinfo: loc_26 ;
        Return (LocInfoE loc_35 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_35 (i2v 0 i32))))
      ]> $
      <[ "#13" :=
        locinfo: loc_29 ;
        Return (LocInfoE loc_34 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_34 (i2v 5 i32))))
      ]> $
      <[ "#14" :=
        locinfo: loc_32 ;
        Return (LocInfoE loc_33 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_33 (i2v 3 i32))))
      ]> $
      <[ "#15" :=
        locinfo: loc_17 ;
        Goto "#9"
      ]> $
      <[ "#17" :=
        locinfo: loc_59 ;
        Goto "#18"
      ]> $
      <[ "#18" :=
        locinfo: loc_61 ;
        Return (LocInfoE loc_86 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_86 (i2v 0 i32))))
      ]> $
      <[ "#19" :=
        locinfo: loc_64 ;
        Switch u8
          (LocInfoE loc_84 (use{it_layout u8} (LocInfoE loc_85 ("level"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> ∅
          )
          (
            (locinfo: loc_74 ;
            Goto "#25") ::
            (locinfo: loc_77 ;
            Goto "#26") ::
            (locinfo: loc_79 ;
            Goto "#27") :: []
          )
          (locinfo: loc_65 ;
          Goto "#22")
      ]> $
      <[ "#2" :=
        locinfo: loc_8 ;
        Goto "#3"
      ]> $
      <[ "#20" :=
        locinfo: loc_67 ;
        Return (LocInfoE loc_72 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_72 (i2v 2 i32))))
      ]> $
      <[ "#21" :=
        locinfo: loc_70 ;
        Return (LocInfoE loc_71 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_71 (i2v 6 i32))))
      ]> $
      <[ "#22" :=
        locinfo: loc_65 ;
        Goto "#20"
      ]> $
      <[ "#23" :=
        locinfo: loc_14 ;
        Goto "#7"
      ]> $
      <[ "#25" :=
        locinfo: loc_76 ;
        Return (LocInfoE loc_83 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_83 (i2v 4 i32))))
      ]> $
      <[ "#26" :=
        locinfo: loc_79 ;
        Goto "#27"
      ]> $
      <[ "#27" :=
        locinfo: loc_81 ;
        Return (LocInfoE loc_82 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_82 (i2v 1 i32))))
      ]> $
      <[ "#28" :=
        locinfo: loc_65 ;
        Goto "#22"
      ]> $
      <[ "#3" :=
        locinfo: loc_10 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_13 ;
        Switch u64
          (LocInfoE loc_87 ((LocInfoE loc_88 (use{it_layout u64} (LocInfoE loc_89 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_90 ((LocInfoE loc_91 ((LocInfoE loc_92 ((LocInfoE loc_93 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_94 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_95 ((LocInfoE loc_96 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_97 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_97 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_98 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_98 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_99 ((LocInfoE loc_100 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_101 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_102 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_102 ((LocInfoE loc_103 ((LocInfoE loc_104 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_105 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_106 (i2v 1 i32))))))))))))
          (
            <[ 0 := 0%nat ]> $
            <[ 2 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_57 ;
            Goto "#17") ::
            (locinfo: loc_59 ;
            Goto "#18") ::
            (locinfo: loc_62 ;
            Goto "#19") ::
            (locinfo: loc_65 ;
            Goto "#20") :: []
          )
          (locinfo: loc_68 ;
          Goto "#21")
      ]> $
      <[ "#5" :=
        locinfo: loc_16 ;
        Switch u64
          (LocInfoE loc_36 ((LocInfoE loc_37 (use{it_layout u64} (LocInfoE loc_38 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_39 ((LocInfoE loc_40 ((LocInfoE loc_41 ((LocInfoE loc_42 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_43 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_44 ((LocInfoE loc_45 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_46 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_46 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_47 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_47 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_48 ((LocInfoE loc_49 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_50 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_51 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_51 ((LocInfoE loc_52 ((LocInfoE loc_53 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_54 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_55 (i2v 1 i32))))))))))))
          (
            <[ 0 := 0%nat ]> $
            <[ 2 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_22 ;
            Goto "#11") ::
            (locinfo: loc_24 ;
            Goto "#12") ::
            (locinfo: loc_27 ;
            Goto "#13") ::
            (locinfo: loc_30 ;
            Goto "#14") :: []
          )
          (locinfo: loc_17 ;
          Goto "#9")
      ]> $
      <[ "#6" :=
        locinfo: loc_19 ;
        Return (LocInfoE loc_20 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_20 (i2v 6 i32))))
      ]> $
      <[ "#7" :=
        locinfo: loc_14 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        locinfo: loc_3 ;
        Goto "#1"
      ]> $
      <[ "#9" :=
        locinfo: loc_17 ;
        Goto "#6"
      ]> $∅
    )%E
  |}.

  (* Definition of function [mkFault]. *)
  Definition impl_mkFault : function := {|
    f_args := [
      ("vaddress", it_layout u64)
    ];
    f_local_vars := [
      ("result", layout_of struct_TLBRecord)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_111 ;
        LocInfoE loc_133 ((LocInfoE loc_134 ((LocInfoE loc_135 ((LocInfoE loc_136 ("result")) at{struct_TLBRecord} "addrdesc")) at{struct_AddressDescriptor} "fault")) at{struct_FaultRecord} "statuscode") <-{ it_layout u32 }
          LocInfoE loc_137 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_137 (i2v 6 i32))) ;
        locinfo: loc_112 ;
        LocInfoE loc_128 ((LocInfoE loc_129 ((LocInfoE loc_130 ((LocInfoE loc_131 ("result")) at{struct_TLBRecord} "addrdesc")) at{struct_AddressDescriptor} "paddress")) at{struct_FullAddress} "address") <-{ it_layout u64 }
          LocInfoE loc_132 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_132 (i2v 0 i32))) ;
        locinfo: loc_113 ;
        LocInfoE loc_123 ((LocInfoE loc_124 ((LocInfoE loc_125 ((LocInfoE loc_126 ("result")) at{struct_TLBRecord} "addrdesc")) at{struct_AddressDescriptor} "paddress")) at{struct_FullAddress} "NS") <-{ it_layout i32 }
          LocInfoE loc_127 (i2v 0 i32) ;
        locinfo: loc_114 ;
        LocInfoE loc_118 ((LocInfoE loc_119 ((LocInfoE loc_120 ("result")) at{struct_TLBRecord} "addrdesc")) at{struct_AddressDescriptor} "vaddress") <-{ it_layout u64 }
          LocInfoE loc_121 (use{it_layout u64} (LocInfoE loc_122 ("vaddress"))) ;
        locinfo: loc_115 ;
        Return (LocInfoE loc_116 (use{layout_of struct_TLBRecord} (LocInfoE loc_117 ("result"))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [hyp_phys_to_virt]. *)
  Definition impl_hyp_phys_to_virt (global_hyp_physvirt_offset : loc): function := {|
    f_args := [
      ("phys", it_layout i64)
    ];
    f_local_vars := [
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_140 ;
        Return (LocInfoE loc_141 (UnOp (CastOp $ PtrOp) (IntOp i64) (LocInfoE loc_142 ((LocInfoE loc_143 (UnOp (CastOp $ IntOp i64) (IntOp i64) (LocInfoE loc_144 (use{it_layout i64} (LocInfoE loc_145 ("phys")))))) -{IntOp i64, IntOp i64} (LocInfoE loc_146 (use{it_layout i64} (LocInfoE loc_147 (global_hyp_physvirt_offset))))))))
      ]> $∅
    )%E
  |}.

  (* Definition of function [AArch64_TranslationTableWalk]. *)
  Definition impl_AArch64_TranslationTableWalk (global_AArch64_TranslationTableWalk global_hyp_phys_to_virt : loc): function := {|
    f_args := [
      ("table_base", it_layout u64);
      ("level", it_layout u64);
      ("vaddress", it_layout u64)
    ];
    f_local_vars := [
      ("table_base_next_virt", it_layout u64);
      ("table_base_next_phys", it_layout u64);
      ("offset", it_layout u64);
      ("pte", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        "offset" <-{ it_layout u64 }
          LocInfoE loc_576 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_576 (i2v 0 i32))) ;
        locinfo: loc_151 ;
        Switch u64
          (LocInfoE loc_574 (use{it_layout u64} (LocInfoE loc_575 ("level"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_450 ;
            Goto "#31") ::
            (locinfo: loc_454 ;
            Goto "#32") ::
            (locinfo: loc_458 ;
            Goto "#33") ::
            (locinfo: loc_462 ;
            Goto "#34") :: []
          )
          (locinfo: loc_466 ;
          Goto "#35")
      ]> $
      <[ "#1" :=
        locinfo: loc_152 ;
        LocInfoE loc_440 ("pte") <-{ it_layout u64 }
          LocInfoE loc_441 (use{it_layout u64} (LocInfoE loc_443 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_444 ((LocInfoE loc_445 (!{it_layout u64} (LocInfoE loc_446 ("table_base")))) +{IntOp u64, IntOp u64} (LocInfoE loc_447 (use{it_layout u64} (LocInfoE loc_448 ("offset"))))))))) ;
        locinfo: loc_153 ;
        Switch u64
          (LocInfoE loc_438 (use{it_layout u64} (LocInfoE loc_439 ("level"))))
          (
            <[ 3 := 0%nat ]> $
            <[ 0 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 2 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_155 ;
            Goto "#3") ::
            (locinfo: loc_158 ;
            Goto "#4") ::
            (locinfo: loc_160 ;
            Goto "#5") ::
            (locinfo: loc_162 ;
            Goto "#7") :: []
          )
          (locinfo: loc_166 ;
          Goto "#8")
      ]> $
      <[ "#10" :=
        locinfo: loc_166 ;
        Goto "#8"
      ]> $
      <[ "#12" :=
        locinfo: loc_177 ;
        Goto "#13"
      ]> $
      <[ "#13" :=
        locinfo: loc_179 ;
        Return (LocInfoE loc_336 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_336 ((LocInfoE loc_337 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_337 (UnOp NegOp (IntOp i32) (LocInfoE loc_338 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_339 (use{it_layout u64} (LocInfoE loc_340 ("vaddress"))))))))
      ]> $
      <[ "#14" :=
        locinfo: loc_182 ;
        Switch u64
          (LocInfoE loc_334 (use{it_layout u64} (LocInfoE loc_335 ("level"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> ∅
          )
          (
            (locinfo: loc_238 ;
            Goto "#20") ::
            (locinfo: loc_241 ;
            Goto "#21") ::
            (locinfo: loc_244 ;
            Goto "#22") :: []
          )
          (locinfo: loc_183 ;
          Goto "#17")
      ]> $
      <[ "#15" :=
        locinfo: loc_186 ;
        LocInfoE loc_216 ("table_base_next_phys") <-{ it_layout u64 }
          LocInfoE loc_217 ((LocInfoE loc_218 (use{it_layout u64} (LocInfoE loc_219 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_220 ((LocInfoE loc_221 ((LocInfoE loc_222 ((LocInfoE loc_223 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_224 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_225 ((LocInfoE loc_226 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_227 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_227 (i2v 12 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_228 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_228 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_229 ((LocInfoE loc_230 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_231 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_232 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_232 ((LocInfoE loc_233 ((LocInfoE loc_234 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_235 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_236 (i2v 47 i32))))))))))) ;
        locinfo: loc_187 ;
        LocInfoE loc_208 ("table_base_next_virt") <-{ it_layout u64 }
          LocInfoE loc_209 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_210 (Call (LocInfoE loc_212 (global_hyp_phys_to_virt)) [@{expr} LocInfoE loc_213 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_214 (use{it_layout u64} (LocInfoE loc_215 ("table_base_next_phys"))))) ]))) ;
        locinfo: loc_188 ;
        Return (LocInfoE loc_197 (Call (LocInfoE loc_199 (global_AArch64_TranslationTableWalk)) [@{expr} LocInfoE loc_200 (use{it_layout u64} (LocInfoE loc_201 ("table_base_next_virt"))) ;
               LocInfoE loc_202 ((LocInfoE loc_203 (use{it_layout u64} (LocInfoE loc_204 ("level")))) +{IntOp u64, IntOp u64} (LocInfoE loc_205 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_205 (i2v 1 i32))))) ;
               LocInfoE loc_206 (use{it_layout u64} (LocInfoE loc_207 ("vaddress"))) ]))
      ]> $
      <[ "#16" :=
        locinfo: loc_191 ;
        Return (LocInfoE loc_192 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_192 ((LocInfoE loc_193 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_193 (UnOp NegOp (IntOp i32) (LocInfoE loc_194 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_195 (use{it_layout u64} (LocInfoE loc_196 ("vaddress"))))))))
      ]> $
      <[ "#17" :=
        locinfo: loc_183 ;
        Goto "#15"
      ]> $
      <[ "#18" :=
        locinfo: loc_166 ;
        Goto "#10"
      ]> $
      <[ "#2" :=
        Return (VOID)
      ]> $
      <[ "#20" :=
        locinfo: loc_240 ;
        Return (LocInfoE loc_329 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_329 ((LocInfoE loc_330 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_330 (UnOp NegOp (IntOp i32) (LocInfoE loc_331 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_332 (use{it_layout u64} (LocInfoE loc_333 ("vaddress"))))))))
      ]> $
      <[ "#21" :=
        locinfo: loc_243 ;
        Return (LocInfoE loc_288 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_288 ((LocInfoE loc_289 ((LocInfoE loc_290 (use{it_layout u64} (LocInfoE loc_291 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_292 ((LocInfoE loc_293 ((LocInfoE loc_294 ((LocInfoE loc_295 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_296 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_297 ((LocInfoE loc_298 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_299 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_299 (i2v 30 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_300 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_300 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_301 ((LocInfoE loc_302 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_303 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_304 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_304 ((LocInfoE loc_305 ((LocInfoE loc_306 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_307 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_308 (i2v 47 i32)))))))))))) |{IntOp u64, IntOp u64} (LocInfoE loc_309 ((LocInfoE loc_310 (use{it_layout u64} (LocInfoE loc_311 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_312 ((LocInfoE loc_313 ((LocInfoE loc_314 ((LocInfoE loc_315 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_316 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_317 ((LocInfoE loc_318 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_319 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_319 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_320 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_320 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_321 ((LocInfoE loc_322 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_323 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_324 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_324 ((LocInfoE loc_325 ((LocInfoE loc_326 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_327 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_328 (i2v 29 i32))))))))))))))))
      ]> $
      <[ "#22" :=
        locinfo: loc_246 ;
        Return (LocInfoE loc_247 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_247 ((LocInfoE loc_248 ((LocInfoE loc_249 (use{it_layout u64} (LocInfoE loc_250 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_251 ((LocInfoE loc_252 ((LocInfoE loc_253 ((LocInfoE loc_254 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_255 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_256 ((LocInfoE loc_257 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_258 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_258 (i2v 21 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_259 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_259 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_260 ((LocInfoE loc_261 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_262 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_263 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_263 ((LocInfoE loc_264 ((LocInfoE loc_265 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_266 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_267 (i2v 47 i32)))))))))))) |{IntOp u64, IntOp u64} (LocInfoE loc_268 ((LocInfoE loc_269 (use{it_layout u64} (LocInfoE loc_270 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_271 ((LocInfoE loc_272 ((LocInfoE loc_273 ((LocInfoE loc_274 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_275 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_276 ((LocInfoE loc_277 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_278 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_278 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_279 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_279 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_280 ((LocInfoE loc_281 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_282 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_283 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_283 ((LocInfoE loc_284 ((LocInfoE loc_285 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_286 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_287 (i2v 20 i32))))))))))))))))
      ]> $
      <[ "#23" :=
        locinfo: loc_183 ;
        Goto "#17"
      ]> $
      <[ "#25" :=
        locinfo: loc_364 ;
        Goto "#26"
      ]> $
      <[ "#26" :=
        locinfo: loc_366 ;
        Goto "#27"
      ]> $
      <[ "#27" :=
        locinfo: loc_368 ;
        Return (LocInfoE loc_413 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_413 ((LocInfoE loc_414 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_414 (UnOp NegOp (IntOp i32) (LocInfoE loc_415 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_416 (use{it_layout u64} (LocInfoE loc_417 ("vaddress"))))))))
      ]> $
      <[ "#28" :=
        locinfo: loc_371 ;
        Return (LocInfoE loc_372 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_372 ((LocInfoE loc_373 ((LocInfoE loc_374 (use{it_layout u64} (LocInfoE loc_375 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_376 ((LocInfoE loc_377 ((LocInfoE loc_378 ((LocInfoE loc_379 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_380 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_381 ((LocInfoE loc_382 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_383 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_383 (i2v 12 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_384 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_384 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_385 ((LocInfoE loc_386 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_387 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_388 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_388 ((LocInfoE loc_389 ((LocInfoE loc_390 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_391 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_392 (i2v 47 i32)))))))))))) |{IntOp u64, IntOp u64} (LocInfoE loc_393 ((LocInfoE loc_394 (use{it_layout u64} (LocInfoE loc_395 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_396 ((LocInfoE loc_397 ((LocInfoE loc_398 ((LocInfoE loc_399 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_400 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_401 ((LocInfoE loc_402 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_403 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_403 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_404 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_404 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_405 ((LocInfoE loc_406 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_407 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_408 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_408 ((LocInfoE loc_409 ((LocInfoE loc_410 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_411 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_412 (i2v 11 i32))))))))))))))))
      ]> $
      <[ "#29" :=
        locinfo: loc_158 ;
        Goto "#6"
      ]> $
      <[ "#3" :=
        locinfo: loc_157 ;
        Switch u64
          (LocInfoE loc_418 ((LocInfoE loc_419 (use{it_layout u64} (LocInfoE loc_420 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_421 ((LocInfoE loc_422 ((LocInfoE loc_423 ((LocInfoE loc_424 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_425 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_426 ((LocInfoE loc_427 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_428 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_428 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_429 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_429 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_430 ((LocInfoE loc_431 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_432 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_433 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_433 ((LocInfoE loc_434 ((LocInfoE loc_435 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_436 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_437 (i2v 1 i32))))))))))))
          (
            <[ 0 := 0%nat ]> $
            <[ 2 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_362 ;
            Goto "#25") ::
            (locinfo: loc_364 ;
            Goto "#26") ::
            (locinfo: loc_366 ;
            Goto "#27") ::
            (locinfo: loc_369 ;
            Goto "#28") :: []
          )
          (locinfo: loc_158 ;
          Goto "#6")
      ]> $
      <[ "#31" :=
        locinfo: loc_452 ;
        LocInfoE loc_549 ("offset") <-{ it_layout u64 }
          LocInfoE loc_550 ((LocInfoE loc_551 ((LocInfoE loc_552 (use{it_layout u64} (LocInfoE loc_553 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_554 ((LocInfoE loc_555 ((LocInfoE loc_556 ((LocInfoE loc_557 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_558 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_559 ((LocInfoE loc_560 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_561 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_561 (i2v 39 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_562 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_562 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_563 ((LocInfoE loc_564 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_565 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_566 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_566 ((LocInfoE loc_567 ((LocInfoE loc_568 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_569 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_570 (i2v 47 i32)))))))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_571 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_571 ((LocInfoE loc_572 (i2v 39 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_573 (i2v 3 i32))))))) ;
        locinfo: loc_152 ;
        Goto "#1"
      ]> $
      <[ "#32" :=
        locinfo: loc_456 ;
        LocInfoE loc_524 ("offset") <-{ it_layout u64 }
          LocInfoE loc_525 ((LocInfoE loc_526 ((LocInfoE loc_527 (use{it_layout u64} (LocInfoE loc_528 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_529 ((LocInfoE loc_530 ((LocInfoE loc_531 ((LocInfoE loc_532 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_533 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_534 ((LocInfoE loc_535 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_536 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_536 (i2v 30 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_537 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_537 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_538 ((LocInfoE loc_539 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_540 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_541 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_541 ((LocInfoE loc_542 ((LocInfoE loc_543 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_544 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_545 (i2v 38 i32)))))))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_546 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_546 ((LocInfoE loc_547 (i2v 30 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_548 (i2v 3 i32))))))) ;
        locinfo: loc_152 ;
        Goto "#1"
      ]> $
      <[ "#33" :=
        locinfo: loc_460 ;
        LocInfoE loc_499 ("offset") <-{ it_layout u64 }
          LocInfoE loc_500 ((LocInfoE loc_501 ((LocInfoE loc_502 (use{it_layout u64} (LocInfoE loc_503 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_504 ((LocInfoE loc_505 ((LocInfoE loc_506 ((LocInfoE loc_507 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_508 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_509 ((LocInfoE loc_510 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_511 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_511 (i2v 21 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_512 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_512 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_513 ((LocInfoE loc_514 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_515 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_516 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_516 ((LocInfoE loc_517 ((LocInfoE loc_518 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_519 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_520 (i2v 29 i32)))))))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_521 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_521 ((LocInfoE loc_522 (i2v 21 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_523 (i2v 3 i32))))))) ;
        locinfo: loc_152 ;
        Goto "#1"
      ]> $
      <[ "#34" :=
        locinfo: loc_464 ;
        LocInfoE loc_474 ("offset") <-{ it_layout u64 }
          LocInfoE loc_475 ((LocInfoE loc_476 ((LocInfoE loc_477 (use{it_layout u64} (LocInfoE loc_478 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_479 ((LocInfoE loc_480 ((LocInfoE loc_481 ((LocInfoE loc_482 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_483 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_484 ((LocInfoE loc_485 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_486 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_486 (i2v 12 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_487 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_487 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_488 ((LocInfoE loc_489 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_490 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_491 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_491 ((LocInfoE loc_492 ((LocInfoE loc_493 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_494 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_495 (i2v 20 i32)))))))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_496 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_496 ((LocInfoE loc_497 (i2v 12 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_498 (i2v 3 i32))))))) ;
        locinfo: loc_152 ;
        Goto "#1"
      ]> $
      <[ "#35" :=
        locinfo: loc_468 ;
        Return (LocInfoE loc_469 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_469 ((LocInfoE loc_470 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_470 (UnOp NegOp (IntOp i32) (LocInfoE loc_471 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_472 (use{it_layout u64} (LocInfoE loc_473 ("vaddress"))))))))
      ]> $
      <[ "#36" :=
        locinfo: loc_152 ;
        Goto "#1"
      ]> $
      <[ "#4" :=
        locinfo: loc_160 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_162 ;
        Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_158 ;
        Goto "#4"
      ]> $
      <[ "#7" :=
        locinfo: loc_165 ;
        Switch u64
          (LocInfoE loc_341 ((LocInfoE loc_342 (use{it_layout u64} (LocInfoE loc_343 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_344 ((LocInfoE loc_345 ((LocInfoE loc_346 ((LocInfoE loc_347 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_348 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_349 ((LocInfoE loc_350 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_351 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_351 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_352 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_352 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_353 ((LocInfoE loc_354 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_355 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_356 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_356 ((LocInfoE loc_357 ((LocInfoE loc_358 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_359 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_360 (i2v 1 i32))))))))))))
          (
            <[ 0 := 0%nat ]> $
            <[ 2 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_175 ;
            Goto "#12") ::
            (locinfo: loc_177 ;
            Goto "#13") ::
            (locinfo: loc_180 ;
            Goto "#14") ::
            (locinfo: loc_183 ;
            Goto "#15") :: []
          )
          (locinfo: loc_189 ;
          Goto "#16")
      ]> $
      <[ "#8" :=
        locinfo: loc_168 ;
        Return (LocInfoE loc_169 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_169 ((LocInfoE loc_170 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_170 (UnOp NegOp (IntOp i32) (LocInfoE loc_171 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_172 (use{it_layout u64} (LocInfoE loc_173 ("vaddress"))))))))
      ]> $
      <[ "#9" :=
        Goto "#2"
      ]> $∅
    )%E
  |}.

  (* Definition of function [main]. *)
  Definition impl_main (global_entry_kind : loc): function := {|
    f_args := [
    ];
    f_local_vars := [
      ("ek", it_layout u32);
      ("level", it_layout u8);
      ("pte", it_layout u64)
    ];
    f_init := "#0";
    f_code := (
      <[ "#0" :=
        locinfo: loc_581 ;
        LocInfoE loc_597 ("pte") <-{ it_layout u64 }
          LocInfoE loc_598 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_598 (i2v 10 i32))) ;
        locinfo: loc_582 ;
        LocInfoE loc_595 ("level") <-{ it_layout u8 }
          LocInfoE loc_596 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_596 (i2v 3 i32))) ;
        "ek" <-{ it_layout u32 }
          LocInfoE loc_586 (Call (LocInfoE loc_588 (global_entry_kind)) [@{expr} LocInfoE loc_589 (use{it_layout u64} (LocInfoE loc_590 ("pte"))) ;
          LocInfoE loc_591 (use{it_layout u8} (LocInfoE loc_592 ("level"))) ]) ;
        locinfo: loc_584 ;
        Return (LocInfoE loc_585 (i2v 0 i32))
      ]> $∅
    )%E
  |}.
End code.
