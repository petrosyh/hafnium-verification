From refinedc.lang Require Export notation.
From refinedc.lang Require Import tactics.
From refinedc.typing Require Import annotations.
Set Default Proof Using "Type".

(* Generated from [src/check_pkvm_pgtables.c]. *)
Section code.
  Definition file_0 : string := "src/check_pkvm_pgtables.c".
  Definition loc_2 : location_info := LocationInfo file_0 201 8 238 9.
  Definition loc_3 : location_info := LocationInfo file_0 201 22 238 9.
  Definition loc_4 : location_info := LocationInfo file_0 201 23 224 9.
  Definition loc_6 : location_info := LocationInfo file_0 202 15 224 9.
  Definition loc_8 : location_info := LocationInfo file_0 203 15 224 9.
  Definition loc_10 : location_info := LocationInfo file_0 205 8 224 9.
  Definition loc_11 : location_info := LocationInfo file_0 206 16 223 17.
  Definition loc_12 : location_info := LocationInfo file_0 224 9 234 17.
  Definition loc_14 : location_info := LocationInfo file_0 226 16 234 17.
  Definition loc_15 : location_info := LocationInfo file_0 234 17 237 32.
  Definition loc_17 : location_info := LocationInfo file_0 237 16 237 32.
  Definition loc_18 : location_info := LocationInfo file_0 237 23 237 31.
  Definition loc_19 : location_info := LocationInfo file_0 226 88 234 17.
  Definition loc_20 : location_info := LocationInfo file_0 226 89 229 42.
  Definition loc_22 : location_info := LocationInfo file_0 227 23 229 42.
  Definition loc_24 : location_info := LocationInfo file_0 229 24 229 42.
  Definition loc_25 : location_info := LocationInfo file_0 229 42 231 43.
  Definition loc_27 : location_info := LocationInfo file_0 231 24 231 43.
  Definition loc_28 : location_info := LocationInfo file_0 231 43 233 50.
  Definition loc_30 : location_info := LocationInfo file_0 233 24 233 50.
  Definition loc_31 : location_info := LocationInfo file_0 233 31 233 49.
  Definition loc_32 : location_info := LocationInfo file_0 231 31 231 42.
  Definition loc_33 : location_info := LocationInfo file_0 229 31 229 41.
  Definition loc_34 : location_info := LocationInfo file_0 226 24 226 86.
  Definition loc_35 : location_info := LocationInfo file_0 226 24 226 27.
  Definition loc_36 : location_info := LocationInfo file_0 226 24 226 27.
  Definition loc_37 : location_info := LocationInfo file_0 226 30 226 86.
  Definition loc_38 : location_info := LocationInfo file_0 226 31 226 58.
  Definition loc_39 : location_info := LocationInfo file_0 226 32 226 53.
  Definition loc_40 : location_info := LocationInfo file_0 226 32 226 38.
  Definition loc_41 : location_info := LocationInfo file_0 226 34 226 37.
  Definition loc_42 : location_info := LocationInfo file_0 226 41 226 53.
  Definition loc_43 : location_info := LocationInfo file_0 226 42 226 45.
  Definition loc_44 : location_info := LocationInfo file_0 226 49 226 52.
  Definition loc_45 : location_info := LocationInfo file_0 226 56 226 57.
  Definition loc_46 : location_info := LocationInfo file_0 226 61 226 85.
  Definition loc_47 : location_info := LocationInfo file_0 226 62 226 66.
  Definition loc_48 : location_info := LocationInfo file_0 226 63 226 66.
  Definition loc_49 : location_info := LocationInfo file_0 226 70 226 84.
  Definition loc_50 : location_info := LocationInfo file_0 226 71 226 77.
  Definition loc_51 : location_info := LocationInfo file_0 226 71 226 73.
  Definition loc_52 : location_info := LocationInfo file_0 226 76 226 77.
  Definition loc_53 : location_info := LocationInfo file_0 226 80 226 83.
  Definition loc_54 : location_info := LocationInfo file_0 206 88 223 17.
  Definition loc_55 : location_info := LocationInfo file_0 206 89 209 42.
  Definition loc_57 : location_info := LocationInfo file_0 207 23 209 42.
  Definition loc_59 : location_info := LocationInfo file_0 209 24 209 42.
  Definition loc_60 : location_info := LocationInfo file_0 209 42 218 25.
  Definition loc_62 : location_info := LocationInfo file_0 211 24 218 25.
  Definition loc_63 : location_info := LocationInfo file_0 218 25 220 40.
  Definition loc_65 : location_info := LocationInfo file_0 220 24 220 40.
  Definition loc_66 : location_info := LocationInfo file_0 220 40 222 40.
  Definition loc_68 : location_info := LocationInfo file_0 222 24 222 40.
  Definition loc_69 : location_info := LocationInfo file_0 222 31 222 39.
  Definition loc_70 : location_info := LocationInfo file_0 220 31 220 39.
  Definition loc_71 : location_info := LocationInfo file_0 212 24 218 25.
  Definition loc_72 : location_info := LocationInfo file_0 212 25 214 62.
  Definition loc_74 : location_info := LocationInfo file_0 214 32 214 62.
  Definition loc_75 : location_info := LocationInfo file_0 214 62 217 48.
  Definition loc_77 : location_info := LocationInfo file_0 215 31 217 48.
  Definition loc_79 : location_info := LocationInfo file_0 217 32 217 48.
  Definition loc_80 : location_info := LocationInfo file_0 217 39 217 47.
  Definition loc_81 : location_info := LocationInfo file_0 214 39 214 61.
  Definition loc_82 : location_info := LocationInfo file_0 211 32 211 37.
  Definition loc_83 : location_info := LocationInfo file_0 211 32 211 37.
  Definition loc_84 : location_info := LocationInfo file_0 209 31 209 41.
  Definition loc_85 : location_info := LocationInfo file_0 206 24 206 86.
  Definition loc_86 : location_info := LocationInfo file_0 206 24 206 27.
  Definition loc_87 : location_info := LocationInfo file_0 206 24 206 27.
  Definition loc_88 : location_info := LocationInfo file_0 206 30 206 86.
  Definition loc_89 : location_info := LocationInfo file_0 206 31 206 58.
  Definition loc_90 : location_info := LocationInfo file_0 206 32 206 53.
  Definition loc_91 : location_info := LocationInfo file_0 206 32 206 38.
  Definition loc_92 : location_info := LocationInfo file_0 206 34 206 37.
  Definition loc_93 : location_info := LocationInfo file_0 206 41 206 53.
  Definition loc_94 : location_info := LocationInfo file_0 206 42 206 45.
  Definition loc_95 : location_info := LocationInfo file_0 206 49 206 52.
  Definition loc_96 : location_info := LocationInfo file_0 206 56 206 57.
  Definition loc_97 : location_info := LocationInfo file_0 206 61 206 85.
  Definition loc_98 : location_info := LocationInfo file_0 206 62 206 66.
  Definition loc_99 : location_info := LocationInfo file_0 206 63 206 66.
  Definition loc_100 : location_info := LocationInfo file_0 206 70 206 84.
  Definition loc_101 : location_info := LocationInfo file_0 206 71 206 77.
  Definition loc_102 : location_info := LocationInfo file_0 206 71 206 73.
  Definition loc_103 : location_info := LocationInfo file_0 206 76 206 77.
  Definition loc_104 : location_info := LocationInfo file_0 206 80 206 83.
  Definition loc_105 : location_info := LocationInfo file_0 201 15 201 20.
  Definition loc_106 : location_info := LocationInfo file_0 201 15 201 20.
  Definition loc_109 : location_info := LocationInfo file_0 326 8 326 69.
  Definition loc_110 : location_info := LocationInfo file_0 326 15 326 68.
  Definition loc_111 : location_info := LocationInfo file_0 326 24 326 67.
  Definition loc_112 : location_info := LocationInfo file_0 326 25 326 44.
  Definition loc_113 : location_info := LocationInfo file_0 326 38 326 44.
  Definition loc_114 : location_info := LocationInfo file_0 326 38 326 44.
  Definition loc_115 : location_info := LocationInfo file_0 326 47 326 66.
  Definition loc_116 : location_info := LocationInfo file_0 326 47 326 66.
  Definition loc_119 : location_info := LocationInfo file_0 339 8 339 38.
  Definition loc_120 : location_info := LocationInfo file_0 340 8 346 9.
  Definition loc_121 : location_info := LocationInfo file_0 349 8 349 60.
  Definition loc_122 : location_info := LocationInfo file_0 351 8 394 9.
  Definition loc_123 : location_info := LocationInfo file_0 351 22 394 9.
  Definition loc_124 : location_info := LocationInfo file_0 351 23 361 17.
  Definition loc_126 : location_info := LocationInfo file_0 353 16 361 17.
  Definition loc_127 : location_info := LocationInfo file_0 361 17 392 9.
  Definition loc_129 : location_info := LocationInfo file_0 363 15 392 9.
  Definition loc_131 : location_info := LocationInfo file_0 364 15 392 9.
  Definition loc_133 : location_info := LocationInfo file_0 367 8 392 9.
  Definition loc_134 : location_info := LocationInfo file_0 368 16 391 17.
  Definition loc_135 : location_info := LocationInfo file_0 392 9 393 40.
  Definition loc_137 : location_info := LocationInfo file_0 393 17 393 40.
  Definition loc_138 : location_info := LocationInfo file_0 393 24 393 39.
  Definition loc_139 : location_info := LocationInfo file_0 393 25 393 27.
  Definition loc_140 : location_info := LocationInfo file_0 393 26 393 27.
  Definition loc_141 : location_info := LocationInfo file_0 393 30 393 38.
  Definition loc_142 : location_info := LocationInfo file_0 393 30 393 38.
  Definition loc_143 : location_info := LocationInfo file_0 368 88 391 17.
  Definition loc_144 : location_info := LocationInfo file_0 368 89 371 47.
  Definition loc_146 : location_info := LocationInfo file_0 369 23 371 47.
  Definition loc_148 : location_info := LocationInfo file_0 371 24 371 47.
  Definition loc_149 : location_info := LocationInfo file_0 371 47 380 25.
  Definition loc_151 : location_info := LocationInfo file_0 373 24 380 25.
  Definition loc_152 : location_info := LocationInfo file_0 380 25 389 17.
  Definition loc_154 : location_info := LocationInfo file_0 382 16 389 17.
  Definition loc_155 : location_info := LocationInfo file_0 383 24 383 112.
  Definition loc_156 : location_info := LocationInfo file_0 384 24 386 64.
  Definition loc_157 : location_info := LocationInfo file_0 388 24 388 101.
  Definition loc_158 : location_info := LocationInfo file_0 389 17 390 48.
  Definition loc_160 : location_info := LocationInfo file_0 390 25 390 48.
  Definition loc_161 : location_info := LocationInfo file_0 390 32 390 47.
  Definition loc_162 : location_info := LocationInfo file_0 390 33 390 35.
  Definition loc_163 : location_info := LocationInfo file_0 390 34 390 35.
  Definition loc_164 : location_info := LocationInfo file_0 390 38 390 46.
  Definition loc_165 : location_info := LocationInfo file_0 390 38 390 46.
  Definition loc_166 : location_info := LocationInfo file_0 388 31 388 100.
  Definition loc_167 : location_info := LocationInfo file_0 388 31 388 59.
  Definition loc_168 : location_info := LocationInfo file_0 388 31 388 59.
  Definition loc_169 : location_info := LocationInfo file_0 388 60 388 80.
  Definition loc_170 : location_info := LocationInfo file_0 388 60 388 80.
  Definition loc_171 : location_info := LocationInfo file_0 388 82 388 89.
  Definition loc_172 : location_info := LocationInfo file_0 388 82 388 87.
  Definition loc_173 : location_info := LocationInfo file_0 388 82 388 87.
  Definition loc_174 : location_info := LocationInfo file_0 388 88 388 89.
  Definition loc_175 : location_info := LocationInfo file_0 388 91 388 99.
  Definition loc_176 : location_info := LocationInfo file_0 388 91 388 99.
  Definition loc_177 : location_info := LocationInfo file_0 384 24 384 44.
  Definition loc_178 : location_info := LocationInfo file_0 385 28 386 63.
  Definition loc_179 : location_info := LocationInfo file_0 385 48 386 63.
  Definition loc_180 : location_info := LocationInfo file_0 385 48 385 64.
  Definition loc_181 : location_info := LocationInfo file_0 385 48 385 64.
  Definition loc_182 : location_info := LocationInfo file_0 386 29 386 62.
  Definition loc_183 : location_info := LocationInfo file_0 386 42 386 62.
  Definition loc_184 : location_info := LocationInfo file_0 386 42 386 62.
  Definition loc_185 : location_info := LocationInfo file_0 383 24 383 44.
  Definition loc_186 : location_info := LocationInfo file_0 383 47 383 111.
  Definition loc_187 : location_info := LocationInfo file_0 383 47 383 50.
  Definition loc_188 : location_info := LocationInfo file_0 383 47 383 50.
  Definition loc_189 : location_info := LocationInfo file_0 383 53 383 111.
  Definition loc_190 : location_info := LocationInfo file_0 383 54 383 82.
  Definition loc_191 : location_info := LocationInfo file_0 383 55 383 77.
  Definition loc_192 : location_info := LocationInfo file_0 383 55 383 61.
  Definition loc_193 : location_info := LocationInfo file_0 383 57 383 60.
  Definition loc_194 : location_info := LocationInfo file_0 383 64 383 77.
  Definition loc_195 : location_info := LocationInfo file_0 383 65 383 68.
  Definition loc_196 : location_info := LocationInfo file_0 383 72 383 76.
  Definition loc_197 : location_info := LocationInfo file_0 383 80 383 81.
  Definition loc_198 : location_info := LocationInfo file_0 383 85 383 110.
  Definition loc_199 : location_info := LocationInfo file_0 383 86 383 90.
  Definition loc_200 : location_info := LocationInfo file_0 383 87 383 90.
  Definition loc_201 : location_info := LocationInfo file_0 383 94 383 109.
  Definition loc_202 : location_info := LocationInfo file_0 383 95 383 101.
  Definition loc_203 : location_info := LocationInfo file_0 383 95 383 97.
  Definition loc_204 : location_info := LocationInfo file_0 383 100 383 101.
  Definition loc_205 : location_info := LocationInfo file_0 383 104 383 108.
  Definition loc_206 : location_info := LocationInfo file_0 373 39 380 25.
  Definition loc_207 : location_info := LocationInfo file_0 373 40 375 55.
  Definition loc_209 : location_info := LocationInfo file_0 375 32 375 55.
  Definition loc_210 : location_info := LocationInfo file_0 375 55 377 181.
  Definition loc_212 : location_info := LocationInfo file_0 377 32 377 181.
  Definition loc_213 : location_info := LocationInfo file_0 377 181 379 181.
  Definition loc_215 : location_info := LocationInfo file_0 379 32 379 181.
  Definition loc_216 : location_info := LocationInfo file_0 379 39 379 180.
  Definition loc_217 : location_info := LocationInfo file_0 379 40 379 106.
  Definition loc_218 : location_info := LocationInfo file_0 379 41 379 44.
  Definition loc_219 : location_info := LocationInfo file_0 379 41 379 44.
  Definition loc_220 : location_info := LocationInfo file_0 379 47 379 105.
  Definition loc_221 : location_info := LocationInfo file_0 379 48 379 76.
  Definition loc_222 : location_info := LocationInfo file_0 379 49 379 71.
  Definition loc_223 : location_info := LocationInfo file_0 379 49 379 55.
  Definition loc_224 : location_info := LocationInfo file_0 379 51 379 54.
  Definition loc_225 : location_info := LocationInfo file_0 379 58 379 71.
  Definition loc_226 : location_info := LocationInfo file_0 379 59 379 62.
  Definition loc_227 : location_info := LocationInfo file_0 379 66 379 70.
  Definition loc_228 : location_info := LocationInfo file_0 379 74 379 75.
  Definition loc_229 : location_info := LocationInfo file_0 379 79 379 104.
  Definition loc_230 : location_info := LocationInfo file_0 379 80 379 84.
  Definition loc_231 : location_info := LocationInfo file_0 379 81 379 84.
  Definition loc_232 : location_info := LocationInfo file_0 379 88 379 103.
  Definition loc_233 : location_info := LocationInfo file_0 379 89 379 95.
  Definition loc_234 : location_info := LocationInfo file_0 379 89 379 91.
  Definition loc_235 : location_info := LocationInfo file_0 379 94 379 95.
  Definition loc_236 : location_info := LocationInfo file_0 379 98 379 102.
  Definition loc_237 : location_info := LocationInfo file_0 379 109 379 179.
  Definition loc_238 : location_info := LocationInfo file_0 379 110 379 118.
  Definition loc_239 : location_info := LocationInfo file_0 379 110 379 118.
  Definition loc_240 : location_info := LocationInfo file_0 379 121 379 178.
  Definition loc_241 : location_info := LocationInfo file_0 379 122 379 149.
  Definition loc_242 : location_info := LocationInfo file_0 379 123 379 144.
  Definition loc_243 : location_info := LocationInfo file_0 379 123 379 129.
  Definition loc_244 : location_info := LocationInfo file_0 379 125 379 128.
  Definition loc_245 : location_info := LocationInfo file_0 379 132 379 144.
  Definition loc_246 : location_info := LocationInfo file_0 379 133 379 136.
  Definition loc_247 : location_info := LocationInfo file_0 379 140 379 143.
  Definition loc_248 : location_info := LocationInfo file_0 379 147 379 148.
  Definition loc_249 : location_info := LocationInfo file_0 379 152 379 177.
  Definition loc_250 : location_info := LocationInfo file_0 379 153 379 157.
  Definition loc_251 : location_info := LocationInfo file_0 379 154 379 157.
  Definition loc_252 : location_info := LocationInfo file_0 379 161 379 176.
  Definition loc_253 : location_info := LocationInfo file_0 379 162 379 168.
  Definition loc_254 : location_info := LocationInfo file_0 379 162 379 164.
  Definition loc_255 : location_info := LocationInfo file_0 379 167 379 168.
  Definition loc_256 : location_info := LocationInfo file_0 379 171 379 175.
  Definition loc_257 : location_info := LocationInfo file_0 377 39 377 180.
  Definition loc_258 : location_info := LocationInfo file_0 377 40 377 106.
  Definition loc_259 : location_info := LocationInfo file_0 377 41 377 44.
  Definition loc_260 : location_info := LocationInfo file_0 377 41 377 44.
  Definition loc_261 : location_info := LocationInfo file_0 377 47 377 105.
  Definition loc_262 : location_info := LocationInfo file_0 377 48 377 76.
  Definition loc_263 : location_info := LocationInfo file_0 377 49 377 71.
  Definition loc_264 : location_info := LocationInfo file_0 377 49 377 55.
  Definition loc_265 : location_info := LocationInfo file_0 377 51 377 54.
  Definition loc_266 : location_info := LocationInfo file_0 377 58 377 71.
  Definition loc_267 : location_info := LocationInfo file_0 377 59 377 62.
  Definition loc_268 : location_info := LocationInfo file_0 377 66 377 70.
  Definition loc_269 : location_info := LocationInfo file_0 377 74 377 75.
  Definition loc_270 : location_info := LocationInfo file_0 377 79 377 104.
  Definition loc_271 : location_info := LocationInfo file_0 377 80 377 84.
  Definition loc_272 : location_info := LocationInfo file_0 377 81 377 84.
  Definition loc_273 : location_info := LocationInfo file_0 377 88 377 103.
  Definition loc_274 : location_info := LocationInfo file_0 377 89 377 95.
  Definition loc_275 : location_info := LocationInfo file_0 377 89 377 91.
  Definition loc_276 : location_info := LocationInfo file_0 377 94 377 95.
  Definition loc_277 : location_info := LocationInfo file_0 377 98 377 102.
  Definition loc_278 : location_info := LocationInfo file_0 377 109 377 179.
  Definition loc_279 : location_info := LocationInfo file_0 377 110 377 118.
  Definition loc_280 : location_info := LocationInfo file_0 377 110 377 118.
  Definition loc_281 : location_info := LocationInfo file_0 377 121 377 178.
  Definition loc_282 : location_info := LocationInfo file_0 377 122 377 149.
  Definition loc_283 : location_info := LocationInfo file_0 377 123 377 144.
  Definition loc_284 : location_info := LocationInfo file_0 377 123 377 129.
  Definition loc_285 : location_info := LocationInfo file_0 377 125 377 128.
  Definition loc_286 : location_info := LocationInfo file_0 377 132 377 144.
  Definition loc_287 : location_info := LocationInfo file_0 377 133 377 136.
  Definition loc_288 : location_info := LocationInfo file_0 377 140 377 143.
  Definition loc_289 : location_info := LocationInfo file_0 377 147 377 148.
  Definition loc_290 : location_info := LocationInfo file_0 377 152 377 177.
  Definition loc_291 : location_info := LocationInfo file_0 377 153 377 157.
  Definition loc_292 : location_info := LocationInfo file_0 377 154 377 157.
  Definition loc_293 : location_info := LocationInfo file_0 377 161 377 176.
  Definition loc_294 : location_info := LocationInfo file_0 377 162 377 168.
  Definition loc_295 : location_info := LocationInfo file_0 377 162 377 164.
  Definition loc_296 : location_info := LocationInfo file_0 377 167 377 168.
  Definition loc_297 : location_info := LocationInfo file_0 377 171 377 175.
  Definition loc_298 : location_info := LocationInfo file_0 375 39 375 54.
  Definition loc_299 : location_info := LocationInfo file_0 375 40 375 42.
  Definition loc_300 : location_info := LocationInfo file_0 375 41 375 42.
  Definition loc_301 : location_info := LocationInfo file_0 375 45 375 53.
  Definition loc_302 : location_info := LocationInfo file_0 375 45 375 53.
  Definition loc_303 : location_info := LocationInfo file_0 373 32 373 37.
  Definition loc_304 : location_info := LocationInfo file_0 373 32 373 37.
  Definition loc_305 : location_info := LocationInfo file_0 371 31 371 46.
  Definition loc_306 : location_info := LocationInfo file_0 371 32 371 34.
  Definition loc_307 : location_info := LocationInfo file_0 371 33 371 34.
  Definition loc_308 : location_info := LocationInfo file_0 371 37 371 45.
  Definition loc_309 : location_info := LocationInfo file_0 371 37 371 45.
  Definition loc_310 : location_info := LocationInfo file_0 368 24 368 86.
  Definition loc_311 : location_info := LocationInfo file_0 368 24 368 27.
  Definition loc_312 : location_info := LocationInfo file_0 368 24 368 27.
  Definition loc_313 : location_info := LocationInfo file_0 368 30 368 86.
  Definition loc_314 : location_info := LocationInfo file_0 368 31 368 58.
  Definition loc_315 : location_info := LocationInfo file_0 368 32 368 53.
  Definition loc_316 : location_info := LocationInfo file_0 368 32 368 38.
  Definition loc_317 : location_info := LocationInfo file_0 368 34 368 37.
  Definition loc_318 : location_info := LocationInfo file_0 368 41 368 53.
  Definition loc_319 : location_info := LocationInfo file_0 368 42 368 45.
  Definition loc_320 : location_info := LocationInfo file_0 368 49 368 52.
  Definition loc_321 : location_info := LocationInfo file_0 368 56 368 57.
  Definition loc_322 : location_info := LocationInfo file_0 368 61 368 85.
  Definition loc_323 : location_info := LocationInfo file_0 368 62 368 66.
  Definition loc_324 : location_info := LocationInfo file_0 368 63 368 66.
  Definition loc_325 : location_info := LocationInfo file_0 368 70 368 84.
  Definition loc_326 : location_info := LocationInfo file_0 368 71 368 77.
  Definition loc_327 : location_info := LocationInfo file_0 368 71 368 73.
  Definition loc_328 : location_info := LocationInfo file_0 368 76 368 77.
  Definition loc_329 : location_info := LocationInfo file_0 368 80 368 83.
  Definition loc_330 : location_info := LocationInfo file_0 353 88 361 17.
  Definition loc_331 : location_info := LocationInfo file_0 353 89 358 47.
  Definition loc_333 : location_info := LocationInfo file_0 354 23 358 47.
  Definition loc_335 : location_info := LocationInfo file_0 355 23 358 47.
  Definition loc_337 : location_info := LocationInfo file_0 358 24 358 47.
  Definition loc_338 : location_info := LocationInfo file_0 358 47 360 173.
  Definition loc_340 : location_info := LocationInfo file_0 360 24 360 173.
  Definition loc_341 : location_info := LocationInfo file_0 360 31 360 172.
  Definition loc_342 : location_info := LocationInfo file_0 360 32 360 98.
  Definition loc_343 : location_info := LocationInfo file_0 360 33 360 36.
  Definition loc_344 : location_info := LocationInfo file_0 360 33 360 36.
  Definition loc_345 : location_info := LocationInfo file_0 360 39 360 97.
  Definition loc_346 : location_info := LocationInfo file_0 360 40 360 68.
  Definition loc_347 : location_info := LocationInfo file_0 360 41 360 63.
  Definition loc_348 : location_info := LocationInfo file_0 360 41 360 47.
  Definition loc_349 : location_info := LocationInfo file_0 360 43 360 46.
  Definition loc_350 : location_info := LocationInfo file_0 360 50 360 63.
  Definition loc_351 : location_info := LocationInfo file_0 360 51 360 54.
  Definition loc_352 : location_info := LocationInfo file_0 360 58 360 62.
  Definition loc_353 : location_info := LocationInfo file_0 360 66 360 67.
  Definition loc_354 : location_info := LocationInfo file_0 360 71 360 96.
  Definition loc_355 : location_info := LocationInfo file_0 360 72 360 76.
  Definition loc_356 : location_info := LocationInfo file_0 360 73 360 76.
  Definition loc_357 : location_info := LocationInfo file_0 360 80 360 95.
  Definition loc_358 : location_info := LocationInfo file_0 360 81 360 87.
  Definition loc_359 : location_info := LocationInfo file_0 360 81 360 83.
  Definition loc_360 : location_info := LocationInfo file_0 360 86 360 87.
  Definition loc_361 : location_info := LocationInfo file_0 360 90 360 94.
  Definition loc_362 : location_info := LocationInfo file_0 360 101 360 171.
  Definition loc_363 : location_info := LocationInfo file_0 360 102 360 110.
  Definition loc_364 : location_info := LocationInfo file_0 360 102 360 110.
  Definition loc_365 : location_info := LocationInfo file_0 360 113 360 170.
  Definition loc_366 : location_info := LocationInfo file_0 360 114 360 141.
  Definition loc_367 : location_info := LocationInfo file_0 360 115 360 136.
  Definition loc_368 : location_info := LocationInfo file_0 360 115 360 121.
  Definition loc_369 : location_info := LocationInfo file_0 360 117 360 120.
  Definition loc_370 : location_info := LocationInfo file_0 360 124 360 136.
  Definition loc_371 : location_info := LocationInfo file_0 360 125 360 128.
  Definition loc_372 : location_info := LocationInfo file_0 360 132 360 135.
  Definition loc_373 : location_info := LocationInfo file_0 360 139 360 140.
  Definition loc_374 : location_info := LocationInfo file_0 360 144 360 169.
  Definition loc_375 : location_info := LocationInfo file_0 360 145 360 149.
  Definition loc_376 : location_info := LocationInfo file_0 360 146 360 149.
  Definition loc_377 : location_info := LocationInfo file_0 360 153 360 168.
  Definition loc_378 : location_info := LocationInfo file_0 360 154 360 160.
  Definition loc_379 : location_info := LocationInfo file_0 360 154 360 156.
  Definition loc_380 : location_info := LocationInfo file_0 360 159 360 160.
  Definition loc_381 : location_info := LocationInfo file_0 360 163 360 167.
  Definition loc_382 : location_info := LocationInfo file_0 358 31 358 46.
  Definition loc_383 : location_info := LocationInfo file_0 358 32 358 34.
  Definition loc_384 : location_info := LocationInfo file_0 358 33 358 34.
  Definition loc_385 : location_info := LocationInfo file_0 358 37 358 45.
  Definition loc_386 : location_info := LocationInfo file_0 358 37 358 45.
  Definition loc_387 : location_info := LocationInfo file_0 353 24 353 86.
  Definition loc_388 : location_info := LocationInfo file_0 353 24 353 27.
  Definition loc_389 : location_info := LocationInfo file_0 353 24 353 27.
  Definition loc_390 : location_info := LocationInfo file_0 353 30 353 86.
  Definition loc_391 : location_info := LocationInfo file_0 353 31 353 58.
  Definition loc_392 : location_info := LocationInfo file_0 353 32 353 53.
  Definition loc_393 : location_info := LocationInfo file_0 353 32 353 38.
  Definition loc_394 : location_info := LocationInfo file_0 353 34 353 37.
  Definition loc_395 : location_info := LocationInfo file_0 353 41 353 53.
  Definition loc_396 : location_info := LocationInfo file_0 353 42 353 45.
  Definition loc_397 : location_info := LocationInfo file_0 353 49 353 52.
  Definition loc_398 : location_info := LocationInfo file_0 353 56 353 57.
  Definition loc_399 : location_info := LocationInfo file_0 353 61 353 85.
  Definition loc_400 : location_info := LocationInfo file_0 353 62 353 66.
  Definition loc_401 : location_info := LocationInfo file_0 353 63 353 66.
  Definition loc_402 : location_info := LocationInfo file_0 353 70 353 84.
  Definition loc_403 : location_info := LocationInfo file_0 353 71 353 77.
  Definition loc_404 : location_info := LocationInfo file_0 353 71 353 73.
  Definition loc_405 : location_info := LocationInfo file_0 353 76 353 77.
  Definition loc_406 : location_info := LocationInfo file_0 353 80 353 83.
  Definition loc_407 : location_info := LocationInfo file_0 351 15 351 20.
  Definition loc_408 : location_info := LocationInfo file_0 351 15 351 20.
  Definition loc_409 : location_info := LocationInfo file_0 349 8 349 11.
  Definition loc_410 : location_info := LocationInfo file_0 349 14 349 59.
  Definition loc_411 : location_info := LocationInfo file_0 349 14 349 59.
  Definition loc_412 : location_info := LocationInfo file_0 349 15 349 59.
  Definition loc_413 : location_info := LocationInfo file_0 349 37 349 58.
  Definition loc_414 : location_info := LocationInfo file_0 349 38 349 48.
  Definition loc_415 : location_info := LocationInfo file_0 349 38 349 48.
  Definition loc_416 : location_info := LocationInfo file_0 349 51 349 57.
  Definition loc_417 : location_info := LocationInfo file_0 349 51 349 57.
  Definition loc_418 : location_info := LocationInfo file_0 340 23 346 9.
  Definition loc_419 : location_info := LocationInfo file_0 340 24 341 107.
  Definition loc_421 : location_info := LocationInfo file_0 341 16 341 107.
  Definition loc_422 : location_info := LocationInfo file_0 341 108 341 114.
  Definition loc_423 : location_info := LocationInfo file_0 341 114 342 107.
  Definition loc_425 : location_info := LocationInfo file_0 342 16 342 107.
  Definition loc_426 : location_info := LocationInfo file_0 342 108 342 114.
  Definition loc_427 : location_info := LocationInfo file_0 342 114 343 107.
  Definition loc_429 : location_info := LocationInfo file_0 343 16 343 107.
  Definition loc_430 : location_info := LocationInfo file_0 343 108 343 114.
  Definition loc_431 : location_info := LocationInfo file_0 343 114 344 107.
  Definition loc_433 : location_info := LocationInfo file_0 344 16 344 107.
  Definition loc_434 : location_info := LocationInfo file_0 344 108 344 114.
  Definition loc_435 : location_info := LocationInfo file_0 344 114 345 40.
  Definition loc_437 : location_info := LocationInfo file_0 345 17 345 40.
  Definition loc_438 : location_info := LocationInfo file_0 345 24 345 39.
  Definition loc_439 : location_info := LocationInfo file_0 345 25 345 27.
  Definition loc_440 : location_info := LocationInfo file_0 345 26 345 27.
  Definition loc_441 : location_info := LocationInfo file_0 345 30 345 38.
  Definition loc_442 : location_info := LocationInfo file_0 345 30 345 38.
  Definition loc_443 : location_info := LocationInfo file_0 344 16 344 22.
  Definition loc_444 : location_info := LocationInfo file_0 344 25 344 106.
  Definition loc_445 : location_info := LocationInfo file_0 344 25 344 96.
  Definition loc_446 : location_info := LocationInfo file_0 344 26 344 34.
  Definition loc_447 : location_info := LocationInfo file_0 344 26 344 34.
  Definition loc_448 : location_info := LocationInfo file_0 344 37 344 95.
  Definition loc_449 : location_info := LocationInfo file_0 344 38 344 66.
  Definition loc_450 : location_info := LocationInfo file_0 344 39 344 61.
  Definition loc_451 : location_info := LocationInfo file_0 344 39 344 45.
  Definition loc_452 : location_info := LocationInfo file_0 344 41 344 44.
  Definition loc_453 : location_info := LocationInfo file_0 344 48 344 61.
  Definition loc_454 : location_info := LocationInfo file_0 344 49 344 52.
  Definition loc_455 : location_info := LocationInfo file_0 344 56 344 60.
  Definition loc_456 : location_info := LocationInfo file_0 344 64 344 65.
  Definition loc_457 : location_info := LocationInfo file_0 344 69 344 94.
  Definition loc_458 : location_info := LocationInfo file_0 344 70 344 74.
  Definition loc_459 : location_info := LocationInfo file_0 344 71 344 74.
  Definition loc_460 : location_info := LocationInfo file_0 344 78 344 93.
  Definition loc_461 : location_info := LocationInfo file_0 344 79 344 85.
  Definition loc_462 : location_info := LocationInfo file_0 344 79 344 81.
  Definition loc_463 : location_info := LocationInfo file_0 344 84 344 85.
  Definition loc_464 : location_info := LocationInfo file_0 344 88 344 92.
  Definition loc_465 : location_info := LocationInfo file_0 344 100 344 106.
  Definition loc_466 : location_info := LocationInfo file_0 344 101 344 103.
  Definition loc_467 : location_info := LocationInfo file_0 344 104 344 105.
  Definition loc_468 : location_info := LocationInfo file_0 343 16 343 22.
  Definition loc_469 : location_info := LocationInfo file_0 343 25 343 106.
  Definition loc_470 : location_info := LocationInfo file_0 343 25 343 96.
  Definition loc_471 : location_info := LocationInfo file_0 343 26 343 34.
  Definition loc_472 : location_info := LocationInfo file_0 343 26 343 34.
  Definition loc_473 : location_info := LocationInfo file_0 343 37 343 95.
  Definition loc_474 : location_info := LocationInfo file_0 343 38 343 66.
  Definition loc_475 : location_info := LocationInfo file_0 343 39 343 61.
  Definition loc_476 : location_info := LocationInfo file_0 343 39 343 45.
  Definition loc_477 : location_info := LocationInfo file_0 343 41 343 44.
  Definition loc_478 : location_info := LocationInfo file_0 343 48 343 61.
  Definition loc_479 : location_info := LocationInfo file_0 343 49 343 52.
  Definition loc_480 : location_info := LocationInfo file_0 343 56 343 60.
  Definition loc_481 : location_info := LocationInfo file_0 343 64 343 65.
  Definition loc_482 : location_info := LocationInfo file_0 343 69 343 94.
  Definition loc_483 : location_info := LocationInfo file_0 343 70 343 74.
  Definition loc_484 : location_info := LocationInfo file_0 343 71 343 74.
  Definition loc_485 : location_info := LocationInfo file_0 343 78 343 93.
  Definition loc_486 : location_info := LocationInfo file_0 343 79 343 85.
  Definition loc_487 : location_info := LocationInfo file_0 343 79 343 81.
  Definition loc_488 : location_info := LocationInfo file_0 343 84 343 85.
  Definition loc_489 : location_info := LocationInfo file_0 343 88 343 92.
  Definition loc_490 : location_info := LocationInfo file_0 343 100 343 106.
  Definition loc_491 : location_info := LocationInfo file_0 343 101 343 103.
  Definition loc_492 : location_info := LocationInfo file_0 343 104 343 105.
  Definition loc_493 : location_info := LocationInfo file_0 342 16 342 22.
  Definition loc_494 : location_info := LocationInfo file_0 342 25 342 106.
  Definition loc_495 : location_info := LocationInfo file_0 342 25 342 96.
  Definition loc_496 : location_info := LocationInfo file_0 342 26 342 34.
  Definition loc_497 : location_info := LocationInfo file_0 342 26 342 34.
  Definition loc_498 : location_info := LocationInfo file_0 342 37 342 95.
  Definition loc_499 : location_info := LocationInfo file_0 342 38 342 66.
  Definition loc_500 : location_info := LocationInfo file_0 342 39 342 61.
  Definition loc_501 : location_info := LocationInfo file_0 342 39 342 45.
  Definition loc_502 : location_info := LocationInfo file_0 342 41 342 44.
  Definition loc_503 : location_info := LocationInfo file_0 342 48 342 61.
  Definition loc_504 : location_info := LocationInfo file_0 342 49 342 52.
  Definition loc_505 : location_info := LocationInfo file_0 342 56 342 60.
  Definition loc_506 : location_info := LocationInfo file_0 342 64 342 65.
  Definition loc_507 : location_info := LocationInfo file_0 342 69 342 94.
  Definition loc_508 : location_info := LocationInfo file_0 342 70 342 74.
  Definition loc_509 : location_info := LocationInfo file_0 342 71 342 74.
  Definition loc_510 : location_info := LocationInfo file_0 342 78 342 93.
  Definition loc_511 : location_info := LocationInfo file_0 342 79 342 85.
  Definition loc_512 : location_info := LocationInfo file_0 342 79 342 81.
  Definition loc_513 : location_info := LocationInfo file_0 342 84 342 85.
  Definition loc_514 : location_info := LocationInfo file_0 342 88 342 92.
  Definition loc_515 : location_info := LocationInfo file_0 342 100 342 106.
  Definition loc_516 : location_info := LocationInfo file_0 342 101 342 103.
  Definition loc_517 : location_info := LocationInfo file_0 342 104 342 105.
  Definition loc_518 : location_info := LocationInfo file_0 341 16 341 22.
  Definition loc_519 : location_info := LocationInfo file_0 341 25 341 106.
  Definition loc_520 : location_info := LocationInfo file_0 341 25 341 96.
  Definition loc_521 : location_info := LocationInfo file_0 341 26 341 34.
  Definition loc_522 : location_info := LocationInfo file_0 341 26 341 34.
  Definition loc_523 : location_info := LocationInfo file_0 341 37 341 95.
  Definition loc_524 : location_info := LocationInfo file_0 341 38 341 66.
  Definition loc_525 : location_info := LocationInfo file_0 341 39 341 61.
  Definition loc_526 : location_info := LocationInfo file_0 341 39 341 45.
  Definition loc_527 : location_info := LocationInfo file_0 341 41 341 44.
  Definition loc_528 : location_info := LocationInfo file_0 341 48 341 61.
  Definition loc_529 : location_info := LocationInfo file_0 341 49 341 52.
  Definition loc_530 : location_info := LocationInfo file_0 341 56 341 60.
  Definition loc_531 : location_info := LocationInfo file_0 341 64 341 65.
  Definition loc_532 : location_info := LocationInfo file_0 341 69 341 94.
  Definition loc_533 : location_info := LocationInfo file_0 341 70 341 74.
  Definition loc_534 : location_info := LocationInfo file_0 341 71 341 74.
  Definition loc_535 : location_info := LocationInfo file_0 341 78 341 93.
  Definition loc_536 : location_info := LocationInfo file_0 341 79 341 85.
  Definition loc_537 : location_info := LocationInfo file_0 341 79 341 81.
  Definition loc_538 : location_info := LocationInfo file_0 341 84 341 85.
  Definition loc_539 : location_info := LocationInfo file_0 341 88 341 92.
  Definition loc_540 : location_info := LocationInfo file_0 341 100 341 106.
  Definition loc_541 : location_info := LocationInfo file_0 341 101 341 103.
  Definition loc_542 : location_info := LocationInfo file_0 341 104 341 105.
  Definition loc_543 : location_info := LocationInfo file_0 340 16 340 21.
  Definition loc_544 : location_info := LocationInfo file_0 340 16 340 21.
  Definition loc_545 : location_info := LocationInfo file_0 339 36 339 37.
  Definition loc_550 : location_info := LocationInfo file_0 402 2 402 11.
  Definition loc_551 : location_info := LocationInfo file_0 403 2 403 12.
  Definition loc_552 : location_info := LocationInfo file_0 405 2 405 46.
  Definition loc_553 : location_info := LocationInfo file_0 409 2 409 11.
  Definition loc_554 : location_info := LocationInfo file_0 409 9 409 10.
  Definition loc_555 : location_info := LocationInfo file_0 405 23 405 45.
  Definition loc_556 : location_info := LocationInfo file_0 405 23 405 33.
  Definition loc_557 : location_info := LocationInfo file_0 405 23 405 33.
  Definition loc_558 : location_info := LocationInfo file_0 405 34 405 37.
  Definition loc_559 : location_info := LocationInfo file_0 405 34 405 37.
  Definition loc_560 : location_info := LocationInfo file_0 405 39 405 44.
  Definition loc_561 : location_info := LocationInfo file_0 405 39 405 44.
  Definition loc_564 : location_info := LocationInfo file_0 403 2 403 7.
  Definition loc_565 : location_info := LocationInfo file_0 403 10 403 11.
  Definition loc_566 : location_info := LocationInfo file_0 402 2 402 5.
  Definition loc_567 : location_info := LocationInfo file_0 402 8 402 10.

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
          (LocInfoE loc_105 (use{it_layout u8} (LocInfoE loc_106 ("level"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_4 ;
            Goto "#2") ::
            (locinfo: loc_6 ;
            Goto "#3") ::
            (locinfo: loc_8 ;
            Goto "#4") ::
            (locinfo: loc_12 ;
            Goto "#5") :: []
          )
          (locinfo: loc_15 ;
          Goto "#6")
      ]> $
      <[ "#1" :=
        Return (VOID)
      ]> $
      <[ "#11" :=
        locinfo: loc_22 ;
        Goto "#12"
      ]> $
      <[ "#12" :=
        locinfo: loc_24 ;
        Return (LocInfoE loc_33 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_33 (i2v 0 i32))))
      ]> $
      <[ "#13" :=
        locinfo: loc_27 ;
        Return (LocInfoE loc_32 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_32 (i2v 5 i32))))
      ]> $
      <[ "#14" :=
        locinfo: loc_30 ;
        Return (LocInfoE loc_31 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_31 (i2v 3 i32))))
      ]> $
      <[ "#15" :=
        locinfo: loc_15 ;
        Goto "#9"
      ]> $
      <[ "#17" :=
        locinfo: loc_57 ;
        Goto "#18"
      ]> $
      <[ "#18" :=
        locinfo: loc_59 ;
        Return (LocInfoE loc_84 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_84 (i2v 0 i32))))
      ]> $
      <[ "#19" :=
        locinfo: loc_62 ;
        Switch u8
          (LocInfoE loc_82 (use{it_layout u8} (LocInfoE loc_83 ("level"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> ∅
          )
          (
            (locinfo: loc_72 ;
            Goto "#25") ::
            (locinfo: loc_75 ;
            Goto "#26") ::
            (locinfo: loc_77 ;
            Goto "#27") :: []
          )
          (locinfo: loc_63 ;
          Goto "#22")
      ]> $
      <[ "#2" :=
        locinfo: loc_6 ;
        Goto "#3"
      ]> $
      <[ "#20" :=
        locinfo: loc_65 ;
        Return (LocInfoE loc_70 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_70 (i2v 2 i32))))
      ]> $
      <[ "#21" :=
        locinfo: loc_68 ;
        Return (LocInfoE loc_69 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_69 (i2v 6 i32))))
      ]> $
      <[ "#22" :=
        locinfo: loc_63 ;
        Goto "#20"
      ]> $
      <[ "#23" :=
        locinfo: loc_12 ;
        Goto "#7"
      ]> $
      <[ "#25" :=
        locinfo: loc_74 ;
        Return (LocInfoE loc_81 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_81 (i2v 4 i32))))
      ]> $
      <[ "#26" :=
        locinfo: loc_77 ;
        Goto "#27"
      ]> $
      <[ "#27" :=
        locinfo: loc_79 ;
        Return (LocInfoE loc_80 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_80 (i2v 1 i32))))
      ]> $
      <[ "#28" :=
        locinfo: loc_63 ;
        Goto "#22"
      ]> $
      <[ "#3" :=
        locinfo: loc_8 ;
        Goto "#4"
      ]> $
      <[ "#4" :=
        locinfo: loc_11 ;
        Switch u64
          (LocInfoE loc_85 ((LocInfoE loc_86 (use{it_layout u64} (LocInfoE loc_87 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_88 ((LocInfoE loc_89 ((LocInfoE loc_90 ((LocInfoE loc_91 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_92 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_93 ((LocInfoE loc_94 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_95 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_95 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_96 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_96 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_97 ((LocInfoE loc_98 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_99 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_100 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_100 ((LocInfoE loc_101 ((LocInfoE loc_102 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_103 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_104 (i2v 1 i32))))))))))))
          (
            <[ 0 := 0%nat ]> $
            <[ 2 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_55 ;
            Goto "#17") ::
            (locinfo: loc_57 ;
            Goto "#18") ::
            (locinfo: loc_60 ;
            Goto "#19") ::
            (locinfo: loc_63 ;
            Goto "#20") :: []
          )
          (locinfo: loc_66 ;
          Goto "#21")
      ]> $
      <[ "#5" :=
        locinfo: loc_14 ;
        Switch u64
          (LocInfoE loc_34 ((LocInfoE loc_35 (use{it_layout u64} (LocInfoE loc_36 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_37 ((LocInfoE loc_38 ((LocInfoE loc_39 ((LocInfoE loc_40 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_41 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_42 ((LocInfoE loc_43 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_44 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_44 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_45 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_45 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_46 ((LocInfoE loc_47 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_48 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_49 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_49 ((LocInfoE loc_50 ((LocInfoE loc_51 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_52 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_53 (i2v 1 i32))))))))))))
          (
            <[ 0 := 0%nat ]> $
            <[ 2 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_20 ;
            Goto "#11") ::
            (locinfo: loc_22 ;
            Goto "#12") ::
            (locinfo: loc_25 ;
            Goto "#13") ::
            (locinfo: loc_28 ;
            Goto "#14") :: []
          )
          (locinfo: loc_15 ;
          Goto "#9")
      ]> $
      <[ "#6" :=
        locinfo: loc_17 ;
        Return (LocInfoE loc_18 (UnOp (CastOp $ IntOp u32) (IntOp i32) (LocInfoE loc_18 (i2v 6 i32))))
      ]> $
      <[ "#7" :=
        locinfo: loc_12 ;
        Goto "#5"
      ]> $
      <[ "#8" :=
        Goto "#1"
      ]> $
      <[ "#9" :=
        locinfo: loc_15 ;
        Goto "#6"
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
        locinfo: loc_109 ;
        Return (LocInfoE loc_110 (UnOp (CastOp $ PtrOp) (IntOp i64) (LocInfoE loc_111 ((LocInfoE loc_112 (UnOp (CastOp $ IntOp i64) (IntOp i64) (LocInfoE loc_113 (use{it_layout i64} (LocInfoE loc_114 ("phys")))))) -{IntOp i64, IntOp i64} (LocInfoE loc_115 (use{it_layout i64} (LocInfoE loc_116 (global_hyp_physvirt_offset))))))))
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
          LocInfoE loc_545 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_545 (i2v 0 i32))) ;
        locinfo: loc_120 ;
        Switch u64
          (LocInfoE loc_543 (use{it_layout u64} (LocInfoE loc_544 ("level"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_419 ;
            Goto "#31") ::
            (locinfo: loc_423 ;
            Goto "#32") ::
            (locinfo: loc_427 ;
            Goto "#33") ::
            (locinfo: loc_431 ;
            Goto "#34") :: []
          )
          (locinfo: loc_435 ;
          Goto "#35")
      ]> $
      <[ "#1" :=
        locinfo: loc_121 ;
        LocInfoE loc_409 ("pte") <-{ it_layout u64 }
          LocInfoE loc_410 (use{it_layout u64} (LocInfoE loc_412 (UnOp (CastOp $ PtrOp) (IntOp u64) (LocInfoE loc_413 ((LocInfoE loc_414 (!{it_layout u64} (LocInfoE loc_415 ("table_base")))) +{IntOp u64, IntOp u64} (LocInfoE loc_416 (use{it_layout u64} (LocInfoE loc_417 ("offset"))))))))) ;
        locinfo: loc_122 ;
        Switch u64
          (LocInfoE loc_407 (use{it_layout u64} (LocInfoE loc_408 ("level"))))
          (
            <[ 3 := 0%nat ]> $
            <[ 0 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 2 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_124 ;
            Goto "#3") ::
            (locinfo: loc_127 ;
            Goto "#4") ::
            (locinfo: loc_129 ;
            Goto "#5") ::
            (locinfo: loc_131 ;
            Goto "#7") :: []
          )
          (locinfo: loc_135 ;
          Goto "#8")
      ]> $
      <[ "#10" :=
        locinfo: loc_135 ;
        Goto "#8"
      ]> $
      <[ "#12" :=
        locinfo: loc_146 ;
        Goto "#13"
      ]> $
      <[ "#13" :=
        locinfo: loc_148 ;
        Return (LocInfoE loc_305 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_305 ((LocInfoE loc_306 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_306 (UnOp NegOp (IntOp i32) (LocInfoE loc_307 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_308 (use{it_layout u64} (LocInfoE loc_309 ("vaddress"))))))))
      ]> $
      <[ "#14" :=
        locinfo: loc_151 ;
        Switch u64
          (LocInfoE loc_303 (use{it_layout u64} (LocInfoE loc_304 ("level"))))
          (
            <[ 0 := 0%nat ]> $
            <[ 1 := 1%nat ]> $
            <[ 2 := 2%nat ]> ∅
          )
          (
            (locinfo: loc_207 ;
            Goto "#20") ::
            (locinfo: loc_210 ;
            Goto "#21") ::
            (locinfo: loc_213 ;
            Goto "#22") :: []
          )
          (locinfo: loc_152 ;
          Goto "#17")
      ]> $
      <[ "#15" :=
        locinfo: loc_155 ;
        LocInfoE loc_185 ("table_base_next_phys") <-{ it_layout u64 }
          LocInfoE loc_186 ((LocInfoE loc_187 (use{it_layout u64} (LocInfoE loc_188 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_189 ((LocInfoE loc_190 ((LocInfoE loc_191 ((LocInfoE loc_192 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_193 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_194 ((LocInfoE loc_195 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_196 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_196 (i2v 12 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_197 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_197 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_198 ((LocInfoE loc_199 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_200 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_201 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_201 ((LocInfoE loc_202 ((LocInfoE loc_203 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_204 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_205 (i2v 47 i32))))))))))) ;
        locinfo: loc_156 ;
        LocInfoE loc_177 ("table_base_next_virt") <-{ it_layout u64 }
          LocInfoE loc_178 (UnOp (CastOp $ IntOp u64) (PtrOp) (LocInfoE loc_179 (Call (LocInfoE loc_181 (global_hyp_phys_to_virt)) [@{expr} LocInfoE loc_182 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_183 (use{it_layout u64} (LocInfoE loc_184 ("table_base_next_phys"))))) ]))) ;
        locinfo: loc_157 ;
        Return (LocInfoE loc_166 (Call (LocInfoE loc_168 (global_AArch64_TranslationTableWalk)) [@{expr} LocInfoE loc_169 (use{it_layout u64} (LocInfoE loc_170 ("table_base_next_virt"))) ;
               LocInfoE loc_171 ((LocInfoE loc_172 (use{it_layout u64} (LocInfoE loc_173 ("level")))) +{IntOp u64, IntOp u64} (LocInfoE loc_174 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_174 (i2v 1 i32))))) ;
               LocInfoE loc_175 (use{it_layout u64} (LocInfoE loc_176 ("vaddress"))) ]))
      ]> $
      <[ "#16" :=
        locinfo: loc_160 ;
        Return (LocInfoE loc_161 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_161 ((LocInfoE loc_162 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_162 (UnOp NegOp (IntOp i32) (LocInfoE loc_163 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_164 (use{it_layout u64} (LocInfoE loc_165 ("vaddress"))))))))
      ]> $
      <[ "#17" :=
        locinfo: loc_152 ;
        Goto "#15"
      ]> $
      <[ "#18" :=
        locinfo: loc_135 ;
        Goto "#10"
      ]> $
      <[ "#2" :=
        Return (VOID)
      ]> $
      <[ "#20" :=
        locinfo: loc_209 ;
        Return (LocInfoE loc_298 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_298 ((LocInfoE loc_299 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_299 (UnOp NegOp (IntOp i32) (LocInfoE loc_300 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_301 (use{it_layout u64} (LocInfoE loc_302 ("vaddress"))))))))
      ]> $
      <[ "#21" :=
        locinfo: loc_212 ;
        Return (LocInfoE loc_257 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_257 ((LocInfoE loc_258 ((LocInfoE loc_259 (use{it_layout u64} (LocInfoE loc_260 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_261 ((LocInfoE loc_262 ((LocInfoE loc_263 ((LocInfoE loc_264 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_265 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_266 ((LocInfoE loc_267 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_268 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_268 (i2v 30 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_269 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_269 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_270 ((LocInfoE loc_271 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_272 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_273 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_273 ((LocInfoE loc_274 ((LocInfoE loc_275 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_276 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_277 (i2v 47 i32)))))))))))) |{IntOp u64, IntOp u64} (LocInfoE loc_278 ((LocInfoE loc_279 (use{it_layout u64} (LocInfoE loc_280 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_281 ((LocInfoE loc_282 ((LocInfoE loc_283 ((LocInfoE loc_284 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_285 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_286 ((LocInfoE loc_287 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_288 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_288 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_289 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_289 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_290 ((LocInfoE loc_291 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_292 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_293 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_293 ((LocInfoE loc_294 ((LocInfoE loc_295 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_296 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_297 (i2v 29 i32))))))))))))))))
      ]> $
      <[ "#22" :=
        locinfo: loc_215 ;
        Return (LocInfoE loc_216 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_216 ((LocInfoE loc_217 ((LocInfoE loc_218 (use{it_layout u64} (LocInfoE loc_219 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_220 ((LocInfoE loc_221 ((LocInfoE loc_222 ((LocInfoE loc_223 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_224 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_225 ((LocInfoE loc_226 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_227 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_227 (i2v 21 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_228 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_228 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_229 ((LocInfoE loc_230 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_231 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_232 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_232 ((LocInfoE loc_233 ((LocInfoE loc_234 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_235 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_236 (i2v 47 i32)))))))))))) |{IntOp u64, IntOp u64} (LocInfoE loc_237 ((LocInfoE loc_238 (use{it_layout u64} (LocInfoE loc_239 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_240 ((LocInfoE loc_241 ((LocInfoE loc_242 ((LocInfoE loc_243 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_244 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_245 ((LocInfoE loc_246 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_247 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_247 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_248 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_248 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_249 ((LocInfoE loc_250 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_251 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_252 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_252 ((LocInfoE loc_253 ((LocInfoE loc_254 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_255 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_256 (i2v 20 i32))))))))))))))))
      ]> $
      <[ "#23" :=
        locinfo: loc_152 ;
        Goto "#17"
      ]> $
      <[ "#25" :=
        locinfo: loc_333 ;
        Goto "#26"
      ]> $
      <[ "#26" :=
        locinfo: loc_335 ;
        Goto "#27"
      ]> $
      <[ "#27" :=
        locinfo: loc_337 ;
        Return (LocInfoE loc_382 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_382 ((LocInfoE loc_383 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_383 (UnOp NegOp (IntOp i32) (LocInfoE loc_384 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_385 (use{it_layout u64} (LocInfoE loc_386 ("vaddress"))))))))
      ]> $
      <[ "#28" :=
        locinfo: loc_340 ;
        Return (LocInfoE loc_341 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_341 ((LocInfoE loc_342 ((LocInfoE loc_343 (use{it_layout u64} (LocInfoE loc_344 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_345 ((LocInfoE loc_346 ((LocInfoE loc_347 ((LocInfoE loc_348 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_349 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_350 ((LocInfoE loc_351 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_352 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_352 (i2v 12 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_353 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_353 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_354 ((LocInfoE loc_355 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_356 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_357 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_357 ((LocInfoE loc_358 ((LocInfoE loc_359 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_360 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_361 (i2v 47 i32)))))))))))) |{IntOp u64, IntOp u64} (LocInfoE loc_362 ((LocInfoE loc_363 (use{it_layout u64} (LocInfoE loc_364 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_365 ((LocInfoE loc_366 ((LocInfoE loc_367 ((LocInfoE loc_368 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_369 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_370 ((LocInfoE loc_371 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_372 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_372 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_373 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_373 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_374 ((LocInfoE loc_375 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_376 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_377 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_377 ((LocInfoE loc_378 ((LocInfoE loc_379 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_380 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_381 (i2v 11 i32))))))))))))))))
      ]> $
      <[ "#29" :=
        locinfo: loc_127 ;
        Goto "#6"
      ]> $
      <[ "#3" :=
        locinfo: loc_126 ;
        Switch u64
          (LocInfoE loc_387 ((LocInfoE loc_388 (use{it_layout u64} (LocInfoE loc_389 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_390 ((LocInfoE loc_391 ((LocInfoE loc_392 ((LocInfoE loc_393 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_394 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_395 ((LocInfoE loc_396 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_397 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_397 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_398 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_398 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_399 ((LocInfoE loc_400 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_401 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_402 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_402 ((LocInfoE loc_403 ((LocInfoE loc_404 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_405 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_406 (i2v 1 i32))))))))))))
          (
            <[ 0 := 0%nat ]> $
            <[ 2 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_331 ;
            Goto "#25") ::
            (locinfo: loc_333 ;
            Goto "#26") ::
            (locinfo: loc_335 ;
            Goto "#27") ::
            (locinfo: loc_338 ;
            Goto "#28") :: []
          )
          (locinfo: loc_127 ;
          Goto "#6")
      ]> $
      <[ "#31" :=
        locinfo: loc_421 ;
        LocInfoE loc_518 ("offset") <-{ it_layout u64 }
          LocInfoE loc_519 ((LocInfoE loc_520 ((LocInfoE loc_521 (use{it_layout u64} (LocInfoE loc_522 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_523 ((LocInfoE loc_524 ((LocInfoE loc_525 ((LocInfoE loc_526 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_527 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_528 ((LocInfoE loc_529 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_530 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_530 (i2v 39 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_531 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_531 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_532 ((LocInfoE loc_533 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_534 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_535 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_535 ((LocInfoE loc_536 ((LocInfoE loc_537 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_538 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_539 (i2v 47 i32)))))))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_540 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_540 ((LocInfoE loc_541 (i2v 39 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_542 (i2v 3 i32))))))) ;
        locinfo: loc_121 ;
        Goto "#1"
      ]> $
      <[ "#32" :=
        locinfo: loc_425 ;
        LocInfoE loc_493 ("offset") <-{ it_layout u64 }
          LocInfoE loc_494 ((LocInfoE loc_495 ((LocInfoE loc_496 (use{it_layout u64} (LocInfoE loc_497 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_498 ((LocInfoE loc_499 ((LocInfoE loc_500 ((LocInfoE loc_501 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_502 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_503 ((LocInfoE loc_504 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_505 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_505 (i2v 30 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_506 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_506 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_507 ((LocInfoE loc_508 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_509 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_510 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_510 ((LocInfoE loc_511 ((LocInfoE loc_512 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_513 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_514 (i2v 38 i32)))))))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_515 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_515 ((LocInfoE loc_516 (i2v 30 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_517 (i2v 3 i32))))))) ;
        locinfo: loc_121 ;
        Goto "#1"
      ]> $
      <[ "#33" :=
        locinfo: loc_429 ;
        LocInfoE loc_468 ("offset") <-{ it_layout u64 }
          LocInfoE loc_469 ((LocInfoE loc_470 ((LocInfoE loc_471 (use{it_layout u64} (LocInfoE loc_472 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_473 ((LocInfoE loc_474 ((LocInfoE loc_475 ((LocInfoE loc_476 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_477 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_478 ((LocInfoE loc_479 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_480 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_480 (i2v 21 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_481 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_481 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_482 ((LocInfoE loc_483 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_484 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_485 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_485 ((LocInfoE loc_486 ((LocInfoE loc_487 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_488 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_489 (i2v 29 i32)))))))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_490 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_490 ((LocInfoE loc_491 (i2v 21 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_492 (i2v 3 i32))))))) ;
        locinfo: loc_121 ;
        Goto "#1"
      ]> $
      <[ "#34" :=
        locinfo: loc_433 ;
        LocInfoE loc_443 ("offset") <-{ it_layout u64 }
          LocInfoE loc_444 ((LocInfoE loc_445 ((LocInfoE loc_446 (use{it_layout u64} (LocInfoE loc_447 ("vaddress")))) &{IntOp u64, IntOp u64} (LocInfoE loc_448 ((LocInfoE loc_449 ((LocInfoE loc_450 ((LocInfoE loc_451 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_452 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_453 ((LocInfoE loc_454 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_455 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_455 (i2v 12 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_456 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_456 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_457 ((LocInfoE loc_458 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_459 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_460 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_460 ((LocInfoE loc_461 ((LocInfoE loc_462 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_463 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_464 (i2v 20 i32)))))))))))) >>{IntOp u64, IntOp u64} (LocInfoE loc_465 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_465 ((LocInfoE loc_466 (i2v 12 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_467 (i2v 3 i32))))))) ;
        locinfo: loc_121 ;
        Goto "#1"
      ]> $
      <[ "#35" :=
        locinfo: loc_437 ;
        Return (LocInfoE loc_438 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_438 ((LocInfoE loc_439 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_439 (UnOp NegOp (IntOp i32) (LocInfoE loc_440 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_441 (use{it_layout u64} (LocInfoE loc_442 ("vaddress"))))))))
      ]> $
      <[ "#36" :=
        locinfo: loc_121 ;
        Goto "#1"
      ]> $
      <[ "#4" :=
        locinfo: loc_129 ;
        Goto "#5"
      ]> $
      <[ "#5" :=
        locinfo: loc_131 ;
        Goto "#7"
      ]> $
      <[ "#6" :=
        locinfo: loc_127 ;
        Goto "#4"
      ]> $
      <[ "#7" :=
        locinfo: loc_134 ;
        Switch u64
          (LocInfoE loc_310 ((LocInfoE loc_311 (use{it_layout u64} (LocInfoE loc_312 ("pte")))) &{IntOp u64, IntOp u64} (LocInfoE loc_313 ((LocInfoE loc_314 ((LocInfoE loc_315 ((LocInfoE loc_316 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_317 (i2v 0 u64)))) -{IntOp u64, IntOp u64} (LocInfoE loc_318 ((LocInfoE loc_319 (i2v 1 u64)) <<{IntOp u64, IntOp u64} (LocInfoE loc_320 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_320 (i2v 0 i32)))))))) +{IntOp u64, IntOp u64} (LocInfoE loc_321 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_321 (i2v 1 i32)))))) &{IntOp u64, IntOp u64} (LocInfoE loc_322 ((LocInfoE loc_323 (UnOp NotIntOp (IntOp u64) (LocInfoE loc_324 (i2v 0 u64)))) >>{IntOp u64, IntOp u64} (LocInfoE loc_325 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_325 ((LocInfoE loc_326 ((LocInfoE loc_327 (i2v 64 i32)) -{IntOp i32, IntOp i32} (LocInfoE loc_328 (i2v 1 i32)))) -{IntOp i32, IntOp i32} (LocInfoE loc_329 (i2v 1 i32))))))))))))
          (
            <[ 0 := 0%nat ]> $
            <[ 2 := 1%nat ]> $
            <[ 1 := 2%nat ]> $
            <[ 3 := 3%nat ]> ∅
          )
          (
            (locinfo: loc_144 ;
            Goto "#12") ::
            (locinfo: loc_146 ;
            Goto "#13") ::
            (locinfo: loc_149 ;
            Goto "#14") ::
            (locinfo: loc_152 ;
            Goto "#15") :: []
          )
          (locinfo: loc_158 ;
          Goto "#16")
      ]> $
      <[ "#8" :=
        locinfo: loc_137 ;
        Return (LocInfoE loc_138 (UnOp (CastOp $ IntOp i64) (IntOp u64) (LocInfoE loc_138 ((LocInfoE loc_139 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_139 (UnOp NegOp (IntOp i32) (LocInfoE loc_140 (i2v 1 i32)))))) ×{IntOp u64, IntOp u64} (LocInfoE loc_141 (use{it_layout u64} (LocInfoE loc_142 ("vaddress"))))))))
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
        locinfo: loc_550 ;
        LocInfoE loc_566 ("pte") <-{ it_layout u64 }
          LocInfoE loc_567 (UnOp (CastOp $ IntOp u64) (IntOp i32) (LocInfoE loc_567 (i2v 10 i32))) ;
        locinfo: loc_551 ;
        LocInfoE loc_564 ("level") <-{ it_layout u8 }
          LocInfoE loc_565 (UnOp (CastOp $ IntOp u8) (IntOp i32) (LocInfoE loc_565 (i2v 3 i32))) ;
        "ek" <-{ it_layout u32 }
          LocInfoE loc_555 (Call (LocInfoE loc_557 (global_entry_kind)) [@{expr} LocInfoE loc_558 (use{it_layout u64} (LocInfoE loc_559 ("pte"))) ;
          LocInfoE loc_560 (use{it_layout u8} (LocInfoE loc_561 ("level"))) ]) ;
        locinfo: loc_553 ;
        Return (LocInfoE loc_554 (i2v 0 i32))
      ]> $∅
    )%E
  |}.
End code.
