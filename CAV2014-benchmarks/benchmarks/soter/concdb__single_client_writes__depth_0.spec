vars
	s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 s34 s35 s36 s37 s38 s39 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46 l47 l48 l49 l50 l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l61 l62 l63 l64 l65 l66 l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78 l79 l80 l81 l82 l83 l84 l85 l86 l87 l88 l89 l90 l91 l92 l93 l94 l95 l96 l97 l98 l99 l100 l101 l102 l103 l104 l105 l106 l107 l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118 l119 l120 l121 l122 l123 l124 l125 l126 l127 l128 l129 l130 l131 l132 l133 l134 l135 l136 l137 l138 l139 l140 l141 l142 l143 l144 l145 l146 l147 l148 l149 l150 l151 l152 l153 l154 l155 l156 l157 l158 l159 l160 l161 l162 l163 l164 l165 l166 l167 l168 l169 l170 l171 l172 l173 l174 l175 l176 l177 l178 l179 l180 l181 l182 l183 l184 l185 l186 l187 l188 l189 l190 l191 l192 l193 l194 l195 l196 l197 l198 l199 l200 l201 l202 l203 l204 l205 l206 l207 l208 l209 l210 l211 l212 l213 l214 l215 l216 l217 l218 l219 l220 l221 l222 l223 l224 l225 l226 l227 l228 l229 l230 l231 l232 l233 l234 l235 l236 l237 l238 l239 l240 l241 l242 l243 l244 l245 l246 l247 l248 l249 l250 l251 l252 l253 l254 l255 l256 l257 l258 l259 l260 l261 l262 l263 l264 l265 l266 l267 l268 l269 l270 l271 l272 l273 l274 l275 l276 l277 l278 l279 l280 l281 l282 l283 l284 l285 l286 l287 l288 l289 l290 l291 l292 l293 l294 l295 l296 l297 l298 l299 l300 l301 l302 l303 l304 l305 l306 l307 l308 l309 l310 l311 l312 l313 l314 l315 l316 l317 l318 l319 l320 l321 l322 l323 l324 l325 l326 l327 l328 l329 l330 l331 l332 l333 l334 l335 l336 l337 l338 l339 l340 l341 l342 l343 l344 l345 l346 l347 l348 l349 l350 l351 l352 l353 l354 l355 l356 l357 l358 l359 l360 l361 l362 l363 l364 l365 l366 l367 l368 l369 l370 l371 l372 l373 l374 l375 l376 l377 l378 l379 l380 l381 l382 l383 l384 l385 l386 l387 l388 l389 l390 l391 l392 l393 l394 l395 l396 l397 l398 l399 l400 l401 l402 l403 l404 l405 l406 l407 l408 l409 l410 l411 l412 l413 l414 l415 l416 l417 l418 l419 l420 l421 l422 l423 l424 l425 l426 l427 l428 l429 l430 l431 l432 l433 l434 l435 l436 l437 l438 l439 l440 l441 l442 l443 l444 l445 l446 l447 l448 l449 l450 l451 l452 l453 l454 l455 l456 l457 l458 l459 l460 l461 l462 l463 l464 l465 l466 l467 l468 l469 l470 l471 l472 l473 l474 l475 l476 l477 l478 l479 l480 l481 l482 l483 l484 l485 l486 l487 l488 l489 l490 l491 l492 l493 l494 l495 l496 l497 l498 l499 l500 l501 l502 l503 l504 l505 l506 l507 l508 l509 l510 l511 l512

rules
	l0 >= 1, s0 >= 1 ->
		s0' = s0 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l1' = l1 + 1;

	l0 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s2' = s2 + 1;

	l1 >= 1, s1 >= 1 ->
		l1' = l1 - 1,
		l3' = l3 + 1;

	l3 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s3' = s3 + 1,
		l3' = l3 - 1,
		l37' = l37 + 1;

	l7 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s4' = s4 + 1,
		l7' = l7 - 1,
		l33' = l33 + 1;

	l32 >= 1, s1 >= 1 ->
		l32' = l32 - 1,
		l7' = l7 + 1;

	l32 >= 1, s1 >= 1 ->
		l32' = l32 - 1,
		l28' = l28 + 1;

	l33 >= 1, s1 >= 1 ->
		l33' = l33 - 1,
		l339' = l339 + 1;

	l33 >= 1, s1 >= 1 ->
		l33' = l33 - 1,
		l345' = l345 + 1;

	l33 >= 1, s1 >= 1 ->
		l33' = l33 - 1,
		l375' = l375 + 1;

	l33 >= 1, s1 >= 1 ->
		l33' = l33 - 1,
		l377' = l377 + 1;

	l36 >= 1, s1 >= 1 ->
		l36' = l36 - 1,
		l7' = l7 + 1;

	l37 >= 1, s1 >= 1 ->
		l37' = l37 - 1,
		l110' = l110 + 1;

	l90 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s5' = s5 + 1,
		l90' = l90 - 1,
		l122' = l122 + 1;

	l91 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s6' = s6 + 1,
		l91' = l91 - 1,
		l136' = l136 + 1;

	l91 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s7' = s7 + 1,
		l91' = l91 - 1,
		l137' = l137 + 1;

	l110 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s8' = s8 + 1,
		l110' = l110 - 1,
		l0' = l0 + 1;

	l110 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s9' = s9 + 1,
		l110' = l110 - 1,
		l0' = l0 + 1;

	l110 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s10' = s10 + 1,
		l110' = l110 - 1,
		l0' = l0 + 1;

	l110 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s11' = s11 + 1,
		l110' = l110 - 1,
		l0' = l0 + 1;

	l112 >= 1, s1 >= 1 ->
		l112' = l112 - 1,
		l110' = l110 + 1;

	l114 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s12' = s12 + 1,
		l114' = l114 - 1,
		l115' = l115 + 1;

	l116 >= 1, s1 >= 1 ->
		l116' = l116 - 1,
		l110' = l110 + 1;

	l123 >= 1, s1 >= 1 ->
		l123' = l123 - 1,
		l124' = l124 + 1;

	l124 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s13' = s13 + 1,
		l124' = l124 - 1,
		l0' = l0 + 1;

	l124 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s14' = s14 + 1,
		l124' = l124 - 1,
		l0' = l0 + 1;

	l125 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s15' = s15 + 1,
		l125' = l125 - 1,
		l126' = l126 + 1;

	l127 >= 1, s1 >= 1 ->
		l127' = l127 - 1,
		l110' = l110 + 1;

	l133 >= 1, s1 >= 1 ->
		l133' = l133 - 1,
		l110' = l110 + 1;

	l149 >= 1, s1 >= 1 ->
		l149' = l149 - 1,
		l90' = l90 + 1;

	l149 >= 1, s1 >= 1 ->
		l149' = l149 - 1,
		l91' = l91 + 1;

	l149 >= 1, s1 >= 1 ->
		l149' = l149 - 1,
		l114' = l114 + 1;

	l149 >= 1, s1 >= 1 ->
		l149' = l149 - 1,
		l125' = l125 + 1;

	l149 >= 1, s1 >= 1 ->
		l149' = l149 - 1,
		l142' = l142 + 1;

	l149 >= 1, s1 >= 1 ->
		l149' = l149 - 1,
		l144' = l144 + 1;

	l149 >= 1, s1 >= 1 ->
		l149' = l149 - 1,
		l146' = l146 + 1;

	l150 >= 1, s1 >= 1 ->
		l150' = l150 - 1,
		l90' = l90 + 1;

	l150 >= 1, s1 >= 1 ->
		l150' = l150 - 1,
		l91' = l91 + 1;

	l150 >= 1, s1 >= 1 ->
		l150' = l150 - 1,
		l114' = l114 + 1;

	l150 >= 1, s1 >= 1 ->
		l150' = l150 - 1,
		l125' = l125 + 1;

	l150 >= 1, s1 >= 1 ->
		l150' = l150 - 1,
		l142' = l142 + 1;

	l150 >= 1, s1 >= 1 ->
		l150' = l150 - 1,
		l144' = l144 + 1;

	l150 >= 1, s1 >= 1 ->
		l150' = l150 - 1,
		l146' = l146 + 1;

	l334 >= 1, s1 >= 1 ->
		l334' = l334 - 1,
		l335' = l335 + 1;

	l335 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s16' = s16 + 1,
		l335' = l335 - 1,
		l0' = l0 + 1;

	l335 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s17' = s17 + 1,
		l335' = l335 - 1,
		l0' = l0 + 1;

	l336 >= 1, s1 >= 1 ->
		l336' = l336 - 1,
		l337' = l337 + 1;

	l336 >= 1, s1 >= 1 ->
		l336' = l336 - 1,
		l338' = l338 + 1;

	l337 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s18' = s18 + 1,
		l337' = l337 - 1,
		l0' = l0 + 1;

	l337 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s19' = s19 + 1,
		l337' = l337 - 1,
		l0' = l0 + 1;

	l338 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s20' = s20 + 1,
		l338' = l338 - 1,
		l0' = l0 + 1;

	l338 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s21' = s21 + 1,
		l338' = l338 - 1,
		l0' = l0 + 1;

	l339 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s22' = s22 + 1,
		l339' = l339 - 1,
		l151' = l151 + 1;

	l339 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s23' = s23 + 1,
		l339' = l339 - 1,
		l151' = l151 + 1;

	l339 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s24' = s24 + 1,
		l339' = l339 - 1,
		l152' = l152 + 1;

	l339 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s25' = s25 + 1,
		l339' = l339 - 1,
		l152' = l152 + 1;

	l340 >= 1, s1 >= 1 ->
		l340' = l340 - 1,
		l509' = l509 + 1;

	l342 >= 1, s1 >= 1 ->
		l342' = l342 - 1,
		l510' = l510 + 1;

	l345 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s26' = s26 + 1,
		l345' = l345 - 1,
		l153' = l153 + 1;

	l345 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s27' = s27 + 1,
		l345' = l345 - 1,
		l153' = l153 + 1;

	l345 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s28' = s28 + 1,
		l345' = l345 - 1,
		l154' = l154 + 1;

	l345 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s29' = s29 + 1,
		l345' = l345 - 1,
		l154' = l154 + 1;

	l353 >= 1, s1 >= 1 ->
		l353' = l353 - 1,
		l339' = l339 + 1;

	l353 >= 1, s1 >= 1 ->
		l353' = l353 - 1,
		l345' = l345 + 1;

	l353 >= 1, s1 >= 1 ->
		l353' = l353 - 1,
		l375' = l375 + 1;

	l353 >= 1, s1 >= 1 ->
		l353' = l353 - 1,
		l377' = l377 + 1;

	l354 >= 1, s1 >= 1 ->
		l354' = l354 - 1,
		l339' = l339 + 1;

	l354 >= 1, s1 >= 1 ->
		l354' = l354 - 1,
		l345' = l345 + 1;

	l354 >= 1, s1 >= 1 ->
		l354' = l354 - 1,
		l375' = l375 + 1;

	l354 >= 1, s1 >= 1 ->
		l354' = l354 - 1,
		l377' = l377 + 1;

	l355 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s30' = s30 + 1,
		l355' = l355 - 1,
		l155' = l155 + 1;

	l355 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s31' = s31 + 1,
		l355' = l355 - 1,
		l155' = l155 + 1;

	l355 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s32' = s32 + 1,
		l355' = l355 - 1,
		l156' = l156 + 1;

	l355 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s33' = s33 + 1,
		l355' = l355 - 1,
		l156' = l156 + 1;

	l484 >= 1, s1 >= 1 ->
		l484' = l484 - 1,
		l496' = l496 + 1;

	l484 >= 1, s1 >= 1 ->
		l484' = l484 - 1,
		l497' = l497 + 1;

	l485 >= 1, s1 >= 1 ->
		l485' = l485 - 1,
		l496' = l496 + 1;

	l485 >= 1, s1 >= 1 ->
		l485' = l485 - 1,
		l497' = l497 + 1;

	l486 >= 1, s1 >= 1 ->
		l486' = l486 - 1,
		l496' = l496 + 1;

	l486 >= 1, s1 >= 1 ->
		l486' = l486 - 1,
		l497' = l497 + 1;

	l487 >= 1, s1 >= 1 ->
		l487' = l487 - 1,
		l488' = l488 + 1;

	l488 >= 1, s1 >= 1 ->
		l488' = l488 - 1,
		l339' = l339 + 1;

	l488 >= 1, s1 >= 1 ->
		l488' = l488 - 1,
		l345' = l345 + 1;

	l488 >= 1, s1 >= 1 ->
		l488' = l488 - 1,
		l375' = l375 + 1;

	l488 >= 1, s1 >= 1 ->
		l488' = l488 - 1,
		l377' = l377 + 1;

	l489 >= 1, s1 >= 1 ->
		l489' = l489 - 1,
		l488' = l488 + 1;

	l490 >= 1, s1 >= 1 ->
		l490' = l490 - 1,
		l491' = l491 + 1;

	l491 >= 1, s1 >= 1 ->
		l491' = l491 - 1,
		l339' = l339 + 1;

	l491 >= 1, s1 >= 1 ->
		l491' = l491 - 1,
		l345' = l345 + 1;

	l491 >= 1, s1 >= 1 ->
		l491' = l491 - 1,
		l375' = l375 + 1;

	l491 >= 1, s1 >= 1 ->
		l491' = l491 - 1,
		l377' = l377 + 1;

	l492 >= 1, s1 >= 1 ->
		l492' = l492 - 1,
		l491' = l491 + 1;

	l496 >= 1, s1 >= 1 ->
		l496' = l496 - 1,
		l355' = l355 + 1;

	l497 >= 1, s1 >= 1 ->
		l497' = l497 - 1,
		l355' = l355 + 1;

	l501 >= 1, s1 >= 1 ->
		l501' = l501 - 1,
		l502' = l502 + 1;

	l502 >= 1, s1 >= 1 ->
		l502' = l502 - 1,
		l339' = l339 + 1;

	l502 >= 1, s1 >= 1 ->
		l502' = l502 - 1,
		l345' = l345 + 1;

	l502 >= 1, s1 >= 1 ->
		l502' = l502 - 1,
		l375' = l375 + 1;

	l502 >= 1, s1 >= 1 ->
		l502' = l502 - 1,
		l377' = l377 + 1;

	l503 >= 1, s1 >= 1 ->
		l503' = l503 - 1,
		l504' = l504 + 1;

	l504 >= 1, s1 >= 1 ->
		l504' = l504 - 1,
		l339' = l339 + 1;

	l504 >= 1, s1 >= 1 ->
		l504' = l504 - 1,
		l345' = l345 + 1;

	l504 >= 1, s1 >= 1 ->
		l504' = l504 - 1,
		l375' = l375 + 1;

	l504 >= 1, s1 >= 1 ->
		l504' = l504 - 1,
		l377' = l377 + 1;

	l505 >= 1, s1 >= 1 ->
		l505' = l505 - 1,
		l504' = l504 + 1;

	l509 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s34' = s34 + 1,
		l509' = l509 - 1,
		l0' = l0 + 1;

	l509 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s35' = s35 + 1,
		l509' = l509 - 1,
		l0' = l0 + 1;

	l509 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s36' = s36 + 1,
		l509' = l509 - 1,
		l0' = l0 + 1;

	l510 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s37' = s37 + 1,
		l510' = l510 - 1,
		l0' = l0 + 1;

	l510 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s38' = s38 + 1,
		l510' = l510 - 1,
		l0' = l0 + 1;

	l510 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s39' = s39 + 1,
		l510' = l510 - 1,
		l0' = l0 + 1;

	l496 >= 1, s2 >= 1 ->
		l496' = l496 - 1,
		l512' = l512 + 1;

	l497 >= 1, s2 >= 1 ->
		l497' = l497 - 1,
		l512' = l512 + 1;

	l0 >= 1, s3 >= 1 ->
		s3' = s3 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l36' = l36 + 1;

	l0 >= 1, s4 >= 1 ->
		s4' = s4 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l32' = l32 + 1;

	l0 >= 1, s5 >= 1 ->
		s5' = s5 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l116' = l116 + 1;

	l0 >= 1, s6 >= 1 ->
		s6' = s6 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l133' = l133 + 1;

	l0 >= 1, s7 >= 1 ->
		s7' = s7 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l133' = l133 + 1;

	l151 >= 1, s8 >= 1 ->
		s8' = s8 - 1,
		s1' = s1 + 1,
		l151' = l151 - 1,
		l150' = l150 + 1;

	l152 >= 1, s9 >= 1 ->
		s9' = s9 - 1,
		s1' = s1 + 1,
		l152' = l152 - 1,
		l150' = l150 + 1;

	l153 >= 1, s10 >= 1 ->
		s10' = s10 - 1,
		s1' = s1 + 1,
		l153' = l153 - 1,
		l149' = l149 + 1;

	l154 >= 1, s11 >= 1 ->
		s11' = s11 - 1,
		s1' = s1 + 1,
		l154' = l154 - 1,
		l149' = l149 + 1;

	l0 >= 1, s12 >= 1 ->
		s12' = s12 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l112' = l112 + 1;

	l155 >= 1, s13 >= 1 ->
		s13' = s13 - 1,
		s1' = s1 + 1,
		l155' = l155 - 1,
		l127' = l127 + 1;

	l156 >= 1, s14 >= 1 ->
		s14' = s14 - 1,
		s1' = s1 + 1,
		l156' = l156 - 1,
		l127' = l127 + 1;

	l0 >= 1, s15 >= 1 ->
		s15' = s15 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l123' = l123 + 1;

	l115 >= 1, s16 >= 1 ->
		s16' = s16 - 1,
		s1' = s1 + 1,
		l115' = l115 - 1,
		l501' = l501 + 1;

	l126 >= 1, s17 >= 1 ->
		s17' = s17 - 1,
		s1' = s1 + 1,
		l126' = l126 - 1,
		l484' = l484 + 1;

	l115 >= 1, s18 >= 1 ->
		s18' = s18 - 1,
		s1' = s1 + 1,
		l115' = l115 - 1,
		l503' = l503 + 1;

	l126 >= 1, s19 >= 1 ->
		s19' = s19 - 1,
		s1' = s1 + 1,
		l126' = l126 - 1,
		l485' = l485 + 1;

	l115 >= 1, s20 >= 1 ->
		s20' = s20 - 1,
		s1' = s1 + 1,
		l115' = l115 - 1,
		l505' = l505 + 1;

	l126 >= 1, s21 >= 1 ->
		s21' = s21 - 1,
		s1' = s1 + 1,
		l126' = l126 - 1,
		l486' = l486 + 1;

	l0 >= 1, s22 >= 1 ->
		s22' = s22 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l334' = l334 + 1;

	l0 >= 1, s23 >= 1 ->
		s23' = s23 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l336' = l336 + 1;

	l0 >= 1, s24 >= 1 ->
		s24' = s24 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l334' = l334 + 1;

	l0 >= 1, s25 >= 1 ->
		s25' = s25 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l336' = l336 + 1;

	l0 >= 1, s26 >= 1 ->
		s26' = s26 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l340' = l340 + 1;

	l0 >= 1, s27 >= 1 ->
		s27' = s27 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l342' = l342 + 1;

	l0 >= 1, s28 >= 1 ->
		s28' = s28 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l340' = l340 + 1;

	l0 >= 1, s29 >= 1 ->
		s29' = s29 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l342' = l342 + 1;

	l0 >= 1, s30 >= 1 ->
		s30' = s30 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l353' = l353 + 1;

	l0 >= 1, s31 >= 1 ->
		s31' = s31 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l354' = l354 + 1;

	l0 >= 1, s32 >= 1 ->
		s32' = s32 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l353' = l353 + 1;

	l0 >= 1, s33 >= 1 ->
		s33' = s33 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l354' = l354 + 1;

	l122 >= 1, s34 >= 1 ->
		s34' = s34 - 1,
		s1' = s1 + 1,
		l122' = l122 - 1,
		l487' = l487 + 1;

	l136 >= 1, s35 >= 1 ->
		s35' = s35 - 1,
		s1' = s1 + 1,
		l136' = l136 - 1,
		l490' = l490 + 1;

	l137 >= 1, s36 >= 1 ->
		s36' = s36 - 1,
		s1' = s1 + 1,
		l137' = l137 - 1,
		l490' = l490 + 1;

	l122 >= 1, s37 >= 1 ->
		s37' = s37 - 1,
		s1' = s1 + 1,
		l122' = l122 - 1,
		l489' = l489 + 1;

	l136 >= 1, s38 >= 1 ->
		s38' = s38 - 1,
		s1' = s1 + 1,
		l136' = l136 - 1,
		l492' = l492 + 1;

	l137 >= 1, s39 >= 1 ->
		s39' = s39 - 1,
		s1' = s1 + 1,
		l137' = l137 - 1,
		l492' = l492 + 1;

init
	l0 >= 1, s0 = 1, s1 = 0, s2 = 0, s3 = 0, s4 = 0, s5 = 0, s6 = 0, s7 = 0, s8 = 0, s9 = 0, s10 = 0, s11 = 0, s12 = 0, s13 = 0, s14 = 0, s15 = 0, s16 = 0, s17 = 0, s18 = 0, s19 = 0, s20 = 0, s21 = 0, s22 = 0, s23 = 0, s24 = 0, s25 = 0, s26 = 0, s27 = 0, s28 = 0, s29 = 0, s30 = 0, s31 = 0, s32 = 0, s33 = 0, s34 = 0, s35 = 0, s36 = 0, s37 = 0, s38 = 0, s39 = 0, l1 = 0, l2 = 0, l3 = 0, l4 = 0, l5 = 0, l6 = 0, l7 = 0, l8 = 0, l9 = 0, l10 = 0, l11 = 0, l12 = 0, l13 = 0, l14 = 0, l15 = 0, l16 = 0, l17 = 0, l18 = 0, l19 = 0, l20 = 0, l21 = 0, l22 = 0, l23 = 0, l24 = 0, l25 = 0, l26 = 0, l27 = 0, l28 = 0, l29 = 0, l30 = 0, l31 = 0, l32 = 0, l33 = 0, l34 = 0, l35 = 0, l36 = 0, l37 = 0, l38 = 0, l39 = 0, l40 = 0, l41 = 0, l42 = 0, l43 = 0, l44 = 0, l45 = 0, l46 = 0, l47 = 0, l48 = 0, l49 = 0, l50 = 0, l51 = 0, l52 = 0, l53 = 0, l54 = 0, l55 = 0, l56 = 0, l57 = 0, l58 = 0, l59 = 0, l60 = 0, l61 = 0, l62 = 0, l63 = 0, l64 = 0, l65 = 0, l66 = 0, l67 = 0, l68 = 0, l69 = 0, l70 = 0, l71 = 0, l72 = 0, l73 = 0, l74 = 0, l75 = 0, l76 = 0, l77 = 0, l78 = 0, l79 = 0, l80 = 0, l81 = 0, l82 = 0, l83 = 0, l84 = 0, l85 = 0, l86 = 0, l87 = 0, l88 = 0, l89 = 0, l90 = 0, l91 = 0, l92 = 0, l93 = 0, l94 = 0, l95 = 0, l96 = 0, l97 = 0, l98 = 0, l99 = 0, l100 = 0, l101 = 0, l102 = 0, l103 = 0, l104 = 0, l105 = 0, l106 = 0, l107 = 0, l108 = 0, l109 = 0, l110 = 0, l111 = 0, l112 = 0, l113 = 0, l114 = 0, l115 = 0, l116 = 0, l117 = 0, l118 = 0, l119 = 0, l120 = 0, l121 = 0, l122 = 0, l123 = 0, l124 = 0, l125 = 0, l126 = 0, l127 = 0, l128 = 0, l129 = 0, l130 = 0, l131 = 0, l132 = 0, l133 = 0, l134 = 0, l135 = 0, l136 = 0, l137 = 0, l138 = 0, l139 = 0, l140 = 0, l141 = 0, l142 = 0, l143 = 0, l144 = 0, l145 = 0, l146 = 0, l147 = 0, l148 = 0, l149 = 0, l150 = 0, l151 = 0, l152 = 0, l153 = 0, l154 = 0, l155 = 0, l156 = 0, l157 = 0, l158 = 0, l159 = 0, l160 = 0, l161 = 0, l162 = 0, l163 = 0, l164 = 0, l165 = 0, l166 = 0, l167 = 0, l168 = 0, l169 = 0, l170 = 0, l171 = 0, l172 = 0, l173 = 0, l174 = 0, l175 = 0, l176 = 0, l177 = 0, l178 = 0, l179 = 0, l180 = 0, l181 = 0, l182 = 0, l183 = 0, l184 = 0, l185 = 0, l186 = 0, l187 = 0, l188 = 0, l189 = 0, l190 = 0, l191 = 0, l192 = 0, l193 = 0, l194 = 0, l195 = 0, l196 = 0, l197 = 0, l198 = 0, l199 = 0, l200 = 0, l201 = 0, l202 = 0, l203 = 0, l204 = 0, l205 = 0, l206 = 0, l207 = 0, l208 = 0, l209 = 0, l210 = 0, l211 = 0, l212 = 0, l213 = 0, l214 = 0, l215 = 0, l216 = 0, l217 = 0, l218 = 0, l219 = 0, l220 = 0, l221 = 0, l222 = 0, l223 = 0, l224 = 0, l225 = 0, l226 = 0, l227 = 0, l228 = 0, l229 = 0, l230 = 0, l231 = 0, l232 = 0, l233 = 0, l234 = 0, l235 = 0, l236 = 0, l237 = 0, l238 = 0, l239 = 0, l240 = 0, l241 = 0, l242 = 0, l243 = 0, l244 = 0, l245 = 0, l246 = 0, l247 = 0, l248 = 0, l249 = 0, l250 = 0, l251 = 0, l252 = 0, l253 = 0, l254 = 0, l255 = 0, l256 = 0, l257 = 0, l258 = 0, l259 = 0, l260 = 0, l261 = 0, l262 = 0, l263 = 0, l264 = 0, l265 = 0, l266 = 0, l267 = 0, l268 = 0, l269 = 0, l270 = 0, l271 = 0, l272 = 0, l273 = 0, l274 = 0, l275 = 0, l276 = 0, l277 = 0, l278 = 0, l279 = 0, l280 = 0, l281 = 0, l282 = 0, l283 = 0, l284 = 0, l285 = 0, l286 = 0, l287 = 0, l288 = 0, l289 = 0, l290 = 0, l291 = 0, l292 = 0, l293 = 0, l294 = 0, l295 = 0, l296 = 0, l297 = 0, l298 = 0, l299 = 0, l300 = 0, l301 = 0, l302 = 0, l303 = 0, l304 = 0, l305 = 0, l306 = 0, l307 = 0, l308 = 0, l309 = 0, l310 = 0, l311 = 0, l312 = 0, l313 = 0, l314 = 0, l315 = 0, l316 = 0, l317 = 0, l318 = 0, l319 = 0, l320 = 0, l321 = 0, l322 = 0, l323 = 0, l324 = 0, l325 = 0, l326 = 0, l327 = 0, l328 = 0, l329 = 0, l330 = 0, l331 = 0, l332 = 0, l333 = 0, l334 = 0, l335 = 0, l336 = 0, l337 = 0, l338 = 0, l339 = 0, l340 = 0, l341 = 0, l342 = 0, l343 = 0, l344 = 0, l345 = 0, l346 = 0, l347 = 0, l348 = 0, l349 = 0, l350 = 0, l351 = 0, l352 = 0, l353 = 0, l354 = 0, l355 = 0, l356 = 0, l357 = 0, l358 = 0, l359 = 0, l360 = 0, l361 = 0, l362 = 0, l363 = 0, l364 = 0, l365 = 0, l366 = 0, l367 = 0, l368 = 0, l369 = 0, l370 = 0, l371 = 0, l372 = 0, l373 = 0, l374 = 0, l375 = 0, l376 = 0, l377 = 0, l378 = 0, l379 = 0, l380 = 0, l381 = 0, l382 = 0, l383 = 0, l384 = 0, l385 = 0, l386 = 0, l387 = 0, l388 = 0, l389 = 0, l390 = 0, l391 = 0, l392 = 0, l393 = 0, l394 = 0, l395 = 0, l396 = 0, l397 = 0, l398 = 0, l399 = 0, l400 = 0, l401 = 0, l402 = 0, l403 = 0, l404 = 0, l405 = 0, l406 = 0, l407 = 0, l408 = 0, l409 = 0, l410 = 0, l411 = 0, l412 = 0, l413 = 0, l414 = 0, l415 = 0, l416 = 0, l417 = 0, l418 = 0, l419 = 0, l420 = 0, l421 = 0, l422 = 0, l423 = 0, l424 = 0, l425 = 0, l426 = 0, l427 = 0, l428 = 0, l429 = 0, l430 = 0, l431 = 0, l432 = 0, l433 = 0, l434 = 0, l435 = 0, l436 = 0, l437 = 0, l438 = 0, l439 = 0, l440 = 0, l441 = 0, l442 = 0, l443 = 0, l444 = 0, l445 = 0, l446 = 0, l447 = 0, l448 = 0, l449 = 0, l450 = 0, l451 = 0, l452 = 0, l453 = 0, l454 = 0, l455 = 0, l456 = 0, l457 = 0, l458 = 0, l459 = 0, l460 = 0, l461 = 0, l462 = 0, l463 = 0, l464 = 0, l465 = 0, l466 = 0, l467 = 0, l468 = 0, l469 = 0, l470 = 0, l471 = 0, l472 = 0, l473 = 0, l474 = 0, l475 = 0, l476 = 0, l477 = 0, l478 = 0, l479 = 0, l480 = 0, l481 = 0, l482 = 0, l483 = 0, l484 = 0, l485 = 0, l486 = 0, l487 = 0, l488 = 0, l489 = 0, l490 = 0, l491 = 0, l492 = 0, l493 = 0, l494 = 0, l495 = 0, l496 = 0, l497 = 0, l498 = 0, l499 = 0, l500 = 0, l501 = 0, l502 = 0, l503 = 0, l504 = 0, l505 = 0, l506 = 0, l507 = 0, l508 = 0, l509 = 0, l510 = 0, l511 = 0, l512 = 0

target
	s2 >= 1, l512 >= 2


