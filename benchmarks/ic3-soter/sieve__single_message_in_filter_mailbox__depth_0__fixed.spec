vars
	s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46 l47 l48 l49 l50 l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l61 l62 l63 l64 l65 l66 l67 l68 l69 l70 l71 l72 l73 l74 l75 l76 l77 l78 l79 l80 l81 l82 l83 l84 l85 l86 l87 l88 l89 l90 l91 l92 l93 l94 l95 l96 l97 l98 l99 l100 l101 l102 l103 l104 l105 l106 l107 l108 l109 l110 l111 l112 l113 l114 l115 l116 l117 l118 l119 l120 l121 l122 l123 l124 l125 l126 l127 l128 l129 l130 l131 l132 l133 l134 l135 l136 l137 l138 l139 l140 l141 l142 l143 l144 l145 l146 l147 l148 l149 l150 l151 l152 l153 l154 l155 l156 l157 l158 l159 l160 l161 l162 l163 l164 l165 l166 l167 l168 l169 l170 l171 l172 l173 l174 l175 l176 l177 l178 l179 l180 l181 l182 l183 l184 l185 l186 l187 l188 l189 l190 l191 l192 l193 l194 l195 l196 l197 l198 l199 l200 l201 l202 l203 l204 l205 l206 l207 l208 l209 l210 l211 l212 l213 l214 l215 l216 l217 l218 l219 l220 l221 l222 l223 l224 l225 l226 l227 l228 l229 l230 l231 l232 l233 l234 l235 l236 l237 l238 l239

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
		l15' = l15 + 1;

	l2 >= 1, s1 >= 1 ->
		l2' = l2 - 1,
		l3' = l3 + 1;

	l3 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s3' = s3 + 1,
		l3' = l3 - 1,
		l21' = l21 + 1;

	l4 >= 1, s1 >= 1 ->
		l4' = l4 - 1,
		l5' = l5 + 1;

	l5 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s4' = s4 + 1,
		l5' = l5 - 1,
		l25' = l25 + 1;

	l6 >= 1, s1 >= 1 ->
		l6' = l6 - 1,
		l7' = l7 + 1;

	l7 >= 1, s1 >= 1 ->
		l7' = l7 - 1,
		l29' = l29 + 1;

	l8 >= 1, s1 >= 1 ->
		l8' = l8 - 1,
		l9' = l9 + 1;

	l9 >= 1, s1 >= 1 ->
		l9' = l9 - 1,
		l29' = l29 + 1;

	l10 >= 1, s1 >= 1 ->
		l10' = l10 - 1,
		l11' = l11 + 1;

	l11 >= 1, s1 >= 1 ->
		l11' = l11 - 1,
		l28' = l28 + 1;

	l12 >= 1, s1 >= 1 ->
		l12' = l12 - 1,
		l13' = l13 + 1;

	l13 >= 1, s1 >= 1 ->
		l13' = l13 - 1,
		l8' = l8 + 1;

	l14 >= 1, s1 >= 1 ->
		l14' = l14 - 1,
		l6' = l6 + 1;

	l15 >= 1, s1 >= 1 ->
		l15' = l15 - 1,
		l10' = l10 + 1;

	l16 >= 1, s1 >= 1 ->
		l16' = l16 - 1,
		l4' = l4 + 1;

	l17 >= 1, s1 >= 1 ->
		l17' = l17 - 1,
		l2' = l2 + 1;

	l18 >= 1, s1 >= 1 ->
		l18' = l18 - 1,
		l19' = l19 + 1;

	l19 >= 1, s1 >= 1 ->
		l19' = l19 - 1,
		l31' = l31 + 1;

	l20 >= 1, s1 >= 1 ->
		l20' = l20 - 1,
		l32' = l32 + 1;

	l21 >= 1, s1 >= 1 ->
		l21' = l21 - 1,
		l106' = l106 + 1;

	l22 >= 1, s1 >= 1 ->
		l22' = l22 - 1,
		l23' = l23 + 1;

	l23 >= 1, s1 >= 1 ->
		l23' = l23 - 1,
		l17' = l17 + 1;

	l24 >= 1, s1 >= 1 ->
		l24' = l24 - 1,
		l14' = l14 + 1;

	l25 >= 1, s1 >= 1 ->
		l25' = l25 - 1,
		l58' = l58 + 1;

	l26 >= 1, s1 >= 1 ->
		l26' = l26 - 1,
		l27' = l27 + 1;

	l27 >= 1, s1 >= 1 ->
		l27' = l27 - 1,
		l16' = l16 + 1;

	l28 >= 1, s1 >= 1 ->
		l28' = l28 - 1,
		l18' = l18 + 1;

	l29 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s5' = s5 + 1,
		l29' = l29 - 1,
		l0' = l0 + 1;

	l30 >= 1, s1 >= 1 ->
		l30' = l30 - 1,
		l12' = l12 + 1;

	l31 >= 1, s1 >= 1 ->
		l31' = l31 - 1,
		l22' = l22 + 1;

	l32 >= 1, s1 >= 1 ->
		l32' = l32 - 1,
		l26' = l26 + 1;

	l34 >= 1, s1 >= 1 ->
		l34' = l34 - 1,
		l35' = l35 + 1;

	l35 >= 1, s1 >= 1 ->
		l35' = l35 - 1,
		l43' = l43 + 1;

	l36 >= 1, s1 >= 1 ->
		l36' = l36 - 1,
		l37' = l37 + 1;

	l37 >= 1, s1 >= 1 ->
		l37' = l37 - 1,
		l38' = l38 + 1;

	l38 >= 1, s1 >= 1 ->
		l38' = l38 - 1,
		l39' = l39 + 1;

	l39 >= 1, s1 >= 1 ->
		l39' = l39 - 1,
		l87' = l87 + 1;

	l40 >= 1, s1 >= 1 ->
		l40' = l40 - 1,
		l41' = l41 + 1;

	l40 >= 1, s1 >= 1 ->
		l40' = l40 - 1,
		l42' = l42 + 1;

	l41 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s6' = s6 + 1,
		l41' = l41 - 1,
		l33' = l33 + 1;

	l42 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s7' = s7 + 1,
		l42' = l42 - 1,
		l33' = l33 + 1;

	l43 >= 1, s1 >= 1 ->
		l43' = l43 - 1,
		l44' = l44 + 1;

	l44 >= 1, s1 >= 1 ->
		l44' = l44 - 1,
		l87' = l87 + 1;

	l45 >= 1, s1 >= 1 ->
		l45' = l45 - 1,
		l46' = l46 + 1;

	l46 >= 1, s1 >= 1 ->
		l46' = l46 - 1,
		l40' = l40 + 1;

	l47 >= 1, s1 >= 1 ->
		l47' = l47 - 1,
		l48' = l48 + 1;

	l47 >= 1, s1 >= 1 ->
		l47' = l47 - 1,
		l49' = l49 + 1;

	l48 >= 1, s1 >= 1 ->
		l48' = l48 - 1,
		l64' = l64 + 1;

	l49 >= 1, s1 >= 1 ->
		l49' = l49 - 1,
		l66' = l66 + 1;

	l50 >= 1, s1 >= 1 ->
		l50' = l50 - 1,
		l51' = l51 + 1;

	l51 >= 1, s1 >= 1 ->
		l51' = l51 - 1,
		l52' = l52 + 1;

	l52 >= 1, s1 >= 1 ->
		l52' = l52 - 1,
		l53' = l53 + 1;

	l53 >= 1, s1 >= 1 ->
		l53' = l53 - 1,
		l90' = l90 + 1;

	l54 >= 1, s1 >= 1 ->
		l54' = l54 - 1,
		l55' = l55 + 1;

	l55 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s8' = s8 + 1,
		l55' = l55 - 1,
		l79' = l79 + 1;

	l56 >= 1, s1 >= 1 ->
		l56' = l56 - 1,
		l57' = l57 + 1;

	l57 >= 1, s1 >= 1 ->
		l57' = l57 - 1,
		l34' = l34 + 1;

	l58 >= 1, s1 >= 1 ->
		l58' = l58 - 1,
		l59' = l59 + 1;

	l59 >= 1, s1 >= 1 ->
		l59' = l59 - 1,
		l36' = l36 + 1;

	l60 >= 1, s1 >= 1 ->
		l60' = l60 - 1,
		l50' = l50 + 1;

	l61 >= 1, s1 >= 1 ->
		l61' = l61 - 1,
		l56' = l56 + 1;

	l62 >= 1, s1 >= 1 ->
		l62' = l62 - 1,
		l63' = l63 + 1;

	l63 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s9' = s9 + 1,
		l63' = l63 - 1,
		l0' = l0 + 1;

	l64 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s10' = s10 + 1,
		l64' = l64 - 1,
		l65' = l65 + 1;

	l66 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s11' = s11 + 1,
		l66' = l66 - 1,
		l67' = l67 + 1;

	l68 >= 1, s1 >= 1 ->
		l68' = l68 - 1,
		l69' = l69 + 1;

	l69 >= 1, s1 >= 1 ->
		l69' = l69 - 1,
		l80' = l80 + 1;

	l70 >= 1, s1 >= 1 ->
		l70' = l70 - 1,
		l69' = l69 + 1;

	l71 >= 1, s1 >= 1 ->
		l71' = l71 - 1,
		l47' = l47 + 1;

	l72 >= 1, s1 >= 1 ->
		l72' = l72 - 1,
		l45' = l45 + 1;

	l73 >= 1, s1 >= 1 ->
		l73' = l73 - 1,
		l54' = l54 + 1;

	l74 >= 1, s1 >= 1 ->
		l74' = l74 - 1,
		l75' = l75 + 1;

	l75 >= 1, s1 >= 1 ->
		l75' = l75 - 1,
		l85' = l85 + 1;

	l76 >= 1, s1 >= 1 ->
		l76' = l76 - 1,
		l77' = l77 + 1;

	l77 >= 1, s1 >= 1 ->
		l77' = l77 - 1,
		l84' = l84 + 1;

	l78 >= 1, s1 >= 1 ->
		l78' = l78 - 1,
		l61' = l61 + 1;

	l79 >= 1, s1 >= 1 ->
		l79' = l79 - 1,
		l199' = l199 + 1;

	l80 >= 1, s1 >= 1 ->
		l80' = l80 - 1,
		l81' = l81 + 1;

	l81 >= 1, s1 >= 1 ->
		l81' = l81 - 1,
		l73' = l73 + 1;

	l82 >= 1, s1 >= 1 ->
		l82' = l82 - 1,
		l83' = l83 + 1;

	l83 >= 1, s1 >= 1 ->
		l83' = l83 - 1,
		l76' = l76 + 1;

	l84 >= 1, s1 >= 1 ->
		l84' = l84 - 1,
		l60' = l60 + 1;

	l85 >= 1, s1 >= 1 ->
		l85' = l85 - 1,
		l71' = l71 + 1;

	l86 >= 1, s1 >= 1 ->
		l86' = l86 - 1,
		l72' = l72 + 1;

	l87 >= 1, s1 >= 1 ->
		l87' = l87 - 1,
		l82' = l82 + 1;

	l88 >= 1, s1 >= 1 ->
		l88' = l88 - 1,
		l74' = l74 + 1;

	l90 >= 1, s1 >= 1 ->
		l90' = l90 - 1,
		l91' = l91 + 1;

	l91 >= 1, s1 >= 1 ->
		l91' = l91 - 1,
		l88' = l88 + 1;

	l92 >= 1, s1 >= 1 ->
		l92' = l92 - 1,
		l93' = l93 + 1;

	l92 >= 1, s1 >= 1 ->
		l92' = l92 - 1,
		l94' = l94 + 1;

	l93 >= 1, s1 >= 1 ->
		l93' = l93 - 1,
		l112' = l112 + 1;

	l94 >= 1, s1 >= 1 ->
		l94' = l94 - 1,
		l113' = l113 + 1;

	l95 >= 1, s1 >= 1 ->
		l95' = l95 - 1,
		l96' = l96 + 1;

	l95 >= 1, s1 >= 1 ->
		l95' = l95 - 1,
		l97' = l97 + 1;

	l96 >= 1, s1 >= 1 ->
		l96' = l96 - 1,
		l116' = l116 + 1;

	l97 >= 1, s1 >= 1 ->
		l97' = l97 - 1,
		l116' = l116 + 1;

	l98 >= 1, s1 >= 1 ->
		l98' = l98 - 1,
		l99' = l99 + 1;

	l99 >= 1, s1 >= 1 ->
		l99' = l99 - 1,
		l100' = l100 + 1;

	l100 >= 1, s1 >= 1 ->
		l100' = l100 - 1,
		l101' = l101 + 1;

	l101 >= 1, s1 >= 1 ->
		l101' = l101 - 1,
		l129' = l129 + 1;

	l102 >= 1, s1 >= 1 ->
		l102' = l102 - 1,
		l103' = l103 + 1;

	l103 >= 1, s1 >= 1 ->
		l103' = l103 - 1,
		l115' = l115 + 1;

	l104 >= 1, s1 >= 1 ->
		l104' = l104 - 1,
		l105' = l105 + 1;

	l105 >= 1, s1 >= 1 ->
		l105' = l105 - 1,
		l102' = l102 + 1;

	l106 >= 1, s1 >= 1 ->
		l106' = l106 - 1,
		l107' = l107 + 1;

	l107 >= 1, s1 >= 1 ->
		l107' = l107 - 1,
		l117' = l117 + 1;

	l108 >= 1, s1 >= 1 ->
		l108' = l108 - 1,
		l98' = l98 + 1;

	l109 >= 1, s1 >= 1 ->
		l109' = l109 - 1,
		l104' = l104 + 1;

	l110 >= 1, s1 >= 1 ->
		l110' = l110 - 1,
		l111' = l111 + 1;

	l111 >= 1, s1 >= 1 ->
		l111' = l111 - 1,
		l121' = l121 + 1;

	l112 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s12' = s12 + 1,
		l112' = l112 - 1,
		l89' = l89 + 1;

	l113 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s13' = s13 + 1,
		l113' = l113 - 1,
		l114' = l114 + 1;

	l115 >= 1, s1 >= 1 ->
		l115' = l115 - 1,
		l123' = l123 + 1;

	l116 >= 1, s1 >= 1 ->
		l116' = l116 - 1,
		l109' = l109 + 1;

	l117 >= 1, s1 >= 1 ->
		l117' = l117 - 1,
		l115' = l115 + 1;

	l118 >= 1, s1 >= 1 ->
		l118' = l118 - 1,
		l92' = l92 + 1;

	l119 >= 1, s1 >= 1 ->
		l119' = l119 - 1,
		l120' = l120 + 1;

	l120 >= 1, s1 >= 1 ->
		l120' = l120 - 1,
		l125' = l125 + 1;

	l121 >= 1, s1 >= 1 ->
		l121' = l121 - 1,
		l122' = l122 + 1;

	l122 >= 1, s1 >= 1 ->
		l122' = l122 - 1,
		l95' = l95 + 1;

	l123 >= 1, s1 >= 1 ->
		l123' = l123 - 1,
		l124' = l124 + 1;

	l124 >= 1, s1 >= 1 ->
		l124' = l124 - 1,
		l119' = l119 + 1;

	l125 >= 1, s1 >= 1 ->
		l125' = l125 - 1,
		l108' = l108 + 1;

	l126 >= 1, s1 >= 1 ->
		l126' = l126 - 1,
		l118' = l118 + 1;

	l127 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s14' = s14 + 1,
		l127' = l127 - 1,
		l0' = l0 + 1;

	l127 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s15' = s15 + 1,
		l127' = l127 - 1,
		l0' = l0 + 1;

	l129 >= 1, s1 >= 1 ->
		l129' = l129 - 1,
		l130' = l130 + 1;

	l130 >= 1, s1 >= 1 ->
		l130' = l130 - 1,
		l127' = l127 + 1;

	l131 >= 1, s1 >= 1 ->
		l131' = l131 - 1,
		l132' = l132 + 1;

	l131 >= 1, s1 >= 1 ->
		l131' = l131 - 1,
		l133' = l133 + 1;

	l132 >= 1, s1 >= 1 ->
		l132' = l132 - 1,
		l232' = l232 + 1;

	l133 >= 1, s1 >= 1 ->
		l133' = l133 - 1,
		l232' = l232 + 1;

	l134 >= 1, s1 >= 1 ->
		l134' = l134 - 1,
		l135' = l135 + 1;

	l134 >= 1, s1 >= 1 ->
		l134' = l134 - 1,
		l136' = l136 + 1;

	l135 >= 1, s1 >= 1 ->
		l135' = l135 - 1,
		l232' = l232 + 1;

	l136 >= 1, s1 >= 1 ->
		l136' = l136 - 1,
		l232' = l232 + 1;

	l137 >= 1, s1 >= 1 ->
		l137' = l137 - 1,
		l138' = l138 + 1;

	l137 >= 1, s1 >= 1 ->
		l137' = l137 - 1,
		l139' = l139 + 1;

	l138 >= 1, s1 >= 1 ->
		l138' = l138 - 1,
		l212' = l212 + 1;

	l139 >= 1, s1 >= 1 ->
		l139' = l139 - 1,
		l212' = l212 + 1;

	l140 >= 1, s1 >= 1 ->
		l140' = l140 - 1,
		l141' = l141 + 1;

	l140 >= 1, s1 >= 1 ->
		l140' = l140 - 1,
		l142' = l142 + 1;

	l141 >= 1, s1 >= 1 ->
		l141' = l141 - 1,
		l213' = l213 + 1;

	l142 >= 1, s1 >= 1 ->
		l142' = l142 - 1,
		l213' = l213 + 1;

	l143 >= 1, s1 >= 1 ->
		l143' = l143 - 1,
		l144' = l144 + 1;

	l143 >= 1, s1 >= 1 ->
		l143' = l143 - 1,
		l145' = l145 + 1;

	l144 >= 1, s1 >= 1 ->
		l144' = l144 - 1,
		l131' = l131 + 1;

	l145 >= 1, s1 >= 1 ->
		l145' = l145 - 1,
		l134' = l134 + 1;

	l146 >= 1, s1 >= 1 ->
		l146' = l146 - 1,
		l147' = l147 + 1;

	l146 >= 1, s1 >= 1 ->
		l146' = l146 - 1,
		l148' = l148 + 1;

	l147 >= 1, s1 >= 1 ->
		l147' = l147 - 1,
		l205' = l205 + 1;

	l148 >= 1, s1 >= 1 ->
		l148' = l148 - 1,
		l206' = l206 + 1;

	l149 >= 1, s1 >= 1 ->
		l149' = l149 - 1,
		l150' = l150 + 1;

	l149 >= 1, s1 >= 1 ->
		l149' = l149 - 1,
		l151' = l151 + 1;

	l150 >= 1, s1 >= 1 ->
		l150' = l150 - 1,
		l232' = l232 + 1;

	l151 >= 1, s1 >= 1 ->
		l151' = l151 - 1,
		l232' = l232 + 1;

	l152 >= 1, s1 >= 1 ->
		l152' = l152 - 1,
		l153' = l153 + 1;

	l152 >= 1, s1 >= 1 ->
		l152' = l152 - 1,
		l154' = l154 + 1;

	l153 >= 1, s1 >= 1 ->
		l153' = l153 - 1,
		l232' = l232 + 1;

	l154 >= 1, s1 >= 1 ->
		l154' = l154 - 1,
		l232' = l232 + 1;

	l155 >= 1, s1 >= 1 ->
		l155' = l155 - 1,
		l156' = l156 + 1;

	l155 >= 1, s1 >= 1 ->
		l155' = l155 - 1,
		l157' = l157 + 1;

	l156 >= 1, s1 >= 1 ->
		l156' = l156 - 1,
		l233' = l233 + 1;

	l157 >= 1, s1 >= 1 ->
		l157' = l157 - 1,
		l233' = l233 + 1;

	l158 >= 1, s1 >= 1 ->
		l158' = l158 - 1,
		l159' = l159 + 1;

	l159 >= 1, s1 >= 1 ->
		l159' = l159 - 1,
		l143' = l143 + 1;

	l160 >= 1, s1 >= 1 ->
		l160' = l160 - 1,
		l161' = l161 + 1;

	l160 >= 1, s1 >= 1 ->
		l160' = l160 - 1,
		l162' = l162 + 1;

	l161 >= 1, s1 >= 1 ->
		l161' = l161 - 1,
		l233' = l233 + 1;

	l162 >= 1, s1 >= 1 ->
		l162' = l162 - 1,
		l233' = l233 + 1;

	l163 >= 1, s1 >= 1 ->
		l163' = l163 - 1,
		l164' = l164 + 1;

	l163 >= 1, s1 >= 1 ->
		l163' = l163 - 1,
		l165' = l165 + 1;

	l164 >= 1, s1 >= 1 ->
		l164' = l164 - 1,
		l149' = l149 + 1;

	l165 >= 1, s1 >= 1 ->
		l165' = l165 - 1,
		l152' = l152 + 1;

	l166 >= 1, s1 >= 1 ->
		l166' = l166 - 1,
		l167' = l167 + 1;

	l166 >= 1, s1 >= 1 ->
		l166' = l166 - 1,
		l168' = l168 + 1;

	l167 >= 1, s1 >= 1 ->
		l167' = l167 - 1,
		l209' = l209 + 1;

	l168 >= 1, s1 >= 1 ->
		l168' = l168 - 1,
		l210' = l210 + 1;

	l169 >= 1, s1 >= 1 ->
		l169' = l169 - 1,
		l170' = l170 + 1;

	l170 >= 1, s1 >= 1 ->
		l170' = l170 - 1,
		l225' = l225 + 1;

	l171 >= 1, s1 >= 1 ->
		l171' = l171 - 1,
		l172' = l172 + 1;

	l172 >= 1, s1 >= 1 ->
		l172' = l172 - 1,
		l160' = l160 + 1;

	l173 >= 1, s1 >= 1 ->
		l173' = l173 - 1,
		l174' = l174 + 1;

	l174 >= 1, s1 >= 1 ->
		l174' = l174 - 1,
		l163' = l163 + 1;

	l175 >= 1, s1 >= 1 ->
		l175' = l175 - 1,
		l176' = l176 + 1;

	l176 >= 1, s1 >= 1 ->
		l176' = l176 - 1,
		l140' = l140 + 1;

	l177 >= 1, s1 >= 1 ->
		l177' = l177 - 1,
		l178' = l178 + 1;

	l178 >= 1, s1 >= 1 ->
		l178' = l178 - 1,
		l179' = l179 + 1;

	l179 >= 1, s1 >= 1 ->
		l179' = l179 - 1,
		l180' = l180 + 1;

	l180 >= 1, s1 >= 1 ->
		l180' = l180 - 1,
		l236' = l236 + 1;

	l181 >= 1, s1 >= 1 ->
		l181' = l181 - 1,
		l182' = l182 + 1;

	l182 >= 1, s1 >= 1 ->
		l182' = l182 - 1,
		l155' = l155 + 1;

	l183 >= 1, s1 >= 1 ->
		l183' = l183 - 1,
		l184' = l184 + 1;

	l184 >= 1, s1 >= 1 ->
		l184' = l184 - 1,
		l137' = l137 + 1;

	l185 >= 1, s1 >= 1 ->
		l185' = l185 - 1,
		l186' = l186 + 1;

	l186 >= 1, s1 >= 1 ->
		l186' = l186 - 1,
		l181' = l181 + 1;

	l187 >= 1, s1 >= 1 ->
		l187' = l187 - 1,
		l188' = l188 + 1;

	l188 >= 1, s1 >= 1 ->
		l188' = l188 - 1,
		l171' = l171 + 1;

	l189 >= 1, s1 >= 1 ->
		l189' = l189 - 1,
		l190' = l190 + 1;

	l190 >= 1, s1 >= 1 ->
		l190' = l190 - 1,
		l158' = l158 + 1;

	l191 >= 1, s1 >= 1 ->
		l191' = l191 - 1,
		l192' = l192 + 1;

	l192 >= 1, s1 >= 1 ->
		l192' = l192 - 1,
		l173' = l173 + 1;

	l193 >= 1, s1 >= 1 ->
		l193' = l193 - 1,
		l194' = l194 + 1;

	l194 >= 1, s1 >= 1 ->
		l194' = l194 - 1,
		l203' = l203 + 1;

	l194 >= 1, s1 >= 1 ->
		l194' = l194 - 1,
		l220' = l220 + 1;

	l194 >= 1, s1 >= 1 ->
		l194' = l194 - 1,
		l231' = l231 + 1;

	l195 >= 1, s1 >= 1 ->
		l195' = l195 - 1,
		l194' = l194 + 1;

	l196 >= 1, s1 >= 1 ->
		l196' = l196 - 1,
		l169' = l169 + 1;

	l197 >= 1, s1 >= 1 ->
		l197' = l197 - 1,
		l175' = l175 + 1;

	l198 >= 1, s1 >= 1 ->
		l198' = l198 - 1,
		l177' = l177 + 1;

	l199 >= 1, s1 >= 1 ->
		l199' = l199 - 1,
		l183' = l183 + 1;

	l200 >= 1, s1 >= 1 ->
		l200' = l200 - 1,
		l187' = l187 + 1;

	l201 >= 1, s1 >= 1 ->
		l201' = l201 - 1,
		l185' = l185 + 1;

	l202 >= 1, s1 >= 1 ->
		l202' = l202 - 1,
		l189' = l189 + 1;

	l203 >= 1, s1 >= 1 ->
		l203' = l203 - 1,
		l191' = l191 + 1;

	l204 >= 1, s1 >= 1 ->
		l204' = l204 - 1,
		l200' = l200 + 1;

	l205 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s16' = s16 + 1,
		l205' = l205 - 1,
		l89' = l89 + 1;

	l206 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s17' = s17 + 1,
		l206' = l206 - 1,
		l114' = l114 + 1;

	l207 >= 1, s1 >= 1 ->
		l207' = l207 - 1,
		l208' = l208 + 1;

	l208 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s18' = s18 + 1,
		l208' = l208 - 1,
		l0' = l0 + 1;

	l209 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s19' = s19 + 1,
		l209' = l209 - 1,
		l128' = l128 + 1;

	l210 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s20' = s20 + 1,
		l210' = l210 - 1,
		l211' = l211 + 1;

	l212 >= 1, s1 >= 1 ->
		l212' = l212 - 1,
		l201' = l201 + 1;

	l213 >= 1, s1 >= 1 ->
		l213' = l213 - 1,
		l226' = l226 + 1;

	l214 >= 1, s1 >= 1 ->
		l214' = l214 - 1,
		l166' = l166 + 1;

	l215 >= 1, s1 >= 1 ->
		l215' = l215 - 1,
		l146' = l146 + 1;

	l216 >= 1, s1 >= 1 ->
		l216' = l216 - 1,
		l217' = l217 + 1;

	l217 >= 1, s1 >= 1 ->
		l217' = l217 - 1,
		l229' = l229 + 1;

	l218 >= 1, s1 >= 1 ->
		l218' = l218 - 1,
		l219' = l219 + 1;

	l219 >= 1, s1 >= 1 ->
		l219' = l219 - 1,
		l230' = l230 + 1;

	l220 >= 1, s1 >= 1 ->
		l220' = l220 - 1,
		l221' = l221 + 1;

	l222 >= 1, s1 >= 1 ->
		l222' = l222 - 1,
		l223' = l223 + 1;

	l223 >= 1, s1 >= 1 ->
		l223' = l223 - 1,
		l193' = l193 + 1;

	l223 >= 1, s1 >= 1 ->
		l223' = l223 - 1,
		l195' = l195 + 1;

	l224 >= 1, s1 >= 1 ->
		l224' = l224 - 1,
		l222' = l222 + 1;

	l225 >= 1, s1 >= 1 ->
		l225' = l225 - 1,
		l224' = l224 + 1;

	l226 >= 1, s1 >= 1 ->
		l226' = l226 - 1,
		l196' = l196 + 1;

	l227 >= 1, s1 >= 1 ->
		l227' = l227 - 1,
		l228' = l228 + 1;

	l228 >= 1, s1 >= 1 ->
		l228' = l228 - 1,
		l216' = l216 + 1;

	l229 >= 1, s1 >= 1 ->
		l229' = l229 - 1,
		l198' = l198 + 1;

	l230 >= 1, s1 >= 1 ->
		l230' = l230 - 1,
		l214' = l214 + 1;

	l231 >= 1, s1 >= 1 ->
		l231' = l231 - 1,
		l215' = l215 + 1;

	l232 >= 1, s1 >= 1 ->
		l232' = l232 - 1,
		l218' = l218 + 1;

	l233 >= 1, s1 >= 1 ->
		l233' = l233 - 1,
		l227' = l227 + 1;

	l234 >= 1, s1 >= 1 ->
		l234' = l234 - 1,
		l197' = l197 + 1;

	l235 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s21' = s21 + 1,
		l235' = l235 - 1,
		l0' = l0 + 1;

	l235 >= 1, s1 >= 1 ->
		s1' = s1 - 1,
		s22' = s22 + 1,
		l235' = l235 - 1,
		l0' = l0 + 1;

	l236 >= 1, s1 >= 1 ->
		l236' = l236 - 1,
		l237' = l237 + 1;

	l237 >= 1, s1 >= 1 ->
		l237' = l237 - 1,
		l235' = l235 + 1;

	l67 >= 1, s2 >= 1 ->
		l67' = l67 - 1,
		l239' = l239 + 1;

	l114 >= 1, s2 >= 1 ->
		l114' = l114 - 1,
		l239' = l239 + 1;

	l211 >= 1, s2 >= 1 ->
		l211' = l211 - 1,
		l239' = l239 + 1;

	l0 >= 1, s3 >= 1 ->
		s3' = s3 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l20' = l20 + 1;

	l0 >= 1, s4 >= 1 ->
		s4' = s4 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l24' = l24 + 1;

	l33 >= 1, s5 >= 1 ->
		s5' = s5 - 1,
		s1' = s1 + 1,
		l33' = l33 - 1,
		l30' = l30 + 1;

	l0 >= 1, s6 >= 1 ->
		s6' = s6 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l68' = l68 + 1;

	l0 >= 1, s7 >= 1 ->
		s7' = s7 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l70' = l70 + 1;

	l0 >= 1, s8 >= 1 ->
		s8' = s8 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l78' = l78 + 1;

	l89 >= 1, s9 >= 1 ->
		s9' = s9 - 1,
		s1' = s1 + 1,
		l89' = l89 - 1,
		l86' = l86 + 1;

	l0 >= 1, s10 >= 1 ->
		s10' = s10 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l62' = l62 + 1;

	l0 >= 1, s11 >= 1 ->
		s11' = s11 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l62' = l62 + 1;

	l0 >= 1, s12 >= 1 ->
		s12' = s12 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l110' = l110 + 1;

	l0 >= 1, s13 >= 1 ->
		s13' = s13 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l110' = l110 + 1;

	l65 >= 1, s14 >= 1 ->
		s14' = s14 - 1,
		s1' = s1 + 1,
		l65' = l65 - 1,
		l126' = l126 + 1;

	l128 >= 1, s15 >= 1 ->
		s15' = s15 - 1,
		s1' = s1 + 1,
		l128' = l128 - 1,
		l126' = l126 + 1;

	l0 >= 1, s16 >= 1 ->
		s16' = s16 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l204' = l204 + 1;

	l0 >= 1, s17 >= 1 ->
		s17' = s17 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l204' = l204 + 1;

	l114 >= 1, s18 >= 1 ->
		s18' = s18 - 1,
		s1' = s1 + 1,
		l114' = l114 - 1,
		l234' = l234 + 1;

	l0 >= 1, s19 >= 1 ->
		s19' = s19 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l207' = l207 + 1;

	l0 >= 1, s20 >= 1 ->
		s20' = s20 - 1,
		s1' = s1 + 1,
		l0' = l0 - 1,
		l207' = l207 + 1;

	l67 >= 1, s21 >= 1 ->
		s21' = s21 - 1,
		s1' = s1 + 1,
		l67' = l67 - 1,
		l202' = l202 + 1;

	l211 >= 1, s22 >= 1 ->
		s22' = s22 - 1,
		s1' = s1 + 1,
		l211' = l211 - 1,
		l202' = l202 + 1;

init
	l0 >= 1, s0 = 1, l169 = 0, l168 = 0, l167 = 0, l166 = 0, l165 = 0, l164 = 0, l163 = 0, l162 = 0, l161 = 0, l160 = 0, l78 = 0, l79 = 0, l72 = 0, l73 = 0, l70 = 0, l71 = 0, l76 = 0, l77 = 0, l74 = 0, l75 = 0, l87 = 0, l86 = 0, l85 = 0, l84 = 0, l83 = 0, l82 = 0, l81 = 0, l80 = 0, l152 = 0, l153 = 0, l150 = 0, l151 = 0, l156 = 0, l157 = 0, l89 = 0, l88 = 0, l171 = 0, l234 = 0, l6 = 0, l7 = 0, l4 = 0, l5 = 0, l2 = 0, l3 = 0, l1 = 0, l224 = 0, l8 = 0, l9 = 0, l94 = 0, l95 = 0, l96 = 0, l97 = 0, l90 = 0, l91 = 0, l92 = 0, l93 = 0, l98 = 0, l99 = 0, l239 = 0, l238 = 0, l201 = 0, l109 = 0, l225 = 0, l232 = 0, l18 = 0, l19 = 0, l14 = 0, l15 = 0, l16 = 0, l17 = 0, l10 = 0, l11 = 0, l12 = 0, l13 = 0, l108 = 0, l226 = 0, l208 = 0, l202 = 0, l203 = 0, s19 = 0, s18 = 0, l206 = 0, l207 = 0, l204 = 0, l205 = 0, s13 = 0, s12 = 0, s11 = 0, s10 = 0, s17 = 0, s16 = 0, s15 = 0, s14 = 0, l21 = 0, l20 = 0, l23 = 0, l22 = 0, l25 = 0, l24 = 0, l27 = 0, l26 = 0, l29 = 0, l28 = 0, l209 = 0, l145 = 0, l144 = 0, l147 = 0, l146 = 0, l141 = 0, l140 = 0, l143 = 0, l142 = 0, l149 = 0, l148 = 0, l235 = 0, l237 = 0, l219 = 0, l218 = 0, l236 = 0, l215 = 0, l214 = 0, l217 = 0, l216 = 0, l211 = 0, l210 = 0, l213 = 0, l212 = 0, l36 = 0, l37 = 0, l34 = 0, l35 = 0, l32 = 0, l33 = 0, l30 = 0, l31 = 0, l233 = 0, l38 = 0, l39 = 0, l231 = 0, l230 = 0, l222 = 0, l130 = 0, l131 = 0, l132 = 0, l133 = 0, l134 = 0, l135 = 0, l136 = 0, l137 = 0, l138 = 0, l139 = 0, l196 = 0, l197 = 0, l194 = 0, l195 = 0, l192 = 0, l193 = 0, l190 = 0, l191 = 0, l223 = 0, l198 = 0, l199 = 0, l43 = 0, l42 = 0, l41 = 0, l40 = 0, l47 = 0, l46 = 0, l45 = 0, l44 = 0, l49 = 0, l48 = 0, l123 = 0, l122 = 0, l121 = 0, l120 = 0, l127 = 0, l126 = 0, l125 = 0, l124 = 0, l129 = 0, l128 = 0, l181 = 0, l180 = 0, l183 = 0, l182 = 0, l185 = 0, l184 = 0, l187 = 0, l186 = 0, l189 = 0, l188 = 0, l158 = 0, l159 = 0, l220 = 0, l229 = 0, l221 = 0, l50 = 0, l51 = 0, s9 = 0, l53 = 0, l54 = 0, l55 = 0, l56 = 0, l57 = 0, s3 = 0, s2 = 0, s1 = 0, s7 = 0, s6 = 0, s5 = 0, s4 = 0, l118 = 0, l119 = 0, l116 = 0, l117 = 0, l114 = 0, l115 = 0, l112 = 0, l113 = 0, l110 = 0, l111 = 0, l227 = 0, l178 = 0, l179 = 0, l174 = 0, l175 = 0, l176 = 0, l177 = 0, l170 = 0, l52 = 0, l172 = 0, l173 = 0, s8 = 0, l154 = 0, l228 = 0, l200 = 0, l155 = 0, l65 = 0, l64 = 0, l67 = 0, l66 = 0, l61 = 0, l60 = 0, l63 = 0, l62 = 0, l69 = 0, l68 = 0, s22 = 0, l58 = 0, s20 = 0, s21 = 0, l59 = 0, l101 = 0, l100 = 0, l103 = 0, l102 = 0, l105 = 0, l104 = 0, l107 = 0, l106 = 0

target
	s2 >= 1, l239 >= 2


