vars
s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 l17 l18 l19 l20 l21 l22 l23 l24 l25 l26 l27 l28 l29 l30 l31 l32 l33 l34 l35 l36 l37 l38 l39 l40 l41 l42 l43 l44 l45 l46 l47 l48 l49 l50 l51 l52 l53 l54 l55 l56 l57 l58 l59 l60 l61 l62 l63 l64 l65 l66 l67 l68 l69 l70 l71 l72 

rules
l0>=1, s0>=1 -> 
	l0'=l0-1,
	l2'=l2+1;

l0>=1, s0>=1 -> 
	s0'=s0-1,
	s4'=s4+1,
	l0'=l0-1,
	l2'=l2+1;

l1>=1, s0>=1 -> 
	l1'=l1-1,
	l3'=l3+1;

l1>=1, s0>=1 -> 
	s0'=s0-1,
	s4'=s4+1,
	l1'=l1-1,
	l3'=l3+1;

l2>=1, s0>=1 -> 
	l2'=l2-1,
	l4'=l4+1;

l2>=1, s0>=1 -> 
	s0'=s0-1,
	s2'=s2+1,
	l2'=l2-1,
	l4'=l4+1;

l3>=1, s0>=1 -> 
	l3'=l3-1,
	l5'=l5+1;

l3>=1, s0>=1 -> 
	s0'=s0-1,
	s2'=s2+1,
	l3'=l3-1,
	l5'=l5+1;

l4>=1, s0>=1 -> 
	l4'=l4-1,
	l6'=l6+1;

l4>=1, s0>=1 -> 
	s0'=s0-1,
	s1'=s1+1,
	l4'=l4-1,
	l6'=l6+1;

l5>=1, s0>=1 -> 
	l5'=l5-1,
	l7'=l7+1;

l5>=1, s0>=1 -> 
	s0'=s0-1,
	s1'=s1+1,
	l5'=l5-1,
	l7'=l7+1;

l6>=1, s0>=1 -> 
	l6'=l6-1,
	l8'=l8+1;

l6>=1, s0>=1 -> 
	l6'=l6-1,
	l9'=l9+1;

l7>=1, s0>=1 -> 
	l7'=l7-1,
	l8'=l8+1;

l7>=1, s0>=1 -> 
	l7'=l7-1,
	l9'=l9+1;

l8>=1, s0>=1 -> 
	s0'=s0-1,
	s1'=s1+1,
	l8'=l8-1,
	l10'=l10+1;

l9>=1, s0>=1 -> 
	s0'=s0-1,
	s1'=s1+1,
	l9'=l9-1,
	l11'=l11+1;

l10>=1, s0>=1 -> 
	s0'=s0-1,
	s4'=s4+1,
	l10'=l10-1,
	l12'=l12+1;

l11>=1, s0>=1 -> 
	s0'=s0-1,
	s4'=s4+1,
	l11'=l11-1,
	l13'=l13+1;

l12>=1, s0>=1 -> 
	s0'=s0-1,
	s4'=s4+1,
	l12'=l12-1,
	l14'=l14+1;

l13>=1, s0>=1 -> 
	s0'=s0-1,
	s4'=s4+1,
	l13'=l13-1,
	l15'=l15+1;

l14>=1, s0>=1 -> 
	l14'=l14-1,
	l16'=l16+1;

l15>=1, s0>=1 -> 
	l15'=l15-1,
	l17'=l17+1;

l18>=1, s0>=1 -> 
	l18'=l18-1,
	l20'=l20+1;

l18>=1, s0>=1 -> 
	l18'=l18-1,
	l21'=l21+1;

l19>=1, s0>=1 -> 
	l19'=l19-1,
	l20'=l20+1;

l19>=1, s0>=1 -> 
	l19'=l19-1,
	l21'=l21+1;

l20>=1, s0>=1 -> 
	l20'=l20-1,
	l22'=l22+1;

l21>=1, s0>=1 -> 
	l21'=l21-1,
	l22'=l22+1;

l22>=1, s0>=1 -> 
	s0'=s0-1,
	s16'=s16+1,
	l22'=l22-1,
	l24'=l24+1;

l23>=1, s0>=1 -> 
	s0'=s0-1,
	s16'=s16+1,
	l23'=l23-1,
	l25'=l25+1;

l34>=1, s0>=1 -> 
	l34'=l34-1,
	l40'=l40+1;

l35>=1, s0>=1 -> 
	l35'=l35-1,
	l37'=l37+1;

l38>=1, s0>=1 -> 
	l38'=l38-1,
	l60'=l60+1;

l39>=1, s0>=1 -> 
	l39'=l39-1,
	l61'=l61+1;

l40>=1, s0>=1 -> 
	l40'=l40-1,
	l42'=l42+1;

l41>=1, s0>=1 -> 
	l41'=l41-1,
	l43'=l43+1;

l42>=1, s0>=1 -> 
	s0'=s0-1,
	s16'=s16+1,
	l42'=l42-1,
	l44'=l44+1;

l43>=1, s0>=1 -> 
	s0'=s0-1,
	s16'=s16+1,
	l43'=l43-1,
	l45'=l45+1;

l50>=1, s0>=1 -> 
	l50'=l50-1,
	l52'=l52+1;

l51>=1, s0>=1 -> 
	s0'=s0-1,
	s4'=s4+1,
	l51'=l51-1,
	l53'=l53+1;

l52>=1, s0>=1 -> 
	s0'=s0-1,
	s16'=s16+1,
	l52'=l52-1,
	l54'=l54+1;

l53>=1, s0>=1 -> 
	s0'=s0-1,
	s16'=s16+1,
	l53'=l53-1,
	l55'=l55+1;

l60>=1, s0>=1 -> 
	l60'=l60-1,
	l62'=l62+1;

l61>=1, s0>=1 -> 
	l61'=l61-1,
	l63'=l63+1;

l62>=1, s0>=1 -> 
	l62'=l62-1,
	l64'=l64+1;

l63>=1, s0>=1 -> 
	l63'=l63-1,
	l65'=l65+1;

l66>=1, s0>=1 -> 
	l66'=l66-1,
	l14'=l14+1;

l67>=1, s0>=1 -> 
	l67'=l67-1,
	l15'=l15+1;

l68>=1, s0>=1 -> 
	l68'=l68-1,
	l70'=l70+1;

l69>=1, s0>=1 -> 
	l69'=l69-1,
	l71'=l71+1;

l0>=1, s1>=1 -> 
	l0'=l0-1,
	l2'=l2+1;

l0>=1, s1>=1 -> 
	s1'=s1-1,
	s5'=s5+1,
	l0'=l0-1,
	l2'=l2+1;

l1>=1, s1>=1 -> 
	l1'=l1-1,
	l3'=l3+1;

l1>=1, s1>=1 -> 
	s1'=s1-1,
	s5'=s5+1,
	l1'=l1-1,
	l3'=l3+1;

l2>=1, s1>=1 -> 
	l2'=l2-1,
	l4'=l4+1;

l2>=1, s1>=1 -> 
	s1'=s1-1,
	s3'=s3+1,
	l2'=l2-1,
	l4'=l4+1;

l3>=1, s1>=1 -> 
	l3'=l3-1,
	l5'=l5+1;

l3>=1, s1>=1 -> 
	s1'=s1-1,
	s3'=s3+1,
	l3'=l3-1,
	l5'=l5+1;

l4>=1, s1>=1 -> 
	s1'=s1-1,
	s0'=s0+1,
	l4'=l4-1,
	l6'=l6+1;

l4>=1, s1>=1 -> 
	l4'=l4-1,
	l6'=l6+1;

l5>=1, s1>=1 -> 
	s1'=s1-1,
	s0'=s0+1,
	l5'=l5-1,
	l7'=l7+1;

l5>=1, s1>=1 -> 
	l5'=l5-1,
	l7'=l7+1;

l6>=1, s1>=1 -> 
	l6'=l6-1,
	l8'=l8+1;

l6>=1, s1>=1 -> 
	l6'=l6-1,
	l9'=l9+1;

l7>=1, s1>=1 -> 
	l7'=l7-1,
	l8'=l8+1;

l7>=1, s1>=1 -> 
	l7'=l7-1,
	l9'=l9+1;

l8>=1, s1>=1 -> 
	l8'=l8-1,
	l10'=l10+1;

l9>=1, s1>=1 -> 
	l9'=l9-1,
	l11'=l11+1;

l10>=1, s1>=1 -> 
	s1'=s1-1,
	s5'=s5+1,
	l10'=l10-1,
	l12'=l12+1;

l11>=1, s1>=1 -> 
	s1'=s1-1,
	s5'=s5+1,
	l11'=l11-1,
	l13'=l13+1;

l12>=1, s1>=1 -> 
	s1'=s1-1,
	s5'=s5+1,
	l12'=l12-1,
	l14'=l14+1;

l13>=1, s1>=1 -> 
	s1'=s1-1,
	s5'=s5+1,
	l13'=l13-1,
	l15'=l15+1;

l14>=1, s1>=1 -> 
	l14'=l14-1,
	l16'=l16+1;

l15>=1, s1>=1 -> 
	l15'=l15-1,
	l17'=l17+1;

l18>=1, s1>=1 -> 
	l18'=l18-1,
	l20'=l20+1;

l18>=1, s1>=1 -> 
	l18'=l18-1,
	l21'=l21+1;

l19>=1, s1>=1 -> 
	l19'=l19-1,
	l20'=l20+1;

l19>=1, s1>=1 -> 
	l19'=l19-1,
	l21'=l21+1;

l20>=1, s1>=1 -> 
	l20'=l20-1,
	l22'=l22+1;

l21>=1, s1>=1 -> 
	l21'=l21-1,
	l22'=l22+1;

l22>=1, s1>=1 -> 
	s1'=s1-1,
	s17'=s17+1,
	l22'=l22-1,
	l24'=l24+1;

l23>=1, s1>=1 -> 
	s1'=s1-1,
	s17'=s17+1,
	l23'=l23-1,
	l25'=l25+1;

l34>=1, s1>=1 -> 
	l34'=l34-1,
	l40'=l40+1;

l35>=1, s1>=1 -> 
	l35'=l35-1,
	l37'=l37+1;

l38>=1, s1>=1 -> 
	l38'=l38-1,
	l60'=l60+1;

l39>=1, s1>=1 -> 
	l39'=l39-1,
	l61'=l61+1;

l40>=1, s1>=1 -> 
	l40'=l40-1,
	l42'=l42+1;

l41>=1, s1>=1 -> 
	l41'=l41-1,
	l43'=l43+1;

l42>=1, s1>=1 -> 
	s1'=s1-1,
	s17'=s17+1,
	l42'=l42-1,
	l44'=l44+1;

l43>=1, s1>=1 -> 
	s1'=s1-1,
	s17'=s17+1,
	l43'=l43-1,
	l45'=l45+1;

l50>=1, s1>=1 -> 
	l50'=l50-1,
	l52'=l52+1;

l51>=1, s1>=1 -> 
	s1'=s1-1,
	s5'=s5+1,
	l51'=l51-1,
	l53'=l53+1;

l52>=1, s1>=1 -> 
	s1'=s1-1,
	s17'=s17+1,
	l52'=l52-1,
	l54'=l54+1;

l53>=1, s1>=1 -> 
	s1'=s1-1,
	s17'=s17+1,
	l53'=l53-1,
	l55'=l55+1;

l60>=1, s1>=1 -> 
	l60'=l60-1,
	l62'=l62+1;

l61>=1, s1>=1 -> 
	l61'=l61-1,
	l63'=l63+1;

l62>=1, s1>=1 -> 
	l62'=l62-1,
	l64'=l64+1;

l63>=1, s1>=1 -> 
	l63'=l63-1,
	l65'=l65+1;

l66>=1, s1>=1 -> 
	l66'=l66-1,
	l14'=l14+1;

l67>=1, s1>=1 -> 
	l67'=l67-1,
	l15'=l15+1;

l68>=1, s1>=1 -> 
	l68'=l68-1,
	l70'=l70+1;

l69>=1, s1>=1 -> 
	l69'=l69-1,
	l71'=l71+1;

l0>=1, s2>=1 -> 
	l0'=l0-1,
	l2'=l2+1;

l0>=1, s2>=1 -> 
	s2'=s2-1,
	s6'=s6+1,
	l0'=l0-1,
	l2'=l2+1;

l1>=1, s2>=1 -> 
	l1'=l1-1,
	l3'=l3+1;

l1>=1, s2>=1 -> 
	s2'=s2-1,
	s6'=s6+1,
	l1'=l1-1,
	l3'=l3+1;

l2>=1, s2>=1 -> 
	s2'=s2-1,
	s0'=s0+1,
	l2'=l2-1,
	l4'=l4+1;

l2>=1, s2>=1 -> 
	l2'=l2-1,
	l4'=l4+1;

l3>=1, s2>=1 -> 
	s2'=s2-1,
	s0'=s0+1,
	l3'=l3-1,
	l5'=l5+1;

l3>=1, s2>=1 -> 
	l3'=l3-1,
	l5'=l5+1;

l4>=1, s2>=1 -> 
	l4'=l4-1,
	l6'=l6+1;

l4>=1, s2>=1 -> 
	s2'=s2-1,
	s3'=s3+1,
	l4'=l4-1,
	l6'=l6+1;

l5>=1, s2>=1 -> 
	l5'=l5-1,
	l7'=l7+1;

l5>=1, s2>=1 -> 
	s2'=s2-1,
	s3'=s3+1,
	l5'=l5-1,
	l7'=l7+1;

l6>=1, s2>=1 -> 
	l6'=l6-1,
	l8'=l8+1;

l6>=1, s2>=1 -> 
	l6'=l6-1,
	l9'=l9+1;

l7>=1, s2>=1 -> 
	l7'=l7-1,
	l8'=l8+1;

l7>=1, s2>=1 -> 
	l7'=l7-1,
	l9'=l9+1;

l8>=1, s2>=1 -> 
	s2'=s2-1,
	s1'=s1+1,
	l8'=l8-1,
	l10'=l10+1;

l9>=1, s2>=1 -> 
	s2'=s2-1,
	s1'=s1+1,
	l9'=l9-1,
	l11'=l11+1;

l10>=1, s2>=1 -> 
	s2'=s2-1,
	s6'=s6+1,
	l10'=l10-1,
	l12'=l12+1;

l11>=1, s2>=1 -> 
	s2'=s2-1,
	s6'=s6+1,
	l11'=l11-1,
	l13'=l13+1;

l12>=1, s2>=1 -> 
	s2'=s2-1,
	s6'=s6+1,
	l12'=l12-1,
	l14'=l14+1;

l13>=1, s2>=1 -> 
	s2'=s2-1,
	s6'=s6+1,
	l13'=l13-1,
	l15'=l15+1;

l14>=1, s2>=1 -> 
	l14'=l14-1,
	l16'=l16+1;

l15>=1, s2>=1 -> 
	l15'=l15-1,
	l17'=l17+1;

l18>=1, s2>=1 -> 
	l18'=l18-1,
	l20'=l20+1;

l18>=1, s2>=1 -> 
	l18'=l18-1,
	l21'=l21+1;

l19>=1, s2>=1 -> 
	l19'=l19-1,
	l20'=l20+1;

l19>=1, s2>=1 -> 
	l19'=l19-1,
	l21'=l21+1;

l20>=1, s2>=1 -> 
	l20'=l20-1,
	l22'=l22+1;

l21>=1, s2>=1 -> 
	l21'=l21-1,
	l22'=l22+1;

l22>=1, s2>=1 -> 
	s2'=s2-1,
	s18'=s18+1,
	l22'=l22-1,
	l24'=l24+1;

l23>=1, s2>=1 -> 
	s2'=s2-1,
	s18'=s18+1,
	l23'=l23-1,
	l25'=l25+1;

l34>=1, s2>=1 -> 
	l34'=l34-1,
	l40'=l40+1;

l35>=1, s2>=1 -> 
	l35'=l35-1,
	l37'=l37+1;

l38>=1, s2>=1 -> 
	l38'=l38-1,
	l60'=l60+1;

l39>=1, s2>=1 -> 
	l39'=l39-1,
	l61'=l61+1;

l40>=1, s2>=1 -> 
	l40'=l40-1,
	l42'=l42+1;

l41>=1, s2>=1 -> 
	l41'=l41-1,
	l43'=l43+1;

l42>=1, s2>=1 -> 
	s2'=s2-1,
	s18'=s18+1,
	l42'=l42-1,
	l44'=l44+1;

l43>=1, s2>=1 -> 
	s2'=s2-1,
	s18'=s18+1,
	l43'=l43-1,
	l45'=l45+1;

l50>=1, s2>=1 -> 
	l50'=l50-1,
	l52'=l52+1;

l51>=1, s2>=1 -> 
	s2'=s2-1,
	s6'=s6+1,
	l51'=l51-1,
	l53'=l53+1;

l52>=1, s2>=1 -> 
	s2'=s2-1,
	s18'=s18+1,
	l52'=l52-1,
	l54'=l54+1;

l53>=1, s2>=1 -> 
	s2'=s2-1,
	s18'=s18+1,
	l53'=l53-1,
	l55'=l55+1;

l60>=1, s2>=1 -> 
	l60'=l60-1,
	l62'=l62+1;

l61>=1, s2>=1 -> 
	l61'=l61-1,
	l63'=l63+1;

l62>=1, s2>=1 -> 
	l62'=l62-1,
	l64'=l64+1;

l63>=1, s2>=1 -> 
	l63'=l63-1,
	l65'=l65+1;

l66>=1, s2>=1 -> 
	l66'=l66-1,
	l14'=l14+1;

l67>=1, s2>=1 -> 
	l67'=l67-1,
	l15'=l15+1;

l68>=1, s2>=1 -> 
	l68'=l68-1,
	l70'=l70+1;

l69>=1, s2>=1 -> 
	l69'=l69-1,
	l71'=l71+1;

l0>=1, s3>=1 -> 
	l0'=l0-1,
	l2'=l2+1;

l0>=1, s3>=1 -> 
	s3'=s3-1,
	s7'=s7+1,
	l0'=l0-1,
	l2'=l2+1;

l1>=1, s3>=1 -> 
	l1'=l1-1,
	l3'=l3+1;

l1>=1, s3>=1 -> 
	s3'=s3-1,
	s7'=s7+1,
	l1'=l1-1,
	l3'=l3+1;

l2>=1, s3>=1 -> 
	s3'=s3-1,
	s1'=s1+1,
	l2'=l2-1,
	l4'=l4+1;

l2>=1, s3>=1 -> 
	l2'=l2-1,
	l4'=l4+1;

l3>=1, s3>=1 -> 
	s3'=s3-1,
	s1'=s1+1,
	l3'=l3-1,
	l5'=l5+1;

l3>=1, s3>=1 -> 
	l3'=l3-1,
	l5'=l5+1;

l4>=1, s3>=1 -> 
	s3'=s3-1,
	s2'=s2+1,
	l4'=l4-1,
	l6'=l6+1;

l4>=1, s3>=1 -> 
	l4'=l4-1,
	l6'=l6+1;

l5>=1, s3>=1 -> 
	s3'=s3-1,
	s2'=s2+1,
	l5'=l5-1,
	l7'=l7+1;

l5>=1, s3>=1 -> 
	l5'=l5-1,
	l7'=l7+1;

l6>=1, s3>=1 -> 
	l6'=l6-1,
	l8'=l8+1;

l6>=1, s3>=1 -> 
	l6'=l6-1,
	l9'=l9+1;

l7>=1, s3>=1 -> 
	l7'=l7-1,
	l8'=l8+1;

l7>=1, s3>=1 -> 
	l7'=l7-1,
	l9'=l9+1;

l8>=1, s3>=1 -> 
	s3'=s3-1,
	s1'=s1+1,
	l8'=l8-1,
	l10'=l10+1;

l9>=1, s3>=1 -> 
	s3'=s3-1,
	s1'=s1+1,
	l9'=l9-1,
	l11'=l11+1;

l10>=1, s3>=1 -> 
	s3'=s3-1,
	s7'=s7+1,
	l10'=l10-1,
	l12'=l12+1;

l11>=1, s3>=1 -> 
	s3'=s3-1,
	s7'=s7+1,
	l11'=l11-1,
	l13'=l13+1;

l12>=1, s3>=1 -> 
	s3'=s3-1,
	s7'=s7+1,
	l12'=l12-1,
	l14'=l14+1;

l13>=1, s3>=1 -> 
	s3'=s3-1,
	s7'=s7+1,
	l13'=l13-1,
	l15'=l15+1;

l14>=1, s3>=1 -> 
	l14'=l14-1,
	l16'=l16+1;

l15>=1, s3>=1 -> 
	l15'=l15-1,
	l17'=l17+1;

l18>=1, s3>=1 -> 
	l18'=l18-1,
	l20'=l20+1;

l18>=1, s3>=1 -> 
	l18'=l18-1,
	l21'=l21+1;

l19>=1, s3>=1 -> 
	l19'=l19-1,
	l20'=l20+1;

l19>=1, s3>=1 -> 
	l19'=l19-1,
	l21'=l21+1;

l20>=1, s3>=1 -> 
	l20'=l20-1,
	l22'=l22+1;

l21>=1, s3>=1 -> 
	l21'=l21-1,
	l22'=l22+1;

l22>=1, s3>=1 -> 
	s3'=s3-1,
	s19'=s19+1,
	l22'=l22-1,
	l24'=l24+1;

l23>=1, s3>=1 -> 
	s3'=s3-1,
	s19'=s19+1,
	l23'=l23-1,
	l25'=l25+1;

l34>=1, s3>=1 -> 
	l34'=l34-1,
	l40'=l40+1;

l35>=1, s3>=1 -> 
	l35'=l35-1,
	l37'=l37+1;

l38>=1, s3>=1 -> 
	l38'=l38-1,
	l60'=l60+1;

l39>=1, s3>=1 -> 
	l39'=l39-1,
	l61'=l61+1;

l40>=1, s3>=1 -> 
	l40'=l40-1,
	l42'=l42+1;

l41>=1, s3>=1 -> 
	l41'=l41-1,
	l43'=l43+1;

l42>=1, s3>=1 -> 
	s3'=s3-1,
	s19'=s19+1,
	l42'=l42-1,
	l44'=l44+1;

l43>=1, s3>=1 -> 
	s3'=s3-1,
	s19'=s19+1,
	l43'=l43-1,
	l45'=l45+1;

l50>=1, s3>=1 -> 
	l50'=l50-1,
	l52'=l52+1;

l51>=1, s3>=1 -> 
	s3'=s3-1,
	s7'=s7+1,
	l51'=l51-1,
	l53'=l53+1;

l52>=1, s3>=1 -> 
	s3'=s3-1,
	s19'=s19+1,
	l52'=l52-1,
	l54'=l54+1;

l53>=1, s3>=1 -> 
	s3'=s3-1,
	s19'=s19+1,
	l53'=l53-1,
	l55'=l55+1;

l60>=1, s3>=1 -> 
	l60'=l60-1,
	l62'=l62+1;

l61>=1, s3>=1 -> 
	l61'=l61-1,
	l63'=l63+1;

l62>=1, s3>=1 -> 
	l62'=l62-1,
	l64'=l64+1;

l63>=1, s3>=1 -> 
	l63'=l63-1,
	l65'=l65+1;

l66>=1, s3>=1 -> 
	l66'=l66-1,
	l14'=l14+1;

l67>=1, s3>=1 -> 
	l67'=l67-1,
	l15'=l15+1;

l68>=1, s3>=1 -> 
	l68'=l68-1,
	l70'=l70+1;

l69>=1, s3>=1 -> 
	l69'=l69-1,
	l71'=l71+1;

l0>=1, s4>=1 -> 
	s4'=s4-1,
	s0'=s0+1,
	l0'=l0-1,
	l2'=l2+1;

l0>=1, s4>=1 -> 
	l0'=l0-1,
	l2'=l2+1;

l1>=1, s4>=1 -> 
	s4'=s4-1,
	s0'=s0+1,
	l1'=l1-1,
	l3'=l3+1;

l1>=1, s4>=1 -> 
	l1'=l1-1,
	l3'=l3+1;

l2>=1, s4>=1 -> 
	l2'=l2-1,
	l4'=l4+1;

l2>=1, s4>=1 -> 
	s4'=s4-1,
	s6'=s6+1,
	l2'=l2-1,
	l4'=l4+1;

l3>=1, s4>=1 -> 
	l3'=l3-1,
	l5'=l5+1;

l3>=1, s4>=1 -> 
	s4'=s4-1,
	s6'=s6+1,
	l3'=l3-1,
	l5'=l5+1;

l4>=1, s4>=1 -> 
	l4'=l4-1,
	l6'=l6+1;

l4>=1, s4>=1 -> 
	s4'=s4-1,
	s5'=s5+1,
	l4'=l4-1,
	l6'=l6+1;

l5>=1, s4>=1 -> 
	l5'=l5-1,
	l7'=l7+1;

l5>=1, s4>=1 -> 
	s4'=s4-1,
	s5'=s5+1,
	l5'=l5-1,
	l7'=l7+1;

l6>=1, s4>=1 -> 
	l6'=l6-1,
	l8'=l8+1;

l6>=1, s4>=1 -> 
	l6'=l6-1,
	l9'=l9+1;

l7>=1, s4>=1 -> 
	l7'=l7-1,
	l8'=l8+1;

l7>=1, s4>=1 -> 
	l7'=l7-1,
	l9'=l9+1;

l8>=1, s4>=1 -> 
	s4'=s4-1,
	s5'=s5+1,
	l8'=l8-1,
	l10'=l10+1;

l9>=1, s4>=1 -> 
	s4'=s4-1,
	s5'=s5+1,
	l9'=l9-1,
	l11'=l11+1;

l10>=1, s4>=1 -> 
	l10'=l10-1,
	l12'=l12+1;

l11>=1, s4>=1 -> 
	l11'=l11-1,
	l13'=l13+1;

l12>=1, s4>=1 -> 
	l12'=l12-1,
	l14'=l14+1;

l13>=1, s4>=1 -> 
	l13'=l13-1,
	l15'=l15+1;

l14>=1, s4>=1 -> 
	l14'=l14-1,
	l16'=l16+1;

l15>=1, s4>=1 -> 
	l15'=l15-1,
	l17'=l17+1;

l18>=1, s4>=1 -> 
	l18'=l18-1,
	l20'=l20+1;

l18>=1, s4>=1 -> 
	l18'=l18-1,
	l21'=l21+1;

l19>=1, s4>=1 -> 
	l19'=l19-1,
	l20'=l20+1;

l19>=1, s4>=1 -> 
	l19'=l19-1,
	l21'=l21+1;

l20>=1, s4>=1 -> 
	l20'=l20-1,
	l22'=l22+1;

l21>=1, s4>=1 -> 
	l21'=l21-1,
	l22'=l22+1;

l22>=1, s4>=1 -> 
	s4'=s4-1,
	s20'=s20+1,
	l22'=l22-1,
	l24'=l24+1;

l23>=1, s4>=1 -> 
	s4'=s4-1,
	s20'=s20+1,
	l23'=l23-1,
	l25'=l25+1;

l34>=1, s4>=1 -> 
	l34'=l34-1,
	l40'=l40+1;

l35>=1, s4>=1 -> 
	l35'=l35-1,
	l37'=l37+1;

l38>=1, s4>=1 -> 
	l38'=l38-1,
	l60'=l60+1;

l39>=1, s4>=1 -> 
	l39'=l39-1,
	l61'=l61+1;

l40>=1, s4>=1 -> 
	l40'=l40-1,
	l42'=l42+1;

l41>=1, s4>=1 -> 
	l41'=l41-1,
	l43'=l43+1;

l42>=1, s4>=1 -> 
	s4'=s4-1,
	s20'=s20+1,
	l42'=l42-1,
	l44'=l44+1;

l43>=1, s4>=1 -> 
	s4'=s4-1,
	s20'=s20+1,
	l43'=l43-1,
	l45'=l45+1;

l50>=1, s4>=1 -> 
	s4'=s4-1,
	s0'=s0+1,
	l50'=l50-1,
	l52'=l52+1;

l51>=1, s4>=1 -> 
	l51'=l51-1,
	l53'=l53+1;

l52>=1, s4>=1 -> 
	s4'=s4-1,
	s20'=s20+1,
	l52'=l52-1,
	l54'=l54+1;

l53>=1, s4>=1 -> 
	s4'=s4-1,
	s20'=s20+1,
	l53'=l53-1,
	l55'=l55+1;

l60>=1, s4>=1 -> 
	l60'=l60-1,
	l62'=l62+1;

l61>=1, s4>=1 -> 
	l61'=l61-1,
	l63'=l63+1;

l62>=1, s4>=1 -> 
	s4'=s4-1,
	s32'=s32+1,
	l62'=l62-1,
	l72'=l72+1;

l63>=1, s4>=1 -> 
	s4'=s4-1,
	s32'=s32+1,
	l63'=l63-1,
	l72'=l72+1;

l66>=1, s4>=1 -> 
	l66'=l66-1,
	l14'=l14+1;

l67>=1, s4>=1 -> 
	l67'=l67-1,
	l15'=l15+1;

l68>=1, s4>=1 -> 
	l68'=l68-1,
	l70'=l70+1;

l69>=1, s4>=1 -> 
	l69'=l69-1,
	l71'=l71+1;

l0>=1, s5>=1 -> 
	s5'=s5-1,
	s1'=s1+1,
	l0'=l0-1,
	l2'=l2+1;

l0>=1, s5>=1 -> 
	l0'=l0-1,
	l2'=l2+1;

l1>=1, s5>=1 -> 
	s5'=s5-1,
	s1'=s1+1,
	l1'=l1-1,
	l3'=l3+1;

l1>=1, s5>=1 -> 
	l1'=l1-1,
	l3'=l3+1;

l2>=1, s5>=1 -> 
	l2'=l2-1,
	l4'=l4+1;

l2>=1, s5>=1 -> 
	s5'=s5-1,
	s7'=s7+1,
	l2'=l2-1,
	l4'=l4+1;

l3>=1, s5>=1 -> 
	l3'=l3-1,
	l5'=l5+1;

l3>=1, s5>=1 -> 
	s5'=s5-1,
	s7'=s7+1,
	l3'=l3-1,
	l5'=l5+1;

l4>=1, s5>=1 -> 
	s5'=s5-1,
	s4'=s4+1,
	l4'=l4-1,
	l6'=l6+1;

l4>=1, s5>=1 -> 
	l4'=l4-1,
	l6'=l6+1;

l5>=1, s5>=1 -> 
	s5'=s5-1,
	s4'=s4+1,
	l5'=l5-1,
	l7'=l7+1;

l5>=1, s5>=1 -> 
	l5'=l5-1,
	l7'=l7+1;

l6>=1, s5>=1 -> 
	l6'=l6-1,
	l8'=l8+1;

l6>=1, s5>=1 -> 
	l6'=l6-1,
	l9'=l9+1;

l7>=1, s5>=1 -> 
	l7'=l7-1,
	l8'=l8+1;

l7>=1, s5>=1 -> 
	l7'=l7-1,
	l9'=l9+1;

l8>=1, s5>=1 -> 
	l8'=l8-1,
	l10'=l10+1;

l9>=1, s5>=1 -> 
	l9'=l9-1,
	l11'=l11+1;

l10>=1, s5>=1 -> 
	l10'=l10-1,
	l12'=l12+1;

l11>=1, s5>=1 -> 
	l11'=l11-1,
	l13'=l13+1;

l12>=1, s5>=1 -> 
	l12'=l12-1,
	l14'=l14+1;

l13>=1, s5>=1 -> 
	l13'=l13-1,
	l15'=l15+1;

l14>=1, s5>=1 -> 
	l14'=l14-1,
	l16'=l16+1;

l15>=1, s5>=1 -> 
	l15'=l15-1,
	l17'=l17+1;

l18>=1, s5>=1 -> 
	l18'=l18-1,
	l20'=l20+1;

l18>=1, s5>=1 -> 
	l18'=l18-1,
	l21'=l21+1;

l19>=1, s5>=1 -> 
	l19'=l19-1,
	l20'=l20+1;

l19>=1, s5>=1 -> 
	l19'=l19-1,
	l21'=l21+1;

l20>=1, s5>=1 -> 
	l20'=l20-1,
	l22'=l22+1;

l21>=1, s5>=1 -> 
	l21'=l21-1,
	l22'=l22+1;

l22>=1, s5>=1 -> 
	s5'=s5-1,
	s21'=s21+1,
	l22'=l22-1,
	l24'=l24+1;

l23>=1, s5>=1 -> 
	s5'=s5-1,
	s21'=s21+1,
	l23'=l23-1,
	l25'=l25+1;

l34>=1, s5>=1 -> 
	l34'=l34-1,
	l40'=l40+1;

l35>=1, s5>=1 -> 
	l35'=l35-1,
	l37'=l37+1;

l38>=1, s5>=1 -> 
	l38'=l38-1,
	l60'=l60+1;

l39>=1, s5>=1 -> 
	l39'=l39-1,
	l61'=l61+1;

l40>=1, s5>=1 -> 
	l40'=l40-1,
	l42'=l42+1;

l41>=1, s5>=1 -> 
	l41'=l41-1,
	l43'=l43+1;

l42>=1, s5>=1 -> 
	s5'=s5-1,
	s21'=s21+1,
	l42'=l42-1,
	l44'=l44+1;

l43>=1, s5>=1 -> 
	s5'=s5-1,
	s21'=s21+1,
	l43'=l43-1,
	l45'=l45+1;

l50>=1, s5>=1 -> 
	s5'=s5-1,
	s1'=s1+1,
	l50'=l50-1,
	l52'=l52+1;

l51>=1, s5>=1 -> 
	l51'=l51-1,
	l53'=l53+1;

l52>=1, s5>=1 -> 
	s5'=s5-1,
	s21'=s21+1,
	l52'=l52-1,
	l54'=l54+1;

l53>=1, s5>=1 -> 
	s5'=s5-1,
	s21'=s21+1,
	l53'=l53-1,
	l55'=l55+1;

l60>=1, s5>=1 -> 
	l60'=l60-1,
	l62'=l62+1;

l61>=1, s5>=1 -> 
	l61'=l61-1,
	l63'=l63+1;

l62>=1, s5>=1 -> 
	s5'=s5-1,
	s32'=s32+1,
	l62'=l62-1,
	l72'=l72+1;

l63>=1, s5>=1 -> 
	s5'=s5-1,
	s32'=s32+1,
	l63'=l63-1,
	l72'=l72+1;

l66>=1, s5>=1 -> 
	l66'=l66-1,
	l14'=l14+1;

l67>=1, s5>=1 -> 
	l67'=l67-1,
	l15'=l15+1;

l68>=1, s5>=1 -> 
	l68'=l68-1,
	l70'=l70+1;

l69>=1, s5>=1 -> 
	l69'=l69-1,
	l71'=l71+1;

l0>=1, s6>=1 -> 
	s6'=s6-1,
	s2'=s2+1,
	l0'=l0-1,
	l2'=l2+1;

l0>=1, s6>=1 -> 
	l0'=l0-1,
	l2'=l2+1;

l1>=1, s6>=1 -> 
	s6'=s6-1,
	s2'=s2+1,
	l1'=l1-1,
	l3'=l3+1;

l1>=1, s6>=1 -> 
	l1'=l1-1,
	l3'=l3+1;

l2>=1, s6>=1 -> 
	s6'=s6-1,
	s4'=s4+1,
	l2'=l2-1,
	l4'=l4+1;

l2>=1, s6>=1 -> 
	l2'=l2-1,
	l4'=l4+1;

l3>=1, s6>=1 -> 
	s6'=s6-1,
	s4'=s4+1,
	l3'=l3-1,
	l5'=l5+1;

l3>=1, s6>=1 -> 
	l3'=l3-1,
	l5'=l5+1;

l4>=1, s6>=1 -> 
	l4'=l4-1,
	l6'=l6+1;

l4>=1, s6>=1 -> 
	s6'=s6-1,
	s7'=s7+1,
	l4'=l4-1,
	l6'=l6+1;

l5>=1, s6>=1 -> 
	l5'=l5-1,
	l7'=l7+1;

l5>=1, s6>=1 -> 
	s6'=s6-1,
	s7'=s7+1,
	l5'=l5-1,
	l7'=l7+1;

l6>=1, s6>=1 -> 
	l6'=l6-1,
	l8'=l8+1;

l6>=1, s6>=1 -> 
	l6'=l6-1,
	l9'=l9+1;

l7>=1, s6>=1 -> 
	l7'=l7-1,
	l8'=l8+1;

l7>=1, s6>=1 -> 
	l7'=l7-1,
	l9'=l9+1;

l8>=1, s6>=1 -> 
	s6'=s6-1,
	s5'=s5+1,
	l8'=l8-1,
	l10'=l10+1;

l9>=1, s6>=1 -> 
	s6'=s6-1,
	s5'=s5+1,
	l9'=l9-1,
	l11'=l11+1;

l10>=1, s6>=1 -> 
	l10'=l10-1,
	l12'=l12+1;

l11>=1, s6>=1 -> 
	l11'=l11-1,
	l13'=l13+1;

l12>=1, s6>=1 -> 
	l12'=l12-1,
	l14'=l14+1;

l13>=1, s6>=1 -> 
	l13'=l13-1,
	l15'=l15+1;

l14>=1, s6>=1 -> 
	l14'=l14-1,
	l16'=l16+1;

l15>=1, s6>=1 -> 
	l15'=l15-1,
	l17'=l17+1;

l18>=1, s6>=1 -> 
	l18'=l18-1,
	l20'=l20+1;

l18>=1, s6>=1 -> 
	l18'=l18-1,
	l21'=l21+1;

l19>=1, s6>=1 -> 
	l19'=l19-1,
	l20'=l20+1;

l19>=1, s6>=1 -> 
	l19'=l19-1,
	l21'=l21+1;

l20>=1, s6>=1 -> 
	l20'=l20-1,
	l22'=l22+1;

l21>=1, s6>=1 -> 
	l21'=l21-1,
	l22'=l22+1;

l22>=1, s6>=1 -> 
	s6'=s6-1,
	s22'=s22+1,
	l22'=l22-1,
	l24'=l24+1;

l23>=1, s6>=1 -> 
	s6'=s6-1,
	s22'=s22+1,
	l23'=l23-1,
	l25'=l25+1;

l34>=1, s6>=1 -> 
	l34'=l34-1,
	l40'=l40+1;

l35>=1, s6>=1 -> 
	l35'=l35-1,
	l37'=l37+1;

l38>=1, s6>=1 -> 
	l38'=l38-1,
	l60'=l60+1;

l39>=1, s6>=1 -> 
	l39'=l39-1,
	l61'=l61+1;

l40>=1, s6>=1 -> 
	l40'=l40-1,
	l42'=l42+1;

l41>=1, s6>=1 -> 
	l41'=l41-1,
	l43'=l43+1;

l42>=1, s6>=1 -> 
	s6'=s6-1,
	s22'=s22+1,
	l42'=l42-1,
	l44'=l44+1;

l43>=1, s6>=1 -> 
	s6'=s6-1,
	s22'=s22+1,
	l43'=l43-1,
	l45'=l45+1;

l50>=1, s6>=1 -> 
	s6'=s6-1,
	s2'=s2+1,
	l50'=l50-1,
	l52'=l52+1;

l51>=1, s6>=1 -> 
	l51'=l51-1,
	l53'=l53+1;

l52>=1, s6>=1 -> 
	s6'=s6-1,
	s22'=s22+1,
	l52'=l52-1,
	l54'=l54+1;

l53>=1, s6>=1 -> 
	s6'=s6-1,
	s22'=s22+1,
	l53'=l53-1,
	l55'=l55+1;

l60>=1, s6>=1 -> 
	l60'=l60-1,
	l62'=l62+1;

l61>=1, s6>=1 -> 
	l61'=l61-1,
	l63'=l63+1;

l62>=1, s6>=1 -> 
	s6'=s6-1,
	s32'=s32+1,
	l62'=l62-1,
	l72'=l72+1;

l63>=1, s6>=1 -> 
	s6'=s6-1,
	s32'=s32+1,
	l63'=l63-1,
	l72'=l72+1;

l66>=1, s6>=1 -> 
	l66'=l66-1,
	l14'=l14+1;

l67>=1, s6>=1 -> 
	l67'=l67-1,
	l15'=l15+1;

l68>=1, s6>=1 -> 
	l68'=l68-1,
	l70'=l70+1;

l69>=1, s6>=1 -> 
	l69'=l69-1,
	l71'=l71+1;

l0>=1, s7>=1 -> 
	s7'=s7-1,
	s3'=s3+1,
	l0'=l0-1,
	l2'=l2+1;

l0>=1, s7>=1 -> 
	l0'=l0-1,
	l2'=l2+1;

l1>=1, s7>=1 -> 
	s7'=s7-1,
	s3'=s3+1,
	l1'=l1-1,
	l3'=l3+1;

l1>=1, s7>=1 -> 
	l1'=l1-1,
	l3'=l3+1;

l2>=1, s7>=1 -> 
	s7'=s7-1,
	s5'=s5+1,
	l2'=l2-1,
	l4'=l4+1;

l2>=1, s7>=1 -> 
	l2'=l2-1,
	l4'=l4+1;

l3>=1, s7>=1 -> 
	s7'=s7-1,
	s5'=s5+1,
	l3'=l3-1,
	l5'=l5+1;

l3>=1, s7>=1 -> 
	l3'=l3-1,
	l5'=l5+1;

l4>=1, s7>=1 -> 
	s7'=s7-1,
	s6'=s6+1,
	l4'=l4-1,
	l6'=l6+1;

l4>=1, s7>=1 -> 
	l4'=l4-1,
	l6'=l6+1;

l5>=1, s7>=1 -> 
	s7'=s7-1,
	s6'=s6+1,
	l5'=l5-1,
	l7'=l7+1;

l5>=1, s7>=1 -> 
	l5'=l5-1,
	l7'=l7+1;

l6>=1, s7>=1 -> 
	l6'=l6-1,
	l8'=l8+1;

l6>=1, s7>=1 -> 
	l6'=l6-1,
	l9'=l9+1;

l7>=1, s7>=1 -> 
	l7'=l7-1,
	l8'=l8+1;

l7>=1, s7>=1 -> 
	l7'=l7-1,
	l9'=l9+1;

l8>=1, s7>=1 -> 
	s7'=s7-1,
	s5'=s5+1,
	l8'=l8-1,
	l10'=l10+1;

l9>=1, s7>=1 -> 
	s7'=s7-1,
	s5'=s5+1,
	l9'=l9-1,
	l11'=l11+1;

l10>=1, s7>=1 -> 
	l10'=l10-1,
	l12'=l12+1;

l11>=1, s7>=1 -> 
	l11'=l11-1,
	l13'=l13+1;

l12>=1, s7>=1 -> 
	l12'=l12-1,
	l14'=l14+1;

l13>=1, s7>=1 -> 
	l13'=l13-1,
	l15'=l15+1;

l14>=1, s7>=1 -> 
	l14'=l14-1,
	l16'=l16+1;

l15>=1, s7>=1 -> 
	l15'=l15-1,
	l17'=l17+1;

l18>=1, s7>=1 -> 
	l18'=l18-1,
	l20'=l20+1;

l18>=1, s7>=1 -> 
	l18'=l18-1,
	l21'=l21+1;

l19>=1, s7>=1 -> 
	l19'=l19-1,
	l20'=l20+1;

l19>=1, s7>=1 -> 
	l19'=l19-1,
	l21'=l21+1;

l20>=1, s7>=1 -> 
	l20'=l20-1,
	l22'=l22+1;

l21>=1, s7>=1 -> 
	l21'=l21-1,
	l22'=l22+1;

l22>=1, s7>=1 -> 
	s7'=s7-1,
	s23'=s23+1,
	l22'=l22-1,
	l24'=l24+1;

l23>=1, s7>=1 -> 
	s7'=s7-1,
	s23'=s23+1,
	l23'=l23-1,
	l25'=l25+1;

l34>=1, s7>=1 -> 
	l34'=l34-1,
	l40'=l40+1;

l35>=1, s7>=1 -> 
	l35'=l35-1,
	l37'=l37+1;

l38>=1, s7>=1 -> 
	l38'=l38-1,
	l60'=l60+1;

l39>=1, s7>=1 -> 
	l39'=l39-1,
	l61'=l61+1;

l40>=1, s7>=1 -> 
	l40'=l40-1,
	l42'=l42+1;

l41>=1, s7>=1 -> 
	l41'=l41-1,
	l43'=l43+1;

l42>=1, s7>=1 -> 
	s7'=s7-1,
	s23'=s23+1,
	l42'=l42-1,
	l44'=l44+1;

l43>=1, s7>=1 -> 
	s7'=s7-1,
	s23'=s23+1,
	l43'=l43-1,
	l45'=l45+1;

l50>=1, s7>=1 -> 
	s7'=s7-1,
	s3'=s3+1,
	l50'=l50-1,
	l52'=l52+1;

l51>=1, s7>=1 -> 
	l51'=l51-1,
	l53'=l53+1;

l52>=1, s7>=1 -> 
	s7'=s7-1,
	s23'=s23+1,
	l52'=l52-1,
	l54'=l54+1;

l53>=1, s7>=1 -> 
	s7'=s7-1,
	s23'=s23+1,
	l53'=l53-1,
	l55'=l55+1;

l60>=1, s7>=1 -> 
	l60'=l60-1,
	l62'=l62+1;

l61>=1, s7>=1 -> 
	l61'=l61-1,
	l63'=l63+1;

l62>=1, s7>=1 -> 
	s7'=s7-1,
	s32'=s32+1,
	l62'=l62-1,
	l72'=l72+1;

l63>=1, s7>=1 -> 
	s7'=s7-1,
	s32'=s32+1,
	l63'=l63-1,
	l72'=l72+1;

l66>=1, s7>=1 -> 
	l66'=l66-1,
	l14'=l14+1;

l67>=1, s7>=1 -> 
	l67'=l67-1,
	l15'=l15+1;

l68>=1, s7>=1 -> 
	l68'=l68-1,
	l70'=l70+1;

l69>=1, s7>=1 -> 
	l69'=l69-1,
	l71'=l71+1;

l16>=1, s8>=1 -> 
	s8'=s8-1,
	s0'=s0+1,
	l16'=l16-1,
	l66'=l66+1;

l17>=1, s8>=1 -> 
	s8'=s8-1,
	s0'=s0+1,
	l17'=l17-1,
	l67'=l67+1;

l16>=1, s9>=1 -> 
	s9'=s9-1,
	s1'=s1+1,
	l16'=l16-1,
	l66'=l66+1;

l17>=1, s9>=1 -> 
	s9'=s9-1,
	s1'=s1+1,
	l17'=l17-1,
	l67'=l67+1;

l16>=1, s10>=1 -> 
	s10'=s10-1,
	s2'=s2+1,
	l16'=l16-1,
	l66'=l66+1;

l17>=1, s10>=1 -> 
	s10'=s10-1,
	s2'=s2+1,
	l17'=l17-1,
	l67'=l67+1;

l16>=1, s11>=1 -> 
	s11'=s11-1,
	s3'=s3+1,
	l16'=l16-1,
	l66'=l66+1;

l17>=1, s11>=1 -> 
	s11'=s11-1,
	s3'=s3+1,
	l17'=l17-1,
	l67'=l67+1;

l16>=1, s12>=1 -> 
	s12'=s12-1,
	s4'=s4+1,
	l16'=l16-1,
	l66'=l66+1;

l17>=1, s12>=1 -> 
	s12'=s12-1,
	s4'=s4+1,
	l17'=l17-1,
	l67'=l67+1;

l16>=1, s13>=1 -> 
	s13'=s13-1,
	s5'=s5+1,
	l16'=l16-1,
	l66'=l66+1;

l17>=1, s13>=1 -> 
	s13'=s13-1,
	s5'=s5+1,
	l17'=l17-1,
	l67'=l67+1;

l16>=1, s14>=1 -> 
	s14'=s14-1,
	s6'=s6+1,
	l16'=l16-1,
	l66'=l66+1;

l17>=1, s14>=1 -> 
	s14'=s14-1,
	s6'=s6+1,
	l17'=l17-1,
	l67'=l67+1;

l16>=1, s15>=1 -> 
	s15'=s15-1,
	s7'=s7+1,
	l16'=l16-1,
	l66'=l66+1;

l17>=1, s15>=1 -> 
	s15'=s15-1,
	s7'=s7+1,
	l17'=l17-1,
	l67'=l67+1;

l24>=1, s16>=1 -> 
	l24'=l24-1,
	l26'=l26+1;

l24>=1, s16>=1 -> 
	l24'=l24-1,
	l30'=l30+1;

l25>=1, s16>=1 -> 
	l25'=l25-1,
	l27'=l27+1;

l25>=1, s16>=1 -> 
	l25'=l25-1,
	l31'=l31+1;

l26>=1, s16>=1 -> 
	l26'=l26-1,
	l29'=l29+1;

l27>=1, s16>=1 -> 
	l27'=l27-1,
	l29'=l29+1;

l28>=1, s16>=1 -> 
	l28'=l28-1,
	l32'=l32+1;

l29>=1, s16>=1 -> 
	l29'=l29-1,
	l33'=l33+1;

l30>=1, s16>=1 -> 
	l30'=l30-1,
	l32'=l32+1;

l30>=1, s16>=1 -> 
	l30'=l30-1,
	l33'=l33+1;

l31>=1, s16>=1 -> 
	l31'=l31-1,
	l32'=l32+1;

l31>=1, s16>=1 -> 
	l31'=l31-1,
	l33'=l33+1;

l32>=1, s16>=1 -> 
	s16'=s16-1,
	s0'=s0+1,
	l32'=l32-1,
	l34'=l34+1;

l33>=1, s16>=1 -> 
	s16'=s16-1,
	s0'=s0+1,
	l33'=l33-1,
	l35'=l35+1;

l46>=1, s16>=1 -> 
	s16'=s16-1,
	s18'=s18+1,
	l46'=l46-1,
	l48'=l48+1;

l47>=1, s16>=1 -> 
	s16'=s16-1,
	s18'=s18+1,
	l47'=l47-1,
	l49'=l49+1;

l48>=1, s16>=1 -> 
	s16'=s16-1,
	s0'=s0+1,
	l48'=l48-1,
	l50'=l50+1;

l49>=1, s16>=1 -> 
	s16'=s16-1,
	s0'=s0+1,
	l49'=l49-1,
	l51'=l51+1;

l56>=1, s16>=1 -> 
	s16'=s16-1,
	s17'=s17+1,
	l56'=l56-1,
	l58'=l58+1;

l57>=1, s16>=1 -> 
	s16'=s16-1,
	s17'=s17+1,
	l57'=l57-1,
	l59'=l59+1;

l58>=1, s16>=1 -> 
	s16'=s16-1,
	s0'=s0+1,
	l58'=l58-1,
	l60'=l60+1;

l59>=1, s16>=1 -> 
	s16'=s16-1,
	s0'=s0+1,
	l59'=l59-1,
	l61'=l61+1;

l24>=1, s17>=1 -> 
	l24'=l24-1,
	l26'=l26+1;

l24>=1, s17>=1 -> 
	l24'=l24-1,
	l30'=l30+1;

l25>=1, s17>=1 -> 
	l25'=l25-1,
	l27'=l27+1;

l25>=1, s17>=1 -> 
	l25'=l25-1,
	l31'=l31+1;

l26>=1, s17>=1 -> 
	l26'=l26-1,
	l29'=l29+1;

l27>=1, s17>=1 -> 
	l27'=l27-1,
	l29'=l29+1;

l28>=1, s17>=1 -> 
	l28'=l28-1,
	l32'=l32+1;

l29>=1, s17>=1 -> 
	l29'=l29-1,
	l33'=l33+1;

l30>=1, s17>=1 -> 
	l30'=l30-1,
	l32'=l32+1;

l30>=1, s17>=1 -> 
	l30'=l30-1,
	l33'=l33+1;

l31>=1, s17>=1 -> 
	l31'=l31-1,
	l32'=l32+1;

l31>=1, s17>=1 -> 
	l31'=l31-1,
	l33'=l33+1;

l32>=1, s17>=1 -> 
	s17'=s17-1,
	s1'=s1+1,
	l32'=l32-1,
	l34'=l34+1;

l33>=1, s17>=1 -> 
	s17'=s17-1,
	s1'=s1+1,
	l33'=l33-1,
	l35'=l35+1;

l44>=1, s17>=1 -> 
	l44'=l44-1,
	l46'=l46+1;

l45>=1, s17>=1 -> 
	l45'=l45-1,
	l47'=l47+1;

l46>=1, s17>=1 -> 
	s17'=s17-1,
	s18'=s18+1,
	l46'=l46-1,
	l48'=l48+1;

l47>=1, s17>=1 -> 
	s17'=s17-1,
	s18'=s18+1,
	l47'=l47-1,
	l49'=l49+1;

l48>=1, s17>=1 -> 
	s17'=s17-1,
	s1'=s1+1,
	l48'=l48-1,
	l50'=l50+1;

l49>=1, s17>=1 -> 
	s17'=s17-1,
	s1'=s1+1,
	l49'=l49-1,
	l51'=l51+1;

l56>=1, s17>=1 -> 
	l56'=l56-1,
	l58'=l58+1;

l57>=1, s17>=1 -> 
	l57'=l57-1,
	l59'=l59+1;

l58>=1, s17>=1 -> 
	s17'=s17-1,
	s1'=s1+1,
	l58'=l58-1,
	l60'=l60+1;

l59>=1, s17>=1 -> 
	s17'=s17-1,
	s1'=s1+1,
	l59'=l59-1,
	l61'=l61+1;

l24>=1, s18>=1 -> 
	l24'=l24-1,
	l26'=l26+1;

l24>=1, s18>=1 -> 
	l24'=l24-1,
	l30'=l30+1;

l25>=1, s18>=1 -> 
	l25'=l25-1,
	l27'=l27+1;

l25>=1, s18>=1 -> 
	l25'=l25-1,
	l31'=l31+1;

l26>=1, s18>=1 -> 
	l26'=l26-1,
	l29'=l29+1;

l27>=1, s18>=1 -> 
	l27'=l27-1,
	l29'=l29+1;

l28>=1, s18>=1 -> 
	l28'=l28-1,
	l32'=l32+1;

l29>=1, s18>=1 -> 
	l29'=l29-1,
	l33'=l33+1;

l30>=1, s18>=1 -> 
	l30'=l30-1,
	l32'=l32+1;

l30>=1, s18>=1 -> 
	l30'=l30-1,
	l33'=l33+1;

l31>=1, s18>=1 -> 
	l31'=l31-1,
	l32'=l32+1;

l31>=1, s18>=1 -> 
	l31'=l31-1,
	l33'=l33+1;

l32>=1, s18>=1 -> 
	s18'=s18-1,
	s2'=s2+1,
	l32'=l32-1,
	l34'=l34+1;

l33>=1, s18>=1 -> 
	s18'=s18-1,
	s2'=s2+1,
	l33'=l33-1,
	l35'=l35+1;

l46>=1, s18>=1 -> 
	l46'=l46-1,
	l48'=l48+1;

l47>=1, s18>=1 -> 
	l47'=l47-1,
	l49'=l49+1;

l48>=1, s18>=1 -> 
	s18'=s18-1,
	s2'=s2+1,
	l48'=l48-1,
	l50'=l50+1;

l49>=1, s18>=1 -> 
	s18'=s18-1,
	s2'=s2+1,
	l49'=l49-1,
	l51'=l51+1;

l54>=1, s18>=1 -> 
	l54'=l54-1,
	l56'=l56+1;

l55>=1, s18>=1 -> 
	l55'=l55-1,
	l57'=l57+1;

l56>=1, s18>=1 -> 
	s18'=s18-1,
	s17'=s17+1,
	l56'=l56-1,
	l58'=l58+1;

l57>=1, s18>=1 -> 
	s18'=s18-1,
	s17'=s17+1,
	l57'=l57-1,
	l59'=l59+1;

l58>=1, s18>=1 -> 
	s18'=s18-1,
	s2'=s2+1,
	l58'=l58-1,
	l60'=l60+1;

l59>=1, s18>=1 -> 
	s18'=s18-1,
	s2'=s2+1,
	l59'=l59-1,
	l61'=l61+1;

l24>=1, s19>=1 -> 
	l24'=l24-1,
	l26'=l26+1;

l24>=1, s19>=1 -> 
	l24'=l24-1,
	l30'=l30+1;

l25>=1, s19>=1 -> 
	l25'=l25-1,
	l27'=l27+1;

l25>=1, s19>=1 -> 
	l25'=l25-1,
	l31'=l31+1;

l26>=1, s19>=1 -> 
	l26'=l26-1,
	l29'=l29+1;

l27>=1, s19>=1 -> 
	l27'=l27-1,
	l29'=l29+1;

l28>=1, s19>=1 -> 
	l28'=l28-1,
	l32'=l32+1;

l29>=1, s19>=1 -> 
	l29'=l29-1,
	l33'=l33+1;

l30>=1, s19>=1 -> 
	l30'=l30-1,
	l32'=l32+1;

l30>=1, s19>=1 -> 
	l30'=l30-1,
	l33'=l33+1;

l31>=1, s19>=1 -> 
	l31'=l31-1,
	l32'=l32+1;

l31>=1, s19>=1 -> 
	l31'=l31-1,
	l33'=l33+1;

l32>=1, s19>=1 -> 
	s19'=s19-1,
	s3'=s3+1,
	l32'=l32-1,
	l34'=l34+1;

l33>=1, s19>=1 -> 
	s19'=s19-1,
	s3'=s3+1,
	l33'=l33-1,
	l35'=l35+1;

l46>=1, s19>=1 -> 
	s19'=s19-1,
	s18'=s18+1,
	l46'=l46-1,
	l48'=l48+1;

l47>=1, s19>=1 -> 
	s19'=s19-1,
	s18'=s18+1,
	l47'=l47-1,
	l49'=l49+1;

l48>=1, s19>=1 -> 
	s19'=s19-1,
	s3'=s3+1,
	l48'=l48-1,
	l50'=l50+1;

l49>=1, s19>=1 -> 
	s19'=s19-1,
	s3'=s3+1,
	l49'=l49-1,
	l51'=l51+1;

l56>=1, s19>=1 -> 
	s19'=s19-1,
	s17'=s17+1,
	l56'=l56-1,
	l58'=l58+1;

l57>=1, s19>=1 -> 
	s19'=s19-1,
	s17'=s17+1,
	l57'=l57-1,
	l59'=l59+1;

l58>=1, s19>=1 -> 
	s19'=s19-1,
	s3'=s3+1,
	l58'=l58-1,
	l60'=l60+1;

l59>=1, s19>=1 -> 
	s19'=s19-1,
	s3'=s3+1,
	l59'=l59-1,
	l61'=l61+1;

l24>=1, s20>=1 -> 
	l24'=l24-1,
	l26'=l26+1;

l24>=1, s20>=1 -> 
	l24'=l24-1,
	l30'=l30+1;

l25>=1, s20>=1 -> 
	l25'=l25-1,
	l27'=l27+1;

l25>=1, s20>=1 -> 
	l25'=l25-1,
	l31'=l31+1;

l26>=1, s20>=1 -> 
	l26'=l26-1,
	l29'=l29+1;

l27>=1, s20>=1 -> 
	l27'=l27-1,
	l29'=l29+1;

l28>=1, s20>=1 -> 
	l28'=l28-1,
	l32'=l32+1;

l29>=1, s20>=1 -> 
	l29'=l29-1,
	l33'=l33+1;

l30>=1, s20>=1 -> 
	l30'=l30-1,
	l32'=l32+1;

l30>=1, s20>=1 -> 
	l30'=l30-1,
	l33'=l33+1;

l31>=1, s20>=1 -> 
	l31'=l31-1,
	l32'=l32+1;

l31>=1, s20>=1 -> 
	l31'=l31-1,
	l33'=l33+1;

l32>=1, s20>=1 -> 
	s20'=s20-1,
	s4'=s4+1,
	l32'=l32-1,
	l34'=l34+1;

l33>=1, s20>=1 -> 
	s20'=s20-1,
	s4'=s4+1,
	l33'=l33-1,
	l35'=l35+1;

l46>=1, s20>=1 -> 
	s20'=s20-1,
	s22'=s22+1,
	l46'=l46-1,
	l48'=l48+1;

l47>=1, s20>=1 -> 
	s20'=s20-1,
	s22'=s22+1,
	l47'=l47-1,
	l49'=l49+1;

l48>=1, s20>=1 -> 
	s20'=s20-1,
	s4'=s4+1,
	l48'=l48-1,
	l50'=l50+1;

l49>=1, s20>=1 -> 
	s20'=s20-1,
	s4'=s4+1,
	l49'=l49-1,
	l51'=l51+1;

l56>=1, s20>=1 -> 
	s20'=s20-1,
	s21'=s21+1,
	l56'=l56-1,
	l58'=l58+1;

l57>=1, s20>=1 -> 
	s20'=s20-1,
	s21'=s21+1,
	l57'=l57-1,
	l59'=l59+1;

l58>=1, s20>=1 -> 
	s20'=s20-1,
	s4'=s4+1,
	l58'=l58-1,
	l60'=l60+1;

l59>=1, s20>=1 -> 
	s20'=s20-1,
	s4'=s4+1,
	l59'=l59-1,
	l61'=l61+1;

l24>=1, s21>=1 -> 
	l24'=l24-1,
	l26'=l26+1;

l24>=1, s21>=1 -> 
	l24'=l24-1,
	l30'=l30+1;

l25>=1, s21>=1 -> 
	l25'=l25-1,
	l27'=l27+1;

l25>=1, s21>=1 -> 
	l25'=l25-1,
	l31'=l31+1;

l26>=1, s21>=1 -> 
	l26'=l26-1,
	l29'=l29+1;

l27>=1, s21>=1 -> 
	l27'=l27-1,
	l29'=l29+1;

l28>=1, s21>=1 -> 
	l28'=l28-1,
	l32'=l32+1;

l29>=1, s21>=1 -> 
	l29'=l29-1,
	l33'=l33+1;

l30>=1, s21>=1 -> 
	l30'=l30-1,
	l32'=l32+1;

l30>=1, s21>=1 -> 
	l30'=l30-1,
	l33'=l33+1;

l31>=1, s21>=1 -> 
	l31'=l31-1,
	l32'=l32+1;

l31>=1, s21>=1 -> 
	l31'=l31-1,
	l33'=l33+1;

l32>=1, s21>=1 -> 
	s21'=s21-1,
	s5'=s5+1,
	l32'=l32-1,
	l34'=l34+1;

l33>=1, s21>=1 -> 
	s21'=s21-1,
	s5'=s5+1,
	l33'=l33-1,
	l35'=l35+1;

l44>=1, s21>=1 -> 
	l44'=l44-1,
	l46'=l46+1;

l45>=1, s21>=1 -> 
	l45'=l45-1,
	l47'=l47+1;

l46>=1, s21>=1 -> 
	s21'=s21-1,
	s22'=s22+1,
	l46'=l46-1,
	l48'=l48+1;

l47>=1, s21>=1 -> 
	s21'=s21-1,
	s22'=s22+1,
	l47'=l47-1,
	l49'=l49+1;

l48>=1, s21>=1 -> 
	s21'=s21-1,
	s5'=s5+1,
	l48'=l48-1,
	l50'=l50+1;

l49>=1, s21>=1 -> 
	s21'=s21-1,
	s5'=s5+1,
	l49'=l49-1,
	l51'=l51+1;

l56>=1, s21>=1 -> 
	l56'=l56-1,
	l58'=l58+1;

l57>=1, s21>=1 -> 
	l57'=l57-1,
	l59'=l59+1;

l58>=1, s21>=1 -> 
	s21'=s21-1,
	s5'=s5+1,
	l58'=l58-1,
	l60'=l60+1;

l59>=1, s21>=1 -> 
	s21'=s21-1,
	s5'=s5+1,
	l59'=l59-1,
	l61'=l61+1;

l24>=1, s22>=1 -> 
	l24'=l24-1,
	l26'=l26+1;

l24>=1, s22>=1 -> 
	l24'=l24-1,
	l30'=l30+1;

l25>=1, s22>=1 -> 
	l25'=l25-1,
	l27'=l27+1;

l25>=1, s22>=1 -> 
	l25'=l25-1,
	l31'=l31+1;

l26>=1, s22>=1 -> 
	l26'=l26-1,
	l29'=l29+1;

l27>=1, s22>=1 -> 
	l27'=l27-1,
	l29'=l29+1;

l28>=1, s22>=1 -> 
	l28'=l28-1,
	l32'=l32+1;

l29>=1, s22>=1 -> 
	l29'=l29-1,
	l33'=l33+1;

l30>=1, s22>=1 -> 
	l30'=l30-1,
	l32'=l32+1;

l30>=1, s22>=1 -> 
	l30'=l30-1,
	l33'=l33+1;

l31>=1, s22>=1 -> 
	l31'=l31-1,
	l32'=l32+1;

l31>=1, s22>=1 -> 
	l31'=l31-1,
	l33'=l33+1;

l32>=1, s22>=1 -> 
	s22'=s22-1,
	s6'=s6+1,
	l32'=l32-1,
	l34'=l34+1;

l33>=1, s22>=1 -> 
	s22'=s22-1,
	s6'=s6+1,
	l33'=l33-1,
	l35'=l35+1;

l46>=1, s22>=1 -> 
	l46'=l46-1,
	l48'=l48+1;

l47>=1, s22>=1 -> 
	l47'=l47-1,
	l49'=l49+1;

l48>=1, s22>=1 -> 
	s22'=s22-1,
	s6'=s6+1,
	l48'=l48-1,
	l50'=l50+1;

l49>=1, s22>=1 -> 
	s22'=s22-1,
	s6'=s6+1,
	l49'=l49-1,
	l51'=l51+1;

l54>=1, s22>=1 -> 
	l54'=l54-1,
	l56'=l56+1;

l55>=1, s22>=1 -> 
	l55'=l55-1,
	l57'=l57+1;

l56>=1, s22>=1 -> 
	s22'=s22-1,
	s21'=s21+1,
	l56'=l56-1,
	l58'=l58+1;

l57>=1, s22>=1 -> 
	s22'=s22-1,
	s21'=s21+1,
	l57'=l57-1,
	l59'=l59+1;

l58>=1, s22>=1 -> 
	s22'=s22-1,
	s6'=s6+1,
	l58'=l58-1,
	l60'=l60+1;

l59>=1, s22>=1 -> 
	s22'=s22-1,
	s6'=s6+1,
	l59'=l59-1,
	l61'=l61+1;

l24>=1, s23>=1 -> 
	l24'=l24-1,
	l26'=l26+1;

l24>=1, s23>=1 -> 
	l24'=l24-1,
	l30'=l30+1;

l25>=1, s23>=1 -> 
	l25'=l25-1,
	l27'=l27+1;

l25>=1, s23>=1 -> 
	l25'=l25-1,
	l31'=l31+1;

l26>=1, s23>=1 -> 
	l26'=l26-1,
	l29'=l29+1;

l27>=1, s23>=1 -> 
	l27'=l27-1,
	l29'=l29+1;

l28>=1, s23>=1 -> 
	l28'=l28-1,
	l32'=l32+1;

l29>=1, s23>=1 -> 
	l29'=l29-1,
	l33'=l33+1;

l30>=1, s23>=1 -> 
	l30'=l30-1,
	l32'=l32+1;

l30>=1, s23>=1 -> 
	l30'=l30-1,
	l33'=l33+1;

l31>=1, s23>=1 -> 
	l31'=l31-1,
	l32'=l32+1;

l31>=1, s23>=1 -> 
	l31'=l31-1,
	l33'=l33+1;

l32>=1, s23>=1 -> 
	s23'=s23-1,
	s7'=s7+1,
	l32'=l32-1,
	l34'=l34+1;

l33>=1, s23>=1 -> 
	s23'=s23-1,
	s7'=s7+1,
	l33'=l33-1,
	l35'=l35+1;

l46>=1, s23>=1 -> 
	s23'=s23-1,
	s22'=s22+1,
	l46'=l46-1,
	l48'=l48+1;

l47>=1, s23>=1 -> 
	s23'=s23-1,
	s22'=s22+1,
	l47'=l47-1,
	l49'=l49+1;

l48>=1, s23>=1 -> 
	s23'=s23-1,
	s7'=s7+1,
	l48'=l48-1,
	l50'=l50+1;

l49>=1, s23>=1 -> 
	s23'=s23-1,
	s7'=s7+1,
	l49'=l49-1,
	l51'=l51+1;

l56>=1, s23>=1 -> 
	s23'=s23-1,
	s21'=s21+1,
	l56'=l56-1,
	l58'=l58+1;

l57>=1, s23>=1 -> 
	s23'=s23-1,
	s21'=s21+1,
	l57'=l57-1,
	l59'=l59+1;

l58>=1, s23>=1 -> 
	s23'=s23-1,
	s7'=s7+1,
	l58'=l58-1,
	l60'=l60+1;

l59>=1, s23>=1 -> 
	s23'=s23-1,
	s7'=s7+1,
	l59'=l59-1,
	l61'=l61+1;

l16>=1, s0>=1 -> 
	s0'=s0-1,
	s8'=s8+1,
	l18'=l18+1;

l17>=1, s0>=1 -> 
	s0'=s0-1,
	s8'=s8+1,
	l19'=l19+1;

l16>=1, s1>=1 -> 
	s1'=s1-1,
	s9'=s9+1,
	l18'=l18+1;

l17>=1, s1>=1 -> 
	s1'=s1-1,
	s9'=s9+1,
	l19'=l19+1;

l16>=1, s2>=1 -> 
	s2'=s2-1,
	s10'=s10+1,
	l18'=l18+1;

l17>=1, s2>=1 -> 
	s2'=s2-1,
	s10'=s10+1,
	l19'=l19+1;

l16>=1, s3>=1 -> 
	s3'=s3-1,
	s11'=s11+1,
	l18'=l18+1;

l17>=1, s3>=1 -> 
	s3'=s3-1,
	s11'=s11+1,
	l19'=l19+1;

l16>=1, s4>=1 -> 
	s4'=s4-1,
	s12'=s12+1,
	l18'=l18+1;

l17>=1, s4>=1 -> 
	s4'=s4-1,
	s12'=s12+1,
	l19'=l19+1;

l16>=1, s5>=1 -> 
	s5'=s5-1,
	s13'=s13+1,
	l18'=l18+1;

l17>=1, s5>=1 -> 
	s5'=s5-1,
	s13'=s13+1,
	l19'=l19+1;

l16>=1, s6>=1 -> 
	s6'=s6-1,
	s14'=s14+1,
	l18'=l18+1;

l17>=1, s6>=1 -> 
	s6'=s6-1,
	s14'=s14+1,
	l19'=l19+1;

l16>=1, s7>=1 -> 
	s7'=s7-1,
	s15'=s15+1,
	l18'=l18+1;

l17>=1, s7>=1 -> 
	s7'=s7-1,
	s15'=s15+1,
	l19'=l19+1;


init
l0>=1, s0=1

target
s32>=1,l72>=1
s0=0, s1=0, s2=0, s3=0, s4=0, s5=0, s6=0, s7=0, s8=0, s9=0, s10=0, s11=0, s12=0, s13=0, s14=0, s15=0, s16=0, s17=0, s18=0, s19=0, s20=0, s21=0, s22=0, s23=0, s24=0, s25=0, s26=0, s27=0, s28=0, s29=0, s30=0, s31=0, s32=0, l0=0, l1=0, l2=0, l3=0, l4=0, l5=0, l6=0, l7=0, l8=0, l9=0, l10=0, l11=0, l12=0, l13=0, l14=0, l15=0, l16=0, l17=0, l18=0, l19=0, l20=0, l21=0, l22=0, l23=0, l24=0, l25=0, l26=0, l27=0, l28=0, l29=0, l30=0, l31=0, l32=0, l33=0, l34=0, l35=0, l36=0, l37=0, l38=0, l39=0, l40=0, l41=0, l42=0, l43=0, l44=0, l45=0, l46=0, l47=0, l48=0, l49=0, l50=0, l51=0, l52=0, l53=0, l54=0, l55=0, l56=0, l57=0, l58=0, l59=0, l60=0, l61=0, l62=0, l63=0, l64=0, l65=0, l66=0, l67=0, l68=0, l69=0, l70=0, l71=0, l72=0, 
