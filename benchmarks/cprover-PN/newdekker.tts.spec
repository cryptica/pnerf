vars
s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 s14 s15 s16 s17 s18 s19 s20 s21 s22 s23 s24 s25 s26 s27 s28 s29 s30 s31 s32 s33 l0 l1 l2 l3 l4 l5 l6 l7 l8 l9 l10 l11 l12 l13 l14 l15 l16 

rules
l0>=1, s0>=1 -> 
	s0'=s0-1,
	s1'=s1+1,
	l0'=l0-1,
	l1'=l1+1;

l0>=1, s1>=1 -> 
	s1'=s1-1,
	s2'=s2+1,
	l0'=l0-1,
	l6'=l6+1;

l0>=1, s2>=1 -> 
	s2'=s2-1,
	s3'=s3+1,
	l0'=l0-1,
	l11'=l11+1;

l0>=1, s3>=1 -> 
	s3'=s3-1,
	s4'=s4+1,
	l0'=l0-1,
	l13'=l13+1;

l0>=1, s4>=1 -> 
	s4'=s4-1,
	s5'=s5+1,
	l0'=l0-1,
	l15'=l15+1;

l1>=1, s5>=1 -> 
	s5'=s5-1,
	s6'=s6+1,
	l1'=l1-1,
	l2'=l2+1;

l2>=1, s5>=1 -> 
	s5'=s5-1,
	s8'=s8+1,
	l2'=l2-1,
	l3'=l3+1;

l2>=1, s5>=1 -> 
	s5'=s5-1,
	s26'=s26+1,
	l2'=l2-1,
	l5'=l5+1;

l3>=1, s5>=1 -> 
	s5'=s5-1,
	s12'=s12+1,
	l3'=l3-1,
	l2'=l2+1;

l3>=1, s5>=1 -> 
	s5'=s5-1,
	s16'=s16+1,
	l3'=l3-1,
	l4'=l4+1;

l4>=1, s5>=1 -> 
	s5'=s5-1,
	s22'=s22+1,
	l4'=l4-1,
	l1'=l1+1;

l5>=1, s5>=1 -> 
	s5'=s5-1,
	s30'=s30+1,
	l5'=l5-1,
	l1'=l1+1;

l6>=1, s5>=1 -> 
	s5'=s5-1,
	s7'=s7+1,
	l6'=l6-1,
	l7'=l7+1;

l7>=1, s5>=1 -> 
	s5'=s5-1,
	s10'=s10+1,
	l7'=l7-1,
	l8'=l8+1;

l7>=1, s5>=1 -> 
	s5'=s5-1,
	s28'=s28+1,
	l7'=l7-1,
	l10'=l10+1;

l8>=1, s5>=1 -> 
	s5'=s5-1,
	s14'=s14+1,
	l8'=l8-1,
	l7'=l7+1;

l8>=1, s5>=1 -> 
	s5'=s5-1,
	s19'=s19+1,
	l8'=l8-1,
	l9'=l9+1;

l9>=1, s5>=1 -> 
	s5'=s5-1,
	s24'=s24+1,
	l9'=l9-1,
	l6'=l6+1;

l10>=1, s5>=1 -> 
	s5'=s5-1,
	s32'=s32+1,
	l10'=l10-1,
	l6'=l6+1;

l11>=1, s6>=1 -> 
	s6'=s6-1,
	s5'=s5+1,
	l11'=l11-1,
	l12'=l12+1;

l13>=1, s7>=1 -> 
	s7'=s7-1,
	s5'=s5+1,
	l13'=l13-1,
	l14'=l14+1;

l14>=1, s8>=1 -> 
	s8'=s8-1,
	s9'=s9+1,
	l14'=l14-1,
	l0'=l0+1;

l0>=1, s9>=1 -> 
	s9'=s9-1,
	s5'=s5+1,
	l0'=l0-1,
	l14'=l14+1;

l12>=1, s10>=1 -> 
	s10'=s10-1,
	s11'=s11+1,
	l12'=l12-1,
	l0'=l0+1;

l0>=1, s11>=1 -> 
	s11'=s11-1,
	s5'=s5+1,
	l0'=l0-1,
	l12'=l12+1;

l15>=1, s12>=1 -> 
	s12'=s12-1,
	s13'=s13+1,
	l15'=l15-1,
	l0'=l0+1;

l0>=1, s13>=1 -> 
	s13'=s13-1,
	s5'=s5+1,
	l0'=l0-1,
	l15'=l15+1;

l16>=1, s14>=1 -> 
	s14'=s14-1,
	s15'=s15+1,
	l16'=l16-1,
	l0'=l0+1;

l0>=1, s15>=1 -> 
	s15'=s15-1,
	s5'=s5+1,
	l0'=l0-1,
	l16'=l16+1;

l12>=1, s16>=1 -> 
	s16'=s16-1,
	s17'=s17+1,
	l12'=l12-1,
	l11'=l11+1;

l16>=1, s17>=1 -> 
	s17'=s17-1,
	s18'=s18+1,
	l16'=l16-1,
	l0'=l0+1;

l0>=1, s18>=1 -> 
	s18'=s18-1,
	s5'=s5+1,
	l0'=l0-1,
	l16'=l16+1;

l14>=1, s19>=1 -> 
	s19'=s19-1,
	s20'=s20+1,
	l14'=l14-1,
	l13'=l13+1;

l15>=1, s20>=1 -> 
	s20'=s20-1,
	s21'=s21+1,
	l15'=l15-1,
	l0'=l0+1;

l0>=1, s21>=1 -> 
	s21'=s21-1,
	s5'=s5+1,
	l0'=l0-1,
	l15'=l15+1;

l15>=1, s22>=1 -> 
	s22'=s22-1,
	s23'=s23+1,
	l15'=l15-1,
	l0'=l0+1;

l0>=1, s23>=1 -> 
	s23'=s23-1,
	s5'=s5+1,
	l0'=l0-1,
	l15'=l15+1;

l16>=1, s24>=1 -> 
	s24'=s24-1,
	s25'=s25+1,
	l16'=l16-1,
	l0'=l0+1;

l0>=1, s25>=1 -> 
	s25'=s25-1,
	s5'=s5+1,
	l0'=l0-1,
	l16'=l16+1;

l13>=1, s26>=1 -> 
	s26'=s26-1,
	s27'=s27+1,
	l13'=l13-1,
	l0'=l0+1;

l0>=1, s27>=1 -> 
	s27'=s27-1,
	s5'=s5+1,
	l0'=l0-1,
	l13'=l13+1;

l11>=1, s28>=1 -> 
	s28'=s28-1,
	s29'=s29+1,
	l11'=l11-1,
	l0'=l0+1;

l0>=1, s29>=1 -> 
	s29'=s29-1,
	s5'=s5+1,
	l0'=l0-1,
	l11'=l11+1;

l12>=1, s30>=1 -> 
	s30'=s30-1,
	s31'=s31+1,
	l12'=l12-1,
	l11'=l11+1;

l15>=1, s31>=1 -> 
	s31'=s31-1,
	s5'=s5+1,
	l15'=l15-1,
	l16'=l16+1;

l14>=1, s32>=1 -> 
	s32'=s32-1,
	s33'=s33+1,
	l14'=l14-1,
	l13'=l13+1;

l16>=1, s33>=1 -> 
	s33'=s33-1,
	s5'=s5+1,
	l16'=l16-1,
	l15'=l15+1;


init
s1=0, s2=0, s3=0, s4=0, s5=0, s6=0, s7=0, s8=0, s9=0, s10=0, s11=0, s12=0, s13=0, s14=0, s15=0, s16=0, s17=0, s18=0, s19=0, s20=0, s21=0, s22=0, s23=0, s24=0, s25=0, s26=0, s27=0, s28=0, s29=0, s30=0, s31=0, s32=0, s33=0, l1=0, l2=0, l3=0, l4=0, l5=0, l6=0, l7=0, l8=0, l9=0, l10=0, l11=0, l12=0, l13=0, l14=0, l15=0, l16=0, 
l0>=1, s0=1

target
s5>=1,l5>=1,l10>=1
