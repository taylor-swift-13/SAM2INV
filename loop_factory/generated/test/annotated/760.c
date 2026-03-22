int main1(){
  int j, lw, jf, ydcy, xu, y6, dn;
  j=45;
  lw=0;
  jf=(1%28)+8;
  ydcy=(1%22)+5;
  xu=0;
  y6=lw;
  dn=j;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= ydcy <= 6;
  loop invariant 0 <= xu;
  loop invariant 0 <= y6;
  loop invariant (y6 % (j+dn) == 0);
  loop invariant jf > 0;
  loop invariant j == dn;
  loop assigns xu, jf, ydcy, y6;
*/
while (ydcy!=0) {
      if (ydcy%2==1) {
          xu += jf;
          ydcy--;
      }
      jf = 2*jf;
      ydcy = ydcy/2;
      y6 += j;
      y6 += dn;
  }
}