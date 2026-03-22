int main1(){
  int yw, ogwq, xc, fbye, bl, e;
  yw=1;
  ogwq=(1%60)+60;
  xc=(1%9)+2;
  fbye=0;
  bl=0;
  e=yw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= bl;
  loop invariant bl < xc;
  loop invariant e == yw;
  loop invariant fbye >= 0;
  loop invariant ogwq >= xc*fbye + bl;
  loop invariant ogwq == 61;
  loop invariant xc == 3;
  loop invariant e == 1;
  loop assigns bl, fbye, e;
*/
while (ogwq>xc*fbye+bl) {
      if (bl==xc-1) {
          bl = 0;
          fbye += 1;
      }
      else {
          bl += 1;
      }
      e = e+fbye-fbye;
  }
}