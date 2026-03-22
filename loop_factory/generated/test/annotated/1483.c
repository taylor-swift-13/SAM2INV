int main1(){
  int kj, upb, ohc, cg;
  kj=5;
  upb=10;
  ohc=3;
  cg=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kj == 5;
  loop invariant cg == upb - 6;
  loop invariant ohc == upb - 7;
  loop invariant upb >= 0;
  loop assigns upb, cg, ohc;
*/
while (1) {
      if (!(upb > 0 && kj > 0)) {
          break;
      }
      upb--;
      cg -= 1;
      ohc = (ohc)+(-(1));
  }
}