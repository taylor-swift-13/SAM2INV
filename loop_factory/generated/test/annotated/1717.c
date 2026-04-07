int main1(){
  int bw, y0vp, p3, vug;
  bw=0;
  y0vp=-19067;
  p3=1+5;
  vug=bw;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant vug == p3*(p3+1)/2 - 21;
  loop invariant y0vp == (p3*p3 + 5*p3 - 38200)/2;
  loop invariant p3 >= 6;
  loop assigns y0vp, p3, vug;
*/
while (1) {
      if (!(y0vp<=-5)) {
          break;
      }
      y0vp = y0vp+p3+3;
      p3++;
      vug = vug + p3;
  }
}