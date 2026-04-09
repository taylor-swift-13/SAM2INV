int main1(){
  int w9, mmz1, ctct, w4r, g8;
  w9=1;
  mmz1=1;
  ctct=0;
  w4r=-4;
  g8=w9;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mmz1 >= 1;
  loop invariant (g8 == 1 + ctct * w9);
  loop invariant (w4r == -4 + 2 * ctct + w9 * ctct * (ctct + 1));
  loop invariant mmz1 == (1 << ctct);
  loop invariant w9 == 1;
  loop assigns ctct, mmz1, g8, w4r;
*/
while (mmz1<w9) {
      ctct++;
      mmz1 = 2*mmz1;
      g8 += w9;
      w4r = w4r+g8+g8;
  }
}