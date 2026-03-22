int main1(){
  int gxrw, q3t, hde, gr;
  gxrw=0;
  q3t=0;
  hde=0;
  gr=(1%18)+5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant (hde == q3t);
  loop invariant gr + q3t == 6;
  loop invariant gxrw % 2 == 0;
  loop invariant hde <= 6;
  loop invariant q3t <= 6;
  loop assigns gr, hde, q3t, gxrw;
*/
while (gr>0) {
      hde = hde+1*1;
      gxrw = gxrw+1*1;
      gr -= 1;
      q3t = q3t+1*1;
      gxrw = gxrw*2;
  }
}