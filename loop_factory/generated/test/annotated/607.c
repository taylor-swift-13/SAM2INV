int main1(){
  int lzp, jfti, nh0, yt;
  lzp=67;
  jfti=-4;
  nh0=3;
  yt=7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant nh0 - yt == -4;
  loop invariant lzp == 67;
  loop invariant jfti <= lzp;
  loop invariant yt - 4*jfti == 23;
  loop assigns jfti, yt, nh0;
*/
while (1) {
      if (!(jfti<=lzp-1)) {
          break;
      }
      jfti = jfti + 1;
      yt += 4;
      nh0 += 4;
  }
}