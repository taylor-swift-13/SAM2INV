int main1(){
  int d7, ccm, yi, rm, uy, l;
  d7=1+24;
  ccm=0;
  yi=-3;
  rm=ccm;
  uy=d7;
  l=d7;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant rm == ccm * uy;
  loop invariant yi == -3 + ccm * uy;
  loop invariant l == d7 + ccm*(ccm+1)/2;
  loop invariant 0 <= ccm;
  loop invariant ccm <= d7;
  loop assigns ccm, rm, l, yi;
*/
while (ccm < d7) {
      ccm++;
      rm += uy;
      l = l + ccm;
      yi += uy;
  }
}