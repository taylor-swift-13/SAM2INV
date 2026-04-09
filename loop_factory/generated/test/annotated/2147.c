int main1(int e){
  int k0, gzhs, lk7e, prr, lhr;
  k0=57;
  gzhs=0;
  lk7e=-1;
  prr=-2;
  lhr=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= gzhs;
  loop invariant gzhs <= k0;
  loop invariant prr + lk7e == -3;
  loop invariant lhr == 4 + (gzhs * (gzhs + 1)) / 2;
  loop assigns prr, gzhs, lk7e, lhr;
*/
while (gzhs < k0) {
      prr = prr - (e*(e>=0) - e*(e<0));
      gzhs = gzhs + 1;
      lk7e = lk7e + (e*(e>=0) - e*(e<0));
      lhr += gzhs;
  }
}