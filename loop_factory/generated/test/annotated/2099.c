int main1(int z){
  int jy, p, wgk, tnjg;
  jy=z*2;
  p=0;
  wgk=6;
  tnjg=p;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant tnjg == 0;
  loop invariant wgk == (p + 6);
  loop invariant p >= 0;
  loop invariant jy == 2 * \at(z, Pre);
  loop invariant (jy < 0) || (p <= jy);
  loop assigns p, wgk, tnjg;
*/
while (1) {
      if (!(p < jy)) {
          break;
      }
      tnjg = tnjg + tnjg;
      wgk += 1;
      p++;
  }
}