int main1(int c){
  int cbd, o3az, ka, mfs, yjy, re;
  cbd=39;
  o3az=0;
  ka=0;
  mfs=0;
  yjy=cbd;
  re=o3az;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant mfs == ((ka * (ka - 1)) / 2);
  loop invariant c == \at(c, Pre) + ((ka * (ka + 1)) / 2);
  loop invariant 0 <= ka <= cbd;
  loop assigns mfs, ka, c;
*/
while (ka<=cbd-1) {
      mfs += ka;
      ka = ka + 1;
      c += ka;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant ka >= 0;
  loop invariant o3az >= 0;
  loop invariant re >= 0;
  loop assigns ka, o3az, yjy;
*/
while (ka<=re-1) {
      ka = ka + 1;
      o3az += ka;
      yjy = re-ka;
  }
}