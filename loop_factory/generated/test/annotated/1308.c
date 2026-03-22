int main1(){
  int k67, v0t, z9gz, sa, k7, mb;
  k67=1+6;
  v0t=k67;
  z9gz=0;
  sa=(1%28)+10;
  k7=3;
  mb=v0t;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant k7 == 3 + v0t * z9gz;
  loop invariant sa == 11 - (z9gz * (z9gz - 1)) / 2;
  loop invariant mb == 7 + 11 * z9gz - ((z9gz - 1) * z9gz * (z9gz + 1)) / 6;
  loop invariant mb >= v0t;
  loop invariant sa >= 0;
  loop invariant z9gz >= 0;
  loop invariant mb >= 7;
  loop assigns k7, mb, sa, z9gz;
*/
while (sa>z9gz) {
      sa -= z9gz;
      k7 += v0t;
      mb += sa;
      z9gz += 1;
  }
}