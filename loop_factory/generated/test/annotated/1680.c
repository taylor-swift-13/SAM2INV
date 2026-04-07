int main1(int b){
  int z0y, cwfp, c, wg;
  z0y=38;
  cwfp=0;
  c=0;
  wg=cwfp;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == cwfp % 2;
  loop invariant wg == (cwfp + 1) / 2;
  loop invariant 0 <= cwfp <= z0y;
  loop assigns c, cwfp, wg;
*/
while (cwfp < z0y) {
      c = 1 - c;
      cwfp = cwfp + 1;
      wg = wg + c;
  }
}