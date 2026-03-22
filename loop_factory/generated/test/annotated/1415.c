int main1(){
  int ijx, cf, lf, uey;
  ijx=53;
  cf=0;
  lf=0;
  uey=ijx;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant lf == cf*(cf+1)/2;
  loop invariant uey == ijx*(cf+1);
  loop invariant 0 <= cf <= ijx;
  loop assigns cf, lf, uey;
*/
while (cf < ijx) {
      lf = lf + (cf + 1);
      uey = uey + ijx;
      cf = cf + 1;
  }
}