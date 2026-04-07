int main1(){
  int an, yes, kf9, c8, ubzr;
  an=10;
  yes=0;
  kf9=0;
  c8=0;
  ubzr=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c8 == yes;
  loop invariant ubzr == 3*yes;
  loop invariant kf9 == 15*(yes/6) + (yes%6)*((yes%6)+1)/2;
  loop invariant 0 <= yes;
  loop invariant yes <= an;
  loop invariant an == 10;
  loop assigns yes, c8, ubzr, kf9;
*/
while (1) {
      if (!(yes < an)) {
          break;
      }
      yes++;
      c8 = yes;
      ubzr = ubzr + 3;
      kf9 = kf9+(c8%6);
  }
}