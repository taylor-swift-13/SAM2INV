int main1(){
  int ig, s5, wkf2, r2, r;
  ig=1+11;
  s5=0;
  wkf2=(1%28)+10;
  r2=-4;
  r=ig;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant r2 == -4 + 2*s5;
  loop invariant wkf2 == 11 - s5*(s5-1)/2;
  loop invariant s5 >= 0;
  loop invariant ig == 12;
  loop invariant r  == 12 + s5*(s5+1)/2;
  loop assigns wkf2, s5, r2, r;
*/
while (1) {
      if (!(wkf2>s5)) {
          break;
      }
      wkf2 -= s5;
      s5 = s5 + 1;
      r2 = (2)+(r2);
      r += s5;
  }
}