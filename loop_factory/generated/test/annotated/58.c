int main1(int b,int h){
  int u2, jzd, h7, s;
  u2=71;
  jzd=0;
  h7=0;
  s=4;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= jzd;
  loop invariant jzd < u2;
  loop invariant s >= 0;
  loop invariant s == 4 - jzd;
  loop invariant h7 == 4*jzd - (jzd*(jzd - 1))/2;
  loop invariant b == \at(b, Pre) + 3*jzd - (jzd*(jzd - 1))/2;
  loop invariant h == \at(h, Pre);
  loop assigns b, h7, jzd, s;
*/
while (jzd<u2&&s>0) {
      h7 = h7 + s;
      jzd++;
      s -= 1;
      b = b + s;
  }
}