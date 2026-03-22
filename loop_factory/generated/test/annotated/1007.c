int main1(){
  int kx1, ua, b, ko;
  kx1=(1%16)+10;
  ua=-5;
  b=3;
  ko=1;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 3 <= b <= 9;
  loop invariant ko == 1 || ko == -1;
  loop invariant ((b - ua) % 2 == 0);
  loop invariant -5 <= ua <= kx1;
  loop assigns ko, b, ua;
*/
while (ua<=kx1-1) {
      if (b>=9) {
          ko = -1;
      }
      if (!(b>3)) {
          ko = 1;
      }
      ua++;
      b += ko;
  }
}