int main1(int s,int m){
  int il, z00, g, kh, y;
  il=(s%17)+12;
  z00=0;
  g=0;
  kh=0;
  y=5;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant kh == g*(11 - g)/2;
  loop invariant (y == 5 - g);
  loop invariant (m == \at(m, Pre));
  loop invariant (il == ((\at(s, Pre)) % 17) + 12);
  loop invariant il == (s % 17) + 12;
  loop invariant g >= 0;
  loop invariant m == \at(m,Pre) + g * z00;
  loop assigns g, kh, m, y;
*/
while (1) {
      if (!(g<il&&y>0)) {
          break;
      }
      kh = kh + y;
      g++;
      m += z00;
      y -= 1;
  }
}