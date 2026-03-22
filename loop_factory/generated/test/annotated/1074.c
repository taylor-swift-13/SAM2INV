int main1(int s){
  int i5, lq, re, cv, y, c8, a;
  i5=s-6;
  lq=i5+3;
  re=0;
  cv=(s%28)+10;
  y=0;
  c8=i5;
  a=lq;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant re == y;
  loop invariant cv == ((s % 28) + 10) - y*(y - 1)/2;
  loop invariant s == \at(s,Pre);
  loop invariant i5 == \at(s,Pre) - 6;
  loop invariant lq == \at(s,Pre) - 3;
  loop invariant re >= 0;
  loop invariant c8 == i5 + y * lq;
  loop invariant a == lq + (y * (y + 1)) / 2;
  loop assigns cv, re, c8, y, a;
*/
while (cv>re) {
      cv = cv - re;
      re += 1;
      c8 = c8 + lq;
      y++;
      a = a + re;
  }
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y >= 0;
  loop invariant i5 == \at(s,Pre) - 6;
  loop assigns y, c8, s;
*/
while (y>c8) {
      y = y - c8;
      c8 += 1;
      s = s+(y%8);
      s = s*s;
  }
}