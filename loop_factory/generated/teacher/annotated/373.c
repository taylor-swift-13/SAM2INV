int main1(int b,int p){
  int c, v, m;

  c=(p%6)+10;
  v=1;
  m=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == \at(p, Pre) % 6 + 10;
  loop invariant p == \at(p, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant v >= 1;
  loop invariant v <= c;
  loop invariant m == 1;
  loop invariant v == 1 || v % 3 == 0;
  loop invariant c == (\at(p, Pre) % 6) + 10;
  loop assigns m, v;
*/
while (v<=c/3) {
      m = m*m;
      v = v*3;
  }

}
