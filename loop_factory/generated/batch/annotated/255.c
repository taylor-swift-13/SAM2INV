int main1(int b,int p){
  int c, v, m;

  c=(p%6)+10;
  v=1;
  m=v;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v >= 1;
  loop invariant (v == 1) || (v % 3 == 0);
  loop invariant v <= c;
  loop invariant c == (\at(p, Pre) % 6 + 10);
  loop invariant p == \at(p, Pre);
  loop invariant v > 0;
  loop invariant c == (p % 6) + 10;
  loop invariant b == \at(b, Pre);
  loop invariant c == \at(p, Pre) % 6 + 10;
  loop invariant v == 1 || v % 3 == 0;
  loop invariant v == 1 || v == 3 || v == 9;
  loop assigns v;
*/
while (v<=c/3) {
      v = v*3;
  }

}
