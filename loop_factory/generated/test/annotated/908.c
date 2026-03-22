int main1(int y){
  int s, uf, v, g6d, d;
  s=y+6;
  uf=0;
  v=0;
  g6d=-1;
  d=s;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant g6d == -1;
  loop invariant s == y + 6;
  loop invariant s == (\at(y, Pre) + 6);
  loop invariant (v == 0) ==> (uf == 0);
  loop invariant (v > 0) ==> (uf == s);
  loop invariant (d - v * y) == \at(y, Pre) + 6;
  loop invariant (0 <= v);
  loop invariant (v <= 1);
  loop assigns d, g6d, uf, v;
*/
while (uf<s) {
      v++;
      d = d + y;
      g6d = g6d + uf;
      uf = s;
  }
}