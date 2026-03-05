int main1(int q,int r){
  int c4v0, d, t7, t;
  c4v0=(r%28)+5;
  d=0;
  t7=0;
  t=0;
  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == d % 2;
  loop invariant q == \at(q, Pre);
  loop invariant r == \at(r, Pre);
  loop invariant t7 == d + d/2;
  loop invariant 0 <= d && (c4v0 <= 0 || d <= c4v0) && c4v0 == (\at(r, Pre) % 28) + 5;
  loop assigns d, t, t7;
*/
while (d<c4v0) {
      t7 = t7 + 1;
      t += 1;
      if (t>=2) {
          t -= 2;
          t7 = t7 + 1;
      }
      d++;
  }
}