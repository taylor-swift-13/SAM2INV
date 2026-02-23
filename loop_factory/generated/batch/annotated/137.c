int main1(int p){
  int m, c, v;

  m=33;
  c=1;
  v=c;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant m == 33;
  loop invariant c >= 1;
  loop invariant c <= m;
  loop invariant v >= 1;
  loop invariant p == \at(p, Pre);
  loop invariant (c > 1) ==> (v % 2 == 0);
  loop invariant 1 <= c;
  loop invariant v >= c;

  loop assigns c, v;
*/
while (c<m) {
      if (c+3<=m+m) {
          v = v+v;
      }
      c = c+1;
  }

}
