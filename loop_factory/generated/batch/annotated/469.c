int main1(int p,int q){
  int k, x, c, t;

  k=p+19;
  x=0;
  c=p;
  t=-8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant c == x + p;
  loop invariant k == p + 19;
  loop invariant q == \at(q, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant x >= 0;
  loop invariant c >= p;
  loop invariant c == p + x;
  loop invariant c - x == p;

  loop assigns c, x;
*/
while (1) {
      if (x>=k) {
          break;
      }
      c = c+1;
      x = x+1;
  }

}
