int main1(int a,int p){
  int m, y, b;

  m=26;
  y=m;
  b=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant y >= 1;
  loop invariant m == y;
  loop invariant b >= y;
  loop invariant (b - y) % (4 + y) == 0;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant m == 26;
  loop invariant y == m;
  loop invariant (b - 26) % 30 == 0;
  loop invariant y < m + 5;
  loop invariant y == 26;
  loop invariant b >= 26;
  loop invariant b % 30 == 26;
  loop assigns b;
*/
while (y>=1) {
      b = b+4;
      if (y<m+5) {
          b = b+y;
      }
  }

}
