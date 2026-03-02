int main1(int n,int q){
  int b, k, y, c;

  b=q;
  k=b;
  y=1;
  c=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == q;
  loop invariant k <= b;
  loop invariant y % 2 == 1;
  loop invariant (y + 3) % 4 == 0;
  loop invariant y >= 1;
  loop invariant q == \at(q, Pre);
  loop invariant n == \at(n, Pre);
  loop invariant k <= b && y >= 1;
  loop invariant n == \at(n, Pre) && q == \at(q, Pre);
  loop invariant q == \at(q, Pre) && n == \at(n, Pre) && b == q;
  loop invariant k <= b && (y == 1 || y % 3 == 0) && k >= q;
  loop invariant k >= q;
  loop invariant b == q && k <= b;
  loop assigns y, k;
*/
while (1) {
      if (k>=b) {
          break;
      }
      y = y+2;
      k = k+1;
      y = y*3;
  }

}
