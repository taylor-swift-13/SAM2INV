int main1(int a,int p){
  int r, j, y, v;

  r=(a%24)+13;
  j=2;
  y=p;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant j >= 2;

  loop invariant y == p + 2*(j - 2);
  loop invariant r == (a % 24) + 13;
  loop invariant p == \at(p, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant y - 2*j == p - 4;
  loop invariant y >= p;
  loop invariant y == 2*j + p - 4;
  loop invariant r == (\at(a, Pre) % 24) + 13;
  loop assigns y, j;
*/
while (1) {
      if (j>=r) {
          break;
      }
      y = y+2;
      j = j+1;
  }

}
