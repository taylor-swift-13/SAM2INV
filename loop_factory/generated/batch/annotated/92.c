int main1(int b,int q){
  int y, a, r;

  y=54;
  a=0;
  r=y;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant b == \at(b, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant a >= 0;
  loop invariant a <= y;
  loop invariant r == y - 4*a;
  loop invariant y == 54;
  loop invariant r + 4*a == y;
  loop invariant 0 <= a;
  loop invariant r == 54 - 4*a;
  loop assigns a, r;
*/
while (a<y) {
      r = r+(-4);
      a = a+1;
  }

}
