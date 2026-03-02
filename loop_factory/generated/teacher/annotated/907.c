int main1(int a,int q){
  int x, u, d;

  x=q;
  u=4;
  d=8;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant u == 4;
  loop invariant x == q;
  loop invariant d == 8 || d == u%5;
  loop invariant d >= 4;
  loop invariant 4 <= d && d <= 8;
  loop invariant u == 4 && (d == 8 || d == 4) && d <= 8;
  loop invariant q == \at(q, Pre);
  loop invariant d == 8 || d == (u % 5);
  loop invariant x == q && u == 4;
  loop invariant (d == 8 || d == 4) && (q == \at(q, Pre)) && (a == \at(a, Pre));
  loop invariant (d == u % 5) || (d == 8);
  loop invariant 0 <= d && d <= 8;

  loop invariant d == 8 || d == 4;
  loop invariant d <= 8;
  loop invariant d >= 0;
  loop assigns d;
*/
while (u+1<=x) {
      d = d+2;
      d = u%5;
  }

}
