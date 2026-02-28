int main1(int a,int q){
  int u, i, b, d, n, v;

  u=57;
  i=0;
  b=a;
  d=0;
  n=u;
  v=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 2*b - 3*d == 2*a;
  loop invariant d >= 0;
  loop invariant a == \at(a, Pre);
  loop invariant q == \at(q, Pre);
  loop invariant u == 57;
  loop invariant (b - a) % 3 == 0;
  loop invariant b >= a;
  loop invariant d % 2 == 0;
  loop invariant 2*(b - a) == 3*d;
  loop invariant 3*d == 2*(b - a);
  loop assigns b, d;
*/
while (1) {
      b = b+2;
      d = d+2;
      b = b+1;
  }

}
