int main1(int a,int b,int n,int p){
  int l, q, t, v, h, e, y;

  l=p;
  q=0;
  t=-1;
  v=-3;
  h=a;
  e=q;
  y=l;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t == q - 1;
  loop invariant h == a + 3*q;
  loop invariant l == p;
  loop invariant p == \at(p, Pre);
  loop invariant (p < b+4) ==> (y == p + q*(q-1));
  loop invariant (p >= b+4) ==> (y == p + (q*(q-1))/2);
  loop invariant q >= 0;
  loop invariant t >= -1;
  loop invariant h >= a;
  loop invariant y >= p;
  loop invariant (l < b+4) ==> (y == p + q*(q-1));

  loop invariant a == \at(a, Pre);
  loop invariant (p < b+4) ==> y == p + q*(q-1) && (p >= b+4) ==> y == p + q*(q-1)/2;
  loop invariant (p < b + 4) ==> y == p + q*(q - 1);
  loop invariant (p >= b + 4) ==> y == p + q*(q - 1)/2;
  loop assigns t, h, y, q;
*/
while (1) {
      t = t+1;
      h = h+3;
      y = y+q;
      if (l<b+4) {
          y = y+t;
      }
      q = q+1;
  }

}
