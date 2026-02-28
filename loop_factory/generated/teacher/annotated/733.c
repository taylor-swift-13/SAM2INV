int main1(int a,int b,int m,int p){
  int s, i, v, t;

  s=a;
  i=0;
  v=p;
  t=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant s == a;
  loop invariant v >= p;
  loop invariant (v - p) % 2 == 0;
  loop invariant p == \at(p, Pre);
  loop invariant a == \at(a, Pre);
  loop invariant b == \at(b, Pre);
  loop invariant m == \at(m, Pre);
  loop invariant (t == v - 2) || (t == 0 && v == p);
  loop invariant v >= \at(p, Pre);
  loop invariant (v - \at(p, Pre)) % 2 == 0;
  loop assigns t, v;
*/
while (1) {
      t = v;
      v = v+2;
  }

}
