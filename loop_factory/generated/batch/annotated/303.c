int main1(int p,int q){
  int u, t, v;

  u=62;
  t=0;
  v=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant t >= 0;
  loop invariant t <= u;
  loop invariant (\at(p,Pre) >= 0) ==> (v >= \at(p,Pre));
  loop invariant p == \at(p, Pre);
  loop invariant q == \at(q, Pre);

  loop invariant u == 62;

  loop invariant 0 <= t;

  loop assigns v, t;
*/
while (t<=u-1) {
      if (v+3<u) {
          v = v+v;
      }
      v = v+1;
      v = v+t;
      t = t+1;
  }

}
