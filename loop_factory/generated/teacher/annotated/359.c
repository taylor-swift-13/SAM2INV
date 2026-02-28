int main1(int a,int p){
  int l, t, w, v;

  l=39;
  t=0;
  w=l;
  v=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant v == 0;
  loop invariant w == 39 + t*(t-1)/2;
  loop invariant 0 <= t <= l;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant t <= l;
  loop invariant l == 39;
  loop invariant t >= 0;
  loop invariant w == l + t*(t-1)/2;
  loop invariant 0 <= t;
  loop invariant w >= 39;
  loop assigns w, v, t;
*/
while (t<=l-1) {
      w = w+t;
      v = v*v;
      v = v+w*v;
      t = t+1;
  }

}
