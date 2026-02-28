int main1(int a,int p){
  int l, t, w, v;

  l=39;
  t=0;
  w=l;
  v=t;

  /* >>> LOOP INVARIANT TO FILL <<< */
/*@
  loop invariant 0 <= t;
  loop invariant t <= l;
  loop invariant w == 39 + t;
  loop invariant v == t*41 + (t*(t-1))/2;
  loop invariant a == \at(a, Pre);
  loop invariant p == \at(p, Pre);
  loop invariant v == 40*t + (t*(t+1))/2;
  loop invariant w == l + t;
  loop invariant v == (l+1)*t + t*(t+1)/2;
  loop invariant t >= 0;
  loop invariant l == 39;
  loop invariant 2*v == t*t + 81*t;
  loop invariant 0 <= t <= l;
  loop invariant v == t*(l+2) + t*(t-1)/2;
  loop assigns w, v, t;
*/
while (t<=l-1) {
      w = w+1;
      v = v+w;
      v = v+1;
      t = t+1;
  }

}
