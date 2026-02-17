int main1(int b,int k,int q){
  int l, i, v, t, u, f, c, x;

  l=63;
  i=0;
  v=2;
  t=k;
  u=i;
  f=k;
  c=-5;
  x=i;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant v == i + 2;
    loop invariant u == i;
    loop invariant t == k + i*(i-1)/2;
    loop invariant (i == 0) ==> (f == k);
    loop invariant k == \at(k, Pre);
    loop assigns f, v, t, u, i;
  */
  while (i<l) {
      f = v+t+u;
      v = v+1;
      t = t+u;
      u = u+1;
      i = i+1;
  }

}