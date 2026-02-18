int main1(int k,int m,int n,int p){
  int l, i, v, u, y;

  l=52;
  i=l;
  v=p;
  u=l;
  y=-1;

  /*>>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v + i == p + 52;
    loop invariant 0 <= i <= 52;
    loop invariant p <= v <= p + 52;
    loop invariant u == 52;
    loop invariant l == 52;
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant i <= l;
    loop invariant v - p == l - i;
    loop invariant i >= 0;
    loop invariant v == p + (l - i);
    loop invariant u == l;
    loop invariant (k == \at(k, Pre));
    loop invariant (m == \at(m, Pre));
    loop invariant (p == \at(p, Pre));
    loop invariant (n == \at(n, Pre));
    loop invariant ((i + v) == (\at(p, Pre) + 52));
    loop invariant (u == 52);
    loop assigns v, u, i;
    loop variant i;
  */
  while (i>0) {
      v = v+1;
      u = u-1;
      u = u+1;
      i = i-1;
  }

}