int main1(int a,int b,int p){
  int l, i, v, u, n, o;

  l=59;
  i=0;
  v=-3;
  u=p;
  n=i;
  o=a;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i <= l;
    loop invariant v == -3 + i;
    loop invariant u == p - i;
    loop invariant p == \at(p, Pre);
    loop invariant a == \at(a, Pre);
    loop assigns i, v, u;
    loop variant l - i;
  */
while (i<l) {
      v = v+1;
      u = u-1;
      i = i+1;
  }

}