int main1(int b,int n,int p){
  int l, i, v, h, e, w, u, k;

  l=39;
  i=l;
  v=b;
  h=-1;
  e=n;
  w=l;
  u=p;
  k=-4;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant i >= 0;
    loop invariant i <= l;
    loop invariant v == b + (l - i);
    loop invariant h == -1 + (l - i) * b + ((l - i) * (l - i + 1)) / 2;
    loop invariant b == \at(b, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop assigns v, h, i;
  */
  while (i>0) {
      v = v+1;
      h = h+v;
      i = i-1;
  }

}