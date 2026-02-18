int main1(int a,int n){
  int l, i, v, w, m;

  l=21;
  i=1;
  v=n;
  w=l;
  m=6;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant (v - \at(n, Pre)) % w == 0;
    loop invariant i > 0;

    loop invariant v >= \at(n, Pre);
    loop invariant w == l;
    loop invariant l == 21;
    loop invariant v >= n;
    loop invariant ((v - n) % w) == 0;
    loop invariant (v - n) % w == 0;
    loop invariant i >= 1;
    loop invariant i <= 2*l;
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+w;
      i = i*2;
  }

}