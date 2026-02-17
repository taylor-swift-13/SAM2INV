int main1(int a,int n,int p){
  int l, i, v, t, q, r, g;

  l=49;
  i=0;
  v=4;
  t=p;
  q=p;
  r=a;
  g=n;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant 0 <= i;
    loop invariant i <= l;
    loop invariant v == i + 4;
    loop invariant t == p + (i*i - 3*i)/2;
    loop invariant (i % 2 == 0) ==> (q == p);
    loop invariant (i % 2 != 0) ==> (q == a - p);
    loop assigns v, t, q, i;
  */
  while (i<l) {
      v = v+1;
      t = t-1;
      t = t+i;
      q = r-q;
      i = i+1;
  }

}