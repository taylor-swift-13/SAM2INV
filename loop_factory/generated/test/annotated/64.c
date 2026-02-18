int main1(int b,int k,int n,int p){
  int l, i, v, g;

  l=13;
  i=l;
  v=0;
  g=p;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant v == 0;
    loop invariant g == \at(p, Pre);
    loop invariant 0 <= i <= 13;
    loop invariant i >= 0;
    loop invariant i <= 13;
    loop invariant l == 13;
    loop invariant g == p;
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant 0 <= i && i <= 13;
    loop assigns v, g, i;
  */
  while (i>0) {
      v = v*2;
      g = g+v;
      i = i-1;
  }

}