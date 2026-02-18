int main1(int a,int k,int n,int q){
  int l, i, v, b;

  l=70;
  i=l;
  v=1;
  b=0;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 4*b == v*v + 4*v - 5;
    loop invariant i >= 0;
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant i == 70;
    loop invariant i == l;
    loop invariant l == 70;
    loop invariant (v - 1) % 2 == 0;
    loop invariant v >= 1;
    loop invariant ((v - 1) % 2) == 0;
    loop invariant b >= 0;
    loop invariant b == ((v - 1)/2) * ((v - 1)/2 + 3);
    loop invariant i <= 70;
    loop assigns v, b;
  */
  while (i>0) {
      v = v+1;
      b = b+1;
      v = v+1;
      b = b+v;
  }

}