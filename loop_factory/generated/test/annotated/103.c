int main1(int a,int b,int m,int p){
  int l, i, v, k;

  l=41;
  i=l;
  v=a;
  k=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@

    loop invariant i >= 0;
    loop invariant i <= 41;
    loop invariant a == \at(a, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant p == \at(p, Pre);
    loop invariant m * k >= 0;
    loop invariant (m == 0) ==> (k == 0);
    loop invariant b == \at(b, Pre);
    loop invariant l == 41;

    loop assigns i, k;
    loop variant i;
  */
  while (i>0) {
      k = k+k;
      i = i-1;
  }

}