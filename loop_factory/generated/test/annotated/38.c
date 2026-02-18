int main1(int a,int k,int m,int n){
  int l, i, v, e;

  l=16;
  i=0;
  v=i;
  e=m;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant m == \at(m, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant i <= l;
    loop invariant e == v + m;
    loop invariant 0 <= i <= l;
    loop invariant l == 16;
    loop invariant e * m >= 0;
    loop invariant 0 <= i;
    loop invariant i >= 0;
    loop assigns v, e, i;
    loop variant (l - i);
  */
  while (i<l) {
      v = v+e;
      e = e+e;
      i = i+1;
  }

}