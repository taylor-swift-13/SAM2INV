int main1(int b,int k,int n){
  int l, i, v, q;

  l=34;
  i=0;
  v=b;
  q=k;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant 0 <= i && i <= l;
    loop invariant (i == 0) ==> (v == b);
    loop invariant (i > 0) ==> (v == l + b);
    loop invariant b == \at(b, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v+q+q;
      v = v+1;
      v = q-v;
      if (i+5<=i+l) {
          v = l+b;
      }
      i = i+1;
  }

}