int main1(int a,int k,int n,int q){
  int l, i, v;

  l=a+18;
  i=0;
  v=-6;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant (a == \at(a, Pre) && k == \at(k, Pre) && n == \at(n, Pre) && q == \at(q, Pre));
    loop invariant (l < 0) || (i <= l);
    loop invariant (i == 0) ==> (v == -6);
    loop invariant (i > 0) ==> (v >= 0);
    loop invariant l == a + 18;
    loop invariant i >= 0;
    loop invariant v >= -6;
    loop invariant (i > 0) ==> (v > 0);
    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && n == \at(n, Pre) && q == \at(q, Pre);
    loop invariant (i > 0) ==> (v > -6);

    loop invariant a == \at(a, Pre);
    loop invariant k == \at(k, Pre);
    loop invariant n == \at(n, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant (i >= 2) ==> (v >= 0);
    loop assigns v, i;
    loop variant l - i;
  */
  while (i<l) {
      v = v*2;
      v = v*v;
      i = i+1;
  }

}