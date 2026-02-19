int main1(int k,int q){
  int l, i, v;

  l=k-5;
  i=0;
  v=q;

  /* >>> LOOP INVARIANT TO FILL <<< */
    /*@
    loop invariant k == \at(k,Pre);
    loop invariant q == \at(q,Pre);
    loop invariant l == \at(k,Pre) - 5;

    loop invariant v >= q;
    loop invariant l == k - 5;
    loop invariant i >= 0;
    loop invariant (i > 0) ==> (v >= 0);
    loop invariant k == \at(k, Pre);
    loop invariant q == \at(q, Pre);
    loop invariant 0 <= i;

    loop invariant (i == 0) ==> (v == q);
    loop invariant (i >= 1) ==> (v >= q*q);
    loop invariant l == \at(k, Pre) - 5;
    loop invariant (l < 0) ==> (i == 0);
    loop invariant i <= l || l < 0;
    loop assigns i, v;
    loop variant l - i;
  */
  while (i<l) {
      v = v+i;
      v = v*v;
      i = i+1;
  }

}