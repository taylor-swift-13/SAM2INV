int main1(int a,int k,int m,int q){
  int l, i, v;

  l=52;
  i=0;
  v=1;

  
  /*@

    loop invariant v == 1 + 5*i;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i <= l;

    loop invariant l == 52;

    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && q == \at(q, Pre);

    loop invariant v == 1 + 5 * i;

    loop invariant 0 <= i;

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      v = v+4;
      i = i+1;
  }

}