int main1(int b,int k,int n,int q){
  int l, i, v;

  l=b-6;
  i=0;
  v=q;

  
  /*@


    loop invariant l == b - 6;

    loop invariant v == q || v == l - 5 + i;

    loop invariant i >= 0;

    loop invariant (i == 0) ==> (v == q);

    loop invariant (i > 0) ==> (v == l - 4 + i - 1);

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant l == \at(b, Pre) - 6;

    loop invariant (i <= l) || (l < 0);

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+i;
      v = l-4;
      if (i<i+4) {
          v = v+i;
      }
      i = i+1;
  }

}