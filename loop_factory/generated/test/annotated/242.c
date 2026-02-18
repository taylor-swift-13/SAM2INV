int main1(int k,int q){
  int l, i, v, b, u;

  l=k;
  i=0;
  v=i;
  b=8;
  u=4;

  
  /*@

    loop invariant v == 0;


    loop invariant i >= 0;

    loop invariant l == k;

    loop invariant k == \at(k, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant 0 <= i;

    loop invariant (i <= l) || (l <= 0);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v*v+v;
      i = i+1;
  }

}