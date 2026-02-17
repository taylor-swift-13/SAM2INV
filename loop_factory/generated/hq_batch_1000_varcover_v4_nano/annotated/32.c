int main1(int b,int k,int q){
  int l, i, v, m, a, s, g, j;

  l=k+21;
  i=l;
  v=q;
  m=4;
  a=b;
  s=i;
  g=k;
  j=3;

  
  /*@

    loop invariant k == \at(k, Pre);

    loop invariant l == k + 21;

    loop invariant q == \at(q, Pre);

    loop invariant i <= l;

    loop invariant l >= 0 ==> i >= 0;

    loop assigns i;

    loop variant i;

  */
while (i>0) {
      i = i/2;
  }

}