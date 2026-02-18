int main1(int a,int k,int m,int n){
  int l, i, v, j;

  l=52;
  i=0;
  v=i;
  j=2;

  
  /*@

    loop invariant i <= l;

    loop invariant 0 <= i;

    loop invariant l == 52;

    loop invariant j == 2 + 2*i;

    loop invariant v == 2*i*i + 3*i;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre);

    loop invariant j == 2*i + 2;

    loop assigns v, j, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+j+j;
      v = v+1;
      j = j+2;
      i = i+1;
  }

}