int main1(int b,int k,int n,int q){
  int l, i, v, j;

  l=65;
  i=0;
  v=k;
  j=8;

  
  /*@

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant l == 65;

    loop invariant k == \at(k, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant j - 8 == 2*(v - k);


    loop invariant 0 <= i <= l;


    loop invariant j == 8 - 2*k + 2*v;

    loop assigns i, v, j;

    loop variant l - i;

  */
  while (i<l) {
      v = v*2;
      j = j+v;
      i = i+1;
  }

}