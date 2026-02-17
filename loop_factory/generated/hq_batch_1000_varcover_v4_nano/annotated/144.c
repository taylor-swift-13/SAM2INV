int main1(int m,int n,int q){
  int l, i, v, c;

  l=66;
  i=0;
  v=6;
  c=i;

  
  /*@

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant 0 <= i <= l;

    loop invariant v == 6 + i;

    loop invariant c == (i*i + 11*i) / 2;

    loop assigns v, c, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      c = c-1;
      if (i<i+2) {
          c = c+v;
      }
      i = i+1;
  }

}