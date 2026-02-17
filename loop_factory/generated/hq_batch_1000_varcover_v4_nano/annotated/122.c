int main1(int m,int n,int q){
  int l, i, v, w, t;

  l=78;
  i=0;
  v=m;
  w=5;
  t=i;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant v == m + i;

    loop invariant w == 5 + i*m + i*(i - 1)/2;

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns i, v, w;

  */
  while (i<l) {
      v = v+1;
      w = w-1;
      w = w+v;
      i = i+1;
  }

}