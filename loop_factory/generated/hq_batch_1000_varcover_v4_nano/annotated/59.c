int main1(int m,int p,int q){
  int l, i, v;

  l=q-7;
  i=0;
  v=m;

  
  /*@

    loop invariant l == q - 7;

    loop invariant 0 <= i;

    loop invariant (l >= 0) ==> (i <= l);

    loop invariant (i > 0) ==> ((v + 2) % 2 == 0);

    loop invariant m == \at(m, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      v = v+v;
      i = i+1;
  }

}