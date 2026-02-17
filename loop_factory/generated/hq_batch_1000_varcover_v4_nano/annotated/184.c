int main1(int m,int p,int q){
  int l, i, v;

  l=76;
  i=0;
  v=1;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant v == 1 || v == l - 4;

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      if (i<q+1) {
          v = v;
      }
      else {
          v = v+i;
      }
      v = v+v;
      v = l+(-4);
      i = i+1;
  }

}