int main1(int a,int k,int m,int p){
  int l, i, v;

  l=72;
  i=0;
  v=-1;

  
  /*@

    loop invariant i <= l;

    loop invariant v == -1 + i*(i-1)/2;

    loop invariant l == 72;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant 0 <= i <= l;

    loop invariant v == -1 + i*(i - 1)/2;

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+i;
      i = i+1;
  }

}