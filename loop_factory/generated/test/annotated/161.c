int main1(int a,int k,int m,int p){
  int l, i, v;

  l=45;
  i=0;
  v=-2;

  
  /*@

    loop invariant v == -2 + 4 * ((i + 1) / 2);

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant l == 45;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant 0 <= i <= l;

    loop invariant 0 <= i && i <= l;

    loop assigns v, i;

  */
  while (i<l) {
      if ((i%2)==0) {
          v = v+4;
      }
      i = i+1;
  }

}