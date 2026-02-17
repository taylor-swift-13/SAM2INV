int main1(int m,int n,int q){
  int l, i, v;

  l=28;
  i=0;
  v=-8;

  
  /*@

    loop invariant v == -8 + 2*i;

    loop invariant 0 <= i && i <= l;

    loop invariant l == 28;

    loop invariant m == \at(m,Pre) && n == \at(n,Pre) && q == \at(q,Pre);

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      v = v+1;
      i = i+1;
  }

}