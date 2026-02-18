int main1(int b,int k,int m,int p){
  int l, i, v;

  l=74;
  i=0;
  v=k;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;


    loop invariant k == \at(k, Pre);

    loop invariant l == 74;

    loop invariant v == \at(k, Pre) * (i + 1) + i * (i - 1) / 2;

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant v == \at(k, Pre) * (1 + i) + i * (i - 1) / 2;

    loop invariant 0 <= i <= l;

    loop invariant v == k*(i+1) + i*(i-1)/2;

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+i;
      v = v+k;
      i = i+1;
  }

}