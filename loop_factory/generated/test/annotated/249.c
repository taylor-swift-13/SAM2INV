int main1(int k,int p){
  int l, i, v, a, f;

  l=8;
  i=0;
  v=6;
  a=6;
  f=0;

  
  /*@

    loop invariant k == \at(k, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v >= 2*i + 4;

    loop invariant l == 8;

    loop invariant v >= 6;

    loop invariant 0 <= i && i <= l;

    loop invariant v % 2 == 0;

    loop invariant (v - 2) % 4 == 0;

    loop assigns v, i;

  */
  while (i<l) {
      v = v*2+2;
      i = i+1;
  }

}