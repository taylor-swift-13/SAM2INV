int main1(int b,int k){
  int l, i, v, p, h;

  l=64;
  i=l;
  v=l;
  p=8;
  h=l;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= 64;

    loop invariant l == 64;

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant v >= 64;

    loop invariant v % 2 == 0;

    loop invariant v >= 0;

    loop invariant i <= l;

    loop invariant v >= l;


    loop invariant v >= i;

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v*2+2;
      i = i/2;
  }

}