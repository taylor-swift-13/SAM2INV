int main1(int a,int p){
  int l, i, v;

  l=14;
  i=l;
  v=i;

  
  /*@

    loop invariant i <= 14;

    loop invariant i >= 0;

    loop invariant v >= i;

    loop invariant a == \at(a, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant l == 14;

    loop invariant v % 2 == 0;

    loop invariant 0 <= i && i <= l;

    loop invariant v >= 0;

    loop invariant a == \at(a, Pre) && p == \at(p, Pre);

    loop invariant i <= l;

    loop invariant v >= 14;

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v*v+v;
      v = v*2;
      i = i-1;
  }

}