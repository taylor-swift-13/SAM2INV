int main1(int b,int n,int p){
  int l, i, v, q, o;

  l=(b%9)+15;
  i=l;
  v=l;
  q=2;
  o=-5;

  
  /*@

    loop invariant l == (b % 9) + 15;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant b == \at(b, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop assigns i;

    loop variant i;

  */
  while (i>0) {
      i = i-1;
  }

}