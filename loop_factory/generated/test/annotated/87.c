int main1(int a,int b,int n,int p){
  int l, i, v;

  l=54;
  i=0;
  v=3;

  
  /*@

    loop invariant l == 54;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant 0 <= i <= l;

    loop invariant 0 <= i && i <= l;

    loop invariant v >= 3;

    loop invariant i <= 54;

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant v > 0;

    loop invariant (i == 0) ==> (v == 3);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v*v+v;
      v = v*v;
      i = i+1;
  }

}