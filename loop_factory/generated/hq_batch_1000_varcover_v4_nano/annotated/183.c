int main1(int a,int n,int p){
  int l, i, v, z, f, j;

  l=77;
  i=l;
  v=i;
  z=-5;
  f=-4;
  j=a;

  
  /*@

    loop invariant 0 <= i <= 77;

    loop invariant v <= 77;

    loop invariant (77 - v) % 5 == 0;

    loop invariant a == \at(a, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v+z;
      i = i/2;
  }

}