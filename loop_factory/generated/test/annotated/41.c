int main1(int a,int b,int m,int q){
  int l, i, v, n, z;

  l=(a%23)+16;
  i=0;
  v=b;
  n=i;
  z=q;

  
  /*@

    loop invariant i >= 0;

    loop invariant (i <= l) || (l < 0);

    loop invariant n == 0;

    loop invariant l == ((\at(a,Pre) % 23) + 16);

    loop invariant l == (a % 23) + 16;


    loop invariant (i > 0) ==> (0 <= v && v <= 8);

    loop invariant l == (\at(a, Pre) % 23) + 16;

    loop invariant z == \at(q, Pre);


    loop invariant z == q;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop assigns v, n, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v*v+v;
      v = v%9;
      n = n*z;
      i = i+1;
  }

}