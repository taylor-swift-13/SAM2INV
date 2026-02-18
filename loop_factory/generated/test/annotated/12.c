int main1(int b,int m,int n,int p){
  int l, i, v, j, a;

  l=17;
  i=0;
  v=-1;
  j=m;
  a=2;

  
  /*@

    loop invariant i % 4 == 0;

    loop invariant 2*a == i + 4;

    loop invariant 8*v == i*i + 4*i - 8;

    loop invariant i == 2*(a - 2);

    loop invariant v == (a*(a - 2))/2 - 1;

    loop invariant 0 <= i && i <= l + 3;

    loop invariant a == 2 + i/2;

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant v == -1 + 2*(i/4)*((i/4)+1);

    loop invariant l == 17;


    loop invariant b == \at(b, Pre) && m == \at(m, Pre) && n == \at(n, Pre) && p == \at(p, Pre);

    loop assigns i, a, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v+4;
      a = a+2;
      v = v+i;
      i = i+4;
  }

}