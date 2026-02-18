int main1(int a,int n,int p,int q){
  int l, i, v, y, z;

  l=13;
  i=0;
  v=l;
  y=a;
  z=6;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i <= l;

    loop invariant i >= 0;

    loop invariant v == 13 + 4*i;

    loop invariant y == a + 2*i*i + 15*i;

    loop invariant z == 6 + a*i + (i*(i+1)*(2*i+1))/3 + (15*i*(i+1))/2;

    loop invariant l == 13;

    loop invariant v == l + 4*i;

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant z == 6 + a*i + i*(i+1)*(2*i+1)/3 + 15*i*(i+1)/2;

    loop invariant y == a + i*l + 2*i*(i+1);

    loop invariant z == 6 + i*a + (l * i * (i+1))/2 + (2 * i * (i+1) * (i+2))/3;

    loop assigns v, y, z, i;

  */
  while (i<l) {
      v = v+4;
      y = y+v;
      z = z+y;
      i = i+1;
  }

}