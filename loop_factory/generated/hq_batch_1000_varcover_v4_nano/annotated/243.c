int main1(int k,int m,int n){
  int l, i, v, s, z, o;

  l=33;
  i=0;
  v=6;
  s=5;
  z=-4;
  o=n;

  
  /*@

    loop invariant v == 6 + 3 * i;

    loop invariant 2 * (s - 5) == 3 * i * (i + 5);

    loop invariant 2 * (z + 4 - 5 * i) == i * (i + 1) * (i + 8);

    loop invariant 0 <= i && i <= l;

    loop invariant k == \at(k, Pre) && m == \at(m, Pre) && n == \at(n, Pre);

    loop assigns v, s, z, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+3;
      s = s+v;
      z = z+s;
      i = i+1;
  }

}