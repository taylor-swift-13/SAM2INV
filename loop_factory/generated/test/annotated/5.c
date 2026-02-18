int main1(int a,int k,int m,int q){
  int l, i, v, w, z;

  l=68;
  i=l;
  v=-6;
  w=8;
  z=1;

  
  /*@

    loop invariant l == 68;

    loop invariant w == 8;

    loop invariant z == 1;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v == -6 + (l - i) * (w + z + 1);

    loop invariant 0 <= i && i <= 68;

    loop invariant 0 <= i && i <= l;

    loop invariant w == 8 && z == 1;

    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && q == \at(q, Pre);

    loop invariant v + 10 * i == 674;

    loop invariant 0 <= i;

    loop invariant i <= 68;

    loop invariant v + i*(w + z + 1) == 674;

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v+w+z;
      v = v+1;
      i = i-1;
  }

}