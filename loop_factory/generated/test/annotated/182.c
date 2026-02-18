int main1(int a,int b,int p,int q){
  int l, i, v, t, z;

  l=72;
  i=0;
  v=i;
  t=b;
  z=b;

  
  /*@

    loop invariant i <= l;

    loop invariant z == b + 3*i;

    loop invariant v == 0;

    loop invariant (i % 2 == 0) ==> t == b;

    loop invariant (i % 2 != 0) ==> t == -b;

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && p == \at(p, Pre) && q == \at(q, Pre);

    loop invariant z == \at(b, Pre) + 3*i;

    loop invariant t*t == \at(b, Pre) * \at(b, Pre);

    loop invariant 0 <= i <= l;

    loop invariant p == \at(p, Pre);

    loop invariant l == 72;

    loop invariant i >= 0;

    loop invariant (i % 2 == 0) ==> t == \at(b, Pre);

    loop invariant (i % 2 == 1) ==> t == - \at(b, Pre);

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant (i % 2 == 1) ==> t == -b;

    loop invariant z == \at(b,Pre) + 3*i;

    loop invariant t*t == \at(b,Pre) * \at(b,Pre);

    loop invariant a == \at(a,Pre) && b == \at(b,Pre) && p == \at(p,Pre) && q == \at(q,Pre);

    loop assigns i, v, z, t;

  */
  while (i<l) {
      v = v+1;
      z = z+3;
      if (v+4<l) {
          v = t-v;
      }
      else {
          v = v-p;
      }
      v = p-p;
      if (i+2<=i+l) {
          t = v-t;
      }
      else {
          z = z+v;
      }
      i = i+1;
  }

}