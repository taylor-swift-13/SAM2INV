int main1(int a,int b,int k,int m){
  int l, i, v;

  l=b+14;
  i=0;
  v=4;

  
  /*@

    loop invariant l == \at(b, Pre) + 14;


    loop invariant i >= 0;

    loop invariant v >= 4;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant l == b + 14;


    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && k == \at(k, Pre) && m == \at(m, Pre);

    loop invariant l <= 0 || i <= l;

    loop invariant v % 2 == 0;

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant v >= 0;

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      v = v*v+v;
      v = v+v;
      if (v+4<l) {
          v = v*v+v;
      }
      i = i+1;
  }

}