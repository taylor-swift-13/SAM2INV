int main1(int b,int k,int m,int n){
  int l, i, v;

  l=33;
  i=1;
  v=5;

  
  /*@

    loop invariant l == 33;

    loop invariant 1 <= i;


    loop invariant i == 1 || i % 3 == 0;

    loop invariant v >= 5;

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant i >= 1;

    loop invariant (i < l) ==> (i + 6 <= l + l);

    loop invariant v % 5 == 0;

    loop invariant i > 0;

    loop invariant (i == 1) || (i % 3 == 0);

    loop invariant b == \at(b,Pre);

    loop invariant k == \at(k,Pre);

    loop invariant m == \at(m,Pre);

    loop invariant n == \at(n,Pre);

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      v = v+v;
      if (i+6<=l+l) {
          v = v+v;
      }
      else {
          v = v+(-3);
      }
      i = i*3;
  }

}