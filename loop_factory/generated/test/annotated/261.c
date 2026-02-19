int main1(int b,int n){
  int l, i, v;

  l=n;
  i=l;
  v=-2;

  
  /*@

    loop invariant v * i >= -2 * \at(n, Pre);


    loop invariant v <= -2;

    loop invariant l == \at(n, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant l == n;

    loop invariant i <= l;


    loop invariant v % 2 == 0;

    loop invariant v < 0;

    loop assigns i, v;

    loop variant i;

  */
while (i>0) {
      if (v+3<l) {
          v = v*2;
      }
      else {
          v = v*2;
      }
      i = i/2;
  }

}