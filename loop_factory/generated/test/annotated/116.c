int main1(int a,int b,int k,int n){
  int l, i, v;

  l=(a%20)+19;
  i=1;
  v=i;

  
  /*@

    loop invariant l == (\at(a,Pre) % 20) + 19;

    loop invariant i >= 1;

    loop invariant v >= 1;

    loop invariant v >= i;

    loop invariant l == (\at(a, Pre) % 20) + 19;


    loop invariant v > 0;

    loop invariant l == (a % 20) + 19;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);


    loop invariant v % 4 == 0 || v == 1;

    loop assigns i, v;

  */
  while (i<l) {
      v = v+v;
      v = v*v;
      i = i*3;
  }

}