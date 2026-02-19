int main1(int b,int m){
  int l, i, v;

  l=m;
  i=0;
  v=i;

  
  /*@

    loop invariant l == m;


    loop invariant v >= i;

    loop invariant v <= i + 8;

    loop invariant l == \at(m, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant 0 <= i;

    loop invariant (i <= l) || (i == 0);

    loop invariant (v == i) || (v == i + 7);

    loop invariant i >= 0;

    loop invariant v <= i + 7;

    loop invariant (i == 0) ==> (v - i == 0);

    loop invariant (l >= 0) ==> (i <= l);

    loop invariant v >= 0;

    loop invariant (i == 0) ==> (v == 0);

    loop invariant (i != 0) ==> (v == i + 7);

    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+1;
      v = i+8;
      i = i+1;
  }

}