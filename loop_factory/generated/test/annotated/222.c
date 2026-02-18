int main1(int a,int k){
  int l, i, v, o, j;

  l=35;
  i=1;
  v=8;
  o=k;
  j=-4;

  
  /*@

    loop invariant k == \at(k,Pre);

    loop invariant a == \at(a,Pre);

    loop invariant i == 1;

    loop invariant i <= l;

    loop invariant v % 4 == 0;

    loop invariant v >= 8;

    loop invariant l == 35;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant v % 8 == 0;

    loop invariant ( (\at(k,Pre) >= 0) ==> o <= \at(k,Pre) ) && ( (\at(k,Pre) < 0) ==> o >= \at(k,Pre) );

    loop invariant i >= 1;


    loop assigns v, o;

  */
while (i<l) {
      v = v*4;
      o = o/4;
  }

}