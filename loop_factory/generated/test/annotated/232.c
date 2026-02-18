int main1(int a,int k){
  int l, i, v;

  l=31;
  i=0;
  v=a;

  
  /*@

    loop invariant l == 31;

    loop invariant i % 5 == 0;

    loop invariant k == \at(k, Pre);

    loop invariant a == \at(a, Pre);

    loop invariant i >= 0;

    loop invariant (i % 5) == 0;

    loop invariant a == \at(a,Pre);

    loop invariant k == \at(k,Pre);

    loop invariant i <= l + 4;

    loop invariant 0 <= i && i <= l + 4;


    loop invariant v == a || (v >= 0 && v <= 7);

    loop assigns v, i;

  */
  while (i<l) {
      v = v*v;
      v = v%8;
      i = i+5;
  }

}