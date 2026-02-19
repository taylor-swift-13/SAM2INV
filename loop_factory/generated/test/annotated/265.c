int main1(int a,int q){
  int l, i, v;

  l=a+9;
  i=0;
  v=a;

  
  /*@

    loop invariant a == \at(a, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant l == a + 9;

    loop invariant i >= 0;


    loop invariant v >= a;

    loop invariant (i == 0) ==> (v == a);

    loop invariant (i > 0) ==> (v >= 0);

    loop invariant a == \at(a,Pre);

    loop invariant l == \at(a,Pre) + 9;

    loop invariant q == \at(q,Pre);



    loop invariant (i == 0 ==> v == \at(a,Pre)) && (i >= 1 ==> v >= 0);

    loop invariant 0 <= i;

    loop invariant 0 <= i && (l < 0 || i <= l);

    loop invariant i == 0 ==> v == \at(a,Pre);

    loop assigns i, v;

    loop variant l - i;

  */
  while (i<l) {
      v = v*v+v;
      v = v*v;
      i = i+1;
  }

}