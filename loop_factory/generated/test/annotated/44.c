int main1(int a,int b,int k,int q){
  int l, i, v;

  l=a;
  i=l;
  v=l;

  
  /*@

    loop invariant l == \at(a, Pre);


    loop invariant (i == l) ==> v == l;

    loop invariant (i < l) ==> v % 2 == 0;

    loop invariant v >= \at(a, Pre);

    loop invariant l == a;

    loop invariant a == \at(a, Pre) && b == \at(b, Pre) && k == \at(k, Pre) && q == \at(q, Pre);

    loop invariant l == \at(a,Pre);

    loop invariant i <= l;


    loop invariant v >= \at(a,Pre);

    loop invariant l - i >= 0;


    loop invariant i <= a;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns i, v;

    loop variant i;

  */
while (i>0) {
      v = v+i;
      v = v*2;
      i = i-1;
  }

}