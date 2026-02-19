int main1(int a,int q){
  int l, i, v;

  l=20;
  i=0;
  v=8;

  
  /*@

    loop invariant 0 <= i && i <= l;

    loop invariant l == 20;

    loop invariant (i == 0 ==> v == 8) && (i >= 1 ==> v == 0);

    loop invariant a == \at(a, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant v >= 0;

    loop invariant v <= 8;

    loop invariant i <= l;

    loop invariant (i == 0 ==> v == 8) && (i > 0 ==> v == 0);

    loop invariant i >= 0;

    loop invariant 0 <= v && v <= 9;

    loop invariant 0 <= i <= l;

    loop invariant v == 8 || v == 0;

    loop invariant (i == 0) ==> (v == 8);

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      v = v%4;
      v = v*v;
      i = i+1;
  }

}