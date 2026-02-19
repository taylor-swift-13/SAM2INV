int main1(int m,int q){
  int l, i, v;

  l=59;
  i=0;
  v=i;

  
  /*@

    loop invariant l == 59;


    loop invariant i % 5 == 0;


    loop invariant m == \at(m, Pre) && q == \at(q, Pre);

    loop invariant v >= 0;

    loop invariant m == \at(m, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant 0 <= i;

    loop invariant i <= l + 4;

    loop invariant v % 2 == 0;

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      v = v+v;
      v = v+2;
      i = i+5;
  }

}