int main1(int a,int k,int m,int p){
  int l, i, v;

  l=(a%34)+5;
  i=0;
  v=m;

  
  /*@

    loop invariant l == (a % 34) + 5;

    loop invariant 0 <= i;


    loop invariant (v - m) % 8 == 0;

    loop invariant v >= m;


    loop invariant (l < 0) || (i <= l);

    loop invariant (i == 0) ==> (v == m);

    loop invariant a == \at(a,Pre) && k == \at(k,Pre) && m == \at(m,Pre) && p == \at(p,Pre);

    loop invariant l == (\at(a,Pre) % 34) + 5;

    loop invariant v == \at(m,Pre) + 4 * (((i - 1) / 8) * (((i - 1) / 8) + 1));

    loop invariant i >= 0;


    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant p == \at(p, Pre);


    loop assigns v, i;

    loop variant l - i;

  */
  while (i<l) {
      if ((i%8)==0) {
          v = v+i;
      }
      i = i+1;
  }

}