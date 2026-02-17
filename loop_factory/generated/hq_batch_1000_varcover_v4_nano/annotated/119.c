int main1(int a,int k,int q){
  int l, i, v, e;

  l=(a%14)+18;
  i=l;
  v=-4;
  e=a;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v == 4*(l - i) - 4;

    loop invariant e == a + 2*(l - i)*(l - i) - 5*(l - i);

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant q == \at(q, Pre);

    loop assigns v, e, i;

    loop variant i;

  */
  while (i>0) {
      v = v+1;
      e = e+v;
      v = v+3;
      i = i-1;
  }

}