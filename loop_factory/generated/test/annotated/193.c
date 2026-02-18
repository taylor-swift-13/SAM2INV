int main1(int a,int k,int n,int p){
  int l, i, v;

  l=11;
  i=l;
  v=a;

  
  /*@

    loop invariant i >= 0;

    loop invariant i <= 11;

    loop invariant v == a + (11 - i) * 12 - ((11 - i) * (10 - i)) / 2;

    loop invariant 0 <= i <= 11;

    loop invariant i*i + 3*i + 2*(v - a) == 154;

    loop invariant a == \at(a, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant p == \at(p, Pre);

    loop invariant v <= a + 77;

    loop invariant 2*v == 2*a + (l - i) * (i + l + 3);

    loop invariant i <= l;

    loop invariant v == \at(a, Pre) + 77 - i*(i+3)/2;

    loop invariant 0 <= i && i <= 11;

    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && n == \at(n, Pre) && p == \at(p, Pre) && l == 11;

    loop assigns v, i;

    loop variant i;

  */
  while (i>0) {
      v = v+i;
      v = v+1;
      i = i-1;
  }

}