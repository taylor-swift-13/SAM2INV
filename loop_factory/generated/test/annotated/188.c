int main1(int a,int b,int k,int m){
  int l, i, v, f;

  l=m+23;
  i=0;
  v=6;
  f=k;

  
  /*@


    loop invariant l == m + 23;

    loop invariant 6 + 5*i <= v;

    loop invariant v <= 6 + 8*i;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant i >= 0;

    loop invariant f == k + i*(i+1)/2;

    loop invariant l == \at(m, Pre) + 23;

    loop invariant 0 <= i;

    loop invariant v >= 6 + 5*i;

    loop invariant f == k + i + i*(i-1)/2;


    loop invariant (i <= 2*l - 2) ==> (v == 6 + 8*i);

    loop assigns v, f, i;

    loop variant l - i;

  */
  while (i<l) {
      v = v+5;
      f = f+1;
      if (i+3<=l+l) {
          v = v+3;
      }
      f = f+i;
      i = i+1;
  }

}