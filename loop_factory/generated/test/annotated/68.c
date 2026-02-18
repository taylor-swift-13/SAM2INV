int main1(int b,int k,int n,int q){
  int l, i, v;

  l=45;
  i=0;
  v=-4;

  
  /*@

    loop invariant b == \at(b, Pre);

    loop invariant k == \at(k, Pre);

    loop invariant n == \at(n, Pre);

    loop invariant q == \at(q, Pre);

    loop invariant i >= 0;

    loop invariant i <= l;

    loop invariant v <= -2*i - 4;

    loop invariant 0 <= i <= l;

    loop invariant (v + 2) % 2 == 0;

    loop invariant v <= -2;

    loop invariant b == \at(b, Pre) && k == \at(k, Pre) && n == \at(n, Pre) && q == \at(q, Pre);

    loop invariant v <= -4 - 2*i;

    loop invariant l == 45;

    loop invariant v <= -4;

    loop assigns v, i;

    loop variant l - i;

  */
while (i<l) {
      v = v+1;
      if (i<l+5) {
          v = v+v;
      }
      else {
          v = v+1;
      }
      i = i+1;
  }

}