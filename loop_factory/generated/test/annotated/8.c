int main1(int a,int k,int m,int q){
  int l, i, v, d, r;

  l=(a%25)+19;
  i=0;
  v=k;
  d=l;
  r=l;

  
  /*@


    loop invariant d - r * i == l;

    loop invariant r == l;

    loop invariant l == (\at(a, Pre) % 25) + 19;

    loop invariant l == (a % 25) + 19;

    loop invariant i >= 0;


    loop invariant d == l + i*r;

    loop invariant d == r*(i+1);

    loop invariant l == \at(a, Pre) % 25 + 19;

    loop invariant d == l + i * r;

    loop invariant i >= 0 && (l >= 0 ==> i <= l);

    loop invariant k == \at(k, Pre);

    loop invariant d == l * (i + 1);

    loop invariant a == \at(a, Pre) && k == \at(k, Pre) && m == \at(m, Pre) && q == \at(q, Pre);

    loop assigns d, i;

    loop variant l - i;

  */
while (i<l) {
      d = d+r;
      i = i+1;
  }

}