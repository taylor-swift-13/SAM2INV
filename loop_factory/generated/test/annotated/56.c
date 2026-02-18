int main1(int a,int b,int m,int n){
  int l, i, v;

  l=n-7;
  i=0;
  v=-3;

  
  /*@


    loop invariant l == \at(n,Pre) - 7;

    loop invariant v == -3 + 4 * ((i + 4) / 5);

    loop invariant i >= 0;

    loop invariant l == \at(n, Pre) - 7;

    loop invariant n == \at(n, Pre);

    loop invariant l == n - 7;


    loop invariant (i == 0) ==> (v == -3);

    loop invariant ((v + 3) % 4) == 0;

    loop invariant a == \at(a, Pre);

    loop invariant b == \at(b, Pre);

    loop invariant m == \at(m, Pre);

    loop invariant i <= l || l < 0;

    loop assigns i, v;

    loop variant l - i;

  */
while (i<l) {
      if ((i%5)==0) {
          v = v+4;
      }
      i = i+1;
  }

}